#!/usr/bin/env python3
"""Run the CI gate on an immutable Git tree, with success-only local caching."""

import fcntl
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib

from sync_pdfs import GENERATED, source_digest

# Lake packages whose build directories are reused between gate runs. Lake
# decides what to rebuild from content traces, so a stale entry costs a rebuild,
# never a wrong result; the cache is keyed by the proof tools' digest.
LAKE_PACKAGES = ("Rule30PrizeKit/lean", "rule30-core-lean", "rule30-bridge",
                 "rule30-lexlean", "rule30-paper")
# Tracked inputs of a LexLean project's verification: the project itself, the
# host Lean it elaborates its external-interface probe against, and the script.
LEXLEAN_INPUTS = {
    "rule30-lexlean": ("rule30-lexlean/", "rule30-core-lean/", "Rule30PrizeKit/lean/",
                       "scripts/verify_lexlean.sh"),
    "rule30-paper": ("rule30-paper/", "rule30-core-lean/", "Rule30PrizeKit/lean/",
                     "scripts/verify_lexlean.sh"),
}


def output(*args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs).strip()


def index_bytes(root, path):
    result = subprocess.run(["git", "show", ":" + path], cwd=root, capture_output=True)
    return result.stdout if result.returncode == 0 else None


def check_generated_worktree(root):
    for path in GENERATED:
        current = (root / path).read_bytes() if (root / path).exists() else None
        if current != index_bytes(root, path):
            raise RuntimeError(f"Unstaged generated artifact would be overwritten: {path}; "
                               "stage or save that edit before committing")


def install_generated(root, snapshot):
    # Check all destinations before touching any, then update the index in one transaction.
    check_generated_worktree(root)
    entries = []
    for path in GENERATED:
        data = (snapshot / path).read_bytes()
        blob = subprocess.check_output(["git", "hash-object", "-w", "--stdin"],
                                       cwd=root, input=data).decode().strip()
        entries.append(f"100644 {blob}\t{path}\0".encode())
    for path in GENERATED:
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(snapshot / path, target)
    subprocess.run(["git", "update-index", "-z", "--index-info"], cwd=root,
                   input=b"".join(entries), check=True)


def lexlean_input_digest(root, tree, project):
    """Hash of every tracked, non-generated blob a project's verification reads."""
    prefixes = LEXLEAN_INPUTS[project]
    entries = subprocess.check_output(["git", "ls-tree", "-rz", "--full-tree", tree],
                                      cwd=root).split(b"\0")
    digest = hashlib.sha256()
    for entry in entries:
        if not entry:
            continue
        path = entry.split(b"\t", 1)[1].decode()
        if path in GENERATED or not path.startswith(prefixes):
            continue
        digest.update(entry + b"\0")
    return digest.hexdigest()


def seed_lake_cache(cache_dir, snapshot):
    """Start the snapshot's Lake builds from the last accepted run's build directories."""
    for package in LAKE_PACKAGES:
        source = cache_dir / package / ".lake"
        target = snapshot / package
        if source.is_dir() and target.is_dir() and not (target / ".lake").exists():
            subprocess.run(["cp", "-a", str(source), str(target / ".lake")], check=True)


def store_lake_cache(cache_dir, snapshot):
    """Keep the accepted snapshot's build directories for the next run."""
    for package in LAKE_PACKAGES:
        built = snapshot / package / ".lake"
        if not built.is_dir():
            continue
        slot = cache_dir / package
        fresh = slot.with_name(slot.name + ".new")
        shutil.rmtree(fresh, ignore_errors=True)
        fresh.mkdir(parents=True)
        subprocess.run(["cp", "-a", str(built), str(fresh / ".lake")], check=True)
        shutil.rmtree(slot, ignore_errors=True)
        fresh.rename(slot)


def main():
    root = Path(output("git", "rev-parse", "--show-toplevel"))
    os.chdir(root)
    staged = len(sys.argv) == 1
    target = output("git", "write-tree") if staged else sys.argv[1]
    tree = output("git", "rev-parse", "--verify", target + "^{tree}")
    if staged:
        check_generated_worktree(root)
    toolchain = output("git", "show", tree + ":rule30-core-lean/lean-toolchain")

    configured = (os.environ.get("LEXLEAN_BIN") or os.environ.get("LEXLEAN")
                  or subprocess.run(["git", "config", "--get", "rule30.lexlean"],
                                    capture_output=True, text=True).stdout.strip())
    candidate = configured or (str(root / ".local/bin/lexlean")
                               if (root / ".local/bin/lexlean").exists() else "lexlean")
    compiler = shutil.which(candidate)
    if not compiler:
        raise RuntimeError("LexLean compiler missing; install the revision in "
                           ".github/lexlean-revision and set LEXLEAN_BIN or git config rule30.lexlean")
    compiler = str(Path(compiler).resolve())
    version = output(compiler, "--version")
    for project in ("rule30-lexlean", "rule30-paper"):
        lock = tomllib.loads(output("git", "show", f"{tree}:{project}/lexlean.lock"))
        if "compiler-semantics " + lock["compiler_semantics"] not in version.splitlines():
            raise RuntimeError("LexLean does not match staged lockfiles; install the compiler "
                               "revision in .github/lexlean-revision and set LEXLEAN_BIN")

    env = os.environ.copy()
    # Git exports repository/index variables into hooks. They must not redirect
    # commands in the snapshot (including regression-test fixture repositories).
    for name in output("git", "rev-parse", "--local-env-vars").splitlines():
        env.pop(name, None)
    # Match CI: each workspace selects its checked-in toolchain. A caller's
    # ELAN_TOOLCHAIN must not hide an incompatible bridge/project toolchain.
    env.pop("ELAN_TOOLCHAIN", None)
    for name in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES"):
        env.pop(name, None)
    env["LEXLEAN_BIN"] = compiler
    env["RULE30_SOURCE_DIGEST"] = source_digest(root, tree)
    # Only pre-commit may replace derived files. CI and pre-push must check them.
    env.pop("RULE30_REFRESH_PDFS", None)
    if staged:
        env["RULE30_REFRESH_PDFS"] = "1"
    version_env = dict(env, ELAN_TOOLCHAIN=toolchain)
    lean_version = output("lean", "--version", env=version_env)
    lake_version = output("lake", "--version", env=version_env)
    digest = hashlib.sha256()
    for item in (toolchain, lean_version, lake_version, version):
        digest.update(item.encode() + b"\0")
    digest.update(Path(compiler).read_bytes())
    digest.update(Path(__file__).read_bytes())
    cache = Path(output("git", "rev-parse", "--path-format=absolute", "--git-common-dir")) / "rule30-validation"
    cache.mkdir(exist_ok=True)
    def cache_key(value):
        keyed = digest.copy()
        keyed.update(value.encode())
        return keyed.hexdigest()

    key = cache_key(tree)
    certificate = cache / (key + ".ok")
    # Finer caches, keyed by the same proof-tool digest: Lake build directories
    # and per-project LexLean verifications.
    tools_key = cache_key("tools")[:16]
    lake_cache = cache / "lake" / tools_key
    lexlean_cache = cache / "lexlean" / tools_key
    env["RULE30_LEXLEAN_CACHE"] = str(lexlean_cache)
    for project in LEXLEAN_INPUTS:
        env["RULE30_LEXLEAN_KEY_" + project.replace("-", "_")] = lexlean_input_digest(root, tree, project)
    with (cache / (key + ".lock")).open("w") as guard:
        fcntl.flock(guard, fcntl.LOCK_EX)
        if certificate.exists():
            print(f"Validation already passed for tree {tree[:12]} (same proof tools).", flush=True)
        else:
            print(f"Validating tree {tree[:12]} in a clean snapshot with make check-ci.", flush=True)
            with tempfile.TemporaryDirectory(prefix="rule30-validation-") as directory:
                # Archive the captured object, never the mutable index/worktree.
                with subprocess.Popen(["git", "archive", "--format=tar", tree],
                                      stdout=subprocess.PIPE) as archive:
                    subprocess.run(["tar", "-xf", "-", "-C", directory],
                                   stdin=archive.stdout, check=True)
                    archive.stdout.close()
                    if archive.wait() != 0:
                        raise RuntimeError("Could not export the captured Git tree")
                seed_lake_cache(lake_cache, Path(directory))
                subprocess.run(["make", "check-ci", "LEXLEAN=" + compiler],
                               cwd=directory, env=env, check=True)
                store_lake_cache(lake_cache, Path(directory))
                if staged:
                    if output("git", "write-tree") != tree:
                        raise RuntimeError("The index changed during validation; retry the commit")
                    install_generated(root, Path(directory))
                    final_tree = output("git", "write-tree")
                    if source_digest(root, final_tree) != env["RULE30_SOURCE_DIGEST"]:
                        raise RuntimeError("The source index changed while installing PDFs; retry")
                    tree = final_tree
                    certificate = cache / (cache_key(tree) + ".ok")
            certificate.write_text(tree + "\n")
        if staged and output("git", "write-tree") != tree:
            raise RuntimeError("The index changed during validation; stage the intended files and retry")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Validation failed; commit/push blocked: {error}", file=sys.stderr)
        sys.exit(1)
