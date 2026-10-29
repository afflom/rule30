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


def output(*args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs).strip()


def main():
    root = Path(output("git", "rev-parse", "--show-toplevel"))
    os.chdir(root)
    staged = len(sys.argv) == 1
    target = output("git", "write-tree") if staged else sys.argv[1]
    tree = output("git", "rev-parse", "--verify", target + "^{tree}")
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
    env["ELAN_TOOLCHAIN"] = toolchain
    env["LEXLEAN_BIN"] = compiler
    lean_version = output("lean", "--version", env=env)
    lake_version = output("lake", "--version", env=env)
    digest = hashlib.sha256()
    for item in (tree, toolchain, lean_version, lake_version, version):
        digest.update(item.encode() + b"\0")
    digest.update(Path(compiler).read_bytes())
    digest.update(Path(__file__).read_bytes())
    cache = Path(output("git", "rev-parse", "--path-format=absolute", "--git-common-dir")) / "rule30-validation"
    cache.mkdir(exist_ok=True)
    key = digest.hexdigest()
    certificate = cache / (key + ".ok")
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
                subprocess.run(["make", "check-ci", "LEXLEAN=" + compiler],
                               cwd=directory, env=env, check=True)
            certificate.write_text(tree + "\n")
        if staged and output("git", "write-tree") != tree:
            raise RuntimeError("The index changed during validation; stage the intended files and retry")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Validation failed; commit/push blocked: {error}", file=sys.stderr)
        sys.exit(1)
