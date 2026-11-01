#!/usr/bin/env python3
"""Kernel-replay the research modules with `leanchecker`, keeping a receipt per
replayed artifact so an unchanged module is never replayed twice.

The artifact of a module is its compiled `.olean` (with the `.olean.private`
part, which holds the proof terms the kernel checks). Its receipt is keyed by
the content of that artifact, the `leanchecker` binary and the toolchain name:
never by the source path or the Git state, so a rebuilt but byte-identical
module reuses its receipt and a changed one is always replayed. The modules
without a receipt are replayed in one `leanchecker` invocation (the same
command as before); a receipt is written for each of them only when it
succeeds. The receipts live in `RULE30_REPLAY_CACHE` when the gate sets it
(beside its Lake and LexLean caches, so they survive rejected commits), else
in `.r30/replay`."""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from check_research_coverage import covered_modules

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PARTS = (".olean", ".olean.private")


def artifact_paths(core, module):
    base = core / ".lake" / "build" / "lib" / "lean" / Path(*module.split("."))
    return [base.with_name(base.name + part) for part in ARTIFACT_PARTS]


def tool_digest(core, leanchecker):
    digest = hashlib.sha256()
    digest.update((core / "lean-toolchain").read_text().strip().encode() + b"\0")
    digest.update(Path(leanchecker).read_bytes())
    return digest.digest()


def kappa(core, module, tools):
    """The content address of a module's compiled artifact under the proof tools."""
    paths = artifact_paths(core, module)
    if not paths[0].exists():
        raise FileNotFoundError(f"{module} has no compiled artifact at {paths[0]}; build first")
    digest = hashlib.sha256(tools)
    for path in paths:
        if path.exists():
            data = path.read_bytes()
            digest.update(f"{path.suffix}\0{len(data)}\0".encode() + data)
    return digest.hexdigest()


def default_leanchecker(core):
    prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=core, text=True).strip()
    return str(Path(prefix) / "bin" / "leanchecker")


def write_receipt(cache, key, module):
    descriptor, temporary = tempfile.mkstemp(prefix=key[:12] + ".", suffix=".tmp", dir=cache)
    with os.fdopen(descriptor, "w") as stream:
        stream.write(module + "\n")
    os.replace(temporary, cache / (key + ".ok"))


def replay(core, modules, leanchecker, cache, log=print):
    cache.mkdir(parents=True, exist_ok=True)
    tools = tool_digest(core, leanchecker)
    keys = {module: kappa(core, module, tools) for module in modules}
    pending = [module for module in modules if not (cache / (keys[module] + ".ok")).exists()]
    for module in modules:
        if module not in pending:
            log(f"{module}: receipt {keys[module][:12]}")
    if pending:
        sys.stdout.flush()
        result = subprocess.run(["lake", "env", leanchecker, *pending], cwd=core)
        if result.returncode != 0:
            raise RuntimeError(f"leanchecker failed on {len(pending)} modules (exit {result.returncode}); "
                               "no receipt written")
        for module in pending:
            write_receipt(cache, keys[module], module)
            log(f"{module}: replayed")
    log(f"kernel replay: {len(pending)} replayed, {len(modules) - len(pending)} receipts, "
        f"receipts in {cache}")
    return pending


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("modules", nargs="*", help="research modules (default: every covered module)")
    parser.add_argument("--core", type=Path, default=ROOT / "rule30-core-lean")
    parser.add_argument("--leanchecker", help="the leanchecker binary (default: the workspace toolchain's)")
    parser.add_argument("--cache", type=Path, help="receipt directory (default: $RULE30_REPLAY_CACHE or .r30/replay)")
    args = parser.parse_args(argv)
    modules = args.modules or covered_modules(ROOT)
    leanchecker = args.leanchecker or default_leanchecker(args.core)
    cache = args.cache or Path(os.environ.get("RULE30_REPLAY_CACHE") or ROOT / ".r30" / "replay")
    replay(args.core, modules, leanchecker, cache)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Kernel replay failed: {error}", file=sys.stderr)
        sys.exit(1)
