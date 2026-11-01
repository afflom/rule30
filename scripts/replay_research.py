#!/usr/bin/env python3
"""Kernel-replay the research modules with `leanchecker`, keeping a receipt per
replayed module so a module whose meaning is unchanged is never replayed twice.

A receipt is κ-addressed: keyed by the module's κ-label (`kappa_research.py`,
the address of the declarations the kernel replays under the canonical-form
rule of UOR-Foundation/uor-addr), together with the toolchain name and the
digest of the `leanchecker` binary. It is never keyed by the object-file
bytes, which also carry source positions, docstrings and extension data, nor
by the source path or the Git state: a module rebuilt after a comment, a
docstring or a bound-variable renaming reuses its receipt, and a module whose
declarations changed is always replayed. The modules without a receipt are
replayed in one `leanchecker` invocation (the same command as before); a
receipt, holding the module name and its full κ, is written atomically for
each of them only when it succeeds. The receipts live in `RULE30_REPLAY_CACHE`
when the gate sets it (beside its Lake and LexLean caches, so they survive
rejected commits), else in `.r30/replay`."""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from check_research_coverage import covered_modules
from kappa_research import SCHEME, module_labels

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PARTS = (".olean", ".olean.private")


def artifact_paths(core, module):
    base = core / ".lake" / "build" / "lib" / "lean" / Path(*module.split("."))
    return [base.with_name(base.name + part) for part in ARTIFACT_PARTS]


def tool_digest(core, leanchecker):
    digest = hashlib.sha256()
    digest.update((core / "lean-toolchain").read_text().strip().encode() + b"\0")
    digest.update(Path(leanchecker).read_bytes())
    return digest.hexdigest()


def receipt_key(kappa, tools):
    """The receipt's file stem: the module's κ under the proof tools."""
    return f"{kappa[len(SCHEME):]}.{tools[:16]}"


def default_leanchecker(core):
    prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=core, text=True).strip()
    return str(Path(prefix) / "bin" / "leanchecker")


def write_receipt(cache, key, module, kappa, tools):
    descriptor, temporary = tempfile.mkstemp(prefix=key[:12] + ".", suffix=".tmp", dir=cache)
    with os.fdopen(descriptor, "w") as stream:
        stream.write(f"{module}\nkappa {kappa}\ntools {tools}\n")
    os.replace(temporary, cache / (key + ".ok"))


def artifact_digest(core, module):
    """The bytes of a module's compiled artifact: a memo key for its κ, never a receipt key."""
    digest = hashlib.sha256(SCHEME.encode())
    for path in artifact_paths(core, module):
        if path.exists():
            digest.update(path.name.encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def module_kappas(core, modules, cache, exporter=None):
    """κ of each module. The κ is a pure function of the artifact bytes, so it is memoized
    under `<cache>/kappa/<artifact digest>`; only modules whose artifact changed are exported.
    The memo is a cache of the computation; receipts stay keyed by the κ itself."""
    memo = cache / "kappa"
    memo.mkdir(parents=True, exist_ok=True)
    kappas, digests = {}, {module: artifact_digest(core, module) for module in modules}
    for module in modules:
        entry = memo / digests[module]
        if entry.exists():
            kappas[module] = entry.read_text().strip()
    fresh = [module for module in modules if module not in kappas]
    if fresh:
        labels = module_labels(core, fresh, exporter=exporter)
        for module in fresh:
            kappas[module] = labels[module]["kappa"]
            tmp = memo / (digests[module] + ".tmp")
            tmp.write_text(kappas[module] + "\n")
            os.replace(tmp, memo / digests[module])
    return kappas


def replay(core, modules, leanchecker, cache, log=print, exporter=None):
    cache.mkdir(parents=True, exist_ok=True)
    for module in modules:
        if not artifact_paths(core, module)[0].exists():
            raise FileNotFoundError(f"{module} has no compiled artifact at {artifact_paths(core, module)[0]}; "
                                    "build first")
    tools = tool_digest(core, leanchecker)
    kappas = module_kappas(core, modules, cache, exporter=exporter)
    keys = {module: receipt_key(kappas[module], tools) for module in modules}
    pending = [module for module in modules if not (cache / (keys[module] + ".ok")).exists()]
    for module in modules:
        if module not in pending:
            log(f"{module}: receipt {kappas[module][:len(SCHEME) + 12]}")
    if pending:
        sys.stdout.flush()
        result = subprocess.run(["lake", "env", leanchecker, *pending], cwd=core)
        if result.returncode != 0:
            raise RuntimeError(f"leanchecker failed on {len(pending)} modules (exit {result.returncode}); "
                               "no receipt written")
        for module in pending:
            write_receipt(cache, keys[module], module, kappas[module], tools)
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
