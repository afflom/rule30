#!/usr/bin/env python3
"""κ-labels of the research modules: memo, redundancy, reports (`kappa_label.py` labels).

The labeling procedure lives in `kappa_label.py`; this file adds what does not change a label:
the memo keyed by artifact bytes and the procedure's digest, the authored-theorem test, the
groups of theorems that state the same thing, and the command-line report."""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from kappa_label import (EXPORTER, NODE_FIELDS, ROOT, SCHEME, canonical, export, kappa, label,  # noqa: E402,F401
                         labels_from_stream, module_labels, parse, positional)
import kappa_label  # noqa: E402


def artifact_paths(core, module):
    base = core / ".lake" / "build" / "lib" / "lean" / Path(*module.split("."))
    # every part the exporter can read, in its order (the server part decides when there is no private one)
    return [base.with_name(base.name + part) for part in (".olean", ".olean.server", ".olean.private")]


def artifact_digest(core, module):
    """The bytes of a module's compiled artifact: a memo key for its labels, never a receipt key."""
    digest = hashlib.sha256(SCHEME.encode())
    for path in artifact_paths(core, module):
        if path.exists():
            digest.update(path.name.encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def exporter_digest(core):
    """The labeling procedure itself (the exporter and this file): labels memoized under one
    procedure are never read back under another."""
    digest = hashlib.sha256(SCHEME.encode())
    for path in (core / EXPORTER, Path(kappa_label.__file__)):
        digest.update(path.name.encode() + b"\0" + (path.read_bytes() if path.exists() else b"") + b"\0")
    return digest.hexdigest()[:16]


def default_memo(core):
    """The gate's memo, beside its other caches in the Git common directory. Only the gate writes
    it (`RULE30_KAPPA_MEMO`); other callers read it and keep what they label in their own store, so
    the gate never trusts a label written from a mutable working tree."""
    common = subprocess.run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"], cwd=core,
                            capture_output=True, text=True)
    if common.returncode != 0:
        return None
    return Path(common.stdout.strip()) / "rule30-validation" / "kappa"


def read_entry(path):
    """A memo entry, or None when it is missing, unreadable or malformed (a miss: relabel)."""
    try:
        row = json.loads(path.read_text())
    except (OSError, ValueError):
        return None
    if not isinstance(row, dict) or not isinstance(row.get("kappa"), str):
        return None
    # rows of lists (declarations, statements) become tuples; lists of names (reserved) stay strings
    return {key: [tuple(x) if isinstance(x, list) else x for x in value] if isinstance(value, list) else value
            for key, value in row.items()}


def memo_labels(core, modules, memo, exporter=None, read_only=()):
    """The labels of the modules (κ, declarations, theorem statements), memoized by the artifact
    bytes under the labeling procedure's digest: looked up in `memo`, then in the `read_only`
    stores; the modules found nowhere are exported in one run and written to `memo` only, under
    the bytes they were computed from."""
    procedure = exporter_digest(core)
    store = memo / procedure
    store.mkdir(parents=True, exist_ok=True)
    stores = [store] + [Path(d) / procedure for d in read_only if d]
    labels, digests = {}, {module: artifact_digest(core, module) for module in modules}
    for module in modules:
        for directory in stores:
            row = read_entry(directory / digests[module])
            if row is not None:
                labels[module] = row
                break
    fresh = [module for module in modules if module not in labels]
    if fresh:
        for module, row in module_labels(core, fresh, exporter=exporter).items():
            if module not in digests:
                continue
            # The exporter read the artifact after it was hashed: refuse to answer if a build
            # replaced it meanwhile, so a label is only ever stored under its own bytes.
            if artifact_digest(core, module) != digests[module]:
                raise RuntimeError(f"{module}: its artifact changed while it was labeled; label again")
            labels[module] = row
            descriptor, temporary = tempfile.mkstemp(prefix=digests[module][:12] + ".", suffix=".tmp", dir=store)
            with os.fdopen(descriptor, "w") as stream:
                stream.write(json.dumps(row) + "\n")
            os.replace(temporary, store / digests[module])
    return {module: labels[module] for module in modules}


def working_memo(core):
    """(memo, read_only) for callers outside the gate: their own store, reading the gate's."""
    return core.parent / ".r30" / "kappa", [default_memo(core)]


def duplicates(labels):
    """Theorems that state the same thing: groups of (module, name) sharing a statement κ, across
    the given modules. Only authored theorems count: the exporter marks a theorem authored when
    Lean recorded a declaration range for it (it was written in a source file), so a lemma Lean
    generated (equation lemmas, functional induction, auxiliary proofs) never counts and a theorem
    someone wrote always does, whatever its name. A group of two or more is redundant work."""
    groups = {}
    for module, row in labels.items():
        authored = set(row.get("authored", ()))
        for name, k, *_ in row.get("statements", []):
            if name in authored:
                groups.setdefault(k, []).append((module, name))
    return {k: sorted(v) for k, v in groups.items() if len(v) > 1}


def render(labels, declarations=False):
    lines = []
    for module, row in labels.items():
        lines.append(f"{module}: {row['kappa']}")
        if declarations:
            lines.extend(f"  {name}: {k}" for name, k in row["declarations"])
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("modules", nargs="+", help="Lean module names (Rule30UOR.*)")
    parser.add_argument("--core", type=Path, default=ROOT / "rule30-core-lean")
    parser.add_argument("--declarations", action="store_true", help="also print each declaration's κ")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    labels = module_labels(args.core, args.modules, exporter=lambda core, modules: export(core, modules))
    if args.json:
        print(json.dumps({m: {"kappa": r["kappa"], "declarations": [{"name": n, "kappa": k} for n, k in r["declarations"]]}
                          for m, r in labels.items()}, indent=1))
    else:
        print(render(labels, args.declarations))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"κ failed: {error}", file=sys.stderr)
        sys.exit(1)
