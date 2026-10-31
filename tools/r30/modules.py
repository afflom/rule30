"""Research modules: the Lean files under `rule30-core-lean/Rule30UOR`. A module
exists for the gate only once it is a Lake root and an import of the axiom
audit (`scripts/check_research_coverage.py` refuses anything else), so adding
one is a repository operation, not a hand edit of two files."""

import re

from . import repo

AUDIT = repo.CORE_LEAN / "scripts/CheckResearchAxioms.lean"
LAKEFILE = repo.CORE_LEAN / "lakefile.toml"

SKELETON = """module
public import Rule30UOR.Interfaces
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

@[expose] public section

namespace {name}

open Rule30UOR.Core

end {name}
"""


def qualify(name):
    name = name.strip()
    if not name.startswith("Rule30UOR."):
        name = "Rule30UOR." + name
    if not re.fullmatch(r"Rule30UOR(?:\.[A-Za-z_][A-Za-z_0-9]*)+", name):
        raise ValueError(f"not a module name: {name}")
    return name


def source_path(name):
    return repo.CORE_LEAN / (name.replace(".", "/") + ".lean")


def list_modules():
    return repo.research_modules()


def register(name, lakefile=LAKEFILE, audit=AUDIT, create=True):
    """Make `name` a build root and an axiom-audit import; create the source
    from the skeleton when it does not exist. Idempotent. Returns what changed."""
    name = qualify(name)
    changed = []
    path = source_path(name)
    if not path.exists():
        if not create:
            raise FileNotFoundError(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(SKELETON.format(name=name))
        changed.append("source")
    text = lakefile.read_text()
    m = re.search(r'(name = "Rule30UOR"\nroots = \[)(.*?)(\])', text, re.S)
    if not m:
        raise ValueError(f"{lakefile} has no Rule30UOR roots list")
    roots = [r.strip().strip('"') for r in m.group(2).split(",") if r.strip()]
    if name not in roots:
        roots.append(name)
        text = text[:m.start(2)] + ", ".join(f'"{r}"' for r in roots) + text[m.end(2):]
        lakefile.write_text(text)
        changed.append("lakefile")
    lines = audit.read_text().split("\n")
    pattern = re.compile(r"^import (Rule30UOR(?:\.[A-Za-z_][A-Za-z_0-9]*)+)\s*$")
    imported = [pattern.match(l).group(1) for l in lines if pattern.match(l)]
    if name not in imported:
        last = max(i for i, l in enumerate(lines) if pattern.match(l))
        lines.insert(last + 1, f"import {name}")
        audit.write_text("\n".join(lines))
        changed.append("audit")
    return {"module": name, "path": str(path), "changed": changed}


def build(names, timeout=3600):
    """`lake build` the modules (the research library when none are given).
    Returns (ok, output) where output keeps only errors."""
    names = [qualify(n) for n in names] or ["Rule30UOR"]
    code, out, err = repo.run(["lake", "build", *names], cwd=repo.CORE_LEAN, timeout=timeout)
    if code == 0:
        return True, ""
    kept, keep = [], False
    for line in (out + err).split("\n"):
        if line.startswith(("✖", "error", "warning")) or ": error:" in line:
            keep = "error" in line
        if keep:
            kept.append(line)
    return False, "\n".join(kept)
