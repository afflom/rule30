"""Research modules: the Lean files under `rule30-core-lean/Rule30UOR`. A module
exists for the gate only once it is a Lake root and an import of the axiom
audit (`scripts/check_research_coverage.py` refuses anything else), so adding
one is a repository operation, not a hand edit of two files."""

import hashlib
import re
import time

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


# `Rule30UOR.Core` imports `LexLeanRuntime.Laws`, which no Lake root covers (the LexLeanRuntime
# library's roots are Portable and Collections), so `lake build` never compiles it. The Makefile's
# `core` recipe, which the gate runs, compiles it by hand between `lake build LexLeanRuntime` and
# `lake build`; `build` does the same, so a build from an empty `.lake` (a fresh clone, a runner
# with a cold cache) succeeds as the gate's does.
LAWS_SOURCE = "LexLeanRuntime/Laws.lean"
LAWS_OUTPUT = ".lake/build/lib/lean/LexLeanRuntime"
LAWS_INPUTS = ("lean-toolchain", "LexLeanRuntime/Portable.lean", "LexLeanRuntime/Collections.lean", LAWS_SOURCE)


def laws_digest():
    """What `LexLeanRuntime.Laws` is compiled from: its source, the runtime modules it imports and
    the toolchain (the stamp beside its outputs)."""
    h = hashlib.sha256()
    for rel in LAWS_INPUTS:
        path = repo.CORE_LEAN / rel
        h.update(rel.encode() + b"\0" + (path.read_bytes() if path.exists() else b"") + b"\0")
    return h.hexdigest()


def build_laws(timeout=3600):
    """Compile `LexLeanRuntime.Laws` as the Makefile's `core` recipe does, unless its outputs carry
    the stamp of its current inputs. Returns (ok, errors); raises subprocess.TimeoutExpired."""
    out = repo.CORE_LEAN / LAWS_OUTPUT
    stamp = out / "Laws.r30-inputs"
    want = laws_digest()
    if (out / "Laws.olean").exists() and (out / "Laws.ilean").exists() and stamp.exists() \
            and stamp.read_text().strip() == want:
        return True, ""
    deadline = time.time() + timeout
    # the stamp vouches for complete outputs only: drop it before anything is rewritten
    if stamp.exists():
        stamp.unlink()
    code, o, e = repo.run(["lake", "build", "LexLeanRuntime"], cwd=repo.CORE_LEAN, timeout=timeout, group=True)
    if code != 0:
        return False, errors_of(o + e)
    out.mkdir(parents=True, exist_ok=True)
    code, o, e = repo.run(["lake", "env", "lean", "-R", ".", "-o", f"{LAWS_OUTPUT}/Laws.olean", "-i", f"{LAWS_OUTPUT}/Laws.ilean",
                           LAWS_SOURCE], cwd=repo.CORE_LEAN, timeout=max(1, int(deadline - time.time())), group=True)
    if code != 0:
        return False, errors_of(o + e)
    stamp.write_text(want + "\n")
    return True, ""


def errors_of(text):
    """The error blocks of a Lake or Lean run (a block ends at the next built module), else its tail."""
    kept, keep = [], False
    for line in text.split("\n"):
        if line.startswith(("✖", "error", "warning")) or ": error:" in line:
            keep = "error" in line
        elif line.startswith(("✔", "⚠", "ℹ")):
            keep = False
        if keep:
            kept.append(line)
    return "\n".join(kept).strip("\n") or text.strip()[-1500:]


def build(names, timeout=3600):
    """`lake build` the modules (the research library when none are given), after
    `LexLeanRuntime.Laws` (`build_laws`). Returns (ok, output) where output keeps only errors;
    raises subprocess.TimeoutExpired when the build outlasts `timeout` seconds."""
    names = [qualify(n) for n in names] or ["Rule30UOR"]
    deadline = time.time() + timeout
    ok, errors = build_laws(timeout)
    if not ok:
        return False, "LexLeanRuntime.Laws: " + errors
    code, out, err = repo.run(["lake", "build", *names], cwd=repo.CORE_LEAN, timeout=max(1, int(deadline - time.time())),
                              group=True)
    if code == 0:
        return True, ""
    return False, errors_of(out + err)
