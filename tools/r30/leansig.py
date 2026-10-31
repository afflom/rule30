"""Ask Lean about declarations: their types as s-expressions, their axioms,
and which theorems depend on `Classical.choice`. One `lake env lean` run per
call; the research library must already be built."""

from pathlib import Path
import hashlib

from . import repo, sexpr

TEMPLATE = Path(__file__).with_name("leansig.lean.tmpl")


def _run(commands, package_dir=repo.CORE_LEAN, modules=None, timeout=1800):
    modules = modules or repo.research_modules()
    text = TEMPLATE.read_text().replace("__IMPORTS__", "".join(f"import {m}\n" for m in modules)) \
        .replace("__COMMANDS__", commands)
    name = "q" + hashlib.sha256(text.encode()).hexdigest()[:12] + ".lean"
    path = repo.scratch_dir() / name
    path.write_text(text)
    try:
        code, out, err = repo.run(["lake", "env", "lean", str(path)], cwd=package_dir,
                                  timeout=timeout)
    finally:
        path.unlink(missing_ok=True)
    errors = [l for l in (out + err).splitlines() if ": error" in l or l.startswith("error")]
    return out, errors


def signatures(names, **kw):
    """{name: {"kind": ..., "type": <sexpr node>}} for each declaration name."""
    out, errors = _run("#r30sig " + " ".join(names), **kw)
    result = {}
    for line in out.splitlines():
        if not line.startswith("SIG "):
            continue
        _, name, rest = line.split(" ", 2)
        if rest == "unknown":
            result[name] = None
        else:
            kind, sx = rest.split(" ", 1)
            result[name] = {"kind": kind, "type": sexpr.parse(sx)}
    for n in names:
        result.setdefault(n, None)
    if errors and not any(result.values()):
        raise RuntimeError("\n".join(errors[:5]))
    return result


def axioms(names, **kw):
    out, _ = _run("#r30axioms " + " ".join(names), **kw)
    result = {}
    for line in out.splitlines():
        if line.startswith("AXIOMS "):
            _, name, rest = line.split(" ", 2)
            result[name] = None if rest == "unknown" else \
                [a.strip() for a in rest.strip("[]").split(",") if a.strip()]
    return result


def choice_users(prefixes=("Rule30UOR",), **kw):
    out, _ = _run("#r30choice " + " ".join(prefixes), **kw)
    return sorted(line.split(" ", 2)[2] for line in out.splitlines() if line.startswith("CHOICE "))


def theorems(prefixes=("Rule30UOR",), **kw):
    """Public theorem names under the module prefixes."""
    out, _ = _run("#r30decls " + " ".join(prefixes), **kw)
    return sorted(line.split(" ", 1)[1] for line in out.splitlines() if line.startswith("DECL "))
