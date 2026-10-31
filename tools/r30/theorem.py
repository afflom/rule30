"""Publish a Lean theorem on the LexLean surface: glossary entry, paper statement,
fast check, and a Lean probe that reproduces what `lexlean verify` will elaborate."""

from pathlib import Path
import re

from . import repo, leansig, sexpr, checks
from .convert import Converter, Unsupported, variables
from .lexicon import Lexicon

ALLOW = "\\allowaxioms{Quot.sound;propext}"


def slugify(lean_name):
    base = lean_name.split(".")[-1]
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "-", base).replace("_", "-").lower()
    return re.sub(r"-+", "-", s).strip("-")


def entry_toml(qid, category, signature, arity, lean_module, lean_name):
    pkg, id_ = qid.split("::")
    surface = id_.replace("-", "")
    if arity == 0:
        frame, render = "atom", f"(operator-name {surface})"
    else:
        slots = " (token comma) (space) ".join(f"(slot {i})" for i in range(arity))
        frame, render = "call", f"(seq (operator-name {surface}) (paren (seq {slots})))"
    return f'''spec = "lexlean/entry/1"
id = "{id_}"
category = "{category}"
signature = "{signature}"
surface_arity = {arity}
frame = "{frame}"

[denotation]
kind = "lean"
module = "{lean_module}"
name = "{lean_name}"

[[form]]
id = "{id_}"
channel = "math"
surface = "{surface}"
canonical_source = true
features = []

[render]
math = "{render}"
'''


def theorem_block(id_, package, statement, args, assumed=()):
    call = f"({', '.join([*args, *assumed])})" if (args or assumed) else ""
    assume = "".join(f"Assume \\({h}\\).\n" for h in assumed)
    return f'''\\begin{{theorem}}{{{id_}}}
{ALLOW}
{statement}
\\begin{{proof}}
{assume}Close the goal with \\(\\lexeme{{{package}::{id_}}}{call}\\).
\\end{{proof}}
\\end{{theorem}}

'''


def lean_module_of(lean_name, modules):
    """The research module whose namespace prefix matches the declaration."""
    best = ""
    for m in modules:
        ns = m  # module Rule30UOR.X declares Rule30UOR.X.*
        if lean_name.startswith(ns + ".") and len(ns) > len(best):
            best = ns
    return best or None


def prepare(lean_name, package, slug=None, lexicon=None, allow_existing=False):
    lx = lexicon or Lexicon()
    if package not in lx.lexicon_dir:
        raise Unsupported(f"unknown lexicon {package}; known: {lx.packages()}")
    sig = leansig.signatures([lean_name])[lean_name]
    if sig is None:
        raise Unsupported(f"Lean does not know `{lean_name}` (is the library built?)")
    conv = Converter(lx, package)
    term = conv.term(sig["type"])
    args = variables(term)
    # LexLean counts the binders of the outer pi group: when a theorem has no
    # variables, its leading hypotheses are the surface arguments, introduced
    # with `Assume` in the proof.
    assumed = [] if args or term.kind != "pi" else [n for n, _ in term.binders]
    id_ = slug or slugify(lean_name)
    qid = f"{package}::{id_}"
    if qid in lx.entries and not allow_existing:
        raise Unsupported(f"{qid} already exists ({lx.entries[qid].lean_name})")
    category = "proof-constant" if sig["kind"] == "theorem" else "function"
    if category == "function":
        # a definition's signature is its type; arity counts all binders
        args = [n for n, _ in term.binders] if term.kind == "pi" else []
    module = lean_module_of(lean_name, repo.research_modules())
    if module is None:
        raise Unsupported(f"cannot place `{lean_name}` in a research module")
    statement = conv.statement(term) + "." if category == "proof-constant" else None
    return {
        "qid": qid, "id": id_, "package": package, "lean": lean_name, "module": module,
        "kind": sig["kind"], "category": category, "args": args, "assumed": assumed,
        "signature": sexpr.dumps(term.lse()),
        "probe_type": conv.lean_type(term),
        "statement": statement,
        "entry_path": lx.lexicon_dir[package] / "entries" / f"{id_}.toml",
        "used": sorted(conv.used),
    }


def probe(prepared_list):
    """Elaborate `example : <type> := <name>` for each prepared item, as verify will."""
    lines = []
    for p in prepared_list:
        lines.append(f"example : {p['probe_type']} := {p['lean']}")
    out, errors = leansig._run("\n".join(lines))
    return errors


def add(lean_name, package, slug=None, target=None, dry_run=False):
    lx = Lexicon()
    p = prepare(lean_name, package, slug, lx, allow_existing=dry_run)
    files = lx.lex_tex_files(package)
    if p["category"] == "proof-constant":
        if target is None:
            target = next((f for f in files if f.name == "Observations.lex.tex"), files[-1])
        p["target"] = str(target)
    if dry_run:
        return p
    errs = probe([p])
    if errs:
        raise Unsupported("Lean probe failed; the statement would not verify:\n" + "\n".join(errs[:6]))
    entry = entry_toml(p["qid"], p["category"], p["signature"], len(p["args"]) + len(p["assumed"]),
                       p["module"], p["lean"])
    p["entry_path"].write_text(entry)
    if p["statement"]:
        text = Path(target).read_text()
        block = theorem_block(p["id"], package, p["statement"], p["args"], p["assumed"])
        i = text.rindex("\\end{section}")
        Path(target).write_text(text[:i] + block + text[i:])
    project = lx.lexicon_project[package]
    checks.lock(project)
    result = checks.check(project, [str(Path(target).relative_to(repo.PROJECTS[project]))] if p["statement"] else None)
    if not result["ok"]:
        # roll back the entry, the statement and the lock
        p["entry_path"].unlink(missing_ok=True)
        if p["statement"]:
            Path(target).write_text(text)
        checks.lock(project)
        raise Unsupported("lexlean check rejected the statement; rolled back:\n" +
                          "\n".join(result["diagnostics"][:6]))
    p["check"] = "ok"
    return p


def selfcheck(package="r30.observation", limit=None):
    """Regenerate every existing proof-constant of a lexicon from Lean and compare
    with the hand-written entry and statement. Returns mismatches."""
    import re as _re
    lx = Lexicon()
    entries = [e for e in lx.entries.values() if e.package == package and e.category == "proof-constant"
               and e.lean_name]
    if limit:
        entries = entries[:limit]
    sigs = leansig.signatures([e.lean_name for e in entries])
    texts = {f: f.read_text() for f in lx.lex_tex_files(package)}
    report = {"checked": 0, "signature_mismatch": [], "statement_mismatch": [], "unsupported": []}
    for e in entries:
        sig = sigs.get(e.lean_name)
        if sig is None:
            report["unsupported"].append((e.qid, "unknown to Lean"))
            continue
        conv = Converter(lx, package)
        try:
            term = conv.term(sig["type"])
            generated = sexpr.dumps(term.lse())
            statement = conv.statement(term) + "."
        except Unsupported as ex:
            report["unsupported"].append((e.qid, str(ex)))
            continue
        report["checked"] += 1
        old = sexpr.dumps(sexpr.parse(e.signature))
        if old != generated:
            kind = "names-only" if _canon(old) == _canon(generated) else "semantic"
            report["signature_mismatch"].append((e.qid, kind, old, generated))
        found = None
        for text in texts.values():
            m = _re.search(r"\\begin\{theorem\}\{" + _re.escape(e.id) + r"\}\n[^\n]*\n([^\n]*)\n", text)
            if m:
                found = m.group(1)
                break
        if found is not None and found.strip() != statement.strip():
            report["statement_mismatch"].append((e.qid, found, statement))
    return report


def _canon(signature):
    """Rename binders positionally so two signatures compare up to alpha."""
    node = sexpr.parse(signature)
    names = {}

    def walk(n):
        if isinstance(n, str):
            return n
        if n and n[0] in ("pi", "lam"):
            groups = []
            for kind, name, ty in n[1]:
                names[name] = f"v{len(names)}"
                groups.append([kind, names[name], walk(ty)])
            return [n[0], groups, walk(n[2])]
        if n and n[0] == "local":
            return ["local", names.get(n[1], n[1])]
        return [walk(x) for x in n]
    return sexpr.dumps(walk(node))


def unpublished(package="r30.observation", prefixes=("Rule30UOR",)):
    """Theorems with no lexeme, each with the converter's verdict: publishable
    (entry and statement generated) or the reason it is not."""
    lx = Lexicon()
    names = [n for n in leansig.theorems(prefixes) if not lx.for_lean(n)
             and not re.search(r"\.(eq_\d+|match_\d+|proof_\d+|_[a-z]+)$", n)]
    sigs = leansig.signatures(names) if names else {}
    rows = []
    for n in names:
        sig = sigs.get(n)
        if sig is None:
            continue
        conv = Converter(lx, package)
        try:
            term = conv.term(sig["type"])
            rows.append({"lean": n, "ok": True, "statement": conv.statement(term)[:160]})
        except Unsupported as ex:
            rows.append({"lean": n, "ok": False, "reason": str(ex)[:120]})
    return rows
