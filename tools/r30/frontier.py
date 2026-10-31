"""The frontier register: the claims the research program is currently about,
with their status, Lean name and lexeme. `frontier.toml` is the machine-readable
counterpart of the prose in STRATEGY.md."""

from datetime import date
import tomllib

from . import repo

STATUSES = ("open", "proved", "refuted", "retired")


def load():
    if not repo.FRONTIER.exists():
        return {"claim": []}
    return tomllib.loads(repo.FRONTIER.read_text())


def _toml_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def save(data):
    lines = ["# The research frontier. Edit with `r30 frontier`; see STRATEGY.md for the prose.", ""]
    for c in data["claim"]:
        lines.append("[[claim]]")
        for key in ("id", "status", "statement", "lean", "lexeme", "since", "note"):
            if c.get(key):
                lines.append(f"{key} = {_toml_str(str(c[key]))}")
        if c.get("depends"):
            lines.append("depends = [" + ", ".join(_toml_str(d) for d in c["depends"]) + "]")
        lines.append("")
    repo.FRONTIER.write_text("\n".join(lines))


def list_claims(status=None):
    claims = load()["claim"]
    if status:
        claims = [c for c in claims if c["status"] == status]
    return claims


def add(id_, statement, status="open", lean=None, lexeme=None, note=None, depends=None):
    if status not in STATUSES:
        raise ValueError(f"status must be one of {STATUSES}")
    data = load()
    if any(c["id"] == id_ for c in data["claim"]):
        raise ValueError(f"claim {id_} exists")
    data["claim"].append({k: v for k, v in dict(
        id=id_, status=status, statement=statement, lean=lean, lexeme=lexeme,
        since=date.today().isoformat(), note=note, depends=depends).items() if v})
    save(data)
    return data["claim"][-1]


def update(id_, **fields):
    data = load()
    for c in data["claim"]:
        if c["id"] == id_:
            for k, v in fields.items():
                if v is None:
                    continue
                if k == "status" and v not in STATUSES:
                    raise ValueError(f"status must be one of {STATUSES}")
                c[k] = v
            save(data)
            return c
    raise ValueError(f"no claim {id_}")


def summary():
    claims = load()["claim"]
    counts = {s: sum(1 for c in claims if c["status"] == s) for s in STATUSES}
    return {"counts": counts, "open": [c["id"] for c in claims if c["status"] == "open"]}


def check(lexicon=None, leansig=None):
    """The register against the kernel. A claim may say `proved` only when its
    Lean name is kernel-checked under {propext, Quot.sound}; a `refuted` claim
    names the Lean refutation or the experiment; dependencies exist and no claim
    is `proved` while depending on an `open` one unless it is an equivalence or
    reduction (its statement says so). Returns a list of problems."""
    from . import leansig as _leansig
    from .lexicon import Lexicon
    leansig = leansig or _leansig
    lx = lexicon or Lexicon()
    claims = load()["claim"]
    ids = {c["id"] for c in claims}
    problems = []
    names = [c["lean"] for c in claims if c.get("lean")]
    axioms = leansig.axioms(names) if names else {}
    for c in claims:
        cid, st = c["id"], c["status"]
        if st not in STATUSES:
            problems.append(f"{cid}: unknown status {st}")
        for d in c.get("depends", []):
            if d not in ids:
                problems.append(f"{cid}: depends on unknown claim {d}")
        if c.get("lean"):
            ax = axioms.get(c["lean"])
            if ax is None:
                problems.append(f"{cid}: Lean does not know {c['lean']}")
            elif any(a not in ("propext", "Quot.sound") for a in ax):
                problems.append(f"{cid}: {c['lean']} depends on {ax}")
            if c.get("lexeme") and lx.get(c["lexeme"]) is None:
                problems.append(f"{cid}: no lexeme {c['lexeme']}")
            if not c.get("lexeme") and lx.for_lean(c["lean"]):
                c["lexeme"] = lx.for_lean(c["lean"]).qid
        if st == "proved" and not c.get("lean"):
            problems.append(f"{cid}: proved without a Lean name")
        if st == "proved" and c.get("lean") and not lx.for_lean(c["lean"]):
            problems.append(f"{cid}: proved but unpublished ({c['lean']} has no lexeme)")
        if st == "refuted" and not (c.get("lean") or "experiments/" in (c.get("note") or "")):
            problems.append(f"{cid}: refuted without a Lean refutation or an experiment")
    try:
        current, _ = render_file(check_only=True)
        if not current:
            problems.append("Frontier.lex.tex is stale; run `bin/r30 frontier render`")
    except Exception as ex:  # the render itself refused
        problems.append(f"Frontier.lex.tex cannot be rendered: {ex}")
    return problems


FRONTIER_TEX = repo.PROJECTS["paper"] / "src/Frontier.lex.tex"
SECTIONS = (("proved", "frontier-proved"), ("refuted", "frontier-refuted"))


def render(lexicon=None, leansig=None):
    """The frontier as a LexLean module: every proved or refuted claim whose Lean
    theorem is published is restated as a theorem block generated from Lean and
    closed by its lexeme, so `lexlean verify` checks the register's content.
    Returns (text, skipped) where skipped lists claims that have no published
    proof-constant to restate."""
    from . import leansig as _leansig, sexpr
    from .convert import Converter, variables
    from .lexicon import Lexicon
    from .theorem import theorem_block, ALLOW
    leansig = leansig or _leansig
    lx = lexicon or Lexicon()
    claims = load()["claim"]
    wanted = [c for c in claims if c["status"] in dict(SECTIONS) and c.get("lean")]
    sigs = leansig.signatures([c["lean"] for c in wanted]) if wanted else {}
    blocks = {status: [] for status, _ in SECTIONS}
    packages, skipped = set(), []
    for c in wanted:
        e = lx.for_lean(c["lean"])
        sig = sigs.get(c["lean"])
        if e is None or e.category != "proof-constant" or sig is None:
            skipped.append(c["id"])
            continue
        conv = Converter(lx, e.package)
        term = conv.term(sig["type"])
        args = variables(term)
        assumed = [] if args or term.kind != "pi" else [n for n, _ in term.binders]
        packages |= {lx.get(q).package for q in conv.used} | {e.package}
        blocks[c["status"]].append(theorem_block("claim-" + c["id"], e.package, conv.statement(term) + ".",
                                                 args, assumed).replace(
            "\\lexeme{" + e.package + "::claim-" + c["id"] + "}", "\\lexeme{" + e.qid + "}"))
    closure = set()
    for p in packages:
        closure |= lx.visible_from(p)
    closure.discard("lexlean.core")
    closure.add("r30.doc")
    lines = ["\\begin{lexlean}{Frontier}"]
    for p in sorted(closure):
        version = "1.2.0" if p.startswith("lexlean.std") else "1.0.0"
        lines.append(f"\\useglossary{{{p}@{version}}}")
    lines += ["\\title{Frontier}", ""]
    for status, label in SECTIONS:
        title = {"proved": "Proved reductions", "refuted": "Refuted routes"}[status]
        lines += [f"\\begin{{section}}{{{label}}}", f"\\heading{{{title}}}", ""]
        lines += [b.rstrip("\n") + "\n" for b in blocks[status]]
        lines += ["\\end{section}", ""]
    lines.append("\\end{lexlean}")
    return "\n".join(lines).replace("\n\n\n", "\n\n") + "\n", skipped


def render_file(check_only=False):
    """Write Frontier.lex.tex (or report whether it is current)."""
    text, skipped = render()
    current = FRONTIER_TEX.read_text() if FRONTIER_TEX.exists() else ""
    if check_only:
        return current == text, skipped
    if current != text:
        FRONTIER_TEX.write_text(text)
        from . import checks
        checks.lock("paper")
    return True, skipped
