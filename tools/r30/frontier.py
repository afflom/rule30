"""The frontier register: the claims the research program is currently about,
with their status, Lean name and lexeme. `frontier.toml` is the machine-readable
counterpart of the prose in STRATEGY.md."""

from datetime import date
import tomllib

from . import repo

STATUSES = ("open", "proved", "refuted", "retired", "observed")
# An `observed` claim is a relation certified on a window by `bin/r30
# discover` (induction), not yet deduced: it carries `relation` (the column
# ids of Sequences.lex.tex whose XOR vanishes, `discoverymodel.parse_column`),
# `window` (the number of times) and `kappa` (the relation's κ-label).
# `frontier check` re-validates it against the committed windows, and the
# path to `proved` is the usual one (a Lean theorem, `frontier set --status
# proved --lean`). A proved claim may carry a `relation` too: the window
# relation its theorem implies, checked the same way.


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
        if c.get("relation"):
            lines.append("relation = [" + ", ".join(_toml_str(d) for d in c["relation"]) + "]")
        if c.get("window"):
            lines.append(f"window = {int(c['window'])}")
        if c.get("kappa"):
            lines.append(f"kappa = {_toml_str(c['kappa'])}")
        lines.append("")
    repo.FRONTIER.write_text("\n".join(lines))


def list_claims(status=None):
    claims = load()["claim"]
    if status:
        claims = [c for c in claims if c["status"] == status]
    return claims


MARKS = {"open": "?", "proved": "✓", "refuted": "✗", "retired": "-", "observed": "~"}


def chain():
    """The reduction tree: from each root claim, the claims that rest on it
    (`depends`), with status and Lean name. Returns (rows, text): the rows are
    the pre-order walk with depth, the text is the indented rendering."""
    claims = load()["claim"]
    by_id = {c["id"]: c for c in claims}
    children = {c["id"]: [] for c in claims}
    for c in claims:
        for d in c.get("depends", []):
            children.setdefault(d, []).append(c["id"])
    roots = [c["id"] for c in claims if not c.get("depends")]
    lines, rows = [], []

    def walk(cid, depth, seen):
        c = by_id[cid]
        rows.append({"id": cid, "depth": depth, "status": c["status"], "lean": c.get("lean")})
        lines.append("  " * depth + f"[{MARKS[c['status']]}] {cid}" + (f"  ({c['lean']})" if c.get("lean") else ""))
        if cid in seen:
            return
        for k in children.get(cid, []):
            walk(k, depth + 1, seen | {cid})
    for r in roots:
        walk(r, 0, set())
    lines.append("")
    lines.append("open leaves are sufficient conditions once every proved arrow above them is read upward;")
    lines.append("a refuted node is a route not to be walked again.")
    return rows, "\n".join(lines)


def open_leaves():
    """The open claims no claim rests on: the sufficient conditions of the tree."""
    claims = load()["claim"]
    depended = {d for c in claims for d in c.get("depends", [])}
    return [c["id"] for c in claims if c["status"] == "open" and c["id"] not in depended]


def relation_kappa(relation):
    """The κ-label of a relation over the committed basis (Sequences.lex.tex)."""
    from . import discoverymodel, sequencemodel
    data = sequencemodel.load()
    if data is None:
        raise ValueError("a relation needs the basis: run `bin/r30 sequences --write`")
    try:
        return discoverymodel.relation_kappa(relation, discoverymodel.kappas_of(data))
    except (KeyError, ValueError) as e:
        raise ValueError(f"the relation names a column outside the basis: {e}")


def _relation_fields(status, relation, window, kappa):
    """Complete and validate the relation fields of a claim."""
    if status == "observed" and not relation:
        raise ValueError("an observed claim carries a relation (--relation)")
    if not relation:
        return {}
    from . import discoverymodel, sequencemodel
    data = sequencemodel.load()
    k = relation_kappa(relation)
    if kappa and kappa != k:
        raise ValueError(f"the κ-label {kappa} is not the label of the relation ({k})")
    return {"relation": list(relation), "window": int(window or discoverymodel.discovery_width(data)), "kappa": k}


def add(id_, statement, status="open", lean=None, lexeme=None, note=None, depends=None, relation=None, window=None,
        kappa=None):
    if status not in STATUSES:
        raise ValueError(f"status must be one of {STATUSES}")
    data = load()
    if any(c["id"] == id_ for c in data["claim"]):
        raise ValueError(f"claim {id_} exists")
    extra = _relation_fields(status, relation, window, kappa)
    data["claim"].append({k: v for k, v in dict(
        id=id_, status=status, statement=statement, lean=lean, lexeme=lexeme,
        since=date.today().isoformat(), note=note, depends=depends, **extra).items() if v})
    save(data)
    return data["claim"][-1]


def update(id_, **fields):
    data = load()
    for c in data["claim"]:
        if c["id"] == id_:
            relation, window = fields.pop("relation", None), fields.pop("window", None)
            for k, v in fields.items():
                if v is None:
                    continue
                if k == "status" and v not in STATUSES:
                    raise ValueError(f"status must be one of {STATUSES}")
                c[k] = v
            if relation is not None or window is not None:
                c.update(_relation_fields(c["status"], relation or c.get("relation"), window or c.get("window"), None))
            elif c["status"] == "observed" and not c.get("relation"):
                raise ValueError("an observed claim carries a relation (--relation)")
            save(data)
            return c
    raise ValueError(f"no claim {id_}")


def relation_problems(claims=None, data=None):
    """The relations of the register against the committed windows: an
    observed claim carries a relation, a window and its κ-label; every
    relation names columns of the basis, has the κ-label of its columns, and
    its columns XOR to zero on its window."""
    from . import discoverymodel as dm, sequencemodel
    claims = load()["claim"] if claims is None else claims
    with_relation = [c for c in claims if c.get("relation") or c["status"] == "observed"]
    if not with_relation:
        return []
    data = sequencemodel.load() if data is None else data
    if data is None or sequencemodel.problems(data):
        return ["claims carry relations but model/sequences.toml is missing or inconsistent"]
    index, bases, kappas = dm.index_of(data), dm.bases_of(data), dm.kappas_of(data)
    problems = []
    for c in with_relation:
        cid, rel = c["id"], c.get("relation") or []
        if c["status"] == "observed" and not (rel and c.get("window") and c.get("kappa")):
            problems.append(f"{cid}: observed without a relation, a window and a κ-label")
            continue
        try:
            specs = [dm.column_spec(x, index) for x in rel]
            k = dm.relation_kappa(rel, kappas)
        except (KeyError, ValueError) as e:
            problems.append(f"{cid}: the relation names a column outside the basis ({e})")
            continue
        if c.get("kappa") and c["kappa"] != k:
            problems.append(f"{cid}: the κ-label is not the label of its relation")
        width = int(c.get("window") or dm.discovery_width(data))
        if width <= 0 or width % dm.CHUNK_BITS or 2 * width > data["window"]:
            problems.append(f"{cid}: the window {width} does not fit the stored window {data['window']}")
            continue
        acc = []
        for w in dm.Mirror.build_columns(width, bases, specs):
            acc = dm.Mirror.xor_word(w, acc)
        if sum(acc):
            problems.append(f"{cid}: its relation does not vanish on t < {width}")
    return problems


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
    problems += relation_problems(claims)
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
    unknown = [c["lean"] for c in wanted if sigs.get(c["lean"]) is None]
    if unknown:
        raise RuntimeError("Lean does not know " + ", ".join(unknown) +
                           " (is rule30-core-lean built?); the frontier cannot be rendered")
    blocks = {status: [] for status, _ in SECTIONS}
    packages, skipped = set(), []
    for c in wanted:
        e = lx.for_lean(c["lean"])
        sig = sigs.get(c["lean"])
        if e is None or e.category != "proof-constant":
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
