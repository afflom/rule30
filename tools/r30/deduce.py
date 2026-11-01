"""`bin/r30 deduce`: deduction mechanized, the third phase of the engine.

Induction (`bin/r30 discover --write`) leaves `observed` claims in the
register: relations among the columns of the basis (`Sequences.lex.tex` and
its transforms `shift:`, `even:`, `odd:`) whose XOR vanishes on a window.
Deduction tries to prove each one for every time with a fixed portfolio of
deterministic Lean proof templates (`enginemodel.PORTFOLIO`, each pinned by
the SHA-256 of its template file under `tools/r30/templates/`), in the order
the learned weights choose (`enginemodel.schedule`):

- `period-reduction`: every column is a word of the right system
  (`towerWord j = rdiag j`, exactly `2^j`-periodic, read from the row
  register by `Antidiagonal.towerWord_eq_row`), so the relation depends on
  `t` modulo the largest period only and the kernel decides the residues;
- `library-rewrite`: the columns are rewritten into the diagonals, one step
  of the rule unfolds definitionally, the library's equalities among the
  involved constants (`leansig.mentions`, the register's proved relations)
  are instantiated, and the relation closes by Boolean case analysis; a
  library theorem that states the relation itself proves the claim with no
  new theorem (the redundancy rule: one proof per statement);
- `step-induction`: the diagonals the relation reads (`rdiag 0..J`,
  `ldiag 0..D`, at `t` and at `2t` for the dilations) form a finite system
  stepped by the rule (`Core.rdiag_step`, `Core.ldiag_step`); by induction on
  the time its state stays in the orbit the kernel decides, and the relation
  holds on every state of the orbit;
- `counterexample`: when the orbit shows a time where the relation fails
  (beyond the window it was observed on), the kernel decides the failure at
  that time and the claim becomes `refuted`.

Every attempt renders one theorem into a scratch file under `.r30/deduce/`,
checks it with one Lean process (`lake env lean -j 1`, the library already
built), and accepts it only when `#print axioms` names nothing beyond
`propext` and `Quot.sound`. A proved theorem is appended to the engine's
module `Rule30UOR.Deduced`, built, refused if it states what a library
theorem states (`kappa --duplicates`: the existing theorem then proves the
claim), published (`theorem add`) and recorded (`frontier set --status
proved --lean`). Every attempt (claim κ, strategy, template digest,
outcome, failure point, seconds) goes into the engine ledger
(`model/engine.toml`, `engine.py`), and no (claim, strategy, template
digest) is attempted twice. The finite systems are decided exactly in
Python first (the orbit of the diagonals from time 0): a template whose
Boolean core fails there is recorded as failed without running Lean."""

import re
import time
from itertools import product

from . import discoverymodel as dm, enginemodel as em, frontier, repo, sequencemodel

DEDUCED = "Rule30UOR.Deduced"
DEDUCED_PATH = repo.CORE_LEAN / "Rule30UOR" / "Deduced.lean"
SCRATCH = "deduce"
# The modules every template reads (rdiag, ldiag, the words, the exposed masks, the time parity,
# rdiag_zero_all, row_testBit, towerWord_eq_row).
BASE_IMPORTS = ["Rule30UOR.Antidiagonal"]
TIMES = {"base": ("t", lambda t: t), "shift": ("t + 1", lambda t: t + 1),
         "even": ("2 * t", lambda t: 2 * t), "odd": ("2 * t + 1", lambda t: 2 * t + 1)}
# The basis columns of the finite systems: the right diagonals (and what is read through
# them) and the left diagonals. Everything else (the center, the cells, the cones) is an
# opaque atom that only library facts can relate.
FINITE = ("one", "time-parity", "rdiag", "tower-word", "exposed", "ldiag")


class Unprovable(RuntimeError):
    """A template's applicability fails for this relation (a reason, not an attempt)."""


# ---------------------------------------------------------------- columns

def base_of(cid):
    """`exposed(3)` -> ("exposed", 3); `center` -> ("center", None)."""
    m = re.fullmatch(r"([a-z-]+)(?:\((-?\d+)\))?", cid)
    if not m:
        raise ValueError(f"not a basis id: {cid}")
    return m.group(1), (int(m.group(2)) if m.group(2) is not None else None)


def columns(relation):
    """[(transform, family, parameter)] of a relation's column ids (no `and:` columns)."""
    out = []
    for cid in relation:
        transform, ids = dm.parse_column(cid)
        if transform == "and":
            out.append(("and", ids, None))
            continue
        fam, p = base_of(ids[0])
        out.append((transform, fam, p))
    return out


_LEAN = {f["family"]: f["lean"].replace("Rule30UOR.", "") for f in sequencemodel.FAMILIES}


def term(fam, p, x):
    """The Lean term of a basis column at the time `x` (a string)."""
    if fam == "one":
        return "true"
    if fam == "cell":
        return f"Core.cell ({x}) ({p})"
    if p is None:
        return f"{_LEAN[fam]} ({x})"
    return f"{_LEAN[fam]} {p} ({x})"


def column_term(col, t="t"):
    transform, fam, p = col
    if transform == "and":
        a, b = (base_of(i) for i in fam)
        return f"({term(*a, t)} && {term(*b, t)})"
    x = TIMES[transform][0].replace("t", t) if not t.isdigit() else str(TIMES[transform][1](int(t)))
    return term(fam, p, x)


def statement(relation, t="t"):
    """`dependent = XOR of the others` (the last column is the dependent one, as the engine
    expresses it through the earlier independent columns); `one` negates."""
    cols = columns(relation)
    dep, rest = cols[-1], cols[:-1]
    negate = sum(1 for c in rest if c[1] == "one") % 2 == 1
    terms = [column_term(c, t) for c in rest if c[1] != "one"]
    if not terms:
        rhs = "true" if negate else "false"
    else:
        rhs = terms[0]
        for x in terms[1:]:
            rhs = f"Core.bxor ({rhs}) ({x})"
        if negate:
            rhs = f"!({rhs})"
    return f"{column_term(dep, t)} = {rhs}"


def _slug(col):
    transform, fam, p = col
    if transform == "and":
        return "and_" + "_".join(re.sub(r"\W", "", x) for x in fam)
    base = {"one": "true", "time-parity": "timeParity"}.get(fam, re.sub(r"-(\w)", lambda m: m.group(1).upper(), fam))
    base += "" if p is None else (str(p) if p >= 0 else f"m{-p}")
    return base + {"base": "", "shift": "_succ", "even": "_even", "odd": "_odd"}[transform]


def theorem_name(relation, kappa):
    cols = columns(relation)
    rest = [c for c in cols[:-1] if c[1] != "one"]
    negate = sum(1 for c in cols[:-1] if c[1] == "one") % 2 == 1
    rhs = "_xor_".join(_slug(c) for c in rest) or ("true" if negate else "false")
    if rest and negate:
        rhs = "not_" + rhs
    name = f"{_slug(cols[-1])}_eq_{rhs}"
    if len(name) > 64:
        name = "relation_" + kappa[len("sha256:"):][:12]
    return name


# ------------------------------------------------- the finite systems, exactly

def needs(relation):
    """(J, D, plain, dilated): the right and left diagonals the relation reads (-1: none), and
    whether it reads the time t (base, shift) and the time 2t (even, odd)."""
    J = D = -1
    plain = dilated = False
    for transform, fam, p in columns(relation):
        if transform == "and" or fam not in FINITE:
            raise Unprovable(f"{fam if transform != 'and' else 'an AND column'} is not a column of the finite systems")
        if fam == "time-parity":
            J = max(J, 1)
        elif fam in ("rdiag", "tower-word"):
            J = max(J, p)
        elif fam == "exposed":
            J = max(J, p + 1)
        elif fam == "ldiag":
            D = max(D, p)
        plain |= transform in ("base", "shift")
        dilated |= transform in ("even", "odd")
    return J, D, plain, dilated


def step(J, D, x):
    """One step of the rule on the state [rdiag 0..J, ldiag 0..D] (Core.rdiag_step, Core.ldiag_step)."""
    r, l = x[:J + 1], x[J + 1:]
    out = []
    for j in range(J + 1):
        out.append(True if j == 0 else (not r[1]) if j == 1 else r[j] ^ (r[j - 1] or r[j - 2]))
    for d in range(D + 1):
        out.append(True if d <= 1 else l[d - 2] ^ (l[d - 1] or l[d]))
    return out


def initial(J, D):
    return [j == 0 for j in range(J + 1)] + [d == 0 for d in range(D + 1)]


def read(col, J, a, b):
    """The value of a column given the state a = state(t) (b = state(2t))."""
    transform, fam, p = col
    x = {"base": a, "shift": None, "even": b, "odd": None}[transform]
    if transform == "shift":
        x = step(J, len(a) - J - 2, a)
    if transform == "odd":
        x = step(J, len(b) - J - 2, b)
    if fam == "one":
        return True
    if fam == "time-parity":
        return x[1]
    if fam in ("rdiag", "tower-word"):
        return x[p]
    if fam == "exposed":
        return x[p] and not x[p + 1]
    return x[J + 1 + p]


def orbit(relation, limit=4096):
    """The joint orbit of (state(t), state(2t)) from t = 0 until it repeats, as a list of states
    (each the concatenation of the parts the relation reads), the first time the relation fails
    on it (None when it holds on the whole orbit, hence for all t), and the layout."""
    J, D, plain, dilated = needs(relation)
    cols = columns(relation)
    a = b = initial(J, D)
    seen, states, fail = {}, [], None
    t = 0
    while True:
        key = tuple((a if plain else []) + (b if dilated else []))
        if key in seen:
            break
        seen[key] = t
        states.append(list(key))
        value = False
        for c in cols:
            value ^= read(c, J, a, b)
        if value and fail is None:
            fail = t
        a = step(J, D, a)
        b = step(J, D, step(J, D, b))
        t += 1
        if t > limit:
            raise Unprovable(f"the orbit of the diagonals exceeds {limit} states")
    return {"states": states, "fail": fail, "J": J, "D": D, "plain": plain, "dilated": dilated}


# ------------------------------------------------------- Lean text pieces

def _b(v):
    return "true" if v else "false"


def _list(xs):
    return "[" + ", ".join(xs) + "]"


def state_terms(J, D, x):
    return [f"Core.rdiag {j} ({x})" for j in range(J + 1)] + [f"Core.ldiag {d} ({x})" for d in range(D + 1)]


def step_lambda(J, D, n, parts):
    """`fun x => ...`: one step on each part (the plain part once, the dilated part twice)."""
    def one(off, get):
        out = []
        for j in range(J + 1):
            out.append("true" if j == 0 else f"!({get(off + 1)})" if j == 1 else
                       f"Core.bxor ({get(off + j)}) ({get(off + j - 1)} || {get(off + j - 2)})")
        for d in range(D + 1):
            k = off + J + 1 + d
            out.append("true" if d <= 1 else f"Core.bxor ({get(k - 2)}) ({get(k - 1)} || {get(k)})")
        return out
    g = lambda i: f"x.getD {i} false"
    body = []
    for idx, part in enumerate(parts):
        off = idx * n
        if part == "plain":
            body += one(off, g)
        else:  # two steps: the inner step's entries substituted into the outer one
            inner = one(off, g)
            body += one(off, lambda i, inner=inner, off=off: f"({inner[i - off]})")
    return "fun x => " + _list(body)


def occurrence_equations(occ, prefix="o"):
    """Level 1: each occurrence (family, parameter, time text) of a column read through the
    diagonals, as `have` lines; returns (lines, names)."""
    lines, names = [], []
    for i, (fam, p, x) in enumerate(occ):
        name = f"{prefix}{i}"
        if fam == "time-parity":
            lines.append(f"  have {name} : EdgeParity.timeParity ({x}) = Core.rdiag 1 ({x}) := by\n"
                         f"    rw [Antidiagonal.rdiag_eq_towerWord, Antidiagonal.towerWord_one]")
        elif fam == "tower-word":
            lines.append(f"  have {name} : Antidiagonal.towerWord {p} ({x}) = Core.rdiag {p} ({x}) :=\n"
                         f"    (Antidiagonal.rdiag_eq_towerWord {p} ({x})).symm")
        elif fam == "exposed":
            lines.append(f"  have {name} : Antidiagonal.exposed {p} ({x}) = (Core.rdiag {p} ({x}) && !Core.rdiag {p + 1} ({x})) := by\n"
                         f"    show (Antidiagonal.towerWord {p} ({x}) && !Antidiagonal.towerWord {p + 1} ({x})) = _\n"
                         f"    rw [← Antidiagonal.rdiag_eq_towerWord, ← Antidiagonal.rdiag_eq_towerWord]")
        else:
            continue
        names.append(name)
    return lines, names


def occurrences(relation, t="t"):
    """The (family, parameter, time text) of the columns read through the diagonals."""
    out = []
    for transform, fam, p in columns(relation):
        if transform == "and" or fam not in ("time-parity", "tower-word", "exposed"):
            continue
        x = TIMES[transform][0].replace("t", t) if not t.isdigit() else str(TIMES[transform][1](int(t)))
        if (fam, p, x) not in out:
            out.append((fam, p, x))
    return out


def atom_expr(col, J, D, unfold):
    """A column at its time in the atoms rdiag/ldiag (unfolded one step for shift and odd when
    `unfold`), as Lean text and as a function of the atom values."""
    transform, fam, p = col
    if fam == "one":
        return "true"
    base_t = {"base": "t", "shift": "t", "even": "2 * t", "odd": "2 * t"}[transform]
    stepped = transform in ("shift", "odd")

    def r(j):
        if not stepped or not unfold:
            x = base_t if not stepped else ("t + 1" if transform == "shift" else "2 * t + 1")
            return f"Core.rdiag {j} ({x})"
        if j == 0:
            return "true"
        if j == 1:
            return f"!(Core.rdiag 1 ({base_t}))"
        return f"Core.bxor (Core.rdiag {j} ({base_t})) (Core.rdiag {j - 1} ({base_t}) || Core.rdiag {j - 2} ({base_t}))"

    def l(d):
        if not stepped or not unfold:
            x = base_t if not stepped else ("t + 1" if transform == "shift" else "2 * t + 1")
            return f"Core.ldiag {d} ({x})"
        if d <= 1:
            return "true"
        return f"Core.bxor (Core.ldiag {d - 2} ({base_t})) (Core.ldiag {d - 1} ({base_t}) || Core.ldiag {d} ({base_t}))"
    if fam == "time-parity":
        return r(1)
    if fam in ("rdiag", "tower-word"):
        return r(p)
    if fam == "exposed":
        return f"({r(p)} && !({r(p + 1)}))"
    return l(p)


def normal_goal(relation, J=None, D=None, unfold=True, opaque=None):
    """The goal over the atoms: dependent = XOR of the others, columns in atom form."""
    cols = columns(relation)

    def expr(c):
        if c[0] == "and" or c[1] not in FINITE:
            return column_term(c)
        return atom_expr(c, J, D, unfold)
    dep, rest = cols[-1], cols[:-1]
    negate = sum(1 for c in rest if c[1] == "one") % 2 == 1
    terms = [expr(c) for c in rest if c[1] != "one"]
    rhs = ("true" if negate else "false") if not terms else terms[0]
    for x in terms[1:]:
        rhs = f"Core.bxor ({rhs}) ({x})"
    if terms and negate:
        rhs = f"!({rhs})"
    return f"{expr(dep)} = {rhs}"


# ----------------------------------------------------------- the templates

def template_text(strategy):
    return em.template_path(strategy).read_text()


def fill(text, **slots):
    for k, v in slots.items():
        text = text.replace("{{" + k + "}}", v)
    left = re.findall(r"\{\{(\w+)\}\}", text)
    if left:
        raise ValueError(f"unfilled template slots: {left}")
    return "\n".join(line for line in text.splitlines() if line.strip() != "") + "\n"


def doc_of(claim, strategy):
    return (f"Deduced by bin/r30 deduce from the observed claim {claim['id']} (strategy {strategy}, "
            f"template {em.template_digest(strategy)[:19]}).")


def _body(text):
    """The theorem without the template's leading comment lines."""
    lines = text.splitlines()
    while lines and lines[0].startswith("--"):
        lines.pop(0)
    return "\n".join(lines) + "\n"


def render_step_induction(claim, name):
    rel = claim["relation"]
    o = orbit(rel)
    if o["fail"] is not None:
        raise Unprovable(f"the relation fails at t = {o['fail']} (a counterexample, not a proof)")
    if len(o["states"]) > em.ORBIT_BOUND:
        raise Unprovable(f"the orbit has {len(o['states'])} states (bound {em.ORBIT_BOUND})")
    J, D = o["J"], o["D"]
    parts = (["plain"] if o["plain"] else []) + (["dilated"] if o["dilated"] else [])
    n = J + D + 2
    occ_lines, occ_names = occurrence_equations(occurrences(rel))
    x_of = {"plain": "s", "dilated": "2 * s"}
    state_s = _list([x for part in parts for x in state_terms(J, D, x_of[part])])
    succ_of = {"plain": "s + 1", "dilated": "2 * s + 1 + 1"}
    state_succ = _list([x for part in parts for x in state_terms(J, D, succ_of[part])])
    reach = _list([_list([_b(v) for v in st]) for st in o["states"]])
    stp = step_lambda(J, D, n, parts)
    # the relation on a state x: every column read from its part (shift and odd one step on)
    off = {p: i * n for i, p in enumerate(parts)}

    def get(col):
        transform, fam, p = col
        part = "plain" if transform in ("base", "shift") else "dilated"
        stepped = transform in ("shift", "odd")
        base = off[part]

        def at(i):
            if not stepped:
                return f"x.getD {base + i} false"
            if i < J + 1:
                j = i
                return ("true" if j == 0 else f"!(x.getD {base + 1} false)" if j == 1 else
                        f"Core.bxor (x.getD {base + j} false) (x.getD {base + j - 1} false || x.getD {base + j - 2} false)")
            d = i - J - 1
            k = base + i
            return "true" if d <= 1 else f"Core.bxor (x.getD {k - 2} false) (x.getD {k - 1} false || x.getD {k} false)"
        if fam == "one":
            return "true"
        if fam == "time-parity":
            return at(1)
        if fam in ("rdiag", "tower-word"):
            return at(p)
        if fam == "exposed":
            return f"({at(p)} && !({at(p + 1)}))"
        return at(J + 1 + p)
    cols = columns(rel)
    dep, rest = cols[-1], cols[:-1]
    negate = sum(1 for c in rest if c[1] == "one") % 2 == 1
    terms = [get(c) for c in rest if c[1] != "one"]
    rhs = ("true" if negate else "false") if not terms else terms[0]
    for x in terms[1:]:
        rhs = f"Core.bxor ({rhs}) ({x})"
    if terms and negate:
        rhs = f"!({rhs})"
    relation = f"fun x => decide ({get(dep)} = {rhs})"
    text = fill(template_text("step-induction"), doc=doc_of(claim, "step-induction"), name=name,
                statement=statement(rel), occurrences="\n".join(occ_lines),
                rewrite_goal=f"  rewrite [{', '.join(occ_names)}]" if occ_names else "",
                reach=reach, state_s=state_s, state_succ=state_succ, step=stp,
                dilation_rewrite=("      rewrite [show 2 * (s + 1) = 2 * s + 1 + 1 by cfomega]" if o["dilated"] else ""),
                relation=relation, time="t")
    return _body(text), {"orbit": len(o["states"])}


def right_period(relation):
    """The largest period 2^j among the right-system columns (None when a column is not one)."""
    period = 2
    for transform, fam, p in columns(relation):
        if transform == "and" or fam not in ("one", "time-parity", "rdiag", "tower-word", "exposed"):
            raise Unprovable(f"{fam} is not a word of the right system")
        j = {"one": 0, "time-parity": 1, "rdiag": p, "tower-word": p, "exposed": (p or 0) + 1}[fam]
        m = 1 << j
        # s(2t) and s(2t+1) depend on t modulo 2^(j-1) only, s(t) and s(t+1) on t modulo 2^j
        period = max(period, m)
    return period


def render_period_reduction(claim, name):
    rel = claim["relation"]
    L = right_period(rel)
    if L > em.PERIOD_BOUND:
        raise Unprovable(f"the library's period 2^j = {L} exceeds the bound {em.PERIOD_BOUND}")
    o = orbit(rel)
    if o["fail"] is not None:
        raise Unprovable(f"the relation fails at t = {o['fail']} (a counterexample, not a proof)")
    lines, names = [], []
    g = {"base": "t % {L}", "shift": "t % {L} + 1", "even": "2 * (t % {L})", "odd": "2 * (t % {L}) + 1"}
    seen = set()
    for transform, fam, p in columns(rel):
        if fam == "one" or (transform, fam, p) in seen:
            continue
        seen.add((transform, fam, p))
        x = TIMES[transform][0]
        r = g[transform].format(L=L)
        name_i = f"o{len(names)}"

        def residue(m):
            """`x mod m` through `t mod L`, and the rewrite that says so (none when it is `t mod L`)."""
            if transform == "base" and m == L:
                return f"t % {L}", []
            return f"({r}) % {m}", [f"show ({x}) % {m} = ({r}) % {m} by cfomega"]

        def row(j):
            m = 1 << j
            res, rw_ = residue(m)
            return f"(Core.row ({res})).testBit {j}", m, rw_
        if fam == "time-parity":
            res, rw_ = residue(2)
            lines.append(f"  have {name_i} : EdgeParity.timeParity ({x}) = decide ({res} = 1) := "
                         + (f"by\n    unfold EdgeParity.timeParity\n    rw [{', '.join(rw_)}]" if rw_ else "rfl"))
        elif fam in ("rdiag", "tower-word"):
            form, m, rw_ = row(p)
            first = ["Antidiagonal.rdiag_eq_towerWord"] if fam == "rdiag" else []
            lines.append(f"  have {name_i} : {term(fam, p, x)} = {form} := by\n"
                         f"    rw [{', '.join(first + ['Antidiagonal.towerWord_eq_row', f'show Core.twopow {p} = {m} from rfl'] + rw_)}]")
        elif fam == "exposed":
            f1, m1, rw1 = row(p)
            f2, m2, rw2 = row(p + 1)
            lines.append(f"  have {name_i} : {term(fam, p, x)} = ({f1} && !{f2}) := by\n"
                         f"    show (Antidiagonal.towerWord {p} ({x}) && !Antidiagonal.towerWord {p + 1} ({x})) = _\n"
                         f"    rw [{', '.join(['Antidiagonal.towerWord_eq_row', 'Antidiagonal.towerWord_eq_row', f'show Core.twopow {p} = {m1} from rfl', f'show Core.twopow {p + 1} = {m2} from rfl'] + rw1 + rw2)}]")
        names.append(name_i)
    text = fill(template_text("period-reduction"), doc=doc_of(claim, "period-reduction"), name=name,
                statement=statement(rel), occurrences="\n".join(lines), rewrites=", ".join(names), period=str(L))
    return _body(text), {"period": L}


# ------------------------------------------------- library facts (library-rewrite)

def _nat(node):
    """A Nat literal node -> int, else None."""
    if isinstance(node, list) and node[:1] == ["app"] and len(node) == 5 and node[1] == ["const", "OfNat.ofNat"]:
        lit = node[3]
        if isinstance(lit, list) and lit[0] == "nat":
            return int(lit[1])
    if isinstance(node, list) and node[0] == "nat":
        return int(node[1])
    return None


def _time(node, var):
    """The transform a time node denotes: x, x + 1, 2 * x, 2 * x + 1."""
    if node == ["local", var]:
        return "base"
    # Nat.succ x is x + 1 (a library statement in the successor form states the same relation)
    if isinstance(node, list) and len(node) == 3 and node[:2] == ["app", ["const", "Nat.succ"]]:
        inner = _time(node[2], var)
        return {"base": "shift", "even": "odd"}.get(inner)
    # (app (const HAdd.hAdd) Nat Nat Nat <instance> a b): eight entries
    if isinstance(node, list) and len(node) == 8 and node[0] == "app" and node[1] == ["const", "HAdd.hAdd"] \
            and _nat(node[7]) == 1:
        inner = node[6]
        if inner == ["local", var]:
            return "shift"
        if _time(inner, var) == "even":
            return "odd"
    if isinstance(node, list) and len(node) == 8 and node[0] == "app" and node[1] == ["const", "HMul.hMul"] \
            and _nat(node[6]) == 2 and node[7] == ["local", var]:
        return "even"
    return None


_BY_LEAN = {f["lean"]: f for f in sequencemodel.FAMILIES}


def _expr(node, var):
    """A Boolean expression over columns at the time var: a nested tuple, or None."""
    if node == ["const", "Bool.true"]:
        return ("const", True)
    if node == ["const", "Bool.false"]:
        return ("const", False)
    if not (isinstance(node, list) and node and node[0] == "app"):
        return None
    head, args = node[1], node[2:]
    name = head[1] if isinstance(head, list) and head[0] == "const" else None
    if name == "Rule30UOR.Core.bxor" and len(args) == 2:
        a, b = _expr(args[0], var), _expr(args[1], var)
        return ("xor", a, b) if a and b else None
    if name in ("not", "Bool.not") and len(args) == 1:
        a = _expr(args[0], var)
        return ("not", a) if a else None
    if name in ("and", "Bool.and", "or", "Bool.or") and len(args) == 2:
        a, b = _expr(args[0], var), _expr(args[1], var)
        return ((name.split(".")[-1]), a, b) if a and b else None
    if name == "Decidable.decide" and len(args) == 2:
        prop = args[0]
        # decide (x % 2 = 1): the time parity (EdgeParity.timeParity is defined so)
        if isinstance(prop, list) and len(prop) == 5 and prop[1] == ["const", "Eq"] and _nat(prop[4]) == 1:
            m = prop[3]
            if isinstance(m, list) and len(m) == 8 and m[1] == ["const", "HMod.hMod"] and _nat(m[7]) == 2:
                tr = _time(m[6], var)
                if tr:
                    return ("col", tr, "time-parity", None)
        return None
    fam = _BY_LEAN.get(name)
    if fam is None:
        return None
    if fam["values"] == [None] and len(args) == 1:
        tr = _time(args[0], var)
        return ("col", tr, fam["family"], None) if tr else None
    if fam["family"] == "cell":
        return None
    if len(args) == 2 and _nat(args[0]) is not None and _nat(args[0]) in fam["values"]:
        tr = _time(args[1], var)
        return ("col", tr, fam["family"], _nat(args[0])) if tr else None
    return None


def parse_fact(name, sig):
    """A library theorem `∀ x : Nat, lhs = rhs` over the basis columns at x, x+1, 2x, 2x+1:
    {"lean", "lhs", "rhs", "columns"} or None."""
    if not sig or sig.get("kind") != "theorem":
        return None
    t = sig["type"]
    if not (isinstance(t, list) and t[:2] == ["pi", "explicit"] and t[3] == ["const", "Nat"]):
        return None
    var, body = t[2], t[4]
    if not (isinstance(body, list) and len(body) == 5 and body[:3] == ["app", ["const", "Eq"], ["const", "Bool"]]):
        return None
    lhs, rhs = _expr(body[3], var), _expr(body[4], var)
    if not lhs or not rhs:
        return None
    return {"lean": name, "lhs": lhs, "rhs": rhs}


def _cols_of(e, out):
    if e[0] == "col":
        out.add(e[1:])
    elif e[0] != "const":
        for x in e[1:]:
            _cols_of(x, out)
    return out


def affine(e):
    """The XOR relation an affine expression denotes, as a multiset mod 2 of column ids
    (`one` for the constant), or None when it is not affine."""
    if e[0] == "const":
        return {"one"} if e[1] else set()
    if e[0] == "col":
        _, tr, fam, p = e
        cid = fam if p is None else f"{fam}({p})"
        return {cid if tr == "base" else f"{tr}:{cid}"}
    if e[0] == "not":
        a = affine(e[1])
        return None if a is None else a ^ {"one"}
    if e[0] == "xor":
        a, b = affine(e[1]), affine(e[2])
        return None if a is None or b is None else a ^ b
    return None


def fact_relation(fact):
    a, b = affine(fact["lhs"]), affine(fact["rhs"])
    return None if a is None or b is None else sorted(a ^ b)


def render_expr(e, t="t"):
    if e[0] == "const":
        return _b(e[1])
    if e[0] == "col":
        _, tr, fam, p = e
        return column_term((tr, fam, p), t)
    if e[0] == "not":
        return f"!({render_expr(e[1], t)})"
    if e[0] == "xor":
        return f"Core.bxor ({render_expr(e[1], t)}) ({render_expr(e[2], t)})"
    return f"({render_expr(e[1], t)} {'&&' if e[0] == 'and' else '||'} {render_expr(e[2], t)})"


def library_facts(relation, cache):
    """The library's unconditional equations among the relation's constants (`mentions`) and the
    register's proved relations, parsed (memoized in `cache` for the run)."""
    from . import leansig
    consts = sorted({"Rule30UOR." + _LEAN[fam] for t, fam, p in columns(relation)
                     if t != "and" and fam in _LEAN and fam != "one"})
    # the time parity is read through rdiag 1 and the words through rdiag: their facts count too
    if any(f in ("time-parity", "tower-word", "exposed") for _, f, _ in columns(relation)):
        consts = sorted(set(consts) | {"Rule30UOR.Core.rdiag"})
    names = set()
    for c in consts:
        if c not in cache.setdefault("mentions", {}):
            cache["mentions"][c] = leansig.mentions([c])
        names |= set(cache["mentions"][c])
    for c in frontier.load()["claim"]:
        if c["status"] == "proved" and c.get("lean") and c.get("relation"):
            names.add(c["lean"])
    want = sorted(n for n in names if n not in cache.setdefault("signatures", {}))
    if want:
        cache["signatures"].update(leansig.signatures(want))
    facts = []
    for n in sorted(names):
        f = parse_fact(n, cache["signatures"].get(n))
        if f:
            facts.append(f)
    return facts


def publishable(lean, cache=None):
    """Whether a theorem has a lexeme or `theorem preview` can state it (memoized in `cache`)."""
    from . import theorem
    from .convert import Unsupported
    from .lexicon import Lexicon
    memo = (cache if cache is not None else {}).setdefault("publishable", {})
    if lean not in memo:
        if Lexicon().for_lean(lean):
            memo[lean] = True
        else:
            try:
                theorem.add(lean, "r30.observation", None, None, dry_run=True)
                memo[lean] = True
            except (Unsupported, RuntimeError):
                memo[lean] = False
    return memo[lean]


def module_of(name):
    """The research module that declares a Lean name: the longest registered module prefix."""
    mods = sorted(repo.research_modules(), key=len, reverse=True)
    if name.startswith("Rule30UOR.Interfaces."):
        return "Rule30UOR.Interfaces"
    return next((m for m in mods if name.startswith(m + ".")), None)


def _eval(e, val):
    k = e[0]
    if k == "const":
        return e[1]
    if k == "atom":
        return val[e[1]]
    if k == "not":
        return not _eval(e[1], val)
    if k == "xor":
        return _eval(e[1], val) ^ _eval(e[2], val)
    if k == "and":
        return _eval(e[1], val) and _eval(e[2], val)
    return _eval(e[1], val) or _eval(e[2], val)


def _atoms(col, base_t, unfold=True):
    """A column at its time as an expression over atom strings (rdiag/ldiag at base_t, or an opaque
    column term), mirroring atom_expr."""
    transform, fam, p = col
    if transform == "and":
        a, b = (base_of(i) for i in fam)
        return ("and", ("atom", term(*a, "t")), ("atom", term(*b, "t")))
    if fam not in FINITE:
        return ("atom", column_term(col))
    if fam == "one":
        return ("const", True)
    stepped = transform in ("shift", "odd")
    bt = {"base": "t", "shift": "t", "even": "2 * t", "odd": "2 * t"}[transform]

    def r(j):
        if not stepped:
            return ("atom", f"Core.rdiag {j} ({bt})")
        if j == 0:
            return ("const", True)
        if j == 1:
            return ("not", ("atom", f"Core.rdiag 1 ({bt})"))
        return ("xor", ("atom", f"Core.rdiag {j} ({bt})"),
                ("or", ("atom", f"Core.rdiag {j - 1} ({bt})"), ("atom", f"Core.rdiag {j - 2} ({bt})")))

    def l(d):
        if not stepped:
            return ("atom", f"Core.ldiag {d} ({bt})")
        if d <= 1:
            return ("const", True)
        return ("xor", ("atom", f"Core.ldiag {d - 2} ({bt})"),
                ("or", ("atom", f"Core.ldiag {d - 1} ({bt})"), ("atom", f"Core.ldiag {d} ({bt})")))
    if fam == "time-parity":
        return r(1)
    if fam in ("rdiag", "tower-word"):
        return r(p)
    if fam == "exposed":
        return ("and", r(p), ("not", r(p + 1)))
    return l(p)


def _atom_set(e, out):
    if e[0] == "atom":
        out.add(e[1])
    elif e[0] != "const":
        for x in e[1:]:
            _atom_set(x, out)
    return out


def _fact_atoms(fact, T):
    """A fact instantiated at the time T ('t' or '2 * t'): its two sides over atoms (its columns
    at base times only: a fact that reads a shifted column is instantiated as written)."""
    def conv(e):
        if e[0] == "const":
            return e
        if e[0] == "col":
            _, tr, fam, p = e
            if tr != "base":
                return None
            return _atoms(("even" if T == "2 * t" else "base", fam, p), T)
        parts = [conv(x) for x in e[1:]]
        return None if any(x is None for x in parts) else (e[0], *parts)
    return conv(fact["lhs"]), conv(fact["rhs"])


def render_library_rewrite(claim, name, cache, facts=None):
    """(text, info) or raise Unprovable; info["known"] names a library theorem that states the
    relation itself (the claim is then proved by it, no new theorem)."""
    rel = claim["relation"]
    facts = library_facts(rel, cache) if facts is None else facts
    target = sorted(rel)
    for f in facts:
        # a library theorem stating the relation proves the claim, once it is (or can be) published
        if fact_relation(f) == target and publishable(f["lean"], cache):
            return None, {"known": f["lean"]}
    cols = columns(rel)
    exprs = [_atoms(c, None) for c in cols]
    goal_atoms = set()
    for e in exprs:
        _atom_set(e, goal_atoms)
    times = sorted({("2 * t" if "(2 * t)" in a else "t") for a in goal_atoms if a.startswith(("Core.rdiag", "Core.ldiag"))})
    used, seen = [], set()
    for f in facts:
        for T in times or ["t"]:
            lhs, rhs = _fact_atoms(f, T)
            if lhs is None:
                continue
            atoms = _atom_set(lhs, set()) | _atom_set(rhs, set())
            key = (_atoms_text(lhs), _atoms_text(rhs))
            if not atoms or not atoms <= goal_atoms or key in seen:
                continue
            # a fact that holds for every assignment of its atoms says nothing (and its proof would
            # close by rewriting alone): only facts that exclude an assignment are instantiated
            names = sorted(atoms)
            if all(_eval(lhs, dict(zip(names, bits))) == _eval(rhs, dict(zip(names, bits)))
                   for bits in product([False, True], repeat=len(names))):
                continue
            seen.add(key)
            used.append((f, T, lhs, rhs))
    zero = [a for a in goal_atoms if a.startswith("Core.rdiag 0 (")]
    atoms = sorted(goal_atoms)
    # the Boolean core, decided here first
    rhs_val = lambda val: sum(_eval(e, val) for e in exprs) % 2 == 0
    hyps = [(lambda val, l=l, r=r: _eval(l, val) == _eval(r, val)) for _, _, l, r in used]
    for bits in product([False, True], repeat=len(atoms)):
        val = dict(zip(atoms, bits))
        if all(val[z] for z in zero) and all(h(val) for h in hyps) and not rhs_val(val):
            raise Unprovable("the library's facts leave an assignment of the atoms that breaks the relation: "
                             + ", ".join(f"{a}={_b(v)}" for a, v in val.items()))
    occ_lines, occ_names = occurrence_equations(occurrences(rel))
    fact_lines, fact_names = [], []
    for z in sorted(zero):
        x = z[len("Core.rdiag 0 ("):-1]
        fact_lines.append(f"  have f{len(fact_names)} : {z} = true := Interfaces.rdiag_zero_all ({x})")
        fact_names.append(f"f{len(fact_names)}")
    for f, T, lhs_t, rhs_t in used:
        k = len(fact_names)
        # the fact in the columns' terms (definitionally the library's statement), then through
        # the diagonals with its own occurrence equations
        stated = f"{render_expr(f['lhs'], T)} = {render_expr(f['rhs'], T)}"
        fo = []
        for e in (f["lhs"], f["rhs"]):
            for tr, fam, p in sorted(_cols_of(e, set()), key=str):
                if fam in ("time-parity", "tower-word", "exposed"):
                    fo.append((fam, p, T))
        lines, names = occurrence_equations(list(dict.fromkeys(fo)), prefix=f"g{k}_")
        fact_lines += lines
        rewrite = f"    rewrite [{', '.join(names)}] at h\n" if names else ""
        fact_lines.append(f"  have f{k} : {_atoms_text(lhs_t)} = {_atoms_text(rhs_t)} := by\n"
                          f"    have h : {stated} := {f['lean']} ({T})\n{rewrite}    all_goals exact h")
        fact_names.append(f"f{k}")
    gen = "\n".join(f"  generalize {a} = a{i}" for i, a in enumerate(sorted(atoms, key=len, reverse=True)))
    revert_atoms = " ".join(f"a{i}" for i in range(len(atoms)))
    text = fill(template_text("library-rewrite"), doc=doc_of(claim, "library-rewrite"), name=name,
                statement=statement(rel), occurrences="\n".join(occ_lines),
                rewrite_goal=f"  rewrite [{', '.join(occ_names)}]" if occ_names else "",
                normal_goal=normal_goal(rel), facts="\n".join(fact_lines),
                revert_facts=f"  revert {' '.join(fact_names)}" if fact_names else "",
                generalize=gen + (f"\n  revert {revert_atoms}" if atoms else ""))
    return _body(text), {"facts": [f["lean"] for f, _, _, _ in used],
                         "imports": sorted({module_of(f["lean"]) for f, _, _, _ in used} - {None})}


def _atoms_text(e):
    k = e[0]
    if k == "const":
        return _b(e[1])
    if k == "atom":
        return e[1]
    if k == "not":
        return f"!({_atoms_text(e[1])})"
    if k == "xor":
        return f"Core.bxor ({_atoms_text(e[1])}) ({_atoms_text(e[2])})"
    return f"({_atoms_text(e[1])} {'&&' if k == 'and' else '||'} {_atoms_text(e[2])})"


def render_counterexample(claim, name):
    rel = claim["relation"]
    o = orbit(rel)
    t0 = o["fail"]
    if t0 is None:
        raise Unprovable("the relation holds on the whole orbit of the diagonals: no counterexample")
    J, D = o["J"], o["D"]
    n = J + D + 2
    lit = str(t0)
    occ_lines, occ_names = occurrence_equations(occurrences(rel, lit))
    cols = columns(rel)
    # the atoms at their numeral times (no unfolding: the iteration evaluates every time)
    atoms = []
    for transform, fam, p in cols:
        if fam == "one":
            continue
        x = TIMES[transform][1](t0)
        idxs = {"time-parity": [1], "rdiag": [p], "tower-word": [p], "exposed": [p, p + 1]}.get(fam, [J + 1 + (p or 0)])
        for i in idxs:
            atoms.append((i, x))
    atoms = sorted(set(atoms))
    stp = step_lambda(J, D, n, ["plain"])
    it = lambda x: f"(Nat.rec (motive := fun _ => List Bool) ({_list([_b(v) for v in initial(J, D)])}) (fun _ x => ({stp}) x) {x})"
    atom_lines, atom_names = [], []
    for k, (i, x) in enumerate(atoms):
        atom = f"Core.rdiag {i} {x}" if i <= J else f"Core.ldiag {i - J - 1} {x}"
        atom_lines.append(f"  have a{k} : {atom} = {it(x)}.getD {i} false := congrArg (fun l => l.getD {i} false) (key {x})")
        atom_names.append(f"a{k}")
    # the refutation: the dependent column at t0 is the negation of what the relation says
    body = statement(rel, lit)
    dep, rhs = body.split(" = ", 1)
    refutation = f"{dep} = !({rhs})"
    text = fill(template_text("counterexample"), doc=doc_of(claim, "counterexample").replace("Deduced", "Refuted at t = " + lit + ";"),
                name=name, refutation=refutation, occurrences="\n".join(occ_lines),
                rewrite_goal=f"  rewrite [{', '.join(occ_names)}]" if occ_names else "",
                state_s=_list(state_terms(J, D, "s")), state_zero=_list([_b(v) for v in initial(J, D)]), step=stp,
                atoms="\n".join(atom_lines), atom_rewrites=", ".join(atom_names))
    return _body(text), {"counterexample": t0}


RENDER = {"period-reduction": lambda c, nm, cache: render_period_reduction(c, nm),
          "library-rewrite": lambda c, nm, cache: render_library_rewrite(c, nm, cache),
          "step-induction": lambda c, nm, cache: render_step_induction(c, nm),
          "counterexample": lambda c, nm, cache: render_counterexample(c, nm)}


def applicable(claim):
    """The strategies of the portfolio whose applicability holds, in portfolio order, and the
    relation's family (the key of the learned weights)."""
    rel = claim["relation"]
    fam = family(rel)
    out = []
    for s in em.PORTFOLIO:
        sid = s["id"]
        if sid == "library-rewrite":
            out.append(sid)
        elif sid == "counterexample":
            try:
                if orbit(rel)["fail"] is not None:
                    out.append(sid)
            except Unprovable:
                pass
        elif sid == "step-induction":
            try:
                o = orbit(rel)
                if o["fail"] is None and len(o["states"]) <= em.ORBIT_BOUND:
                    out.append(sid)
            except Unprovable:
                pass
        elif sid == "period-reduction":
            try:
                if right_period(rel) <= em.PERIOD_BOUND and orbit(rel)["fail"] is None:
                    out.append(sid)
            except Unprovable:
                pass
    return out, fam


def family(relation):
    """The relation's family: the systems it reads and how it reads time (em.FAMILIES)."""
    cols = columns(relation)
    fams = {f for t, f, _ in cols if t != "and"}
    if any(t == "and" for t, _, _ in cols) or not fams <= set(FINITE):
        return "open"
    left = "ldiag" in fams
    right = bool(fams & {"time-parity", "rdiag", "tower-word", "exposed"})
    system = "joint" if left and right else "left" if left else "right"
    reads = {t for t, _, _ in cols}
    time_ = "dilated" if reads & {"even", "odd"} else "shift" if "shift" in reads else "plain"
    return f"{system}-{time_}"


# ------------------------------------------------------------- the Lean check

def scratch_file(name, body, imports):
    lines = ["module", *[f"public import {m}" for m in sorted(set(BASE_IMPORTS) | set(imports))],
             "set_option autoImplicit false", "set_option maxRecDepth 100000", "set_option maxHeartbeats 1000000000", "",
             "@[expose] public section", "", f"namespace {DEDUCED}", "", body, f"end {DEDUCED}", "",
             f"#print axioms {DEDUCED}.{name}", ""]
    return "\n".join(lines)


def check(name, body, imports, timeout):
    """One Lean process on the scratch file: (outcome, failure point, axioms)."""
    d = repo.scratch_dir() / SCRATCH
    d.mkdir(parents=True, exist_ok=True)
    path = d / f"{name}.lean"
    path.write_text(scratch_file(name, body, imports))
    try:
        code, out, err = repo.run(["lake", "env", "lean", "-j", "1", str(path)], cwd=repo.CORE_LEAN, timeout=timeout,
                                  env={"LEAN_NUM_THREADS": "1"})
    except Exception as e:  # subprocess.TimeoutExpired
        return "timeout", f"no answer within {timeout} s ({type(e).__name__})", None
    text = out + err
    errors = [l for l in text.splitlines() if ": error" in l]
    if errors:
        return "failed", _failure_point(errors[0], path), None
    m = re.search(r"depends on axioms: \[([^\]]*)\]", text)
    axioms = [a.strip() for a in m.group(1).split(",")] if m else []
    if code != 0:
        return "failed", (text.strip().splitlines() or ["lean exited " + str(code)])[-1][:300], axioms
    bad = [a for a in axioms if a not in ("propext", "Quot.sound")]
    if bad:
        return "failed", "depends on " + ", ".join(bad), axioms
    return "proved", "", axioms


def _failure_point(line, path):
    """`<file>:L:C: error: msg` -> `L:C msg` relative to the theorem."""
    return line.replace(str(path) + ":", "").strip()[:300]


# ---------------------------------------------------------------- the module

HEADER = """module
{imports}
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Deduced: the theorems the engine proved

Every theorem here was rendered by `bin/r30 deduce` from an observed claim of the register (a
relation among the columns of the basis that `bin/r30 discover` certified on a window) with a
proof template of the portfolio (`tools/r30/templates/`, pinned by digest in `Engine.lex.tex`),
checked by Lean, published, and recorded as the claim's proof. The engine only adds to this
module; nothing here is written by hand. -/

@[expose] public section

namespace Rule30UOR.Deduced

"""


def module_text(theorems):
    """The module from its theorems [{name, body, imports}] (in the order proved)."""
    imports = sorted(set(BASE_IMPORTS) | {m for t in theorems for m in t.get("imports", [])})
    return (HEADER.format(imports="\n".join(f"public import {m}" for m in imports))
            + "\n".join(t["body"].rstrip("\n") + "\n" for t in theorems) + "\nend Rule30UOR.Deduced\n")


def read_module():
    """[{name, body, imports}] of the current module (the imports are shared: kept on the first)."""
    if not DEDUCED_PATH.exists():
        return []
    text = DEDUCED_PATH.read_text()
    imports = re.findall(r"^public import (\S+)$", text, re.M)
    start = text.find("namespace Rule30UOR.Deduced\n")
    end = text.rfind("end Rule30UOR.Deduced")
    if start < 0 or end < 0:
        return []
    body = text[start + len("namespace Rule30UOR.Deduced\n"):end]
    out = []
    for chunk in re.split(r"\n(?=/-- )", "\n" + body.strip("\n")):
        chunk = chunk.strip("\n")
        m = re.search(r"^theorem (\S+)", chunk, re.M)
        if m:
            out.append({"name": m.group(1), "body": chunk + "\n", "imports": []})
    if out:
        out[0]["imports"] = imports
    return out


# ---------------------------------------------------------------- the run

def plan(claims=None, ledger=None):
    """For each observed claim: its family, its applicable strategies in the learned order, and
    which of them are still unattempted for the current template digests."""
    from . import engine
    ledger = engine.load() if ledger is None else ledger
    rows = []
    for c in frontier.load()["claim"]:
        if c["status"] != "observed" or (claims and c["id"] not in claims):
            continue
        try:
            apps, fam = applicable(c)
        except (ValueError, KeyError) as e:
            apps, fam = [], "open"
        order = em.schedule(engine.weights(ledger), fam, apps)
        done = {(a["strategy"], a["template"]) for a in ledger["attempt"] if a["kappa"] == c.get("kappa")}
        pending = [s for s in order if (s, em.template_digest(s)) not in done]
        rows.append({"id": c["id"], "kappa": c.get("kappa"), "family": fam, "order": order, "pending": pending})
    return rows


def run(budget_minutes=60, claims=None, dry_run=False, log=print, tick=0):
    """Attempt the pending strategies of the observed claims within the budget; record every
    attempt; publish and register the proofs. Returns the report."""
    from . import engine, modules
    ledger = engine.load()
    deadline = time.time() + budget_minutes * 60
    if not dry_run and DEDUCED_PATH.exists():
        # the library queries import every research module: the engine's own one is built first
        ok, errors = modules.build([DEDUCED])
        if not ok:
            raise RuntimeError("Rule30UOR.Deduced does not build:\n" + errors[:1200])
    rows = plan(claims, ledger)
    by_id = {c["id"]: c for c in frontier.load()["claim"]}
    cache, report = {}, {"attempts": [], "proved": [], "refuted": [], "known": [], "skipped": [], "dry_run": dry_run}
    accepted = []
    for row in rows:
        claim = by_id[row["id"]]
        name = theorem_name(claim["relation"], claim["kappa"])
        for sid in row["pending"]:
            if time.time() >= deadline:
                report["skipped"].append({"id": row["id"], "strategy": sid, "reason": "budget"})
                continue
            digest = em.template_digest(sid)
            t0 = time.time()
            attempt = {"claim": row["id"], "kappa": claim["kappa"], "strategy": sid, "template": digest,
                       "family": row["family"], "outcome": "failed", "failure": "", "seconds": 0, "theorem": ""}
            try:
                body, info = RENDER[sid](claim, name if sid != "counterexample" else name + "_fails", cache)
            except Unprovable as e:
                attempt.update(outcome="failed", failure="(decided in Python) " + str(e)[:280])
                body, info = None, {}
            except RuntimeError as e:
                # Lean did not answer the library-facts query: the environment failed, not the
                # template, so nothing is recorded and the run stops
                for at in report["attempts"]:
                    engine.record_attempt(ledger, at, tick)
                engine.save(ledger)
                raise RuntimeError(f"the library-facts query failed ({row['id']}): {str(e)[:400]}")
            if body is None and info.get("known"):
                attempt.update(outcome="known", theorem=info["known"])
            elif body is not None:
                if dry_run:
                    log(f"[dry-run] {row['id']} {sid}:\n{body}")
                    attempt.update(outcome="dry-run")
                else:
                    thm = name + ("_fails" if sid == "counterexample" else "")
                    # an attempt never runs past the stage's deadline (homeostasis cuts it, the gate keeps its share)
                    timeout = max(30, min(em.ATTEMPT_TIMEOUT, int(deadline - time.time())))
                    outcome, failure, _ = check(thm, body, info.get("imports", []), timeout)
                    attempt.update(outcome="refuted" if (outcome == "proved" and sid == "counterexample") else outcome,
                                   failure=failure, theorem=f"{DEDUCED}.{thm}" if outcome == "proved" else "")
                    if outcome == "proved":
                        accepted.append({"claim": row["id"], "name": thm, "body": body,
                                         "imports": info.get("imports", []), "refutes": sid == "counterexample",
                                         "counterexample": info.get("counterexample")})
            attempt["seconds"] = round(time.time() - t0, 1)
            report["attempts"].append(attempt)
            log(f"{row['id']} [{row['family']}] {sid}: {attempt['outcome']}" + (f" ({attempt['failure'][:120]})" if attempt["failure"] else "")
                + f" {attempt['seconds']}s")
            if dry_run:
                continue
            if attempt["outcome"] == "known":
                report["known"].append({"id": row["id"], "lean": attempt["theorem"]})
                break
            if attempt["outcome"] in ("proved", "refuted"):
                break
    if dry_run:
        return report
    try:
        if accepted or report["known"]:
            settle(accepted, report, log)
    finally:
        # the ledger takes every attempt with the outcome settling gave it (a duplicate of a library
        # theorem becomes `known`, an unstatable proof `failed`), and learns from it
        for attempt in report["attempts"]:
            engine.record_attempt(ledger, attempt, tick)
        engine.save(ledger)
    return report


def settle(accepted, report, log=print):
    """Append the accepted theorems to the module, build it, replace any that a library theorem
    already states (κ duplicates), publish, and record the claims."""
    from . import cli, modules
    existing = read_module()
    have = {t["name"] for t in existing}
    fresh = [a for a in accepted if a["name"] not in have]
    if fresh:
        if not DEDUCED_PATH.exists():
            modules.register(DEDUCED)
        DEDUCED_PATH.write_text(module_text(existing + [{"name": a["name"], "body": a["body"], "imports": a["imports"]}
                                                         for a in fresh]))
        ok, errors = modules.build([DEDUCED])
        if not ok:
            # never leave a module that does not build: drop what was appended
            DEDUCED_PATH.write_text(module_text(existing))
            raise RuntimeError("the Deduced module did not build with the accepted theorems:\n" + errors[:1500])
        dup = duplicate_partners([f"{DEDUCED}.{a['name']}" for a in fresh])
        if dup:
            keep = [a for a in fresh if f"{DEDUCED}.{a['name']}" not in dup]
            DEDUCED_PATH.write_text(module_text(existing + [{"name": a["name"], "body": a["body"], "imports": a["imports"]}
                                                             for a in keep]))
            modules.build([DEDUCED])
            for a in fresh:
                partner = dup.get(f"{DEDUCED}.{a['name']}")
                if partner:
                    log(f"{a['claim']}: {a['name']} states what {partner} states; the library theorem proves the claim")
                    report["known"].append({"id": a["claim"], "lean": partner})
                    for at in report["attempts"]:
                        if at["claim"] == a["claim"] and at["theorem"] == f"{DEDUCED}.{a['name']}":
                            at.update(outcome="known", theorem=partner)
            fresh = keep
    # publish and record; a proof LexLean cannot state is no proof for the register: it leaves the
    # module and its attempt records why
    unstated = []
    for a in fresh:
        lean = f"{DEDUCED}.{a['name']}"
        try:
            publish(lean)
        except RuntimeError as e:
            if not a["refutes"]:
                unstated.append((a, str(e)))
                continue
            log(f"{lean} stays unpublished (a refutation needs no lexeme): {e}")
        if not a["refutes"]:
            frontier.update(a["claim"], status="proved", lean=lean)
            report["proved"].append({"id": a["claim"], "lean": lean})
        else:
            frontier.update(a["claim"], status="refuted", lean=lean,
                            note=f"Refuted by bin/r30 deduce: the relation fails at t = {a['counterexample']} ({lean}).")
            report["refuted"].append({"id": a["claim"], "lean": lean, "t": a["counterexample"]})
    if unstated:
        drop = {a["name"] for a, _ in unstated}
        DEDUCED_PATH.write_text(module_text([x for x in read_module() if x["name"] not in drop]))
        modules.build([DEDUCED])
        for a, why in unstated:
            for at in report["attempts"]:
                if at["claim"] == a["claim"] and at["theorem"] == f"{DEDUCED}.{a['name']}":
                    at.update(outcome="failed", theorem="", failure="unstatable: " + why[:250])
    for row in list(report["known"]):
        try:
            publish(row["lean"])
        except RuntimeError as e:
            # a second proof would be refused by the gate and an unpublished one proves nothing for the
            # register: the claim stays observed, and the attempt says why
            log(f"{row['id']}: the library theorem {row['lean']} cannot be published ({e}); the claim stays observed")
            report["known"].remove(row)
            for at in report["attempts"]:
                if at["claim"] == row["id"] and at["outcome"] == "known":
                    at.update(outcome="failed", failure=f"known as {row['lean']}, which LexLean cannot state: {str(e)[:200]}")
            continue
        frontier.update(row["id"], status="proved", lean=row["lean"])
    frontier.render_file()
    cli._sync_register()


def publish(lean):
    """`theorem add` unless the theorem already has a lexeme."""
    from . import theorem
    from .convert import Unsupported
    from .lexicon import Lexicon
    if Lexicon().for_lean(lean):
        return
    try:
        theorem.add(lean, "r30.observation", None, None)
    except Unsupported as e:
        raise RuntimeError(f"{lean} cannot be stated in LexLean: {e}")


def duplicate_partners(names):
    """{new theorem: the library theorem with the same statement κ} (`kappa --duplicates`)."""
    from . import cli, modules
    kr = cli._kappa_research()
    every = list(modules.list_modules())
    memo, read_only = kr.working_memo(repo.CORE_LEAN)
    labels = kr.memo_labels(repo.CORE_LEAN, every, memo, read_only=read_only)
    groups = kr.duplicates(labels)
    out = {}
    for members in groups.values():
        full = [n for _, n in members]
        for n in names:
            if n in full:
                others = [m for m in full if m != n and not m.startswith(DEDUCED + ".")] or [m for m in full if m != n]
                out[n] = others[0]
    return out


def render(r):
    lines = [f"attempts {len(r['attempts'])}: " + ", ".join(
        f"{k} {sum(1 for a in r['attempts'] if a['outcome'] == k)}"
        for k in ("proved", "known", "refuted", "failed", "timeout", "dry-run") if any(a['outcome'] == k for a in r['attempts']))]
    for a in r["attempts"]:
        lines.append(f"  {a['claim']} [{a['family']}] {a['strategy']}: {a['outcome']} {a['seconds']}s"
                     + (f"  {a['theorem']}" if a["theorem"] else "") + (f"\n      {a['failure']}" if a["failure"] else ""))
    for k in ("proved", "known", "refuted"):
        if r[k]:
            lines.append(f"{k}: " + ", ".join(f"{x['id']} ({x['lean']})" for x in r[k]))
    if r["skipped"]:
        lines.append(f"left for the next tick (budget): {len(r['skipped'])}")
    return "\n".join(lines)
