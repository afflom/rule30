"""`bin/r30 discover`: the runtime of Discovery.lex.tex on the basis.

Induction here is exact and finite: the relation engine (Gaussian elimination
over F2) returns a basis of the XOR relations among the columns of the
extended basis on the window `t < W`, each certified by the postcondition
validator, and the recurrence engine (Berlekamp-Massey) the connection
polynomial of every base window, certified the same way. Nothing is guessed
and nothing is enumerated about Rule 30 itself: the columns are the paper's
notions (`Sequences.lex.tex`) and their transforms, the engines are the
model's realizations, and what comes out is a list of statements each of
which holds on the window and is a candidate for deduction (a Lean theorem,
then `frontier set --status proved`).

The runtime is the certified Rust of the three production roots
(`buildColumns`, `findRelations`, `findRecurrence`), exported by `bin/r30 api
production` and driven by a harness cargo builds (`discover_rust.py`). There is
no other runtime: without them the run is refused. The report says why it ran.

What the report separates:

- `register`: the relation has the κ-label of a register claim's relation;
- `trivial`: a consequence (an XOR combination) of the definitional
  relations of the basis (`trivial_relations`: the rule `Core.cell_succ`, the
  masked column's definition, `towerWord j = rdiag j`, the constant
  diagonals, the transforms of the constant, the definitions of the time and
  trailing parities) and of their images under the substitutions
  `t -> t+1, 2t, 2t+1` that are again relations among columns;
- `consequence`: a combination of those, the register's relations, the
  relations reported before it, and the images of all of these under the
  same substitutions (an identity of sequences stays one under a
  substitution of `t`);
- `new`: everything else, in the engine's order; `self` when every column
  is the constant or a transform of one base sequence (a 2-kernel or shift
  relation of that sequence), `cross` otherwise. With `--write` the new
  relations are appended to the register as status `observed`.

Every relation carries its certificate: the window, the columns (ids and
κ-labels), the relation κ-label `(relation <sorted column labels>)`, and the
rank of the columns before its dependent column, so that `2^(rank - W)` bounds
the chance that a random column lands in their span."""

from datetime import date

from . import discoverymodel as dm, frontier, repo, sequencemodel
from .discoverymodel import Mirror


class BasisError(RuntimeError):
    pass


class Refused(RuntimeError):
    pass


def trivial_relations(present):
    """The definitional relations of the extended basis whose columns are all present."""
    rows = [(["one", "rdiag(0)"], "Core.rdiag: rdiag 0 t = true"),
            (["one", "ldiag(0)"], "Core.ldiag: ldiag 0 t = true"),
            (["time-parity", "rdiag(1)"], "Core.rdiag: rdiag 1 0 = false and rdiag 1 (s+1) = not rdiag 1 s; EdgeParity.timeParity"),
            (["masked-column", "cell(1)", "and:center:cell(1)"], "Antidiagonal.maskedColumn: cell t 1 && !center t"),
            (["one", "shift:one"], "the shift of the constant"),
            (["one", "even:one"], "the even dilation of the constant"),
            (["one", "odd:one"], "the odd dilation of the constant"),
            (["one", "time-parity", "shift:time-parity"], "EdgeParity.timeParity: timeParity (t+1) = not timeParity t"),
            (["even:time-parity"], "EdgeParity.timeParity: timeParity (2t) = false"),
            (["one", "odd:time-parity"], "EdgeParity.timeParity: timeParity (2t+1) = true"),
            (["even:trailing-parity"], "Ledger.trailingParityFuel: no trailing ones in an even number"),
            (["one", "trailing-parity", "odd:trailing-parity"], "Ledger.trailingParityFuel: trailingParity (2t+1) = not trailingParity t")]
    rows += [([f"rdiag({j})", f"tower-word({j})"], "Antidiagonal.rdiag_eq_towerWord") for j in range(13)]
    gens = dm.AND_GENERATORS
    for i in range(len(gens) - 1):
        c, r = gens[i], gens[i + 1]
        p = -3 + i
        left = "center" if p - 1 == 0 else f"cell({p - 1})"
        rows.append(([f"shift:{c}", left, c, r, f"and:{c}:{r}"],
                     "Core.cell_succ: cell (t+1) p = rule (cell t (p-1)) (cell t p) (cell t (p+1)), rule a c r = a + c + r + c r"))
    return [(cols, by) for cols, by in rows if all(x in present for x in cols)]


def columns_of(data, degree):
    ids = [r["id"] for r in data["sequence"]]
    cols = list(ids)
    for t in ("shift", "even", "odd"):
        cols += [f"{t}:{i}" for i in ids]
    if degree >= 2:
        g = dm.AND_GENERATORS
        cols += [f"and:{g[i]}:{g[k]}" for i in range(len(g)) for k in range(i + 1, len(g))]
    return cols


class Span:
    """A subspace of F2^m as reduced bitmask pivots (Python ints)."""

    def __init__(self):
        self.pivots = {}

    def reduce(self, v):
        while v:
            top = v.bit_length() - 1
            if top not in self.pivots:
                return v
            v ^= self.pivots[top]
        return 0

    def add(self, v):
        v = self.reduce(v)
        if v:
            self.pivots[v.bit_length() - 1] = v
            return True
        return False

    def __contains__(self, v):
        return self.reduce(v) == 0


def _mask_int(indices):
    v = 0
    for i in indices:
        v |= 1 << i
    return v


def runtime():
    """The harness of the certified roots; `engine_rust.NoRoot` when it cannot be had."""
    from . import discover_rust
    return discover_rust.runner()


def run(window=256, degree=2, write=False, data=None, claims=None, engine=None):
    data = sequencemodel.load() if data is None else data
    bad = sequencemodel.problems(data)
    if bad:
        raise BasisError(bad[0])
    stored = data["window"]
    if window <= 0 or window % dm.CHUNK_BITS or 2 * window > stored:
        raise Refused(f"the discovery window {window} must be a positive multiple of {dm.CHUNK_BITS} "
                      f"and at most half the stored window {stored} (the odd dilation reads s(2t+1))")
    claims = frontier.load()["claim"] if claims is None else claims
    index = dm.index_of(data)
    kappas = dm.kappas_of(data)
    bases = dm.bases_of(data)
    cols = columns_of(data, degree)
    specs = [dm.column_spec(c, index) for c in cols]
    handle = engine or runtime()
    words = handle.build_columns(window, bases, specs)
    found = handle.find_relations(window, words)
    recurrences = handle.find_recurrences([sequencemodel.unchunk(w, stored) for w in bases])
    path = {"runtime": "rust", "why": handle.why}
    col_kappa = {c: dm.column_kappa(c, kappas) for c in cols}
    position = {col_kappa[c]: i for i, c in enumerate(cols)}

    def mask_of(cids):
        return _mask_int(position[dm.column_kappa(c, kappas)] for c in cids)

    present = set(cols)

    def closure(cids):
        """A relation and its images under t -> t+1, 2t, 2t+1 that are again
        relations among columns (an identity of sequences stays one under a
        substitution of t): a base column s goes to shift:s, even:s, odd:s,
        and shift:s under t -> 2t to odd:s."""
        out = [cids]
        image = {"shift": {"base": "shift"}, "even": {"base": "even", "shift": "odd"}, "odd": {"base": "odd"}}
        for t, rule in image.items():
            mapped = []
            for c in cids:
                kind, ids = dm.parse_column(c)
                if kind not in rule:
                    break
                mapped.append(f"{rule[kind]}:{ids[0]}")
            else:
                out.append(mapped)
        return [x for x in out if all(dm.column_kappa(c, kappas) in position for c in x)]

    trivial = trivial_relations(present)
    triv_span = Span()
    for c_ids, _ in trivial:
        for x in closure(c_ids):
            triv_span.add(mask_of(x))
    reg = []
    for c in claims:
        if c.get("relation") and all(dm.column_kappa(x, kappas) in position for x in c["relation"]):
            reg.append({"claim": c["id"], "status": c["status"], "relation": c["relation"],
                        "kappa": dm.relation_kappa(c["relation"], kappas)})
    known = Span()
    for c_ids, _ in trivial:
        for x in closure(c_ids):
            known.add(mask_of(x))
    for r in reg:
        for x in closure(r["relation"]):
            known.add(mask_of(x))
    by_kappa = {r["kappa"]: r["claim"] for r in reg}
    rows, new_count = [], 0
    for k, mask in enumerate(found):
        idx = [i for i, bit in enumerate(mask) if bit]
        cids = [cols[i] for i in idx]
        dependent = idx[-1]
        rank = dependent - sum(1 for m in found[:k] if max(i for i, bit in enumerate(m) if bit) < dependent)
        v = _mask_int(idx)
        kap = dm.relation_kappa(cids, kappas)
        if kap in by_kappa:
            cls = "register"
        elif v in triv_span:
            cls = "trivial"
        elif v in known:
            cls = "consequence"
        else:
            cls = "new"
            new_count += 1
        # whatever its class, a relation that holds is an identity to substitute into
        for x in closure(cids):
            known.add(mask_of(x))
        bases_used = {dm.parse_column(c)[1][0] for c in cids if c != "one"} | {
            x for c in cids for x in dm.parse_column(c)[1][1:]}
        rows.append({"columns": cids, "kappa": kap, "class": cls, "claim": by_kappa.get(kap),
                     "scope": "self" if len(bases_used - {"one"}) <= 1 else "cross",
                     "dependent": cols[dependent], "rank": rank, "chance_log2": rank - window})
    recs = []
    for r, conn in zip(data["sequence"], recurrences):
        length = len(conn) - 1
        # Berlekamp-Massey's recurrence is the unique shortest one when 2L <= N, and it
        # predicts the N - 2L values beyond the 2L that determine it: the margin is the
        # evidence (a window without structure has L about N/2, margin about 0)
        recs.append({"id": r["id"], "kappa": r["kappa"], "length": length, "window": stored,
                     "connection": conn, "margin": stored - 2 * length, "determined": 2 * length < stored})
    rank_total = len(cols) - len(found)
    result = {**path, "window": window, "stored_window": stored, "degree": degree, "columns": len(cols),
              "rank": rank_total, "relations": rows,
              "counts": {c: sum(1 for x in rows if x["class"] == c) for c in ("register", "trivial", "consequence", "new")},
              "recurrences": recs, "written": []}
    if write:
        result["written"] = write_observed([x for x in rows if x["class"] == "new"], window)
    return result


def statement(row, window):
    return (f"On every t < {window}: " + " XOR ".join(_read(c) for c in row["columns"]) + " = 0"
            + f" (found by bin/r30 discover, {row['scope']} relation; a candidate for deduction).")


def _read(cid):
    transform, ids = dm.parse_column(cid)
    if transform == "base":
        return f"{ids[0]}(t)"
    if transform == "shift":
        return f"{ids[0]}(t+1)"
    if transform == "even":
        return f"{ids[0]}(2t)"
    if transform == "odd":
        return f"{ids[0]}(2t+1)"
    return f"({ids[0]}(t) AND {ids[1]}(t))"


def write_observed(rows, window):
    """Append the new relations to the register as `observed` claims."""
    written = []
    have = {c.get("kappa") for c in frontier.load()["claim"]}
    for row in rows:
        if row["kappa"] in have:
            continue
        cid = "observed-" + row["kappa"][len("sha256:"):][:12]
        frontier.add(cid, statement(row, window), status="observed", relation=row["columns"], window=window,
                     kappa=row["kappa"])
        written.append(cid)
    if written:
        from . import cli
        cli._sync_register()
    return written


def render(r):
    lines = [f"runtime {r['runtime']} ({r['why']}); window {r['window']} of {r['stored_window']}, degree {r['degree']}, "
             f"{r['columns']} columns, rank {r['rank']}",
             "relations: " + ", ".join(f"{v} {k}" for k, v in r["counts"].items())]
    for kind in ("new", "register", "consequence"):
        rows = [x for x in r["relations"] if x["class"] == kind]
        if not rows:
            continue
        lines.append(f"{kind.upper()}:")
        for x in rows:
            lines.append(f"  [{x['scope']}, rank {x['rank']}, chance <= 2^{x['chance_log2']}] "
                         + " + ".join(x["columns"]) + f"  {x['kappa'][:19]}"
                         + (f"  ({x['claim']})" if x.get("claim") else ""))
    det = [x for x in r["recurrences"] if x["determined"]]
    lines.append(f"recurrences (Berlekamp-Massey on {r['stored_window']} times): {len(det)} of {len(r['recurrences'])} "
                 "with 2L < N (the margin N - 2L is the number of values the recurrence predicts)")
    for x in r["recurrences"]:
        lines.append(f"  {x['id']}: L = {x['length']}, margin {x['margin']}" + ("" if x["determined"] else " (none: 2L >= N)")
                     + (f"  c = {''.join(map(str, x['connection']))}" if x["determined"] and x["length"] <= 24 else ""))
    if r["written"]:
        lines.append("written to the register as observed: " + ", ".join(r["written"]))
    return "\n".join(lines)
