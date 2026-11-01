"""The audit: pruning conditional refutations of the period by exact facts
about theorems.

A *conditional refutation* is a theorem of the research library (every
module `scripts/check_research_coverage.py --modules` lists) whose conclusion
is `¬ Rule30UOR.Scale.CenterPeriodic T P`, `Problem1` or
`¬ Rule30UOR.Right.CenterPer T P`, or `False` under a `CenterPeriodic`
hypothesis: it refutes the period under hypotheses, so the route it opens is
"derive the hypotheses from the period". One generated Lean file
(`audit.lean.tmpl` after `leansig.lean.tmpl`) prints every public theorem of
the `Rule30UOR` namespace with its binders, each marked `prop` or `data` by
Lean, and its conclusion, as the repository's s-expressions; everything
below is read off those statements, never guessed.

The hypotheses of a conditional refutation are its propositional binders
minus the period itself and the *side conditions*: order, equality and
divisibility relations (and their negations, conjunctions and ∀-closures)
whose only constants are arithmetic (numerals, `+ - * / %`, `twopow`,
`min`, `max`, the instances). Each remaining hypothesis is identified by its
*key*: the head constant of its statement after its leading ∀ and →, written
`not K` under a negation and `R[c1,...]` for a relation `R` (with the defined
constants `ci` it mentions), e.g. `Rule30UOR.Interfaces.LhColAgree` or, for
a ∀-statement of `rhCenter` agreements, `Eq[Rule30UOR.Interfaces.rhCenter]`
(labelled `forall Eq[...]`).

For each key `H` the library is searched for a *refutation under a period*
(a theorem with a `CenterPeriodic` or `CenterPer` hypothesis concluding
`¬ H'` with `H'` of key `H`) and for *discharges by key* (theorems
concluding some `H'` of key `H`, with a period hypothesis or none); the key
table records both. Lean then decides, for every hypothesis that has
discharges by key, whether one of them proves it *at its own instance*
(`#r30discharge`: in the conditional refutation's context reduced to its data,
its side conditions and the period, the discharge applied at reducible
transparency and its premises closed by assumption or `omega`). A conditional
refutation is

- `dead` when some hypothesis is refuted under a period by a named theorem
  (deriving it from the period is then the whole problem again);
- `live-discharged` when its composition closes in Lean: `#r30compose`
  applies the conditional refutation to the goal
  `∀ T P, 0 < P → ¬ CenterPeriodic T P` (or `Problem1`), closes every premise
  by the period, `0 < P`, `omega` or a discharge, and the kernel accepts the
  composed term (that would be a proof of Problem 1);
- `open` otherwise, with its open hypotheses: those neither refuted under a
  period nor discharged at their instance (when every hypothesis is
  discharged and only the composition for every period fails, that is said).

`bin/r30 audit --write` writes `rule30-api/model/audit.toml` and
`rule30-api/src/Audit.lex.tex` (the audit as data, `Conditional` records,
with decided theorems: every dead entry names a refuting theorem, the
statuses are from the declared set, the theorem names are distinct (each
name stored as its segments, compared segment by segment: comparing a few
hundred whole names pairwise exceeds lexlean's child timeout), and the
counts per status); `api sync` re-renders the module from the TOML and
`api check` refuses drift. The open hypotheses of each entry are the open
obligations `bin/r30 claim <id> --related` lists for the claims they concern.
"""

from pathlib import Path
import importlib.util
import tomllib

from . import frontier, leansig, repo, sexpr
from .semantic import (BOOL, NAT, STR, all_members, b, call, definition, eq_string, field_of_each, holds, if_,
                       list_t, lst, match_list, member_string, n, named, proj, record, s, strings, structure, theorem, var)

API = repo.ROOT / "rule30-api"
REGISTER = API / "model" / "audit.toml"
MODULE = API / "src" / "Audit.lex.tex"
TEMPLATE = Path(__file__).with_name("audit.lean.tmpl")

PERIODIC = "Rule30UOR.Scale.CenterPeriodic"
CENTER_PER = "Rule30UOR.Right.CenterPer"
PROBLEM1 = "Ruliology.CellularAutomata.Rule30Prize.Problem1"
TARGETS = (PERIODIC, CENTER_PER, PROBLEM1)
# the period hypotheses, with the `#r30compose` kind of a refutation of each
PERIODS = {PERIODIC: "periodic", CENTER_PER: "centerPer"}
STATUSES = ("dead", "live-discharged", "open")

RELATIONS = ("Eq", "Ne", "LT.lt", "LE.le", "GT.gt", "GE.ge", "Dvd.dvd", "HEq")
CONNECTIVES = ("Not", "And", "Or", "Iff", "Exists", "True", "False")
ARITHMETIC = {"Nat", "Int", "Bool", "Prop", "OfNat.ofNat", "HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HDiv.hDiv",
              "HMod.hMod", "HPow.hPow", "Nat.succ", "Nat.pred", "Min.min", "Max.max", "Rule30UOR.Core.twopow",
              "Bool.true", "Bool.false"}


# --- reading statements -------------------------------------------------

def head(t):
    """The head constant of a node (`local`, `pi`, ... for other heads)."""
    while isinstance(t, list) and t and t[0] == "app":
        t = t[1]
    if isinstance(t, list) and len(t) == 2 and t[0] == "const":
        return t[1]
    return t[0] if isinstance(t, list) and t else str(t)


def body(t):
    """The statement under its leading ∀ and →."""
    while isinstance(t, list) and t and t[0] == "pi":
        t = t[4]
    return t


def constants(t):
    found = set()

    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and x[0] == "const" and isinstance(x[1], str):
                found.add(x[1])
            for y in x:
                walk(y)
    walk(t)
    return found


def _arithmetic(c):
    return c in ARITHMETIC or c.rsplit(".", 1)[-1].startswith("inst")


def defined(t):
    """The defined constants a statement mentions: not arithmetic, not a relation or connective."""
    return sorted(c for c in constants(t) if not _arithmetic(c) and c not in RELATIONS and c not in CONNECTIVES)


def _negated(t):
    return isinstance(t, list) and len(t) == 3 and t[0] == "app" and t[1] == ["const", "Not"]


def key(t):
    """The identity of a hypothesis or conclusion: its head after the leading ∀ and →."""
    x = body(t)
    if _negated(x):
        return "not " + key(x[2])
    h = head(x)
    if h in RELATIONS or h in CONNECTIVES:
        return f"{h}[{','.join(defined(x))}]"
    return h


def label(t):
    return ("forall " if isinstance(t, list) and t and t[0] == "pi" else "") + key(t)


def is_period(t):
    return not (isinstance(t, list) and t and t[0] == "pi") and head(t) in PERIODS


def is_side(t):
    """An order, equality or divisibility relation (or a connective of them) over arithmetic only."""
    x = body(t)
    while _negated(x):
        x = x[2]
    return head(x) in RELATIONS + CONNECTIVES and not defined(t)


def kind(th):
    """`periodic`, `centerPer` or `problem1` for a conditional refutation, else None."""
    c = th["conclusion"]
    if c == ["const", PROBLEM1]:
        return "problem1"
    if _negated(c) and head(c[2]) in PERIODS and c[2][0] != "pi":
        return PERIODS[head(c[2])]
    if c == ["const", "False"]:
        for x in th["binders"]:
            if x["role"] == "prop" and is_period(x["type"]):
                return PERIODS[head(x["type"])]
    return None


def under_period(th):
    return any(x["role"] == "prop" and is_period(x["type"]) for x in th["binders"])


# --- the Lean side ------------------------------------------------------

def research_modules():
    """The modules `scripts/check_research_coverage.py --modules` lists."""
    spec = importlib.util.spec_from_file_location("check_research_coverage", repo.ROOT / "scripts/check_research_coverage.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m.covered_modules(repo.ROOT)


def parse(out):
    """The `R30AUDIT` lines: ({name: theorem}, {name: conclusion})."""
    full, conclusions = {}, {}
    for line in out.splitlines():
        if not line.startswith("R30AUDIT "):
            continue
        node = sexpr.parse(line[len("R30AUDIT "):])
        if node[0] == "theorem":
            _, name, binders, conclusion = node
            full[name] = {"name": name, "conclusion": conclusion,
                          "binders": [{"role": x[0], "kind": x[1], "name": x[2], "type": x[3]} for x in binders[1:]]}
        elif node[0] == "conclusion":
            conclusions[node[1]] = node[2]
    return full, conclusions


def introspect(package_dir=None, modules=None):
    """One Lean run over the research library."""
    commands = TEMPLATE.read_text() + "\n#r30audit Rule30UOR : " + " ".join(TARGETS) + "\n"
    out, errors = leansig._run(commands, package_dir=package_dir or repo.CORE_LEAN,
                               modules=modules or research_modules())
    full, conclusions = parse(out)
    if errors or not full:
        raise RuntimeError("\n".join(errors[:5]) or "the introspection printed no theorem")
    return full, conclusions


def decide(discharges, candidates, package_dir=None, modules=None):
    """One scratch Lean file: every discharge attempt (`#r30discharge`, each premise
    at its own instance) and every composition (`#r30compose`). Returns
    ({(theorem, position): discharging theorem or None},
     {theorem: {"composed": True, "axioms": [...], "proof": str} or {"composed": False, "reason": str}})."""
    if not discharges and not candidates:
        return {}, {}
    commands = TEMPLATE.read_text() + "\n" + "".join(
        f"#r30discharge {d['kind']} {d['theorem']} \"{d['table']}\" \"{d['content']}\"\n" for d in discharges) + "".join(
        f"#r30compose {e['kind']} {e['theorem']} \"{e['table']}\"\n" for e in candidates)
    out, errors = leansig._run(commands, package_dir=package_dir or repo.CORE_LEAN,
                               modules=modules or research_modules())
    found, results = {}, {}
    for line in out.splitlines():
        if line.startswith("R30DISCHARGE "):
            _, name, position, d = line.split(" ", 3)
            found[(name, int(position))] = None if d == "-" else d
        elif line.startswith("R30COMPOSE "):
            parts = line.split(" ", 4)
            if parts[1] == "composed":
                results[parts[2]] = {"composed": True, "axioms": [a for a in parts[3].split(",") if a],
                                     "proof": parts[4] if len(parts) > 4 else ""}
            else:
                results[parts[2]] = {"composed": False, "reason": " ".join(parts[3:])[:400]}
    if (discharges or candidates) and not found and not results:
        raise RuntimeError("\n".join(errors[:5]) or "the discharge and composition run printed nothing")
    for e in candidates:
        results.setdefault(e["theorem"], {"composed": False, "reason": "; ".join(errors[:2])[:400] or "no answer"})
    return found, results


# --- the classification -------------------------------------------------

def index(full, conclusions):
    """{key: refuting theorems under a period}, {key: [(discharging theorem, under a period)]}."""
    refuters, discharges = {}, {}
    for name, th in full.items():
        c, under = th["conclusion"], under_period(th)
        if under and _negated(c):
            refuters.setdefault(key(c[2]), []).append(name)
        discharges.setdefault(key(c), []).append((name, under))
    for name, c in conclusions.items():
        discharges.setdefault(key(c), []).append((name, False))
    return refuters, discharges


def classify(full, conclusions):
    """Every conditional refutation with its hypotheses, before composition
    (status `dead`, `open`, or `candidate`: every hypothesis has a discharge),
    and the key table: for each hypothesis key, its refutations under a period
    and its discharges with and without a period hypothesis."""
    refuters, discharges = index(full, conclusions)
    keys, entries = {}, []
    for name in sorted(full):
        th = full[name]
        k = kind(th)
        if k is None:
            continue
        hyps = []
        for i, x in enumerate(th["binders"]):
            t = x["type"]
            if x["role"] != "prop" or is_period(t) or is_side(t):
                continue
            kk = key(t)
            if kk not in keys:
                keys[kk] = {"refutedBy": sorted(set(refuters.get(kk, []))),
                            "dischargedUnderPeriod": sorted({d for d, u in discharges.get(kk, []) if u}),
                            "dischargedWithoutPeriod": sorted({d for d, u in discharges.get(kk, []) if not u})}
            row = keys[kk]
            refuted = [r for r in row["refutedBy"] if r != name]
            discharged = [d for d in row["dischargedUnderPeriod"] + row["dischargedWithoutPeriod"] if d != name]
            hyps.append({"binder": x["name"], "position": i, "key": kk, "label": label(t),
                         "status": "refuted" if refuted else "open", "dischargedBy": "", "byKey": bool(discharged)})
        if any(h["status"] == "refuted" for h in hyps):
            status = "dead"
        elif all(h["byKey"] for h in hyps):
            status = "candidate"
        else:
            status = "open"
        entries.append({"theorem": name, "kind": k, "status": status, "hypotheses": hyps,
                        "refutedBy": sorted({r for h in hyps for r in keys[h["key"]]["refutedBy"] if r != name}),
                        "dischargedBy": [], "open": [], "composition": ""})
    return entries, keys


def table(entry, keys):
    """The Lean commands' table: the discharges by key of each hypothesis that has
    any, by binder position (`i D1 D2;j D3`)."""
    rows = []
    for h in entry["hypotheses"]:
        ds = [d for d in keys[h["key"]]["dischargedUnderPeriod"] + keys[h["key"]]["dischargedWithoutPeriod"]
              if d != entry["theorem"]]
        if ds:
            rows.append(f"{h['position']} " + " ".join(ds))
    return ";".join(rows)


def settle(entries, found, results):
    """Fix every entry by what Lean decided: a hypothesis is `discharged` when
    a named theorem proves it at its instance (`found`); an entry is
    `live-discharged` when its composition closed and the kernel accepted it,
    `dead` when a hypothesis is refuted under a period, `open` otherwise, with
    the hypotheses neither refuted nor discharged."""
    for e in entries:
        for h in e["hypotheses"]:
            d = found.get((e["theorem"], h["position"]))
            if h["status"] != "refuted" and d:
                h["status"], h["dischargedBy"] = "discharged", d
            h.pop("byKey", None)
        e["dischargedBy"] = sorted({h["dischargedBy"] for h in e["hypotheses"] if h["dischargedBy"]})
        e["open"] = [h["label"] for h in e["hypotheses"] if h["status"] == "open"]
        if e["status"] != "candidate":
            continue
        r = results.get(e["theorem"], {"composed": False, "reason": "not attempted"})
        if r["composed"] and "sorryAx" in r["axioms"]:
            r = {"composed": False, "reason": "the composed term depends on sorryAx"}
        if r["composed"]:
            e["status"] = "live-discharged"
            e["composition"] = "composed; axioms " + (", ".join(r["axioms"]) or "none") + "; proof " + r["proof"]
        else:
            e["status"] = "open"
            e["composition"] = "failed: " + r["reason"]
            if not e["open"]:
                e["open"] = [("(every hypothesis is discharged at its instance;" if e["hypotheses"] else
                              "(no hypothesis beyond the side conditions;") + " the composition for every period did not close)"]
    return entries


def recorded(entry, claims):
    """The refuted claims of the register that already record this route: they
    name the conditional refutation, or cite one of its refuting theorems."""
    short = entry["theorem"].rsplit(".", 1)[-1]
    return sorted(c["id"] for c in claims if c["status"] == "refuted" and (
        c.get("lean") == entry["theorem"] or c.get("lean") in entry["refutedBy"]
        or short in (c.get("statement") or "") or short in (c.get("note") or "")))


def report(entries, keys, claims=None):
    claims = frontier.load()["claim"] if claims is None else claims
    counts = {st: sum(1 for e in entries if e["status"] == st) for st in STATUSES}
    for e in entries:
        e["recordedBy"] = recorded(e, claims) if e["status"] == "dead" else []
    return {"counts": counts, "conditionals": entries, "keys": keys,
            "live": [e["theorem"] for e in entries if e["status"] == "live-discharged"],
            "unrecorded_dead": [e["theorem"] for e in entries if e["status"] == "dead" and not e["recordedBy"]]}


def run(package_dir=None, modules=None):
    """The audit of the current library: introspection, classification, compositions."""
    full, conclusions = introspect(package_dir, modules)
    entries, keys = classify(full, conclusions)
    discharges = [{"theorem": e["theorem"], "kind": e["kind"], "table": table(e, keys),
                   "content": " ".join(str(h["position"]) for h in e["hypotheses"])}
                  for e in entries if e["status"] != "dead" and table(e, keys)]
    candidates = [{"theorem": e["theorem"], "kind": e["kind"], "table": table(e, keys)}
                  for e in entries if e["status"] == "candidate"]
    found, results = decide(discharges, candidates, package_dir, modules)
    return report(settle(entries, found, results), keys)


# --- the register: model/audit.toml -------------------------------------

def _q(v):
    return '"' + str(v).replace("\\", "\\\\").replace('"', '\\"') + '"'


def _l(xs):
    return "[" + ", ".join(_q(x) for x in xs) + "]"


def register_toml(rep):
    lines = ['spec = "r30/audit/1"', "# @generated by `bin/r30 audit --write`: the conditional refutations of the period",
             "# in the research library, each classified by exact facts about theorems (tools/r30/auditmodel.py),",
             "# and the hypothesis keys with their refutations under a period and their discharges.", ""]
    for e in rep["conditionals"]:
        lines += ["[[conditional]]", f"theorem = {_q(e['theorem'])}", f"kind = {_q(e['kind'])}", f"status = {_q(e['status'])}",
                  f"refutedBy = {_l(e['refutedBy'])}", f"dischargedBy = {_l(e['dischargedBy'])}", f"open = {_l(e['open'])}",
                  f"recordedBy = {_l(e.get('recordedBy', []))}", f"composition = {_q(e['composition'])}", ""]
        for h in e["hypotheses"]:
            lines += ["[[conditional.hypothesis]]", f"binder = {_q(h['binder'])}", f"position = {int(h['position'])}",
                      f"key = {_q(h['key'])}", f"label = {_q(h['label'])}", f"status = {_q(h['status'])}",
                      f"dischargedBy = {_q(h['dischargedBy'])}", ""]
    for k in sorted(rep["keys"]):
        row = rep["keys"][k]
        lines += ["[[key]]", f"key = {_q(k)}", f"refutedBy = {_l(row['refutedBy'])}",
                  f"dischargedUnderPeriod = {_l(row['dischargedUnderPeriod'])}",
                  f"dischargedWithoutPeriod = {_l(row['dischargedWithoutPeriod'])}", ""]
    return "\n".join(lines)


def _read(text):
    data = tomllib.loads(text)
    rows = data.get("conditional", [])
    for r in rows:
        r["hypotheses"] = r.pop("hypothesis", [])
        r.setdefault("dischargedBy", [])
    keys = {k.pop("key"): k for k in data.get("key", [])}
    return rows, keys


def load():
    """The last written audit (model/audit.toml): (conditionals, keys), or None."""
    if not REGISTER.exists():
        return None
    return _read(REGISTER.read_text())


def problems(rows):
    """What Audit.lex.tex decides, checked first so a failure names the row."""
    out = []
    names = [r["theorem"] for r in rows]
    if len(set(names)) != len(names):
        out.append("theorem names are not distinct")
    for r in rows:
        if r["status"] not in STATUSES:
            out.append(f"{r['theorem']}: status {r['status']} is not one of {', '.join(STATUSES)}")
        if r["status"] == "dead" and not r["refutedBy"]:
            out.append(f"{r['theorem']}: dead without a refuting theorem")
    return out


# --- the module: src/Audit.lex.tex --------------------------------------

def _count(name, status):
    return definition(name, NAT,
                      match_list(var("xs"), n(0), "head", "tail",
                                 if_(eq_string(proj(var("head"), "status"), s(status)),
                                     {"kind": "add", "left": n(1), "right": call(name, var("tail"))},
                                     call(name, var("tail")))),
                      parameters=[("xs", list_t(named("Conditional")))], recursive="xs")


def segments(name):
    """A Lean name as the list of its segments, each separator `.` or `_` kept at
    the front of the segment it opens, so that the segments join to the name."""
    import re
    return [x for x in re.split(r"(?=[._])", name) if x]


def declarations(rows, keys):
    c_t = named("Conditional")
    nonempty = lambda field: {"kind": "match", "scrutinee": proj(var("head"), field), "branches": [
        {"constructor": {"name": "List.nil"}, "binders": [], "body": b(False)},
        {"constructor": {"name": "List.cons"}, "binders": ["r", "rs"], "body": b(True)}]}
    return [
        # `theorem` is the Lean name as its segments (`segments`): ["Rule30UOR", ".Band", ".problem1", "_of", ...]
        structure("Conditional", [("theorem", list_t(STR)), ("hypotheses", list_t(STR)), ("status", STR),
                                  ("refutedBy", list_t(STR)), ("dischargedBy", list_t(STR))]),
        definition("conditionals", list_t(c_t), lst([
            record("Conditional", theorem=strings(segments(r["theorem"])), hypotheses=strings([h["label"] for h in r["hypotheses"]]),
                   status=s(r["status"]), refutedBy=strings(r["refutedBy"]), dischargedBy=strings(r["dischargedBy"]))
            for r in rows], c_t)),
        definition("statuses", list_t(STR), strings(list(STATUSES))),
        member_string(), all_members(),
        # distinct names, decided over their segments: two names are compared segment by
        # segment and part at their first differing segment, a few characters long,
        # where comparing whole names of a few hundred conditional refutations exceeds
        # lexlean's child timeout
        definition("sameName", BOOL,
                   match_list(var("a"), match_list(var("b"), b(True), "y", "ys", b(False)), "x", "xs",
                              match_list(var("b"), b(False), "y", "ys",
                                         if_(eq_string(var("x"), var("y")), call("sameName", var("xs"), var("ys")), b(False)))),
                   parameters=[("a", list_t(STR)), ("b", list_t(STR))], recursive="a"),
        definition("memberName", BOOL,
                   match_list(var("names"), b(False), "head", "tail",
                              if_(call("sameName", var("name"), var("head")), b(True), call("memberName", var("name"), var("tail")))),
                   parameters=[("name", list_t(STR)), ("names", list_t(list_t(STR)))], recursive="names"),
        definition("distinctNames", BOOL,
                   match_list(var("names"), b(True), "head", "tail",
                              if_(call("memberName", var("head"), var("tail")), b(False), call("distinctNames", var("tail")))),
                   parameters=[("names", list_t(list_t(STR)))], recursive="names"),
        field_of_each("conditionalTheorems", c_t, "theorem", result=list_t(STR)),
        field_of_each("conditionalStatuses", c_t, "status"),
        # a dead entry names at least one refuting theorem
        definition("deadNameRefutations", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(eq_string(proj(var("head"), "status"), s("dead")),
                                  if_(nonempty("refutedBy"), call("deadNameRefutations", var("tail")), b(False)),
                                  call("deadNameRefutations", var("tail")))),
                   parameters=[("xs", list_t(c_t))], recursive="xs"),
        _count("deadCount", "dead"), _count("liveCount", "live-discharged"), _count("openCount", "open"),
        holds("everyDeadNamesARefutation", call("deadNameRefutations", call("conditionals"))),
        holds("statusesDeclared", call("allMembers", call("conditionalStatuses", call("conditionals")), call("statuses"))),
        holds("theoremNamesDistinct", call("distinctNames", call("conditionalTheorems", call("conditionals")))),
        theorem("deadCountIs", call("deadCount", call("conditionals")), n(sum(r["status"] == "dead" for r in rows))),
        theorem("liveCountIs", call("liveCount", call("conditionals")), n(sum(r["status"] == "live-discharged" for r in rows))),
        theorem("openCountIs", call("openCount", call("conditionals")), n(sum(r["status"] == "open" for r in rows))),
    ]


def render(rows, keys):
    from . import lexmod
    return lexmod.module("Audit", declarations(rows, keys))


# The `--json` report of `bin/r30 audit` (`r30/audit-result/1`), closed like
# the result schemas of `schema.py`; `prismmodel` publishes it with its contract.
_NAMES = {"type": "array", "items": {"type": "string"}}
_STATUS = {"type": "string", "enum": list(STATUSES)}
RESULT_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "r30/audit-result/1",
    "title": "audit --json: the conditional refutations of the period, each dead, live-discharged or open",
    "type": "object", "additionalProperties": False, "required": ["counts", "conditionals", "keys", "live", "unrecorded_dead"],
    "properties": {
        "counts": {"type": "object", "additionalProperties": False, "required": list(STATUSES),
                   "properties": {st: {"type": "integer"} for st in STATUSES}},
        "conditionals": {"type": "array", "items": {
            "type": "object", "additionalProperties": False,
            "required": ["theorem", "kind", "status", "hypotheses", "refutedBy", "dischargedBy", "open", "composition", "recordedBy"],
            "properties": {
                "theorem": {"type": "string"},
                "kind": {"type": "string", "enum": ["periodic", "centerPer", "problem1"]},
                "status": _STATUS, "refutedBy": _NAMES, "dischargedBy": _NAMES, "open": _NAMES, "recordedBy": _NAMES,
                "composition": {"type": "string"},
                "hypotheses": {"type": "array", "items": {
                    "type": "object", "additionalProperties": False,
                    "required": ["binder", "position", "key", "label", "status", "dischargedBy"],
                    "properties": {"binder": {"type": "string"}, "position": {"type": "integer"}, "key": {"type": "string"},
                                   "label": {"type": "string"},
                                   "status": {"type": "string", "enum": ["refuted", "discharged", "open"]},
                                   "dischargedBy": {"type": "string"}}}},
            }}},
        "keys": {"type": "object", "additionalProperties": {
            "type": "object", "additionalProperties": False,
            "required": ["refutedBy", "dischargedUnderPeriod", "dischargedWithoutPeriod"],
            "properties": {"refutedBy": _NAMES, "dischargedUnderPeriod": _NAMES, "dischargedWithoutPeriod": _NAMES}}},
        "live": _NAMES,
        "unrecorded_dead": _NAMES,
    },
}
SCHEMA_FILE = API / "schemas" / "audit-result.schema.json"
CONTRACT = {"schema": "r30/audit-result/1", "path": "schemas/audit-result.schema.json",
            "media_type": "application/vnd.r30.audit-result.v1+json", "identity": "sha256-canonical-json",
            "maximum_bytes": 16777216, "maximum_items": 65536, "extension_policy": "closed",
            "compatibility": "exact-major", "produced_by": "audit", "artifact": "--json"}


def files():
    """What `api sync` writes and `api check` compares: the result schema, and
    the module rendered from the register (once `audit --write` recorded one)."""
    import json
    record = load()
    out = {SCHEMA_FILE: json.dumps(RESULT_SCHEMA, indent=1) + "\n"}
    if record is not None:
        out[MODULE] = render(*record)
    return out


def write(rep):
    """model/audit.toml and src/Audit.lex.tex from a report; refused when the data
    violates what the module decides. Returns the problems (empty when written)."""
    text = register_toml(rep)
    rows, keys = _read(text)
    bad = problems(rows)
    if bad:
        return bad
    REGISTER.parent.mkdir(parents=True, exist_ok=True)
    REGISTER.write_text(text)
    MODULE.write_text(render(rows, keys))
    return []


# --- what the register and the commands read ----------------------------

def related(claim, rows=None):
    """The audit entries a claim concerns: the claim's Lean name is the
    conditional refutation or the key of one of its hypotheses, or the claim's
    statement or note names the conditional refutation. Each with its status
    and its open hypotheses (the obligations the claim carries)."""
    if rows is None:
        record = load()
        rows = record[0] if record else []
    text = (claim.get("statement") or "") + " " + (claim.get("note") or "")
    lean = claim.get("lean")
    out = []
    for r in rows:
        if (lean and (r["theorem"] == lean or any(h["key"] == lean for h in r["hypotheses"]))) \
                or r["theorem"].rsplit(".", 1)[-1] in text:
            out.append({"theorem": r["theorem"], "status": r["status"], "open": r["open"], "refutedBy": r["refutedBy"]})
    return out


def _short(name):
    return name.replace("Rule30UOR.", "").replace("Ruliology.CellularAutomata.Rule30Prize.", "")


def render_table(rep):
    lines = [f"conditional refutations of the period: {len(rep['conditionals'])}  "
             + "  ".join(f"{st.upper()} {rep['counts'][st]}" for st in STATUSES), ""]
    if rep["live"]:
        lines += ["!!! LIVE-DISCHARGED: the composition closed in Lean; this is a proof of Problem 1 !!!"]
        for e in rep["conditionals"]:
            if e["status"] == "live-discharged":
                lines += [f"  {e['theorem']}", f"    {e['composition']}"]
        lines.append("")
    lines.append(f"{'STATUS':16s} {'THEOREM':72s} HYPOTHESES -> REFUTED BY | OPEN")
    for e in rep["conditionals"]:
        hyps = ", ".join(_short(h["label"]) for h in e["hypotheses"]) or "-"
        tail = (" -> " + ", ".join(_short(r) for r in e["refutedBy"][:3]) + (" ..." if len(e["refutedBy"]) > 3 else "")
                if e["status"] == "dead" else " | open: " + "; ".join(_short(o) for o in e["open"])
                if e["status"] == "open" else "")
        lines.append(f"{e['status'].upper():16s} {_short(e['theorem']):72s} {hyps}{tail}")
    if rep["unrecorded_dead"]:
        lines += ["", "DEAD routes not recorded as refuted in frontier.toml (evidence: the refuting theorems above):"]
        lines += [f"  {_short(t)}" for t in rep["unrecorded_dead"]]
    return "\n".join(lines)
