"""The engine as a LexLean model: the workload, the portfolio, the learning rule
and the scheduler.

`rule30-api/src/Engine.lex.tex` declares, as data the kernel decides about:

- the workload: the GitHub Actions workflow that runs the engine
  (`.github/workflows/engine.yml`, rendered from this data by `bin/r30 api
  sync` and drift-checked by `api check`): its triggers, the cron minutes,
  the concurrency group, the runner, the timeout, the permissions, the one
  secret it may read, the actions it uses, the stages of a tick with their
  budgets, and the cache families; the decided theorems are that no secret
  but `GITHUB_TOKEN` is read, that the permissions are exactly `contents`
  and `actions` with `write`, that the stage budgets fill the tick budget
  and with the setup fit the timeout, that the gate keeps its share, that
  the cron minutes are off the hour and thirty minutes apart, that there is
  one concurrency group and runs never cancel each other, and that every
  action used is one the repository already used;
- the portfolio of deduction strategies (`deduce.py`), each pinned by the
  SHA-256 of its template file (`tools/r30/templates/`) and of the renderer
  that fills it (`deduce.py`): the ids and the digests are distinct, and
  `api check` refuses a template or renderer whose digest drifted;
- the learning layer, literally neuromorphic: the units are the basis
  sequences (`Sequences.lex.tex`), the synapses the observed and proved
  relations of the register, the events the ticks. Plasticity is the
  bounded Hebbian rule `learn` on integer strategy weights per relation
  family (an attempt that proves, refutes or finds the relation in the
  library raises the weight of its strategy for the relation's family by
  `RAISE`, a failure lowers it by `LOWER`, clamped to `[W_MIN, W_MAX]`),
  `learnAll` folds a tick's outcomes into the table, and `schedule` orders
  the applicable strategies by weight, ties by portfolio order. Homeostasis
  is the budget regulation of a tick (`engine.py`); consolidation is the
  table committed to main with each tick (`model/engine.toml`, the
  `committedWeights` here). The kernel decides that `learn` keeps every
  weight of its domain in bounds, that the committed table is in bounds,
  that the schedule of every subset of the portfolio under the committed
  table, in every family, is a permutation of the subset ordered by weight,
  and the frozen fixtures.

`learnAll` and `schedule`, with `mint` of Hypotheses.lex.tex, are production
roots (rust-std): `bin/r30 api production` exports them to certified Rust and
`engine_rust.py` drives them; they have no other runtime."""

import hashlib
import json
from pathlib import Path

from . import repo
from .semantic import (BOOL, NAT, STR, b, beq, ble, blt, call, definition, field_of_each, holds, if_, list_t, lst,
                       match_list, member_string, all_members, n, proj, record, s, strings, structure, var)

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Engine.lex.tex"
NAME = "Engine"
LEAN_MODULE = "Rule30Api.Engine"
WORKFLOW = repo.ROOT / ".github" / "workflows" / "engine.yml"
TEMPLATES = Path(__file__).with_name("templates")
EFFECTS = {"effects": ["allocation", "overflow", "recursion"], "targets": ["rust-std"]}
PRODUCTION_ROOTS = {"learnAll": EFFECTS, "schedule": EFFECTS}
HYPOTHESES_MODULE, HYPOTHESES_ROOTS = "Rule30Api.Hypotheses", {"mint": EFFECTS}

# ------------------------------------------------------------ plasticity

W_MIN, W_MAX, W_INIT, RAISE, LOWER = 1, 16, 8, 2, 1
SUCCESS = ("proved", "known", "refuted")  # outcomes that potentiate

# The families of relations (deduce.family): the systems a relation reads and how it reads time.
FAMILIES = [f"{sys_}-{t}" for sys_ in ("right", "left", "joint") for t in ("plain", "shift", "dilated")] + ["open"]

# ------------------------------------------------------------ the portfolio

PORTFOLIO = [
    {"id": "library-rewrite", "template": "library-rewrite.lean.tmpl",
     "statement": "the columns rewritten into the diagonals, one rule step unfolded, the library's equalities among "
                  "the constants instantiated, closed by Boolean case analysis; a library theorem stating the "
                  "relation itself proves the claim"},
    {"id": "step-induction", "template": "step-induction.lean.tmpl",
     "statement": "the diagonals the relation reads as a finite system stepped by the rule; by induction the state "
                  "stays in the orbit the kernel decides, on which the relation holds"},
    {"id": "period-reduction", "template": "period-reduction.lean.tmpl",
     "statement": "every column a word of the right system read from the row register modulo its period 2^j; the "
                  "kernel decides the residues"},
    {"id": "counterexample", "template": "counterexample.lean.tmpl",
     "statement": "the rule iterated from time 0 to a time where the relation fails beyond its window; the kernel "
                  "decides the failure and the claim is refuted"},
]
ORBIT_BOUND = 256        # step-induction: the largest orbit the kernel decides
PERIOD_BOUND = 256       # period-reduction: the largest period 2^j whose residues the kernel decides
ATTEMPT_TIMEOUT = 600    # seconds of one Lean process


def template_path(strategy):
    return TEMPLATES / next(p["template"] for p in PORTFOLIO if p["id"] == strategy)


RENDERER = Path(__file__).with_name("deduce.py")


def template_digest(strategy):
    """What renders an attempt: the template file and the renderer (`deduce.py`) that fills it. A
    change to either is a new digest, so the claims it applies to are attempted again; an attempt
    with an unchanged digest never is (the redundancy rule)."""
    h = hashlib.sha256()
    h.update(b"template\0" + template_path(strategy).read_bytes() + b"\0renderer\0" + RENDERER.read_bytes())
    return "sha256:" + h.hexdigest()


# ------------------------------------------------------------ the workload

PUSH_PATHS = ["tools/r30/**", "rule30-core-lean/**", "rule30-api/src/**", "rule30-api/model/sequences.toml",
              "frontier.toml", "scripts/**", "Makefile", ".github/workflows/engine.yml", ".github/actions/**"]
LAKE_DIRS = ["Rule30PrizeKit/lean/.lake", "rule30-core-lean/.lake", "rule30-bridge/.lake", "rule30-paper/.lake",
             "rule30-lexlean/.lake", "rule30-api/.lake"]
BUNDLE_DIR = "rule30-api/.lexlean/production"
# what the bundle is built from: a new key only when one of these changed
BUNDLE_INPUTS = ["rule30-api/src/**", "rule30-api/stdlib/**", "rule30-api/language/**", "lexlean-stdlib/**",
                 "rule30-api/lexlean.toml", "rule30-api/lean-toolchain", "rule30-api/lexlean.lock",
                 "rule30-api/production/request.json", ".github/lexlean-revision"]
WORKLOAD = {
    "workflow": "Engine", "file": ".github/workflows/engine.yml", "repository": "afflom/rule30",
    "runsOn": "ubuntu-24.04", "timeoutMinutes": 355, "setupMinutes": 55, "tickBudget": 300,  # the setup holds a cold bundle
    "cronMinutes": [17, 47], "concurrencyGroup": "r30-engine", "cancelInProgress": False,
    "killSwitch": "R30_ENGINE", "secrets": ["GITHUB_TOKEN"],
    "permissions": [("contents", "write"), ("actions", "write")],
    "triggers": [("schedule", "17,47 * * * *"), ("workflow_dispatch", "manual"), ("push", "main")],
    "actions": ["actions/checkout@v4", "actions/cache/restore@v4", "actions/cache/save@v4",
                "./.github/actions/setup-proof-tools"],
    "allowedActions": ["actions/checkout@v4", "actions/cache@v4", "actions/cache/restore@v4", "actions/cache/save@v4",
                       "actions/upload-artifact@v4", "actions/upload-pages-artifact@v3", "actions/deploy-pages@v4",
                       "dtolnay/rust-toolchain@stable", "./.github/actions/setup-proof-tools"],
    # the stages of a tick with their budget shares (minutes of the tick budget); the gate's share is
    # reserved first and never cut
    "stages": [("build", 60, False), ("induction", 30, False), ("pruning", 20, False), ("deduction", 95, False),
               ("learning", 5, False), ("hypotheses", 5, False), ("gate", 85, True)],
    "hypothesisBudget": 16,  # the most `Hypotheses.mint` adds in one full tick
    "gateMinimum": 60,
    # cache families (actions/cache): the compiler, the certified bundle, the Lake builds, the gate's evidence
    # (pruned, never a certificate) and the settled marker of a commit the engine has nothing more to do on
    "caches": [("lexlean", ".local"), ("bundle", BUNDLE_DIR), ("lake", "\n".join(LAKE_DIRS)), ("gate", ".git/rule30-validation"),
               ("settled", ".r30/settled")],
    "identity": ("r30-engine", "r30-engine@users.noreply.github.com"),
}


def cron():
    return ",".join(str(m) for m in WORKLOAD["cronMinutes"]) + " * * * *"


def schedule(weights, fam, applicable):
    """The learned order of the applicable strategies, by the certified root (`engine_rust.NoRoot` when it cannot run)."""
    from . import engine_rust
    return engine_rust.runner().schedule([(r["strategy"], r["family"], r["value"]) for r in weights], fam, applicable)


def initial_table():
    return [(p["id"], f, W_INIT) for p in PORTFOLIO for f in FAMILIES]


# ------------------------------------------------------------ the module

WEIGHT_T = {"kind": "named", "member": {"name": "Weight"}, "arguments": []}
OUTCOME_T = {"kind": "named", "member": {"name": "Outcome"}, "arguments": []}
STRATEGY_T = {"kind": "named", "member": {"name": "Strategy"}, "arguments": []}
STAGE_T = {"kind": "named", "member": {"name": "Stage"}, "arguments": []}
PERM_T = {"kind": "named", "member": {"name": "Permission"}, "arguments": []}
TRIGGER_T = {"kind": "named", "member": {"name": "Trigger"}, "arguments": []}
CACHE_T = {"kind": "named", "member": {"name": "CacheFamily"}, "arguments": []}
LS = list_t(STR)
LN = list_t(NAT)


def _and(a, c):
    return {"kind": "and", "left": a, "right": c}


def _not(a):
    return {"kind": "not", "value": a}


def _eqs(a, c):
    return {"kind": "primitive", "operation": "equal", "result": BOOL, "arguments": [a, c]}


def _p(op, args, result):
    return {"kind": "primitive", "operation": op, "result": result, "arguments": list(args)}


def _add(a, c):
    return {"kind": "add", "left": a, "right": c}


def _sub(a, c):
    return _p("subtract", [a, c], NAT)


def _len(x):
    return _p("length", [x], NAT)


def _cons(h, t):
    return {"kind": "cons", "head": h, "tail": t}


def _nil(t):
    return {"kind": "nil", "element": t}


def _ex(name, result, body, parameters=(), recursive=None):
    return definition(name, result, body, parameters=parameters, recursive=recursive,
                      production=PRODUCTION_ROOTS.get(name), executable=True)


def _weight(st, f, v):
    return record("Weight", strategy=s(st), family=s(f), value=n(v))


def _outcome(st, f, ok):
    return record("Outcome", strategy=s(st), family=s(f), success=b(ok))


def _match_nat(scrutinee, zero_body, binder, succ_body):
    return {"kind": "match", "scrutinee": scrutinee, "branches": [
        {"constructor": {"name": "Nat.zero"}, "binders": [], "body": zero_body},
        {"constructor": {"name": "Nat.succ"}, "binders": [binder], "body": succ_body}]}


def learning_declarations():
    w, x, xs, h, t = var("w"), var("x"), var("xs"), var("head"), var("tail")
    table, fam, st = var("table"), var("family"), var("strategy")
    matches = lambda r: _and(_eqs(proj(r, "strategy"), st), _eqs(proj(r, "family"), fam))
    return [
        structure("Weight", [("strategy", STR), ("family", STR), ("value", NAT)]),
        structure("Outcome", [("strategy", STR), ("family", STR), ("success", BOOL)]),
        definition("weightMin", NAT, n(W_MIN), executable=True),
        definition("weightMax", NAT, n(W_MAX), executable=True),
        definition("weightInitial", NAT, n(W_INIT), executable=True),
        # plasticity: the bounded Hebbian rule
        _ex("learn", NAT,
            if_(var("success"),
                if_(ble(_add(w, n(RAISE)), n(W_MAX)), _add(w, n(RAISE)), n(W_MAX)),
                if_(ble(n(W_MIN + LOWER), w), _sub(w, n(LOWER)), n(W_MIN))),
            parameters=[("w", NAT), ("success", BOOL)]),
        _ex("weightOf", NAT,
            match_list(table, n(W_INIT), "head", "tail",
                       if_(matches(h), proj(h, "value"), call("weightOf", st, fam, t))),
            parameters=[("strategy", STR), ("family", STR), ("table", list_t(WEIGHT_T))], recursive="table"),
        _ex("updateWeight", list_t(WEIGHT_T),
            match_list(table,
                       _cons(record("Weight", strategy=st, family=fam, value=call("learn", n(W_INIT), var("success"))),
                             _nil(WEIGHT_T)),
                       "head", "tail",
                       if_(matches(h),
                           _cons(record("Weight", strategy=st, family=fam, value=call("learn", proj(h, "value"), var("success"))), t),
                           _cons(h, call("updateWeight", t, st, fam, var("success"))))),
            parameters=[("table", list_t(WEIGHT_T)), ("strategy", STR), ("family", STR), ("success", BOOL)],
            recursive="table"),
        _ex("learnAll", list_t(WEIGHT_T),
            match_list(var("outcomes"), table, "head", "tail",
                       call("learnAll", call("updateWeight", table, proj(h, "strategy"), proj(h, "family"), proj(h, "success")), t)),
            parameters=[("table", list_t(WEIGHT_T)), ("outcomes", list_t(OUTCOME_T))], recursive="outcomes"),
        # the scheduler: insertion by weight, stable (ties keep portfolio order)
        _ex("insertByWeight", LS,
            match_list(var("ordered"), _cons(x, _nil(STR)), "head", "tail",
                       if_(blt(call("weightOf", h, fam, table), call("weightOf", x, fam, table)),
                           _cons(x, _cons(h, t)),
                           _cons(h, call("insertByWeight", fam, table, x, t)))),
            parameters=[("family", STR), ("table", list_t(WEIGHT_T)), ("x", STR), ("ordered", LS)], recursive="ordered"),
        _ex("scheduleFrom", LS,
            match_list(var("pending"), var("ordered"), "head", "tail",
                       call("scheduleFrom", fam, table, t, call("insertByWeight", fam, table, h, var("ordered")))),
            parameters=[("family", STR), ("table", list_t(WEIGHT_T)), ("pending", LS), ("ordered", LS)], recursive="pending"),
        _ex("schedule", LS, call("scheduleFrom", fam, table, var("applicable"), _nil(STR)),
            parameters=[("table", list_t(WEIGHT_T)), ("family", STR), ("applicable", LS)]),
        # the invariants' tests
        definition("inBounds", BOOL, _and(ble(n(W_MIN), w), ble(w, n(W_MAX))), parameters=[("w", NAT)]),
        definition("learnBoundedUpTo", BOOL,
                   _match_nat(var("k"),
                              if_(call("inBounds", n(0)), _and(call("inBounds", call("learn", n(0), b(True))),
                                                               call("inBounds", call("learn", n(0), b(False)))), b(True)),
                              "j",
                              _and(if_(call("inBounds", _add(var("j"), n(1))),
                                       _and(call("inBounds", call("learn", _add(var("j"), n(1)), b(True))),
                                            call("inBounds", call("learn", _add(var("j"), n(1)), b(False)))), b(True)),
                                   call("learnBoundedUpTo", var("j")))),
                   parameters=[("k", NAT)], recursive="k"),
        definition("weightsBounded", BOOL,
                   match_list(table, b(True), "head", "tail",
                              _and(call("inBounds", proj(h, "value")), call("weightsBounded", t))),
                   parameters=[("table", list_t(WEIGHT_T))], recursive="table"),
        definition("countString", NAT,
                   match_list(var("values"), n(0), "head", "tail",
                              _add(if_(_eqs(var("value"), h), n(1), n(0)), call("countString", var("value"), t))),
                   parameters=[("value", STR), ("values", LS)], recursive="values"),
        definition("sameCounts", BOOL,
                   match_list(var("probe"), b(True), "head", "tail",
                              _and(beq(call("countString", h, var("xs")), call("countString", h, var("ys"))),
                                   call("sameCounts", t, var("xs"), var("ys")))),
                   parameters=[("probe", LS), ("xs", LS), ("ys", LS)], recursive="probe"),
        definition("isPermutation", BOOL,
                   _and(beq(_len(var("xs")), _len(var("ys"))),
                        _and(call("sameCounts", var("xs"), var("xs"), var("ys")), call("sameCounts", var("ys"), var("xs"), var("ys")))),
                   parameters=[("xs", LS), ("ys", LS)]),
        definition("byWeight", BOOL,
                   match_list(var("ordered"), b(True), "head", "tail",
                              match_list(t, b(True), "later", "more",
                                         _and(ble(call("weightOf", var("later"), fam, table), call("weightOf", h, fam, table)),
                                              call("byWeight", table, fam, t)))),
                   parameters=[("table", list_t(WEIGHT_T)), ("family", STR), ("ordered", LS)], recursive="ordered"),
        definition("scheduleSound", BOOL,
                   _and(call("isPermutation", call("schedule", table, fam, var("applicable")), var("applicable")),
                        call("byWeight", table, fam, call("schedule", table, fam, var("applicable")))),
                   parameters=[("table", list_t(WEIGHT_T)), ("family", STR), ("applicable", LS)]),
        definition("soundForSubsets", BOOL,
                   match_list(var("subsets"), b(True), "head", "tail",
                              _and(call("scheduleSound", table, fam, h), call("soundForSubsets", table, fam, t))),
                   parameters=[("table", list_t(WEIGHT_T)), ("family", STR), ("subsets", list_t(LS))], recursive="subsets"),
        definition("soundForFamilies", BOOL,
                   match_list(var("families"), b(True), "head", "tail",
                              _and(call("soundForSubsets", table, h, var("subsets")),
                                   call("soundForFamilies", table, t, var("subsets")))),
                   parameters=[("table", list_t(WEIGHT_T)), ("families", LS), ("subsets", list_t(LS))], recursive="families"),
    ]


def subsets(ids):
    out = []
    for mask in range(1 << len(ids)):
        out.append([x for i, x in enumerate(ids) if mask >> i & 1])
    return out


FIXTURE_OUTCOMES = [("step-induction", "left-plain", True), ("library-rewrite", "left-plain", False),
                    ("library-rewrite", "left-plain", False), ("period-reduction", "right-shift", True),
                    ("step-induction", "right-shift", False), ("counterexample", "open", False)]
# what the kernel decides `learnAll` and `schedule` answer on them (Engine.lex.tex)
FIXTURE_LEARNED = {("step-induction", "left-plain"): 10, ("library-rewrite", "left-plain"): 6,
                   ("period-reduction", "right-shift"): 10, ("step-induction", "right-shift"): 7,
                   ("counterexample", "open"): 7}
FIXTURE_SCHEDULES = [("left-plain", ["library-rewrite", "step-induction", "period-reduction"],
                      ["step-induction", "period-reduction", "library-rewrite"]),
                     ("right-shift", ["library-rewrite", "step-induction", "period-reduction"],
                      ["period-reduction", "library-rewrite", "step-induction"]),
                     ("open", ["library-rewrite"], ["library-rewrite"])]


def fixture_declarations(committed):
    ids = [p["id"] for p in PORTFOLIO]
    start = initial_table()
    learned = [(a, c, FIXTURE_LEARNED.get((a, c), v)) for a, c, v in start]
    decls = [
        definition("initialWeights", list_t(WEIGHT_T), lst([_weight(*r) for r in start], WEIGHT_T), executable=True),
        definition("fixtureOutcomes", list_t(OUTCOME_T), lst([_outcome(*o) for o in FIXTURE_OUTCOMES], OUTCOME_T),
                   executable=True),
        definition("fixtureLearned", list_t(WEIGHT_T), lst([_weight(*r) for r in learned], WEIGHT_T), executable=True),
        definition("committedWeights", list_t(WEIGHT_T), lst([_weight(*r) for r in committed], WEIGHT_T), executable=True),
        definition("strategyIds", LS, strings(ids)),
        definition("familyIds", LS, strings(FAMILIES)),
        definition("portfolioSubsets", list_t(LS), lst([strings(x) for x in subsets(ids)], LS)),
        definition("sameWeights", BOOL,
                   match_list(var("xs"), beq(_len(var("ys")), n(0)), "head", "tail",
                              match_list(var("ys"), b(False), "y", "rest",
                                         _and(_and(_eqs(proj(var("head"), "strategy"), proj(var("y"), "strategy")),
                                                   _eqs(proj(var("head"), "family"), proj(var("y"), "family"))),
                                              _and(beq(proj(var("head"), "value"), proj(var("y"), "value")),
                                                   call("sameWeights", var("tail"), var("rest")))))),
                   parameters=[("xs", list_t(WEIGHT_T)), ("ys", list_t(WEIGHT_T))], recursive="xs"),
        definition("sameStrings", BOOL,
                   match_list(var("xs"), beq(_len(var("ys")), n(0)), "head", "tail",
                              match_list(var("ys"), b(False), "y", "rest",
                                         _and(_eqs(var("head"), var("y")), call("sameStrings", var("tail"), var("rest"))))),
                   parameters=[("xs", LS), ("ys", LS)], recursive="xs"),
        holds("learnStaysInBounds", call("learnBoundedUpTo", n(W_MAX))),
        holds("initialWeightsBounded", call("weightsBounded", call("initialWeights"))),
        holds("committedWeightsBounded", call("weightsBounded", call("committedWeights"))),
        holds("learnAllFixture", call("sameWeights", call("learnAll", call("initialWeights"), call("fixtureOutcomes")),
                                      call("fixtureLearned"))),
        holds("learnAllFixtureBounded", call("weightsBounded", call("learnAll", call("initialWeights"), call("fixtureOutcomes")))),
        holds("everyScheduleIsSound", call("soundForFamilies", call("committedWeights"), call("familyIds"),
                                           call("portfolioSubsets"))),
    ]
    for i, (fam, apps, expected) in enumerate(FIXTURE_SCHEDULES):
        decls.append(holds(f"scheduleFixture{i}", call("sameStrings",
                                                       call("schedule", call("fixtureLearned"), s(fam), strings(apps)),
                                                       strings(expected))))
    return decls


def workload_declarations():
    wl = WORKLOAD
    h, t = var("head"), var("tail")
    stage_budget_sum = definition(
        "budgetSum", NAT, match_list(var("xs"), n(0), "head", "tail", _add(proj(h, "budget"), call("budgetSum", t))),
        parameters=[("xs", list_t(STAGE_T))], recursive="xs")
    gate_share = definition(
        "gateShare", NAT, match_list(var("xs"), n(0), "head", "tail",
                                     _add(if_(proj(h, "gate"), proj(h, "budget"), n(0)), call("gateShare", t))),
        parameters=[("xs", list_t(STAGE_T))], recursive="xs")
    perms_ok = definition(
        "permissionsWrite", BOOL,
        match_list(var("xs"), b(True), "head", "tail",
                   _and(_and(call("memberString", proj(h, "scope"), strings(["contents", "actions"])),
                             _eqs(proj(h, "access"), s("write"))), call("permissionsWrite", t))),
        parameters=[("xs", list_t(PERM_T))], recursive="xs")
    off_hour = definition(
        "offTheHour", BOOL,
        match_list(var("xs"), b(True), "head", "tail",
                   _and(_and(blt(n(0), h), blt(h, n(60))), call("offTheHour", t))),
        parameters=[("xs", LN)], recursive="xs")
    every30 = definition(
        "thirtyApart", BOOL,
        match_list(var("xs"), b(False), "head", "tail",
                   match_list(t, b(False), "later", "more",
                              _and(beq(var("later"), _add(h, n(30))), beq(_len(var("more")), n(0))))),
        parameters=[("xs", LN)])
    distinct = definition(
        "distinctStrings", BOOL,
        match_list(var("values"), b(True), "head", "tail",
                   _and(_not(call("memberString", h, t)), call("distinctStrings", t))),
        parameters=[("values", LS)], recursive="values")
    nonempty = definition(
        "allNonEmpty", BOOL,
        match_list(var("values"), b(True), "head", "tail", _and(_not(_eqs(h, s(""))), call("allNonEmpty", t))),
        parameters=[("values", LS)], recursive="values")
    return [
        structure("Trigger", [("event", STR), ("value", STR)]),
        structure("Permission", [("scope", STR), ("access", STR)]),
        structure("Stage", [("id", STR), ("budget", NAT), ("gate", BOOL)]),
        structure("CacheFamily", [("id", STR), ("path", STR)]),
        structure("Strategy", [("id", STR), ("template", STR), ("digest", STR)]),
        definition("workflowName", STR, s(wl["workflow"])),
        definition("workflowFile", STR, s(wl["file"])),
        definition("repository", STR, s(wl["repository"])),
        definition("runsOn", STR, s(wl["runsOn"])),
        definition("timeoutMinutes", NAT, n(wl["timeoutMinutes"])),
        definition("setupMinutes", NAT, n(wl["setupMinutes"])),
        definition("tickBudget", NAT, n(wl["tickBudget"])),
        definition("gateMinimum", NAT, n(wl["gateMinimum"])),
        definition("hypothesisBudget", NAT, n(wl["hypothesisBudget"])),
        definition("cronMinutes", LN, lst([n(m) for m in wl["cronMinutes"]], NAT)),
        definition("concurrencyGroups", LS, strings([wl["concurrencyGroup"]])),
        definition("cancelInProgress", BOOL, b(wl["cancelInProgress"])),
        definition("killSwitch", STR, s(wl["killSwitch"])),
        definition("secrets", LS, strings(wl["secrets"])),
        definition("permissions", list_t(PERM_T),
                   lst([record("Permission", scope=s(a), access=s(c)) for a, c in wl["permissions"]], PERM_T)),
        definition("triggers", list_t(TRIGGER_T),
                   lst([record("Trigger", event=s(a), value=s(c)) for a, c in wl["triggers"]], TRIGGER_T)),
        definition("pushPaths", LS, strings(PUSH_PATHS)),
        definition("actionsUsed", LS, strings(wl["actions"])),
        definition("actionsAllowed", LS, strings(wl["allowedActions"])),
        definition("stages", list_t(STAGE_T),
                   lst([record("Stage", id=s(a), budget=n(c), gate=b(g)) for a, c, g in wl["stages"]], STAGE_T)),
        definition("caches", list_t(CACHE_T),
                   lst([record("CacheFamily", id=s(a), path=s(c)) for a, c in wl["caches"]], CACHE_T)),
        definition("portfolio", list_t(STRATEGY_T),
                   lst([record("Strategy", id=s(p["id"]), template=s(p["template"]), digest=s(template_digest(p["id"])))
                        for p in PORTFOLIO], STRATEGY_T)),
        field_of_each("strategyIdsOf", STRATEGY_T, "id"),
        field_of_each("digestsOf", STRATEGY_T, "digest"),
        field_of_each("stageIdsOf", STAGE_T, "id"),
        field_of_each("cacheIdsOf", CACHE_T, "id"),
        stage_budget_sum, gate_share, perms_ok, off_hour, every30, distinct, nonempty,
        holds("onlyGithubToken", call("allMembers", call("secrets"), strings(["GITHUB_TOKEN"]))),
        holds("permissionsContentsActionsWrite",
              _and(call("permissionsWrite", call("permissions")), beq(_len(call("permissions")), n(2)))),
        holds("stageBudgetsFillTheTick", beq(call("budgetSum", call("stages")), call("tickBudget"))),
        holds("stageBudgetsFitTheTimeout", ble(_add(call("setupMinutes"), call("budgetSum", call("stages"))),
                                               call("timeoutMinutes"))),
        holds("gateKeepsItsShare", ble(call("gateMinimum"), call("gateShare", call("stages")))),
        holds("cronOffTheHour", _and(call("offTheHour", call("cronMinutes")), call("thirtyApart", call("cronMinutes")))),
        holds("concurrencySingle", _and(beq(_len(call("concurrencyGroups")), n(1)), _not(call("cancelInProgress")))),
        holds("actionsAlreadyUsed", call("allMembers", call("actionsUsed"), call("actionsAllowed"))),
        holds("portfolioIdsDistinct", call("distinctStrings", call("strategyIdsOf", call("portfolio")))),
        holds("templatesPinnedByDigest", _and(call("distinctStrings", call("digestsOf", call("portfolio"))),
                                              call("allNonEmpty", call("digestsOf", call("portfolio"))))),
        holds("stageIdsDistinct", call("distinctStrings", call("stageIdsOf", call("stages")))),
        holds("cacheIdsDistinct", call("distinctStrings", call("cacheIdsOf", call("caches")))),
    ]


THEOREMS = [
    {"name": "onlyGithubToken", "statement": "the workflow reads no secret but GITHUB_TOKEN"},
    {"name": "permissionsContentsActionsWrite", "statement": "the permissions are exactly contents and actions, with write"},
    {"name": "stageBudgetsFillTheTick", "statement": "the stage budgets sum to the tick budget"},
    {"name": "stageBudgetsFitTheTimeout", "statement": "the setup and the stage budgets fit the job timeout"},
    {"name": "gateKeepsItsShare", "statement": "the gate's share is at least its minimum"},
    {"name": "cronOffTheHour", "statement": "the cron minutes are off the hour and thirty minutes apart"},
    {"name": "concurrencySingle", "statement": "one concurrency group, and a run never cancels another"},
    {"name": "actionsAlreadyUsed", "statement": "every action the workflow uses is one the repository already used"},
    {"name": "portfolioIdsDistinct", "statement": "the strategy ids are distinct"},
    {"name": "templatesPinnedByDigest", "statement": "every template is pinned by a distinct, nonempty digest"},
    {"name": "learnStaysInBounds", "statement": "learn keeps every weight of [W_MIN, W_MAX] in bounds, on success and on failure"},
    {"name": "committedWeightsBounded", "statement": "the committed weights are in bounds"},
    {"name": "learnAllFixture", "statement": "learnAll on the fixture outcomes gives the frozen table"},
    {"name": "everyScheduleIsSound", "statement": "under the committed weights, the schedule of every subset of the portfolio in every family is a permutation of it ordered by weight"},
]


def declarations(committed):
    return [member_string(), all_members()] + workload_declarations() + learning_declarations() \
        + fixture_declarations(committed)


def committed_table():
    """The consolidated weights of model/engine.toml (the initial table when there is none)."""
    from . import engine
    rows = engine.load()["weight"]
    return [(r["strategy"], r["family"], r["value"]) for r in rows] or initial_table()


def render(committed=None):
    from . import lexmod
    return lexmod.module(NAME, declarations(committed_table() if committed is None else committed))


# ------------------------------------------------------------ the workflow

def render_workflow():
    wl = WORKLOAD
    run_if = "steps.tip.outputs.current == 'true' && steps.settled.outputs.cache-hit != 'true'"
    # a stale tick (main moved during the setup) did nothing: there is nothing new to cache
    save_if = f"always() && {run_if} && steps.tick.outputs.outcome != 'stale'"
    lake = "\n".join("            " + p for p in LAKE_DIRS)
    toolchain = "${{ hashFiles('rule30-core-lean/lean-toolchain', '.github/lexlean-revision') }}"
    bundle = "${{ hashFiles(" + ", ".join(f"'{p}'" for p in BUNDLE_INPUTS) + ") }}"
    paths = "\n".join(f'      - "{p}"' for p in PUSH_PATHS)
    name, email = wl["identity"]
    return f"""# Generated by `bin/r30 api sync` from rule30-api/src/Engine.lex.tex (tools/r30/enginemodel.py).
# Do not edit: `bin/r30 api check` refuses drift. The kernel decides the facts this file rests on
# (Engine.lex.tex): no secret but GITHUB_TOKEN, contents and actions write only, the stage budgets
# within the timeout, the cron off the hour, one concurrency group that never cancels a run.
#
# One tick of the engine (`bin/r30 engine tick`), on the certified bundle of the production roots (restored,
# or built here; a build that fails ends the job, there is no other runtime of the roots): build the library,
# induction (sequences when their inputs changed, discover), pruning (audit), deduction (deduce), learning,
# hypotheses (mint), then the commit through the unchanged pre-commit gate and a push only when main has not moved. Pushes made with
# GITHUB_TOKEN start no workflow, so the engine never triggers itself; the view is dispatched.
# A commit the engine has nothing more to do on (an idle tick), or one whose tick the gate refused or
# a stage failed on, is marked settled (a cache entry), and later ticks on it stop after the checkout
# until a new commit reaches main; a tick cut by its budget settles nothing. A run whose commit is no
# longer the tip of main (queued while an earlier tick pushed) stops after the checkout too. Before
# caching, the gate's evidence is pruned to what the next run can use (`bin/r30 engine prune`: the
# current tools key, the newest LexLean attestation per project, never a certificate), and each cache
# family keeps its newest entry. The kill switch is the repository variable {wl['killSwitch']}=off.
name: {wl['workflow']}

on:
  schedule:
    - cron: "{cron()}"
  workflow_dispatch:
  push:
    branches: [main]
    paths:
{paths}

permissions:
{chr(10).join(f'  {a}: {c}' for a, c in wl['permissions'])}

concurrency:
  group: {wl['concurrencyGroup']}
  cancel-in-progress: {'true' if wl['cancelInProgress'] else 'false'}

jobs:
  tick:
    name: One tick of the engine
    if: github.repository == '{wl['repository']}' && vars.{wl['killSwitch']} != 'off'
    runs-on: {wl['runsOn']}
    timeout-minutes: {wl['timeoutMinutes']}
    steps:
      - name: Checkout (full history, so the tick can push)
        uses: actions/checkout@v4
        with:
          fetch-depth: 0

      - name: Is this commit still the tip of main
        id: tip
        run: echo "current=$([ "$(git ls-remote origin refs/heads/main | cut -f1)" = "$GITHUB_SHA" ] && echo true || echo false)" >> "$GITHUB_OUTPUT"

      - name: Is this commit settled
        id: settled
        uses: actions/cache/restore@v4
        with:
          path: .r30/settled
          key: r30-settled-${{{{ github.sha }}}}
          lookup-only: true

      - name: Restore the pinned compiler
        if: {run_if}
        id: compiler
        uses: actions/cache/restore@v4
        with:
          path: .local
          key: r30-lexlean-${{{{ runner.os }}}}-${{{{ hashFiles('.github/lexlean-revision') }}}}

      - name: Set up proof toolchain
        if: {run_if}
        uses: ./.github/actions/setup-proof-tools

      - name: Save the pinned compiler
        if: {run_if} && steps.compiler.outputs.cache-hit != 'true'
        uses: actions/cache/save@v4
        with:
          path: .local
          key: r30-lexlean-${{{{ runner.os }}}}-${{{{ hashFiles('.github/lexlean-revision') }}}}

      - name: Restore the certified bundle
        if: {run_if}
        id: bundle
        uses: actions/cache/restore@v4
        with:
          path: {BUNDLE_DIR}
          key: r30-bundle-${{{{ runner.os }}}}-{bundle}

      - name: Build the certified bundle
        if: {run_if} && steps.bundle.outputs.cache-hit != 'true'
        run: bin/r30 api production

      - name: Save the certified bundle
        if: {run_if} && steps.bundle.outputs.cache-hit != 'true'
        uses: actions/cache/save@v4
        with:
          path: {BUNDLE_DIR}
          key: r30-bundle-${{{{ runner.os }}}}-{bundle}

      - name: Restore the Lake builds
        if: {run_if}
        uses: actions/cache/restore@v4
        with:
          path: |
{lake}
          key: r30-lake-${{{{ runner.os }}}}-{toolchain}-${{{{ github.sha }}}}
          restore-keys: |
            r30-lake-${{{{ runner.os }}}}-{toolchain}-

      - name: Restore the gate's evidence
        if: {run_if}
        uses: actions/cache/restore@v4
        with:
          path: .git/rule30-validation
          key: r30-gate-${{{{ runner.os }}}}-${{{{ github.sha }}}}
          restore-keys: |
            r30-gate-${{{{ runner.os }}}}-

      - name: Engine identity and hooks
        if: {run_if}
        run: |
          git config user.name "{name}"
          git config user.email "{email}"
          make hooks

      - name: Tick
        if: {run_if}
        id: tick
        run: bin/r30 engine tick --budget-minutes {wl['tickBudget']} --commit --push

      - name: Tick summary
        if: always() && {run_if}
        run: |
          {{ echo "outcome: ${{{{ steps.tick.outputs.outcome }}}}"; echo '```'; bin/r30 engine status || true; echo '```'; }} >> "$GITHUB_STEP_SUMMARY"
          for f in .r30/commit-*.log; do if [ -f "$f" ]; then echo "::group::gate log $f"; tail -n 200 "$f"; echo "::endgroup::"; fi; done

      - name: Prune the gate's evidence before caching
        if: {save_if}
        run: bin/r30 engine prune --apply

      - name: Save the Lake builds
        if: {save_if}
        uses: actions/cache/save@v4
        with:
          path: |
{lake}
          key: r30-lake-${{{{ runner.os }}}}-{toolchain}-${{{{ github.sha }}}}-${{{{ github.run_id }}}}

      - name: Save the gate's evidence
        if: {save_if}
        uses: actions/cache/save@v4
        with:
          path: .git/rule30-validation
          key: r30-gate-${{{{ runner.os }}}}-${{{{ github.sha }}}}-${{{{ github.run_id }}}}

      - name: Mark the commit settled
        if: always() && {run_if} && contains(fromJSON('["idle", "refused", "error", "stalled"]'), steps.tick.outputs.outcome)
        uses: actions/cache/save@v4
        with:
          path: .r30/settled
          key: r30-settled-${{{{ github.sha }}}}

      - name: Keep the newest entry of each cache family
        if: always() && {run_if}
        env:
          GH_TOKEN: ${{{{ github.token }}}}
        run: |
          for family in r30-bundle r30-lake r30-gate r30-settled; do
            gh cache list --key "$family-" --sort created_at --order desc --limit 100 --json id --jq '.[1:][].id' \\
              | xargs -r -n1 gh cache delete || true
          done

      - name: Publish the view of the pushed commit
        if: {run_if} && steps.tick.outputs.pushed == 'true'
        env:
          GH_TOKEN: ${{{{ github.token }}}}
        run: gh workflow run view.yml --ref main
"""


def workflow_problems(text):
    """What the workflow must never contain, read from the text (the kernel decides the data)."""
    import re
    out = []
    secrets = set(re.findall(r"secrets\.([A-Za-z_]+)", text))
    if secrets - {"GITHUB_TOKEN"}:
        out.append("a secret other than GITHUB_TOKEN: " + ", ".join(sorted(secrets)))
    uses = set(re.findall(r"uses:\s*(\S+)", text))
    if not uses <= set(WORKLOAD["allowedActions"]):
        out.append("an action beyond those already used: " + ", ".join(sorted(uses - set(WORKLOAD["allowedActions"]))))
    if re.search(r"pull_request", text):
        out.append("a pull_request trigger")
    return out


# ------------------------------------------------------------ sync / check

def files():
    return {MODULE: render(), WORKFLOW: render_workflow()}


def sync():
    changed = False
    for path, text in files().items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
            changed = True
    return {"module": str(MODULE.relative_to(repo.ROOT)), "theorems": len(THEOREMS), "changed": changed}


def check():
    for path, text in files().items():
        if not path.exists() or path.read_text() != text:
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} drifted from enginemodel.py, the templates "
                                           "or model/engine.toml; run `bin/r30 api sync`"}
    bad = workflow_problems(WORKFLOW.read_text())
    if bad:
        return {"ok": False, "reason": "engine.yml: " + "; ".join(bad)}
    return {"ok": True, "reason": None}
