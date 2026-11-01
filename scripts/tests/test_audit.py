"""Tests for the audit of the conditional refutations (`bin/r30 audit`,
`tools/r30/auditmodel.py`) and for the induce phase of the saved round
workflow (`.claude/workflows/rule30-round.js`). They need no Lean build: the
introspection is replaced by recorded statements in the form Lean prints them
(`R30AUDIT`, `R30DISCHARGE`, `R30COMPOSE` lines). Each PrismPM id of
`prismmodel.API_IDS` here has a test whose name ends in the id."""

from pathlib import Path
import io
import json
import contextlib
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.r30 import auditmodel, schema  # noqa: E402

NAT = "(const Nat)"


def lit(n):
    return f"(app (const OfNat.ofNat) {NAT} (nat {n}) (app (const instOfNatNat) (nat {n})))"


def loc(x):
    return f"(local {x})"


def add(a, b):
    return f"(app (const HAdd.hAdd) {NAT} {NAT} {NAT} (app (const instHAdd) {NAT} (const instAddNat)) {a} {b})"


def lt(a, b):
    return f"(app (const LT.lt) {NAT} (const instLTNat) {a} {b})"


def le(a, b):
    return f"(app (const LE.le) {NAT} (const instLENat) {a} {b})"


def per(t, p):
    return f"(app (const Rule30UOR.Scale.CenterPeriodic) {t} {p})"


def neg(x):
    return f"(app (const Not) {x})"


def eq_bool(a, b):
    return f"(app (const Eq) (const Bool) {a} {b})"


def rh(x):
    return f"(app (const Rule30UOR.Interfaces.rhCenter) {x})"


def data(name):
    return f"(data explicit {name} {NAT})"


def prop(name, ty):
    return f"(prop explicit {name} {ty})"


def theorem(name, binders, conclusion):
    return f"R30AUDIT (theorem {name} (binders {' '.join(binders)}) {conclusion})"


T, P = loc("T"), loc("P")
POS = prop("hP", lt(lit(0), P))
LH = "Rule30UOR.Interfaces.LhColAgree"
EIGHT = "Rule30UOR.LeftBand.EightAperiodic"
PROBLEM1 = "(const Ruliology.CellularAutomata.Rule30Prize.Problem1)"

# What `#r30audit` prints for a small library: four conditional refutations (a
# negated period, a negated period with a ∀-hypothesis, Problem1 from a named
# predicate, False under the period), a refutation under a period, a discharge
# under a period, an unconditional discharge (conclusion only) and an unrelated theorem.
INTROSPECTION = "\n".join([
    theorem("X.c_dead", [data("T"), data("P"), data("z"), POS,
                         prop("hz", f"(app (const Rule30UOR.ZeroDiagonals.IsZeroDiag) {loc('z')})"),
                         prop("hlh", f"(app (const {LH}) {loc('z')} {P} {lit(1)} {loc('z')})")], neg(per(T, P))),
    theorem("X.r_lh", [data("T"), data("P"), data("t"), POS, prop("hper", per(T, P))],
            neg(f"(app (const {LH}) {loc('t')} {P} {lit(1)} {loc('t')})")),
    theorem("X.c_open", [data("T"), data("P"), data("k"), data("z"), POS,
                         prop("hd", f"(app (const Rule30UOR.CompilePoints.DoublesAt) {loc('k')} {loc('z')})"),
                         prop("hpref", f"(pi explicit i {NAT} (pi explicit a {lt(loc('i'), loc('k'))} "
                                       f"{eq_bool(rh(loc('i')), rh(add(loc('i'), P)))}))")], neg(per(T, P))),
    theorem("X.d_rh", [data("T"), data("P"), data("i"), prop("hper", per(T, P))], eq_bool(rh(loc("i")), rh(add(loc("i"), P)))),
    theorem("X.p1", [prop("h", f"(const {EIGHT})")], PROBLEM1),
    "R30AUDIT (conclusion X.d_eight (const Rule30UOR.LeftBand.EightAperiodic))",
    theorem("X.c_false", [data("T"), data("P"), prop("hper", per(T, P)), prop("hS", le(add(P, lit(1)), T)),
                          prop("hset", le(f"(app (const Rule30UOR.Intent.settle) {T})", add(T, P)))], "(const False)"),
    "R30AUDIT (conclusion X.other " + eq_bool(f"(app (const Rule30UOR.Scale.center) {lit(0)})", "(const Bool.true)") + ")",
]) + "\n"


class AuditTests(unittest.TestCase):
    """The audit reads the statements exactly as Lean prints them, classifies
    every conditional refutation, records the result in model/audit.toml and
    Audit.lex.tex, and refuses data the module would not decide."""

    def classified(self):
        full, conclusions = auditmodel.parse(INTROSPECTION)
        return auditmodel.classify(full, conclusions)

    def test_classification_of_recorded_statements_conditional_audit(self):
        entries, keys = self.classified()
        by = {e["theorem"]: e for e in entries}
        self.assertEqual(sorted(by), ["X.c_dead", "X.c_false", "X.c_open", "X.p1"])
        self.assertEqual({k: by[k]["kind"] for k in by},
                         {"X.c_dead": "periodic", "X.c_false": "periodic", "X.c_open": "periodic", "X.p1": "problem1"})
        # the period and the arithmetic side conditions are not hypotheses; the rest are identified by their heads
        self.assertEqual([h["key"] for h in by["X.c_dead"]["hypotheses"]], ["Rule30UOR.ZeroDiagonals.IsZeroDiag", LH])
        self.assertEqual([h["label"] for h in by["X.c_open"]["hypotheses"]],
                         ["Rule30UOR.CompilePoints.DoublesAt", "forall Eq[Rule30UOR.Interfaces.rhCenter]"])
        self.assertEqual([h["key"] for h in by["X.c_false"]["hypotheses"]], ["LE.le[Rule30UOR.Intent.settle]"])
        self.assertEqual(keys[LH]["refutedBy"], ["X.r_lh"])
        self.assertEqual(keys["Eq[Rule30UOR.Interfaces.rhCenter]"]["dischargedUnderPeriod"], ["X.d_rh"])
        self.assertEqual(keys[EIGHT]["dischargedWithoutPeriod"], ["X.d_eight"])
        self.assertEqual(by["X.c_dead"]["status"], "dead")
        self.assertEqual(by["X.c_dead"]["refutedBy"], ["X.r_lh"])
        self.assertEqual(by["X.p1"]["status"], "candidate")
        self.assertEqual(by["X.c_open"]["status"], "open")
        # Lean's commands receive the discharges by key at each binder position
        self.assertEqual(auditmodel.table(by["X.c_open"], keys), "6 X.d_rh")
        self.assertEqual(auditmodel.table(by["X.p1"], keys), "0 X.d_eight")
        # what Lean decided: the agreement is discharged at its instance; Problem1 composed
        found = {("X.c_open", 6): "X.d_rh", ("X.c_false", 4): None}
        results = {"X.p1": {"composed": True, "axioms": ["propext"], "proof": "X.p1 X.d_eight"}}
        auditmodel.settle(entries, found, results)
        self.assertEqual(by["X.c_open"]["open"], ["Rule30UOR.CompilePoints.DoublesAt"])
        self.assertEqual(by["X.c_open"]["dischargedBy"], ["X.d_rh"])
        self.assertEqual(by["X.c_open"]["hypotheses"][1]["status"], "discharged")
        self.assertEqual(by["X.p1"]["status"], "live-discharged")
        self.assertIn("X.p1 X.d_eight", by["X.p1"]["composition"])
        self.assertEqual(by["X.c_false"]["open"], ["LE.le[Rule30UOR.Intent.settle]"])
        claims = [{"id": "route-x", "status": "refuted", "statement": "s", "lean": "X.r_lh"}]
        rep = auditmodel.report(entries, keys, claims)
        self.assertEqual(rep["counts"], {"dead": 1, "live-discharged": 1, "open": 2})
        self.assertEqual(rep["live"], ["X.p1"])
        self.assertEqual(by["X.c_dead"]["recordedBy"], ["route-x"])
        self.assertEqual(rep["unrecorded_dead"], [])
        self.assertEqual(auditmodel.report(entries, keys, [])["unrecorded_dead"], ["X.c_dead"])
        schema.validate(auditmodel.RESULT_SCHEMA, json.loads(json.dumps(rep)))
        # the record round-trips, and the module states what the kernel decides
        rows, keys2 = auditmodel._read(auditmodel.register_toml(rep))
        self.assertEqual(keys2, keys)
        self.assertEqual([r["theorem"] for r in rows], sorted(by))
        self.assertEqual(auditmodel.problems(rows), [])
        module = auditmodel.render(rows, keys2)
        for name in ("everyDeadNamesARefutation", "statusesDeclared", "theoremNamesDistinct"):
            self.assertIn(f"name: {name},", module)
        self.assertIn("statement: ((deadCount (conditionals)) = 1)", module)
        self.assertIn("statement: ((liveCount (conditionals)) = 1)", module)
        self.assertIn("statement: ((openCount (conditionals)) = 2)", module)
        # a dead entry without a refutation, an undeclared status, a repeated name are refused
        bad = [dict(rows[0], refutedBy=[]), dict(rows[1], status="maybe"), dict(rows[2]), dict(rows[2])]
        problems = auditmodel.problems(bad)
        self.assertTrue(any("dead without a refuting theorem" in p for p in problems))
        self.assertTrue(any("status maybe" in p for p in problems))
        self.assertIn("theorem names are not distinct", problems)
        # a claim concerns an entry through its Lean name, a hypothesis key, or by naming it
        self.assertEqual([r["theorem"] for r in auditmodel.related({"lean": EIGHT}, rows)], ["X.p1"])
        self.assertEqual([r["theorem"] for r in auditmodel.related({"note": "fires c_open"}, rows)], ["X.c_open"])

    def test_run_reads_lean_and_decides_in_lean(self):
        """`run` asks Lean twice (the introspection, then the discharges and
        compositions in one file) and believes only what Lean printed."""
        from tools.r30 import leansig
        sent = []

        def fake(commands, package_dir=None, modules=None, timeout=1800):
            sent.append(commands)
            if "#r30audit Rule30UOR :" in commands:
                return INTROSPECTION, []
            return ("R30DISCHARGE X.c_open 6 X.d_rh\nR30DISCHARGE X.c_false 4 -\n"
                    "R30COMPOSE failed X.p1 goals remain\n"), []
        old = leansig._run
        leansig._run = fake
        self.addCleanup(lambda: setattr(leansig, "_run", old))
        rep = auditmodel.run(modules=["Rule30UOR.Core"])
        self.assertIn(" ".join(auditmodel.TARGETS), sent[0])
        self.assertIn('#r30discharge periodic X.c_open "6 X.d_rh" "5 6"', sent[1])
        self.assertIn('#r30compose problem1 X.p1 "0 X.d_eight"', sent[1])
        self.assertNotIn("X.c_dead", sent[1])  # a dead entry is not decided further
        self.assertEqual(rep["counts"], {"dead": 1, "live-discharged": 0, "open": 3})
        p1 = next(e for e in rep["conditionals"] if e["theorem"] == "X.p1")
        self.assertEqual(p1["composition"], "failed: goals remain")
        self.assertEqual(p1["open"], [EIGHT])
        schema.validate(auditmodel.RESULT_SCHEMA, json.loads(json.dumps(rep)))

    def test_lean_side_declares_the_three_commands(self):
        text = auditmodel.TEMPLATE.read_text()
        for command in ('elab "#r30audit "', 'elab "#r30discharge "', 'elab "#r30compose "'):
            self.assertIn(command, text)
        for marker in ("R30AUDIT (theorem", "R30AUDIT (conclusion", "R30DISCHARGE", "R30COMPOSE composed", "R30COMPOSE failed"):
            self.assertIn(marker, text)
        self.assertIn("addDecl", text)  # a composition is checked by the kernel before it is reported
        self.assertNotIn("sorry", text.replace("hasSorry", "").replace("sorryAx", ""))

    def test_committed_record_module_and_schema_agree(self):
        """The recorded audit (model/audit.toml) satisfies what Audit.lex.tex
        decides, the module is its rendering, and the cached report fits the schema."""
        self.assertEqual(json.loads(auditmodel.SCHEMA_FILE.read_text()), auditmodel.RESULT_SCHEMA)
        record = auditmodel.load()
        if record is None:
            self.skipTest("no audit recorded")
        rows, keys = record
        self.assertEqual(auditmodel.problems(rows), [])
        self.assertEqual(auditmodel.MODULE.read_text(), auditmodel.render(rows, keys))
        self.assertTrue(all(h["key"] in keys for r in rows for h in r["hypotheses"]))
        out = io.StringIO()
        from tools.r30 import cli
        with contextlib.redirect_stdout(out):
            cli.main(["--json", "audit", "--cached", "--status", "open"])
        rep = json.loads(out.getvalue())
        schema.validate(auditmodel.RESULT_SCHEMA, rep)
        self.assertTrue(all(e["status"] == "open" for e in rep["conditionals"]))
        self.assertEqual(sum(rep["counts"].values()), len(rows))

    def test_claim_related_lists_the_audit_obligations(self):
        record = auditmodel.load()
        if record is None:
            self.skipTest("no audit recorded")
        from tools.r30 import cli, leansig, prismmodel
        old = leansig.signatures, leansig.mentions
        leansig.signatures = lambda names, **kw: {n: {"kind": "theorem", "type": ["const", "Prop"]} for n in names}
        leansig.mentions = lambda names, prefixes=("Rule30UOR",), **kw: []
        self.addCleanup(lambda: (setattr(leansig, "signatures", old[0]), setattr(leansig, "mentions", old[1])))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            cli.main(["--json", "claim", "single-row-agreement", "--related"])
        data = json.loads(out.getvalue())
        doc = json.loads((prismmodel.SCHEMAS / "claim-result.schema.json").read_text())
        schema.validate(doc, data)
        names = [a["theorem"] for a in data["audit"]]
        self.assertIn("Rule30UOR.Interfaces.not_centerPeriodic_of_two_scale_single_rh_row_prefix_and_tail_settleBound", names)


class RoundWorkflowTests(unittest.TestCase):
    """The saved round workflow opens with the Induce phase: discover and audit
    first, their results to every lens and straight to Refute and Mechanize."""

    WORKFLOW = ROOT / ".claude" / "workflows" / "rule30-round.js"

    def meta(self, text):
        m = re.search(r"^export const meta = (\{.*?\n\})\n", text, re.S | re.M)
        self.assertIsNotNone(m)
        return m.group(1)

    def test_the_round_opens_with_the_induce_phase_induce_phase(self):
        text = self.WORKFLOW.read_text()
        meta = self.meta(text)
        self.assertNotIn("${", meta)  # a pure literal: no interpolation
        self.assertNotIn("...", meta)
        titles = re.findall(r"\{ title: '([^']+)'", meta)
        self.assertEqual(titles, ["Induce", "Propose", "Refute", "Mechanize"])
        for arg in ("round", "lenses", "extra", "induce"):
            self.assertIn(arg, meta)  # the args are documented where the workflow list shows them
        self.assertLess(text.index("phase('Induce')"), text.index("phase('Propose')"))
        self.assertIn("bin/r30 discover --window 256 --degree 2 --json", text)
        self.assertIn("bin/r30 audit --json", text)
        self.assertIn("invalid choice", text)  # a missing command is reported, not substituted
        from tools.r30.presentationmodel import ARTIFACTS
        published = next(a for a in ARTIFACTS if a["id"] == "round-workflow")
        self.assertEqual(published["source"], ".claude/workflows/rule30-round.js")
        self.assertEqual(published["command"], "view_render")
        if shutil.which("node"):
            self.dry_run(text)

    def dry_run(self, text):
        """Run the script under node with recording stubs for the workflow hooks."""
        stub = r'''
const calls = []
const phase = t => calls.push({ phase: t })
const log = m => {}
async function agent(prompt, opts) {
  calls.push({ label: opts.label, phase: opts.phase, prompt })
  if (opts.label === 'induce') return { discover_available: false, audit_available: true,
    relations: [{ title: 'r', lean_statement: 'theorem r : forall t, f t = g t', certificate: 'window 256' }],
    obligations: [{ theorem: 'A', open_hypotheses: ['x', 'y'] }, { theorem: 'B', open_hypotheses: ['y', 'x'] }], notes: 'discover absent' }
  if (opts.phase === 'Propose') return { title: 't', lean_statement: 'l', proof_sketch: 'p', routes_to_problem1: 'r', what_fails: 'w', confidence: 0.9, closes_problem1: false }
  if (opts.phase === 'Refute') return { refuted: false, reason: 'ok', counterexample_or_gap: '', salvage: '' }
  return { module: 'M', proved: [], not_proved: '', report: '' }
}
async function parallel(thunks) { const out = []; for (const t of thunks) out.push(await t()); return out }
async function pipeline(items, ...stages) {
  return Promise.all(items.map(async (it, i) => { let v = it
    for (const s of stages) v = await s(v, it, i); return v }))
}
'''
        body = text.replace("export const meta = ", "const meta = ", 1)
        script = stub + "const result = await (async (args) => {\n" + body + "\n})(" + \
            json.dumps({"round": "t", "lenses": [{"key": "a", "prompt": "p"}]}) + \
            ")\nconsole.log(JSON.stringify({ result, calls }))\n"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "round.mjs"
            path.write_text(script)
            proc = subprocess.run(["node", str(path)], capture_output=True, text=True, timeout=60)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        out = json.loads(proc.stdout)
        labels = [c.get("label") for c in out["calls"] if c.get("label")]
        self.assertEqual(labels[0], "induce")
        lens = next(c for c in out["calls"] if c.get("label") == "propose:a")
        self.assertIn("INDUCED THIS ROUND", lens["prompt"])  # every lens sees the induced context
        self.assertIn("refute:induced-relation-1:truth-and-provability", labels)
        self.assertIn("refute:induced-obligation-1:routing-and-rules", labels)
        self.assertNotIn("refute:induced-obligation-2:routing-and-rules", labels)  # one proposal per hypothesis set
        self.assertIn("mechanize:induced-relation-1", labels)
        mech = next(c for c in out["calls"] if c.get("label") == "mechanize:induced-relation-1")
        self.assertIn("OBSERVED RELATION", mech["prompt"])
        self.assertEqual(out["result"]["induced"]["obligation_sets"], 1)
        self.assertFalse(out["result"]["induced"]["discover_available"])


if __name__ == "__main__":
    unittest.main()
