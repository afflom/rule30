"""Tests for the `r30` tooling that need no Lean build: s-expressions, the
Lean-to-LexLean converter on recorded signatures, the frontier register and the
MCP argument mapping."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.r30 import sexpr, frontier, repo  # noqa: E402
from tools.r30.convert import Converter, Unsupported, variables  # noqa: E402
from tools.r30.lexicon import Lexicon  # noqa: E402
from tools.r30.mcp_server import argv_for, tool_list  # noqa: E402

NAT = "(const Nat)"
BOOL = "(const Bool)"


def nat_lit(n):
    return f"(app (const OfNat.ofNat) {NAT} (nat {n}) (app (const instOfNatNat) (nat {n})))"


def add(a, b):
    return f"(app (const HAdd.hAdd) {NAT} {NAT} {NAT} (app (const instHAdd) {NAT} (const instAddNat)) {a} {b})"


# `center_defect_coupling` as Lean prints it (recorded from `r30 sig`).
COUPLING = (
    f"(pi explicit Q {NAT} (pi explicit t {NAT} (pi explicit h0 "
    f"(app (const Eq) {BOOL} (app (const Rule30UOR.Collision.leftDefect) (local Q) (local t) {nat_lit(0)}) (const Bool.false)) "
    f"(app (const Eq) {BOOL} (app (const Rule30UOR.Collision.leftDefect) (local Q) {add('(local t)', nat_lit(1))} {nat_lit(0)}) "
    f"(app (const Rule30UOR.Core.bxor) (app (const Rule30UOR.Collision.leftDefect) (local Q) (local t) {nat_lit(1)}) "
    f"(app (const Rule30UOR.WittDefect.centerGate) (local Q) (local t)))))))"
)


class SexprTests(unittest.TestCase):
    def test_roundtrip(self):
        text = "(pi ((explicit Q (const lexlean.std.nat::nat))) (app (const f) (local Q) (nat 3)))"
        self.assertEqual(sexpr.dumps(sexpr.parse(text)), text)

    def test_rejects_trailing(self):
        with self.assertRaises(ValueError):
            sexpr.parse("(a) (b)")


class ConverterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lx = Lexicon()

    def convert(self, text, package="r30.observation"):
        conv = Converter(self.lx, package)
        term = conv.term(sexpr.parse(text))
        return conv, term

    def test_coupling_signature_statement_and_probe(self):
        conv, term = self.convert(COUPLING)
        self.assertEqual(
            sexpr.dumps(term.lse()),
            "(pi ((explicit Q (const lexlean.std.nat::nat)) (explicit t (const lexlean.std.nat::nat))) "
            "(pi ((explicit h0 (app (const lexlean.core::eq) (app (const r30.observation::left-defect) (local Q) (local t) (nat 0)) (const lexlean.std.bool::false)))) "
            "(app (const lexlean.core::eq) (app (const r30.observation::left-defect) (local Q) (app (const lexlean.std.nat::add) (local t) (nat 1)) (nat 0)) "
            "(app (const r30.local::bxor) (app (const r30.observation::left-defect) (local Q) (local t) (nat 1)) (app (const r30.observation::center-gate) (local Q) (local t))))))")
        self.assertEqual(
            conv.statement(term),
            "For every natural number \\(Q\\) and natural number \\(t\\), if \\(leftdefect(Q, t, 0) = false\\), "
            "then \\(leftdefect(Q, t + 1, 0) = bxor(leftdefect(Q, t, 1), centergate(Q, t))\\)")
        self.assertIn("Rule30UOR.Core.bxor", conv.lean_type(term))
        self.assertEqual(variables(term), ["Q", "t"])

    def test_bool_xor_is_refused_with_hint(self):
        text = f"(pi explicit b {BOOL} (app (const Eq) {BOOL} (app (const Bool.xor) (local b) (local b)) (const Bool.false)))"
        with self.assertRaisesRegex(Unsupported, "bxor"):
            self.convert(text)

    def test_implicit_binder_is_refused(self):
        with self.assertRaisesRegex(Unsupported, "implicit"):
            self.convert(f"(pi implicit n {NAT} (app (const Eq) {NAT} (local n) (local n)))")

    def test_binder_a_is_renamed_only_under_numeral_eq(self):
        plain = f"(pi explicit a {NAT} (app (const Eq) {NAT} (local a) (local a)))"
        conv, term = self.convert(plain)
        self.assertEqual(variables(term), ["a"])
        numeral = f"(pi explicit a {NAT} (app (const Eq) {NAT} (local a) {nat_lit(0)}))"
        conv, term = self.convert(numeral)
        self.assertEqual(variables(term), ["a0"])

    def test_double_negation_prose(self):
        text = (f"(pi explicit N {NAT} (app (const Not) (app (const Not) (app (const Exists) {NAT} "
                f"(lam t {NAT} (app (const LE.le) {NAT} (const instLENat) (local N) (local t)))))))")
        conv, term = self.convert(text)
        self.assertEqual(conv.statement(term),
                         "For every natural number \\(N\\), not not there exists a natural number \\(t\\) such that \\(N ≤ t\\)")

    def test_precedence_parentheses(self):
        text = (f"(pi explicit x {NAT} (app (const Eq) {NAT} "
                f"(app (const HMul.hMul) {NAT} {NAT} {NAT} (app (const instHMul) {NAT} (const instMulNat)) {nat_lit(2)} {add('(local x)', nat_lit(1))}) "
                f"{add(add('(local x)', '(local x)'), nat_lit(2))}))")
        conv, term = self.convert(text)
        self.assertEqual(conv.statement(term), "For every natural number \\(x\\), \\(2 * (x + 1) = x + x + 2\\)")


class FrontierTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.old = repo.FRONTIER
        repo.FRONTIER = Path(self.tmp.name) / "frontier.toml"
        self.addCleanup(lambda: setattr(repo, "FRONTIER", self.old))

    def test_add_update_roundtrip(self):
        frontier.add("c1", "a claim with \"quotes\"", lean="Foo.bar")
        frontier.update("c1", status="proved", note="done")
        claims = frontier.list_claims()
        self.assertEqual(claims[0]["status"], "proved")
        self.assertEqual(claims[0]["statement"], 'a claim with "quotes"')
        with self.assertRaises(ValueError):
            frontier.update("c1", status="bogus")
        self.assertEqual(frontier.summary()["counts"]["proved"], 1)


class FrontierCheckTests(unittest.TestCase):
    """`frontier check` against a fake kernel and lexicon."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.old = repo.FRONTIER
        repo.FRONTIER = Path(self.tmp.name) / "frontier.toml"
        self.addCleanup(lambda: setattr(repo, "FRONTIER", self.old))

    class FakeLean:
        def __init__(self, table):
            self.table = table

        def axioms(self, names):
            return {n: self.table.get(n) for n in names}

    class FakeLexicon:
        def __init__(self, published):
            self.published = published

        def get(self, qid):
            return qid in self.published.values() or None

        def for_lean(self, name, visible=None):
            qid = self.published.get(name)
            return type("E", (), {"qid": qid})() if qid else None

    def test_proved_needs_kernel_and_lexeme(self):
        frontier.add("ok", "fine", status="proved", lean="A.good")
        frontier.add("unpub", "no lexeme", status="proved", lean="A.hidden")
        frontier.add("choice", "uses choice", status="proved", lean="A.classical")
        frontier.add("noexp", "refuted by nothing", status="refuted")
        frontier.add("dep", "depends on ghost", status="open", depends=["ghost"])
        lean = self.FakeLean({"A.good": ["propext"], "A.hidden": ["propext"],
                              "A.classical": ["propext", "Classical.choice"]})
        lx = self.FakeLexicon({"A.good": "p::good"})
        problems = frontier.check(lx, lean)
        joined = "\n".join(problems)
        self.assertNotIn("ok:", joined)
        self.assertIn("unpub: proved but unpublished", joined)
        self.assertIn("Classical.choice", joined)
        self.assertIn("noexp: refuted without", joined)
        self.assertIn("dep: depends on unknown claim ghost", joined)


class FrontierRenderTests(unittest.TestCase):
    """The register renders to a LexLean module deterministically, from a fake
    kernel: the test must not depend on a built Lean library (the gate runs the
    tooling tests before the build, and a cached olean may predate a claim)."""

    IFF = ("(app (const Iff) (const Ruliology.CellularAutomata.Rule30Prize.Problem1) "
           "(const Rule30UOR.CentralCollision.NoRecurrentCentralCollision))")

    class FakeLean:
        def __init__(self, table):
            self.table = table

        def signatures(self, names):
            return {n: ({"kind": "theorem", "type": sexpr.parse(self.table[n])} if n in self.table else None)
                    for n in names}

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.old = repo.FRONTIER
        repo.FRONTIER = Path(self.tmp.name) / "frontier.toml"
        self.addCleanup(lambda: setattr(repo, "FRONTIER", self.old))
        frontier.add("rcc", "the collision reduction", status="proved",
                     lean="Rule30UOR.CentralCollision.problem1_iff_no_recurrent_central_collision")
        frontier.add("ghost", "no published theorem", status="refuted", lean="Rule30UOR.Nope.x")

    def test_render_restates_published_claims_and_reports_the_rest(self):
        lean = self.FakeLean({"Rule30UOR.CentralCollision.problem1_iff_no_recurrent_central_collision": self.IFF,
                              "Rule30UOR.Nope.x": self.IFF})
        text1, skipped = frontier.render(Lexicon(), lean)
        text2, _ = frontier.render(Lexicon(), lean)
        self.assertEqual(text1, text2)
        self.assertIn("\\begin{lexlean}{Frontier}", text1)
        self.assertIn("\\begin{theorem}{claim-rcc}", text1)
        self.assertIn("problemone ↔ norecurrentcentralcollision", text1)
        self.assertIn("\\lexeme{r30.frontier::problem-one-iff-no-recurrent-central-collision}", text1)
        self.assertEqual(skipped, ["ghost"])

    def test_render_refuses_when_lean_cannot_answer(self):
        with self.assertRaisesRegex(RuntimeError, "Lean does not know"):
            frontier.render(Lexicon(), self.FakeLean({}))


class ModuleRegisterTests(unittest.TestCase):
    """`module add` edits the Lake roots and the audit imports exactly as
    `check_research_coverage.py` expects, and is idempotent."""

    def setUp(self):
        from tools.r30 import modules
        self.modules = modules
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        core = Path(self.tmp.name)
        self.old = repo.CORE_LEAN
        repo.CORE_LEAN = core
        self.addCleanup(lambda: setattr(repo, "CORE_LEAN", self.old))
        self.lakefile = core / "lakefile.toml"
        self.lakefile.write_text('[[lean_lib]]\nname = "LexLeanRuntime"\nroots = ["LexLeanRuntime.Portable"]\n\n'
                                 '[[lean_lib]]\nname = "Rule30UOR"\nroots = ["Rule30UOR.Core", "Rule30UOR.Frontier"]\n')
        self.audit = core / "scripts/CheckResearchAxioms.lean"
        self.audit.parent.mkdir()
        self.audit.write_text("import Rule30UOR.Core\nimport Rule30UOR.Frontier\nimport Lean.Util.CollectAxioms\n\n"
                              "if (`Rule30UOR).isPrefixOf name then\n")
        (core / "Rule30UOR").mkdir()
        for m in ("Core", "Frontier"):
            (core / "Rule30UOR" / f"{m}.lean").write_text("module\n")

    def test_register_creates_root_audit_and_skeleton(self):
        sys.path.insert(0, str(ROOT / "scripts"))
        import check_research_coverage as coverage
        r = self.modules.register("Horizon", lakefile=self.lakefile, audit=self.audit)
        self.assertEqual(r["changed"], ["source", "lakefile", "audit"])
        self.assertIn("namespace Rule30UOR.Horizon", (Path(self.tmp.name) / "Rule30UOR/Horizon.lean").read_text())
        self.assertIn('"Rule30UOR.Frontier", "Rule30UOR.Horizon"]', self.lakefile.read_text())
        self.assertIn("import Rule30UOR.Horizon\nimport Lean.Util.CollectAxioms", self.audit.read_text())
        root = Path(self.tmp.name).parent
        with tempfile.TemporaryDirectory() as fake_root:
            (Path(fake_root) / "rule30-core-lean").symlink_to(Path(self.tmp.name))
            self.assertEqual(coverage.covered_modules(Path(fake_root)),
                             ["Rule30UOR.Core", "Rule30UOR.Frontier", "Rule30UOR.Horizon"])
        again = self.modules.register("Rule30UOR.Horizon", lakefile=self.lakefile, audit=self.audit)
        self.assertEqual(again["changed"], [])
        with self.assertRaises(ValueError):
            self.modules.register("Rule30UOR.bad-name", lakefile=self.lakefile, audit=self.audit)


class ConsolidateTests(unittest.TestCase):
    """One proof per statement: the planner keeps the proof the others lean on, adds imports only
    along the grain, and the rewrite never touches a declaration's own name."""
    A = ("module\npublic import Init\n@[expose] public section\nnamespace Rule30UOR.A\n\n"
         "/-- the proof -/\ntheorem t (n : Nat) : n + 0 = n := by\n  simp\n\n"
         "theorem t_prop (n : Nat) : n + 0 = n :=\n  t n\n\n"
         "theorem use (n : Nat) : n + 0 = n := t_prop n\n\nend Rule30UOR.A\n")
    B = ("module\npublic import Rule30UOR.A\n@[expose] public section\nnamespace Rule30UOR.B\n\n"
         "theorem t (m : Nat) : m + 0 = m := Rule30UOR.A.t m\n\n"
         "theorem w (m : Nat) : m + 0 = m := t m\n\nend Rule30UOR.B\n")

    def setUp(self):
        from tools.r30 import consolidate
        self.c = consolidate
        self.sources = {"Rule30UOR.A": self.A, "Rule30UOR.B": self.B}

    def test_span_takes_the_docstring_and_stops_at_the_next_item(self):
        a, b = self.c.declaration_span(self.A, "Rule30UOR.A.t")
        self.assertTrue(self.A[a:b].startswith("/-- the proof -/\ntheorem t "))
        self.assertTrue(self.A[b:].startswith("theorem t_prop"))
        self.assertIsNone(self.c.declaration_span(self.A, "Rule30UOR.A.absent"))
        self.assertIsNone(self.c.declaration_span(self.A, "Rule30UOR.B.t"))

    def test_the_wrapper_goes_and_the_proof_stays(self):
        groups = {"k1": [("Rule30UOR.A", "Rule30UOR.A.t"), ("Rule30UOR.A", "Rule30UOR.A.t_prop")]}
        plan = self.c.plan(groups, self.sources)
        self.assertEqual(plan["keep"][0]["canonical"], "Rule30UOR.A.t")
        self.assertEqual([r["name"] for r in plan["keep"][0]["removed"]], ["Rule30UOR.A.t_prop"])

    def test_the_upstream_module_keeps_the_proof_and_no_import_is_added(self):
        groups = {"k": [("Rule30UOR.A", "Rule30UOR.A.t"), ("Rule30UOR.B", "Rule30UOR.B.t")]}
        row = self.c.plan(groups, self.sources)["keep"][0]
        self.assertEqual((row["canonical"], row["imports"]), ("Rule30UOR.A.t", []))

    def test_rewrite_spares_declaration_names(self):
        p = self.c.name_pattern("Rule30UOR.B.t", True)
        text = self.c.without(self.B, self.c.declaration_span(self.B, "Rule30UOR.B.t"))
        out = p.sub("Rule30UOR.A.t", text)
        self.assertIn("theorem w (m : Nat) : m + 0 = m := Rule30UOR.A.t m", out)
        self.assertEqual(p.sub("X", "theorem t (m : Nat)"), "theorem t (m : Nat)")
        self.assertNotIn("\n\n\n", out)

    def test_bare_names_are_rewritten_only_where_visible(self):
        self.assertTrue(self.c.short_visible("Rule30UOR.B.t", self.B, "Rule30UOR.B", "Rule30UOR.B"))
        self.assertFalse(self.c.short_visible("Rule30UOR.B.t", self.A, "Rule30UOR.A", "Rule30UOR.B"))
        self.assertTrue(self.c.short_visible("Rule30UOR.B.t", "open B\n", "Rule30UOR.C", "Rule30UOR.B"))

    def test_opens_read_continuation_lines(self):
        text = "open Rule30UOR.Core\nopen Rule30UOR.Ledger\n  Rule30UOR.DyadicRow Rule30UOR.Band\n\ntheorem x : True := trivial\n"
        self.assertIn("Rule30UOR.DyadicRow", self.c.opens(text))
        self.assertTrue(self.c.short_visible("Rule30UOR.DyadicRow.f", text, "Rule30UOR.K", "Rule30UOR.DyadicRow"))
        self.assertNotIn("theorem", self.c.opens(text))

    def test_private_theorems_keep_their_source_name_and_scope(self):
        full = "_private.Rule30UOR.A.0.Rule30UOR.A.helper"
        self.assertEqual(self.c.source_name(full), "Rule30UOR.A.helper")
        text = "namespace Rule30UOR.A\n\nprivate theorem helper : True := trivial\n\ntheorem u : True := helper\n"
        self.assertIsNotNone(self.c.declaration_span(text, full))
        self.assertEqual(self.c.users_of(full, "Rule30UOR.A", {"Rule30UOR.A": text, "Rule30UOR.B": "helper"}),
                         {"Rule30UOR.A"})

    def test_a_shadowed_or_scoped_open_is_not_visible(self):
        self.assertFalse(self.c.short_visible("Rule30UOR.B.t", "open Rule30UOR.B in\ntheorem x := t\n", "M", "Rule30UOR.B"))
        self.assertTrue(self.c.short_visible("Rule30UOR.B.t", "open Rule30UOR.B (t)\n", "M", "Rule30UOR.B"))
        self.assertFalse(self.c.short_visible("Rule30UOR.B.t", "open Rule30UOR.B (w)\n", "M", "Rule30UOR.B"))
        self.assertFalse(self.c.short_visible("Rule30UOR.B.t", "open Rule30UOR.B hiding t\n", "M", "Rule30UOR.B"))
        shadow = "open Rule30UOR.B\nnamespace Rule30UOR.C\ntheorem t : True := trivial\nend Rule30UOR.C\n"
        self.assertFalse(self.c.short_visible("Rule30UOR.B.t", shadow, "Rule30UOR.C", "Rule30UOR.B"))

    def test_a_canonical_declared_after_a_reference_it_takes_is_not_chosen(self):
        text = ("namespace Rule30UOR.A\n\ntheorem late_user : 0 + 0 = 0 := early_copy\n\n"
                "theorem early_copy : 0 + 0 = 0 := rfl\n\ntheorem later : 0 + 0 = 0 := rfl\n\nend Rule30UOR.A\n")
        groups = {"k": [("Rule30UOR.A", "Rule30UOR.A.early_copy"), ("Rule30UOR.A", "Rule30UOR.A.later")]}
        plan = self.c.plan(groups, {"Rule30UOR.A": text})
        self.assertEqual(plan["keep"][0]["canonical"], "Rule30UOR.A.early_copy")

    def test_add_import_is_idempotent(self):
        once = self.c.add_import(self.B, "Rule30UOR.Z")
        self.assertEqual(self.c.add_import(once, "Rule30UOR.Z"), once)

    def test_add_import_follows_the_last_import(self):
        self.assertIn("public import Rule30UOR.A\npublic import Rule30UOR.Z\n",
                      self.c.add_import(self.B, "Rule30UOR.Z"))


class ApiModelTests(unittest.TestCase):
    """The command surface is a LexLean semantic module generated from the CLI
    parser; the committed module must match the parser (the gate verifies the
    module with lexlean, so the API's description carries kernel evidence)."""

    def test_render_is_a_semantic_module_with_a_count_theorem(self):
        from tools.r30 import apimodel
        rows = apimodel.surface()
        text = apimodel.render(rows)
        self.assertIn("\\begin{semanticmodule}", text)
        self.assertIn("structure{\n  name: Command", text)
        self.assertIn(f"statement: ((commandCount) = {len(rows)})", text)
        self.assertTrue(any(r["name"] == "api_sync" for r in rows))

    def test_committed_module_matches_the_cli(self):
        from tools.r30 import apimodel
        r = apimodel.check()
        self.assertTrue(r["ok"], r["reason"])

    def test_architecture_module_is_current_and_closes_its_concerns(self):
        """The data the kernel decides over is also checked here, so a test
        failure names the entry before `lexlean verify` reports a false `decide`."""
        from tools.r30 import archmodel, apimodel
        r = archmodel.check()
        self.assertTrue(r["ok"], r["reason"])
        concern_ids = {c["id"] for c in archmodel.CONCERNS}
        held = {s["id"]: set(s["concerns"]) for s in archmodel.STAKEHOLDERS}
        for s in archmodel.STAKEHOLDERS:
            self.assertTrue(held[s["id"]] <= concern_ids, s["id"])
        for vp in archmodel.VIEWPOINTS:
            self.assertIn(vp["concern"], held[vp["stakeholder"]], vp["id"])
            self.assertIn(vp["model_kind"], archmodel.MODEL_KINDS)
        self.assertEqual(concern_ids, {vp["concern"] for vp in archmodel.VIEWPOINTS})
        self.assertEqual({vp["id"] for vp in archmodel.VIEWPOINTS}, {v["viewpoint"] for v in archmodel.VIEWS})
        commands = {row["name"] for row in apimodel.surface()}
        for v in archmodel.VIEWS:
            self.assertIn(v["command"], commands, v["id"])
        for m in archmodel.MEASURES:
            self.assertIn(m["command"], commands, m["id"])
            self.assertIn(m["requirement"], {q["id"] for q in archmodel.REQUIREMENTS})
        self.assertEqual({q["id"] for q in archmodel.REQUIREMENTS}, {m["requirement"] for m in archmodel.MEASURES})
        text = archmodel.render()
        self.assertIn("\\importmodule{Foundation.Arch}", text)
        self.assertIn("{name: entity, type: Foundation.Arch::Stakeholder}", text)
        self.assertIn("(record Foundation.Qual::QualityMeasure {index := 0, requirementIndex := 0, threshold := 60})", text)
        for name in ("everyConcernFramed", "viewpointStakeholdersIndexed", "everyMeasureCommandExists", "optimalViewpointIsQualityModel"):
            self.assertIn(f"name: {name}", text)

    def test_presentation_and_application_modules_are_current_and_consistent(self):
        from tools.r30 import presentationmodel as pm, archmodel, apimodel
        r = pm.check()
        self.assertTrue(r["ok"], r["reason"])
        viewpoints = {vp["id"] for vp in archmodel.VIEWPOINTS}
        artifacts = {a["id"] for a in pm.ARTIFACTS}
        panels = {p["id"] for p in pm.PANELS}
        commands = {row["name"] for row in apimodel.surface()}
        for p in pm.PANELS:
            self.assertIn(p["viewpoint"], viewpoints, p["id"])
            self.assertIn(p["artifact"], artifacts, p["id"])
        for j in pm.JOURNEYS:
            self.assertIn(j["stakeholder"], {s["id"] for s in archmodel.STAKEHOLDERS}, j["id"])
            self.assertTrue(set(j["panels"]) <= panels, j["id"])
        self.assertEqual(panels, {p for j in pm.JOURNEYS for p in j["panels"]})
        for a in pm.ARTIFACTS:
            self.assertIn(a["command"], commands, a["id"])
            if a["source"]:
                self.assertTrue((repo.ROOT / a["source"]).exists(), a["source"])
        self.assertEqual(len({a["path"] for a in pm.ARTIFACTS}), len(pm.ARTIFACTS))
        self.assertIn(pm.APPLICATION_RECORD["entry"], {a["path"] for a in pm.ARTIFACTS})
        self.assertIn(pm.PUBLICATION["command"], commands)
        self.assertLessEqual(pm.PUBLICATION["timeoutMinutes"],
                             next(m["threshold"] for m in archmodel.MEASURES if m["id"] == "ci-render-time"))
        text = pm.render_application()
        self.assertIn("\\importmodule{Presentation}", text)
        self.assertIn("name: publicationWithinBudget", text)
        self.assertIn('(Architecture::measureThreshold "ci-render-time" (Architecture::measures))', text)
        self.assertEqual({m["status"] for m in pm.STATUS_MARKS}, set(frontier.STATUSES))

    def test_observer_module_is_current_and_its_quadruples_are_the_journeys(self):
        """The data the kernel decides over, checked here first so a failure
        names the row before `lexlean verify` reports a false `decide`."""
        from tools.r30 import observermodel as om, presentationmodel as pm, archmodel
        r = om.check()
        self.assertTrue(r["ok"], r["reason"])
        d = om.data()
        self.assertEqual(om.problems(d), [])
        claims = {c["id"]: c for c in d["claims"]}
        proved = {i for i, c in claims.items() if c["status"] == "proved"}
        opened = {i for i, c in claims.items() if c["status"] == "open"}
        panels = {p["id"] for p in pm.PANELS}
        self.assertEqual([q["sensualObject"] for q in d["quadruples"]], [j["id"] for j in pm.JOURNEYS])
        for q, j in zip(d["quadruples"], pm.JOURNEYS):
            self.assertEqual(q["object"], archmodel.CONCEPTUAL_MODEL["id"])
            self.assertEqual(q["realObject"], om.REAL_OBJECT)
            self.assertEqual(q["sensualQualities"], j["panels"])
            self.assertTrue(set(q["realQualities"]) <= proved, q["sensualObject"])
            self.assertTrue(q["realQualities"], q["sensualObject"])
            self.assertEqual(set(q["withdrawn"]), opened)
            self.assertIn(om.WITHDRAWN_CORE, q["withdrawn"])
            self.assertTrue(set(q["sensualQualities"]) <= panels)
        # withdrawal: no overlap is a withdrawn claim; the overlaps are the real qualities
        self.assertEqual({(o["vantage"], o["claim"]) for o in d["overlaps"]},
                         {(q["sensualObject"], c) for q in d["quadruples"] for c in q["realQualities"]})
        self.assertFalse({o["claim"] for o in d["overlaps"]} & opened)
        # interactions: symmetric, through shared panels
        by_vantage = {q["sensualObject"]: set(q["sensualQualities"]) for q in d["quadruples"]}
        pairs = {(i["source"], i["target"], frozenset(i["viaPanels"])) for i in d["interactions"]}
        for source, target, via in pairs:
            self.assertIn((target, source, via), pairs)
            self.assertTrue(via <= by_vantage[source] & by_vantage[target])
            self.assertTrue(via)
        # the facets of the proof
        pole_of = {f["facet"]: f["pole"] for f in d["facets"]}
        self.assertEqual({f["pole"] for f in d["facets"]} - set(om.POLES), set())
        self.assertEqual({f["vantage"] for f in d["facets"]} - set(om.VANTAGES), set())
        for f in om.REGULAR_SIDE:
            self.assertEqual(pole_of[f["facet"]], "sensual-quality")
            self.assertIn(f["facet"], proved)
        self.assertEqual(pole_of[om.WITHDRAWN_CORE], "withdrawn")
        self.assertEqual({f["facet"] for f in d["facets"] if f["pole"] == "real-quality"},
                         {i for i in proved if claims[i].get("depends", []) == [om.REAL_OBJECT]})
        text = om.render(d)
        for name in ("withdrawal", "everyVantageSeesTheObject", "interactionsAreSymmetric", "vantagesAreJourneys",
                     "objectIsTheProblem", "realQualitiesAreProved", "withdrawnAreOpen", "gaugeKeepsRealQualities",
                     "gaugeTransformsSensualQualities"):
            self.assertIn(f"name: {name},", text)
        self.assertIn("\\importmodule{Presentation}", text)
        self.assertIn('(claimsWithStatus "proved" (Register::claims))', text)
        self.assertIn('(project (Architecture::conceptualModel) id)', text)

    def test_observer_rendering_rules_follow_the_artifacts_and_refuse_a_blind_vantage(self):
        from tools.r30 import observermodel as om, presentationmodel as pm
        claims = [{"id": "root", "status": "open", "depends": []},
                  {"id": "a", "status": "proved", "lean": "X.a", "depends": ["root"]},
                  {"id": "b", "status": "proved", "lean": "X.b", "depends": ["a"]},
                  {"id": "leaf", "status": "open", "depends": ["b"]},
                  {"id": "aside", "status": "proved", "lean": "X.c", "depends": ["root"]}]
        tree = next(p for p in pm.PANELS if p["artifact"] == "chain")
        sheets = next(p for p in pm.PANELS if p["artifact"] == "interfaces")
        leaves = next(p for p in pm.PANELS if p["id"] in om.LEAVES_PANELS)
        modules = next(p for p in pm.PANELS if p["id"] == "modules")
        self.assertEqual(om.rendered(tree, claims), ["a", "b", "aside"])
        self.assertEqual(om.rendered(sheets, claims), ["a", "b"])
        self.assertEqual(om.rendered(leaves, claims), [])
        self.assertEqual(om.rendered(modules, claims), ["a", "b", "aside"])
        self.assertEqual(om.rendered({"id": "picture", "artifact": "logo"}, claims), [])
        blind = [{"id": "glance", "stakeholder": "community", "panels": ["open-leaves"]}]
        d = om.data(journeys=blind)
        self.assertEqual([p for p in om.problems(d) if "glance" in p],
                         ["vantage glance sees no proved claim: give the journey a panel that renders the register"])
        with self.assertRaisesRegex(ValueError, "glance"):
            om.render(d)
        self.assertIn("[[quadruple]]", om.register_toml(om.data()))

    def test_register_module_matches_frontier_and_states_well_formedness(self):
        from tools.r30 import registermodel
        r = registermodel.check()
        self.assertTrue(r["ok"], r["reason"])
        text = registermodel.render([{"id": "a", "status": "proved", "lean": "X.y", "depends": []},
                                     {"id": "b", "status": "open", "lean": "", "depends": ["a"]}])
        self.assertIn("name: registerDependsResolve", text)
        self.assertIn("proof: decide{}", text)
        self.assertIn('(record Claim {id := "b", status := "open", lean := "", depends := (cons "a" (nil String)), '
                      'relation := (nil String), kappa := ""})', text)
        self.assertIn("name: registerObservedHaveRelations", text)


class ConvertModelTests(unittest.TestCase):
    """The converter is a LexLean module: the signature arena, the lexicon as
    data, `convert` as definitions, and one decided theorem per fixture
    saying that the module and `convert.py` agree character for character."""

    def test_committed_module_matches_convert_py_the_glossary_and_the_fixtures(self):
        from tools.r30 import convertmodel
        r = convertmodel.check()
        self.assertTrue(r["ok"], r["reason"])

    def test_arena_lays_out_a_binder_type_before_the_binder_before_the_body(self):
        from tools.r30 import convertmodel
        nodes, root = convertmodel.encode(sexpr.parse(COUPLING))
        self.assertEqual(nodes[0]["kind"], "nil")
        self.assertEqual((nodes[root]["kind"], nodes[root]["atom"], nodes[root]["mode"]), ("pi", "Q", "explicit"))
        self.assertLess(nodes[root]["left"], root)
        self.assertGreater(nodes[root]["right"], root)
        self.assertEqual(nodes[nodes[root]["left"]], {"kind": "const", "atom": "Nat", "mode": "", "left": 0, "right": 0})
        binders = [n["atom"] for n in nodes if n["kind"] == "pi"]
        self.assertEqual(binders, ["Q", "t", "h0"])

    def test_fixtures_are_the_named_signatures_with_statements_and_refusals(self):
        from tools.r30 import convertmodel
        rows = convertmodel.load_fixtures()
        self.assertEqual([r["lean"] for r in rows], convertmodel.FIXTURE_NAMES)
        lx = Lexicon()
        verdicts = {convertmodel.expected(r["signature"], lx)[0] for r in rows}
        self.assertEqual(verdicts, {"statement", "refused"})
        text = convertmodel.MODULE.read_text()
        self.assertEqual(text.count("proof: decide{}"), len(rows))
        self.assertIn(f"statement: ((fixtureCount) = {len(rows)})", text)

    def test_lexicon_snapshot_is_the_entries_the_fixtures_resolve(self):
        """A glossary change outside the snapshot leaves the module unchanged
        (no re-verification on the proof loop); a change inside it is drift."""
        from tools.r30 import convertmodel
        from tools.r30.lexicon import Entry
        lx = Lexicon()
        fixtures = [{"lean": "X.y", "signature": COUPLING}]
        rows, _ = convertmodel.lexemes(fixtures, lx)
        qids = {r["qid"] for r in rows}
        self.assertIn("r30.local::bxor", qids)
        self.assertIn("lexlean.core::eq", qids)
        self.assertNotIn("r30.observation::edge-diagonal", qids)
        before = convertmodel.render(fixtures, lx)
        lx.entries["r30.observation::unrelated-notion"] = Entry("r30.observation::unrelated-notion", "function", "call", 1,
                                                                 "unrelated", lean_name="Rule30UOR.Nowhere.unrelated", project="paper")
        self.assertEqual(convertmodel.render(fixtures, lx), before)
        lx.entries["r30.local::bxor"].surface = "xor"
        self.assertNotEqual(convertmodel.render(fixtures, lx), before)

    def test_render_states_the_python_statement_as_characters(self):
        from tools.r30 import convertmodel
        text = convertmodel.render([{"lean": "X.y", "signature": COUPLING}])
        verdict, statement = convertmodel.expected(COUPLING)
        self.assertEqual(verdict, "statement")
        self.assertTrue(statement.startswith("For every natural number \\(Q\\)"))
        self.assertIn('(cons "statement" (cons "F" (cons "o" (cons "r" (cons " " ', text)
        self.assertIn("name: converts1", text)
        self.assertIn('(record Lexeme {qid := "r30.local::bxor"', text)


class McpTests(unittest.TestCase):
    """The MCP tools are derived from the CLI parser: every leaf subcommand is a
    tool, and a tool call rebuilds an argv the parser accepts."""

    SAMPLE = {"names": ["X"], "query": "q", "id": "i", "message": "m", "name": "n", "statement": "s",
              "qids": ["p::q"], "prefixes": ["Rule30UOR"]}

    def test_every_tool_maps_to_argv(self):
        for tool in tool_list():
            if tool["name"] == "tail_log":
                continue
            argv = argv_for(tool["name"], self.SAMPLE)
            self.assertIsInstance(argv, list)
            self.assertTrue(argv)

    def test_tools_are_the_cli_leaves_and_round_trip(self):
        from tools.r30 import cli
        parser = cli.build_parser()
        names = {t["name"] for t in tool_list()}
        self.assertIn("theorem_add", names)
        self.assertIn("frontier_set", names)
        self.assertIn("interface", names)
        for tool in tool_list():
            if tool["name"] == "tail_log":
                continue
            argv = argv_for(tool["name"], self.SAMPLE)
            try:
                ns = parser.parse_args(argv)
            except SystemExit as e:
                self.fail(f"{tool['name']}: argv {argv} rejected by the CLI parser ({e})")
            self.assertTrue(callable(ns.fn))


class NotationTests(unittest.TestCase):
    """`lexmod` writes the language-1.2 authoring notation; members of an
    imported module are `Module::name` (SPEC §17.21.4)."""

    def test_qualified_members_types_calls_and_constructors(self):
        from tools.r30 import lexmod
        from tools.r30.semantic import ble, call, ctor, n, named, record, s
        self.assertEqual(lexmod.type_(named("Stakeholder", "Foundation.Arch")), "Foundation.Arch::Stakeholder")
        self.assertEqual(lexmod.type_({"kind": "list", "element": named("Command", "Api")}), "(List Api::Command)")
        self.assertEqual(lexmod.expr(call("commands", module="Api")), "(Api::commands)")
        self.assertEqual(lexmod.expr(ctor("ModelKind.qualityModel", "Foundation.Arch")), "(ctor Foundation.Arch::ModelKind.qualityModel)")
        self.assertEqual(lexmod.expr(record("Concern", "Foundation.Arch", index=n(2))), "(record Foundation.Arch::Concern {index := 2})")
        self.assertEqual(lexmod.expr(ble(n(5), call("measureThreshold", s("ci-render-time"), call("measures")))),
                         '(5 <=? (measureThreshold "ci-render-time" (measures)))')
        text = lexmod.module("M", [], imports=["Zeta", "Alpha"], glossaries=["prism.arch@1.0.0"])
        self.assertIn("\\useglossary{lexlean.std.bool@1.2.0}\n\\useglossary{lexlean.std.nat@1.2.0}\n\\useglossary{prism.arch@1.0.0}\n"
                      "\\importmodule{Alpha}\n\\importmodule{Zeta}\n\\title{Boolean}", text)

    def test_long_literal_lists_stay_below_the_notation_nesting_limit(self):
        """The pinned notation's reader nests about 128 levels (LLT4001 beyond);
        `semantic.lst` chunks every literal list through `prim append`, so the
        longest list a generator can produce (a register of 500 records, each
        with its own string list) stays below 100 levels of parentheses."""
        from tools.r30 import lexmod, semantic
        from tools.r30.semantic import CHUNK, definition, list_t, lst, named, record, s, strings

        def depth(text):
            best = current = 0
            in_string = escape = False
            for ch in text:
                if in_string:
                    if escape:
                        escape = False
                    elif ch == "\\":
                        escape = True
                    elif ch == '"':
                        in_string = False
                    continue
                if ch == '"':
                    in_string = True
                elif ch in "([{":
                    current += 1
                    best = max(best, current)
                elif ch in ")]}":
                    current -= 1
            return best

        self.assertEqual(CHUNK, 40)
        rows = [record("Claim", id=s(f"claim-{i}"), depends=strings([f"dep-{j}" for j in range(i % (CHUNK + 1))]))
                for i in range(500)]
        text = lexmod.decl(definition("claims", list_t(named("Claim")), lst(rows, named("Claim"))))
        self.assertLess(depth(text), 100)
        self.assertLess(depth(lexmod.expr(strings([str(i) for i in range(500)]))), 100)
        self.assertEqual(lexmod.expr(semantic.lst([s("a")], semantic.STR)), '(cons "a" (nil String))')
        self.assertEqual(text.count("(prim append"), 12)
        # The chunking is a construction, not a change of value: the generators
        # that chunk by hand produce the same data form.
        from tools.r30 import convertmodel, observermodel
        self.assertIs(convertmodel.lst, lst)
        self.assertIs(observermodel.lst, lst)
        self.assertEqual(convertmodel.CHUNK, CHUNK)

    def test_vendored_stdlib_is_language_1_2_and_declares_the_arch_entities(self):
        api = repo.PROJECTS["api"]
        arch = (api / "stdlib" / "Foundation" / "Arch.lex.tex").read_text()
        self.assertIn("\\useglossary{prism.arch@1.0.0}", arch)
        self.assertNotIn("\\semanticdata", arch)
        for name in ("Stakeholder", "Concern", "Viewpoint", "View", "ModelKind"):
            self.assertIn(f"name: {name},", arch)
        import tomllib
        project = tomllib.loads((api / "lexlean.toml").read_text())
        self.assertEqual(project["source_roots"], ["src", "stdlib"])
        self.assertEqual({x["package"] for x in project["lexicon_source"] if x["kind"] == "path"}, {"prism.arch", "prism.qual"})
        self.assertEqual(project["entrypoints"], sorted(project["entrypoints"]))
        for lic in ("stdlib/LICENSE-APACHE", "stdlib/LICENSE-MIT", "language/LICENSE-APACHE", "language/LICENSE-MIT"):
            self.assertTrue((api / lic).exists(), lic)


class PrismModelTests(unittest.TestCase):
    """The PrismPM registers are generated from the register, the parser and
    the architecture; every command of the parser has a row, every standard
    entry is a vendored lexicon entry, and the published JSON fits its schema."""

    def test_model_registers_are_current(self):
        from tools.r30 import prismmodel
        r = prismmodel.check()
        self.assertTrue(r["ok"], r["reason"])
        for name in ("authorities", "ids", "ledger", "commands", "standards", "projection", "contracts"):
            self.assertTrue((prismmodel.MODEL / f"{name}.toml").exists(), name)

    def test_commands_register_is_the_parser(self):
        import tomllib
        from tools.r30 import prismmodel, apimodel
        rows = tomllib.loads(prismmodel.commands())["command"]
        self.assertEqual([r["name"] for r in rows], [r["name"] for r in apimodel.surface()])
        by_name = {r["name"]: r for r in rows}
        self.assertEqual(by_name["chain"]["mutates"], "never")
        self.assertEqual(by_name["view_render"]["mutates"], "view-directory")
        self.assertEqual(by_name["frontier_set"]["mutates"], "register")
        self.assertEqual(by_name["api_sync"]["result_schema"], "r30/api-sync-result/1")

    def test_standards_name_vendored_entries_used_by_the_architecture(self):
        import tomllib
        from tools.r30 import prismmodel, standardsmodel
        rows = tomllib.loads(prismmodel.standards())["standard"]
        self.assertEqual([r["id"] for r in rows], [r["id"] for r in standardsmodel.rows()])
        faceted = [r for r in rows if "facet_package" in r]
        self.assertEqual({r["facet_package"] for r in faceted}, {"prism.arch", "prism.qual"})
        self.assertEqual({r["id"] for r in faceted}, set(standardsmodel.FACETS))
        for r in faceted:
            for e in r["facet_entries"]:
                self.assertTrue((repo.PROJECTS["api"] / "language" / r["facet_package"] / "entries" / f"{e}.toml").exists(), e)

    def test_projection_targets_declared_types(self):
        import tomllib
        from tools.r30 import prismmodel
        rows = tomllib.loads(prismmodel.projection())
        src = repo.PROJECTS["api"] / "src"
        for e in rows["entity"]:
            self.assertIn(f"name: {e['type_name']},", (src / f"{e['module']}.lex.tex").read_text(), e)
        self.assertEqual(rows["catalog"][0]["declaration"], "ModelKind")

    def test_register_json_fits_its_contract(self):
        import tomllib
        from tools.r30 import prismmodel, apimodel
        contracts = tomllib.loads(prismmodel.contracts())["contract"]
        commands = {r["name"] for r in apimodel.surface()}
        for c in contracts:
            self.assertIn(c["produced_by"], commands, c["schema"])
            self.assertTrue((repo.PROJECTS["api"] / c["path"]).exists(), c["path"])
        schema = prismmodel.REGISTER_SCHEMA["items"]
        for claim in frontier.list_claims():
            self.assertTrue(set(schema["required"]) <= set(claim), claim["id"])
            self.assertTrue(set(claim) <= set(schema["properties"]), claim["id"])
            self.assertIn(claim["status"], schema["properties"]["status"]["enum"])


class StandardsTests(unittest.TestCase):
    """Standards.lex.tex names every external standard the implementation
    realizes; the data the kernel decides over is checked here first, and the
    machine-readable artifacts the standards call for are read back from a
    rendered view."""

    @classmethod
    def setUpClass(cls):
        from tools.r30 import site
        cls.tmp = tempfile.TemporaryDirectory()
        cls.out = Path(cls.tmp.name) / "view"
        site.render_view(cls.out)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def read_json(self, name):
        import json
        return json.loads((self.out / name).read_text())

    def test_module_is_current_and_the_register_covers_the_declared_things(self):
        from tools.r30 import standardsmodel as sm, presentationmodel as pm, apimodel
        r = sm.check()
        self.assertTrue(r["ok"], r["reason"])
        self.assertEqual(sm.problems(), [])
        rows = sm.rows()
        self.assertEqual(len({x["id"] for x in rows}), len(rows))
        declared = set(sm.declared_ids())
        realizers = {x for st in rows for x in st["realizedBy"]}
        for st in rows:
            self.assertTrue(st["authority"].startswith("https://"), st["id"])
            self.assertTrue(st["realizedBy"], st["id"])
            self.assertTrue(set(st["realizedBy"]) <= declared, st["id"])
            self.assertIn(st["coverage"], ("implemented", "planned"))
        for x in [p["id"] for p in pm.PANELS] + [a["id"] for a in pm.ARTIFACTS] + [j["id"] for j in pm.JOURNEYS] + \
                [row["name"] for row in apimodel.surface()] + sm.NAVIGATION + sm.VISUALIZATIONS:
            self.assertIn(x, realizers, x)
        by_id = {st["id"]: st for st in rows}
        self.assertEqual(by_id["lean-4"]["version"], (repo.PROJECTS["api"] / "lean-toolchain").read_text().strip())
        self.assertIn("language 1.2", by_id["lexlean"]["version"])
        self.assertEqual(by_id["oci-distribution"]["coverage"], "planned")
        text = sm.render()
        self.assertIn("\\importmodule{Presentation}", text)
        for name in ("Standard", "standards", "navigation", "visualizations", "declaredIds", "standardIdsDistinct", "everyStandardHasAuthority",
                     "everyStandardRealized", "realizersDeclared", "panelsNameAStandard", "artifactsNameAStandard", "journeysNameAStandard",
                     "commandsNameAStandard", "navigationNamesAStandard", "visualizationsNameAStandard", "leanToolchainPinned", "lexleanPinned"):
            self.assertIn(f"name: {name},", text)
        self.assertIn('(allMembers (Architecture::commandNames (Api::commands)) (standardRealizers (standards)))', text)
        # a realizer nobody declares, and a command no standard names, are found before the kernel
        broken = [dict(rows[0], realizedBy=["ghost"])] + rows[1:]
        self.assertIn("standard iso-42010: realizer ghost is not declared", sm.problems(broken))
        self.assertIn("command sig names no standard", sm.problems([r for r in rows if r["id"] != "openapi-3.1"]))
        # the artifacts the standards call for are declared, rendered and cited by a verification step
        evidence = {e for s in pm.STEPS if s["pole"] == "verification" for e in s["evidence"]}
        for aid in ("standards", "standards-module", "openapi", "sitemap", "provenance", "jsonld", "attestations", "citation"):
            self.assertIn(aid, {a["id"] for a in pm.ARTIFACTS}, aid)
            self.assertIn(aid, evidence, aid)
        from tools.r30 import schema
        schema.validate(sm.STANDARDS_SCHEMA, self.read_json("standards.json"))
        self.assertEqual([x["id"] for x in self.read_json("standards.json")], [x["id"] for x in rows])

    def test_openapi_describes_the_command_surface(self):
        from tools.r30 import apimodel, prismmodel, schema
        doc = self.read_json("openapi.json")
        self.assertEqual(doc["openapi"], "3.1.0")
        self.assertEqual(doc["jsonSchemaDialect"], schema.DRAFT)
        surface = apimodel.surface()
        self.assertEqual(sorted(doc["paths"]), sorted("/" + "/".join(r["path"]) for r in surface))
        ops = {op["operationId"]: (method, op) for item in doc["paths"].values() for method, op in item.items()}
        self.assertEqual(set(ops), {r["name"] for r in surface})
        self.assertEqual(ops["chain"][0], "get")
        self.assertEqual(ops["api_sync"][0], "post")
        self.assertEqual(ops["frontier_set"][1]["x-r30-mutates"], "register")
        claim = ops["claim"][1]
        self.assertEqual([(p["name"], p["required"]) for p in claim["parameters"]], [("id", True), ("related", False)])
        self.assertEqual(claim["responses"]["200"]["content"]["application/json"]["schema"], {"$ref": "#/components/schemas/claim-result"})
        self.assertIn("R301001", claim["responses"]["default"]["description"])
        for name in schema.RESULTS:
            self.assertIn(name, doc["components"]["schemas"])
            self.assertNotIn("$defs", doc["components"]["schemas"][name])
        self.assertEqual(doc["components"]["schemas"]["brief-result"]["properties"]["open"]["items"]["type"], "object")
        self.assertIn("register", doc["components"]["schemas"])
        for op_method, op in ops.values():
            schema_id = op["x-r30-result-schema"]
            self.assertEqual(schema_id, prismmodel.result_schema(op["operationId"]))
        text = (self.out / "openapi.json").read_text()
        self.assertNotIn('"$ref": "#/$defs', text)

    def test_sitemap_lists_every_step_deep_link(self):
        import xml.etree.ElementTree as ET
        from tools.r30 import presentationmodel as pm, standardsmodel as sm
        root = ET.fromstring((self.out / "sitemap.xml").read_text())
        ns = {"s": "http://www.sitemaps.org/schemas/sitemap/0.9"}
        locs = [u.find("s:loc", ns).text for u in root.findall("s:url", ns)]
        self.assertEqual(locs[0], pm.PUBLICATION["url"])
        self.assertEqual(locs[1:], [sm.step_url(s) for s in pm.STEPS])
        for u in root.findall("s:url", ns):
            self.assertRegex(u.find("s:lastmod", ns).text, r"^\d{4}-\d{2}-\d{2}$")
        self.assertIn(f"Sitemap: {pm.PUBLICATION['url']}sitemap.xml", (self.out / "robots.txt").read_text())

    def test_provenance_derives_every_proved_claim_from_its_theorem(self):
        from tools.r30 import standardsmodel as sm
        doc = self.read_json("provenance.jsonld")
        self.assertIn("prov", doc["@context"])
        by_id = {g["@id"]: g for g in doc["@graph"]}
        claims = {c["id"]: c for c in frontier.list_claims()}
        for cid, c in claims.items():
            entity = by_id[f"r30:claim/{cid}"]
            self.assertEqual(entity["r30:status"], c["status"])
            if c["status"] == "proved":
                self.assertEqual(entity["prov:wasDerivedFrom"], f"r30:lean/{c['lean']}")
                self.assertEqual(entity["prov:wasAttributedTo"], "r30:agent/lean-kernel")
                theorem = by_id[f"r30:lean/{c['lean']}"]
                module = by_id[theorem["r30:module"]]
                self.assertTrue(("r30:kappa" in module) != ("r30:kappaNote" in module), module["@id"])
                if "r30:kappa" in module:
                    self.assertRegex(module["r30:kappa"], r"^sha256:[0-9a-f]{64}$")
                if c.get("lexeme"):
                    self.assertTrue(entity["r30:attestedBy"].startswith("r30:activity/attestation/"))
            else:
                self.assertNotIn("prov:wasDerivedFrom", entity)
        self.assertEqual(by_id["r30:agent/lean-kernel"]["r30:axiomsAllowed"], ["propext", "Quot.sound"])
        # without receipts the labels are omitted and the document says so
        without = sm.provenance(list(claims.values()), "abc", "now", {"id": "a" * 64}, kappas={})
        self.assertTrue(without["r30:kappaLabels"].startswith("omitted"))
        self.assertTrue(all("r30:kappaNote" in g for g in without["@graph"] if g.get("r30:kind") == "Lean module"))
        self.assertEqual(sm.module_of("Rule30UOR.Interfaces.lhBandAgree_engine_hypotheses_unsat"), "Rule30UOR.Interfaces")

    def test_schema_org_describes_every_step_the_paper_the_repository_and_the_register(self):
        from tools.r30 import presentationmodel as pm, standardsmodel as sm
        doc = self.read_json("schema.json")
        self.assertEqual(doc["@context"], "https://schema.org")
        types = {}
        for g in doc["@graph"]:
            types.setdefault(g["@type"], []).append(g)
        self.assertEqual({g["name"] for g in types["ScholarlyArticle"]}, {sm.PAPER_TITLE})
        self.assertEqual(types["SoftwareSourceCode"][0]["codeRepository"], pm.APPLICATION_RECORD["repository"])
        self.assertEqual(len(types["Dataset"]), 1)
        steps = [g for g in types["LearningResource"] if g["learningResourceType"] == "lesson step"]
        self.assertEqual([g["@id"] for g in steps], [sm.step_url(s) for s in pm.STEPS])
        self.assertEqual([g["teaches"] for g in steps], [s["goal"] for s in pm.STEPS])
        lessons = [g for g in types["LearningResource"] if g["learningResourceType"] == "lesson"]
        self.assertEqual([g["@id"].split("#")[1] for g in lessons], [j["id"] for j in pm.JOURNEYS])
        for g in types["ScholarlyArticle"]:
            self.assertEqual(len(g["associatedMedia"]), 3)
            for m in g["associatedMedia"]:
                self.assertRegex(m["sha256"], r"^[0-9a-f]{64}$")

    def test_site_head_carries_json_ld_and_open_graph(self):
        import json
        from tools.r30 import presentationmodel as pm, site
        html = (self.out / "index.html").read_text()
        head = html[:html.index("</head>")]
        self.assertIn('<script type="application/ld+json">', head)
        start = head.index('<script type="application/ld+json">') + len('<script type="application/ld+json">')
        graph = json.loads(head[start:head.index("</script>", start)].replace("<\\/", "</"))
        self.assertEqual(graph, self.read_json("schema.json"))
        for prop in ("og:title", "og:type", "og:url", "og:description", "og:image"):
            self.assertIn(f'<meta property="{prop}" content="', head)
        self.assertIn(f'<meta property="og:url" content="{pm.PUBLICATION["url"]}">', head)
        self.assertIn('<link rel="sitemap" type="application/xml" href="sitemap.xml">', head)
        # the body is untouched by the injection: the template's body is the rendered body
        template = site.TEMPLATE.read_text()
        self.assertEqual(html[html.index("<body>"):html.index(site.DATA_OPEN)], template[template.index("<body>"):template.index(site.DATA_OPEN)])
        # a template without a head (the embed test's snippet) takes the data and ignores the head block
        self.assertEqual(site.embed(f"<x>{site.DATA_OPEN}null</script></x>", {}, "<meta>"), f"<x>{site.DATA_OPEN}{{}}</script></x>")

    def test_in_toto_statement_subjects_are_the_attested_documents(self):
        from tools.r30 import site
        doc = self.read_json("attestations.intoto.json")
        self.assertEqual(doc["_type"], "https://in-toto.io/Statement/v1")
        digests = {d["pdfSha256"] for d in site.documents()["documents"]}
        self.assertTrue(digests <= {s["digest"]["sha256"] for s in doc["subject"]})
        self.assertEqual({s["name"] for s in doc["subject"] if s["name"].endswith(".pdf")}, set(site.PDF_PACKAGE.values()))
        self.assertEqual(doc["predicate"]["attestation"]["id"], site.attestation("paper")["id"])

    def test_citation_file_names_the_author_the_title_and_the_repository(self):
        from tools.r30 import standardsmodel as sm
        text = (ROOT / "CITATION.cff").read_text()
        self.assertEqual(text, (self.out / "CITATION.cff").read_text())
        self.assertIn("cff-version: 1.2.0", text)
        self.assertIn(f'title: "{sm.PAPER_TITLE}"', text)
        self.assertIn("family-names: Flom", text)
        self.assertIn("given-names: Alex", text)
        self.assertIn(f'repository-code: "{sm.REPOSITORY}"', text)
        self.assertIn("license: MIT", text)
        self.assertTrue((ROOT / "LICENSE").read_text().startswith("MIT License"))

    def test_spdx_expressions_are_well_formed(self):
        import re, tomllib
        from tools.r30 import prismmodel
        pkg = tomllib.loads(prismmodel.stdlib_package())
        for part in re.split(r"\s+(?:OR|AND|WITH)\s+", pkg["license"]):
            self.assertRegex(part, r"^[A-Za-z0-9.+-]+$", pkg["license"])
            self.assertTrue((repo.PROJECTS["api"] / "stdlib" / f"LICENSE-{part.split('-')[0].upper()}").exists(), part)


class SiteTests(unittest.TestCase):
    """`view render` is the runtime of Presentation.lex.tex: it writes every
    declared artifact, embeds the data in the site, and the logo is Rule 30."""

    def test_rule30_rows_and_logo(self):
        from tools.r30 import site
        import xml.etree.ElementTree as ET
        rows = site.rule30_rows(4)
        self.assertEqual(rows, [[1], [1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1, 1, 1]])
        svg = site.logo_svg(rows=12)
        root = ET.fromstring(svg)
        self.assertEqual(root.tag, "{http://www.w3.org/2000/svg}svg")
        rects = [r for r in root if r.tag.endswith("rect")]
        accent = [r for r in rects if r.get("fill") == site.ACCENT]
        self.assertEqual(len(accent), sum(r[len(r) // 2] for r in site.rule30_rows(12)))
        self.assertNotIn("<script", svg)
        r = site.check_logo()
        self.assertTrue(r["ok"], r["reason"])

    def test_render_view_writes_every_declared_artifact_with_embedded_data(self):
        import json
        from tools.r30 import site, presentationmodel as pm
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "view"
            r = site.render_view(out)
            self.assertEqual(r["written"], [a["path"] for a in pm.ARTIFACTS])
            for a in pm.ARTIFACTS:
                self.assertTrue((out / a["path"]).exists(), a["path"])
            html = (out / "index.html").read_text()
            start = html.index(site.DATA_OPEN) + len(site.DATA_OPEN)
            data = json.loads(html[start:html.index(site.DATA_CLOSE, start)].replace("<\\/", "</"))
            self.assertEqual([c["id"] for c in data["register"]], [c["id"] for c in frontier.list_claims()])
            self.assertEqual(data["chain"], frontier.chain()[0])
            self.assertEqual(data["brand"]["name"], pm.BRAND["name"])
            self.assertTrue(set(data["openLeaves"]) <= {c["id"] for c in data["register"] if c["status"] == "open"})
            self.assertEqual((out / "chain.txt").read_text().strip(), frontier.chain()[1].strip())
            self.assertEqual(json.loads((out / "register.json").read_text()), frontier.list_claims())
        self.assertIn("</script>", site.embed('<script id="r30-data" type="application/json">null</script>', {"x": "</script>"}))
        self.assertNotIn("</script>\"", site.embed('<script id="r30-data" type="application/json">null</script>', {"x": "</script>"}))

    def test_open_leaves_are_open_claims_nothing_rests_on(self):
        claims = frontier.list_claims()
        depended = {d for c in claims for d in c.get("depends", [])}
        for leaf in frontier.open_leaves():
            c = next(x for x in claims if x["id"] == leaf)
            self.assertEqual(c["status"], "open")
            self.assertNotIn(leaf, depended)

    def test_view_workflow_is_the_publication_the_application_declares(self):
        from tools.r30 import presentationmodel as pm
        text = (repo.ROOT / pm.PUBLICATION["workflow"]).read_text()
        self.assertIn("python3 -m tools.r30 view render --out view", text)
        self.assertIn(f"timeout-minutes: {pm.PUBLICATION['timeoutMinutes']}", text)
        self.assertIn(f"name: {pm.PUBLICATION['artifactName']}", text)
        for forbidden in ("lake", "lexlean", "unittest", "pytest"):
            self.assertNotIn(forbidden + " ", text.replace("no Lean, no lexlean", ""), forbidden)
        self.assertEqual(pm.APPLICATION_RECORD["workflow"], pm.PUBLICATION["workflow"])
        # GitHub Pages: the rendered view is uploaded as the Pages artifact and
        # deployed in the named environment with the permissions a deployment
        # needs, under one concurrency group, and the deployed page is checked
        # to serve the commit it was rendered from (the site embeds it)
        self.assertIn("actions/upload-pages-artifact@v", text)
        self.assertIn("actions/deploy-pages@v", text)
        self.assertIn(f"name: {pm.PUBLICATION['environment']}", text)
        for permission in ("contents: read", "pages: write", "id-token: write"):
            self.assertIn(permission, text)
        self.assertIn("group: pages", text)
        self.assertIn('grep -qF "\\"commit\\": \\"$GITHUB_SHA\\""', text)
        self.assertTrue(pm.PUBLICATION["url"].startswith("https://") and pm.PUBLICATION["url"].endswith("/"))
        self.assertIn(pm.PUBLICATION["url"], text)

    def test_mathematician_and_layperson_views_are_modeled_and_rendered(self):
        """The two reading stakeholders: each holds the concern its viewpoint
        frames, each viewpoint governs a view and panels, each has a journey,
        and the explainer is plain language (no formal vocabulary) declared as
        data with distinct ids."""
        from tools.r30 import archmodel, presentationmodel as pm, site
        held = {s["id"]: set(s["concerns"]) for s in archmodel.STAKEHOLDERS}
        self.assertIn("mathematics", held["mathematician"]); self.assertIn("plain-language", held["layperson"])
        viewpoints = {vp["id"]: vp for vp in archmodel.VIEWPOINTS}
        self.assertEqual((viewpoints["paper"]["stakeholder"], viewpoints["paper"]["concern"]), ("mathematician", "mathematics"))
        self.assertEqual((viewpoints["plain"]["stakeholder"], viewpoints["plain"]["concern"]), ("layperson", "plain-language"))
        panels = {p["id"]: p for p in pm.PANELS}
        self.assertEqual({p for p, x in panels.items() if x["viewpoint"] == "paper" and not p.startswith("viz-")}, {"paper", "obligation", "refutations"})
        self.assertEqual({p for p, x in panels.items() if x["viewpoint"] == "plain" and not p.startswith("viz-")}, {"picture", "explainer"})
        journeys = {j["id"]: j for j in pm.JOURNEYS}
        self.assertEqual(journeys["mathematics"]["stakeholder"], "mathematician")
        # a journey's panels are its steps' panels in order of first use
        self.assertEqual([p for p in journeys["mathematics"]["panels"] if not p.startswith("viz-")], ["paper", "reduction-tree", "register", "obligation", "refutations", "verify"])
        self.assertEqual((journeys["first-visit"]["stakeholder"], [p for p in journeys["first-visit"]["panels"] if not p.startswith("viz-")]),
                         ("layperson", ["picture", "explainer", "reduction-tree", "register", "obligation", "verify"]))
        self.assertEqual(len({e["id"] for e in pm.EXPLAINER}), len(pm.EXPLAINER))
        for e in pm.EXPLAINER:
            self.assertTrue(e["title"] and e["text"], e["id"])
            for jargon in ("LexLean", "lexeme", "propext", "Quot.sound", "bxor", "twopow", "2-kernel", "automatic"):
                self.assertNotIn(jargon, e["text"], f"{e['id']} uses {jargon}")
        # the explainer's center column is Rule 30's
        words = {1: "black", 0: "white"}
        column = ", ".join(words[r[len(r) // 2]] for r in site.rule30_rows(16))
        self.assertIn(column, next(e["text"] for e in pm.EXPLAINER if e["id"] == "center-column"))
        self.assertEqual(next(c["status"] for c in frontier.list_claims() if c["id"] == pm.OBLIGATION), "open")
        text = pm.render_presentation()
        for name in ("Paragraph", "explainer", "obligation", "paragraphIdsDistinct"):
            self.assertIn(f"name: {name}", text)
        app = pm.render_application()
        for name in ("obligationIsOpen", "publicationIsTheApplicationWorkflow"):
            self.assertIn(f"name: {name}", app)
        self.assertIn(f'url := "{pm.PUBLICATION["url"]}"', app)

    def test_statements_picture_and_explainer_artifacts(self):
        """statements.json carries every theorem, lemma and corollary of
        Observations.lex.tex with its Lean name and lexeme from the glossary,
        the attested PDFs with the manifest's digests and the attestation; the
        picture is Rule 30 with the center column in the accent colour."""
        import json
        import xml.etree.ElementTree as ET
        from tools.r30 import site, presentationmodel as pm
        st = site.statements()
        text = site.PAPER_MODULE.read_text()
        self.assertEqual(len(st["statements"]), sum(text.count(f"\\begin{{{k}}}") for k in ("theorem", "lemma", "corollary")))
        for r in st["statements"]:
            self.assertTrue(r["lean"] and r["lexeme"] and r["section"] and r["statement"], r["id"])
            self.assertIn(r["kind"], ("theorem", "lemma", "corollary"))
            self.assertNotIn("\\allowaxioms", r["statement"])
        self.assertEqual({s["id"] for s in st["sections"]}, {r["section"] for r in st["statements"]})
        manifest = json.loads((ROOT / "pdf-manifest.json").read_text())
        self.assertEqual({d["name"]: d["pdfSha256"] for d in st["pdfs"]["documents"]},
                         {k: v["pdf_sha256"] for k, v in manifest["documents"].items()})
        published = {a["path"] for a in pm.ARTIFACTS}
        for d in st["pdfs"]["documents"]:
            self.assertIn(d["path"], published, d["name"])
        self.assertTrue(st["attestation"] and len(st["attestation"]["id"]) == 64)
        svg = site.picture_svg(rows=20)
        root = ET.fromstring(svg)
        rects = [r for r in root if r.tag.endswith("rect")]
        self.assertEqual(len([r for r in rects if r.get("fill") == site.ACCENT]), sum(r[len(r) // 2] for r in site.rule30_rows(20)))
        self.assertIn('fill="var(--accent)"', site.picture_svg(rows=4, ink="var(--ink)", accent="var(--accent)", background=None))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "view"
            site.render_view(out)
            self.assertEqual(json.loads((out / "statements.json").read_text())["statements"], st["statements"])
            self.assertEqual(json.loads((out / "explainer.json").read_text()), pm.EXPLAINER)
            self.assertTrue((out / "rule30.svg").read_text().startswith("<svg"))
            self.assertTrue((out / "Rule30-Paper.pdf").read_bytes().startswith(b"%PDF-"))
            html = (out / "index.html").read_text()
            self.assertIn('"commit": "', html)
            for panel in pm.PANELS:
                self.assertIn(f'"id": "{panel["id"]}"', html)


class ProductionTests(unittest.TestCase):
    """The production roots of Api.lex.tex are executable definitions with a
    production clause (SPEC §17.13); the request and the runtime-roots register
    follow them; the pinned compiler's targets are the pinned digests."""

    def test_api_module_declares_the_production_roots(self):
        from tools.r30 import apimodel, production
        text = apimodel.MODULE.read_text()
        for name, spec in apimodel.PRODUCTION_ROOTS.items():
            self.assertIn(f"name: {name},", text)
            self.assertIn(f"production: {{effects: [{', '.join(spec['effects'])}], targets: [{', '.join(spec['targets'])}]}}", text)
        self.assertEqual(text.count("executable: true"), len(apimodel.PRODUCTION_ROOTS))
        roots = production.roots()
        self.assertEqual([r["root"] for r in roots], sorted(r["root"] for r in roots))
        self.assertEqual(production.crate_name("commandCount"), "rule30_api_command_count")

    def test_request_and_runtime_roots_are_generated_from_the_roots(self):
        import tomllib, json
        from tools.r30 import production
        req = json.loads(production.request_json())
        self.assertEqual(req["spec"], "lexlean/production-request/1")
        self.assertEqual([r["root"] for r in req["roots"]], [r["root"] for r in production.roots()])
        for r in req["roots"]:
            for t in r["targets"]:
                self.assertEqual(t["digest"], production.TARGET_DIGESTS[t["id"]])
            self.assertRegex(r["package"]["name"], r"^[a-z][a-z0-9_]{0,63}$")
        self.assertEqual(production.REQUEST.read_text(), production.request_json())
        rr = tomllib.loads(production.runtime_roots_toml())
        self.assertEqual(rr["spec"], "prismpm/runtime-roots/1")
        self.assertEqual(rr["roots"], [r["root"] for r in production.roots()])
        self.assertEqual(production.RUNTIME_ROOTS.read_text(), production.runtime_roots_toml())

    def test_pinned_compiler_states_the_pinned_targets(self):
        """Skipped without the pinned binary; with it, the version and the
        target digests the request pins are the compiler's own."""
        from tools.r30 import production
        if not Path(repo.lexlean_bin()).exists():
            self.skipTest("no pinned lexlean")
        code, out, _ = repo.run([repo.lexlean_bin(), "--version"])
        self.assertEqual(code, 0)
        self.assertEqual(out.splitlines()[0], f"lexlean {production.LEXLEAN_VERSION}")
        t = production.targets()
        self.assertTrue(t["ok"], t["diagnostics"])
        self.assertEqual(t["targets"], production.TARGET_DIGESTS)

    def test_summarize_reads_a_production_result(self):
        from tools.r30 import production, schema
        result = {"result_id": "ab" * 32, "compiler": {"version": "0.4.0", "semantics": "s", "lean_toolchain": "t"},
                  "source": {"semantic_id": "cd" * 32},
                  "roots": [{"root": "Rule30Api.Api.commands", "optimality": {"status": "not-claimed"}, "outputs": [{
                      "target": {"id": "rust-std"}, "package": {"directory": "packages/rust-std/rule30_api_commands"},
                      "crate": {"path": "evidence/crate/R0.rust-std.rs"},
                      "certification": {"status": "kernel-checked", "axioms": ["Classical.choice", "Quot.sound", "propext"]},
                      "effects": ["allocation", "recursion"]}]}]}
        report = {"ok": True, "stage": "build", "bundle": "rule30-api/.lexlean/production/x", "diagnostics": [],
                  "replay": "bindings-verified", **production.summarize(result)}
        self.assertEqual(report["needs_stack"], 1)
        self.assertEqual(report["outputs"][0]["certification"], "kernel-checked")
        schema.validate(schema.document("api-production-result"), report)
        self.assertIn("rule30_api_commands [rust-std]: kernel-checked", production.render(report))
        self.assertIn("FAILED", production.render({"ok": False, "stage": "build", "diagnostics": ["LLC0202 x"]}))


class ErrorRegisterTests(unittest.TestCase):
    """Every public failure of the CLI is typed: `cli.py` exits only through
    `errors.fail` with a registered code, every registered code is raised, and
    every command a row names is a leaf of the parser (R5)."""

    def test_cli_fails_only_through_registered_codes(self):
        import re
        from tools.r30 import errors
        source = (ROOT / "tools/r30/cli.py").read_text()
        self.assertNotIn("sys.exit(", source)
        self.assertNotIn("sys.exit(", source)
        used = set(re.findall(r'"(R30\d{4})"', source))
        self.assertTrue(all(line.lstrip().startswith("fail(") or "fail(" in line
                            for line in source.splitlines() if re.search(r'"R30\d{4}"', line)))
        registered = {e["code"] for e in errors.ERRORS}
        self.assertEqual(used, registered)
        self.assertEqual(len(registered), len(errors.ERRORS))
        self.assertTrue(all(e["exit"] in (1, 2) for e in errors.ERRORS))

    def test_error_commands_are_parser_leaves_and_register_matches(self):
        import tomllib
        from tools.r30 import errors, prismmodel, apimodel
        leaves = {r["name"] for r in apimodel.surface()}
        for e in errors.ERRORS:
            self.assertTrue(set(e["commands"]) <= leaves, e["code"])
        rows = tomllib.loads(prismmodel.errors())["error"]
        self.assertEqual([r["code"] for r in rows], [e["code"] for e in errors.ERRORS])
        self.assertEqual((prismmodel.MODEL / "errors.toml").read_text(), prismmodel.errors())

    def test_fail_prints_the_code_and_exits_with_its_status(self):
        import io, contextlib
        from tools.r30 import errors
        err = io.StringIO()
        with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as cm:
            errors.fail("R301001", "ghost")
        self.assertEqual(cm.exception.code, 2)
        self.assertEqual(err.getvalue().strip(), "R301001 Unknown claim: ghost")

    def test_unknown_claim_is_a_typed_failure(self):
        import io, contextlib
        from tools.r30 import cli
        err = io.StringIO()
        with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as cm:
            cli.main(["claim", "no-such-claim"])
        self.assertEqual(cm.exception.code, 2)
        self.assertTrue(err.getvalue().startswith("R301001 "))


class ResultSchemaTests(unittest.TestCase):
    """The `--json` report of each read-only command fits its schema file, and
    the validator refuses what the schema excludes."""

    def run_json(self, *argv):
        import io, json, contextlib
        from tools.r30 import cli
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            cli.main(["--json", *argv])
        return json.loads(out.getvalue())

    def schema_for(self, name):
        import json
        from tools.r30 import prismmodel
        return json.loads((prismmodel.SCHEMAS / f"{name}.schema.json").read_text())

    def test_status_brief_chain_and_api_check_fit_their_schemas(self):
        from tools.r30 import schema
        for command, name in (("status", "status-result"), ("brief", "brief-result"), ("chain", "chain-result")):
            schema.validate(self.schema_for(name), self.run_json(command))
        schema.validate(self.schema_for("api-check-result"), self.run_json("api", "check"))

    def test_frontier_list_and_claim_fit_their_schemas(self):
        """`claim` asks Lean for the type; here the kernel is replaced so the
        test needs no built library, and the report shape is the command's."""
        from tools.r30 import schema, cli, leansig
        schema.validate(self.schema_for("register"), self.run_json("frontier", "list"))
        old = leansig.signatures
        leansig.signatures = lambda names, **kw: {n: {"kind": "theorem", "type": ["const", "Prop"]} for n in names}
        self.addCleanup(lambda: setattr(leansig, "signatures", old))
        data = self.run_json("claim", "problem1")
        schema.validate(self.schema_for("claim-result"), data)
        self.assertEqual(data["lean_type"], "(const Prop)")
        self.assertIn("coupling-law", data["dependents"])

    def test_every_result_schema_of_commands_toml_with_a_file_validates_its_shape(self):
        import tomllib, json
        from tools.r30 import prismmodel, schema
        rows = tomllib.loads(prismmodel.commands())["command"]
        by_name = {r["name"]: r["result_schema"] for r in rows}
        self.assertEqual(by_name["frontier_list"], "r30/register/1")
        self.assertEqual(by_name["interface"], "r30/interface-sheet/1")
        self.assertEqual(by_name["api_production"], "r30/api-production-result/1")
        for name in schema.RESULTS:
            doc = json.loads((prismmodel.SCHEMAS / f"{name}.schema.json").read_text())
            self.assertEqual(doc["$id"], f"r30/{name}/1")
            self.assertIn(f"r30/{name}/1", by_name.values())
        contracts = tomllib.loads(prismmodel.contracts())["contract"]
        self.assertTrue({c["schema"] for c in contracts} >= {f"r30/{n}/1" for n in schema.RESULTS})

    def test_validator_refuses_what_the_schema_excludes(self):
        from tools.r30 import schema
        doc = schema.document("chain-result")
        schema.validate(doc, [{"depth": 0, "id": "a", "lean": None, "status": "open"}])
        for bad in ([{"depth": 0, "id": "a", "lean": None, "status": "bogus"}],
                    [{"depth": 0, "id": "a", "lean": None, "status": "open", "extra": 1}],
                    [{"depth": "0", "id": "a", "lean": None, "status": "open"}],
                    [{"id": "a", "lean": None, "status": "open"}]):
            with self.assertRaises(schema.Invalid):
                schema.validate(doc, bad)
        with self.assertRaises(schema.Invalid):
            schema.validate(schema.document("status-result"), {"head": [], "dirty": True})


class ConformanceTests(unittest.TestCase):
    """One scenario per id, tagged with the id and its level; CONFORMANCE.md
    lists every id with its evidence; the registers are drift-checked."""

    def test_every_id_has_one_scenario_tagged_with_its_level(self):
        import re, tomllib
        from tools.r30 import prismmodel
        ids_ = tomllib.loads(prismmodel.ids(prismmodel.rows()))["id"]
        features = prismmodel.features(prismmodel.rows())
        self.assertEqual(set(features), {r["suite"] for r in ids_})
        for suite, text in features.items():
            self.assertEqual((prismmodel.FEATURES / f"{suite}.feature").read_text(), text)
            tags = re.findall(r"^  @(\S+) @(\S+)\n  Scenario: ", text, re.M)
            rows = [r for r in ids_ if r["suite"] == suite]
            self.assertEqual(tags, [(r["id"], r["level"]) for r in rows])
            self.assertEqual(text.count("  Scenario: "), len(rows))
        levels = {r["level"] for r in ids_}
        self.assertEqual(levels, {"some-true", "build", "open"})
        self.assertIn("never asserted", features["register"])
        self.assertIn("nothing is established here", features["register"])

    def test_conformance_document_is_generated_from_the_register(self):
        from tools.r30 import prismmodel
        text = prismmodel.conformance(prismmodel.rows())
        self.assertEqual(prismmodel.CONFORMANCE.read_text(), text)
        self.assertTrue(text.startswith("<!-- @generated by `bin/r30 api sync`"))
        for r in prismmodel.all_ids(prismmodel.rows()).values():
            self.assertIn(f"| `{r['id']}` | `{r['level']}` |", text)
        for a in prismmodel.AUTHORITIES:
            self.assertIn(a["citation"], text)

    def test_dependencies_and_stdlib_registers_bind_the_pins(self):
        import tomllib
        from tools.r30 import prismmodel, production
        deps = {d["id"]: d for d in tomllib.loads(prismmodel.dependencies())["dependency"]}
        self.assertEqual(deps["lexlean"]["version"], production.LEXLEAN_VERSION)
        lock = tomllib.loads((prismmodel.API / "lexlean.lock").read_text())
        self.assertEqual(deps["lexlean"]["revision"], lock["compiler_semantics"])
        self.assertEqual(deps["lean4"]["version"], lock["lean_toolchain"])
        arts = {a["path"]: a["sha256"] for a in deps["prism-stdlib"]["artifact"]}
        self.assertEqual(arts["rule30-api/stdlib/Foundation"], prismmodel.tree_sha256(prismmodel.API / "stdlib" / "Foundation"))
        self.assertEqual(arts["rule30-api/language/prism.arch"], next(p["tree_sha256"] for p in lock["package"] if p["id"] == "prism.arch"))
        std = tomllib.loads(prismmodel.stdlib_package())
        self.assertEqual(std["version"], prismmodel.STDLIB["version"])
        self.assertEqual(deps["prism-stdlib"]["version"], std["version"])
        self.assertEqual((prismmodel.MODEL / "dependencies.toml").read_text(), prismmodel.dependencies())
        self.assertEqual((prismmodel.MODEL / "stdlib-package.toml").read_text(), prismmodel.stdlib_package())


class AccessibilityTests(unittest.TestCase):
    """The site: landmarks, a skip link, a visible focus ring, reduced motion
    honoured, keyboard-operable claim cards, every journey step a panel, and
    WCAG AA contrast (4.5:1) of every text token on its surfaces, in both
    themes, measured from the stylesheet."""

    @staticmethod
    def luminance(hex_colour):
        r, g, b = (int(hex_colour[i:i + 2], 16) / 255 for i in (1, 3, 5))
        f = lambda c: c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
        return 0.2126 * f(r) + 0.7152 * f(g) + 0.0722 * f(b)

    def contrast(self, a, b):
        la, lb = self.luminance(a), self.luminance(b)
        return (max(la, lb) + 0.05) / (min(la, lb) + 0.05)

    def tokens(self, html):
        import re
        themes = {}
        for name, start in (("light", ":root {"), ("dark", ':root[data-theme="dark"] {')):
            block = html[html.index(start):]
            block = block[:block.index("}")]
            themes[name] = dict(re.findall(r"--([a-z-]+):\s*(#[0-9a-f]{6})", block))
        return themes

    def test_landmarks_focus_motion_and_keyboard(self):
        from tools.r30 import site
        html = site.TEMPLATE.read_text()
        self.assertIn('<a class="skip" href="#main">', html)
        self.assertIn('<main id="main"', html)
        for landmark in ("<header", "<nav", "<main", "<footer"):
            self.assertIn(landmark, html)
        self.assertIn(":focus-visible { outline: 3px solid var(--focus)", html)
        self.assertIn("@media (prefers-reduced-motion: reduce)", html)
        self.assertIn('reducedMotion() ? "auto" : "smooth"', html)
        self.assertIn('role="button" tabindex="0" aria-pressed=', html)
        self.assertIn('e.key !== "Enter" && e.key !== " "', html)
        self.assertIn('aria-label="Toggle dark or light theme"', html)
        self.assertIn('role="status"', html)
        self.assertIn('data-missing=', html)
        # one step at a time: the step heading takes focus on navigation, the
        # progress dots mark the current step, the arrow keys move between steps
        self.assertIn('<h2 id="step-title" tabindex="-1">', html)
        self.assertIn('aria-current="step"', html)
        self.assertIn('e.key === "ArrowLeft" || e.key === "ArrowRight"', html)
        self.assertIn('aria-label="Toggle dark or light theme"', html)

    def test_text_tokens_meet_aa_contrast_in_both_themes(self):
        """The design model's pairs, measured here in floating point
        independently of the kernel's integer arithmetic, in both themes as
        the template's generated token block carries them."""
        from tools.r30 import designmodel, site
        themes = self.tokens(site.TEMPLATE.read_text())
        for name in ("light", "dark"):
            self.assertEqual(themes[name], {x["id"]: x[name] for x in designmodel.TOKENS}, name)
        pairs = [(p["foreground"], p["background"], p["minimum"] / 10) for p in designmodel.PAIRS]
        for needle in (("ink", "bg", 4.5), ("muted", "panel", 4.5), ("link", "soft", 4.5), ("accent-ink", "accent", 4.5), ("focus", "bg", 3.0)):
            self.assertIn(needle, pairs)
        for name, t in themes.items():
            for fg, bg, minimum in pairs:
                self.assertGreaterEqual(self.contrast(t[fg], t[bg]), minimum, f"{name}: {fg} on {bg}")

    def test_journeys_check_finds_a_step_without_a_panel(self):
        from tools.r30 import site, presentationmodel as pm
        self.assertEqual(site.check_journeys(), [])
        broken = [{"id": "j", "stakeholder": "researcher", "panels": ["register", "ghost-panel"]}]
        self.assertEqual(site.check_journeys(pm.PANELS, broken, steps=[]), ["journey j: panel ghost-panel is not rendered", "journey j: no steps"])
        nobody = [{"id": "j", "stakeholder": "nobody", "panels": ["register"]}]
        self.assertEqual(site.check_journeys(pm.PANELS, nobody, steps=[]), ["journey j: stakeholder nobody is not declared", "journey j: no steps"])
        old = pm.JOURNEYS[:]
        pm.JOURNEYS[:] = broken
        self.addCleanup(lambda: pm.JOURNEYS.__setitem__(slice(None), old))
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "ghost-panel"):
                site.render_view(Path(tmp) / "view")

    def test_readme_points_to_the_view_and_the_api(self):
        text = (ROOT / "README.md").read_text()
        from tools.r30 import presentationmodel as pm
        self.assertIn("## Centerline: the current view and the API modules", text)
        for needle in ("bin/r30 view render", "bin/r30 api check", "src/Api.lex.tex", "rule30-current-view", "bin/r30 api production",
                       pm.PUBLICATION["url"]):
            self.assertIn(needle, text)
        api = (ROOT / "rule30-api" / "README.md").read_text()
        for needle in ("## The views and the Pages deployment", pm.PUBLICATION["url"], "statements.json", "explainer.json",
                       "actions/deploy-pages", "github-pages"):
            self.assertIn(needle, api)


class PedagogyTests(unittest.TestCase):
    """The site is a lesson: every journey is an ordered sequence of steps
    through the Observer's poles, modeled in Presentation.lex.tex, decided by
    the kernel, mirrored by `step_problems`, and rendered one step at a time
    with deep links."""

    JARGON = ("Lean", "LexLean", "kernel", "theorem", "lexeme", "2-adic", "propext", "Quot.sound")

    def test_steps_are_modeled_and_the_theorems_are_stated(self):
        from tools.r30 import presentationmodel as pm, archmodel, observermodel as om
        self.assertEqual(pm.step_problems([c["id"] for c in frontier.list_claims()]), [])
        poles = [x["id"] for x in pm.POLES]
        self.assertEqual(poles, ["sensual-object", "sensual-quality", "real-quality", "withdrawn", "verification"])
        self.assertEqual(len({s["id"] for s in pm.STEPS}), len(pm.STEPS))
        for j in pm.JOURNEYS:
            mine = [s for s in pm.STEPS if s["journey"] == j["id"]]
            self.assertEqual([s["order"] for s in mine], list(range(1, len(mine) + 1)), j["id"])
            self.assertEqual([s["next"] for s in mine], [s["id"] for s in mine[1:]] + [""], j["id"])
            indices = [poles.index(s["pole"]) for s in mine]
            self.assertEqual(indices, sorted(indices), j["id"])
            self.assertEqual(set(poles), {s["pole"] for s in mine}, j["id"])
            self.assertEqual(mine[-1]["pole"], "verification", j["id"])
            self.assertEqual(mine[-1]["panel"], "verify", j["id"])
            self.assertIn("obligation", [s["panel"] for s in mine if s["pole"] == "withdrawn"], j["id"])
            self.assertIn(pm.OBLIGATION, [e for s in mine if s["pole"] == "withdrawn" for e in s["evidence"]], j["id"])
            self.assertEqual(j["panels"], list(dict.fromkeys(s["panel"] for s in mine)), j["id"])
            for s in mine:
                self.assertTrue(s["title"] and s["goal"], s["id"])
        # every verification command is a command; the Observer reads the steps' panels unchanged
        self.assertTrue({v["command"] for v in pm.VERIFICATIONS} <= {row["name"] for row in __import__("tools.r30.apimodel", fromlist=["surface"]).surface()})
        for q, j in zip(om.data()["quadruples"], pm.JOURNEYS):
            self.assertEqual(q["sensualQualities"], j["panels"])
        text = pm.render_presentation()
        self.assertIn("\\importmodule{Register}", text)
        for name in ("Pole", "Step", "Verification", "steps", "poles", "verifications", "stepPanelsArePanels", "stepJourneysAreJourneys",
                     "journeysStepsConsecutive", "journeysStepsLinked", "journeysCoverPolesInOrder", "journeysEndInVerification",
                     "journeyPanelsAreStepPanels", "stepEvidenceDeclared", "stepParagraphsDeclared", "verificationsAreCommands", "everyPanelInAStep"):
            self.assertIn(f"name: {name},", text)
        self.assertIn('(appendStrings (Register::idsOf (Register::claims)) (artifactIds (artifacts)))', text)
        self.assertIn('(prim equal (lastString (stepPoles (stepsOfJourney (project head id) ss)) "") "verification" : Bool)', text)
        # the quality model measures the pedagogy by the decided predicate
        measure = next(m for m in archmodel.MEASURES if m["id"] == "pedagogy")
        requirement = next(r for r in archmodel.REQUIREMENTS if r["id"] == measure["requirement"])
        sub = next(x for x in archmodel.SUBCHARACTERISTICS if x["id"] == requirement["subcharacteristic"])
        self.assertEqual((sub["id"], sub["characteristic"], measure["threshold"], measure["command"]), ("learnability", "interaction-capability", 0, "verify"))
        for name in ("journeysCoverPolesInOrder", "journeysEndInVerification", "stepEvidenceDeclared"):
            self.assertIn(name, measure["statement"])

    def test_step_problems_name_each_fault(self):
        from tools.r30 import presentationmodel as pm
        good = [s for s in pm.STEPS if s["journey"] == "reading"]
        journeys = [j for j in pm.JOURNEYS if j["id"] == "reading"]
        claims = [c["id"] for c in frontier.list_claims()]
        self.assertEqual(pm.step_problems(claims, steps=good, journeys=journeys), [])
        import copy
        swapped = copy.deepcopy(good)
        swapped[1]["pole"], swapped[2]["pole"] = swapped[2]["pole"], swapped[1]["pole"]
        self.assertIn("journey reading: poles are out of order", pm.step_problems(claims, steps=swapped, journeys=journeys))
        unlinked = copy.deepcopy(good)
        unlinked[0]["next"] = "elsewhere"
        self.assertIn("journey reading: steps are not linked by next", pm.step_problems(claims, steps=unlinked, journeys=journeys))
        gap = copy.deepcopy(good)
        gap[2]["order"] = 7
        self.assertIn(f"journey reading: orders are not 1..{len(good)}", pm.step_problems(claims, steps=gap, journeys=journeys))
        # without its verification steps (the standards and the reproduction)
        truncated = [s for s in copy.deepcopy(good) if s["pole"] != "verification"]
        truncated[-1]["next"] = ""
        problems = pm.step_problems(claims, steps=truncated, journeys=journeys)
        self.assertIn("journey reading: poles not covered: verification", problems)
        self.assertIn("journey reading: the last step is not the verification step", problems)
        self.assertIn("journey reading: its panels are not its steps' panels", problems)
        unbacked = copy.deepcopy(good)
        unbacked[0]["evidence"] = ["ghost-claim"]; unbacked[0]["paragraphs"] = ["ghost-paragraph"]; unbacked[0]["panel"] = "ghost-panel"
        problems = pm.step_problems(claims, steps=unbacked, journeys=journeys)
        for needle in ("step rd-tree: evidence ghost-claim is neither a claim nor an artifact", "step rd-tree: paragraph ghost-paragraph is not declared",
                       "step rd-tree: panel ghost-panel is not a panel"):
            self.assertIn(needle, problems)

    def test_layperson_journey_reads_as_a_lesson(self):
        """The first-visit journey presupposes no formal vocabulary before the
        step that introduces it: nothing before the kernel-checked step names
        Lean, LexLean, the kernel, a theorem or a lexeme; the whole lesson is
        free of the formal tokens the explainer refuses; every explainer
        paragraph belongs to a step; the picture comes first and its paragraph
        states the number of rows shown."""
        from tools.r30 import presentationmodel as pm, site
        paragraphs = {e["id"]: e for e in pm.EXPLAINER}
        steps = [s for s in pm.STEPS if s["journey"] == "first-visit"]
        texts = lambda s: [s["title"], s["goal"], s["text"]] + [paragraphs[q]["title"] + " " + paragraphs[q]["text"] for q in s["paragraphs"]]
        introduces = next(i for i, s in enumerate(steps) if "kernel-checked" in s["paragraphs"])
        self.assertLess(introduces, next(i for i, s in enumerate(steps) if s["panel"] == "reduction-tree"))
        self.assertLess(introduces, next(i for i, s in enumerate(steps) if any(e in {c["id"] for c in frontier.list_claims() if c["status"] == "proved"} for e in s["evidence"])))
        for s in steps[:introduces]:
            for text in texts(s):
                for token in self.JARGON:
                    self.assertNotIn(token, text, f"{s['id']} presupposes {token}")
        for s in steps:
            for text in texts(s):
                for jargon in ("LexLean", "lexeme", "propext", "Quot.sound", "bxor", "twopow", "2-kernel", "automatic"):
                    self.assertNotIn(jargon, text, f"{s['id']} uses {jargon}")
        self.assertEqual(steps[0]["panel"], "picture")
        self.assertEqual({q for s in steps for q in s["paragraphs"]}, set(paragraphs))
        self.assertIn(f"first {site.PICTURE_ROWS} rows", paragraphs["the-picture"]["text"])
        self.assertIn(f"rows 0 to {site.PICTURE_ROWS - 1}", paragraphs["the-picture"]["text"])
        withdrawn = next(s for s in steps if s["pole"] == "withdrawn")
        self.assertEqual(withdrawn["panel"], "obligation")
        self.assertIn("It is open", paragraphs[withdrawn["paragraphs"][0]]["text"])
        self.assertIn("never reproduces the ruler", paragraphs[withdrawn["paragraphs"][0]]["text"])

    def test_mathematician_journey_introduces_claims_in_dependency_order(self):
        """Each claim the mathematician's steps cite comes after (or with) the
        proved claims it rests on, when the journey cites them (an open claim
        is withdrawn and read in full at the withdrawn pole, after the proved
        facts about it); the vocabulary comes first, from the paper's Notions
        section."""
        from tools.r30 import presentationmodel as pm, site
        claims = {c["id"]: c for c in frontier.list_claims()}
        steps = [s for s in pm.STEPS if s["journey"] == "mathematics"]
        first = {}
        for i, s in enumerate(steps):
            for e in s["evidence"]:
                if e in claims:
                    first.setdefault(e, i)
        self.assertGreaterEqual(len(first), 30)
        for cid, i in first.items():
            for d in claims[cid].get("depends", []):
                if d in first and claims[d]["status"] == "proved":
                    self.assertLessEqual(first[d], i, f"{cid} is introduced before {d}")
        self.assertEqual(first[pm.OBLIGATION], next(i for i, s in enumerate(steps) if s["pole"] == "withdrawn"))
        self.assertEqual(steps[0]["panel"], "paper")
        self.assertIn("statements", steps[0]["evidence"])
        self.assertIn("Notions", steps[0]["text"])
        self.assertEqual(site.statements()["sections"][0]["id"], "notions")
        self.assertEqual({e for s in steps for e in s["evidence"] if e in claims and claims[e]["status"] == "refuted"},
                         {i for i, c in claims.items() if c["status"] == "refuted"})
        withdrawn = [s for s in steps if s["pole"] == "withdrawn"]
        self.assertIn(pm.OBLIGATION, withdrawn[0]["evidence"])
        self.assertIn(claims[pm.OBLIGATION]["lean"].split(".")[-1], withdrawn[0]["goal"])

    def test_site_renders_one_step_at_a_time_with_deep_links(self):
        import json
        from tools.r30 import site, presentationmodel as pm
        html = site.TEMPLATE.read_text()
        for needle in ('id="vantages"', 'id="stepbar"', 'id="switch"', "Switch vantage", 'id="progress"', 'id="step-title"', 'id="panel-body"',
                       'id="detail-slot"', 'id="evidence"', 'id="nav-stepper"', 'window.addEventListener("hashchange"', 'rel="next"', 'rel="prev"',
                       'return "#" + encodeURIComponent(s.journey) + "/" + encodeURIComponent(s.id);', '"Step " + (n + 1) + " of " + total',
                       'String(list[i].order) === ref', 'data-journey='):
            self.assertIn(needle, html)
        # every panel of the model has a renderer in the page; a visualization
        # panel (viz-*) is drawn by window.r30viz[panelId] instead
        for panel in pm.PANELS:
            if not panel["id"].startswith("viz-"):
                self.assertIn(f'"{panel["id"]}": function', html, panel["id"])
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "view"
            site.render_view(out)
            rendered = (out / "index.html").read_text()
            start = rendered.index(site.DATA_OPEN) + len(site.DATA_OPEN)
            data = json.loads(rendered[start:rendered.index(site.DATA_CLOSE, start)].replace("<\\/", "</"))
        self.assertEqual(data["steps"], pm.STEPS)
        self.assertEqual(data["poles"], pm.POLES)
        self.assertEqual(data["verifications"], pm.VERIFICATIONS)
        self.assertEqual(data["pictureRows"], site.PICTURE_ROWS)
        self.assertIn(f'<title id="pt">Rule 30, rows 0 to {site.PICTURE_ROWS - 1}</title>', data["picture"])


class NavigationTests(unittest.TestCase):
    """The central navigation is an implementation of the WAI-ARIA Authoring
    Practices, modeled in Presentation.lex.tex (Pattern, Navigation, NavItem),
    decided by the kernel, mirrored by `nav_problems`, and rendered by the
    site: the disclosure navigation menu, the breadcrumb, the stepper and the
    register search as a combobox, with the landmarks of the HTML standard and
    the WCAG 2.2 criteria the template is checked for."""

    CHROME = Path.home() / ".cache/ms-playwright/chromium_headless_shell-1234/chrome-headless-shell-linux64/chrome-headless-shell"

    def test_navigation_is_modeled_and_the_theorems_are_stated(self):
        from tools.r30 import presentationmodel as pm
        self.assertEqual(pm.nav_problems(), [])
        self.assertEqual([x["id"] for x in pm.NAVIGATIONS], ["nav-primary", "nav-breadcrumb", "nav-stepper"])
        patterns = {x["id"]: x for x in pm.NAV_PATTERNS}
        self.assertEqual(set(patterns), {"disclosure-navigation-menu", "breadcrumb", "stepper", "combobox"})
        for x in pm.NAV_PATTERNS:
            self.assertTrue(x["authority"].startswith("https://www.w3.org/WAI/ARIA/apg/"), x["id"])
        top = [x for x in pm.NAV_ITEMS if x["navigation"] == "nav-primary" and x["parent"] == ""]
        self.assertEqual([x["label"] for x in top], ["Vantages", "Register", "Modules", "Verify", "Standards"])
        journeys = {j["id"] for j in pm.JOURNEYS}
        self.assertEqual({x["target"] for x in pm.NAV_ITEMS if x["navigation"] == "nav-primary" and x["kind"] == "journey"}, journeys)
        self.assertEqual({x["target"] for x in pm.NAV_ITEMS if x["navigation"] == "nav-stepper"}, journeys)
        last = {[s for s in pm.STEPS if s["journey"] == j][-1]["id"] for j in journeys}
        self.assertEqual({x["target"] for x in pm.NAV_ITEMS if x["parent"] == "nav-verify"}, last)
        self.assertEqual([x["kind"] for x in pm.NAV_ITEMS if x["navigation"] == "nav-breadcrumb"], ["journey", "pole", "step"])
        search = next(x for x in pm.NAV_ITEMS if x["id"] == "nav-search")
        self.assertEqual((search["pattern"], next(s["panel"] for s in pm.STEPS if s["id"] == search["target"])), ("combobox", "register"))
        self.assertIn("rd-map", {x["target"] for x in pm.NAV_ITEMS if x["parent"] == "nav-vantages"})
        self.assertEqual(next(s["panel"] for s in pm.STEPS if s["id"] == "rd-map"), "sitemap")
        text = pm.render_presentation()
        for name in ("Pattern", "Navigation", "NavItem", "navPatterns", "navigations", "navItems", "navIdsDistinct", "navigationsNamePatterns",
                     "navItemsNamePatterns", "navItemsInNavigations", "navItemParentsAreItems", "everyJourneyInPrimaryNavigation",
                     "stepperListsEveryJourney", "navJourneyTargetsAreJourneys", "navStepTargetsAreSteps", "navArtifactTargetsAreArtifacts",
                     "breadcrumbIsVantagePoleStep", "everyBreadcrumbResolves", "verifyReachableFromEveryJourney", "searchOpensTheRegister",
                     "navGroupsOrdered", "navTopLevelOrdered"):
            self.assertIn(f"name: {name},", text)
        self.assertIn('(cons "journey" (cons "pole" (cons "step" (nil String))))', text)
        self.assertIn('(navTargets "journey" "nav-primary" (navItems))', text)

    def test_nav_problems_name_each_fault(self):
        from tools.r30 import presentationmodel as pm
        items = [dict(x) for x in pm.NAV_ITEMS]
        bad = next(x for x in items if x["id"] == "nav-vantage-reading")
        bad["target"] = "nowhere"
        problems = pm.nav_problems(items=items)
        self.assertIn("item nav-vantage-reading: journey nowhere is not a journey", problems)
        self.assertIn("journey reading: not reachable from nav-primary", problems)
        items = [dict(x) for x in pm.NAV_ITEMS]
        next(x for x in items if x["id"] == "nav-search")["pattern"] = "menubar"
        self.assertIn("item nav-search: pattern menubar is not declared", pm.nav_problems(items=items))
        items = [x for x in pm.NAV_ITEMS if x["id"] != "nav-crumb-pole"]
        self.assertIn("nav-breadcrumb: the trail is not vantage > pole > step", pm.nav_problems(items=items))
        items = [dict(x) for x in pm.NAV_ITEMS]
        next(x for x in items if x["id"] == "nav-verify-mathematics")["target"] = "ma-tree"
        self.assertIn("journey mathematics: its verification step is not a target of nav-primary", pm.nav_problems(items=items))
        items = [dict(x) for x in pm.NAV_ITEMS]
        next(x for x in items if x["id"] == "nav-register-json")["order"] = 9
        self.assertTrue(any(p.startswith("nav-primary: the orders under nav-register are not") for p in pm.nav_problems(items=items)))
        from tools.r30 import site
        self.assertEqual(site.check_journeys(), [])

    def test_template_realizes_the_apg_patterns(self):
        from tools.r30 import site
        html = site.TEMPLATE.read_text()
        # the disclosure navigation menu: a nav landmark, buttons with aria-expanded and aria-controls over hidden lists, Escape and the arrow keys
        for needle in ('<nav id="nav-primary" class="primary" aria-label="Site">', '<ul id="nav-primary-list" class="menubar">',
                       'aria-expanded="false" aria-controls="menu-', 'class="submenu" hidden>',
                       'if (k === "Escape")', 'k === "ArrowRight"', 'k === "ArrowLeft"', 'k === "ArrowDown"', 'k === "ArrowUp"', 'k === "Home"', 'k === "End"',
                       'function closeAll(except)', 'primary.addEventListener("focusout"', 'setOpen(owner, false); owner.focus();'):
            self.assertIn(needle, html, needle)
        # the breadcrumb: a labeled nav, an ordered list, the current step aria-current="page"
        for needle in ('<nav id="nav-breadcrumb" class="breadcrumb" aria-label="Breadcrumb"><ol id="crumb"></ol></nav>', '" aria-current="page"><span class="k">'):
            self.assertIn(needle, html, needle)
        # the stepper: a labeled nav landmark, the step list, aria-current="step", a disclosure of the titles
        for needle in ('<nav class="stepnav" id="nav-stepper" aria-label="Steps of this vantage"></nav>', '<ol id="stepper-list" class="progress',
                       'aria-current="step"', 'id="stepper-toggle" aria-expanded="', 'aria-controls="stepper-list"', 'rel="prev"', 'rel="next"'):
            self.assertIn(needle, html, needle)
        # the register search: an editable combobox with a listbox popup and a live region, reachable from the primary navigation
        for needle in ('role="combobox" aria-expanded="false" aria-controls="nav-q-list" aria-autocomplete="list" aria-haspopup="listbox"',
                       'role="listbox" aria-label="Matching claims"', 'role="option" aria-selected=', 'aria-activedescendant', '<label for="nav-q">',
                       'id="nav-q-status" class="live" role="status" aria-live="polite"'):
            self.assertIn(needle, html, needle)
        # landmarks of the HTML standard, one h1, the where-am-I, the site map, the visualization slot, consistent help
        for needle in ('<header class="top">', '<main id="main"', '<aside class="evidence" id="evidence" aria-labelledby="evidence-title">', "<footer>",
                       'id="whereami"', '"sitemap": function', '<div id="viz-slot" hidden></div>', 'window.r30viz', 'indexOf("viz-") === 0',
                       'min-width: 24px; min-height: 24px', 'min-width: 320px', "@media (prefers-reduced-motion: reduce)", 'parts[2] && byId[parts[2]]'):
            self.assertIn(needle, html, needle)
        self.assertEqual(html.count("<h1>"), 1)
        self.assertEqual(html.count("<h1"), 1)
        # the inline script parses (node --check) when node is available
        script = html[html.rindex("<script>") + len("<script>"):html.rindex("</script>")]
        if shutil.which("node"):
            with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
                f.write(script)
            try:
                r = subprocess.run(["node", "--check", f.name], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
            finally:
                Path(f.name).unlink()

    def test_rendered_dom_has_the_apg_structure(self):
        """With the cached headless chromium: at a deep link the page carries
        five closed disclosures with aria-controls over hidden lists, one
        combobox, a three-link breadcrumb ending in aria-current=page, one
        current step, no duplicate id, one h1 and no heading that skips a
        level; the home page hides the stepbar."""
        if not self.CHROME.exists():
            self.skipTest("no headless chromium")
        import re
        from html.parser import HTMLParser
        from tools.r30 import site

        class Tags(HTMLParser):
            def __init__(self):
                super().__init__(); self.rows = []; self.stack = []
            def handle_starttag(self, tag, attrs):
                a = dict(attrs); self.rows.append((tag, a, list(self.stack)))
                if tag not in ("br", "img", "meta", "link", "input", "hr"):
                    self.stack.append((tag, a.get("id")))
            def handle_endtag(self, tag):
                for i in range(len(self.stack) - 1, -1, -1):
                    if self.stack[i][0] == tag:
                        del self.stack[i:]; break

        def dump(view, h):
            r = subprocess.run([str(self.CHROME), "--headless", "--disable-gpu", "--no-sandbox", "--virtual-time-budget=3000", "--dump-dom",
                                f"file://{view}/index.html{h}"], capture_output=True, text=True, timeout=120)
            p = Tags(); p.feed(re.sub(r"<script.*?</script>", "", r.stdout, flags=re.S)); return p.rows

        with tempfile.TemporaryDirectory() as tmp:
            view = Path(tmp) / "view"
            site.render_view(view)
            for h, on_step in (("#mathematics/ma-tree", True), ("", False)):
                rows = dump(view, h)
                if not rows:
                    self.skipTest("headless chromium produced no DOM")
                ids = [a["id"] for _, a, _ in rows if "id" in a]
                self.assertEqual(len(ids), len(set(ids)), h)
                self.assertEqual(sum(1 for t, _, _ in rows if t == "h1"), 1, h)
                hidden = {a.get("id") for _, a, _ in rows if "hidden" in a and a.get("id")}
                levels = [int(t[1]) for t, a, anc in rows if re.fullmatch(r"h[1-6]", t) and "hidden" not in a and not any(i in hidden for _, i in anc)]
                self.assertTrue(all(n <= p + 1 for p, n in zip(levels, levels[1:])), (h, levels))
                btns = [a for t, a, anc in rows if t == "button" and "aria-controls" in a and any(i == "nav-primary" for _, i in anc)]
                menus = {a["id"]: a for t, a, _ in rows if t == "ul" and a.get("class") == "submenu"}
                self.assertEqual(len(btns), 5, h)
                for b in btns:
                    self.assertEqual(b["aria-expanded"], "false"); self.assertIn("hidden", menus[b["aria-controls"]])
                self.assertEqual(sum(1 for t, a, _ in rows if t == "input" and a.get("role") == "combobox"), 1, h)
                self.assertEqual(len([a for t, a, anc in rows if t == "a" and any(i == "menu-nav-verify" for _, i in anc)]), 6, h)
                stepbar = next(a for _, a, _ in rows if a.get("id") == "stepbar")
                if on_step:
                    self.assertNotIn("hidden", stepbar)
                    crumbs = [a for t, a, anc in rows if t == "a" and any(i == "nav-breadcrumb" for _, i in anc)]
                    self.assertEqual((len(crumbs), crumbs[-1].get("aria-current")), (3, "page"))
                    steps = [a for t, a, anc in rows if t == "a" and any(i == "stepper-list" for _, i in anc)]
                    self.assertEqual(sum(1 for a in steps if a.get("aria-current") == "step"), 1)
                else:
                    self.assertIn("hidden", stepbar)


class DesignTests(unittest.TestCase):
    """The design system and the experience: tokens with decided WCAG 2.2
    contrast (integer arithmetic over relative luminance), the scales and
    motion, the landing, the standards, model and design panels, the evidence
    cards, the loader contract of the visualizations and deep links,
    modeled in Presentation.lex.tex and rendered by the site."""

    CHROME = Path.home() / ".cache/ms-playwright/chromium_headless_shell-1234/chrome-headless-shell-linux64/chrome-headless-shell"

    def test_design_model_is_decided_and_its_problems_named(self):
        from tools.r30 import designmodel as dm, presentationmodel as pm
        self.assertEqual(dm.problems(pm.JOURNEYS, pm.OBLIGATION), [])
        text = pm.render_presentation()
        for name in ("Token", "ContrastPair", "TypeStep", "SpaceStep", "Motion", "Landing", "srgbLinear", "tokens", "contrastPairs",
                     "typeScale", "spacing", "motion", "landing", "luminance", "meetsContrast") + tuple(dm.THEOREMS):
            self.assertIn(f"name: {name},", text, name)
        self.assertIn("(prim multiply", text)
        # the kernel's integer luminance is WCAG's, to the table's rounding
        for t in dm.TOKENS:
            for mode in ("light", "dark"):
                self.assertAlmostEqual(dm.luminance(t[mode]) / 1e10, AccessibilityTests.luminance(t[mode]), places=5)
                self.assertIn(f"{mode}Luminance := {dm.luminance(t[mode])}", text)
        self.assertEqual(len(dm.SRGB_LINEAR), 256)
        self.assertEqual((dm.SRGB_LINEAR[0], dm.SRGB_LINEAR[255]), (0, 1000000))
        # a failing pair, a bad minimum, a stray text token and slow motion are each named
        old = [dict(x) for x in dm.TOKENS], [dict(x) for x in dm.PAIRS], [dict(x) for x in dm.MOTION]
        def restore():
            dm.TOKENS[:], dm.PAIRS[:], dm.MOTION[:] = old
        self.addCleanup(restore)
        next(x for x in dm.TOKENS if x["id"] == "muted")["light"] = "#b0b0b0"
        dm.PAIRS[0]["minimum"] = 40
        dm.TOKENS.append({"id": "ghost", "role": "text", "light": "#000000", "dark": "#ffffff", "statement": ""})
        dm.MOTION[0]["reduced"] = 100
        problems = dm.problems(pm.JOURNEYS, pm.OBLIGATION)
        self.assertTrue(any(p.startswith("pair muted on bg (light)") for p in problems), problems)
        self.assertIn("pair ink on bg: minimum 40 is not WCAG's for text", problems)
        self.assertIn("token ghost: a text colour on no declared background", problems)
        self.assertIn("motion quick: the reduced duration is not 0", problems)

    def test_tokens_are_generated_into_the_template_and_published(self):
        from tools.r30 import designmodel as dm, site
        html = site.TEMPLATE.read_text()
        self.assertIn(site.TOKENS_OPEN + dm.css() + site.TOKENS_CLOSE, html)
        self.assertTrue(site.check_logo()["ok"])
        self.assertNotEqual(site.with_tokens(html, "/* drifted */\n"), html)
        css = dm.css()
        for needle in ("--ink: #16181d;", "@media (prefers-color-scheme: dark)", ':root[data-theme="dark"]',
                       "@media (prefers-reduced-motion: reduce) { :root { --motion-quick: 0ms;", "--space-target: 24px;", "--text-base: 1rem;"):
            self.assertIn(needle, css)
        # the stylesheet reads colours only through the tokens: no literal hex outside the generated block
        import re
        body = html[html.index(site.TOKENS_CLOSE):]
        style = body[:body.index("</style>", len(site.TOKENS_CLOSE))]
        self.assertEqual(re.findall(r"#[0-9a-fA-F]{6}\b", style), [])

    def test_template_realizes_the_experience_and_the_loader_contract(self):
        from tools.r30 import site, presentationmodel as pm
        html = site.TEMPLATE.read_text()
        for needle in (
                # the landing: the question, what is proved, what is open, the triangle drawn row by row, the vantages
                'id="hero-q"', 'id="hero-proved"', 'id="hero-open"', 'id="hero-triangle"', "function rule30Rows(count)", "animation-delay: calc(var(--motion-reveal) * var(--t))",
                'id="replay"', 'data-journey=',
                # the step: a transition on the motion token, a progress line, evidence as APG disclosures with the theorem in place
                "#step.entering { animation: stepin var(--motion-step)", 'id="progressline"', 'class="ev-toggle" aria-expanded="false" aria-controls="',
                "<dt>Lean name</dt>", "<dt>lexeme</dt>", "κ-label", 'role="status" aria-live="polite"',
                # consistent help in the banner, the site map and the standards in the footer
                'id="help"', 'id="foot-links"', 'id="foot-standards"',
                # the panels of the experience
                '"standards": function', '"model": function', '"design": function', 'role="graphics-document document"', 'role="graphics-symbol img"',
                'data-model-pick=', 'data-std-filter=',
                # the loader contract: window.r30viz[panelId](slot, viewData), a graceful placeholder otherwise
                '<script id="r30-viz"></script>', 'window.r30viz = window.r30viz || {};', 'draw(viz, viewFor(step))', 'vizPlaceholder(viz, step, "")',
                'class="viz-missing" data-missing="'):
            self.assertIn(needle, html, needle)
        self.assertLess(html.index('<script id="r30-viz">'), html.rindex("<script>"))
        # the inlining: viz/*.js land in the hook, a closing script tag cannot escape it
        inlined = site.with_viz(html, "window.r30viz['viz-x'] = function (slot, v) { slot.textContent = '<\\/script>'; };")
        self.assertIn("window.r30viz['viz-x']", inlined)
        self.assertEqual(site.with_viz("<p>no hook</p>", "x"), "<p>no hook</p>")
        # the steps the experience adds are reachable from the pedagogy and the navigation
        steps = {s["id"]: s for s in pm.STEPS}
        self.assertEqual((steps["rd-standards"]["panel"], steps["sf-model"]["panel"], steps["sf-design"]["panel"]), ("standards", "model", "design"))
        targets = {x["target"] for x in pm.NAV_ITEMS if x["navigation"] == "nav-primary"}
        self.assertTrue({"rd-standards", "sf-model", "sf-design"} <= targets)

    def test_rendered_pages_at_deep_links(self):
        """With the cached headless chromium: the landing, a step with its
        evidence cards, the standards, the model with a vantage selected by
        the deep link, the design system, and a visualization panel through
        the loader contract (a registered function and a missing one)."""
        if not self.CHROME.exists():
            self.skipTest("no headless chromium")
        import re
        from tools.r30 import site, standardsmodel, presentationmodel as pm

        def dump(view, h):
            r = subprocess.run([str(self.CHROME), "--headless", "--disable-gpu", "--no-sandbox", "--virtual-time-budget=3000", "--dump-dom",
                                f"file://{view}/index.html{h}"], capture_output=True, text=True, timeout=120)
            return re.sub(r"<script.*?</script>", "", r.stdout, flags=re.S)

        with tempfile.TemporaryDirectory() as tmp:
            view = Path(tmp) / "view"
            site.render_view(view)
            home = dump(view, "")
            if "<body" not in home:
                self.skipTest("headless chromium produced no DOM (run without a ulimit)")
            self.assertEqual(home.count('class="vantage"'), len(pm.JOURNEYS))
            self.assertIn('aria-labelledby="hero-t hero-d"', home)
            self.assertIn("aperiodic-compensation", home)
            step = dump(view, "#mathematics/ma-edges")
            ev = [s for s in pm.STEPS if s["id"] == "ma-edges"][0]["evidence"]
            self.assertEqual(step.count('class="ev-toggle"'), len(ev))
            self.assertIn('aria-current="page"', step)
            std = dump(view, "#reading/rd-standards")
            self.assertEqual(std.count('<div class="card" id="std-'), len(standardsmodel.rows()))
            model = dump(view, "#stdlib-feedback/sf-model/mathematics")
            self.assertIn('data-model-pick="mathematics" aria-pressed="true"', model)
            self.assertIn("<h4>Real qualities</h4>", model)
            design = dump(view, "#stdlib-feedback/sf-design")
            from tools.r30 import designmodel as dm
            self.assertEqual(design.count("4.5:1 ✓") + design.count("3.0:1 ✓"), len(dm.PAIRS))
            # the loader contract, exercised with a stand-in visualization on a step that shows a viz-* panel
            html = (view / "index.html").read_text()
            start = html.index(site.DATA_OPEN) + len(site.DATA_OPEN)
            import json
            data = json.loads(html[start:html.index(site.DATA_CLOSE, start)].replace("<\\/", "</"))
            data["panels"].append({"id": "viz-probe", "title": "Probe", "viewpoint": "plain", "artifact": "picture", "statement": "A probe."})
            data["steps"][0]["panel"] = "viz-probe"
            first = data["steps"][0]
            probe = "window.r30viz['viz-probe'] = function (slot, v) { slot.innerHTML = '<p id=\"probe\">' + v.step.id + ' ' + v.register.length + '</p>'; };"
            (view / "probe.html").write_text(site.with_viz(site.embed(html, data), probe))
            (view / "missing.html").write_text(site.with_viz(site.embed(html, data), ""))
            for name, needle in (("probe", f'<p id="probe">{first["id"]} {len(data["register"])}</p>'), ("missing", 'class="viz-missing" data-missing="viz-probe"')):
                r = subprocess.run([str(self.CHROME), "--headless", "--disable-gpu", "--no-sandbox", "--virtual-time-budget=3000", "--dump-dom",
                                    f"file://{view}/{name}.html#{first['journey']}/{first['id']}"], capture_output=True, text=True, timeout=120)
                self.assertIn(needle, r.stdout, name)



class VisualizationTests(unittest.TestCase):
    """The visualizations (tools/r30/vizmodel.py): panels with the claims
    they render, decided in Presentation.lex.tex, read by the Observer,
    reachable as steps at the sensual-quality pole, published by `view
    render`, computed in plain JavaScript that passes `node --check` and
    reproduces the identities the panels check."""

    VIZ = ["viz-triangle", "viz-tower", "viz-ledger", "viz-rays", "viz-defects", "viz-dyadic"]

    def test_viz_panels_are_modeled_with_the_claims_they_render(self):
        from tools.r30 import presentationmodel as pm, observermodel as om, standardsmodel, vizmodel
        claims = {c["id"]: c for c in frontier.list_claims()}
        proved = {i for i, c in claims.items() if c["status"] == "proved"}
        self.assertEqual([p["id"] for p in vizmodel.VIZ_PANELS], self.VIZ)
        self.assertEqual(self.VIZ, standardsmodel.VISUALIZATIONS)
        self.assertEqual(vizmodel.problems(), [])
        panels = {p["id"]: p for p in pm.PANELS}
        for p in vizmodel.VIZ_PANELS:
            self.assertIs(panels[p["id"]], p)
            self.assertTrue(p["renders"], p["id"])
            self.assertTrue(set(p["renders"]) <= proved, p["id"])
            # the generated row is the declared row less what the register does not hold yet
            self.assertEqual(p["renders"], [i for i in vizmodel.declared(p["id"]) if i in claims])
            script = next(a for a in pm.ARTIFACTS if a["id"] == p["artifact"])
            self.assertEqual(script["media"], "application/javascript")
            self.assertTrue(script["path"].startswith("viz/") and script["source"].startswith("rule30-api/site/viz/"))
            self.assertTrue((ROOT / script["source"]).exists(), script["source"])
            self.assertEqual(om.rendered(p, list(claims.values())), [i for i in claims if i in set(p["renders"]) and i in proved])
        self.assertEqual(vizmodel.declared("viz-tower"), ["antidiagonal", "diagonal-halving", "mask-transport", "lucas-frame"])
        self.assertEqual(vizmodel.declared("viz-triangle"), ["antidiagonal", "diagonal-halving", "edge-parity"])
        self.assertEqual(vizmodel.declared("viz-ledger"), ["left-band", "three-diagonal-band", "edge-parity"])
        self.assertEqual(vizmodel.declared("viz-rays"), ["kernel-law", "residue-dichotomy", "second-table"])
        self.assertEqual(vizmodel.declared("viz-defects"), ["coupling-law", "left-defect-sourcing", "recurrent-central-collision"])
        self.assertEqual(vizmodel.declared("viz-dyadic"), ["scale-free-rows", "dyadic-response-reduction"])
        self.assertEqual([a["path"] for a in vizmodel.VIZ_ARTIFACTS][0], "viz/core.js")
        # the Python decision names a bad row before the kernel does
        import copy
        bad = copy.deepcopy(vizmodel.VIZ_PANELS)
        bad[1]["renders"] = []
        bad[3]["renders"] = ["ghost-claim", pm.OBLIGATION]
        saved = vizmodel.VIZ_PANELS[:]
        try:
            vizmodel.VIZ_PANELS[:] = bad
            problems = vizmodel.problems(panels=pm.PANELS + bad)
        finally:
            vizmodel.VIZ_PANELS[:] = saved
        self.assertIn("viz panel viz-tower renders no claim", problems)
        self.assertIn("viz panel viz-rays renders ghost-claim, which is not a claim", problems)
        self.assertIn(f"viz panel viz-rays renders {pm.OBLIGATION}, which is open, not proved", problems)
        # the theorems, stated in Presentation
        text = pm.render_presentation()
        for name in ("VizPanel", "vizPanels", "vizRenders", "vizEachRenders", "vizAllProved", "vizPanelsArePanels", "vizPanelsAreSteps",
                     "vizScriptsArePublished", "vizPanelsRender", "vizRendersAreClaims", "vizRendersAreProved"):
            self.assertIn(f"name: {name},", text)
        self.assertIn("(allMembers (vizRenders (vizPanels)) (Register::idsOf (Register::claims)))", text)
        self.assertEqual((ROOT / "rule30-api/src/Presentation.lex.tex").read_text(), text)

    def test_viz_steps_are_at_the_sensual_quality_pole_and_the_observer_reads_them(self):
        from tools.r30 import presentationmodel as pm, observermodel as om, vizmodel
        steps = [s for s in pm.STEPS if s["panel"] in self.VIZ]
        self.assertEqual({s["panel"] for s in steps}, set(self.VIZ))
        panels = {p["id"]: p for p in pm.PANELS}
        for s in steps:
            self.assertEqual(s["pole"], "sensual-quality", s["id"])
            # the mathematician meets a visualization before its claims are introduced (that journey reads
            # claims in dependency order), so there it cites the script and links the claims through `renders`
            expected = [panels[s["panel"]]["artifact"]] + ([] if s["journey"] == "mathematics" else panels[s["panel"]]["renders"])
            self.assertEqual(s["evidence"], expected, s["id"])
        self.assertEqual({s["journey"] for s in steps}, {"first-visit", "mathematics", "reading", "prize-review"})
        self.assertEqual([s["panel"] for s in steps if s["journey"] == "mathematics"], ["viz-tower", "viz-ledger", "viz-defects", "viz-rays", "viz-dyadic"])
        # an anchor that a journey no longer has: the step goes after the last early-pole step
        moved = vizmodel.with_viz_steps({"reading": [{"id": "x", "pole": "sensual-object"}, {"id": "y", "pole": "real-quality"}]})
        self.assertEqual([s["id"] for s in moved["reading"]], ["x", "rd-triangle", "rd-tower", "y"])
        quadruples = {q["sensualObject"]: q for q in om.data()["quadruples"]}
        for s in steps:
            q = quadruples[s["journey"]]
            self.assertIn(s["panel"], q["sensualQualities"])
            self.assertTrue(set(panels[s["panel"]]["renders"]) <= set(q["realQualities"]), s["id"])

    def test_the_rendered_view_publishes_the_scripts_and_lists_them(self):
        import json
        from tools.r30 import site, presentationmodel as pm, vizmodel
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "view"
            site.render_view(out)
            for a in vizmodel.VIZ_ARTIFACTS:
                self.assertEqual((out / a["path"]).read_text(), (ROOT / a["source"]).read_text(), a["path"])
            html = (out / "index.html").read_text()
            start = html.index(site.DATA_OPEN) + len(site.DATA_OPEN)
            data = json.loads(html[start:html.index(site.DATA_CLOSE, start)].replace("<\\/", "</"))
        listed = [a["path"] for a in data["artifacts"] if a["media"] == "application/javascript"]
        self.assertEqual(listed, [a["path"] for a in vizmodel.VIZ_ARTIFACTS])
        self.assertTrue({p["id"] for p in data["panels"]} >= set(self.VIZ))

    def test_viz_scripts_are_plain_accessible_and_pass_node_check(self):
        import shutil
        import subprocess
        from tools.r30 import vizmodel
        scripts = [ROOT / a["source"] for a in vizmodel.VIZ_ARTIFACTS]
        for path in scripts:
            text = path.read_text().replace("http://www.w3.org/2000/svg", "")  # the SVG namespace is not a dependency
            for forbidden in ("import(", "require(", "https://", "http://", "<script", "localStorage", "eval("):
                self.assertNotIn(forbidden, text, f"{path.name} uses {forbidden}")
            self.assertIn('"use strict"', text)
        core = (ROOT / "rule30-api/site/viz/core.js").read_text()
        for needle in ('role: "graphics-document"', '"aria-labelledby"', '"aria-describedby"', '"graphics-symbol"', 'matchMedia("(prefers-reduced-motion: reduce)")',
                       '"aria-pressed"', 'el("label"', "focus-visible", "<pattern>", "var(--ink,", "y ^ ((y << 1n) | (y << 2n))", "coreVectors", "the verified values win"):
            self.assertIn(needle, core)
        for path in scripts[1:]:
            text = path.read_text()
            panel = "viz-" + path.stem
            for needle in (f'window.r30viz["{panel}"] = function (slot, d)', "C.picture(", "C.checkNotice(d", '"aria-live": "polite"', "viz-summary", "C.frame(slot)", "C.legend("):
                self.assertIn(needle, text, f"{path.name} lacks {needle}")
        node = shutil.which("node")
        if not node:
            self.skipTest("node is not installed")
        for path in scripts:
            r = subprocess.run([node, "--check", str(path)], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, f"{path.name}: {r.stderr}")

    def test_viz_core_reproduces_the_rows_and_the_identities(self):
        import json
        import shutil
        import subprocess
        from tools.r30 import site
        node = shutil.which("node")
        if not node:
            self.skipTest("node is not installed")
        r = subprocess.run([node, str(ROOT / "scripts/tests/viz_check.js"), str(ROOT / "rule30-api/site/viz/core.js")],
                           capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr)
        out = json.loads(r.stdout)
        rows = site.rule30_rows(520)
        self.assertEqual(out["centers"], "".join(str(row[len(row) // 2]) for row in rows[:256]))
        # rdiag j s = cell s (s - j): the words at their drawn lengths 1, 2, 2^(j-1)
        for j, w in enumerate(out["words"]):
            length = 1 if j == 0 else 2 if j == 1 else 2 ** (j - 1)
            self.assertEqual(w, "".join(str(rows[s][2 * s - j]) if 2 * s >= j else "0" for s in range(length)), f"word {j}")
        self.assertEqual(out["periods"], [1, 2, 2, 4, 8, 8, 16, 32, 32, 64, 64, 64, 64])
        self.assertEqual(out["secondTable4"], "0001111001100000")
        self.assertEqual(out["secondTable5"], "00011111110010010110001101011010")
        self.assertTrue(out["frozenAgree"])
        for key in ("selfCheck", "badHalving", "badAntidiagonal", "badMask", "badLucas", "badExposed", "badEight", "badThree", "badRowTerm",
                    "badLaw", "badRuler", "badDyadic", "badDyadicRow", "badCoupling", "compareOk"):
            self.assertEqual(out[key], [], key)
        self.assertEqual(out["comparePlanted"], ["center 2"])


class CoreModelTests(unittest.TestCase):
    """Rule30Core.lex.tex is the automaton's computational core as executable
    definitions with decided theorems, generated by coremodel.py; its Python
    replica agrees with the known centers, with the main checkout's Lean
    definitions (cell, row, rdiag, towerWord, trailingParity, rulerBackground)
    and with the site's own rows; core-vectors.json is generated from the same
    model, cross-checked against the decided literals, and published by the
    view; the production roots are requested beside those of Api."""

    def test_core_module_is_current_and_states_the_decided_theorems(self):
        import tomllib
        from tools.r30 import coremodel
        r = coremodel.check()
        self.assertTrue(r["ok"], r["reason"])
        text = coremodel.MODULE.read_text()
        self.assertEqual(coremodel.theorem_names(text), [t["name"] for t in coremodel.THEOREMS])
        for name in ("rule", "walk", "step", "rows", "nth", "center", "rdiag", "rightRecursion", "twopow", "towerWord",
                     "timeParity", "trailingParityFuel", "trailingParity", "rulerBackground", "knownCenters", "knownRuler"):
            self.assertIn(f"name: {name},", text)
        for root in coremodel.PRODUCTION_ROOTS:
            self.assertIn(f"  name: {root},", text)
        self.assertEqual(text.count("production: {effects: [allocation, overflow, recursion], targets: [rust-std]}"),
                         len(coremodel.PRODUCTION_ROOTS))
        self.assertTrue(all("proof: decide{}" in block for block in text.split("theorem{")[1:]))
        self.assertEqual(coremodel.decided_literal("knownCenters", text), coremodel.KNOWN_CENTERS)
        project = tomllib.loads((repo.PROJECTS["api"] / "lexlean.toml").read_text())
        self.assertIn("src/Rule30Core.lex.tex", project["entrypoints"])

    def test_replica_agrees_with_the_lean_definitions_and_the_site_rows(self):
        from tools.r30 import coremodel, site
        r = coremodel.REPLICA
        self.assertEqual(r.centers(32), [1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0])
        self.assertEqual(r.centers(32), coremodel.KNOWN_CENTERS)

        # Core.lean: cell 0 p = (p = 0); cell (s+1) p = rule (cell s (p-1)) (cell s p) (cell s (p+1)),
        # rule a b c = a XOR (b OR c); center t = cell t 0
        def cell(t, p, memo={}):
            if (t, p) not in memo:
                memo[(t, p)] = int(p == 0) if t == 0 else cell(t - 1, p - 1) ^ (cell(t - 1, p) | cell(t - 1, p + 1))
            return memo[(t, p)]
        for t in range(40):
            self.assertEqual(r.rows(t), [cell(t, p) for p in range(-t, t + 1)], t)
        picture = site.rule30_rows(48)
        for t in range(48):
            self.assertEqual(r.rows(t), picture[t], t)
        # Core.lean rdiag (the right-edge recursion) is the cell at position t - j
        for t in range(12):
            for j in range(t + 3):
                self.assertEqual(r.right_recursion(j, t), r.rdiag(j, t), (j, t))
                if j <= 2 * t:
                    self.assertEqual(r.rdiag(j, t), cell(t, t - j), (j, t))
        self.assertTrue(all(r.rdiag(1, t) == r.time_parity(t) for t in range(64)))
        self.assertTrue(all(r.center(t) == r.tower_word(t, t) for t in range(64)))
        self.assertTrue(all(r.tower_word(k + 2, s + 1) == r.tower_word(k + 2, s) ^ (r.tower_word(k + 1, s) | r.tower_word(k, s))
                            for k in range(8) for s in range(256)))
        self.assertTrue(all(r.rdiag(j, t + 2 ** j) == r.rdiag(j, t) for j in range(8) for t in range(2 ** j)))
        self.assertTrue(all(r.rdiag(j, t + 2 ** (j - 1)) == r.rdiag(j, t) for j in range(2, 9) for t in range(2 ** j)))
        # Ledger.lean trailingParity: the parity of the trailing ones
        self.assertEqual([r.trailing_parity(t) for t in range(8)], [0, 1, 0, 0, 0, 1, 0, 1])
        self.assertEqual(r.ruler_background(5), r.trailing_parity(3) ^ 0 ^ r.trailing_parity(1) ^ r.trailing_parity(0))

    def test_vectors_are_generated_cross_checked_and_current(self):
        import json
        from tools.r30 import coremodel
        v = json.loads(coremodel.VECTORS.read_text())
        self.assertEqual(coremodel.VECTORS.read_text(), coremodel.vectors_json())
        self.assertEqual((v["spec"], len(v["centers"]), len(v["towerWords"]), len(v["rulerBackground"])),
                         ("r30/core-vectors/1", 256, 12, 512))
        self.assertEqual([len(w) for w in v["towerWords"]], [2 ** j for j in range(12)])
        self.assertEqual(v["centers"][:32], coremodel.KNOWN_CENTERS)
        self.assertEqual(v["theorems"], coremodel.THEOREMS)
        self.assertIsNone(v["browserTarget"])
        self.assertEqual(v["crossCheck"]["recheckedOnVectors"], [t["name"] for t in coremodel.THEOREMS])
        # a vector that contradicts a decided literal or identity is refused
        bad = dict(v, centers=[1 - v["centers"][0]] + v["centers"][1:])
        with self.assertRaises(ValueError):
            coremodel.cross_check(bad)
        words = [list(w) for w in v["towerWords"]]
        words[5][3] ^= 1
        with self.assertRaises(ValueError):
            coremodel.cross_check(dict(v, towerWords=words))

    def test_core_roots_are_requested_beside_the_api_roots_and_the_vectors_published(self):
        import json
        from tools.r30 import coremodel, production, presentationmodel as pm, site, standardsmodel
        roots = {r["root"]: r for r in production.roots()}
        for name in coremodel.PRODUCTION_ROOTS:
            self.assertEqual(roots[f"{coremodel.LEAN_MODULE}.{name}"]["effects"], ["allocation", "overflow", "recursion"])
        self.assertEqual(production.crate_name("rows", "core"), "rule30_api_core_rows")
        req = json.loads(production.REQUEST.read_text())
        self.assertIn(f"{coremodel.LEAN_MODULE}.center", [r["root"] for r in req["roots"]])
        self.assertIn("Rule30Core", standardsmodel.MODULES)
        artifacts = {a["id"]: a for a in pm.ARTIFACTS}
        self.assertEqual((artifacts["core-vectors"]["path"], artifacts["core-vectors"]["source"]),
                         ("core-vectors.json", str(coremodel.VECTORS.relative_to(repo.ROOT))))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "view"
            site.render_view(out)
            self.assertEqual((out / "core-vectors.json").read_text(), coremodel.VECTORS.read_text())




class DiscoveryTests(unittest.TestCase):
    """Induction mechanized (suite `discovery` of ids.toml): the basis of the
    map, the relation and recurrence engines of Discovery.lex.tex, their
    certified roots, `bin/r30 discover`, and the register's `observed`
    status. Each test ends in the id it exercises."""

    def setUp(self):
        from tools.r30 import sequencemodel
        self.data = sequencemodel.load()
        if self.data is None:
            self.skipTest("model/sequences.toml is absent (bin/r30 sequences --write)")

    def test_basis_is_declared_labelled_and_evaluated_discovery_basis(self):
        from tools.r30 import sequencemodel, coremodel
        self.assertEqual(sequencemodel.problems(self.data), [])
        self.assertTrue(sequencemodel.check()["ok"], sequencemodel.check()["reason"])
        rows = self.data["sequence"]
        self.assertEqual([r["id"] for r in rows], [e["id"] for e in sequencemodel.basis()])
        self.assertEqual(len(rows), 79)
        for r in rows:
            self.assertEqual(r["kappa"], sequencemodel.kappa(["sequence", r["lexeme"], *map(str, r["parameters"])]))
        self.assertEqual(len({r["kappa"] for r in rows}), len(rows))
        w = sequencemodel.windows(self.data)
        n = self.data["window"]
        self.assertEqual(w["center"][:32], coremodel.KNOWN_CENTERS)
        self.assertEqual(w["time-parity"], [t % 2 for t in range(n)])
        self.assertEqual(w["one"], [1] * n)
        self.assertEqual(w["center"][:256], coremodel.REPLICA.centers(256))
        self.assertEqual(w["rdiag(5)"], [coremodel.REPLICA.rdiag(5, t) for t in range(n)])
        # the evaluation program proves each evaluation form equal to its host constant
        program = sequencemodel.lean_program(64)
        for name in ("cell_memo", "ldiag_memo", "towerWord_memo", "exposed_memo", "coneZero_memo", "leftCone_memo",
                     "maskedColumn_memo", "rdiag_memo", "center_memo"):
            self.assertIn(f"theorem {name}", program)
        self.assertNotIn("sorry", program)
        text = sequencemodel.MODULE.read_text()
        for t in sequencemodel.THEOREMS:
            self.assertIn(f"name: {t['name']},", text)
        self.assertEqual({x["id"] for x in self.data["excluded"]}, {"dyadic-row", "block-parity", "witt-resp"})
        bad = {**self.data, "sequence": [{**rows[0], "kappa": rows[1]["kappa"]}] + rows[1:]}
        self.assertTrue(any("κ-label" in p for p in sequencemodel.problems(bad)))

    def test_relation_engine_contract_fixtures_and_validators_relation_search(self):
        from tools.r30 import discoverymodel as dm
        text = dm.MODULE.read_text()
        self.assertTrue(dm.check()["ok"], dm.check()["reason"])
        for needle in ("contract{", "name: RelationSearch", "precondition: IsWindow", "postcondition: AllRelationsHold",
                       "realization{", "name: RelationEngine", "model{", "name: RelationSearchModel",
                       "name: is_window_check_sound", "name: all_relations_hold_check_sound", "name: zero_word_iff",
                       "induction{", "name: relationFixtureFindsTheRegister", "name: relationFixtureHasNoFalseRelation"):
            self.assertIn(needle, text)
        fx = dm.fixtures(self.data)
        found = [{dm.FIXTURE_COLUMNS[i] for i, bit in enumerate(r) if bit} for r in fx["relations"]]
        for rel in ({"edge-diagonal", "time-parity"}, {"left-cone", "one", "center"}, {"cone-zero", "cell(-1)"},
                    {"shift:center", "center", "cell(-1)", "masked-column"}):
            self.assertIn(rel, found)
        self.assertEqual(len(found), 4)
        words = fx["window"][1]
        self.assertEqual(dm.Mirror.window_misfits(fx["window"]), 0)
        self.assertEqual(dm.Mirror.relation_residue(words, fx["relations"]), 0)
        false = [list(fx["relations"][0])]
        false[0][2] ^= 1
        self.assertGreater(dm.Mirror.relation_residue(words, false), 0)
        self.assertGreater(dm.Mirror.relation_residue(words, [[0] * len(words)]), 0)
        self.assertGreater(dm.Mirror.window_misfits((fx["window"][0], [words[0] + [1 << 32]] + words[1:])), 0)
        self.assertEqual(dm.Mirror.find_relations((32, [[5], [3], [6]])), [[1, 1, 1]])
        self.assertEqual([t["id"] for t in dm.TRANSFORMS], ["base", "shift", "even", "odd", "and"])
        kappas = dm.kappas_of(self.data)
        self.assertEqual(dm.column_kappa("and:center:cell(1)", kappas), dm.column_kappa("and:cell(1):center", kappas))
        self.assertNotEqual(dm.column_kappa("shift:center", kappas), dm.column_kappa("center", kappas))

    def test_berlekamp_massey_certifies_recurrences_recurrence_search(self):
        from tools.r30 import discoverymodel as dm, sequencemodel
        text = dm.MODULE.read_text()
        for needle in ("name: RecurrenceSearch", "precondition: IsSequenceWindow", "postcondition: SatisfiesRecurrence",
                       "name: RecurrenceEngine", "name: RecurrenceSearchModel", "name: timeParityRecurrence",
                       "name: towerWordTwoRecurrence", "name: periodThreeRecurrence"):
            self.assertIn(needle, text)
        mirror = dm.Mirror
        self.assertEqual(mirror.find_recurrence([t % 2 for t in range(64)]), [1, 0, 1])
        self.assertEqual(mirror.find_recurrence(([1, 0, 0] * 22)[:64]), [1, 0, 0, 1])
        center = sequencemodel.windows(self.data)["center"]
        conn = mirror.find_recurrence(center)
        self.assertEqual(mirror.recurrence_defects(center, conn), 0)
        self.assertGreater(len(conn) - 1, len(center) // 2 - 8)
        self.assertGreater(mirror.recurrence_defects([t % 2 for t in range(64)], [1, 1]), 0)
        self.assertEqual(mirror.recurrence_defects([0] * 8, [0, 1]), 1)  # a leading coefficient 0 is refused
        for rec in dm.fixtures(self.data)["recurrences"]:
            self.assertEqual(rec["found"], rec["expected"], rec["name"])

    def test_roots_are_checked_both_ways_and_requested_discovery_roots(self):
        from tools.r30 import discoverymodel as dm, production
        text = dm.MODULE.read_text()
        self.assertEqual(set(dm.PRODUCTION_ROOTS), {"buildColumns", "findRelations", "findRecurrence"})
        self.assertIn("(checked RelationSearchModel window with [postcondition, precondition])", text)
        self.assertIn("(checked RecurrenceSearchModel sq with [postcondition, precondition])", text)
        roots = {r["root"]: r for r in production.roots()}
        for name in dm.PRODUCTION_ROOTS:
            r = roots[f"{dm.LEAN_MODULE}.{name}"]
            self.assertEqual(r["effects"], ["allocation", "overflow", "recursion"])
            self.assertEqual(r["targets"], ["rust-std"])
        self.assertIn("Rule30Api.Discovery.findRelations", (production.RUNTIME_ROOTS).read_text())
        self.assertIn("rule30_api_discovery_find_relations", production.REQUEST.read_text())

    def test_certified_runtime_agrees_with_the_mirror_discovery_roots(self):
        """When `bin/r30 api production` has published the discovery packages and
        cargo is present, the generated harness drives the certified roots and
        they return exactly what the mirror returns on the fixture (the bundle is
        never committed, so without one the check is skipped)."""
        import shutil
        from tools.r30 import discover_rust, discoverymodel as dm
        if not discover_rust.bundles() or not shutil.which("cargo"):
            self.skipTest("no production bundle with the discovery packages, or no cargo")
        kind, runner = discover_rust.locate()
        self.assertEqual(kind, "rust", runner)
        fx = dm.fixtures(self.data)
        bases = dm.bases_of(self.data)
        words = runner.build_columns(dm.FIXTURE_WIDTH, bases, fx["specs"])
        self.assertEqual(words, fx["window"][1])
        self.assertEqual(runner.find_relations(dm.FIXTURE_WIDTH, words), fx["relations"])
        self.assertEqual(runner.find_recurrences([r["bits"] for r in fx["recurrences"]]), [r["found"] for r in fx["recurrences"]])

    def test_discover_classifies_relations_with_certificates_discover_command(self):
        import json
        from tools.r30 import discover, discoverymodel as dm, schema, prismmodel
        before = repo.FRONTIER.read_text()
        r = discover.run(window=256, degree=2, engine=("python", "test"))
        self.assertEqual(repo.FRONTIER.read_text(), before)
        self.assertEqual(r["runtime"], "python")
        self.assertEqual(r["columns"], 79 * 4 + 21)
        kappas = dm.kappas_of(self.data)
        classes = {}
        for x in r["relations"]:
            self.assertEqual(x["kappa"], dm.relation_kappa(x["columns"], kappas))
            self.assertLessEqual(x["chance_log2"], 0)
            classes.setdefault(x["class"], []).append(set(x["columns"]))
        # cone-zero = cell(-1) follows from the increment law (register), the rule and the masked column
        self.assertIn({"cone-zero", "cell(-1)"}, classes["consequence"])
        self.assertIn({"edge-diagonal", "time-parity"}, classes["register"])
        # a new relation stays new until discover --write records it as an observed claim
        self.assertIn({"one", "time-parity", "center", "low-diagonal", "interior-three-diagonal"},
                      classes.get("new", []) + classes.get("register", []))
        self.assertLess(max(x["rank"] for x in r["relations"]), r["window"])
        self.assertIn({"one", "rdiag(0)"}, classes["trivial"])
        self.assertEqual(sum(r["counts"].values()), len(r["relations"]))
        doc = json.loads((prismmodel.SCHEMAS / "discover-result.schema.json").read_text())
        schema.validate(doc, json.loads(json.dumps(r)))
        rec = {x["id"]: x for x in r["recurrences"]}
        self.assertEqual(rec["time-parity"]["connection"], [1, 0, 1])
        self.assertEqual(rec["time-parity"]["margin"], self.data["window"] - 4)
        self.assertLessEqual(rec["center"]["margin"], 8)  # the center's window has no short recurrence
        with self.assertRaises(discover.Refused):
            discover.run(window=self.data["window"], degree=1, engine=("python", "test"))
        self.assertIn("relations:", discover.render(r))

    def test_observed_claims_are_validated_on_their_window_observed_status(self):
        import tempfile as tf
        from tools.r30 import observermodel, registermodel
        self.assertIn("observed", frontier.STATUSES)
        tmp = tf.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        old = repo.FRONTIER
        repo.FRONTIER = Path(tmp.name) / "frontier.toml"
        self.addCleanup(lambda: setattr(repo, "FRONTIER", old))
        frontier.add("true-one", "cone-zero is cell(-1)", status="observed", relation=["cone-zero", "cell(-1)"], window=64)
        frontier.add("proved-one", "edge parity", status="proved", lean="X.y", relation=["edge-diagonal", "time-parity"])
        self.assertEqual(frontier.relation_problems(), [])
        c = frontier.list_claims()[0]
        self.assertEqual(c["window"], 64)
        self.assertTrue(c["kappa"].startswith("sha256:"))
        with self.assertRaises(ValueError):
            frontier.add("bare", "no relation", status="observed")
        with self.assertRaises(ValueError):
            frontier.add("ghost", "x", status="observed", relation=["no-such-sequence"])
        frontier.add("false-one", "center is the time parity", status="observed", relation=["center", "time-parity"])
        problems = frontier.relation_problems()
        self.assertEqual(len(problems), 1)
        self.assertIn("false-one: its relation does not vanish", problems[0])
        claims = frontier.list_claims()
        d = observermodel.data(claims=claims)
        for q in d["quadruples"]:
            self.assertNotIn("true-one", q["realQualities"] + q["withdrawn"])
        text = registermodel.render(registermodel.rows())
        self.assertIn("name: observedHaveRelations", text)
        self.assertIn('"cone-zero"', text)

    def test_candidates_are_reported_never_asserted_discovery_candidates(self):
        import tomllib
        from tools.r30 import prismmodel
        rows = {r["id"]: r for r in tomllib.loads(prismmodel.ids(prismmodel.rows()))["id"]}
        self.assertEqual(rows["discovery-candidates"]["level"], "open")
        self.assertEqual(prismmodel.LEVEL["observed"], "open")
        feature = (prismmodel.FEATURES / "discovery.feature").read_text()
        self.assertIn("@discovery-candidates @open", feature)
        self.assertIn("never asserted", feature)
        for x in prismmodel.API_IDS:
            if x["suite"] == "discovery":
                suffix = x["id"].replace("-", "_")
                self.assertTrue(any(name.endswith(suffix) for name in dir(DiscoveryTests)), x["id"])


if __name__ == "__main__":
    unittest.main()
