"""Tests for the `r30` tooling that need no Lean build: s-expressions, the
Lean-to-LexLean converter on recorded signatures, the frontier register and the
MCP argument mapping."""

from pathlib import Path
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
                     lean="Rule30UOR.Frontier.problem1_iff_noRecurrentCentralCollision")
        frontier.add("ghost", "no published theorem", status="refuted", lean="Rule30UOR.Nope.x")

    def test_render_restates_published_claims_and_reports_the_rest(self):
        lean = self.FakeLean({"Rule30UOR.Frontier.problem1_iff_noRecurrentCentralCollision": self.IFF,
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

    def test_register_module_matches_frontier_and_states_well_formedness(self):
        from tools.r30 import registermodel
        r = registermodel.check()
        self.assertTrue(r["ok"], r["reason"])
        text = registermodel.render([{"id": "a", "status": "proved", "lean": "X.y", "depends": []},
                                     {"id": "b", "status": "open", "lean": "", "depends": ["a"]}])
        self.assertIn("name: registerDependsResolve", text)
        self.assertIn("proof: decide{}", text)
        self.assertIn('(record Claim {id := "b", status := "open", lean := "", depends := (cons "a" (nil String))})', text)


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
        from tools.r30 import prismmodel
        rows = tomllib.loads(prismmodel.standards())["standard"]
        self.assertEqual({r["facet_package"] for r in rows}, {"prism.arch", "prism.qual"})
        for r in rows:
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

    def test_text_tokens_meet_aa_contrast_in_both_themes(self):
        from tools.r30 import site
        themes = self.tokens(site.TEMPLATE.read_text())
        pairs = [("ink", "bg"), ("ink", "panel"), ("ink", "soft"), ("muted", "bg"), ("muted", "panel"), ("link", "bg"),
                 ("link", "panel"), ("open", "open-bg"), ("open", "panel"), ("proved", "proved-bg"), ("proved", "panel"),
                 ("refuted", "refuted-bg"), ("refuted", "panel"), ("retired", "retired-bg"), ("retired", "panel"),
                 ("ink", "open-bg"), ("focus", "bg")]
        for name, t in themes.items():
            for fg, bg in pairs:
                self.assertGreaterEqual(self.contrast(t[fg], t[bg]), 4.5 if fg != "focus" else 3.0, f"{name}: {fg} on {bg}")

    def test_journeys_check_finds_a_step_without_a_panel(self):
        from tools.r30 import site, presentationmodel as pm
        self.assertEqual(site.check_journeys(), [])
        broken = [{"id": "j", "stakeholder": "researcher", "panels": ["register", "ghost-panel"]}]
        self.assertEqual(site.check_journeys(pm.PANELS, broken), ["journey j: panel ghost-panel is not rendered"])
        nobody = [{"id": "j", "stakeholder": "nobody", "panels": ["register"]}]
        self.assertEqual(site.check_journeys(pm.PANELS, nobody), ["journey j: stakeholder nobody is not declared"])
        old = pm.JOURNEYS[:]
        pm.JOURNEYS[:] = broken
        self.addCleanup(lambda: pm.JOURNEYS.__setitem__(slice(None), old))
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "ghost-panel"):
                site.render_view(Path(tmp) / "view")

    def test_readme_points_to_the_view_and_the_api(self):
        text = (ROOT / "README.md").read_text()
        self.assertIn("## Centerline: the current view and the API modules", text)
        for needle in ("bin/r30 view render", "bin/r30 api check", "src/Api.lex.tex", "rule30-current-view", "bin/r30 api production"):
            self.assertIn(needle, text)


if __name__ == "__main__":
    unittest.main()
