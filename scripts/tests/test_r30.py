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
    """The register renders to a LexLean module deterministically, and a stale
    render is a check failure. Uses the real register and a fake kernel."""

    class FakeLean:
        def signatures(self, names):
            from tools.r30 import leansig
            return leansig.signatures(names)

    def test_render_is_deterministic_and_check_detects_staleness(self):
        text1, _ = frontier.render()
        text2, _ = frontier.render()
        self.assertEqual(text1, text2)
        self.assertIn("\\begin{lexlean}{Frontier}", text1)
        self.assertIn("claim-recurrent-central-collision", text1)
        current, _ = frontier.render_file(check_only=True)
        self.assertTrue(current, "Frontier.lex.tex is stale in the working tree; run bin/r30 frontier render")


class McpTests(unittest.TestCase):
    def test_every_tool_maps_to_argv(self):
        for tool in tool_list():
            if tool["name"] == "tail_log":
                continue
            argv = argv_for(tool["name"], {"names": ["X"], "query": "q", "id": "i", "message": "m",
                                           "name": "n", "statement": "s"})
            self.assertIsInstance(argv, list)
            self.assertTrue(argv)


if __name__ == "__main__":
    unittest.main()
