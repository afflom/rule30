"""κ-labels (scripts/kappa_research.py): the Rivest canonicalizer, the no-prefix
rule of uor-addr, and the rule30 profile of a Lean declaration, checked against
hand-computed vectors."""

import contextlib
import hashlib
import io
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import kappa_research as K  # noqa: E402


def sha(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def line(*parts):
    return K.canonical(list(parts)) + b"\n"


class CanonicalFormTests(unittest.TestCase):
    def test_json_vector_is_hashed_with_no_prefix(self):
        # uor-addr's README vector: {"foo": "bar"} under JCS is {"foo":"bar"}, and the
        # label is the SHA-256 of exactly those canonical bytes.
        canonical_json = b'{"foo":"bar"}'
        self.assertEqual(K.label(canonical_json),
                         "sha256:7a38bf81f383f69433ad6e900d35b3e2385593f76a7b7ab5d4355b8ba41ee24b")
        self.assertEqual(K.label(canonical_json), "sha256:" + hashlib.sha256(canonical_json).hexdigest())
        self.assertEqual(len(K.label(canonical_json)), 71)

    def test_rivest_vectors(self):
        self.assertEqual(K.canonical(["a", "b", "c"]), b"(1:a 1:b 1:c)")
        self.assertEqual(K.canonical([]), b"()")
        self.assertEqual(K.canonical("hello world"), b"11:hello world")
        self.assertEqual(K.canonical(""), b"0:")
        self.assertEqual(K.canonical("κ"), b"2:\xce\xba")
        self.assertEqual(K.canonical(["a", ["b", "c"], [], "d e"]), b"(1:a (1:b 1:c) () 3:d e)")
        self.assertEqual(K.canonical([b"raw", "text"]), b"(3:raw 4:text)")

    def test_labels_compose_as_atoms(self):
        inner = K.kappa(["b", "c"])
        self.assertEqual(K.kappa(["a", inner]), sha(b"(1:a 71:" + inner.encode() + b")"))

    def test_parse_inverts_canonical(self):
        values = [["a", ["b", "c"], [], "d e", "(x)"], "atom", [], ["nested", [["deep"]]]]
        data = b"\n".join(K.canonical(v) for v in values) + b"\n"
        expected = [[b"a", [b"b", b"c"], [], b"d e", b"(x)"], b"atom", [], [b"nested", [[b"deep"]]]]
        self.assertEqual(list(K.parse(data)), expected)
        self.assertEqual(list(K.parse(b"  (1:a\n1:b)\t")), [[b"a", b"b"]])
        self.assertEqual(list(K.parse(b"")), [])

    def test_parse_refuses_what_is_not_canonical(self):
        for bad in (b"(1:a", b"1:a)", b"(a b)", b"3:ab", b"(1:a))"):
            with self.assertRaises(ValueError):
                list(K.parse(bad))


class DeclarationProfileTests(unittest.TestCase):
    AXIOM = (line("module", "Foo", ["constants", "1"]) +
             line("node", "0", "lparam", "u") +
             line("node", "1", "sort", "0") +
             line("decl", "Foo", "axiom", ["levels", "u"], "1", [], ["safety", "safe"]) +
             line("end", "Foo"))

    def test_axiom_by_hand(self):
        k0 = sha(b"(6:lparam 1:u)")
        k1 = sha(b"(4:sort 71:" + k0.encode() + b")")
        kd = sha(b"(4:decl 3:Foo 5:axiom (6:levels 1:u) 71:" + k1.encode() + b" () (6:safety 4:safe))")
        km = sha(b"(11:lean-module 3:Foo 71:" + kd.encode() + b")")
        labels = K.labels_from_stream(self.AXIOM)
        self.assertEqual(labels, {"Foo": {"kappa": km, "declarations": [("Foo", kd)], "statements": [],
                                          "kinds": {"Foo": "axiom"}, "reserved": []}})

    def theorem(self, module, sharing, order="forward", value="0"):
        """A module with a definition `d` of type Prop and value `(lit nat value)`
        and a theorem `t : Prop := d`, with or without shared nodes."""
        zero = line("node", "0", "lzero")
        prop = line("node", "1", "sort", "0")
        lit = line("node", "2", "lit", "nat", value)
        d = line("decl", module + ".d", "def", ["levels"], "1", "2", ["safety", "safe"])
        const = line("node", "3", "const", module + ".d")
        if sharing:
            t = line("decl", module + ".t", "thm", ["levels"], "1", "3")
            nodes = zero + prop + lit + const
        else:  # Prop emitted twice, under two ids: sharing is the stream's, not the meaning's
            nodes = zero + prop + lit + const + line("node", "4", "lzero") + line("node", "5", "sort", "4")
            t = line("decl", module + ".t", "thm", ["levels"], "5", "3")
        decls = d + t if order == "forward" else t + d
        return line("module", module, ["constants", "2"]) + nodes + decls + line("end", module)

    def test_sharing_and_order_are_not_part_of_the_meaning(self):
        shared = K.labels_from_stream(self.theorem("M", sharing=True))
        unshared = K.labels_from_stream(self.theorem("M", sharing=False))
        reordered = K.labels_from_stream(self.theorem("M", sharing=True, order="backward"))
        self.assertEqual(shared, unshared)
        self.assertEqual(shared, reordered)
        self.assertEqual([n for n, _ in shared["M"]["declarations"]], ["M.d", "M.t"])

    def test_a_changed_value_changes_the_definition_the_module_and_nothing_else(self):
        before = K.labels_from_stream(self.theorem("M", sharing=True))["M"]
        after = K.labels_from_stream(self.theorem("M", sharing=True, value="1"))["M"]
        self.assertNotEqual(before["kappa"], after["kappa"])
        self.assertNotEqual(dict(before["declarations"])["M.d"], dict(after["declarations"])["M.d"])
        # `t` refers to `d` by name, so its own label does not move.
        self.assertEqual(dict(before["declarations"])["M.t"], dict(after["declarations"])["M.t"])

    def test_recursor_rules_address_their_right_hand_sides(self):
        stream = (line("module", "R", ["constants", "1"]) +
                  line("node", "0", "lzero") + line("node", "1", "sort", "0") +
                  line("node", "2", "lit", "nat", "7") +
                  line("decl", "R.rec", "rec", ["levels"], "1", [], ["all", "R"], ["params", "0"],
                       ["indices", "0"], ["motives", "1"], ["minors", "1"],
                       ["rules", ["rule", "R.mk", "0", "2"]], ["k", "0"], ["safety", "safe"]) +
                  line("end", "R"))
        k1 = sha(b"(4:sort 71:" + sha(b"(5:lzero)").encode() + b")")
        k2 = sha(b"(3:lit 3:nat 1:7)")
        kd = K.kappa(["decl", "R.rec", "rec", ["levels"], k1, [], ["all", "R"], ["params", "0"], ["indices", "0"],
                      ["motives", "1"], ["minors", "1"], ["rules", ["rule", "R.mk", "0", k2]], ["k", "0"],
                      ["safety", "safe"]])
        self.assertEqual(K.labels_from_stream(stream)["R"]["declarations"], [("R.rec", kd)])

    def test_stream_must_close_its_modules(self):
        with self.assertRaises(ValueError):
            K.labels_from_stream(line("module", "M", ["constants", "0"]))
        with self.assertRaises(ValueError):
            K.labels_from_stream(line("module", "M", ["constants", "0"]) + line("end", "N"))


class ExporterTests(unittest.TestCase):
    def test_module_labels_takes_an_injected_exporter_and_names_what_is_missing(self):
        calls = []

        def exporter(core, modules):
            calls.append((core, list(modules)))
            return DeclarationProfileTests.AXIOM

        labels = K.module_labels(Path("core"), ["Foo"], exporter=exporter)
        self.assertEqual(calls, [(Path("core"), ["Foo"])])
        self.assertEqual(set(labels), {"Foo"})
        with self.assertRaises(RuntimeError) as cm:
            K.module_labels(Path("core"), ["Foo", "Bar"], exporter=exporter)
        self.assertIn("Bar", str(cm.exception))
        self.assertEqual(K.module_labels(Path("core"), [], exporter=exporter), {})

    def test_main_prints_labels_and_json(self):
        old = K.export
        K.export = lambda core, modules: DeclarationProfileTests.AXIOM
        self.addCleanup(lambda: setattr(K, "export", old))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            K.main(["Foo"])
        self.assertRegex(out.getvalue().strip(), r"^Foo: sha256:[0-9a-f]{64}$")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            K.main(["Foo", "--declarations"])
        self.assertEqual(len(out.getvalue().splitlines()), 2)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            K.main(["Foo", "--json"])
        import json
        data = json.loads(out.getvalue())
        self.assertEqual(list(data), ["Foo"])
        self.assertEqual(data["Foo"]["declarations"][0]["name"], "Foo")



class RedundancyTests(unittest.TestCase):
    """Theorems that state the same thing group whatever their names, privacy, binders or
    universe names; generated declarations never count."""

    def test_reserved_names_are_generated_and_nothing_else_by_suffix(self):
        reserved = {"Rule30UOR.A.f.eq_1", "Rule30UOR.A.f.induct", "Rule30UOR.A.C.mk.injEq"}
        for name in reserved:
            self.assertFalse(K.authored(name, {}, reserved), name)
        # the same suffixes, where Lean does not reserve them, are names someone wrote
        for written in ("Rule30UOR.A.g.induct", "Rule30UOR.A.Periodic.elim", "Rule30UOR.A.t.inj",
                        "Rule30UOR.A.Col.red.inj", "Rule30UOR.A.Foo.ext_iff", "Rule30UOR.A.t.eq_1",
                        "_private.Rule30UOR.A.0.Rule30UOR.A.helper", "Rule30UOR.A.eq_of_range"):
            self.assertTrue(K.authored(written, {}, reserved), written)

    def test_auxiliary_components_count_only_under_a_declaration(self):
        kinds = {"Rule30UOR.A.t": "thm", "Rule30UOR.A.f": "def"}
        for generated in ("Rule30UOR.A.t._proof_1", "Rule30UOR.A.t._simp_1_2", "Rule30UOR.A.f.match_1",
                          "_private.Rule30UOR.A.0.Rule30UOR.A.t._proof_1_4",
                          "_private.Rule30UOR.A.0.Nat.pow.match_1.eq_1", "Init.Foo._proof_1"):
            self.assertFalse(K.authored(generated, kinds), generated)
        for written in ("Rule30UOR.A.helper._aux", "Rule30UOR.A.x.proof_2", "_private.Rule30UOR.A.0.Nat.my_lemma"):
            self.assertTrue(K.authored(written, kinds), written)

    def test_universe_parameters_are_numbered_by_first_occurrence(self):
        line = lambda *parts: K.canonical(list(parts)) + b"\n"
        def module(name, order):
            return (line("module", name, ["constants", "1"]) + line("node", "0", "lparam", "u") +
                    line("node", "1", "lparam", "v") + line("node", "2", "sort", "0") + line("node", "3", "sort", "1") +
                    line("node", "4", "forallE", "default", "2", "3") +
                    line("decl", name + ".t", "thm", ["levels", *order], "4", "4") + line("end", name))
        a = K.labels_from_stream(module("A", ["u", "v"]))["A"]["statements"][0]
        b = K.labels_from_stream(module("B", ["v", "u"]))["B"]["statements"][0]
        self.assertEqual(a[1], b[1])

    def test_groups_span_privacy(self):
        labels = {"C": {"statements": [("_private.C.0.C.v", "K", "e1"), ("C.u", "J", "e2")]},
                  "D": {"statements": [("D.eq_of_x", "J", "e3"), ("D.w", "K", "e1")]}}
        self.assertEqual(K.duplicates(labels), {"J": [("C", "C.u"), ("D", "D.eq_of_x")],
                                                "K": [("C", "_private.C.0.C.v"), ("D", "D.w")]})

    def test_binder_info_and_universe_names_do_not_separate_statements(self):
        line = lambda *parts: K.canonical(list(parts)) + b"\n"
        def module(name, binder, level):
            return (line("module", name, ["constants", "1"]) + line("node", "0", "lparam", level) +
                    line("node", "1", "sort", "0") + line("node", "2", "bvar", "0") +
                    line("node", "3", "forallE", binder, "1", "2") +
                    line("decl", name + ".t", "thm", ["levels", level], "3", "2") + line("end", name))
        a = K.labels_from_stream(module("A", "default", "u"))["A"]["statements"][0]
        b = K.labels_from_stream(module("B", "implicit", "v"))["B"]["statements"][0]
        self.assertEqual(a[1], b[1])
        self.assertNotEqual(a[2], b[2])


if __name__ == "__main__":
    unittest.main()
