import importlib.util
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("no_choice", ROOT / "scripts/check_no_choice.py")
no_choice = importlib.util.module_from_spec(spec)
spec.loader.exec_module(no_choice)


class NoChoiceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        (self.repo / "rule30-paper/src").mkdir(parents=True)
        (self.repo / "rule30-lexlean/src").mkdir(parents=True)
        (self.repo / "rule30-core-lean/Rule30UOR").mkdir(parents=True)
        (self.repo / "rule30-core-lean/scripts").mkdir(parents=True)
        self.audit("``propext, ``Quot.sound")

    def audit(self, names):
        (self.repo / "rule30-core-lean/scripts/CheckResearchAxioms.lean").write_text(
            "  let allowed : Array Name := #[" + names + "]\n")

    def lean(self, text):
        (self.repo / "rule30-core-lean/Rule30UOR/M.lean").write_text(text)

    def lex(self, text):
        (self.repo / "rule30-paper/src/P.lex.tex").write_text(text)

    def test_clean_tree_passes(self):
        self.lean("theorem t : True := trivial\n")
        self.lex("\\allowaxioms{Quot.sound;propext}\n")
        self.assertEqual(no_choice.violations(self.repo), [])

    def test_lexlean_allowlist_with_choice_fails(self):
        self.lex("\\allowaxioms{Classical.choice;Quot.sound;propext}\n")
        self.assertRegex(" ".join(no_choice.violations(self.repo)), "allows Classical.choice")

    def test_classical_constant_in_lean_fails(self):
        self.lean("theorem t (p : Prop) : p ∨ ¬ p := Classical.em p\n")
        self.assertRegex(" ".join(no_choice.violations(self.repo)), "Classical.e")

    def test_choose_field_notation_fails(self):
        self.lean("def f (h : ∃ n : Nat, n = 0) : Nat := h.choose\n")
        self.assertRegex(" ".join(no_choice.violations(self.repo)), "choose")

    def test_open_classical_fails(self):
        self.lean("open Classical in\ntheorem t : True := trivial\n")
        self.assertRegex(" ".join(no_choice.violations(self.repo)), "open Classical")

    def test_comments_are_ignored(self):
        self.lean("/-! Avoids `Classical.choice` and `Exists.choose`. -/\n-- Classical.em\n"
                  "theorem t : True := trivial\n")
        self.assertEqual(no_choice.violations(self.repo), [])

    def test_audit_allowing_choice_fails(self):
        self.audit("``propext, ``Classical.choice, ``Quot.sound")
        self.assertRegex(" ".join(no_choice.violations(self.repo)), "audit allows")


if __name__ == "__main__":
    unittest.main()
