import importlib.util
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("coverage_check", ROOT / "scripts/check_research_coverage.py")
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)


class ResearchCoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.core = self.repo / "rule30-core-lean"
        (self.core / "Rule30UOR").mkdir(parents=True)
        (self.core / "scripts").mkdir()
        self.source("Existing")
        self.configure(["Existing"])

    def source(self, name):
        path = self.core / ("Rule30UOR/" + name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("-- coverage fixture\n")

    def configure(self, names, audited=None, namespace="Rule30UOR"):
        roots = ", ".join('"Rule30UOR.' + name + '"' for name in names)
        (self.core / "lakefile.toml").write_text('[[lean_lib]]\nname = "Rule30UOR"\nroots = [' + roots + ']\n')
        audit = "".join("import Rule30UOR." + name + "\n" for name in (names if audited is None else audited))
        audit += "if (`" + namespace + ").isPrefixOf name then\n"
        (self.core / "scripts/CheckResearchAxioms.lean").write_text(audit)

    def test_unregistered_frontier_module_fails(self):
        self.source("Frontier")
        with self.assertRaisesRegex(ValueError, "unregistered=.*Frontier"):
            coverage.covered_modules(self.repo)

    def test_registered_but_unaudited_module_fails(self):
        self.source("Frontier")
        self.configure(["Existing", "Frontier"], audited=["Existing"])
        with self.assertRaisesRegex(ValueError, "missing from axiom audit.*Frontier"):
            coverage.covered_modules(self.repo)

    def test_narrow_namespace_audit_fails(self):
        self.configure(["Existing"], namespace="Rule30UOR.Existing")
        with self.assertRaisesRegex(ValueError, "entire Rule30UOR namespace"):
            coverage.covered_modules(self.repo)

    def test_missing_root_source_fails(self):
        self.configure(["Existing", "Missing"])
        with self.assertRaisesRegex(ValueError, "missing sources=.*Missing"):
            coverage.covered_modules(self.repo)

    def test_all_sources_including_nested_modules_are_covered(self):
        self.source("Nested.Frontier")
        self.configure(["Existing", "Nested.Frontier"])
        self.assertEqual(coverage.covered_modules(self.repo),
                         ["Rule30UOR.Existing", "Rule30UOR.Nested.Frontier"])

    def test_repository_sources_are_covered(self):
        self.assertIn("Rule30UOR.Frontier", coverage.covered_modules(ROOT))
