import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class HookTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.env = os.environ.copy()
        self.env.pop("ALLOW_NON_LEXLEAN_AUTHORING", None)
        self.git("init", "-q")
        self.git("config", "user.name", "Hook Test")
        self.git("config", "user.email", "hook@example.invalid")
        self.git("config", "core.hooksPath", "/dev/null")
        self.files = {
            "README.md": "baseline\n",
            "rule30-lexlean/src/Core.lex.tex": "source\n",
            "rule30-core-lean/Rule30UOR/Example.lean": "proof\n",
            "rule30-bridge/Example.lean": "bridge\n",
            "Rule30-Core.pdf": "generated\n",
            ".github/lexlean-revision": "a" * 40 + "\n",
            "rule30-lexlean/lexlean.lock": 'compiler_semantics = "' + "a" * 64 + '"\nlanguage = "1.2"\n',
        }
        for path, contents in self.files.items():
            self.write(path, contents)
        self.git("add", ".")
        self.git("commit", "-qm", "baseline")

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.repo, env=self.env,
                              check=True, capture_output=True, text=True)

    def write(self, path, contents):
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents)

    def stage(self, path, contents="modified\n"):
        self.write(path, contents)
        self.git("add", "--", path)

    def hook(self, allowed):
        result = subprocess.run(["bash", str(ROOT / ".githooks/pre-commit")],
                                cwd=self.repo, env=self.env, capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, allowed, result.stderr)

    def compiler_refresh(self):
        self.stage(".github/lexlean-revision", "b" * 40 + "\n")
        self.stage("rule30-lexlean/lexlean.lock",
                   self.files["rule30-lexlean/lexlean.lock"].replace("a" * 64, "b" * 64))

    def test_tooling_only(self):
        self.stage("README.md")
        self.hook(True)

    def test_host_proof_requires_source(self):
        self.stage("rule30-core-lean/Rule30UOR/Example.lean")
        self.hook(False)

    def test_bridge_requires_source(self):
        self.stage("rule30-bridge/Example.lean")
        self.hook(False)

    def test_proof_with_source(self):
        self.stage("rule30-core-lean/Rule30UOR/Example.lean")
        self.stage("rule30-lexlean/src/Core.lex.tex")
        self.hook(True)

    def test_unstaged_source_does_not_count(self):
        self.stage("rule30-core-lean/Rule30UOR/Example.lean")
        self.write("rule30-lexlean/src/Core.lex.tex", "unstaged\n")
        self.hook(False)

    def test_generated_requires_source(self):
        self.stage("Rule30-Core.pdf")
        self.hook(False)

    def test_generated_with_source(self):
        self.stage("Rule30-Core.pdf")
        self.stage("rule30-lexlean/src/Core.lex.tex")
        self.hook(True)

    def test_lock_only_is_blocked(self):
        self.compiler_refresh()
        self.git("reset", "-q", "HEAD", "--", ".github/lexlean-revision")
        self.hook(False)

    def test_compiler_fingerprint_refresh(self):
        self.compiler_refresh()
        self.hook(True)

    def test_compiler_refresh_cannot_change_other_lock_fields(self):
        self.compiler_refresh()
        self.stage("rule30-lexlean/lexlean.lock", 'language = "1.3"\n')
        self.hook(False)

    def test_compiler_refresh_cannot_edit_pdfs(self):
        self.compiler_refresh()
        self.stage("Rule30-Core.pdf")
        self.hook(False)

    def test_compiler_refresh_cannot_edit_proofs(self):
        self.compiler_refresh()
        self.stage("rule30-core-lean/Rule30UOR/Example.lean")
        self.hook(False)

    def test_invalid_compiler_revision(self):
        self.compiler_refresh()
        self.stage(".github/lexlean-revision", "main\n")
        self.hook(False)

    def test_proof_deletion_requires_source(self):
        self.git("rm", "rule30-core-lean/Rule30UOR/Example.lean")
        self.hook(False)

    def test_proof_rename_requires_source(self):
        self.git("mv", "rule30-core-lean/Rule30UOR/Example.lean", "renamed.txt")
        self.hook(False)

    def test_paths_with_newlines(self):
        self.stage("rule30-core-lean/Rule30UOR/unusual\nname.lean")
        self.hook(False)


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        (self.repo / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/verify_lexlean.sh", self.repo / "scripts")
        for project in ("rule30-lexlean", "rule30-paper"):
            cache = self.repo / project / ".lexlean"
            cache.mkdir(parents=True)
            (cache / "latest-verified.json").write_text(json.dumps({"success": True, "attestation_id": "old"}))
        self.compiler = self.repo / "compiler"

    def run_verify(self, body):
        self.compiler.write_text("#!/bin/bash\n" + body)
        self.compiler.chmod(0o755)
        return subprocess.run(["bash", str(self.repo / "scripts/verify_lexlean.sh"), str(self.compiler)],
                              cwd=self.repo, capture_output=True, text=True)

    def latest(self):
        return json.loads((self.repo / "rule30-lexlean/.lexlean/latest-verified.json").read_text())

    def test_success_records_both_results(self):
        result = self.run_verify('if [[ "$1" == lock ]]; then exit 0; fi\nprintf \'{"success":true,"attestation_id":"new"}\\n\'\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        for project in ("rule30-lexlean", "rule30-paper"):
            record = json.loads((self.repo / project / ".lexlean/latest-verified.json").read_text())
            self.assertEqual(record["attestation_id"], "new")

    def test_verification_failure_invalidates_previous_result(self):
        result = self.run_verify('if [[ "$1" == lock ]]; then exit 0; fi\nexit 1\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.latest()["success"])

    def test_lock_failure_invalidates_previous_result(self):
        result = self.run_verify("exit 1\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.latest()["success"])

    def test_invalid_success_result_fails(self):
        result = self.run_verify('if [[ "$1" == lock ]]; then exit 0; fi\nprintf \'{"success":false}\\n\'\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.latest()["success"])


class PackagingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        (self.repo / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/build_release.sh", self.repo / "scripts")
        self.bin = self.repo / "bin"
        self.bin.mkdir()
        latex = self.bin / "pdflatex"
        latex.write_text('#!/bin/bash\nfor arg; do case "$arg" in *.tex) printf "rendered" > "${arg%.tex}.pdf";; esac; done\n')
        latex.chmod(0o755)
        self.env = os.environ.copy()
        self.env["PATH"] = str(self.bin) + os.pathsep + self.env["PATH"]
        for project, module in (("rule30-lexlean", "Core"), ("rule30-paper", "Paper")):
            self.bundle(project, module, "f" * 64, "verified-latest")
            (self.repo / project / "lexlean.lock").write_text('compiler_semantics = "test-compiler"\n')
            (self.repo / project / (module + ".pdf")).write_text("tracked release PDF\n")

    def bundle(self, project, module, identity, kind):
        directory = self.repo / project / kind / identity
        modules = directory / "modules" / ("Rule30UOR" if module == "Core" else "Rule30Paper")
        modules.mkdir(parents=True)
        for extension in ("tex", "lean"):
            (modules / (module + "." + extension)).write_text(identity)
        (directory / "attestation.json").write_text(json.dumps({
            "status": "verified", "attestation_id": identity,
            "lexlean": {"compiler_semantics": "test-compiler"}}))
        return directory

    def run_package(self, success=True, *args):
        result = subprocess.run(["bash", str(self.repo / "scripts/build_release.sh"), *args],
                                env=self.env, cwd=self.repo, capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)

    def test_release_bundle_and_clean_sources(self):
        before = {p: p.read_bytes() for p in self.repo.rglob("*") if p.is_file()}
        self.run_package(True, "--package-only")
        for path, contents in before.items():
            self.assertEqual(path.read_bytes(), contents, str(path))
        subprocess.run(["sha256sum", "--check", "SHA256SUMS"], cwd=self.repo / "dist",
                       check=True, capture_output=True)

    def test_latest_verification_beats_lexical_hash_order(self):
        identity = "0" * 64
        self.bundle("rule30-lexlean", "Core", identity, ".lexlean/verified")
        (self.repo / "rule30-lexlean/.lexlean/latest-verified.json").write_text(
            json.dumps({"success": True, "attestation_id": identity}))
        self.run_package(True, "--package-only")
        self.assertEqual((self.repo / "dist/Core.lean").read_text(), identity)

    def test_ambiguous_release_bundles_fail(self):
        self.bundle("rule30-lexlean", "Core", "0" * 64, "verified-latest")
        self.run_package(False, "--package-only")

    def test_failed_verification_cannot_fall_back(self):
        cache = self.repo / "rule30-lexlean/.lexlean"
        cache.mkdir()
        (cache / "latest-verified.json").write_text(json.dumps({"success": False}))
        self.run_package(False, "--package-only")

    def test_full_build_requires_compiler(self):
        self.env["LEXLEAN_BIN"] = str(self.repo / "missing-compiler")
        self.run_package(False)

    def test_compiler_fingerprint_mismatch_fails(self):
        (self.repo / "rule30-lexlean/lexlean.lock").write_text('compiler_semantics = "different"\n')
        self.run_package(False, "--package-only")


if __name__ == "__main__":
    unittest.main()
