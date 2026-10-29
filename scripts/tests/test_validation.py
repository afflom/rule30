"""Regression coverage for the build failure that escaped the authoring-only hook."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class SnapshotHookTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.repo.mkdir()
        tools = self.base / "tools"
        tools.mkdir()
        self.compiler = tools / "lexlean"
        for name, body in {
            "lexlean": "echo 'compiler-semantics " + "a" * 64 + "'\n",
            "lean": "echo 'Lean test version'\n",
            "lake": "echo 'Lake test version'\n",
        }.items():
            path = tools / name
            path.write_text("#!/bin/sh\n" + body)
            path.chmod(0o755)
        self.env = os.environ.copy()
        self.env.pop("ALLOW_NON_LEXLEAN_AUTHORING", None)
        self.env["PATH"] = str(tools) + os.pathsep + self.env["PATH"]
        self.env["LEXLEAN_BIN"] = str(self.compiler)
        self.env["VALIDATION_COUNTER"] = str(self.base / "counter")
        self.git("init", "-q")
        self.git("config", "user.name", "Validation Test")
        self.git("config", "user.email", "validation@example.invalid")
        self.git("config", "core.hooksPath", "/dev/null")
        for path in (".githooks/pre-commit", ".githooks/pre-push",
                     "scripts/check_authoring_policy.sh", "scripts/validate_git_tree.py"):
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / path, target)
        for project in ("rule30-lexlean", "rule30-paper"):
            self.write(project + "/lexlean.lock", 'compiler_semantics = "' + "a" * 64 + '"\n')
        self.write("rule30-core-lean/lean-toolchain", "test-toolchain\n")
        self.write("rule30-paper/src/Observations.lex.tex", "valid\n")
        self.write("Makefile", "check-ci:\n\tpython3 fixture_gate.py\n")
        self.write("fixture_gate.py", '''import os
from pathlib import Path
p = Path(os.environ["VALIDATION_COUNTER"])
p.write_text(p.read_text() + "run\\n" if p.exists() else "run\\n")
assert "FAIL" not in Path("rule30-paper/src/Observations.lex.tex").read_text()
''')
        self.git("add", ".")
        self.git("commit", "-qm", "baseline")
        self.git("config", "core.hooksPath", ".githooks")

    def git(self, *args, check=True):
        return subprocess.run(["git", *args], cwd=self.repo, env=self.env,
                              check=check, capture_output=True, text=True)

    def write(self, name, contents):
        target = self.repo / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents)

    def stage(self, contents):
        self.write("rule30-paper/src/Observations.lex.tex", contents)
        self.git("add", "rule30-paper/src/Observations.lex.tex")

    def validate(self, success):
        result = subprocess.run(["python3", "scripts/validate_git_tree.py"],
                                cwd=self.repo, env=self.env, capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def runs(self):
        counter = self.base / "counter"
        return len(counter.read_text().splitlines()) if counter.exists() else 0

    def test_real_commit_blocks_paired_but_invalid_source(self):
        self.stage("FAIL\n")
        self.write("rule30-core-lean/Rule30UOR/Example.lean", "proof edit\n")
        self.git("add", "rule30-core-lean/Rule30UOR/Example.lean")
        before = self.git("rev-parse", "HEAD").stdout
        result = self.git("commit", "-qm", "must fail", check=False)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(before, self.git("rev-parse", "HEAD").stdout)
        self.assertEqual(self.runs(), 1)

    def test_unstaged_fix_cannot_hide_staged_failure(self):
        self.stage("FAIL\n")
        self.write("rule30-paper/src/Observations.lex.tex", "unstaged fix\n")
        self.validate(False)
        self.assertEqual(self.runs(), 1)
        self.assertEqual((self.repo / "rule30-paper/src/Observations.lex.tex").read_text(), "unstaged fix\n")
        self.assertEqual(self.git("show", ":rule30-paper/src/Observations.lex.tex").stdout, "FAIL\n")

    def test_unstaged_failure_does_not_poison_valid_staged_tree(self):
        self.stage("valid staged\n")
        self.write("rule30-paper/src/Observations.lex.tex", "FAIL\n")
        self.validate(True)

    def test_policy_override_does_not_skip_build(self):
        self.stage("FAIL\n")
        self.env["ALLOW_NON_LEXLEAN_AUTHORING"] = "1"
        self.assertNotEqual(self.git("commit", "-qm", "must fail", check=False).returncode, 0)
        self.assertEqual(self.runs(), 1)

    def test_only_success_is_cached_for_exact_tree_and_compiler(self):
        self.stage("FAIL\n")
        self.validate(False)
        self.validate(False)
        self.assertEqual(self.runs(), 2)
        self.stage("valid\n")
        self.validate(True)
        self.validate(True)
        self.assertEqual(self.runs(), 3)
        self.stage("changed valid\n")
        self.validate(True)
        self.assertEqual(self.runs(), 4)
        self.compiler.write_text(self.compiler.read_text() + "# compiler binary changed\n")
        self.validate(True)
        self.assertEqual(self.runs(), 5)

    def test_wrong_compiler_blocks_before_build(self):
        self.compiler.write_text("#!/bin/sh\necho 'compiler-semantics wrong'\n")
        self.validate(False)
        self.assertEqual(self.runs(), 0)

    def test_pre_push_validates_tip_instead_of_fixed_worktree(self):
        self.stage("FAIL\n")
        # Simulate a commit made by a client without hooks.
        self.git("-c", "core.hooksPath=/dev/null", "commit", "-qm", "unchecked")
        oid = self.git("rev-parse", "HEAD").stdout.strip()
        self.stage("fixed working tree\n")
        result = self.push_hook(oid)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.runs(), 1)

    def test_pre_push_reuses_commit_certificate_and_skips_deletion(self):
        self.stage("valid updated\n")
        self.git("commit", "-qm", "checked")
        oid = self.git("rev-parse", "HEAD").stdout.strip()
        self.assertEqual(self.push_hook(oid).returncode, 0)
        self.assertEqual(self.push_hook("0" * 40).returncode, 0)
        self.assertEqual(self.runs(), 1)

    def push_hook(self, oid):
        return subprocess.run(["bash", ".githooks/pre-push"], cwd=self.repo, env=self.env,
                              input=f"refs/heads/main {oid} refs/heads/main {'0' * 40}\n",
                              capture_output=True, text=True)


class CompleteGateTests(unittest.TestCase):
    def run_gate(self, failure="", drift=""):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "scripts").mkdir()
            shutil.copy(ROOT / "scripts/check_ci.sh", repo / "scripts")
            for project in ("rule30-lexlean", "rule30-paper"):
                (repo / project).mkdir()
                (repo / project / "lexlean.lock").write_text("original\n")
            stages = ["check-tooling", "check-research", "bridge", "lexlean", "release-artifacts"]
            recipes = []
            for stage in stages:
                recipe = f"{stage}:\n\t@echo {stage} >> stages\n"
                if stage == failure:
                    recipe += "\t@exit 1\n"
                if stage == "lexlean" and drift:
                    recipe += f"\t@echo drift >> {drift}/lexlean.lock\n"
                recipes.append(recipe)
            (repo / "Makefile").write_text("\n".join(recipes))
            result = subprocess.run(["bash", "scripts/check_ci.sh", "compiler"],
                                    cwd=repo, capture_output=True, text=True)
            return result, (repo / "stages").read_text().splitlines()

    def test_gate_runs_every_ci_stage(self):
        result, stages = self.run_gate()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(stages, ["check-tooling", "check-research", "bridge", "lexlean", "release-artifacts"])

    def test_each_stage_failure_blocks_gate(self):
        for stage in ("check-tooling", "check-research", "bridge", "lexlean", "release-artifacts"):
            with self.subTest(stage=stage):
                result, stages = self.run_gate(failure=stage)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(stages[-1], stage)

    def test_either_lockfile_drifting_blocks_packaging(self):
        for project in ("rule30-lexlean", "rule30-paper"):
            with self.subTest(project=project):
                result, stages = self.run_gate(drift=project)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn("release-artifacts", stages)
