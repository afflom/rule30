"""Repository layout and process helpers shared by every `r30` command."""

from pathlib import Path
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[2]
CORE_LEAN = ROOT / "rule30-core-lean"
BRIDGE = ROOT / "rule30-bridge"
PROJECTS = {
    "paper": ROOT / "rule30-paper",
    "core": ROOT / "rule30-lexlean",
}
FRONTIER = ROOT / "frontier.toml"
SCRATCH = ROOT / ".r30"


def lexlean_bin():
    for candidate in (os.environ.get("LEXLEAN_BIN"), git_config("rule30.lexlean"),
                      str(ROOT / ".local/bin/lexlean")):
        if candidate and Path(candidate).exists():
            return candidate
    return "lexlean"


def git_config(key):
    code, out, _ = run(["git", "config", key], cwd=ROOT)
    return out.strip() if code == 0 else None


def run(cmd, cwd=ROOT, timeout=None, env=None, input=None):
    """Run a command; return (code, stdout, stderr). Never raises on nonzero exit."""
    merged = dict(os.environ)
    if env:
        merged.update(env)
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                          env=merged, input=input)
    return proc.returncode, proc.stdout, proc.stderr


def lake_roots(package_dir):
    import tomllib
    config = tomllib.loads((package_dir / "lakefile.toml").read_text())
    roots = []
    for lib in config["lean_lib"]:
        roots.extend(lib.get("roots", [lib["name"]]))
    return roots


def research_modules():
    return [m for m in lake_roots(CORE_LEAN) if m.startswith("Rule30UOR.")]


def scratch_dir():
    SCRATCH.mkdir(exist_ok=True)
    return SCRATCH


def to_json(obj):
    return json.dumps(obj, indent=1, sort_keys=True, ensure_ascii=False)
