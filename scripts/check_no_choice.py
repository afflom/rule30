#!/usr/bin/env python3
"""Forbid `Classical.choice` in the authored proof surfaces.

The kernel audit (`CheckResearchAxioms.lean`) rejects any research theorem that
depends on an axiom outside `propext` and `Quot.sound`. This source check fails
earlier and names the line:

* no LexLean statement may allow `Classical.choice` in `\\allowaxioms` or
  `\\exactaxioms`;
* no research or bridge Lean source may use a classical constant (`Classical.*`,
  `Exists.choose`, `.choose`/`.choose_spec` field notation) or `open Classical`;
* the kernel audit's allowlist must not contain `Classical.choice`.

Comments and docstrings are ignored, so the prose may discuss classical steps.
"""

from pathlib import Path
import re
import sys

LEXLEAN_SOURCES = ["rule30-lexlean/src", "rule30-paper/src"]
LEAN_SOURCES = ["rule30-core-lean/Rule30UOR", "rule30-bridge/Rule30Paper"]
LEAN_TOP_LEVEL = ["rule30-bridge"]
AUDIT = "rule30-core-lean/scripts/CheckResearchAxioms.lean"

AXIOM_LIST = re.compile(r"\\(?:allow|exact)axioms\{([^}]*)\}")
CLASSICAL = re.compile(
    r"\bClassical\.[A-Za-z_]|\bopen\s+(?:[A-Za-z_.]+\s+)*Classical\b|"
    r"\bExists\.choose(?:_spec)?\b|\.choose(?:_spec)?\b")


def strip_lean_comments(text):
    """Blank out `--` comments and nested `/- -/` blocks, keeping line numbers."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def violations(root):
    root = Path(root)
    found = []
    for base in LEXLEAN_SOURCES:
        for path in sorted((root / base).glob("*.lex.tex")):
            for n, line in enumerate(path.read_text().splitlines(), 1):
                for m in AXIOM_LIST.finditer(line):
                    if "Classical.choice" in m.group(1):
                        found.append(f"{path.relative_to(root)}:{n}: allows Classical.choice")
    for base in LEAN_SOURCES:
        for path in sorted((root / base).rglob("*.lean")):
            code = strip_lean_comments(path.read_text())
            for n, line in enumerate(code.splitlines(), 1):
                m = CLASSICAL.search(line)
                if m:
                    found.append(f"{path.relative_to(root)}:{n}: classical constant `{m.group(0)}`")
    for base in LEAN_TOP_LEVEL:
        for path in sorted((root / base).glob("*.lean")):
            code = strip_lean_comments(path.read_text())
            for n, line in enumerate(code.splitlines(), 1):
                m = CLASSICAL.search(line)
                if m:
                    found.append(f"{path.relative_to(root)}:{n}: classical constant `{m.group(0)}`")
    audit = root / AUDIT
    if audit.exists():
        allowed = re.search(r"let allowed : Array Name := #\[([^\]]*)\]", audit.read_text())
        if allowed is None:
            found.append(f"{AUDIT}: allowlist not found")
        elif "Classical.choice" in allowed.group(1):
            found.append(f"{AUDIT}: the kernel audit allows Classical.choice")
    return found


if __name__ == "__main__":
    problems = violations(Path(__file__).resolve().parents[1])
    if problems:
        print("Classical.choice is forbidden:", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        sys.exit(1)
    print("No Classical.choice in LexLean statements, research sources, or the axiom audit.")
