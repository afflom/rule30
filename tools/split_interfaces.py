#!/usr/bin/env python3
"""Split `Rule30UOR/Interfaces.lean` into parts along its `/-! ### ... -/` section
headers, keeping declaration order and the single namespace.

Each part is `Rule30UOR/Interfaces/PartNN.lean`, opens the namespace, repeats the
`open` lines that precede it in the original, and imports the previous part.
`Rule30UOR/Interfaces.lean` becomes a facade that publicly imports every part,
so `import Rule30UOR.Interfaces` and every `Rule30UOR.Interfaces.*` name are
unchanged. The four `private` lemmas become ordinary (still undocumented)
lemmas, since parts reference them across file boundaries.

Usage: tools/split_interfaces.py [--max-lines N] [--write]
"""

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "rule30-core-lean/Rule30UOR/Interfaces.lean"
PART_DIR = ROOT / "rule30-core-lean/Rule30UOR/Interfaces"
HEADER = re.compile(r"^/-! ### (.*?) -/$")


def split(max_lines):
    lines = SRC.read_text().split("\n")
    # prologue: everything before the first `namespace` line
    first_ns = next(i for i, l in enumerate(lines) if l.startswith("namespace Rule30UOR.Interfaces"))
    prologue = lines[:first_ns]
    imports = [l for l in prologue if l.startswith("public import")]
    doc = "\n".join(l for l in prologue if not l.startswith("public import") and l != "module").strip()
    body = lines[first_ns:]
    # drop namespace/end lines; collect opens in order of first appearance
    sections = []           # (title, [lines])
    opens_so_far = []
    cur_title, cur = "Preamble", []
    cur_opens = []
    for l in body:
        if l.startswith("namespace Rule30UOR.Interfaces") or l == "end Rule30UOR.Interfaces":
            continue
        m = HEADER.match(l)
        if m:
            sections.append((cur_title, cur, list(cur_opens)))
            cur_title, cur = m.group(1), [l]
            cur_opens = list(opens_so_far)
            continue
        if l.startswith("open "):
            opens_so_far.append(l)
            cur_opens.append(l)
        cur.append(l)
    sections.append((cur_title, cur, list(cur_opens)))
    # group sections into parts of at most max_lines
    parts, acc, acc_titles, acc_opens = [], [], [], []
    for title, sec, opens in sections:
        if acc and len(acc) + len(sec) > max_lines:
            parts.append((acc_titles, acc, acc_opens))
            acc, acc_titles, acc_opens = [], [], []
        acc += sec
        acc_titles.append(title)
        acc_opens = opens  # opens visible at the start of the *first* section are a prefix of these
    parts.append((acc_titles, acc, acc_opens))
    return imports, doc, parts


def render_part(n, titles, content, opens, imports, prev):
    name = f"Rule30UOR.Interfaces.Part{n:02d}"
    header = ["module", ""]
    header += [f"public import {prev}"] if prev else imports
    header += ["", "/-!", f"# `Rule30UOR.Interfaces`, part {n}", "",
               *[f"* {t}" for t in titles], "-/", "", "@[expose] public section", "",
               "namespace Rule30UOR.Interfaces", ""]
    # opens that must be in scope for this part: all opens seen before its first line
    body = "\n".join(content).strip("\n")
    body = re.sub(r"^private (theorem|def) ", r"\1 ", body, flags=re.M)
    text = "\n".join(header) + "\n".join(opens) + ("\n\n" if opens else "") + body + \
        "\n\nend Rule30UOR.Interfaces\n"
    return name, text


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-lines", type=int, default=2500)
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    imports, doc, parts = split(args.max_lines)
    names = []
    rendered = []
    prev = None
    for n, (titles, content, opens) in enumerate(parts, 1):
        # a part's own `open` lines are inside its content; the ones it inherits are `opens`
        inherited = [o for o in opens if o not in content]
        name, text = render_part(n, titles, content, inherited, imports, prev)
        names.append(name)
        rendered.append((name, text))
        prev = name
    facade = ["module", ""] + [f"public import {n}" for n in names] + ["", doc, ""]
    print(f"{len(parts)} parts: " + ", ".join(f"{n.split('.')[-1]}({len(t.splitlines())})" for n, t in rendered))
    if not args.write:
        return
    PART_DIR.mkdir(exist_ok=True)
    for name, text in rendered:
        (PART_DIR / (name.split(".")[-1] + ".lean")).write_text(text)
    SRC.write_text("\n".join(facade))
    lakefile = ROOT / "rule30-core-lean/lakefile.toml"
    s = lakefile.read_text()
    s = s.replace('"Rule30UOR.Interfaces", ', '"Rule30UOR.Interfaces", ' + "".join(f'"{n}", ' for n in names), 1)
    lakefile.write_text(s)
    audit = ROOT / "rule30-core-lean/scripts/CheckResearchAxioms.lean"
    a = audit.read_text()
    a = a.replace("import Rule30UOR.Interfaces\n", "import Rule30UOR.Interfaces\n" +
                  "".join(f"import {n}\n" for n in names), 1)
    audit.write_text(a)
    print("written")


if __name__ == "__main__":
    main()
