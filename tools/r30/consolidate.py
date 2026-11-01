"""Consolidation of redundant theorems: one proof per statement.

Two authored theorems whose statements share a κ-label (`bin/r30 kappa --duplicates`: the type as
a meaning, without binder info or universe names) are the same theorem proved twice; the gate
refuses them. For each group the plan keeps one proof, the canonical one, and removes the others:
their declarations leave the Lean sources, every reference to them is rewritten to the canonical
name (core modules, the bridge, the core scripts, glossary entries and their denotation modules,
the register, the research log, the paper's sources, the tooling and its fixtures, tests and
experiments), a module that now uses the canonical theorem imports its module, and the interface
sheets that named a removed theorem are regenerated after the build.

The canonical member is chosen, in order: a choice that adds no import cycle (the bridge's paper
module included), that does not wrap another member, whose module is declared before every
reference it takes over, that is public (a private canonical used outside its module is promoted to public),
that adds the fewest imports, that is published, without the generated `_prop` suffix, then the
shortest name. A group whose members differ in binder info (references pass arguments
differently), or with no admissible choice, is left for a person and reported. The plan is
computed from the built library and is deterministic; `apply` is idempotent."""

import re
from pathlib import Path

from . import repo

CORE = repo.CORE_LEAN / "Rule30UOR"
GLOSSARIES = ["rule30-paper/glossary/*/entries/*.toml", "rule30-lexlean/glossary/*/entries/*.toml",
              "rule30-api/glossary/*/entries/*.toml"]
# Lean files outside the research library that may name its theorems.
OUTER_LEAN = ["rule30-bridge/*.lean", "rule30-bridge/Rule30Paper/*.lean", "rule30-core-lean/scripts/*.lean"]
# Prose and data that name theorems by full or qualified name.
REFERENCING = ["frontier.toml", "rule30-lexlean/STRATEGY.md", "AGENTS.md", "README.md"]
REFERENCING_GLOBS = GLOSSARIES + ["rule30-paper/src/*.lex.tex", "scripts/tests/*.py", "experiments/*.py",
                                  "tools/r30/*.py", "tools/r30/*.tmpl", "tools/r30/*.json"]
MODIFIERS = r"(?:(?:private|protected|public|noncomputable|nonrec|unsafe|partial)\s+)*"


def module_path(module):
    return repo.CORE_LEAN / Path(*module.split(".")).with_suffix(".lean")


def lean_modules():
    return {"Rule30UOR." + ".".join(p.relative_to(CORE).with_suffix("").parts): p for p in sorted(CORE.rglob("*.lean"))}


def imports_of(text):
    return re.findall(r"^(?:public\s+)?import\s+(\S+)", text, re.M)


def dependencies(sources):
    """Each module's transitive research imports."""
    direct = {m: [i for i in imports_of(t) if i in sources] for m, t in sources.items()}
    closure = {}

    def visit(m, stack=()):
        if m not in closure:
            seen = set()
            for i in direct.get(m, []):
                if i not in stack:
                    seen |= {i} | visit(i, stack + (m,))
            closure[m] = seen
        return closure[m]

    for m in direct:
        visit(m)
    return closure


def published_names():
    names = set()
    for pattern in GLOSSARIES:
        for path in repo.ROOT.glob(pattern):
            names.update(re.findall(r'^name = "([^"]+)"', path.read_text(), re.M))
    return names


def is_private(full):
    return full.startswith("_private.")


def source_name(full):
    """The name a source file uses: a private theorem `_private.<module>.<n>.<name>` is written
    `<name>` (fully qualified by its namespaces) inside its module."""
    if not is_private(full):
        return full
    parts = full.split(".")
    tail = next((i for i in range(1, len(parts)) if parts[i].isdigit()), None)
    return ".".join(parts[tail + 1:]) if tail is not None else full


def namespaces(text):
    return set(re.findall(r"^namespace\s+(\S+)", text, re.M))


def opens(text):
    """What the file's top-level `open` commands admit: {namespace: None (everything) or a set of
    admitted short names, or ("hiding", set)}. `open ... in` scopes one command and is skipped;
    `open` commands continued on indented lines are read whole."""
    admitted, lines, i = {}, text.splitlines(), 0
    while i < len(lines):
        head = re.match(r"^open\s+(.*)$", lines[i])
        if not head:
            i += 1
            continue
        command = head.group(1)
        while i + 1 < len(lines) and lines[i + 1][:1] in (" ", "\t") and \
                re.fullmatch(r"\s+[A-Za-z_(][\w.' ()]*", lines[i + 1]):
            i += 1
            command += " " + lines[i].strip()
        i += 1
        if re.search(r"\sin\s*$", " " + command) or re.search(r"\bin$", command.strip()):
            continue
        only = re.fullmatch(r"\s*(\S+)\s*\(([^)]*)\)\s*", command)
        hiding = re.fullmatch(r"\s*(\S+)\s+hiding\s+(.+)", command)
        if only:
            admitted.setdefault(only.group(1), set()).update(only.group(2).split())
        elif hiding:
            admitted[hiding.group(1)] = ("hiding", set(hiding.group(2).split()))
        else:
            for name in command.split():
                if name not in ("renaming", "->", "→"):
                    admitted[name] = None
    return admitted


def scoped_lines(lines):
    """(index, line, namespace components) for each line that is not a scope command: `namespace
    X.Y` opens a scope with its components, `section [X]` one with none, and `end [X]` closes the
    innermost scope (so `end S` of a section never drops a namespace component)."""
    scopes = []
    for i, line in enumerate(lines):
        ns = re.match(r"^namespace\s+(\S+)", line)
        if ns:
            scopes.append(ns.group(1).split("."))
            continue
        if re.match(r"^(noncomputable\s+)?section\b", line):
            scopes.append([])
            continue
        if re.match(r"^end(\s|$)", line):
            if scopes:
                scopes.pop()
            continue
        yield i, line, [part for scope in scopes for part in scope]


def declared_names(text):
    """The full source-level names of the theorems and definitions a file declares."""
    head = re.compile(r"^(?:@\[[^\]]*\]\s*)?" + MODIFIERS + r"(?:theorem|lemma|def|abbrev|instance)\s+((?:_root_\.)?[\w.']+)")
    names = set()
    for _, line, stack in scoped_lines(text.splitlines()):
        m = head.match(line)
        if m:
            ident = m.group(1)
            names.add(ident[len("_root_."):] if ident.startswith("_root_.") else ".".join(stack + [ident]))
    return names


def short_visible(full, text, module, owner):
    """Whether a bare short name in this file denotes `full`: the file is its module or declares
    its namespace, or opens it (and admits the name), and declares no other theorem of that short
    name (which the bare name would denote instead)."""
    full = source_name(full)
    ns, short = full.rsplit(".", 1)
    if any(n != full and n.rsplit(".", 1)[-1] == short for n in declared_names(text)):
        return False
    if module == owner or ns in namespaces(text):
        return True
    if module is not None and owner is not None and module != owner and is_private(full):
        return False
    parts = ns.split(".")
    admitted = opens(text)
    for i in range(len(parts)):
        rule = admitted.get(".".join(parts[i:]), False)
        if rule is None or (isinstance(rule, set) and short in rule) or \
                (isinstance(rule, tuple) and short not in rule[1]):
            return True
    return False


def name_pattern(full, short_ok):
    """Mentions of `full` (never a declaration's own name): any suffix with a namespace component,
    or, when visible, the bare name."""
    parts = source_name(full).split(".")
    forms = [".".join(parts[i:]) for i in range(len(parts) - (0 if short_ok else 1))]
    if is_private(full):
        forms.append(full)
    alternation = "|".join(re.escape(f) for f in sorted(set(forms), key=len, reverse=True))
    return re.compile(r"(?<![\w.'])(?<!theorem )(?<!lemma )(?<!def )(?:_root_\.)?(?:" + alternation + r")(?![\w'])")


def without(text, span):
    """The text with the span removed, closing the seam to one blank line."""
    if span is None:
        return text
    before, after = text[:span[0]].rstrip("\n"), text[span[1]:].lstrip("\n")
    return before + ("\n\n" if before and after else "\n") + after


def declaration_span(text, full):
    """(start, end) of the theorem whose full source-level name is `full`, with its docstring and
    attributes, or None: scopes are tracked (`scoped_lines`), so the same short name in another
    namespace is never taken; the span ends before the next line that starts in column 0."""
    target = source_name(full)
    lines = text.splitlines(keepends=True)
    head = re.compile(r"^(?:@\[[^\]]*\]\s*)?" + MODIFIERS + r"(?:theorem|lemma)\s+((?:_root_\.)?[\w.']+)")
    for i, line, stack in scoped_lines(lines):
        m = head.match(line)
        if not m:
            continue
        ident = m.group(1)
        resolved = ident[len("_root_."):] if ident.startswith("_root_.") else ".".join(stack + [ident])
        if resolved != target:
            continue
        start = i
        while start > 0 and lines[start - 1].startswith("@["):
            start -= 1
        if start > 0 and lines[start - 1].rstrip().endswith("-/"):
            j = start - 1
            while j > 0 and not lines[j].lstrip().startswith("/-"):
                j -= 1
            if lines[j].startswith("/--"):
                start = j
                while start > 0 and lines[start - 1].startswith("@["):
                    start -= 1
        end = i + 1
        while end < len(lines) and (not lines[end].strip() or lines[end][0] in " \t"):
            end += 1
        offset = lambda n: sum(len(x) for x in lines[:n])
        return offset(start), offset(end)
    return None


def code_only(text):
    """The text with its comments blanked (offsets kept): a mention in a comment needs no import
    and constrains no declaration order."""
    blank = lambda m: re.sub(r"[^\n]", " ", m.group(0))
    return re.sub(r"--[^\n]*", blank, re.sub(r"/-[\s\S]*?-/", blank, text))


def mentions(full, text, module, owner):
    """The positions in the code of `text` that refer to `full`, outside its own declaration."""
    span = declaration_span(text, full) if module == owner else None
    pattern = name_pattern(full, short_visible(full, text, module, owner))
    return [m.start() for m in pattern.finditer(code_only(text)) if not (span and span[0] <= m.start() < span[1])]


def users_of(full, owner, sources):
    """Modules that mention `full` outside its own declaration (a private theorem: its own only)."""
    scope = {owner: sources[owner]} if is_private(full) else sources
    return {m for m, t in scope.items() if mentions(full, t, m, owner)}


def add_import(text, module):
    found = list(re.finditer(r"^(public\s+)?import\s+\S+\n", text, re.M))
    if not found or module in imports_of(text):
        return text
    last = found[-1]
    return text[:last.end()] + f"{last.group(1) or ''}import {module}\n" + text[last.end():]


def outer_files():
    """{path: (text, module name)} of the Lean files outside the library (bridge, core scripts)."""
    files = {}
    for pattern in OUTER_LEAN:
        for path in sorted(repo.ROOT.glob(pattern)):
            rel = str(path.relative_to(repo.ROOT))
            root = repo.ROOT / rel.split("/")[0]
            files[rel] = (path.read_text(), ".".join(path.relative_to(root).with_suffix("").parts))
    return files


def outer_reach(rel, outer, deps, seen=None):
    """The research modules an outer Lean file reaches through its imports, following the other
    outer files it imports (the bridge's own modules)."""
    seen = seen if seen is not None else set()
    if rel in seen:
        return set()
    seen.add(rel)
    reach = set()
    by_module = {mod: r for r, (_, mod) in outer.items()}
    for imported in imports_of(outer[rel][0]):
        if imported in deps:
            reach |= {imported} | deps[imported]
        elif imported in by_module:
            reach |= outer_reach(by_module[imported], outer, deps, seen)
    return reach


def plan(groups, sources=None, exact=None):
    """{"keep": [...], "manual": [...]}: per group the canonical theorem, the removed ones and the
    modules that must import the canonical module. Groups are decided one after another on the
    import graph as the earlier decisions leave it, so two decisions never import each other."""
    sources = sources or {m: p.read_text() for m, p in lean_modules().items()}
    deps = dependencies(sources)
    published = published_names()
    outer = outer_files()
    keep, manual, found = [], [], {}

    def users(name, owner):
        if (name, owner) not in found:
            found[name, owner] = users_of(name, owner, sources)
        return found[name, owner]

    def option(canon, members):
        removed = [mn for mn in members if mn != canon]
        using = sorted({u for m, name in removed for u in users(name, m)} - {canon[0]})
        text = sources[canon[0]]
        span = declaration_span(text, canon[1])
        body = text[span[0]:span[1]] if span else ""
        wrapper = span is None or any(name_pattern(n, short_visible(n, text, canon[0], m)).search(body)
                                      for m, n in removed)
        # A reference the canonical takes over in its own file must come after its declaration.
        early = span is not None and any(p < span[1] for m, n in removed for p in mentions(n, text, canon[0], m))
        cycle = [u for u in using if u in deps.get(canon[0], ())]
        # A Lean file outside the library that names a removed theorem must reach the canonical's
        # module through its imports (it gets no import added).
        for rel, (text_o, _) in outer.items():
            if any(not is_private(n) and mentions(n, text_o, None, m) for m, n in removed) and \
                    canon[0] not in outer_reach(rel, outer, deps):
                cycle.append(rel)
        # A private canonical used outside its module is promoted to public: visibility only widens.
        # (or when a removed member is public: prose, glossaries and the bridge may name it).
        promote = is_private(canon[1]) and (bool(using) or any(not is_private(n) for _, n in removed))
        clash = sorted(m for m, t in sources.items() if m != canon[0] and source_name(canon[1]) in declared_names(t)) \
            if promote else []
        imports = [u for u in using if canon[0] not in deps.get(u, ())]
        rank = (bool(cycle) or bool(clash), wrapper, early, promote, is_private(canon[1]), len(imports), canon[1] not in published,
                canon[1].endswith("_prop"), len(canon[1]), canon[1])
        return rank, {"canonical": canon[1], "module": canon[0],
                      "removed": [{"module": m, "name": n} for m, n in removed], "imports": imports,
                      **({"cycle": cycle} if cycle else {}), **({"wrapper": True} if wrapper else {}),
                      **({"early": True} if early else {}), **({"promote": True} if promote else {}),
                      **({"clash": clash} if clash else {})}

    ordered = sorted(groups.items(), key=lambda kv: (len({m for m, _ in kv[1]}) > 1, kv[0]))
    for k, members in ordered:
        rank, row = min((option(c, members) for c in members), key=lambda o: o[0])
        row = dict(statement=k, **row)
        if exact and len({exact.get(n) for _, n in members}) > 1:
            # Same statement, different binder info: references pass arguments differently, so a
            # rename is not enough; a person aligns the binders first.
            row["binders"] = True
        if any(row.get(flag) for flag in ("cycle", "clash", "wrapper", "early", "binders")):
            manual.append(row)
            continue
        keep.append(row)
        for user in row["imports"]:
            gained = {row["module"]} | deps.get(row["module"], set())
            for m in deps:
                if m == user or user in deps[m]:
                    deps[m] = deps[m] | gained
    return {"keep": keep, "manual": manual}


def stale_sheets(planned):
    """The interface sheets to regenerate after a consolidation: every sheet, since a sheet lists
    the theorems about each notion with counts, which a removal changes even where no removed
    name is printed (generated files are regenerated, never patched)."""
    if not planned["keep"]:
        return []
    return sorted(p.stem for p in (repo.ROOT / "interfaces").glob("*.md") if p.stem != "README")


def apply(planned):
    """Edit the sources as planned; returns the touched files (repository-relative). Idempotent:
    a declaration already removed is skipped and its references are still rewritten."""
    sources = {m: p.read_text() for m, p in lean_modules().items()}
    deps = dependencies(sources)
    texts = dict(sources)
    outer = {str(p.relative_to(repo.ROOT)): p.read_text() for g in OUTER_LEAN for p in sorted(repo.ROOT.glob(g))}
    original_outer = dict(outer)
    other = {}
    for rel in REFERENCING:
        if (repo.ROOT / rel).exists():
            other[rel] = (repo.ROOT / rel).read_text()
    for pattern in REFERENCING_GLOBS:
        for path in sorted(repo.ROOT.glob(pattern)):
            other[str(path.relative_to(repo.ROOT))] = path.read_text()
    original_other = dict(other)
    for row in planned["keep"]:
        canon = source_name(row["canonical"])
        if row.get("promote"):
            text = texts[row["module"]]
            span = declaration_span(text, row["canonical"])
            if span is not None:
                segment = text[span[0]:span[1]]
                head = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:[a-z]+\s+)*?(private\s+)(?=" + MODIFIERS
                                  + r"(?:theorem|lemma)\s)", re.M)
                found = head.search(code_only(segment))
                if found:
                    segment = segment[:found.start(1)] + segment[found.end(1):]
                texts[row["module"]] = text[:span[0]] + segment + text[span[1]:]
        for gone in row["removed"]:
            full, owner = gone["name"], gone["module"]
            texts[owner] = without(texts[owner], declaration_span(texts[owner], full))
            scope = [owner] if is_private(full) else list(texts)
            for m in scope:
                texts[m] = name_pattern(full, short_visible(full, texts[m], m, owner)).sub(canon, texts[m])
            if is_private(full):
                continue
            for rel in outer:
                outer[rel] = name_pattern(full, short_visible(full, outer[rel], None, owner)).sub(canon, outer[rel])
            # A glossary entry naming the removed theorem: its denotation module must reach the
            # canonical's module (it is repointed when it does not).
            entry = re.compile(r'^module = "([^"]*)"(\s*\nname = )"' + re.escape(full) + '"', re.M)
            reach = lambda m: m == row["module"] or row["module"] in deps.get(m, ())
            qualified = name_pattern(full, False)
            for rel in other:
                if "/glossary/" in rel:
                    other[rel] = entry.sub(lambda e: f'module = "{e.group(1) if reach(e.group(1)) else row["module"]}"'
                                                     f'{e.group(2)}"{canon}"', other[rel])
                other[rel] = qualified.sub(canon, other[rel])
        for user in row["imports"]:
            texts[user] = add_import(texts[user], row["module"])
    touched = []
    for m, t in texts.items():
        if t != sources[m]:
            module_path(m).write_text(t)
            touched.append(str(module_path(m).relative_to(repo.ROOT)))
    for rel, t in list(outer.items()) + list(other.items()):
        if t != (original_outer.get(rel) if rel in original_outer else original_other.get(rel)):
            (repo.ROOT / rel).write_text(t)
            touched.append(rel)
    return sorted(touched)
