"""The combined lexicon: every glossary entry of both LexLean projects plus the
builtin core/std entries of the pinned LexLean, indexed by qualified id, by Lean
denotation and by surface."""

from dataclasses import dataclass, field
from pathlib import Path
import json
import tomllib

from . import repo

BUILTIN = Path(__file__).with_name("builtin_lexicon.json")


@dataclass
class Entry:
    qid: str
    category: str
    frame: str
    arity: int
    surface: str | None
    precedence: int | None = None
    associativity: str | None = None
    signature: str | None = None
    lean_name: str | None = None
    lean_module: str | None = None
    core_constructor: str | None = None
    path: Path | None = None
    project: str | None = None
    render_math: str | None = None

    @property
    def package(self):
        return self.qid.split("::")[0]

    @property
    def id(self):
        return self.qid.split("::")[1]

    def row(self):
        return {"id": self.qid, "surface": self.surface, "frame": self.frame, "arity": self.arity,
                "lean": self.lean_name, "category": self.category}


class Lexicon:
    def __init__(self):
        self.entries: dict[str, Entry] = {}
        self.by_lean: dict[str, list[Entry]] = {}
        self.imports: dict[str, list[str]] = {}
        self.lexicon_dir: dict[str, Path] = {}
        self.lexicon_project: dict[str, str] = {}
        self._load_builtin()
        for project, root in repo.PROJECTS.items():
            for lexicon_toml in sorted((root / "glossary").glob("*/lexicon.toml")):
                self._load_lexicon(project, lexicon_toml)

    def _load_builtin(self):
        data = json.loads(BUILTIN.read_text())
        self.builtin_revision = data["lexlean_revision"]
        for qid, e in data["entries"].items():
            den = e.get("denotation") or {}
            entry = Entry(qid, e.get("category"), e.get("frame"), e.get("arity") or 0,
                          e.get("surface"), e.get("precedence"), e.get("associativity"),
                          e.get("signature"), den.get("name"), den.get("module"),
                          den.get("constructor"), None, "builtin")
            self._add(entry)

    def _load_lexicon(self, project, lexicon_toml):
        meta = tomllib.loads(lexicon_toml.read_text())
        package = meta["package"]
        self.imports[package] = [i.split("@")[0] for i in meta.get("imports", [])]
        self.lexicon_dir[package] = lexicon_toml.parent
        self.lexicon_project[package] = project
        for path in sorted((lexicon_toml.parent / "entries").glob("*.toml")):
            e = tomllib.loads(path.read_text())
            forms = [f for f in e.get("form", []) if f.get("channel") == "math"]
            den = e.get("denotation") or {}
            entry = Entry(f"{package}::{e['id']}", e.get("category"), e.get("frame"),
                          e.get("surface_arity", 0), forms[0]["surface"] if forms else None,
                          e.get("precedence"), e.get("associativity"), e.get("signature"),
                          den.get("name"), den.get("module"), den.get("constructor"), path,
                          project, (e.get("render") or {}).get("math"))
            self._add(entry)

    def _add(self, entry):
        self.entries[entry.qid] = entry
        if entry.lean_name:
            self.by_lean.setdefault(entry.lean_name, []).append(entry)

    def get(self, qid):
        return self.entries.get(qid)

    def for_lean(self, name, visible=None):
        """The entry denoting a Lean constant, preferring one visible from `visible`."""
        found = self.by_lean.get(name, [])
        if visible is not None:
            for e in found:
                if e.package in visible or e.project == "builtin":
                    return e
        return found[0] if found else None

    def search(self, query, limit=40):
        q = query.lower()
        rows = []
        for e in self.entries.values():
            hay = " ".join(x for x in (e.qid, e.surface or "", e.lean_name or "") if x).lower()
            if q in hay:
                rows.append(e.row())
        rows.sort(key=lambda r: (len(r["id"]), r["id"]))
        return rows[:limit]

    def visible_from(self, package):
        """Packages whose entries a lexicon may reference: itself and its imports, transitively."""
        seen, todo = set(), [package]
        while todo:
            p = todo.pop()
            if p in seen:
                continue
            seen.add(p)
            todo.extend(self.imports.get(p, []))
        return seen

    def packages(self):
        return sorted(self.lexicon_dir)

    def lex_tex_files(self, package):
        root = repo.PROJECTS[self.lexicon_project[package]]
        return sorted((root / "src").glob("*.lex.tex"))
