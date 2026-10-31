"""The runtime of `Presentation.lex.tex` and `Application.lex.tex`: the view
directory the workflow publishes, and the logo.

`render_view(out)` writes every artifact `presentationmodel.ARTIFACTS`
declares: the generated ones (the reduction tree, the register as text and
JSON, the README, the paper's statements with the PDF attestations, the
explainer, the Rule 30 picture) from the register, the paper and the model,
the copied ones from their sources (the modules, the sheets, the attested
PDFs), and the site with the view data embedded in it so that `index.html`
opened from the downloaded artifact needs no server and no dependency. The
logo is Rule 30 itself: the first rows of the automaton from a single black
cell, with the center column (the object of Problem 1) in the accent colour;
`sync_logo` writes it and `check_logo` refuses a drifted one, like the
modules."""

from datetime import datetime, timezone
import json
import re
import shutil

from . import archmodel, frontier, repo
from .presentationmodel import (APPLICATION_RECORD, ARTIFACTS, BRAND, EXPLAINER, JOURNEYS, OBLIGATION, PANELS,
                                PUBLICATION, STATUS_MARKS)

SITE = repo.ROOT / "rule30-api" / "site"
LOGO = SITE / "logo.svg"
TEMPLATE = SITE / "index.html"
DATA_OPEN = '<script id="r30-data" type="application/json">'
DATA_CLOSE = "</script>"

INK = "#14161a"
PAPER = "#f4f1ea"
ACCENT = "#e0a526"


def rule30_rows(count):
    """Rows 0..count-1 of Rule 30 from a single black cell, each as a list of
    bits over the cells -t..t (so row t has 2t+1 entries)."""
    rows = [[1]]
    for t in range(1, count):
        prev = rows[-1]
        wide = [0, 0] + prev + [0, 0]
        row = [wide[i - 1] ^ (wide[i] | wide[i + 1]) for i in range(1, len(wide) - 1)]
        rows.append(row)
    return rows


def logo_svg(rows=12):
    """An original mark: the Rule 30 triangle in a rounded tile, its center
    column in the accent colour."""
    grid = rule30_rows(rows)
    width = 2 * rows - 1
    size = 120
    cell = 104 / width
    left = (size - width * cell) / 2
    top = (size - rows * cell) / 2
    cells = []
    for t, row in enumerate(grid):
        offset = rows - 1 - t
        for i, bit in enumerate(row):
            if not bit:
                continue
            x = left + (offset + i) * cell
            y = top + t * cell
            fill = ACCENT if offset + i == rows - 1 else PAPER
            cells.append(f'<rect x="{x:.2f}" y="{y:.2f}" width="{cell - 0.6:.2f}" height="{cell - 0.6:.2f}" fill="{fill}"/>')
    return ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {size} {size}" width="{size}" height="{size}" role="img" '
            f'aria-labelledby="t d">\n<title id="t">{BRAND["name"]}</title>\n'
            f'<desc id="d">Rule 30 from a single black cell, rows 0 to {rows - 1}; the center column in amber.</desc>\n'
            f'<rect width="{size}" height="{size}" rx="22" fill="{INK}"/>\n' + "\n".join(cells) + "\n</svg>\n")


def picture_svg(rows=48, ink=INK, accent=ACCENT, background=PAPER):
    """The picture panel: a larger triangle than the logo, the center column
    highlighted. With CSS variables as colours it is inlined in the themed
    site; with literal colours it is the standalone `rule30.svg`."""
    grid = rule30_rows(rows)
    width = 2 * rows - 1
    cell = 10
    w, h = width * cell, rows * cell
    cells = []
    for t, row in enumerate(grid):
        offset = rows - 1 - t
        for i, bit in enumerate(row):
            if not bit:
                continue
            fill = accent if offset + i == rows - 1 else ink
            cells.append(f'<rect x="{(offset + i) * cell}" y="{t * cell}" width="{cell}" height="{cell}" fill="{fill}"/>')
    back = [f'<rect width="{w}" height="{h}" fill="{background}"/>'] if background else []
    head = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}" role="img" '
            'aria-labelledby="pt pd" shape-rendering="crispEdges">',
            f'<title id="pt">Rule 30, rows 0 to {rows - 1}</title>',
            f'<desc id="pd">Rule 30 from a single black cell, rows 0 to {rows - 1}; the center column highlighted.</desc>']
    return "\n".join(head + back + cells + ["</svg>"]) + "\n"


def sync_logo():
    SITE.mkdir(parents=True, exist_ok=True)
    text = logo_svg()
    changed = not LOGO.exists() or LOGO.read_text() != text
    if changed:
        LOGO.write_text(text)
    return {"logo": str(LOGO.relative_to(repo.ROOT)), "changed": changed}


def check_logo():
    if not LOGO.exists():
        return {"ok": False, "reason": "rule30-api/site/logo.svg is missing; run `bin/r30 api sync`"}
    ok = LOGO.read_text() == logo_svg()
    return {"ok": ok, "reason": None if ok else "rule30-api/site/logo.svg drifted; run `bin/r30 api sync`"}


def register_text(claims):
    return "\n".join(f"[{c['status']:7s}] {c['id']}: {c['statement']}" + (f"  ({c['lean']})" if c.get("lean") else "")
                     for c in claims) + "\n"


def commit_id():
    code, out, _ = repo.run(["git", "rev-parse", "HEAD"])
    return out.strip() if code == 0 else ""


PAPER_MODULE = repo.PROJECTS["paper"] / "src" / "Observations.lex.tex"
PDF_MANIFEST = repo.ROOT / "pdf-manifest.json"
PDF_PACKAGE = {"Paper": "Rule30-Paper.pdf", "Observations": "Rule30-Observations.pdf", "Core": "Rule30-Core.pdf"}
_BLOCK = re.compile(r"\\begin\{(theorem|lemma|corollary)\}\{([^}]*)\}(.*?)\\begin\{proof\}(.*?)\\end\{proof\}", re.S)
_SECTION = re.compile(r"\\begin\{section\}\{([^}]*)\}\s*(?:\\heading\{([^}]*)\})?")
_LEXEME = re.compile(r"\\lexeme\{([^}]*)\}")


def statements_of(path, lexicon):
    """The theorem, lemma and corollary blocks of a `.lex.tex` module as
    rows: id, kind, section, the controlled-English statement, the lexeme
    the proof closes the goal with, and from that glossary entry the Lean
    name and module (the denotation `theorem add` wrote)."""
    text = path.read_text()
    title = (re.search(r"\\title\{([^}]*)\}", text) or [None, ""])[1]
    boundaries = [(m.start(), m.group(1), m.group(2) or m.group(1)) for m in _SECTION.finditer(text)]
    sections = [{"id": sid, "heading": heading} for _, sid, heading in boundaries]
    rows = []
    for m in _BLOCK.finditer(text):
        section = next((sid for start, sid, _ in reversed(boundaries) if start < m.start()), None)
        statement = " ".join(line.strip() for line in m.group(3).splitlines()
                             if line.strip() and not line.strip().startswith("\\allowaxioms"))
        lexeme = next((q.group(1) for q in _LEXEME.finditer(m.group(4))), None)
        entry = lexicon.get(lexeme) if lexeme else None
        rows.append({"id": m.group(2), "kind": m.group(1), "section": section, "statement": statement,
                     "lean": entry.lean_name if entry else None, "leanModule": entry.lean_module if entry else None,
                     "lexeme": lexeme})
    return {"module": str(path.relative_to(repo.ROOT)), "title": title, "sections": sections, "statements": rows}


def attestation(project="paper"):
    """The latest accepted attestation of a LexLean project (`verified-latest`),
    reduced to its identifiers: what the gate verified and with what."""
    latest = repo.PROJECTS[project] / "verified-latest"
    found = sorted(latest.glob("*/attestation.json")) if latest.exists() else []
    if not found:
        return None
    a = json.loads(found[-1].read_text())
    return {"project": project, "id": a.get("attestation_id"), "spec": a.get("spec"), "sourceId": a.get("source_id"),
            "semanticId": a.get("semantic_id"), "lexlean": (a.get("lexlean") or {}).get("version"),
            "declarations": len(a.get("declarations") or [])}


def documents():
    """The attested PDFs as `pdf-manifest.json` lists them, with the published
    path of each (the view copies the PDFs beside the site)."""
    if not PDF_MANIFEST.exists():
        return {"generated": None, "sourceDigest": None, "documents": []}
    m = json.loads(PDF_MANIFEST.read_text())
    docs = [{"name": name, "path": PDF_PACKAGE.get(name), "pdfSha256": d.get("pdf_sha256"), "texSha256": d.get("tex_sha256")}
            for name, d in sorted((m.get("documents") or {}).items())]
    return {"generated": m.get("generated_at_utc"), "sourceDigest": m.get("source_digest"), "documents": docs}


def statements():
    """`statements.json`: the published statements of the paper's observation
    module as mathematics, with the attested PDFs and the attestation."""
    from .lexicon import Lexicon
    paper = statements_of(PAPER_MODULE, Lexicon())
    paper["pdfs"] = documents()
    paper["attestation"] = attestation("paper")
    return paper


def view_data(claims, rows, sheets, commit, paper=None):
    """Everything the site renders, as one JSON value: the register, the tree,
    the open leaves, the sheets present, the paper's statements, the explainer,
    the picture, and the presentation and architecture data the modules
    declare."""
    return {
        "brand": BRAND,
        "application": APPLICATION_RECORD,
        "publication": PUBLICATION,
        "commit": commit,
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "register": claims,
        "chain": rows,
        "openLeaves": frontier.open_leaves(),
        "sheets": sheets,
        "statusMarks": STATUS_MARKS,
        "panels": PANELS,
        "journeys": JOURNEYS,
        "explainer": EXPLAINER,
        "obligation": OBLIGATION,
        "picture": picture_svg(ink="var(--ink)", accent="var(--accent)", background=None),
        "statements": paper if paper is not None else statements(),
        "artifacts": [{k: a[k] for k in ("id", "path", "media", "command")} for a in ARTIFACTS],
        "conceptualModel": archmodel.CONCEPTUAL_MODEL,
        "stakeholders": archmodel.STAKEHOLDERS,
        "concerns": archmodel.CONCERNS,
        "viewpoints": archmodel.VIEWPOINTS,
        "views": archmodel.VIEWS,
        "characteristics": archmodel.CHARACTERISTICS,
        "subcharacteristics": archmodel.SUBCHARACTERISTICS,
        "requirements": archmodel.REQUIREMENTS,
        "measures": archmodel.MEASURES,
    }


def check_journeys(panels=PANELS, journeys=JOURNEYS):
    """Every step of every journey is a panel the site renders, and every
    journey belongs to a declared stakeholder: the runtime's own check of
    what `Presentation.lex.tex` decides (`journeysThroughPanels`,
    `journeysOfStakeholders`), so a render cannot publish a journey whose
    step has no section to scroll to. Returns the problems, empty when none."""
    ids = {p["id"] for p in panels}
    stakeholders = {s["id"] for s in archmodel.STAKEHOLDERS}
    problems = []
    for j in journeys:
        for step in j["panels"]:
            if step not in ids:
                problems.append(f"journey {j['id']}: panel {step} is not rendered")
        if j["stakeholder"] not in stakeholders:
            problems.append(f"journey {j['id']}: stakeholder {j['stakeholder']} is not declared")
    return problems


def embed(html, data):
    """The template with its data script filled (an embedded `</` is escaped
    so the JSON cannot close the script element)."""
    start = html.index(DATA_OPEN) + len(DATA_OPEN)
    end = html.index(DATA_CLOSE, start)
    payload = json.dumps(data, ensure_ascii=False, sort_keys=True).replace("</", "<\\/")
    return html[:start] + payload + html[end:]


def render_view(out):
    problems = check_journeys()
    if problems:
        raise ValueError("; ".join(problems))
    out.mkdir(parents=True, exist_ok=True)
    claims = frontier.list_claims()
    rows, chain_text = frontier.chain()
    commit = commit_id()
    paper = statements()
    sheets_dir = repo.ROOT / "interfaces"
    sheets = sorted(p.stem for p in sheets_dir.glob("*.md") if p.stem != "README") if sheets_dir.exists() else []
    written = []
    for a in ARTIFACTS:
        target = out / a["path"]
        if a["id"] == "site":
            target.write_text(embed((repo.ROOT / a["source"]).read_text(), view_data(claims, rows, sheets, commit, paper)))
        elif a["source"]:
            source = repo.ROOT / a["source"]
            if source.is_dir():
                if target.exists():
                    shutil.rmtree(target)
                shutil.copytree(source, target)
            else:
                shutil.copyfile(source, target)
        elif a["id"] == "chain":
            target.write_text(chain_text + "\n")
        elif a["id"] == "register-json":
            target.write_text(repo.to_json(claims) + "\n")
        elif a["id"] == "register-text":
            target.write_text(register_text(claims))
        elif a["id"] == "statements":
            target.write_text(repo.to_json(paper) + "\n")
        elif a["id"] == "explainer":
            target.write_text(repo.to_json(EXPLAINER) + "\n")
        elif a["id"] == "picture":
            target.write_text(picture_svg())
        elif a["id"] == "readme":
            target.write_text(f"# {BRAND['name']}: {BRAND['tagline']}\n\nRule 30 Prize, Problem 1: the current view.\n\n"
                              f"Commit: {commit}\n\nOpen `index.html` for the rendered view; `chain.txt` is the reduction tree:\n\n"
                              f"```\n{chain_text}\n```\n")
        else:
            raise ValueError(f"no renderer for artifact {a['id']}")
        written.append(a["path"])
    return {"out": str(out), "written": written, "commit": commit, "claims": len(claims)}
