"""The runtime of `Presentation.lex.tex` and `Application.lex.tex`: the view
directory the workflow publishes, and the logo.

`render_view(out)` writes every artifact `presentationmodel.ARTIFACTS`
declares: the generated ones (the reduction tree, the register as text and
JSON, the README, the paper's statements with the PDF attestations, the
explainer, the Rule 30 picture) from the register, the paper and the model,
the copied ones from their sources (the modules, the sheets, the attested
PDFs), and the site with the view data embedded in it (the register, the
tree, the paper's statements, the panels, and the journeys as steps with
their poles, so the page opens on a choice of vantage and shows one step at a
time) so that `index.html` opened from the downloaded artifact needs no server
and no dependency; `check_journeys` refuses a step the model would. The
logo is Rule 30 itself: the first rows of the automaton from a single black
cell, with the center column (the object of Problem 1) in the accent colour;
`sync_logo` writes it and `check_logo` refuses a drifted one, like the
modules."""

from datetime import datetime, timezone
import json
import re
import shutil

from . import archmodel, designmodel, frontier, observermodel, repo, standardsmodel
from .presentationmodel import (APPLICATION_RECORD, ARTIFACTS, BRAND, EXPLAINER, JOURNEYS, JOURNEY_LABELS, NAV_ITEMS, NAV_PATTERNS,
                                NAVIGATIONS, OBLIGATION, PANELS, POLES, PUBLICATION, STATUS_MARKS, STEPS, VERIFICATIONS,
                                nav_problems, step_problems)

SITE = repo.ROOT / "rule30-api" / "site"
LOGO = SITE / "logo.svg"
TEMPLATE = SITE / "index.html"
DATA_OPEN = '<script id="r30-data" type="application/json">'
DATA_CLOSE = "</script>"
HEAD_CLOSE = "</head>"
# the design tokens (designmodel.css) live in the template between these
# markers, written by `api sync` and refused when drifted by `api check`
TOKENS_OPEN = '<style id="r30-tokens">\n'
TOKENS_CLOSE = "</style>"
# the loader hook of the visualizations: `view render` inlines every
# rule30-api/site/viz/*.js here, before the page's own script, so each can
# register window.r30viz[panelId] = function (slot, viewData) {...}
VIZ_DIR = SITE / "viz"
VIZ_OPEN = '<script id="r30-viz">'
VIZ_CLOSE = "</script>"

INK = "#14161a"
PAPER = "#f4f1ea"
ACCENT = "#e0a526"
# rows 0..PICTURE_ROWS-1 of the picture panel and of rule30.svg; the
# explainer's paragraph on reading the picture states the same number
PICTURE_ROWS = 48


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


def picture_svg(rows=PICTURE_ROWS, ink=INK, accent=ACCENT, background=PAPER):
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


def with_tokens(html, css=None):
    """The template with its token block replaced by the design model's CSS."""
    css = designmodel.css() if css is None else css
    start = html.index(TOKENS_OPEN) + len(TOKENS_OPEN)
    end = html.index(TOKENS_CLOSE, start)
    return html[:start] + css + html[end:]


def sync_logo():
    """The logo and the template's design tokens, both generated: `api sync`
    writes them, `api check` refuses a drifted one (`check_logo`)."""
    SITE.mkdir(parents=True, exist_ok=True)
    text = logo_svg()
    changed = not LOGO.exists() or LOGO.read_text() != text
    if changed:
        LOGO.write_text(text)
    html = TEMPLATE.read_text()
    tokens = with_tokens(html)
    if tokens != html:
        TEMPLATE.write_text(tokens)
        changed = True
    return {"logo": str(LOGO.relative_to(repo.ROOT)), "changed": changed}


def check_logo():
    if not LOGO.exists():
        return {"ok": False, "reason": "rule30-api/site/logo.svg is missing; run `bin/r30 api sync`"}
    if LOGO.read_text() != logo_svg():
        return {"ok": False, "reason": "rule30-api/site/logo.svg drifted; run `bin/r30 api sync`"}
    html = TEMPLATE.read_text()
    if with_tokens(html) != html:
        return {"ok": False, "reason": "the design tokens of rule30-api/site/index.html drifted from designmodel; run `bin/r30 api sync`"}
    return {"ok": True, "reason": None}


def viz_scripts():
    """The visualization scripts, in name order, as one inline block."""
    files = sorted(VIZ_DIR.glob("*.js")) if VIZ_DIR.exists() else []
    return "\n".join(f"/* viz/{f.name} */\n" + f.read_text().replace("</script", "<\\/script") for f in files)


def with_viz(html, scripts=None):
    """The template with the visualization scripts inlined at the loader hook."""
    scripts = viz_scripts() if scripts is None else scripts
    if VIZ_OPEN not in html:
        return html
    start = html.index(VIZ_OPEN) + len(VIZ_OPEN)
    end = html.index(VIZ_CLOSE, start)
    # the registry exists before any visualization registers into it
    return html[:start] + ("\nwindow.r30viz = window.r30viz || {};\n" + scripts + "\n" if scripts else "") + html[end:]


def provenance_summary(prov):
    """Per claim, what an evidence card opens in place: the Lean theorem, the
    lexeme, the research module and its kappa-label, from provenance.jsonld."""
    graph = {x["@id"]: x for x in prov.get("@graph", [])}
    out = {}
    for x in prov.get("@graph", []):
        if not x["@id"].startswith("r30:claim/"):
            continue
        row = {"status": x.get("r30:status")}
        theorem = graph.get(x.get("prov:wasDerivedFrom") or "")
        if theorem:
            row["lean"] = theorem.get("schema:name")
            module = graph.get(theorem.get("r30:module") or "")
            if module:
                row["module"] = module.get("schema:name")
                row["kappa"] = module.get("r30:kappa")
                row["kappaNote"] = module.get("r30:kappaSource") or module.get("r30:kappaNote")
        if x.get("r30:lexeme"):
            row["lexeme"] = x["r30:lexeme"]
        if x.get("r30:attestedBy"):
            row["attestation"] = x["r30:attestedBy"].rsplit("/", 1)[-1]
        out[x["schema:name"]] = row
    return out


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


def view_data(claims, rows, sheets, commit, paper=None, provenance=None):
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
        "poles": POLES,
        "steps": STEPS,
        "verifications": VERIFICATIONS,
        "navPatterns": NAV_PATTERNS,
        "navigations": NAVIGATIONS,
        "navItems": NAV_ITEMS,
        "journeyLabels": JOURNEY_LABELS,
        "explainer": EXPLAINER,
        "obligation": OBLIGATION,
        "pictureRows": PICTURE_ROWS,
        "picture": picture_svg(rows=PICTURE_ROWS, ink="var(--ink)", accent="var(--accent)", background=None),
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
        "standards": standardsmodel.rows(),
        "design": designmodel.view_data(),
        "observer": {k: v for k, v in observermodel.data(claims=claims).items() if k != "claims"},
        "provenance": provenance or {},
    }


def check_journeys(panels=PANELS, journeys=JOURNEYS, steps=None, claims=None):
    """Every panel of every journey is a panel the site renders, every
    journey belongs to a declared stakeholder, and the steps are the pedagogy
    `Presentation.lex.tex` decides (`presentationmodel.step_problems`: steps
    on panels of journeys, consecutive and linked, covering the poles in
    order, ending in verification, on declared evidence): the runtime's own
    check of `journeysThroughPanels`, `journeysOfStakeholders` and the step
    theorems, so a render cannot publish a journey whose step has no panel
    to show or no evidence to link; and the navigation theorems
    (`presentationmodel.nav_problems`), so every journey stays reachable from
    the primary navigation. Returns the problems, empty when none."""
    ids = {p["id"] for p in panels}
    stakeholders = {s["id"] for s in archmodel.STAKEHOLDERS}
    problems = []
    for j in journeys:
        for step in j["panels"]:
            if step not in ids:
                problems.append(f"journey {j['id']}: panel {step} is not rendered")
        if j["stakeholder"] not in stakeholders:
            problems.append(f"journey {j['id']}: stakeholder {j['stakeholder']} is not declared")
    claim_ids = [c["id"] for c in (frontier.list_claims() if claims is None else claims)]
    problems += step_problems(claim_ids, steps=STEPS if steps is None else steps, journeys=journeys, panels=panels)
    if steps is None:
        problems += nav_problems(journeys=journeys)
        problems += designmodel.problems(journeys, OBLIGATION)
    return problems


def embed(html, data, head=""):
    """The template with its data script filled (an embedded `</` is escaped
    so the JSON cannot close the script element) and, when given, `head`
    (the schema.org JSON-LD and Open Graph block) injected before `</head>`."""
    start = html.index(DATA_OPEN) + len(DATA_OPEN)
    end = html.index(DATA_CLOSE, start)
    payload = json.dumps(data, ensure_ascii=False, sort_keys=True).replace("</", "<\\/")
    html = html[:start] + payload + html[end:]
    if TOKENS_OPEN in html:
        html = with_viz(with_tokens(html))
    return html.replace(HEAD_CLOSE, head + HEAD_CLOSE, 1) if head and HEAD_CLOSE in html else html


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
    standardsmodel.citation_file()
    generated = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    prov = standardsmodel.provenance(claims, commit, generated, paper["attestation"])
    data = view_data(claims, rows, sheets, commit, paper, provenance_summary(prov))
    data["generated"] = generated
    jsonld = standardsmodel.schema_org(STEPS, JOURNEYS, archmodel.STAKEHOLDERS, commit, paper["pdfs"]["documents"])
    written = []
    from .vizmodel import publish as publish_viz; publish_viz(out)  # noqa: E702 (the visualizations' hook)
    for a in ARTIFACTS:
        target = out / a["path"]
        if a["id"] == "site":
            target.write_text(embed((repo.ROOT / a["source"]).read_text(), data,
                                    standardsmodel.head_block(jsonld, BRAND, PUBLICATION["url"])))
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
                              f"```\n{chain_text}\n```\n\nThe standards this view implements, with what realizes each and the check "
                              "behind it, are `standards.json`; `openapi.json` describes the command surface, `provenance.jsonld` "
                              "the provenance of every claim, `schema.json` the site for machines, `attestations.intoto.json` the "
                              "attested documents, `CITATION.cff` how to cite the work.\n")
        elif a["id"] == "standards":
            target.write_text(standardsmodel.artifacts_json())
        elif a["id"] == "openapi":
            target.write_text(repo.to_json(standardsmodel.openapi()) + "\n")
        elif a["id"] == "sitemap":
            target.write_text(standardsmodel.sitemap(STEPS, data["generated"][:10]))
        elif a["id"] == "robots":
            target.write_text(standardsmodel.robots())
        elif a["id"] == "provenance":
            target.write_text(repo.to_json(prov) + "\n")
        elif a["id"] == "tokens":
            target.write_text(designmodel.css())
        elif a["id"] == "jsonld":
            target.write_text(repo.to_json(jsonld) + "\n")
        elif a["id"] == "attestations":
            target.write_text(repo.to_json(standardsmodel.in_toto_statement(paper["pdfs"]["documents"], paper["attestation"], paper["pdfs"], commit)) + "\n")
        else:
            raise ValueError(f"no renderer for artifact {a['id']}")
        written.append(a["path"])
    return {"out": str(out), "written": written, "commit": commit, "claims": len(claims)}
