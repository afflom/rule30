"""The runtime of `Presentation.lex.tex` and `Application.lex.tex`: the view
directory the workflow publishes, and the logo.

`render_view(out)` writes every artifact `presentationmodel.ARTIFACTS`
declares: the generated ones (the reduction tree, the register as text and
JSON, the README) from the register, the copied ones from their sources, and
the site with the view data embedded in it so that `index.html` opened from
the downloaded artifact needs no server and no dependency. The logo is Rule
30 itself: the first rows of the automaton from a single black cell, with the
center column (the object of Problem 1) in the accent colour; `sync_logo`
writes it and `check_logo` refuses a drifted one, like the modules."""

from datetime import datetime, timezone
import json
import shutil

from . import archmodel, frontier, repo
from .presentationmodel import (APPLICATION_RECORD, ARTIFACTS, BRAND, JOURNEYS, PANELS, PUBLICATION, STATUS_MARKS)

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


def view_data(claims, rows, sheets, commit):
    """Everything the site renders, as one JSON value: the register, the tree,
    the open leaves, the sheets present, and the presentation and architecture
    data the modules declare."""
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
    sheets_dir = repo.ROOT / "interfaces"
    sheets = sorted(p.stem for p in sheets_dir.glob("*.md") if p.stem != "README") if sheets_dir.exists() else []
    written = []
    for a in ARTIFACTS:
        target = out / a["path"]
        if a["id"] == "site":
            target.write_text(embed((repo.ROOT / a["source"]).read_text(), view_data(claims, rows, sheets, commit)))
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
        elif a["id"] == "readme":
            target.write_text(f"# {BRAND['name']}: {BRAND['tagline']}\n\nRule 30 Prize, Problem 1: the current view.\n\n"
                              f"Commit: {commit}\n\nOpen `index.html` for the rendered view; `chain.txt` is the reduction tree:\n\n"
                              f"```\n{chain_text}\n```\n")
        else:
            raise ValueError(f"no renderer for artifact {a['id']}")
        written.append(a["path"])
    return {"out": str(out), "written": written, "commit": commit, "claims": len(claims)}
