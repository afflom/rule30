"""The stakeholder view of the proof as LexLean modules.

`rule30-api/src/Presentation.lex.tex` declares the brand, the artifacts the
view workflow publishes, the panels of the site (the Rule 30 picture, the
plain-language explainer, the reduction tree, the register, the open leaves,
the paper's statements, the open obligation, the refuted routes, the
interface sheets, the modules, the quality measures), the explainer's
paragraphs as data, the id of the open obligation, and the journey of each
stakeholder through the panels, with decided theorems that every panel is
governed by a viewpoint of `Architecture`, every journey belongs to a
declared stakeholder, every artifact is produced by a command of `Api`, the
published paths and the explainer's paragraph ids are distinct.

`rule30-api/src/Application.lex.tex` declares the application (name,
version, entry page, logo, workflow) and its publication (the view workflow
on every push to main, its artifact name, its command, its timeout, the
GitHub Pages environment and URL it deploys to), and decides that the entry
and the logo are published artifacts, that the publication's command exists,
that its workflow is the application's, that its timeout is within the
quality threshold of `Architecture`, that the obligation `Presentation`
names is an open claim of `Register`, and that the status marks the site
uses cover every status of `Register`.

`bin/r30 view render` is the runtime of these two modules: it writes the
artifacts into a directory from the same lists (`site.py`)."""

from . import repo
from .semantic import (BOOL, NAT, STR, all_members, b, ble, call, definition, eq_string, field_of_each, holds, if_,
                       index_of, list_t, lookup_field, lst, match_list, member_string, n, named, proj, record, s, strings,
                       structure, var)

PRESENTATION = repo.ROOT / "rule30-api" / "src" / "Presentation.lex.tex"
APPLICATION = repo.ROOT / "rule30-api" / "src" / "Application.lex.tex"

BRAND = {
    "name": "Centerline",
    "tagline": "Every arrow a theorem.",
    "description": "The current view of Wolfram's Rule 30 Prize, Problem 1: what is proved, what is open and what was refuted, rendered from the kernel-checked register on every push, with the paper's statements for the mathematician and a plain-language guide for everyone else.",
    "logo": "logo.svg",
}

# What the view workflow publishes, in the order it is written. `path` is the
# published path in the artifact; `source` the repository path it is copied
# from (None when the command generates it); `command` the r30 command whose
# output it is.
ARTIFACTS = [
    {"id": "chain", "path": "chain.txt", "media": "text/plain", "command": "chain", "source": None},
    {"id": "register-json", "path": "register.json", "media": "application/json", "command": "frontier_list", "source": None},
    {"id": "register-text", "path": "register.txt", "media": "text/plain", "command": "frontier_list", "source": None},
    {"id": "frontier", "path": "frontier.toml", "media": "application/toml", "command": "view_render", "source": "frontier.toml"},
    {"id": "interfaces", "path": "interfaces", "media": "text/markdown", "command": "interface", "source": "interfaces"},
    {"id": "statements", "path": "statements.json", "media": "application/json", "command": "view_render", "source": None},
    {"id": "explainer", "path": "explainer.json", "media": "application/json", "command": "view_render", "source": None},
    {"id": "picture", "path": "rule30.svg", "media": "image/svg+xml", "command": "view_render", "source": None},
    {"id": "paper-pdf", "path": "Rule30-Paper.pdf", "media": "application/pdf", "command": "view_render", "source": "Rule30-Paper.pdf"},
    {"id": "observations-pdf", "path": "Rule30-Observations.pdf", "media": "application/pdf", "command": "view_render", "source": "Rule30-Observations.pdf"},
    {"id": "core-pdf", "path": "Rule30-Core.pdf", "media": "application/pdf", "command": "view_render", "source": "Rule30-Core.pdf"},
    {"id": "pdf-manifest", "path": "pdf-manifest.json", "media": "application/json", "command": "view_render", "source": "pdf-manifest.json"},
    {"id": "api-module", "path": "Api.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Api.lex.tex"},
    {"id": "register-module", "path": "Register.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Register.lex.tex"},
    {"id": "architecture-module", "path": "Architecture.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Architecture.lex.tex"},
    {"id": "presentation-module", "path": "Presentation.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Presentation.lex.tex"},
    {"id": "application-module", "path": "Application.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Application.lex.tex"},
    {"id": "frontier-module", "path": "Frontier.lex.tex", "media": "text/x-lexlean", "command": "frontier_render", "source": "rule30-paper/src/Frontier.lex.tex"},
    {"id": "agents", "path": "AGENTS.md", "media": "text/markdown", "command": "view_render", "source": "AGENTS.md"},
    {"id": "strategy", "path": "STRATEGY.md", "media": "text/markdown", "command": "view_render", "source": "rule30-lexlean/STRATEGY.md"},
    {"id": "readme", "path": "README.md", "media": "text/markdown", "command": "view_render", "source": None},
    {"id": "logo", "path": "logo.svg", "media": "image/svg+xml", "command": "api_sync", "source": "rule30-api/site/logo.svg"},
    {"id": "site", "path": "index.html", "media": "text/html", "command": "view_render", "source": "rule30-api/site/index.html"},
]

# The open claim every proved reduction ends at (the register's "remaining
# obligation"); Application.lex.tex decides that it is an open claim.
OBLIGATION = "aperiodic-compensation"

PANELS = [
    {"id": "picture", "title": "Rule 30", "viewpoint": "plain", "artifact": "picture",
     "statement": "The first rows of Rule 30 from a single black cell; the center column, the object of Problem 1, in amber."},
    {"id": "explainer", "title": "In plain words", "viewpoint": "plain", "artifact": "explainer",
     "statement": "What Rule 30 is, what Problem 1 asks, what is proved here, what remains open, what kernel-checked means, and how to read the rest."},
    {"id": "reduction-tree", "title": "Reduction tree", "viewpoint": "reduction", "artifact": "chain",
     "statement": "The register as a tree from problem1: proved arrows, open leaves, refuted routes."},
    {"id": "register", "title": "Register", "viewpoint": "evidence", "artifact": "register-json",
     "statement": "Every claim with its status, statement, Lean name and lexeme; filter by status, search by notion."},
    {"id": "open-leaves", "title": "Open leaves", "viewpoint": "reduction", "artifact": "register-json",
     "statement": "The open claims no open claim rests on: each is a sufficient condition for Problem 1 once the proved arrows above it are read upward."},
    {"id": "paper", "title": "Paper", "viewpoint": "paper", "artifact": "statements",
     "statement": "Every published theorem of Observations.lex.tex in the paper's controlled English with its Lean name, lexeme and section; the attested PDFs with their digests."},
    {"id": "obligation", "title": "Open obligation", "viewpoint": "paper", "artifact": "register-json",
     "statement": "The open claim every proved reduction ends at, in full: statement, Lean predicate, exact forms, the chain to Problem 1 and what rests on it."},
    {"id": "refutations", "title": "Refuted routes", "viewpoint": "paper", "artifact": "register-json",
     "statement": "Each refuted claim with the Lean refutation or the experiment that refutes it."},
    {"id": "interface-sheets", "title": "Interface sheets", "viewpoint": "comprehension", "artifact": "interfaces",
     "statement": "The labeled sheet of the selected claim: chain, notions, exact facts, handles."},
    {"id": "modules", "title": "LexLean modules", "viewpoint": "stdlib", "artifact": "api-module",
     "statement": "The command surface, the register, the architecture and this presentation as verified semantic modules."},
    {"id": "quality", "title": "Quality", "viewpoint": "optimal", "artifact": "architecture-module",
     "statement": "The measures of an optimal implementation, each with its threshold and the command that reports it."},
]

JOURNEYS = [
    {"id": "prize-review", "stakeholder": "wolfram", "panels": ["reduction-tree", "register", "open-leaves"]},
    {"id": "research-session", "stakeholder": "researcher", "panels": ["open-leaves", "interface-sheets", "quality"]},
    {"id": "reading", "stakeholder": "community", "panels": ["reduction-tree", "interface-sheets", "register"]},
    {"id": "stdlib-feedback", "stakeholder": "uor-foundation", "panels": ["modules", "quality"]},
    {"id": "mathematics", "stakeholder": "mathematician", "panels": ["paper", "reduction-tree", "obligation", "refutations", "register"]},
    {"id": "first-visit", "stakeholder": "layperson", "panels": ["picture", "explainer", "reduction-tree"]},
]

# The plain-language panel, as data: short paragraphs a reader without Lean
# or LexLean can follow. `view render` writes them as explainer.json and the
# site renders them; the tests refuse formal vocabulary in them.
EXPLAINER = [
    {"id": "rule-30", "title": "What Rule 30 is",
     "text": "Rule 30 is a one-line machine. Start with a row of cells, all white except one black cell in the middle. To make the next row, look at each cell together with its left and right neighbours. If the left neighbour is black, the cell below turns black only when the cell and its right neighbour are both white; if the left neighbour is white, the cell below turns black when the cell or its right neighbour is black. Repeat, row after row, forever. The picture above shows the first rows: a regular pattern grows on the left and a tangled one on the right."},
    {"id": "center-column", "title": "The center column",
     "text": "Read the cells straight down from the first black cell: black, black, white, black, black, black, white, white, black, black, white, white, white, black, white, black, and so on. This list of blacks and whites is the center column. It looks random. Nobody has found a pattern in it, and nobody has proved that there is none."},
    {"id": "problem-1", "title": "What Problem 1 asks",
     "text": "Stephen Wolfram's Rule 30 Prize asks three questions about the center column. Problem 1 asks whether it ever settles into a repeating pattern: whether there is a point after which the same block of blacks and whites repeats forever. The statement to be proved is that it never does."},
    {"id": "what-is-proved", "title": "What is proved here",
     "text": "This work has not solved Problem 1. What it has done is prove, in a form a computer checks, that Problem 1 is the same question as several other, more concrete questions. Each proved arrow in the reduction tree below says: if you could prove the statement at the arrow's end, Problem 1 would follow. The main ones are these."},
    {"id": "reduction-collisions", "title": "Collisions at the center",
     "text": "If the center column repeated with some period, disturbances travelling in from the left and from the right would have to keep meeting at the center forever, in a band of fixed width. Problem 1 is the same as saying that they cannot keep meeting."},
    {"id": "reduction-edges", "title": "The edges are simple",
     "text": "The center column is the exact combination of two parts: one coming from the two straight edges of the triangle and one from its interior. The edge part turns out to be nothing but whether the row number is even or odd. So Problem 1 is the same as saying that the interior part never settles into a repeating pattern."},
    {"id": "reduction-bands", "title": "Stripping the bands",
     "text": "A few diagonals next to each edge carry known, regular rhythms, and they can be removed exactly. What is left is the deep interior. Problem 1 is the same as saying that the deep interior is never a simple ruler-like rhythm plus a repeating pattern. That last statement is the remaining obligation."},
    {"id": "reduction-sparse", "title": "A sparser sequence is enough",
     "text": "If the center column repeated, then the column read only at rows 1, 2, 4, 8, 16 and so on would also eventually repeat. So it is enough to show that this far sparser sequence does not, and the same holds for the responses read along that diagonal. These are the open leaves on the right of the tree."},
    {"id": "reduction-horizon", "title": "A checked certificate",
     "text": "For every candidate starting point up to 512 and every candidate period up to 128, the computer checked that the center column breaks the pattern within 32 rows. This does not settle Problem 1, which asks about every starting point and every period, but it is a verified fact about the ranges it covers."},
    {"id": "what-is-open", "title": "What remains open",
     "text": "The register names one remaining obligation, aperiodic-compensation. Roughly: the deep interior of the triangle, with the bands next to both edges stripped away, never settles into a ruler-like rhythm plus a repeating pattern. Proving it would close Problem 1, and so would proving any other open leaf of the tree, such as the sparser sequences above. Nobody knows how yet. Several tempting routes were tried and shown not to work; those are the refuted routes, kept so that nobody walks them again."},
    {"id": "kernel-checked", "title": "What kernel-checked means",
     "text": "Every proved statement here was written in a proof language called Lean and checked by its kernel, a small program that accepts a proof only when every step follows from the rules. A reader can misread a long argument; the kernel does not. Kernel-checked means the proof passed that check, using only two standard logical principles and no extra assumptions. The statements are also written in a controlled English that is itself translated to Lean and checked, so the sentence you read and the theorem the kernel checked are the same thing."},
    {"id": "how-to-read", "title": "How to read this site",
     "text": "The reduction tree is the map: Problem 1 at the top and, below it, the statements it has been reduced to. A check mark is a proved arrow, a question mark an open statement, a cross a route that was tried and refuted. The register lists every statement with its status; select one for its details. The open leaves are where work continues. The paper panel has every published theorem in full, with the PDFs. The other panels are for people working on the proof or on its tooling."},
]

APPLICATION_RECORD = {
    "name": "rule30-api",
    "version": "0.1.0",
    "repository": "https://github.com/afflom/rule30",
    "entry": "index.html",
    "logo": "logo.svg",
    "workflow": ".github/workflows/view.yml",
}

# The view workflow: it renders the view, keeps it as the named artifact,
# and deploys it to GitHub Pages in the named environment; the site at `url`
# embeds the commit it was rendered from, which the workflow checks after
# the deployment.
PUBLICATION = {
    "workflow": ".github/workflows/view.yml",
    "trigger": "push to main",
    "artifactName": "rule30-current-view",
    "command": "view_render",
    "timeoutMinutes": 5,
    "environment": "github-pages",
    "url": "https://afflom.github.io/rule30/",
}

STATUS_MARKS = [
    {"status": "open", "mark": "?", "label": "open: a claim to work on"},
    {"status": "proved", "mark": "✓", "label": "proved: kernel-checked under propext and Quot.sound and published"},
    {"status": "refuted", "mark": "✗", "label": "refuted: a route not to be walked again"},
    {"status": "retired", "mark": "-", "label": "retired: superseded by an exact restatement"},
]


def _distinct(name):
    return definition(name, BOOL,
                      match_list(var("xs"), b(True), "head", "tail",
                                 if_(call("memberString", var("head"), var("tail")), b(False), call(name, var("tail")))),
                      parameters=[("xs", list_t(STR))], recursive="xs")


def presentation_declarations():
    br_t, ar_t, pa_t, jo_t, pg_t = named("Brand"), named("Artifact"), named("Panel"), named("Journey"), named("Paragraph")
    return [
        structure("Brand", [("name", STR), ("tagline", STR), ("description", STR), ("logo", STR)]),
        structure("Artifact", [("id", STR), ("path", STR), ("mediaType", STR), ("command", STR)]),
        structure("Panel", [("id", STR), ("title", STR), ("viewpoint", STR), ("artifact", STR), ("statement", STR)]),
        structure("Journey", [("id", STR), ("stakeholder", STR), ("panels", list_t(STR))]),
        structure("Paragraph", [("id", STR), ("title", STR), ("text", STR)]),
        definition("brand", br_t, record("Brand", **{k: s(v) for k, v in BRAND.items()})),
        definition("artifacts", list_t(ar_t), lst([
            record("Artifact", id=s(a["id"]), path=s(a["path"]), mediaType=s(a["media"]), command=s(a["command"]))
            for a in ARTIFACTS], ar_t)),
        definition("panels", list_t(pa_t), lst([
            record("Panel", id=s(p["id"]), title=s(p["title"]), viewpoint=s(p["viewpoint"]), artifact=s(p["artifact"]),
                   statement=s(p["statement"])) for p in PANELS], pa_t)),
        definition("journeys", list_t(jo_t), lst([
            record("Journey", id=s(j["id"]), stakeholder=s(j["stakeholder"]), panels=strings(j["panels"]))
            for j in JOURNEYS], jo_t)),
        definition("explainer", list_t(pg_t), lst([
            record("Paragraph", id=s(e["id"]), title=s(e["title"]), text=s(e["text"])) for e in EXPLAINER], pg_t)),
        definition("obligation", STR, s(OBLIGATION)),
        member_string(), all_members(), _distinct("distinctStrings"),
        field_of_each("artifactIds", ar_t, "id"),
        field_of_each("artifactPaths", ar_t, "path"),
        field_of_each("artifactCommands", ar_t, "command"),
        field_of_each("panelIds", pa_t, "id"),
        field_of_each("panelViewpoints", pa_t, "viewpoint"),
        field_of_each("panelArtifacts", pa_t, "artifact"),
        field_of_each("journeyStakeholders", jo_t, "stakeholder"),
        field_of_each("paragraphIds", pg_t, "id"),
        definition("journeyPanels", list_t(STR),
                   match_list(var("js"), {"kind": "nil", "element": STR}, "head", "tail",
                              call("appendStrings", proj(var("head"), "panels"), call("journeyPanels", var("tail")))),
                   parameters=[("js", list_t(jo_t))], recursive="js"),
        holds("panelsGovernedByViewpoints",
              call("allMembers", call("panelViewpoints", call("panels")),
                   call("viewpointIds", call("viewpoints", module="Architecture"), module="Architecture"))),
        holds("panelsReadArtifacts", call("allMembers", call("panelArtifacts", call("panels")), call("artifactIds", call("artifacts")))),
        holds("journeysOfStakeholders",
              call("allMembers", call("journeyStakeholders", call("journeys")),
                   call("stakeholderIds", call("stakeholders", module="Architecture"), module="Architecture"))),
        holds("journeysThroughPanels", call("allMembers", call("journeyPanels", call("journeys")), call("panelIds", call("panels")))),
        holds("everyPanelInAJourney", call("allMembers", call("panelIds", call("panels")), call("journeyPanels", call("journeys")))),
        holds("artifactsByCommands",
              call("allMembers", call("artifactCommands", call("artifacts")),
                   call("commandNames", call("commands", module="Api"), module="Architecture"))),
        holds("artifactPathsDistinct", call("distinctStrings", call("artifactPaths", call("artifacts")))),
        holds("artifactIdsDistinct", call("distinctStrings", call("artifactIds", call("artifacts")))),
        holds("paragraphIdsDistinct", call("distinctStrings", call("paragraphIds", call("explainer")))),
    ]


def _append_strings():
    return definition("appendStrings", list_t(STR),
                      match_list(var("xs"), var("ys"), "head", "tail",
                                 {"kind": "cons", "head": var("head"), "tail": call("appendStrings", var("tail"), var("ys"))}),
                      parameters=[("xs", list_t(STR)), ("ys", list_t(STR))], recursive="xs")


def application_declarations():
    ap_t, pu_t, sm_t = named("Application"), named("Publication"), named("StatusMark")
    claim_t = named("Claim", "Register")
    return [
        structure("Application", [("name", STR), ("version", STR), ("repository", STR), ("entry", STR), ("logo", STR), ("workflow", STR)]),
        structure("Publication", [("workflow", STR), ("trigger", STR), ("artifactName", STR), ("command", STR), ("timeoutMinutes", NAT),
                                  ("environment", STR), ("url", STR)]),
        structure("StatusMark", [("status", STR), ("mark", STR), ("label", STR)]),
        definition("application", ap_t, record("Application", **{k: s(v) for k, v in APPLICATION_RECORD.items()})),
        definition("publication", pu_t, record("Publication", workflow=s(PUBLICATION["workflow"]), trigger=s(PUBLICATION["trigger"]),
                                               artifactName=s(PUBLICATION["artifactName"]), command=s(PUBLICATION["command"]),
                                               timeoutMinutes=n(PUBLICATION["timeoutMinutes"]),
                                               environment=s(PUBLICATION["environment"]), url=s(PUBLICATION["url"]))),
        definition("statusMarks", list_t(sm_t), lst([
            record("StatusMark", status=s(m["status"]), mark=s(m["mark"]), label=s(m["label"])) for m in STATUS_MARKS], sm_t)),
        member_string(), all_members(),
        field_of_each("markStatuses", sm_t, "status"),
        field_of_each("claimStatuses", claim_t, "status"),
        lookup_field("claimStatus", claim_t, "id", "status", STR, s("")),
        holds("entryIsPublished",
              call("memberString", proj(call("application"), "entry"),
                   call("artifactPaths", call("artifacts", module="Presentation"), module="Presentation"))),
        holds("logoIsPublished",
              call("memberString", proj(call("application"), "logo"),
                   call("artifactPaths", call("artifacts", module="Presentation"), module="Presentation"))),
        holds("publicationCommandExists",
              call("memberString", proj(call("publication"), "command"),
                   call("commandNames", call("commands", module="Api"), module="Architecture"))),
        holds("publicationIsTheApplicationWorkflow",
              eq_string(proj(call("publication"), "workflow"), proj(call("application"), "workflow"))),
        holds("obligationIsOpen",
              eq_string(call("claimStatus", call("obligation", module="Presentation"), call("claims", module="Register")), s("open"))),
        holds("publicationWithinBudget",
              ble(proj(call("publication"), "timeoutMinutes"),
                  call("measureThreshold", s("ci-render-time"), call("measures", module="Architecture"), module="Architecture"))),
        holds("statusMarksCoverRegister",
              call("allMembers", call("claimStatuses", call("claims", module="Register")), call("markStatuses", call("statusMarks")))),
    ]


def render_presentation():
    from . import lexmod
    decls = presentation_declarations()
    # appendStrings precedes journeyPanels (no forward references)
    i = next(k for k, d in enumerate(decls) if d["name"] == "journeyPanels")
    decls.insert(i, _append_strings())
    return lexmod.module("Presentation", decls, imports=["Api", "Architecture"])


def render_application():
    from . import lexmod
    return lexmod.module("Application", application_declarations(), imports=["Api", "Architecture", "Presentation", "Register"])


def _write(path, text):
    changed = not path.exists() or path.read_text() != text
    if changed:
        path.write_text(text)
    return changed


def sync():
    PRESENTATION.parent.mkdir(parents=True, exist_ok=True)
    p = _write(PRESENTATION, render_presentation())
    a = _write(APPLICATION, render_application())
    return {"module": str(PRESENTATION.relative_to(repo.ROOT)), "panels": len(PANELS), "changed": p or a}


def check():
    for path, text in ((PRESENTATION, render_presentation()), (APPLICATION, render_application())):
        if not path.exists():
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} is missing; run `bin/r30 api sync`"}
        if path.read_text() != text:
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} drifted; run `bin/r30 api sync`"}
    return {"ok": True, "reason": None}
