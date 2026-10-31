"""The stakeholder view of the proof as LexLean modules.

`rule30-api/src/Presentation.lex.tex` declares the brand, the artifacts the
view workflow publishes, the panels of the site (the reduction tree, the
register, the open leaves, the interface sheets, the modules, the quality
measures) and the journey of each stakeholder through them, with decided
theorems that every panel is governed by a viewpoint of `Architecture`, every
journey belongs to a declared stakeholder, every artifact is produced by a
command of `Api`, and the published paths are distinct.

`rule30-api/src/Application.lex.tex` declares the application (name,
version, entry page, logo, workflow) and its publication (the view workflow
on every push to main, its artifact name, its command, its timeout), and
decides that the entry and the logo are published artifacts, that the
publication's command exists, that its timeout is within the quality
threshold of `Architecture`, and that the status marks the site uses cover
every status of `Register`.

`bin/r30 view render` is the runtime of these two modules: it writes the
artifacts into a directory from the same lists (`site.py`)."""

from . import repo
from .semantic import (BOOL, NAT, STR, all_members, b, ble, call, definition, field_of_each, holds, if_, index_of,
                       list_t, lst, match_list, member_string, n, named, proj, record, s, strings, structure, var)

PRESENTATION = repo.ROOT / "rule30-api" / "src" / "Presentation.lex.tex"
APPLICATION = repo.ROOT / "rule30-api" / "src" / "Application.lex.tex"

BRAND = {
    "name": "Centerline",
    "tagline": "Every arrow a theorem.",
    "description": "The current view of Wolfram's Rule 30 Prize, Problem 1: the reduction tree, the register, the interface sheets and the open leaves, rendered from the kernel-checked register on every push.",
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

PANELS = [
    {"id": "reduction-tree", "title": "Reduction tree", "viewpoint": "reduction", "artifact": "chain",
     "statement": "The register as a tree from problem1: proved arrows, open leaves, refuted routes."},
    {"id": "register", "title": "Register", "viewpoint": "evidence", "artifact": "register-json",
     "statement": "Every claim with its status, statement, Lean name and lexeme; filter by status, search by notion."},
    {"id": "open-leaves", "title": "Open leaves", "viewpoint": "reduction", "artifact": "register-json",
     "statement": "The open claims no open claim rests on: each is a sufficient condition for Problem 1 once the proved arrows above it are read upward."},
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
]

APPLICATION_RECORD = {
    "name": "rule30-api",
    "version": "0.1.0",
    "repository": "https://github.com/afflom/rule30",
    "entry": "index.html",
    "logo": "logo.svg",
    "workflow": ".github/workflows/view.yml",
}

PUBLICATION = {
    "workflow": ".github/workflows/view.yml",
    "trigger": "push to main",
    "artifactName": "rule30-current-view",
    "command": "view_render",
    "timeoutMinutes": 5,
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
    br_t, ar_t, pa_t, jo_t = named("Brand"), named("Artifact"), named("Panel"), named("Journey")
    return [
        structure("Brand", [("name", STR), ("tagline", STR), ("description", STR), ("logo", STR)]),
        structure("Artifact", [("id", STR), ("path", STR), ("mediaType", STR), ("command", STR)]),
        structure("Panel", [("id", STR), ("title", STR), ("viewpoint", STR), ("artifact", STR), ("statement", STR)]),
        structure("Journey", [("id", STR), ("stakeholder", STR), ("panels", list_t(STR))]),
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
        member_string(), all_members(), _distinct("distinctStrings"),
        field_of_each("artifactIds", ar_t, "id"),
        field_of_each("artifactPaths", ar_t, "path"),
        field_of_each("artifactCommands", ar_t, "command"),
        field_of_each("panelIds", pa_t, "id"),
        field_of_each("panelViewpoints", pa_t, "viewpoint"),
        field_of_each("panelArtifacts", pa_t, "artifact"),
        field_of_each("journeyStakeholders", jo_t, "stakeholder"),
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
        structure("Publication", [("workflow", STR), ("trigger", STR), ("artifactName", STR), ("command", STR), ("timeoutMinutes", NAT)]),
        structure("StatusMark", [("status", STR), ("mark", STR), ("label", STR)]),
        definition("application", ap_t, record("Application", **{k: s(v) for k, v in APPLICATION_RECORD.items()})),
        definition("publication", pu_t, record("Publication", workflow=s(PUBLICATION["workflow"]), trigger=s(PUBLICATION["trigger"]),
                                               artifactName=s(PUBLICATION["artifactName"]), command=s(PUBLICATION["command"]),
                                               timeoutMinutes=n(PUBLICATION["timeoutMinutes"]))),
        definition("statusMarks", list_t(sm_t), lst([
            record("StatusMark", status=s(m["status"]), mark=s(m["mark"]), label=s(m["label"])) for m in STATUS_MARKS], sm_t)),
        member_string(), all_members(),
        field_of_each("markStatuses", sm_t, "status"),
        field_of_each("claimStatuses", claim_t, "status"),
        holds("entryIsPublished",
              call("memberString", proj(call("application"), "entry"),
                   call("artifactPaths", call("artifacts", module="Presentation"), module="Presentation"))),
        holds("logoIsPublished",
              call("memberString", proj(call("application"), "logo"),
                   call("artifactPaths", call("artifacts", module="Presentation"), module="Presentation"))),
        holds("publicationCommandExists",
              call("memberString", proj(call("publication"), "command"),
                   call("commandNames", call("commands", module="Api"), module="Architecture"))),
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
