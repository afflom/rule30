"""The Observer as a LexLean semantic module.

`rule30-api/src/Observer.lex.tex` records, as data with decided theorems,
what the site, the register and the views implement of the object quadruple
(Harman's object-oriented ontology in the UOR framework: every object has a
withdrawn real object RO, a sensual object SO as it appears from a vantage,
real qualities RQ invariant across vantages, and sensual qualities SQ that
depend on the vantage; RO·SO is the part of the real object a vantage sees,
objects interact only vicariously through shared sensual qualities, and an
automorphism of the algebra keeps RQ and transforms SQ). Here:

- the object is the conceptual model of `Architecture` (Problem 1) and the
  real object is the proof of it: the root claim of the register, whose
  withdrawn core is the open obligation `aperiodic-compensation`;
- each journey of `Presentation` is a sensual object (a vantage);
- the real qualities visible from a vantage are the proved claims its panels
  render: a panel presenting an artifact that carries the register (the
  tree, the register, the Register and Frontier modules, which the modules
  panel lists) renders every proved claim, the interface sheets render the
  selected claim with the proved chain above it (the open leaves are what a
  sheet is written for), the open leaves show only withdrawn claims; the `Overlap` rows are exactly these pairs;
- the sensual qualities are the panels of the journey, and two vantages
  interact through the panels they share (`Interaction` rows);
- the withdrawn ids are the open claims, of which no panel renders a proof.

The proof itself is cross-correlated as data (`Facet` rows, not theorems
about the automaton): the regular side of the pattern is a vantage from which
the center shows sensual qualities (the proved claims `edge-parity`,
`three-diagonal-band`, `left-band`), the deep interior is the withdrawn core
(`aperiodic-compensation`, whose withdrawal is the measured non-collapse of
the diagonals of index at least three), and the proved reductions of the root
are the real qualities every vantage shares, under the kernel.

The kernel decides: every quadruple's vantage is a declared journey and every
journey has one; the object is the declared problem and the real object a
claim; every real quality is a proved claim, every withdrawn id an open claim,
every sensual quality a panel, and the sensual qualities of a vantage are its
journey's panels; no sensual quality renders a withdrawn claim (withdrawal);
every vantage sees part of the real object; interactions are symmetric and run
through panels both vantages have; the facets are claims with declared poles
and vantages, proved where sensual or real and open where withdrawn; and a
declared renaming of the panel ids (the gauge) keeps the real qualities and
the withdrawn core while it transforms the sensual qualities (covariance).

Stakeholders, journeys and panels are read from `archmodel` and
`presentationmodel` when the module is generated, never copied here."""

from . import archmodel, frontier, repo
from . import presentationmodel as pm

from .semantic import (BOOL, STR, all_members, b, call, definition, eq_string, field_of_each, holds, if_, list_t,
                       lookup_field, lst, match_list, member_string, named, proj, record, s, strings, structure,
                       theorem, var)

MODULE = repo.ROOT / "rule30-api" / "src" / "Observer.lex.tex"
REGISTER = repo.ROOT / "rule30-api" / "model" / "observer.toml"

REAL_OBJECT = "problem1"
WITHDRAWN_CORE = "aperiodic-compensation"
POLES = ["sensual-quality", "withdrawn", "real-quality"]
VANTAGES = ["regular-side", "chaotic-side", "kernel"]
GAUGE_PREFIX = "sq:"

# The regular side of the pattern as a vantage on the center: the proved
# claims that are its sensual qualities, with what each shows.
REGULAR_SIDE = [
    {"facet": "edge-parity", "basis": "the edge parity: the edge diagonal of the center is the parity of time"},
    {"facet": "three-diagonal-band", "basis": "the ruler of the three-diagonal band"},
    {"facet": "left-band", "basis": "the rulers of the left band"},
]
WITHDRAWAL = "the measured non-collapse of the diagonals of index at least three: the deep interior withdraws"
KERNEL_BASIS = "a proved reduction of the root, the same from every vantage, kernel-checked under propext and Quot.sound"

# Artifacts that carry the register (every claim with its status): a panel
# reading one renders a proof of every proved claim.
REGISTER_COMMANDS = {"chain", "frontier_list", "frontier_render"}
REGISTER_SOURCES = {"frontier.toml", "rule30-api/src/Register.lex.tex"}
MODULE_MEDIA = "text/x-lexlean"
# Panels that show only the open leaves: withdrawn claims, nothing proved.
LEAVES_PANELS = {"open-leaves"}


def _ids(rows):
    return [r["id"] for r in rows]


def register_artifacts(artifacts=None):
    arts = pm.ARTIFACTS if artifacts is None else artifacts
    return {a["id"] for a in arts if a["command"] in REGISTER_COMMANDS or (a.get("source") or "") in REGISTER_SOURCES}


def proved_chain(cid, by_id):
    """The proved claims above a claim (its `depends`, transitively), in register order."""
    seen, stack = set(), list(by_id[cid].get("depends", []))
    while stack:
        d = stack.pop()
        if d in seen or d not in by_id:
            continue
        seen.add(d)
        stack.extend(by_id[d].get("depends", []))
    return [i for i in by_id if i in seen and by_id[i]["status"] == "proved"]


def presented(panel, artifacts=None):
    """The artifacts a panel presents: its own, or every LexLean module when
    its own is one (the modules panel lists them all)."""
    arts = pm.ARTIFACTS if artifacts is None else artifacts
    own = next((a for a in arts if a["id"] == panel["artifact"]), None)
    if own and own["media"] == MODULE_MEDIA:
        return [a for a in arts if a["media"] == MODULE_MEDIA]
    return [own] if own else []


def rendered(panel, claims, artifacts=None):
    """The proved claims a panel renders a proof of."""
    by_id = {c["id"]: c for c in claims}
    proved = [c["id"] for c in claims if c["status"] == "proved"]
    if panel["id"] in LEAVES_PANELS:
        return []
    shown = presented(panel, artifacts)
    if any(a["id"] in register_artifacts(artifacts) for a in shown):
        return proved
    if any(a["command"] == "interface" for a in shown):
        depended = {d for c in claims for d in c.get("depends", [])}
        leaves = [c["id"] for c in claims if c["status"] == "open" and c["id"] not in depended]
        chains = {i for leaf in leaves for i in proved_chain(leaf, by_id)}
        return [i for i in proved if i in chains]
    return []


def data(claims=None, panels=None, journeys=None, artifacts=None):
    """Every row of the module, derived from the register and the presentation."""
    claims = frontier.load()["claim"] if claims is None else claims
    panels = pm.PANELS if panels is None else panels
    journeys = pm.JOURNEYS if journeys is None else journeys
    by_panel = {p["id"]: p for p in panels}
    proved = [c["id"] for c in claims if c["status"] == "proved"]
    open_ids = [c["id"] for c in claims if c["status"] == "open"]
    quadruples = []
    for j in journeys:
        shown = {i for p in j["panels"] if p in by_panel for i in rendered(by_panel[p], claims, artifacts)}
        quadruples.append({"object": archmodel.CONCEPTUAL_MODEL["id"], "realObject": REAL_OBJECT, "sensualObject": j["id"],
                           "realQualities": [i for i in proved if i in shown], "sensualQualities": list(j["panels"]),
                           "withdrawn": open_ids})
    overlaps = [{"vantage": q["sensualObject"], "claim": c} for q in quadruples for c in q["realQualities"]]
    interactions = []
    for a in journeys:
        for c in journeys:
            shared = [p for p in a["panels"] if p in c["panels"]]
            if a["id"] != c["id"] and shared:
                interactions.append({"source": a["id"], "target": c["id"], "viaPanels": shared})
    facets = ([{"facet": f["facet"], "pole": "sensual-quality", "vantage": "regular-side", "basis": f["basis"]} for f in REGULAR_SIDE]
              + [{"facet": WITHDRAWN_CORE, "pole": "withdrawn", "vantage": "chaotic-side", "basis": WITHDRAWAL}]
              + [{"facet": c["id"], "pole": "real-quality", "vantage": "kernel", "basis": KERNEL_BASIS}
                 for c in claims if c["status"] == "proved" and c.get("depends", []) == [REAL_OBJECT]])
    gauge = [{"panel": p["id"], "image": GAUGE_PREFIX + p["id"]} for p in panels]
    return {"quadruples": quadruples, "overlaps": overlaps, "interactions": interactions, "facets": facets, "gauge": gauge,
            "claims": claims}


def problems(d):
    """What the kernel would refuse, named before `lexlean verify` reports a
    false `decide`: a vantage that sees nothing of the real object, a facet
    that is not a claim of the stated status."""
    status = {c["id"]: c["status"] for c in d["claims"]}
    out = []
    if REAL_OBJECT not in status:
        out.append(f"the real object {REAL_OBJECT} is not a claim")
    if status.get(WITHDRAWN_CORE) != "open":
        out.append(f"the withdrawn core {WITHDRAWN_CORE} is not an open claim")
    for q in d["quadruples"]:
        if not q["realQualities"]:
            out.append(f"vantage {q['sensualObject']} sees no proved claim: give the journey a panel that renders the register")
    expected = {"sensual-quality": "proved", "real-quality": "proved", "withdrawn": "open"}
    for f in d["facets"]:
        if status.get(f["facet"]) != expected[f["pole"]]:
            out.append(f"facet {f['facet']} ({f['pole']}) is not a {expected[f['pole']]} claim")
    return out


def declarations(d):
    qd_t, ov_t, in_t, fa_t, re_t = named("Quadruple"), named("Overlap"), named("Interaction"), named("Facet"), named("Renaming")
    jo_t = named("Journey", "Presentation")
    claim_t = named("Claim", "Register")
    nil_s = {"kind": "nil", "element": STR}
    register_claims = call("claims", module="Register")
    claim_ids = call("idsOf", register_claims, module="Register")
    proved = call("claimsWithStatus", s("proved"), register_claims)
    opened = call("claimsWithStatus", s("open"), register_claims)
    journeys = call("journeys", module="Presentation")
    panel_ids = call("panelIds", call("panels", module="Presentation"), module="Presentation")

    def concat(name, field):
        return definition(name, list_t(STR),
                          match_list(var("qs"), nil_s, "head", "tail",
                                     call("appendStrings", proj(var("head"), field), call(name, var("tail")))),
                          parameters=[("qs", list_t(qd_t))], recursive="qs")

    def each(name, element_type, param, condition):
        """`name xs ...`: `condition` holds of every record (the extra
        parameters are fixed through the recursion)."""
        params = [("xs", list_t(element_type))] + param
        return definition(name, BOOL,
                          match_list(var("xs"), b(True), "head", "tail",
                                     if_(condition, call(name, var("tail"), *[var(p) for p, _ in param]), b(False))),
                          parameters=params, recursive="xs")

    quadruple = lambda q: record("Quadruple", object=s(q["object"]), realObject=s(q["realObject"]), sensualObject=s(q["sensualObject"]),
                                 realQualities=strings(q["realQualities"]), sensualQualities=strings(q["sensualQualities"]),
                                 withdrawn=strings(q["withdrawn"]))
    rename_fields = {f: proj(var("q"), f) for f in ("object", "realObject", "sensualObject", "realQualities", "withdrawn")}
    return [
        structure("Quadruple", [("object", STR), ("realObject", STR), ("sensualObject", STR), ("realQualities", list_t(STR)),
                                ("sensualQualities", list_t(STR)), ("withdrawn", list_t(STR))]),
        structure("Overlap", [("vantage", STR), ("claim", STR)]),
        structure("Interaction", [("source", STR), ("target", STR), ("viaPanels", list_t(STR))]),
        structure("Facet", [("facet", STR), ("pole", STR), ("vantage", STR), ("basis", STR)]),
        structure("Renaming", [("panel", STR), ("image", STR)]),
        definition("realObject", STR, s(REAL_OBJECT)),
        definition("withdrawnCore", STR, s(WITHDRAWN_CORE)),
        definition("poles", list_t(STR), strings(POLES)),
        definition("vantages", list_t(STR), strings(VANTAGES)),
        definition("quadruples", list_t(qd_t), lst([quadruple(q) for q in d["quadruples"]], qd_t)),
        definition("overlaps", list_t(ov_t), lst([record("Overlap", vantage=s(o["vantage"]), claim=s(o["claim"]))
                                                  for o in d["overlaps"]], ov_t)),
        definition("interactions", list_t(in_t), lst([record("Interaction", source=s(i["source"]), target=s(i["target"]),
                                                             viaPanels=strings(i["viaPanels"])) for i in d["interactions"]], in_t)),
        definition("facets", list_t(fa_t), lst([record("Facet", facet=s(f["facet"]), pole=s(f["pole"]), vantage=s(f["vantage"]),
                                                       basis=s(f["basis"])) for f in d["facets"]], fa_t)),
        definition("gauge", list_t(re_t), lst([record("Renaming", panel=s(r["panel"]), image=s(r["image"])) for r in d["gauge"]], re_t)),
        member_string(), all_members(),
        definition("appendStrings", list_t(STR),
                   match_list(var("xs"), var("ys"), "head", "tail",
                              {"kind": "cons", "head": var("head"), "tail": call("appendStrings", var("tail"), var("ys"))}),
                   parameters=[("xs", list_t(STR)), ("ys", list_t(STR))], recursive="xs"),
        definition("noneMembers", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(call("memberString", var("head"), var("ids")), b(False), call("noneMembers", var("tail"), var("ids")))),
                   parameters=[("xs", list_t(STR)), ("ids", list_t(STR))], recursive="xs"),
        definition("sameMembers", BOOL, if_(call("allMembers", var("xs"), var("ys")), call("allMembers", var("ys"), var("xs")), b(False)),
                   parameters=[("xs", list_t(STR)), ("ys", list_t(STR))]),
        definition("allEqual", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(eq_string(var("head"), var("value")), call("allEqual", var("tail"), var("value")), b(False))),
                   parameters=[("xs", list_t(STR)), ("value", STR)], recursive="xs"),
        definition("claimsWithStatus", list_t(STR),
                   match_list(var("cs"), nil_s, "head", "tail",
                              if_(eq_string(var("status"), proj(var("head"), "status")),
                                  {"kind": "cons", "head": proj(var("head"), "id"), "tail": call("claimsWithStatus", var("status"), var("tail"))},
                                  call("claimsWithStatus", var("status"), var("tail")))),
                   parameters=[("status", STR), ("cs", list_t(claim_t))], recursive="cs"),
        field_of_each("journeyIds", jo_t, "id"),
        lookup_field("journeyPanelsOf", jo_t, "id", "panels", list_t(STR), nil_s),
        field_of_each("quadrupleObjects", qd_t, "object"),
        field_of_each("quadrupleRealObjects", qd_t, "realObject"),
        field_of_each("quadrupleSensualObjects", qd_t, "sensualObject"),
        concat("quadrupleRealQualities", "realQualities"),
        concat("quadrupleSensualQualities", "sensualQualities"),
        concat("quadrupleWithdrawn", "withdrawn"),
        lookup_field("realQualitiesOf", qd_t, "sensualObject", "realQualities", list_t(STR), nil_s),
        lookup_field("sensualQualitiesOf", qd_t, "sensualObject", "sensualQualities", list_t(STR), nil_s),
        each("sensualQualitiesAreJourneyPanels", qd_t, [("js", list_t(jo_t))],
             call("sameMembers", proj(var("head"), "sensualQualities"), call("journeyPanelsOf", proj(var("head"), "sensualObject"), var("js")))),
        each("everyQuadrupleWithdraws", qd_t, [("claim", STR)], call("memberString", var("claim"), proj(var("head"), "withdrawn"))),
        field_of_each("overlapVantages", ov_t, "vantage"),
        field_of_each("overlapClaims", ov_t, "claim"),
        each("overlapsInRealQualities", ov_t, [("qs", list_t(qd_t))],
             call("memberString", proj(var("head"), "claim"), call("realQualitiesOf", proj(var("head"), "vantage"), var("qs")))),
        definition("hasOverlap", BOOL,
                   match_list(var("os"), b(False), "head", "tail",
                              if_(eq_string(var("vantage"), proj(var("head"), "vantage")), b(True), call("hasOverlap", var("vantage"), var("tail")))),
                   parameters=[("vantage", STR), ("os", list_t(ov_t))], recursive="os"),
        each("everyVantageOverlaps", qd_t, [("os", list_t(ov_t))], call("hasOverlap", proj(var("head"), "sensualObject"), var("os"))),
        field_of_each("interactionSources", in_t, "source"),
        field_of_each("interactionTargets", in_t, "target"),
        definition("hasReverse", BOOL,
                   match_list(var("rows"), b(False), "head", "tail",
                              if_(eq_string(var("source"), proj(var("head"), "target")),
                                  if_(eq_string(var("target"), proj(var("head"), "source")),
                                      if_(call("sameMembers", var("panels"), proj(var("head"), "viaPanels")), b(True),
                                          call("hasReverse", var("source"), var("target"), var("panels"), var("tail"))),
                                      call("hasReverse", var("source"), var("target"), var("panels"), var("tail"))),
                                  call("hasReverse", var("source"), var("target"), var("panels"), var("tail")))),
                   parameters=[("source", STR), ("target", STR), ("panels", list_t(STR)), ("rows", list_t(in_t))], recursive="rows"),
        each("symmetric", in_t, [("rows", list_t(in_t))],
             call("hasReverse", proj(var("head"), "source"), proj(var("head"), "target"), proj(var("head"), "viaPanels"), var("rows"))),
        each("interactionsShare", in_t, [("qs", list_t(qd_t))],
             if_(call("allMembers", proj(var("head"), "viaPanels"), call("sensualQualitiesOf", proj(var("head"), "source"), var("qs"))),
                 call("allMembers", proj(var("head"), "viaPanels"), call("sensualQualitiesOf", proj(var("head"), "target"), var("qs"))),
                 b(False))),
        field_of_each("facetIds", fa_t, "facet"),
        field_of_each("facetPoles", fa_t, "pole"),
        field_of_each("facetVantages", fa_t, "vantage"),
        definition("facetsOfPole", list_t(STR),
                   match_list(var("fs"), nil_s, "head", "tail",
                              if_(eq_string(var("pole"), proj(var("head"), "pole")),
                                  {"kind": "cons", "head": proj(var("head"), "facet"), "tail": call("facetsOfPole", var("pole"), var("tail"))},
                                  call("facetsOfPole", var("pole"), var("tail")))),
                   parameters=[("pole", STR), ("fs", list_t(fa_t))], recursive="fs"),
        # the gauge: a renaming of the panel ids applied to the sensual qualities
        definition("renameString", STR,
                   match_list(var("rs"), var("x"), "head", "tail",
                              if_(eq_string(var("x"), proj(var("head"), "panel")), proj(var("head"), "image"),
                                  call("renameString", var("x"), var("tail")))),
                   parameters=[("x", STR), ("rs", list_t(re_t))], recursive="rs"),
        definition("renameStrings", list_t(STR),
                   match_list(var("xs"), nil_s, "head", "tail",
                              {"kind": "cons", "head": call("renameString", var("head"), var("rs")),
                               "tail": call("renameStrings", var("tail"), var("rs"))}),
                   parameters=[("xs", list_t(STR)), ("rs", list_t(re_t))], recursive="xs"),
        definition("renameQuadruple", qd_t,
                   record("Quadruple", object=rename_fields["object"], realObject=rename_fields["realObject"],
                          sensualObject=rename_fields["sensualObject"], realQualities=rename_fields["realQualities"],
                          sensualQualities=call("renameStrings", proj(var("q"), "sensualQualities"), var("rs")),
                          withdrawn=rename_fields["withdrawn"]),
                   parameters=[("q", qd_t), ("rs", list_t(re_t))]),
        definition("renameQuadruples", list_t(qd_t),
                   match_list(var("qs"), {"kind": "nil", "element": qd_t}, "head", "tail",
                              {"kind": "cons", "head": call("renameQuadruple", var("head"), var("rs")),
                               "tail": call("renameQuadruples", var("tail"), var("rs"))}),
                   parameters=[("qs", list_t(qd_t)), ("rs", list_t(re_t))], recursive="qs"),
        # the vantages are the journeys, the object is the problem, the real object a claim
        holds("vantagesAreJourneys", call("allMembers", call("quadrupleSensualObjects", call("quadruples")), call("journeyIds", journeys))),
        holds("everyJourneyIsAVantage", call("allMembers", call("journeyIds", journeys), call("quadrupleSensualObjects", call("quadruples")))),
        holds("objectIsTheProblem",
              call("allEqual", call("quadrupleObjects", call("quadruples")), proj(call("conceptualModel", module="Architecture"), "id"))),
        holds("realObjectIsTheRoot", call("allEqual", call("quadrupleRealObjects", call("quadruples")), call("realObject"))),
        holds("realObjectIsAClaim", call("memberString", call("realObject"), claim_ids)),
        # the poles over the register and the presentation
        holds("realQualitiesAreProved", call("allMembers", call("quadrupleRealQualities", call("quadruples")), proved)),
        holds("withdrawnAreOpen", call("allMembers", call("quadrupleWithdrawn", call("quadruples")), opened)),
        holds("sensualQualitiesArePanels", call("allMembers", call("quadrupleSensualQualities", call("quadruples")), panel_ids)),
        holds("sensualQualitiesAreTheJourney", call("sensualQualitiesAreJourneyPanels", call("quadruples"), journeys)),
        holds("withdrawnCoreIsOpen", call("memberString", call("withdrawnCore"), opened)),
        holds("withdrawnCoreIsWithdrawnEverywhere", call("everyQuadrupleWithdraws", call("quadruples"), call("withdrawnCore"))),
        # withdrawal: no sensual quality renders a proof of a withdrawn claim
        holds("withdrawal", call("noneMembers", call("overlapClaims", call("overlaps")), call("quadrupleWithdrawn", call("quadruples")))),
        holds("overlapsAreRealQualities", call("overlapsInRealQualities", call("overlaps"), call("quadruples"))),
        holds("overlapVantagesAreVantages",
              call("allMembers", call("overlapVantages", call("overlaps")), call("quadrupleSensualObjects", call("quadruples")))),
        holds("everyVantageSeesTheObject", call("everyVantageOverlaps", call("quadruples"), call("overlaps"))),
        # vicarious interaction: symmetric, through shared panels
        holds("interactionSourcesAreVantages",
              call("allMembers", call("interactionSources", call("interactions")), call("quadrupleSensualObjects", call("quadruples")))),
        holds("interactionTargetsAreVantages",
              call("allMembers", call("interactionTargets", call("interactions")), call("quadrupleSensualObjects", call("quadruples")))),
        holds("interactionsAreSymmetric", call("symmetric", call("interactions"), call("interactions"))),
        holds("interactionsThroughSharedPanels", call("interactionsShare", call("interactions"), call("quadruples"))),
        # the proof's facets as data over the register
        holds("facetsAreClaims", call("allMembers", call("facetIds", call("facets")), claim_ids)),
        holds("facetPolesDeclared", call("allMembers", call("facetPoles", call("facets")), call("poles"))),
        holds("facetVantagesDeclared", call("allMembers", call("facetVantages", call("facets")), call("vantages"))),
        holds("sensualFacetsAreProved", call("allMembers", call("facetsOfPole", s("sensual-quality"), call("facets")), proved)),
        holds("realFacetsAreProved", call("allMembers", call("facetsOfPole", s("real-quality"), call("facets")), proved)),
        holds("withdrawnFacetsAreOpen", call("allMembers", call("facetsOfPole", s("withdrawn"), call("facets")), opened)),
        holds("withdrawnCoreIsAFacet", call("memberString", call("withdrawnCore"), call("facetsOfPole", s("withdrawn"), call("facets")))),
        # gauge covariance: the renaming keeps RQ and the withdrawn core, transforms SQ
        theorem("gaugeKeepsRealQualities",
                call("quadrupleRealQualities", call("renameQuadruples", call("quadruples"), call("gauge"))),
                call("quadrupleRealQualities", call("quadruples"))),
        theorem("gaugeKeepsWithdrawn",
                call("quadrupleWithdrawn", call("renameQuadruples", call("quadruples"), call("gauge"))),
                call("quadrupleWithdrawn", call("quadruples"))),
        theorem("gaugeTransformsSensualQualities",
                call("quadrupleSensualQualities", call("renameQuadruples", call("quadruples"), call("gauge"))),
                call("renameStrings", call("quadrupleSensualQualities", call("quadruples")), call("gauge"))),
    ]


def _q(v):
    return '"' + str(v).replace("\\", "\\\\").replace('"', '\\"') + '"'


def _list(xs):
    return "[" + ", ".join(_q(x) for x in xs) + "]"


def register_toml(d):
    """`rule30-api/model/observer.toml`: the same rows as the module, in the
    shape of the other model registers."""
    lines = ['spec = "r30/observer/1"', f"object = {_q(archmodel.CONCEPTUAL_MODEL['id'])}", f"real_object = {_q(REAL_OBJECT)}",
             f"withdrawn_core = {_q(WITHDRAWN_CORE)}", f"poles = {_list(POLES)}", f"vantages = {_list(VANTAGES)}", ""]
    for q in d["quadruples"]:
        lines += ["[[quadruple]]", f"vantage = {_q(q['sensualObject'])}", f"real_qualities = {_list(q['realQualities'])}",
                  f"sensual_qualities = {_list(q['sensualQualities'])}", f"withdrawn = {_list(q['withdrawn'])}", ""]
    for o in d["overlaps"]:
        lines += ["[[overlap]]", f"vantage = {_q(o['vantage'])}", f"claim = {_q(o['claim'])}", ""]
    for i in d["interactions"]:
        lines += ["[[interaction]]", f"source = {_q(i['source'])}", f"target = {_q(i['target'])}", f"via_panels = {_list(i['viaPanels'])}", ""]
    for f in d["facets"]:
        lines += ["[[facet]]", f"facet = {_q(f['facet'])}", f"pole = {_q(f['pole'])}", f"vantage = {_q(f['vantage'])}",
                  f"basis = {_q(f['basis'])}", ""]
    return "\n".join(lines)


def render(d=None):
    from . import lexmod
    d = data() if d is None else d
    bad = problems(d)
    if bad:
        raise ValueError("; ".join(bad))
    return lexmod.module("Observer", declarations(d), imports=["Architecture", "Presentation", "Register"])


def sync():
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    d = data()
    text = render(d)
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "quadruples": len(d["quadruples"]), "changed": changed}


def check():
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Observer.lex.tex is missing; run `bin/r30 api sync`"}
    ok = MODULE.read_text() == render()
    return {"ok": ok, "reason": None if ok else "Observer.lex.tex drifted; run `bin/r30 api sync`"}
