"""The architecture description as a LexLean semantic module on prism-stdlib.

`rule30-api/src/Architecture.lex.tex` declares, as data with decided
theorems, the conceptual model (the Rule 30 Prize, Problem 1), the
stakeholders of the effort, their concerns, the viewpoints that frame each
concern for a stakeholder, the views governed by those viewpoints (the
reduction tree, the register, the gate, the interface sheets, the published
view, the API modules), and the quality model that says what an optimal
implementation is here. The entities are the stdlib's: `Foundation.Arch`
(ISO/IEC/IEEE 42010 as PrismPM's `prism.arch` lexicon models it: Stakeholder,
Concern, Viewpoint, View, ModelKind) and `Foundation.Qual` (ISO/IEC 25010:
ProductQualityCharacteristic, QualitySubcharacteristic, QualityRequirement,
QualityMeasure), vendored under `rule30-api/stdlib` and imported. The stdlib
references entities by index; each labeled entry here carries its stdlib
entity, and the theorems decide that the indices agree with the labels, that
every concern is framed and every viewpoint governs a view, and that every
command a view or a measure names is a command of `Api.lex.tex`."""

from . import repo
from .semantic import (BOOL, NAT, STR, add, all_members, b, beq, call, ctor, definition, each_indexed,
                       each_resolves, field_of_each, holds, if_, index_of, list_t, lookup_field, lst,
                       match_list, member_string, n, named, proj, record, s, strings, structure, theorem, var)

MODULE = repo.ROOT / "rule30-api" / "src" / "Architecture.lex.tex"
ARCH = "Foundation.Arch"
QUAL = "Foundation.Qual"

CONCEPTUAL_MODEL = {
    "id": "rule30-problem-1",
    "statement": "Wolfram's Rule 30 Prize, Problem 1: the center column of Rule 30 from a single black cell is not eventually periodic.",
    "citation": "https://www.rule30prize.org",
}

STAKEHOLDERS = [
    {"id": "wolfram", "name": "Stephen Wolfram and the Rule 30 Prize committee",
     "concerns": ["closure", "evidence"]},
    {"id": "researcher", "name": "The researcher driving the proof",
     "concerns": ["closure", "optimal-implementation", "comprehension"]},
    {"id": "community", "name": "The community and industry reading and reusing the work",
     "concerns": ["evidence", "comprehension", "current-view"]},
    {"id": "uor-foundation", "name": "The UOR Foundation (LexLean and prism-stdlib improve through this research)",
     "concerns": ["stdlib", "optimal-implementation", "current-view"]},
    {"id": "mathematician", "name": "A mathematician reading the proof",
     "concerns": ["mathematics", "closure", "evidence"]},
    {"id": "layperson", "name": "A reader with no Lean or LexLean background",
     "concerns": ["plain-language", "comprehension"]},
]

CONCERNS = [
    {"id": "closure", "statement": "Problem 1 is closed by a kernel-checked chain of reductions."},
    {"id": "evidence", "statement": "Every claim is backed by kernel evidence; nothing unproved is called proved."},
    {"id": "optimal-implementation", "statement": "The implementation stays optimal: validation runs once, in the gate, and never impedes the research."},
    {"id": "comprehension", "statement": "The features of the problem and of the solution are labeled and readable from the register."},
    {"id": "current-view", "statement": "Each push publishes the current state of the implementation."},
    {"id": "stdlib", "statement": "What the research needs from LexLean and prism-stdlib is identified and fed back."},
    {"id": "mathematics", "statement": "The statements are readable as mathematics, each with its Lean name and lexeme, and their proofs are attested."},
    {"id": "plain-language", "statement": "The problem, the proved facts and the open obligation are explained without formal prerequisites."},
]

# ISO 42010: a viewpoint frames one concern for a stakeholder and names the
# kind of model its views are made of (Foundation.Arch.ModelKind).
MODEL_KINDS = ["componentModel", "securityModel", "qualityModel"]

VIEWPOINTS = [
    {"id": "reduction", "stakeholder": "wolfram", "concern": "closure", "model_kind": "componentModel",
     "statement": "The proof as a tree of reductions: what rests on what, which arrows are theorems, which leaves are open."},
    {"id": "evidence", "stakeholder": "wolfram", "concern": "evidence", "model_kind": "componentModel",
     "statement": "Every status in the register read against the kernel: a proved claim names a theorem checked under propext and Quot.sound."},
    {"id": "optimal", "stakeholder": "researcher", "concern": "optimal-implementation", "model_kind": "qualityModel",
     "statement": "The implementation measured by the quality model below: validation time, regenerability, and correctness thresholds."},
    {"id": "comprehension", "stakeholder": "community", "concern": "comprehension", "model_kind": "componentModel",
     "statement": "Each claim with its chain from the root, its notions, the exact facts about them and the handles to continue."},
    {"id": "current", "stakeholder": "community", "concern": "current-view", "model_kind": "componentModel",
     "statement": "The current state of the implementation as a published artifact, rendered from the register on every push."},
    {"id": "stdlib", "stakeholder": "uor-foundation", "concern": "stdlib", "model_kind": "componentModel",
     "statement": "The LexLean modules of the project on the stdlib's types, and what they needed from the language."},
    {"id": "paper", "stakeholder": "mathematician", "concern": "mathematics", "model_kind": "componentModel",
     "statement": "The published theorems in the paper's controlled English with their Lean names and lexemes, the attested PDFs with their digests, the open obligation in its exact form, and the refuted routes with their refutations."},
    {"id": "plain", "stakeholder": "layperson", "concern": "plain-language", "model_kind": "componentModel",
     "statement": "Rule 30 drawn, and the problem, what is proved, what is open and what kernel-checked means, in plain words, with a guide to the other panels."},
]

VIEWS = [
    {"id": "reduction-tree", "viewpoint": "reduction", "command": "chain",
     "statement": "The register as one DAG from problem1 to the open leaves, every arrow a theorem."},
    {"id": "register-evidence", "viewpoint": "evidence", "command": "frontier_check",
     "statement": "frontier check: proved claims kernel-checked under propext and Quot.sound and published; Register.lex.tex decided."},
    {"id": "gate", "viewpoint": "optimal", "command": "commit",
     "statement": "One validate-and-commit step with cached Lake directories and reused LexLean attestations; CI renders, it does not re-validate."},
    {"id": "interface-sheets", "viewpoint": "comprehension", "command": "interface",
     "statement": "The labeled interface sheet of every claim: chain, notions, exact facts, handles."},
    {"id": "published-view", "viewpoint": "current", "command": "view_render",
     "statement": "The view workflow renders the tree, the register, the sheets, the API modules and the site on every push to main."},
    {"id": "api-modules", "viewpoint": "stdlib", "command": "api_sync",
     "statement": "The command surface, the register, this architecture and the presentation are LexLean semantic modules on prism-stdlib; what they needed from the language is recorded in AGENTS.md."},
    {"id": "paper-statements", "viewpoint": "paper", "command": "view_render",
     "statement": "statements.json: every theorem of Observations.lex.tex with its Lean name, lexeme and section, the attested PDFs with their digests; the obligation and the refuted routes read from the register."},
    {"id": "explainer", "viewpoint": "plain", "command": "view_render",
     "statement": "The Rule 30 picture and the plain-language paragraphs Presentation.lex.tex declares as data, rendered by the site."},
]

# ISO 25010 product quality, restricted to what "optimal implementation" means
# for a proof repository. A measure names the command that reports it and the
# threshold it must stay within (Foundation.Qual.QualityMeasure.threshold).
CHARACTERISTICS = [
    {"id": "performance-efficiency", "statement": "Validation costs time once, in the gate, and never on the research loop."},
    {"id": "maintainability", "statement": "Every generated module has one generator and one source; nothing is written twice."},
    {"id": "functional-correctness", "statement": "Nothing unproved is called proved, and no proof uses an axiom beyond propext and Quot.sound."},
]

SUBCHARACTERISTICS = [
    {"id": "time-behaviour", "characteristic": "performance-efficiency",
     "statement": "The inner loop takes seconds, the whole gate minutes, and CI only renders."},
    {"id": "modularity", "characteristic": "maintainability",
     "statement": "The LexLean modules are regenerated from the parser, the register and the model data, and drift is refused."},
    {"id": "reusability", "characteristic": "maintainability",
     "statement": "The architecture and quality entities are the stdlib's, not private copies."},
    {"id": "correctness", "characteristic": "functional-correctness",
     "statement": "The register is read against the kernel on every commit."},
]

REQUIREMENTS = [
    {"id": "module-check-seconds", "subcharacteristic": "time-behaviour",
     "statement": "Checking or verifying one LexLean module takes seconds."},
    {"id": "api-verify-seconds", "subcharacteristic": "time-behaviour",
     "statement": "Verifying the whole rule30-api project takes under a minute."},
    {"id": "ci-render-minutes", "subcharacteristic": "time-behaviour",
     "statement": "The view workflow renders the current view within its timeout and runs no Lean, no lexlean and no tests."},
    {"id": "gate-minutes", "subcharacteristic": "time-behaviour",
     "statement": "The pre-commit gate, reusing accepted Lake directories and LexLean attestations, finishes within half an hour."},
    {"id": "no-drift", "subcharacteristic": "modularity",
     "statement": "Every generated module and register matches its generator (api check)."},
    {"id": "stdlib-entities", "subcharacteristic": "reusability",
     "statement": "The architecture declares no private stakeholder, concern, viewpoint, view or quality type: each entry carries a stdlib entity."},
    {"id": "unbacked-claims", "subcharacteristic": "correctness",
     "statement": "No proved claim lacks a kernel-checked, published Lean theorem (frontier check)."},
    {"id": "forbidden-axioms", "subcharacteristic": "correctness",
     "statement": "No theorem depends on an axiom beyond propext and Quot.sound (axioms, choice-audit)."},
]

MEASURES = [
    {"id": "module-check-time", "requirement": "module-check-seconds", "threshold": 60, "unit": "seconds", "command": "check",
     "statement": "Seconds reported by `check` or `verify --modules` for one module."},
    {"id": "api-verify-time", "requirement": "api-verify-seconds", "threshold": 60, "unit": "seconds", "command": "verify",
     "statement": "Seconds reported by `verify api`."},
    {"id": "ci-render-time", "requirement": "ci-render-minutes", "threshold": 5, "unit": "minutes", "command": "view_render",
     "statement": "The timeout of the view workflow's render job."},
    {"id": "gate-time", "requirement": "gate-minutes", "threshold": 30, "unit": "minutes", "command": "gate",
     "statement": "Minutes between the start and the end of the pre-commit gate (`gate` reports the running one)."},
    {"id": "drifted-modules", "requirement": "no-drift", "threshold": 0, "unit": "modules", "command": "api_check",
     "statement": "Modules or registers that `api check` reports as drifted."},
    {"id": "private-entities", "requirement": "stdlib-entities", "threshold": 0, "unit": "structures", "command": "api_check",
     "statement": "Architecture structures without an `entity` field of a stdlib type."},
    {"id": "unbacked-proved", "requirement": "unbacked-claims", "threshold": 0, "unit": "claims", "command": "frontier_check",
     "statement": "Proved claims whose Lean name is not kernel-checked and published."},
    {"id": "forbidden-axiom-uses", "requirement": "forbidden-axioms", "threshold": 0, "unit": "theorems", "command": "choice_audit",
     "statement": "Theorems depending on Classical.choice or any axiom beyond propext and Quot.sound."},
]


def _ids(rows):
    return [r["id"] for r in rows]


def _index(rows, value):
    return _ids(rows).index(value)


def model_kind_index(kind):
    return MODEL_KINDS.index(kind)


def declarations():
    sh_t, co_t, vp_t, vw_t = named("StakeholderEntry"), named("ConcernEntry"), named("ViewpointEntry"), named("ViewEntry")
    ch_t, sc_t, rq_t, me_t = (named("CharacteristicEntry"), named("SubcharacteristicEntry"),
                              named("RequirementEntry"), named("MeasureEntry"))
    kind_t = named("ModelKind", ARCH)
    cmd_t = named("Command", "Api")

    stakeholder_entries = [
        record("StakeholderEntry", entity=record("Stakeholder", ARCH, index=n(i)), id=s(x["id"]), name=s(x["name"]),
               concerns=strings(x["concerns"])) for i, x in enumerate(STAKEHOLDERS)]
    concern_entries = [
        record("ConcernEntry", entity=record("Concern", ARCH, index=n(i)), id=s(x["id"]), statement=s(x["statement"]))
        for i, x in enumerate(CONCERNS)]
    viewpoint_entries = [
        record("ViewpointEntry",
               entity=record("Viewpoint", ARCH, index=n(i), stakeholderIndex=n(_index(STAKEHOLDERS, x["stakeholder"])),
                             concernIndex=n(_index(CONCERNS, x["concern"])), modelKindIndex=n(model_kind_index(x["model_kind"]))),
               id=s(x["id"]), stakeholder=s(x["stakeholder"]), concern=s(x["concern"]),
               modelKind=ctor(f"ModelKind.{x['model_kind']}", ARCH), statement=s(x["statement"]))
        for i, x in enumerate(VIEWPOINTS)]
    view_entries = [
        record("ViewEntry",
               entity=record("View", ARCH, index=n(i), viewpointIndex=n(_index(VIEWPOINTS, x["viewpoint"])),
                             modelKindIndex=n(model_kind_index(VIEWPOINTS[_index(VIEWPOINTS, x["viewpoint"])]["model_kind"]))),
               id=s(x["id"]), viewpoint=s(x["viewpoint"]), command=s(x["command"]), statement=s(x["statement"]))
        for i, x in enumerate(VIEWS)]
    characteristic_entries = [
        record("CharacteristicEntry", entity=record("ProductQualityCharacteristic", QUAL, index=n(i)),
               id=s(x["id"]), statement=s(x["statement"])) for i, x in enumerate(CHARACTERISTICS)]
    subcharacteristic_entries = [
        record("SubcharacteristicEntry",
               entity=record("QualitySubcharacteristic", QUAL, index=n(i), characteristicIndex=n(_index(CHARACTERISTICS, x["characteristic"]))),
               id=s(x["id"]), characteristic=s(x["characteristic"]), statement=s(x["statement"]))
        for i, x in enumerate(SUBCHARACTERISTICS)]
    requirement_entries = [
        record("RequirementEntry",
               entity=record("QualityRequirement", QUAL, index=n(i), subcharacteristicIndex=n(_index(SUBCHARACTERISTICS, x["subcharacteristic"]))),
               id=s(x["id"]), subcharacteristic=s(x["subcharacteristic"]), statement=s(x["statement"]))
        for i, x in enumerate(REQUIREMENTS)]
    measure_entries = [
        record("MeasureEntry",
               entity=record("QualityMeasure", QUAL, index=n(i), requirementIndex=n(_index(REQUIREMENTS, x["requirement"])),
                             threshold=n(x["threshold"])),
               id=s(x["id"]), requirement=s(x["requirement"]), unit=s(x["unit"]), command=s(x["command"]),
               statement=s(x["statement"]))
        for i, x in enumerate(MEASURES)]

    def kind_branch(kind, i):
        return {"constructor": {"name": f"ModelKind.{kind}", "module": ARCH}, "binders": [], "body": n(i)}

    return [
        structure("ConceptualModel", [("id", STR), ("statement", STR), ("citation", STR)]),
        structure("StakeholderEntry", [("entity", named("Stakeholder", ARCH)), ("id", STR), ("name", STR), ("concerns", list_t(STR))]),
        structure("ConcernEntry", [("entity", named("Concern", ARCH)), ("id", STR), ("statement", STR)]),
        structure("ViewpointEntry", [("entity", named("Viewpoint", ARCH)), ("id", STR), ("stakeholder", STR), ("concern", STR),
                                     ("modelKind", kind_t), ("statement", STR)]),
        structure("ViewEntry", [("entity", named("View", ARCH)), ("id", STR), ("viewpoint", STR), ("command", STR), ("statement", STR)]),
        structure("CharacteristicEntry", [("entity", named("ProductQualityCharacteristic", QUAL)), ("id", STR), ("statement", STR)]),
        structure("SubcharacteristicEntry", [("entity", named("QualitySubcharacteristic", QUAL)), ("id", STR),
                                             ("characteristic", STR), ("statement", STR)]),
        structure("RequirementEntry", [("entity", named("QualityRequirement", QUAL)), ("id", STR),
                                       ("subcharacteristic", STR), ("statement", STR)]),
        structure("MeasureEntry", [("entity", named("QualityMeasure", QUAL)), ("id", STR), ("requirement", STR),
                                   ("unit", STR), ("command", STR), ("statement", STR)]),
        definition("conceptualModel", named("ConceptualModel"),
                   record("ConceptualModel", **{k: s(v) for k, v in CONCEPTUAL_MODEL.items()})),
        definition("stakeholders", list_t(sh_t), lst(stakeholder_entries, sh_t)),
        definition("concerns", list_t(co_t), lst(concern_entries, co_t)),
        definition("viewpoints", list_t(vp_t), lst(viewpoint_entries, vp_t)),
        definition("views", list_t(vw_t), lst(view_entries, vw_t)),
        definition("characteristics", list_t(ch_t), lst(characteristic_entries, ch_t)),
        definition("subcharacteristics", list_t(sc_t), lst(subcharacteristic_entries, sc_t)),
        definition("requirements", list_t(rq_t), lst(requirement_entries, rq_t)),
        definition("measures", list_t(me_t), lst(measure_entries, me_t)),
        # the model kind of a viewpoint as the stdlib indexes it
        definition("modelKindIndex", NAT,
                   {"kind": "match", "scrutinee": var("kind"),
                    "branches": [kind_branch(k, i) for i, k in enumerate(MODEL_KINDS)]},
                   parameters=[("kind", kind_t)]),
        member_string(), all_members(), index_of(),
        field_of_each("stakeholderIds", sh_t, "id"),
        field_of_each("concernIds", co_t, "id"),
        field_of_each("viewpointIds", vp_t, "id"),
        field_of_each("viewIds", vw_t, "id"),
        field_of_each("viewpointConcerns", vp_t, "concern"),
        field_of_each("viewViewpoints", vw_t, "viewpoint"),
        field_of_each("viewCommands", vw_t, "command"),
        field_of_each("characteristicIds", ch_t, "id"),
        field_of_each("subcharacteristicIds", sc_t, "id"),
        field_of_each("requirementIds", rq_t, "id"),
        field_of_each("measureRequirements", me_t, "requirement"),
        field_of_each("measureCommands", me_t, "command"),
        field_of_each("commandNames", cmd_t, "name"),
        lookup_field("stakeholderConcerns", sh_t, "id", "concerns", list_t(STR), {"kind": "nil", "element": STR}),
        lookup_field("measureThreshold", me_t, "id", "threshold", NAT, n(0), path=("entity",)),
        lookup_field("viewpointKind", vp_t, "id", "modelKind", kind_t, ctor("ModelKind.componentModel", ARCH)),
        definition("stakeholderConcernsExist", BOOL,
                   match_list(var("ss"), b(True), "head", "tail",
                              if_(call("allMembers", proj(var("head"), "concerns"), var("ids")),
                                  call("stakeholderConcernsExist", var("tail"), var("ids")), b(False))),
                   parameters=[("ss", list_t(sh_t)), ("ids", list_t(STR))], recursive="ss"),
        # the stakeholder a viewpoint frames a concern for holds that concern
        definition("viewpointsHeld", BOOL,
                   match_list(var("vs"), b(True), "head", "tail",
                              if_(call("memberString", proj(var("head"), "concern"),
                                       call("stakeholderConcerns", proj(var("head"), "stakeholder"), var("ss"))),
                                  call("viewpointsHeld", var("tail"), var("ss")), b(False))),
                   parameters=[("vs", list_t(vp_t)), ("ss", list_t(sh_t))], recursive="vs"),
        # the stdlib's modelKindIndex of a viewpoint is the index of its model kind
        definition("viewpointKindsAgree", BOOL,
                   match_list(var("vs"), b(True), "head", "tail",
                              if_(beq(proj(proj(var("head"), "entity"), "modelKindIndex"),
                                      call("modelKindIndex", proj(var("head"), "modelKind"))),
                                  call("viewpointKindsAgree", var("tail")), b(False))),
                   parameters=[("vs", list_t(vp_t))], recursive="vs"),
        each_indexed("stakeholdersIndexed", sh_t),
        each_indexed("concernsIndexed", co_t),
        each_indexed("viewpointsIndexed", vp_t),
        each_indexed("viewsIndexed", vw_t),
        each_resolves("viewpointStakeholdersResolve", vp_t, "stakeholder", "stakeholderIndex"),
        each_resolves("viewpointConcernsResolve", vp_t, "concern", "concernIndex"),
        each_resolves("viewsResolve", vw_t, "viewpoint", "viewpointIndex"),
        each_resolves("subcharacteristicsResolve", sc_t, "characteristic", "characteristicIndex"),
        each_resolves("requirementsResolve", rq_t, "subcharacteristic", "subcharacteristicIndex"),
        each_resolves("measuresResolve", me_t, "requirement", "requirementIndex"),
        # ISO 42010 well-formedness, decided
        holds("stakeholderConcernsDeclared", call("stakeholderConcernsExist", call("stakeholders"), call("concernIds", call("concerns")))),
        holds("stakeholdersAreIndexed", call("stakeholdersIndexed", call("stakeholders"), n(0))),
        holds("concernsAreIndexed", call("concernsIndexed", call("concerns"), n(0))),
        holds("viewpointsAreIndexed", call("viewpointsIndexed", call("viewpoints"), n(0))),
        holds("viewsAreIndexed", call("viewsIndexed", call("views"), n(0))),
        holds("viewpointStakeholdersIndexed",
              call("viewpointStakeholdersResolve", call("viewpoints"), call("stakeholderIds", call("stakeholders")))),
        holds("viewpointConcernsIndexed", call("viewpointConcernsResolve", call("viewpoints"), call("concernIds", call("concerns")))),
        holds("viewpointsFrameHeldConcerns", call("viewpointsHeld", call("viewpoints"), call("stakeholders"))),
        holds("viewpointModelKindsIndexed", call("viewpointKindsAgree", call("viewpoints"))),
        holds("everyConcernFramed", call("allMembers", call("concernIds", call("concerns")), call("viewpointConcerns", call("viewpoints")))),
        holds("viewsGovernedByViewpoints", call("viewsResolve", call("views"), call("viewpointIds", call("viewpoints")))),
        holds("everyViewpointGovernsAView", call("allMembers", call("viewpointIds", call("viewpoints")), call("viewViewpoints", call("views")))),
        holds("everyViewCommandExists", call("allMembers", call("viewCommands", call("views")), call("commandNames", call("commands", module="Api")))),
        # ISO 25010 chain, decided
        holds("subcharacteristicsIndexed",
              call("subcharacteristicsResolve", call("subcharacteristics"), call("characteristicIds", call("characteristics")))),
        holds("requirementsIndexed", call("requirementsResolve", call("requirements"), call("subcharacteristicIds", call("subcharacteristics")))),
        holds("measuresIndexed", call("measuresResolve", call("measures"), call("requirementIds", call("requirements")))),
        holds("everyRequirementMeasured", call("allMembers", call("requirementIds", call("requirements")), call("measureRequirements", call("measures")))),
        holds("everyMeasureCommandExists", call("allMembers", call("measureCommands", call("measures")), call("commandNames", call("commands", module="Api")))),
        # the viewpoint of the optimal-implementation concern is made of the quality model
        theorem("optimalViewpointIsQualityModel",
                call("modelKindIndex", call("viewpointKind", s("optimal"), call("viewpoints"))),
                n(model_kind_index("qualityModel"))),
    ]


def render():
    from . import lexmod
    return lexmod.module("Architecture", declarations(), imports=["Api", ARCH, QUAL])


def sync():
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    text = render()
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "stakeholders": len(STAKEHOLDERS), "changed": changed}


def check():
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Architecture.lex.tex is missing; run `bin/r30 api sync`"}
    ok = MODULE.read_text() == render()
    return {"ok": ok, "reason": None if ok else "Architecture.lex.tex drifted; run `bin/r30 api sync`"}
