"""The standards register as a LexLean module, and the machine-readable
artifacts the standards call for.

`rule30-api/src/Standards.lex.tex` declares, as data with decided theorems,
the external standards this implementation realizes: one `Standard` row
each, with the authority (URL), the version, the scope (what it governs
here), the declared things that realize it (`realizedBy`: modules, published
artifacts, panels, journeys, `r30` commands, workflows, model registers, the
site's navigation and visualization ids) and the command or decided
predicate that confirms conformance. The kernel decides that the ids are
distinct, that every standard has an authority and at least one realizer,
that every realizer is a declared thing, and the coverage the other way:
every panel, artifact, journey and command of `Presentation` and `Api`, and
every navigation and visualization id, names at least one standard; and
that the Lean and LexLean rows carry the pinned versions.
`rule30-api/model/standards.toml` (`prismpm/standards/1`) is the same rows
as a PrismPM register.

`bin/r30 view render` writes the artifacts the standards call for from the
same rows and the same models (`site.py` calls the builders here):
`openapi.json` (OpenAPI 3.1 from the CLI parser, the responses from the
result schemas), `sitemap.xml` and `robots.txt` (the journeys' deep links),
`provenance.jsonld` (W3C PROV-O: every proved claim derived from its Lean
theorem, attributed to the kernel, attested by the paper's LexLean
attestation and, when a replay receipt is readable, the module's κ-label),
`schema.json` (schema.org JSON-LD: a LearningResource per step, the paper as
ScholarlyArticle, the repository as SoftwareSourceCode, the register as
Dataset; also embedded in `index.html`), `attestations.intoto.json` (an
in-toto Statement v1 over the attested PDFs and modules), `standards.json`
(this register) and `CITATION.cff` (copied from the repository root)."""

import argparse
import json
import tomllib
from xml.sax.saxutils import escape

from . import archmodel, frontier, repo
from .semantic import (BOOL, STR, all_members, b, call, definition, eq_string, field_of_each, holds, if_, list_t, lookup_field,
                       lst, match_list, member_string, named, proj, record, s, strings, structure, var)

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Standards.lex.tex"
REGISTER = API / "model" / "standards.toml"
CITATION = repo.ROOT / "CITATION.cff"

PAGES_URL = "https://afflom.github.io/rule30/"
REPOSITORY = "https://github.com/afflom/rule30"
PAPER_TITLE = "Rule thirty: the places of infinity"
AUTHOR = {"family": "Flom", "given": "Alex"}

# The ids the site's navigation (S2) and visualizations (S3) use: declared
# here so the standards can name them and the kernel can decide that each is
# covered by a standard before the page that renders them lands.
NAVIGATION = ["nav-primary", "nav-breadcrumb", "nav-stepper"]
VISUALIZATIONS = ["viz-triangle", "viz-tower", "viz-ledger", "viz-rays", "viz-defects", "viz-dyadic"]
MODULES = ["Api", "Register", "Architecture", "Presentation", "Application", "Observer", "Convert", "Standards", "Rule30Core",
           "Sequences", "Discovery"]
WORKFLOWS = ["view-workflow"]
REGISTERS = ["authorities", "ids", "ledger", "commands", "standards", "projection", "contracts", "errors", "dependencies",
             "runtime-roots", "stdlib-package", "observer", "sequences"]

# The two ISO rows keep the vendored lexicon facets `Architecture.lex.tex`
# is built on (prism.arch, prism.qual); `prismmodel.check` confirms the
# entries exist under rule30-api/language.
FACETS = {
    "iso-42010": {"package": "prism.arch", "entries": ["arch-concern", "arch-model-kind", "arch-stakeholder", "arch-view", "arch-viewpoint"]},
    "iso-25010": {"package": "prism.qual", "entries": ["qual-characteristic", "qual-measure", "qual-requirement", "qual-subcharacteristic"]},
}


def lean_toolchain():
    return (API / "lean-toolchain").read_text().strip()


def lexlean_pin():
    """`<version>, language <language>` from production's pin and lexlean.lock."""
    from .production import LEXLEAN_VERSION
    lock = tomllib.loads((API / "lexlean.lock").read_text())
    return f"{LEXLEAN_VERSION}, language {lock['language']}, compiler semantics {lock['compiler_semantics'][:12]}"


def _commands():
    from . import apimodel
    return [r["name"] for r in apimodel.surface()]


def _json_commands():
    """The commands whose --json report has a published schema (contracts.toml)."""
    from . import schema
    from .prismmodel import SCHEMA_OF
    return sorted({n[:-len("-result")].replace("-", "_") for n in schema.RESULTS} | set(SCHEMA_OF))


def rows():
    """The standards register: id, name, authority, version, scope,
    realizedBy, conformance, coverage. Derived lists (the measures' commands,
    the command surface, the artifacts) come from their models, so a new
    command or artifact is covered or the kernel refuses the module."""
    from .presentationmodel import ARTIFACTS, JOURNEYS, PANELS
    artifacts = [a["id"] for a in ARTIFACTS]
    panels = [p["id"] for p in PANELS]
    journeys = [j["id"] for j in JOURNEYS]
    measure_commands = sorted({m["command"] for m in archmodel.MEASURES})
    pdfs = [a["id"] for a in ARTIFACTS if a["media"] == "application/pdf"]
    svgs = [a["id"] for a in ARTIFACTS if a["media"] == "image/svg+xml"]
    tests = "python3 -m unittest scripts.tests.test_r30.StandardsTests"
    return [
        {"id": "iso-42010", "name": "ISO/IEC/IEEE 42010:2022, Architecture description",
         "authority": "https://www.iso.org/standard/74393.html", "version": "2022",
         "scope": "Stakeholders, concerns, viewpoints and views of the proof effort on Foundation.Arch; every panel of the site is governed by a viewpoint.",
         "realizedBy": ["Architecture", "architecture-module", "Presentation"],
         "conformance": "bin/r30 verify api: everyConcernFramed, viewpointsFrameHeldConcerns, everyViewpointGovernsAView (Architecture), panelsGovernedByViewpoints (Presentation)",
         "coverage": "implemented"},
        {"id": "iso-25010", "name": "ISO/IEC 25010:2023, Product quality model",
         "authority": "https://www.iso.org/standard/78176.html", "version": "2023",
         "scope": "What an optimal implementation is here: characteristics, subcharacteristics, requirements and measures with thresholds on Foundation.Qual, each measure naming the command that reports it.",
         "realizedBy": ["Architecture", "quality", "architecture-module"] + measure_commands,
         "conformance": "bin/r30 verify api: everyRequirementMeasured, everyMeasureCommandExists (Architecture), publicationWithinBudget (Application)",
         "coverage": "implemented"},
        {"id": "wcag-2.2", "name": "W3C WCAG 2.2, Web Content Accessibility Guidelines",
         "authority": "https://www.w3.org/TR/WCAG22/", "version": "2.2 (Recommendation, 2023-10-05)",
         "scope": "The site at level AA: 4.5:1 text contrast in both themes, one visible focus ring, a skip link, reduced motion honoured, keyboard operation of every control and step.",
         "realizedBy": ["site"] + panels + NAVIGATION,
         "conformance": "python3 -m unittest scripts.tests.test_r30.AccessibilityTests (contrast measured from the stylesheet, landmarks, focus, motion, keyboard)",
         "coverage": "implemented"},
        {"id": "wai-aria-1.2", "name": "W3C WAI-ARIA 1.2 and the ARIA Authoring Practices Guide",
         "authority": "https://www.w3.org/TR/wai-aria-1.2/", "version": "1.2 (Recommendation, 2023-06-06); APG patterns",
         "scope": "The navigation of the site: the primary navigation, the breadcrumb and the stepper follow the APG patterns (roles, aria-current, arrow keys), the status region is live.",
         "realizedBy": ["site"] + NAVIGATION,
         "conformance": "python3 -m unittest scripts.tests.test_r30.AccessibilityTests (role, aria-current, aria-pressed, role=status, arrow keys)",
         "coverage": "implemented"},
        {"id": "html-living-standard", "name": "WHATWG HTML Living Standard",
         "authority": "https://html.spec.whatwg.org/multipage/", "version": "living standard",
         "scope": "The page's landmarks (header, nav, main, footer), the one-document site with its data in a JSON script element and its metadata in the head.",
         "realizedBy": ["site"] + NAVIGATION,
         "conformance": "python3 -m unittest scripts.tests.test_r30.AccessibilityTests.test_landmarks_focus_motion_and_keyboard",
         "coverage": "implemented"},
        {"id": "svg-2", "name": "W3C SVG 2",
         "authority": "https://www.w3.org/TR/SVG2/", "version": "2 (Candidate Recommendation, 2018-10-04)",
         "scope": "The Rule 30 picture, the logo and the visualizations are SVG documents with a title and a description, crisp cells, colours from the page's tokens.",
         "realizedBy": svgs + VISUALIZATIONS,
         "conformance": "python3 -m unittest scripts.tests.test_r30.SiteTests.test_rule30_rows_and_logo (parsed as SVG, no script)",
         "coverage": "implemented"},
        {"id": "wai-aria-graphics-1.0", "name": "W3C WAI-ARIA Graphics Module 1.0",
         "authority": "https://www.w3.org/TR/graphics-aria-1.0/", "version": "1.0 (Recommendation, 2018-10-02)",
         "scope": "Every drawing carries role=img with aria-labelledby pointing at its title and description; the interactive visualizations use graphics-document and graphics-symbol.",
         "realizedBy": svgs + VISUALIZATIONS,
         "conformance": "python3 -m unittest scripts.tests.test_r30.SiteTests.test_statements_picture_and_explainer_artifacts (role=img, aria-labelledby)",
         "coverage": "implemented"},
        {"id": "schema-org", "name": "schema.org vocabulary (JSON-LD)",
         "authority": "https://schema.org/", "version": "current release (https://schema.org/docs/releases.html)",
         "scope": "A LearningResource for every pedagogical step of every journey, the paper as ScholarlyArticle, the repository as SoftwareSourceCode, the register as Dataset, embedded in the page and published as schema.json.",
         "realizedBy": ["jsonld", "site", "paper-pdf", "register-json", "readme"] + journeys,
         "conformance": tests + ".test_schema_org_describes_every_step_the_paper_the_repository_and_the_register",
         "coverage": "implemented"},
        {"id": "json-ld-1.1", "name": "W3C JSON-LD 1.1",
         "authority": "https://www.w3.org/TR/json-ld11/", "version": "1.1 (Recommendation, 2020-07-16)",
         "scope": "The serialization of the schema.org and PROV-O graphs: a @context, a @graph, ids under the published URL.",
         "realizedBy": ["jsonld", "provenance"],
         "conformance": tests + " (both documents parse and carry @context and @graph)",
         "coverage": "implemented"},
        {"id": "prov-o", "name": "W3C PROV-O, the PROV Ontology",
         "authority": "https://www.w3.org/TR/prov-o/", "version": "Recommendation, 2013-04-30",
         "scope": "Provenance of every claim: a proved claim prov:wasDerivedFrom its Lean theorem and prov:wasAttributedTo the Lean kernel, attested by the paper's LexLean attestation and the module's kappa-label; the view prov:wasGeneratedBy the render of this commit under the view workflow.",
         "realizedBy": ["provenance", "view-workflow", "view_render", "frontier_check", "kappa", "verify"],
         "conformance": tests + ".test_provenance_derives_every_proved_claim_from_its_theorem",
         "coverage": "implemented"},
        {"id": "json-schema-2020-12", "name": "JSON Schema 2020-12",
         "authority": "https://json-schema.org/draft/2020-12/schema", "version": "2020-12",
         "scope": "The closed schemas of register.json, the interface sheets, standards.json and the --json reports (rule30-api/schemas), validated by the tests and referenced from openapi.json.",
         "realizedBy": ["register-json", "standards", "openapi"] + _json_commands(),
         "conformance": "python3 -m unittest scripts.tests.test_r30.ResultSchemaTests; bin/r30 api check",
         "coverage": "implemented"},
        {"id": "openapi-3.1", "name": "OpenAPI Specification 3.1",
         "authority": "https://spec.openapis.org/oas/v3.1.1", "version": "3.1.1 (2024-10-24)",
         "scope": "The r30 command surface as an API description: one path per command of the parser, its arguments as parameters, its responses from the result schemas, the same leaves as Api.lex.tex and the MCP tools.",
         "realizedBy": ["openapi"] + _commands(),
         "conformance": tests + ".test_openapi_describes_the_command_surface; bin/r30 api check (Api.lex.tex)",
         "coverage": "implemented"},
        {"id": "gherkin", "name": "Gherkin (Cucumber reference)",
         "authority": "https://cucumber.io/docs/gherkin/reference/", "version": "Gherkin reference (current)",
         "scope": "One scenario per conformance id in features/suites, tagged with the id and its honesty level, generated with the registers.",
         "realizedBy": ["api_sync", "api_check"],
         "conformance": "python3 -m unittest scripts.tests.test_r30.ConformanceTests; bin/r30 api check",
         "coverage": "implemented"},
        {"id": "citation-cff", "name": "Citation File Format 1.2.0",
         "authority": "https://citation-file-format.github.io/", "version": "1.2.0",
         "scope": "CITATION.cff at the repository root (and copied into the view): the author, the title of the paper, the repository and the published view.",
         "realizedBy": ["citation", "readme"],
         "conformance": tests + ".test_citation_file_names_the_author_the_title_and_the_repository",
         "coverage": "implemented"},
        {"id": "spdx", "name": "SPDX License Expressions (SPDX 2.3, ISO/IEC 5962:2021)",
         "authority": "https://spdx.github.io/spdx-spec/v2.3/SPDX-license-expressions/", "version": "2.3",
         "scope": "License identifiers of the vendored sources: the repository is MIT (LICENSE at the root, `license: MIT` in CITATION.cff); the prism-stdlib register carries the SPDX expression of its vendored license files.",
         "realizedBy": ["stdlib-package", "citation"],
         "conformance": tests + ".test_spdx_expressions_are_well_formed",
         "coverage": "implemented"},
        {"id": "sitemap-protocol", "name": "Sitemaps XML protocol 0.9",
         "authority": "https://www.sitemaps.org/protocol.html", "version": "0.9",
         "scope": "sitemap.xml: the page and the deep link of every step of every journey; robots.txt names the sitemap.",
         "realizedBy": ["sitemap", "robots", "site"] + journeys,
         "conformance": tests + ".test_sitemap_lists_every_step_deep_link",
         "coverage": "implemented"},
        {"id": "open-graph", "name": "The Open Graph protocol",
         "authority": "https://ogp.me/", "version": "ogp.me (2014-10)",
         "scope": "og:title, og:type, og:url, og:description and og:image in the page's head, injected with the JSON-LD at render.",
         "realizedBy": ["site", "logo"],
         "conformance": tests + ".test_site_head_carries_json_ld_and_open_graph",
         "coverage": "implemented"},
        {"id": "rfc-8785", "name": "RFC 8785, JSON Canonicalization Scheme (JCS)",
         "authority": "https://www.rfc-editor.org/rfc/rfc8785", "version": "2020-06",
         "scope": "The identity of the published JSON contracts (sha256-canonical-json in contracts.toml) and the canonical JSON of the LexLean attestations; uor-addr labels JSON under JCS.",
         "realizedBy": ["register-json", "statements", "kappa"],
         "conformance": "python3 -m unittest scripts.tests.test_kappa (the no-prefix rule on the JCS vector)",
         "coverage": "implemented"},
        {"id": "rivest-csexp", "name": "Rivest, S-Expressions (canonical form, section 4.3)",
         "authority": "https://people.csail.mit.edu/rivest/Sexp.txt", "version": "draft-rivest-sexp-00, 1997-05-04",
         "scope": "The kappa-label of a research module: the SHA-256 of the canonical S-expression of the declarations the kernel replays, as UOR-Foundation/uor-addr mints labels; the key of the replay receipts. The same canonical form labels the sequences of the basis, (sequence <lexeme> <parameters>), their transforms and the relations the discovery engines find, (relation <sorted column labels>).",
         "realizedBy": ["kappa", "provenance", "sequences", "discover", "Sequences", "Discovery"],
         "conformance": "python3 -m unittest scripts.tests.test_kappa; bin/r30 kappa <modules>; bin/r30 api check (sequences)",
         "coverage": "implemented"},
        {"id": "in-toto-statement-v1", "name": "in-toto Attestation Framework, Statement v1",
         "authority": "https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md", "version": "v1",
         "scope": "attestations.intoto.json: a Statement whose subjects are the attested PDFs and the paper's sources with their SHA-256 digests and whose predicate is the paper's LexLean attestation.",
         "realizedBy": ["attestations", "pdf-manifest", "verify"] + pdfs,
         "conformance": tests + ".test_in_toto_statement_subjects_are_the_attested_documents",
         "coverage": "implemented"},
        {"id": "oci-distribution", "name": "OCI Distribution Specification",
         "authority": "https://github.com/opencontainers/distribution-spec/blob/main/spec.md", "version": "1.1.0 (2024-02)",
         "scope": "Planned: a kappa-registry serving the replay receipts and certified bundles by content address; today only the kappa-labels that would address them exist.",
         "realizedBy": ["kappa"],
         "conformance": "bin/r30 kappa <modules> (the labels); no registry runs yet",
         "coverage": "planned"},
        {"id": "iana-media-types", "name": "IANA Media Types (RFC 6838)",
         "authority": "https://www.iana.org/assignments/media-types/", "version": "RFC 6838 (2013-01)",
         "scope": "Every published artifact declares its media type in Presentation.lex.tex; the contracts register declares the vendor types of the JSON reports.",
         "realizedBy": artifacts,
         "conformance": "bin/r30 verify api: artifactPathsDistinct, panelsReadArtifacts (Presentation); " + tests,
         "coverage": "implemented"},
        {"id": "lean-4", "name": "Lean 4 (the kernel)",
         "authority": "https://github.com/leanprover/lean4", "version": lean_toolchain(),
         "scope": "Every proved claim names a theorem the Lean kernel checked under propext and Quot.sound; the research modules are kernel-replayed with leanchecker.",
         "realizedBy": ["Register", "axioms", "choice_audit", "frontier_check", "kappa", "module_build"],
         "conformance": "bin/r30 frontier check; bin/r30 axioms <Lean names>; bin/r30 choice-audit",
         "coverage": "implemented"},
        {"id": "lexlean", "name": "UOR-Foundation/LexLean (closed-lexicon LaTeX to Lean 4)",
         "authority": "https://github.com/UOR-Foundation/LexLean", "version": lexlean_pin(),
         "scope": "The authoring surface: the paper, the register and these API modules are LexLean modules verified by lexlean; the production roots export to certified Rust.",
         "realizedBy": MODULES + ["verify", "check", "api_sync", "api_check", "api_production"],
         "conformance": "bin/r30 verify api; bin/r30 check api; bin/r30 api check",
         "coverage": "implemented"},
    ]


def declared_ids():
    """Every id a standard may be realized by, in the order the module lists them."""
    from .presentationmodel import ARTIFACTS, JOURNEYS, PANELS
    return (MODULES + [a["id"] for a in ARTIFACTS] + [p["id"] for p in PANELS] + [j["id"] for j in JOURNEYS] + _commands()
            + NAVIGATION + VISUALIZATIONS + WORKFLOWS + REGISTERS)


def problems(standards=None):
    """What `Standards.lex.tex` decides, checked in Python first so a failure
    names the row before `lexlean verify` reports a false `decide`."""
    from .presentationmodel import ARTIFACTS, JOURNEYS, PANELS
    standards = rows() if standards is None else standards
    declared = set(declared_ids())
    realizers = {r for st in standards for r in st["realizedBy"]}
    out = []
    ids = [st["id"] for st in standards]
    if len(set(ids)) != len(ids):
        out.append("standard ids are not distinct")
    for st in standards:
        if not st["authority"].startswith("https://"):
            out.append(f"standard {st['id']}: no https authority")
        if not st["realizedBy"]:
            out.append(f"standard {st['id']}: realized by nothing")
        for r in st["realizedBy"]:
            if r not in declared:
                out.append(f"standard {st['id']}: realizer {r} is not declared")
    for kind, group in (("panel", [p["id"] for p in PANELS]), ("artifact", [a["id"] for a in ARTIFACTS]),
                        ("journey", [j["id"] for j in JOURNEYS]), ("command", _commands()),
                        ("navigation", NAVIGATION), ("visualization", VISUALIZATIONS)):
        for x in group:
            if x not in realizers:
                out.append(f"{kind} {x} names no standard")
    return out


def declarations():
    st_t = named("Standard")
    standards = rows()
    realizers = call("standardRealizers", call("standards"))

    def covered(name, ids_expr):
        return holds(name, call("allMembers", ids_expr, realizers))

    return [
        structure("Standard", [("id", STR), ("name", STR), ("authority", STR), ("version", STR), ("scope", STR),
                               ("realizedBy", list_t(STR)), ("conformance", STR), ("coverage", STR)]),
        definition("standards", list_t(st_t), lst([
            record("Standard", id=s(x["id"]), name=s(x["name"]), authority=s(x["authority"]), version=s(x["version"]),
                   scope=s(x["scope"]), realizedBy=strings(x["realizedBy"]), conformance=s(x["conformance"]),
                   coverage=s(x["coverage"])) for x in standards], st_t)),
        definition("modules", list_t(STR), strings(MODULES)),
        definition("navigation", list_t(STR), strings(NAVIGATION)),
        definition("visualizations", list_t(STR), strings(VISUALIZATIONS)),
        definition("workflows", list_t(STR), strings(WORKFLOWS)),
        definition("registers", list_t(STR), strings(REGISTERS)),
        member_string(), all_members(),
        definition("appendStrings", list_t(STR),
                   match_list(var("xs"), var("ys"), "head", "tail",
                              {"kind": "cons", "head": var("head"), "tail": call("appendStrings", var("tail"), var("ys"))}),
                   parameters=[("xs", list_t(STR)), ("ys", list_t(STR))], recursive="xs"),
        definition("distinctStrings", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(call("memberString", var("head"), var("tail")), b(False), call("distinctStrings", var("tail")))),
                   parameters=[("xs", list_t(STR))], recursive="xs"),
        definition("allNonEmpty", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(eq_string(var("head"), s("")), b(False), call("allNonEmpty", var("tail")))),
                   parameters=[("xs", list_t(STR))], recursive="xs"),
        field_of_each("standardIds", st_t, "id"),
        field_of_each("standardAuthorities", st_t, "authority"),
        lookup_field("standardVersion", st_t, "id", "version", STR, s("")),
        definition("standardRealizers", list_t(STR),
                   match_list(var("xs"), {"kind": "nil", "element": STR}, "head", "tail",
                              call("appendStrings", proj(var("head"), "realizedBy"), call("standardRealizers", var("tail")))),
                   parameters=[("xs", list_t(st_t))], recursive="xs"),
        # a standard realized by nothing has an empty realizer list
        definition("eachRealized", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              {"kind": "match", "scrutinee": proj(var("head"), "realizedBy"), "branches": [
                                  {"constructor": {"name": "List.nil"}, "binders": [], "body": b(False)},
                                  {"constructor": {"name": "List.cons"}, "binders": ["r", "rs"], "body": call("eachRealized", var("tail"))}]}),
                   parameters=[("xs", list_t(st_t))], recursive="xs"),
        # every id a standard may name: modules, artifacts, panels, journeys, commands, navigation, visualizations, workflows, registers
        definition("declaredIds", list_t(STR),
                   call("appendStrings", call("modules"),
                        call("appendStrings", call("artifactIds", call("artifacts", module="Presentation"), module="Presentation"),
                             call("appendStrings", call("panelIds", call("panels", module="Presentation"), module="Presentation"),
                                  call("appendStrings", call("journeyIds", call("journeys", module="Presentation"), module="Presentation"),
                                       call("appendStrings", call("commandNames", call("commands", module="Api"), module="Architecture"),
                                            call("appendStrings", call("navigation"),
                                                 call("appendStrings", call("visualizations"),
                                                      call("appendStrings", call("workflows"), call("registers")))))))))),
        holds("standardIdsDistinct", call("distinctStrings", call("standardIds", call("standards")))),
        holds("everyStandardHasAuthority", call("allNonEmpty", call("standardAuthorities", call("standards")))),
        holds("everyStandardRealized", call("eachRealized", call("standards"))),
        holds("realizersDeclared", call("allMembers", realizers, call("declaredIds"))),
        covered("panelsNameAStandard", call("panelIds", call("panels", module="Presentation"), module="Presentation")),
        covered("artifactsNameAStandard", call("artifactIds", call("artifacts", module="Presentation"), module="Presentation")),
        covered("journeysNameAStandard", call("journeyIds", call("journeys", module="Presentation"), module="Presentation")),
        covered("commandsNameAStandard", call("commandNames", call("commands", module="Api"), module="Architecture")),
        covered("navigationNamesAStandard", call("navigation")),
        covered("visualizationsNameAStandard", call("visualizations")),
        holds("leanToolchainPinned", eq_string(call("standardVersion", s("lean-4"), call("standards")), s(lean_toolchain()))),
        holds("lexleanPinned", eq_string(call("standardVersion", s("lexlean"), call("standards")), s(lexlean_pin()))),
    ]


def render():
    from . import lexmod
    return lexmod.module("Standards", declarations(), imports=["Api", "Architecture", "Presentation"])


def _q(v):
    return '"' + str(v).replace("\\", "\\\\").replace('"', '\\"') + '"'


def _list(xs):
    return "[" + ", ".join(_q(x) for x in xs) + "]"


def register_toml():
    """`rule30-api/model/standards.toml` (`prismpm/standards/1`): the same rows
    as the module; the ISO rows keep their vendored lexicon facets."""
    lines = ['spec = "prismpm/standards/1"', ""]
    for st in rows():
        lines += ["[[standard]]", f"id = {_q(st['id'])}", f"name = {_q(st['name'])}", f"authority = {_q(st['authority'])}",
                  f"version = {_q(st['version'])}", f"scope = {_q(st['scope'])}", "realized_by = " + _list(st["realizedBy"]),
                  f"conformance = {_q(st['conformance'])}", f"coverage_state = {_q(st['coverage'])}",
                  f"release_scope = {'true' if st['coverage'] == 'implemented' else 'false'}"]
        facet = FACETS.get(st["id"])
        if facet:
            lines += [f"facet_package = {_q(facet['package'])}", "facet_entries = " + _list(facet["entries"])]
        lines.append("")
    return "\n".join(lines)


STANDARDS_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "r30/standards/1",
    "title": "The standards register (view/standards.json)",
    "type": "array",
    "items": {
        "type": "object",
        "required": ["id", "name", "authority", "version", "scope", "realizedBy", "conformance", "coverage"],
        "additionalProperties": False,
        "properties": {
            "id": {"type": "string", "pattern": "^[a-z][a-z0-9.-]*$"},
            "name": {"type": "string"},
            "authority": {"type": "string", "pattern": "^https://"},
            "version": {"type": "string"},
            "scope": {"type": "string"},
            "realizedBy": {"type": "array", "items": {"type": "string"}},
            "conformance": {"type": "string"},
            "coverage": {"type": "string", "enum": ["implemented", "planned"]},
        },
    },
}


def sync():
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    text = render()
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "standards": len(rows()), "changed": changed}


def check():
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Standards.lex.tex is missing; run `bin/r30 api sync`"}
    if MODULE.read_text() != render():
        return {"ok": False, "reason": "Standards.lex.tex drifted; run `bin/r30 api sync`"}
    faults = problems()
    if faults:
        return {"ok": False, "reason": "standards register: " + "; ".join(faults)}
    return {"ok": True, "reason": None}


# ---------------------------------------------------------------------------
# The machine-readable artifacts the standards call for.

def _inline_defs(node, defs):
    """A schema with its `#/$defs/<name>` references inlined, so it can sit
    under an OpenAPI document's components without a resource root."""
    if isinstance(node, dict):
        if "$ref" in node and node["$ref"].startswith("#/$defs/"):
            return _inline_defs(defs[node["$ref"][len("#/$defs/"):]], defs)
        return {k: _inline_defs(v, defs) for k, v in node.items() if k != "$defs"}
    if isinstance(node, list):
        return [_inline_defs(x, defs) for x in node]
    return node


def _component(schema_doc):
    return _inline_defs({k: v for k, v in schema_doc.items() if k not in ("$schema", "$id")}, schema_doc.get("$defs", {}))


def openapi():
    """OpenAPI 3.1: one path per leaf of the parser (`/<path>`), the
    operation's parameters from argparse, the response from the result schema
    when the command has one, the typed failures from the error register."""
    from . import cli, schema
    from .errors import ERRORS
    from .mcp_server import _arguments, _leaves, _tool_name
    from .presentationmodel import APPLICATION_RECORD, BRAND
    from .prismmodel import MUTATES, REGISTER_SCHEMA, SHEET_SCHEMA, result_schema
    components = {name: _component(schema.document(name)) for name in schema.RESULTS}
    components["register"] = _component(REGISTER_SCHEMA)
    components["interface-sheet"] = _component(SHEET_SCHEMA)
    components["error"] = {"type": "object", "required": ["code", "title", "detail", "exit"], "additionalProperties": False,
                           "properties": {"code": {"type": "string", "pattern": "^R30[0-9]{4}$"}, "title": {"type": "string"},
                                          "detail": {"type": "string"}, "exit": {"type": "integer", "enum": [1, 2]}}}
    by_schema = {f"r30/{name}/1": name for name in components}
    paths = {}
    for path, parser, help_text in _leaves(cli.build_parser()):
        name = _tool_name(path)
        parameters = []
        for a in _arguments(parser):
            if isinstance(a, argparse._StoreTrueAction):
                t = {"type": "boolean"}
            elif a.nargs in ("+", "*"):
                t = {"type": "array", "items": {"type": "string"}}
            elif a.type is int:
                t = {"type": "integer"}
            else:
                t = {"type": "string"}
            optional = bool(a.option_strings) or a.nargs in ("?", "*")
            p = {"name": a.dest, "in": "query", "required": not optional, "schema": t}
            if a.help:
                p["description"] = a.help
            if a.default not in (None, False, argparse.SUPPRESS) and not isinstance(a.default, list):
                p["schema"] = {**t, "default": a.default}
            parameters.append(p)
        sid = result_schema(name)
        component = by_schema.get(sid)
        ok = {"description": f"the report of `r30 {' '.join(path)}` (`--json`)"}
        if component:
            ok["content"] = {"application/json": {"schema": {"$ref": f"#/components/schemas/{component}"}}}
        errors = [e for e in ERRORS if name in e["commands"]]
        responses = {"200": ok}
        if errors:
            responses["default"] = {"description": "a typed failure of errors.toml: " + "; ".join(f"{e['code']} {e['title']} (exit {e['exit']})" for e in errors),
                                    "content": {"application/json": {"schema": {"$ref": "#/components/schemas/error"}}}}
        op = {"operationId": name, "summary": help_text or name, "parameters": parameters, "responses": responses,
              "x-r30-mutates": MUTATES.get(name, "never"), "x-r30-result-schema": sid, "x-mcp-tool": name}
        paths["/" + "/".join(path)] = {("post" if MUTATES.get(name, "never") != "never" else "get"): op}
    return {
        "openapi": "3.1.0",
        "jsonSchemaDialect": schema.DRAFT,
        "info": {"title": f"{BRAND['name']}: the r30 command surface", "version": APPLICATION_RECORD["version"],
                 "summary": "Every command of bin/r30, as Api.lex.tex declares it and the MCP server serves it.",
                 "description": "A path per leaf of the command-line parser; GET for a command that only reads, POST for one that mutates "
                                "(model/commands.toml names what). The same parser generates Api.lex.tex, whose command count the kernel decides.",
                 "contact": {"name": f"{AUTHOR['given']} {AUTHOR['family']}", "url": REPOSITORY}},
        "externalDocs": {"description": "The current view", "url": PAGES_URL},
        "servers": [{"url": "r30://local", "description": "bin/r30 in a checkout of the repository; the MCP server exposes the same operations as tools"}],
        "paths": paths,
        "components": {"schemas": components},
    }


def step_url(step):
    return f"{PAGES_URL}#{step['journey']}/{step['id']}"


def sitemap(steps, lastmod):
    """Sitemaps 0.9: the page and the deep link of every step."""
    urls = [PAGES_URL] + [step_url(st) for st in steps]
    body = "".join(f"\n  <url>\n    <loc>{escape(u)}</loc>\n    <lastmod>{lastmod}</lastmod>\n  </url>" for u in urls)
    return f'<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">{body}\n</urlset>\n'


def robots():
    return f"User-agent: *\nAllow: /\nSitemap: {PAGES_URL}sitemap.xml\n"


def kappa_labels():
    """{module: {kappa, receipt}} from the kernel-replay receipts of the last
    accepted gate (`scripts/replay_research.py`, under the Git common
    directory's rule30-validation/replay, or RULE30_REPLAY_CACHE), the latest
    receipt per module; empty when none is readable (CI renders without
    them), and the provenance then says so instead of computing a label,
    which would need the built research library."""
    import os
    from pathlib import Path
    roots = []
    if os.environ.get("RULE30_REPLAY_CACHE"):
        roots.append(Path(os.environ["RULE30_REPLAY_CACHE"]))
    code, out, _ = repo.run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"])
    if code == 0 and out.strip():
        roots.append(Path(out.strip()) / "rule30-validation" / "replay")
    found = {}
    for root in roots:
        if not root.is_dir():
            continue
        for receipt in root.rglob("*.ok"):
            try:
                lines = receipt.read_text().splitlines()
            except OSError:
                continue
            if len(lines) >= 2 and lines[1].startswith("kappa sha256:"):
                stamp = receipt.stat().st_mtime
                if lines[0] not in found or found[lines[0]]["stamp"] < stamp:
                    found[lines[0]] = {"kappa": lines[1].split()[1], "receipt": receipt.name, "stamp": stamp}
    return {m: {"kappa": r["kappa"], "receipt": r["receipt"]} for m, r in found.items()}


def module_of(lean_name):
    """The research module a Lean name belongs to: the longest module prefix."""
    modules = sorted(repo.research_modules(), key=len, reverse=True)
    return next((m for m in modules if lean_name.startswith(m + ".")), None)


def provenance(claims, commit, generated, attestation, kappas=None):
    """PROV-O as JSON-LD: the claims as entities (a proved one derived from
    its Lean theorem and attributed to the kernel; an open one derived from
    nothing), the theorems and their modules with kappa-labels, the agents
    (the kernel, lexlean, leanchecker), the activities (the gate's register
    check and replay, the paper's attestation, this render)."""
    kappas = kappa_labels() if kappas is None else kappas
    base = PAGES_URL
    ctx = {"prov": "http://www.w3.org/ns/prov#", "schema": "https://schema.org/", "xsd": "http://www.w3.org/2001/XMLSchema#",
           "r30": base + "ns#",
           "prov:wasDerivedFrom": {"@type": "@id"}, "prov:wasAttributedTo": {"@type": "@id"}, "prov:wasGeneratedBy": {"@type": "@id"},
           "prov:wasAssociatedWith": {"@type": "@id"}, "prov:used": {"@type": "@id"}, "prov:wasInvalidatedBy": {"@type": "@id"},
           "prov:wasInformedBy": {"@type": "@id"}}
    kernel = {"@id": "r30:agent/lean-kernel", "@type": ["prov:Agent", "prov:SoftwareAgent"], "schema:name": "the Lean 4 kernel",
              "schema:softwareVersion": lean_toolchain(), "r30:axiomsAllowed": ["propext", "Quot.sound"]}
    lexlean_agent = {"@id": "r30:agent/lexlean", "@type": ["prov:Agent", "prov:SoftwareAgent"], "schema:name": "lexlean",
                     "schema:softwareVersion": lexlean_pin()}
    checker = {"@id": "r30:agent/leanchecker", "@type": ["prov:Agent", "prov:SoftwareAgent"], "schema:name": "leanchecker (kernel replay)"}
    author = {"@id": "r30:agent/author", "@type": ["prov:Agent", "prov:Person"], "schema:givenName": AUTHOR["given"], "schema:familyName": AUTHOR["family"]}
    gate = {"@id": "r30:activity/gate", "@type": "prov:Activity", "schema:name": "the pre-commit gate: bin/r30 frontier check and the kernel replay of the research modules",
            "prov:wasAssociatedWith": ["r30:agent/lean-kernel", "r30:agent/leanchecker"]}
    render = {"@id": f"r30:activity/render/{commit or 'uncommitted'}", "@type": "prov:Activity", "schema:name": "bin/r30 view render",
              "prov:endedAtTime": {"@value": generated, "@type": "xsd:string"}, "r30:commit": commit or None,
              "prov:wasAssociatedWith": ["r30:agent/author"], "r30:workflow": ".github/workflows/view.yml", "prov:wasInformedBy": "r30:activity/gate"}
    graph = [kernel, lexlean_agent, checker, author, gate, render]
    if attestation and attestation.get("id"):
        graph.append({"@id": f"r30:activity/attestation/{attestation['id']}", "@type": "prov:Activity",
                      "schema:name": "lexlean verify of the paper (the latest accepted attestation)",
                      "r30:attestationId": attestation["id"], "r30:sourceId": attestation.get("sourceId"), "r30:semanticId": attestation.get("semanticId"),
                      "r30:spec": attestation.get("spec"), "prov:wasAssociatedWith": ["r30:agent/lexlean", "r30:agent/lean-kernel"]})
    modules_seen = {}
    for c in claims:
        entity = {"@id": f"r30:claim/{c['id']}", "@type": "prov:Entity", "schema:name": c["id"], "r30:status": c["status"],
                  "schema:description": c["statement"], "prov:wasGeneratedBy": render["@id"]}
        if c.get("depends"):
            entity["r30:dependsOn"] = [f"r30:claim/{d}" for d in c["depends"]]
        if c["status"] == "proved":
            theorem = f"r30:lean/{c['lean']}"
            entity["prov:wasDerivedFrom"] = theorem
            entity["prov:wasAttributedTo"] = "r30:agent/lean-kernel"
            entity["r30:provedBy"] = "r30:activity/gate"
            if c.get("lexeme"):
                entity["r30:lexeme"] = c["lexeme"]
                if attestation and attestation.get("id"):
                    entity["r30:attestedBy"] = f"r30:activity/attestation/{attestation['id']}"
            module = module_of(c["lean"])
            theorem_entity = {"@id": theorem, "@type": "prov:Entity", "schema:name": c["lean"], "r30:kind": "Lean theorem",
                              "prov:wasAttributedTo": "r30:agent/lean-kernel"}
            if module:
                theorem_entity["r30:module"] = f"r30:module/{module}"
                if module not in modules_seen:
                    row = {"@id": f"r30:module/{module}", "@type": "prov:Entity", "schema:name": module, "r30:kind": "Lean module",
                           "prov:wasAttributedTo": "r30:agent/leanchecker"}
                    if module in kappas:
                        row["r30:kappa"] = kappas[module]["kappa"]
                        row["r30:kappaSource"] = f"kernel-replay receipt {kappas[module]['receipt']} of the last accepted gate"
                    else:
                        row["r30:kappaNote"] = "no replay receipt readable at render; `bin/r30 kappa " + module + "` prints the label from the built library"
                    modules_seen[module] = row
            graph.append(theorem_entity)
        elif c["status"] == "refuted":
            entity["r30:refutedBy"] = c.get("lean") or "experiment (see the register's note)"
            entity["prov:wasInvalidatedBy"] = "r30:activity/gate"
        else:
            entity["r30:derivation"] = "none: the claim is " + c["status"] + " and nothing here calls it proved"
        graph.append(entity)
    graph.extend(modules_seen.values())
    return {"@context": ctx, "@id": base + "provenance.jsonld", "prov:generatedAtTime": generated,
            "r30:kappaLabels": "recorded" if kappas else "omitted (no replay receipt readable at render)", "@graph": graph}


def schema_org(steps, journeys, stakeholders, commit, documents):
    """schema.org JSON-LD: the site, the repository, the paper, the register,
    and a LearningResource for every step of every journey."""
    from .presentationmodel import APPLICATION_RECORD, BRAND
    names = {st["id"]: st["name"] for st in stakeholders}
    person = {"@type": "Person", "givenName": AUTHOR["given"], "familyName": AUTHOR["family"], "name": f"{AUTHOR['given']} {AUTHOR['family']}"}
    about = {"@type": "Thing", "name": "Wolfram's Rule 30 Prize, Problem 1", "url": "https://www.rule30prize.org"}
    pdfs = [{"@type": "MediaObject", "name": d["name"], "contentUrl": PAGES_URL + d["path"], "encodingFormat": "application/pdf",
             "sha256": d["pdfSha256"]} for d in documents if d.get("path")]
    graph = [
        {"@id": PAGES_URL, "@type": "WebSite", "name": BRAND["name"], "alternateName": BRAND["tagline"], "description": BRAND["description"],
         "url": PAGES_URL, "author": person, "about": about, "inLanguage": "en"},
        {"@id": REPOSITORY, "@type": "SoftwareSourceCode", "name": "afflom/rule30", "codeRepository": REPOSITORY,
         "programmingLanguage": ["Lean 4", "LexLean", "Python"], "runtimePlatform": lean_toolchain(), "version": APPLICATION_RECORD["version"],
         "author": person, "about": about, "url": PAGES_URL, **({"identifier": commit} if commit else {})},
        {"@id": PAGES_URL + "#paper", "@type": "ScholarlyArticle", "name": PAPER_TITLE, "headline": PAPER_TITLE, "author": person, "about": about,
         "inLanguage": "en", "associatedMedia": pdfs, "isBasedOn": REPOSITORY,
         "description": "The paper's statements in LexLean's controlled English, each closed by the lexeme of a kernel-checked Lean theorem; the attested PDFs carry the same text."},
        {"@id": PAGES_URL + "register.json", "@type": "Dataset", "name": "The claim register of the Rule 30 effort",
         "description": "Every claim with its status (open, proved, refuted, retired), statement, Lean name, lexeme and dependencies; the plan of the proof, kernel-checked where proved.",
         "creator": person, "about": about, "isBasedOn": REPOSITORY,
         "distribution": [{"@type": "DataDownload", "contentUrl": PAGES_URL + "register.json", "encodingFormat": "application/json"},
                          {"@type": "DataDownload", "contentUrl": PAGES_URL + "frontier.toml", "encodingFormat": "application/toml"}],
         "variableMeasured": [{"@type": "PropertyValue", "name": "status", "description": "open, proved, refuted or retired"}]},
    ]
    for j in journeys:
        mine = [st for st in steps if st["journey"] == j["id"]]
        course = {"@id": f"{PAGES_URL}#{j['id']}", "@type": "LearningResource", "name": f"Journey: {j['id']}", "learningResourceType": "lesson",
                  "audience": {"@type": "Audience", "audienceType": names.get(j["stakeholder"], j["stakeholder"])}, "about": about, "inLanguage": "en",
                  "numberOfItems": len(mine), "hasPart": [step_url(st) for st in mine], "isPartOf": PAGES_URL}
        graph.append(course)
        for st in mine:
            graph.append({"@id": step_url(st), "@type": "LearningResource", "name": st["title"], "learningResourceType": "lesson step",
                          "teaches": st["goal"], "position": st["order"], "isPartOf": course["@id"], "url": step_url(st),
                          "about": about, "inLanguage": "en", "educationalLevel": st["pole"],
                          "audience": {"@type": "Audience", "audienceType": names.get(j["stakeholder"], j["stakeholder"])}})
    return {"@context": "https://schema.org", "@graph": graph}


def in_toto_statement(documents, attestation, manifest, commit):
    """An in-toto Statement v1 whose subjects are the attested PDFs (and the
    sources they were typeset from) with their SHA-256 digests, and whose
    predicate is the paper's LexLean attestation."""
    subjects = []
    for d in documents:
        if d.get("pdfSha256"):
            subjects.append({"name": d["path"] or d["name"], "digest": {"sha256": d["pdfSha256"]}})
        if d.get("texSha256"):
            subjects.append({"name": f"{d['name']}.tex", "digest": {"sha256": d["texSha256"]}})
    predicate = {"attestation": attestation, "pdfManifest": {"generated": manifest.get("generated"), "sourceDigest": manifest.get("sourceDigest")},
                 "commit": commit or None, "verifier": {"lexlean": lexlean_pin(), "lean": lean_toolchain()},
                 "statement": "The documents were typeset from sources whose LexLean modules verified under the named attestation; nothing unproved is called proved."}
    return {"_type": "https://in-toto.io/Statement/v1", "subject": subjects,
            "predicateType": PAGES_URL + "ns#lexlean-attestation/1", "predicate": predicate}


def open_graph(brand, url):
    return [("og:title", brand["name"]), ("og:type", "website"), ("og:url", url), ("og:description", brand["description"]),
            ("og:image", url + "logo.svg"), ("og:image:alt", "Rule 30 from a single black cell; the center column in amber"),
            ("og:site_name", brand["name"]), ("og:locale", "en_US")]


def head_block(jsonld, brand, url):
    """The lines injected before `</head>`: the schema.org JSON-LD script and
    the Open Graph metadata (`</` escaped so the JSON cannot close the script)."""
    payload = json.dumps(jsonld, ensure_ascii=False, sort_keys=True).replace("</", "<\\/")
    metas = "\n".join(f'<meta property="{p}" content="{escape(c, {chr(34): "&quot;"})}">' for p, c in open_graph(brand, url))
    return f'{metas}\n<link rel="sitemap" type="application/xml" href="sitemap.xml">\n<script type="application/ld+json">{payload}</script>\n'


CITATION_TEXT = f"""cff-version: 1.2.0
message: "If you use this work, please cite it as below."
type: software
title: "{PAPER_TITLE}"
authors:
  - family-names: {AUTHOR['family']}
    given-names: {AUTHOR['given']}
repository-code: "{REPOSITORY}"
url: "{PAGES_URL}"
license: MIT
abstract: "Work on Wolfram's Rule 30 Prize, Problem 1: a register of kernel-checked reductions, written in LexLean and checked by the Lean 4 kernel under propext and Quot.sound, with the open obligation stated as open."
keywords:
  - Rule 30
  - cellular automata
  - Lean 4
  - LexLean
  - formal verification
"""


def citation_file():
    """CITATION.cff at the repository root, generated from the model."""
    if not CITATION.exists() or CITATION.read_text() != CITATION_TEXT:
        CITATION.write_text(CITATION_TEXT)
    return CITATION


def artifacts_json():
    return json.dumps(rows(), indent=1, sort_keys=True, ensure_ascii=False) + "\n"
