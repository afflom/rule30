"""The stakeholder view of the proof as LexLean modules.

`rule30-api/src/Presentation.lex.tex` declares the brand, the artifacts the
view workflow publishes, the panels of the site (the Rule 30 picture, the
plain-language explainer, the reduction tree, the register, the open leaves,
the paper's statements, the open obligation, the refuted routes, the
interface sheets, the modules, the quality measures), the explainer's
paragraphs as data, the id of the open obligation, the journey of each
stakeholder through the panels, and the pedagogy: every journey is an ordered
sequence of steps (`Step`), each at one of the Observer's poles (`Pole`: what
the vantage is, how the proof appears from it, what is proved, what is open,
what the reader can verify), each showing one panel toward one goal and
resting on declared evidence (claims of `Register` or artifacts), with the
commands a reader verifies with (`Verification`). The decided theorems: every
panel is governed by a viewpoint of `Architecture`, every journey belongs to
a declared stakeholder, every artifact is produced by a command of `Api`, the
published paths and the explainer's paragraph ids are distinct; every step's
panel is a panel and its journey a journey, the steps of a journey have
consecutive orders from 1 and are linked by `next`, every journey covers the
poles in their canonical order and ends in the verification step, every
evidence id is a claim or an artifact, every paragraph a step cites is
declared, and each journey's panels are exactly its steps' panels (what the
Observer reads as the vantage's sensual qualities). The central navigation is
declared too, as an implementation of the WAI-ARIA Authoring Practices
(`Pattern`, `Navigation`, `NavItem`: the disclosure navigation menu
`nav-primary`, the breadcrumb `nav-breadcrumb`, the stepper `nav-stepper`,
the register search as a combobox), and decided: ids distinct, every item
names a declared pattern and a declared navigation, every journey is
reachable from the primary navigation and listed by the stepper, targets are
journeys, steps or artifacts, the breadcrumb is vantage > pole > step and
resolves for every step, and the verification step of every journey is a
primary target (WCAG 2.2 consistent help). The design system is declared
here too (`designmodel`: `Token`, `ContrastPair`, `TypeStep`, `SpaceStep`,
`Motion`, `Landing`), with the kernel deciding WCAG 2.2 contrast of every
pair in both themes in integer arithmetic over relative luminance; the
experience adds three panels reached from the pedagogy: the standards
(`rd-standards`), the model of the site with the Observer's quadruples
(`sf-model`) and the design system itself (`sf-design`).

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

from . import designmodel, repo
from .semantic import (BOOL, NAT, STR, add, all_members, b, beq, ble, call, definition, eq_string, field_of_each, holds, if_,
                       index_of, list_t, lookup_field, lst, match_list, member_string, n, named, proj, record, s, strings,
                       structure, theorem, var)
from .vizmodel import VIZ_ARTIFACTS, VIZ_PANELS, viz_declarations, with_viz_steps

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
    {"id": "core-vectors", "path": "core-vectors.json", "media": "application/json", "command": "api_sync", "source": "rule30-api/production/core-vectors.json"},
    {"id": "frontier-module", "path": "Frontier.lex.tex", "media": "text/x-lexlean", "command": "frontier_render", "source": "rule30-paper/src/Frontier.lex.tex"},
    {"id": "agents", "path": "AGENTS.md", "media": "text/markdown", "command": "view_render", "source": "AGENTS.md"},
    {"id": "strategy", "path": "STRATEGY.md", "media": "text/markdown", "command": "view_render", "source": "rule30-lexlean/STRATEGY.md"},
    {"id": "readme", "path": "README.md", "media": "text/markdown", "command": "view_render", "source": None},
    {"id": "logo", "path": "logo.svg", "media": "image/svg+xml", "command": "api_sync", "source": "rule30-api/site/logo.svg"},
    # the machine-readable artifacts the standards register (Standards.lex.tex) calls for
    {"id": "standards", "path": "standards.json", "media": "application/json", "command": "view_render", "source": None},
    {"id": "standards-module", "path": "Standards.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Standards.lex.tex"},
    {"id": "openapi", "path": "openapi.json", "media": "application/vnd.oai.openapi+json", "command": "view_render", "source": None},
    {"id": "sitemap", "path": "sitemap.xml", "media": "application/xml", "command": "view_render", "source": None},
    {"id": "robots", "path": "robots.txt", "media": "text/plain", "command": "view_render", "source": None},
    {"id": "provenance", "path": "provenance.jsonld", "media": "application/ld+json", "command": "view_render", "source": None},
    {"id": "jsonld", "path": "schema.json", "media": "application/ld+json", "command": "view_render", "source": None},
    {"id": "attestations", "path": "attestations.intoto.json", "media": "application/vnd.in-toto+json", "command": "view_render", "source": None},
    {"id": "citation", "path": "CITATION.cff", "media": "application/yaml", "command": "view_render", "source": "CITATION.cff"},
    # the Observer module the model panel draws, and the design tokens as the stylesheet the site inlines
    {"id": "observer-module", "path": "Observer.lex.tex", "media": "text/x-lexlean", "command": "api_sync", "source": "rule30-api/src/Observer.lex.tex"},
    {"id": "tokens", "path": "tokens.css", "media": "text/css", "command": "view_render", "source": None},
    {"id": "site", "path": "index.html", "media": "text/html", "command": "view_render", "source": "rule30-api/site/index.html"},
] + VIZ_ARTIFACTS

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
    {"id": "sitemap", "title": "Site map", "viewpoint": "comprehension", "artifact": "site",
     "statement": "Every vantage of this site with every step of its lesson, in order and with its pole: the same list the published sitemap mirrors."},
    {"id": "verify", "title": "Verify it yourself", "viewpoint": "evidence", "artifact": "pdf-manifest",
     "statement": "The commands that reproduce what this page shows, the attested PDFs with their digests, the attestation of the paper and the published artifacts; nothing here asks to be taken on trust."},
    {"id": "standards", "title": "Standards", "viewpoint": "evidence", "artifact": "standards",
     "statement": "Every external standard this site and its API implement, with its authority, version, scope, what realizes it here and the check that confirms it: standards.json, rendered."},
    {"id": "model", "title": "The model of the site", "viewpoint": "stdlib", "artifact": "observer-module",
     "statement": "The application as PrismPM models it: stakeholders, viewpoints, journeys and panels, and the Observer's quadruple of each vantage (what it sees proved, what it shows, what stays withdrawn), drawn from the modules the kernel decides."},
    {"id": "design", "title": "The design system", "viewpoint": "comprehension", "artifact": "tokens",
     "statement": "The colour tokens of both themes with the contrast ratio of every pair the stylesheet uses, the type and spacing scales and the motion durations, as Presentation.lex.tex declares them and the kernel decides them against WCAG 2.2."},
] + VIZ_PANELS

# The Observer's poles as the canonical order of every journey: a lesson
# first says what the vantage is, then shows the proof as it appears from
# there, then the proved claims as kernel-checked evidence, then the open
# obligation as open, and ends with what the reader can verify alone.
POLES = [
    {"id": "sensual-object", "title": "What this vantage is",
     "statement": "The object as it appears from here: the picture and the words, the paper, the tree, the leaves or the modules."},
    {"id": "sensual-quality", "title": "How the proof appears from here",
     "statement": "The panels that show the proof from this vantage; they depend on the vantage, the proof does not."},
    {"id": "real-quality", "title": "What is proved",
     "statement": "The proved claims as kernel-checked evidence, the same from every vantage: each names a Lean theorem checked under propext and Quot.sound."},
    {"id": "withdrawn", "title": "What is open",
     "statement": "The open obligation stated as open, with its exact Lean predicate; no panel renders a proof of it."},
    {"id": "verification", "title": "Verify it yourself",
     "statement": "The commands, attestations and documents with which the reader reproduces what the page shows."},
]

# The commands the verification step offers, each a command of Api.lex.tex.
VERIFICATIONS = [
    {"command": "brief", "invocation": "bin/r30 brief",
     "statement": "One screen: the open claims, the proved reductions, the refuted routes."},
    {"command": "claim", "invocation": "bin/r30 claim <id>",
     "statement": "One claim in full: register entry, Lean type, published statement, dependents."},
    {"command": "frontier_check", "invocation": "bin/r30 frontier check",
     "statement": "The register against the kernel: every proved claim names a theorem checked under propext and Quot.sound and published."},
    {"command": "axioms", "invocation": "bin/r30 axioms <Lean names>",
     "statement": "The axioms a theorem depends on; must print only propext and Quot.sound."},
    {"command": "kappa", "invocation": "bin/r30 kappa <modules>",
     "statement": "The kappa-labels of the research modules: the address of the declarations the kernel replays."},
    {"command": "verify", "invocation": "bin/r30 verify api",
     "statement": "lexlean verify of the API modules: the kernel decides the theorems this page's model states, the pedagogy among them."},
    {"command": "api_check", "invocation": "bin/r30 api check",
     "statement": "Refuses a module, register, schema or feature that drifted from its generator."},
    {"command": "view_render", "invocation": "bin/r30 view render --out view",
     "statement": "This view, rendered from the register into a directory; open view/index.html without a server."},
]

# One stakeholder's lesson, step by step. `panel` is the panel the step shows,
# `pole` its place in the canonical order, `goal` what the reader can do or
# verify after it, `text` and `paragraphs` (ids of `EXPLAINER`) its body,
# `evidence` the claim ids and artifact ids it rests on. `order` and `next`
# are derived from the sequence.
_STEPS = {
    "first-visit": [
        {"id": "fv-picture", "pole": "sensual-object", "panel": "picture", "title": "What Rule 30 is",
         "goal": "Read the picture: how each row is made from the one above it, and which cells are the center column.",
         "paragraphs": ["rule-30", "the-picture"], "evidence": ["picture"]},
        {"id": "fv-problem", "pole": "sensual-object", "panel": "explainer", "title": "The center column and Problem 1",
         "goal": "State Problem 1 in your own words: does the center column ever settle into a block that repeats forever? The claim to be proved is that it never does.",
         "paragraphs": ["center-column", "problem-1"], "evidence": ["explainer", "problem1"]},
        {"id": "fv-kernel", "pole": "sensual-object", "panel": "explainer", "title": "What kernel-checked means",
         "goal": "Know what this site means by kernel-checked before any checked statement is shown.",
         "paragraphs": ["kernel-checked"], "evidence": ["explainer"]},
        {"id": "fv-tree", "pole": "sensual-quality", "panel": "reduction-tree", "title": "The map of what is proved",
         "goal": "Read the reduction tree: Problem 1 at the top, and under it the statements it has been reduced to; a check mark is a proved arrow.",
         "paragraphs": ["what-is-proved", "how-to-read"], "evidence": ["chain", "problem1"]},
        {"id": "fv-reductions", "pole": "sensual-quality", "panel": "explainer", "title": "The main proved arrows, in words",
         "goal": "Say in plain words what the main proved arrows reduce Problem 1 to: collisions, edges, bands, a sparser sequence, and a checked certificate.",
         "paragraphs": ["reduction-collisions", "reduction-edges", "reduction-bands", "reduction-sparse", "reduction-horizon"],
         "evidence": ["recurrent-central-collision", "edge-parity", "interior-aperiodicity", "three-diagonal-band", "left-band",
                      "periodic-finite-kernel", "dilation-reduction", "dyadic-response-reduction", "horizon-certificate"]},
        {"id": "fv-register", "pole": "real-quality", "panel": "register", "title": "The register",
         "goal": "Find a proved statement in the register and see the name of the checked theorem behind it; filter by proved.",
         "paragraphs": ["the-register"], "evidence": ["register-json", "edge-parity", "left-band"]},
        {"id": "fv-open", "pole": "withdrawn", "panel": "obligation", "title": "What remains open",
         "goal": "State the one remaining obligation in plain words and recognize that it is open, not proved.",
         "paragraphs": ["what-is-open"], "evidence": ["aperiodic-compensation"]},
        {"id": "fv-verify", "pole": "verification", "panel": "verify", "title": "What you can check yourself",
         "goal": "Reproduce what this page shows: the briefing, one statement in full, and the paper as it was verified.",
         "paragraphs": ["verify-yourself"], "evidence": ["paper-pdf", "pdf-manifest", "readme"]},
    ],
    "mathematics": [
        {"id": "ma-paper", "pole": "sensual-object", "panel": "paper", "title": "The paper's vocabulary",
         "goal": "Read the paper's statements as mathematics, the defining equations of the Notions section first: every later statement is in their terms.",
         "text": "Observations.lex.tex is written in a controlled English whose every sentence compiles to a Lean statement and is closed by the lexeme of the theorem it states, so the sentence read here and the theorem the kernel checked are the same object. The Notions section publishes the defining equations of the host notions (the center, the carry ledger, the defects, the trinomial and trailing parities) as lemmas; the Lean name and the lexeme are under each statement, and the attested PDFs carry the same text.",
         "evidence": ["statements", "paper-pdf", "observations-pdf", "core-pdf"]},
        {"id": "ma-tree", "pole": "sensual-quality", "panel": "reduction-tree", "title": "The register as a tree",
         "goal": "Read the register as a tree of reductions from problem1: a proved arrow is a theorem toward Problem 1, an open leaf a sufficient condition, a cross a refuted route; the open obligation is the node every exact decomposition ends at.",
         "text": "problem1 is Ruliology.CellularAutomata.Rule30Prize.Problem1 as the prize kit states it. A proved child of a node is a kernel-checked implication or equivalence toward the node; an open leaf is a statement that would close Problem 1 through the proved arrows above it; aperiodic-compensation is the open statement the exact decompositions of the next steps end at, read in full once they have been read.",
         "evidence": ["chain", "problem1"]},
        {"id": "ma-edges", "pole": "real-quality", "panel": "register", "title": "The edge chain",
         "goal": "Follow the exact decomposition of the center: ledger-diagonal, edge-interior-split, edge-diagonal-formula, edge-parity (center t = not (timeParity t XOR interiorDiagonal t)), hence Problem 1 iff InteriorAperiodic.",
         "text": "The center is the complement of the diagonal of the carry ledger (centerPeriodic_iff_ledgerPeriodic); every elementary rule is a linear part plus a carry (rule_eq_linear_xor_carry), and the carry is the intersection of a row with its own translate. The two edge carries of every row, propagated through the trinomial triangle, contribute exactly the time parity (edgeDiagonal_eq_timeParity), so a period of the center is a period of the interior diagonal up to a factor 2 (problem1_iff_interiorAperiodic).",
         "evidence": ["ledger-diagonal", "all-rules-facet", "characteristic-one-facet", "edge-interior-split", "edge-diagonal-formula",
                      "interior-diagonal-formula", "edge-parity", "interior-aperiodicity"]},
        {"id": "ma-bands", "pole": "real-quality", "panel": "register", "title": "Stripping the bands",
         "goal": "Strip the regular bands exactly: center t = trailingParity (t-2) XOR interiorThreeDiagonal t (three-diagonal-band), center t = rulerBackground t XOR interiorEightDiagonal t (left-band), and the renormalization of the obligation on every dyadic class.",
         "text": "The three inner diagonals of the regular side inject the period-doubling sequence trailingParity, which has no eventual period (trailingParity_not_periodic); the first diagonals of the chaotic side inject two further ruler terms. Under a center period the deep interior has no eventual period at all (not_threePeriodic_of_centerPeriodic) and the equation against the ruler reproduces itself with the same period on every class 2^k u + 1 (threeClass_of_centerPeriodic). Problem 1 iff ThreeAperiodic iff EightAperiodic.",
         "evidence": ["three-diagonal-band", "dyadic-renormalization", "left-band"]},
        {"id": "ma-collisions", "pole": "real-quality", "panel": "register", "title": "Collisions, coupling and certificates",
         "goal": "Read the nonlinear facts: Problem 1 iff no recurrent central collision, the coupling law of the center defect, left-defect sourcing from column one, and the kernel-checked horizon certificate for T <= 512 and P <= 128.",
         "text": "problem1_iff_noRecurrentCentralCollision is the band form, choice-free. center_periodic_of_coupling states a center period as the coupling leftDefect(t,1) XOR (not center t AND rightDefect(t,1)) at every later time. left_defect_sourced says where a left defect comes from. horizon_thirty_two is a finite certificate the kernel evaluated directly on the rows; the uniform horizon H(T, P) is the open claim horizon-criterion.",
         "evidence": ["recurrent-central-collision", "coupling-law", "left-defect-sourcing", "horizon-certificate"]},
        {"id": "ma-dyadic", "pole": "real-quality", "panel": "register", "title": "The dyadic side",
         "goal": "Read the 2-kernel reductions: a periodic center has a finite 2-kernel, which forces dyadic self-similarity, the dilation and response reductions, the fixed sequence dyadicRow, and the freezing law of the linear transport (kernel-law).",
         "text": "centerKernelFinite_of_centerPeriodic: under CenterPeriodic T P every subsequence t -> center(2^k t + r) is eventually periodic with a common period. From it: problem1_of_no_dyadic_self_similarity, problem1_of_dyadic_column_aperiodic, problem1_of_dilation_aperiodic_in_paper (any base), kappaCollapse_iff, problem1_of_dyadic_response_aperiodic; the trinomial kernel is dyadically stable (dyadicColumnAperiodic_iff_stable), each row's contribution to the dyadic column is scale-free (center_twopow_succ_eq), and rowTerm_kernel_law makes every 2-kernel sequence explicit up to the rows at or above the scale.",
         "evidence": ["periodic-finite-kernel", "kernel-self-similarity", "dilation-reduction", "base-generic-reduction", "interior-kernel-reduction",
                      "stable-kernel", "kappa-collapse", "dyadic-response-reduction", "scale-free-rows", "kernel-law"]},
        {"id": "ma-obligation", "pole": "withdrawn", "panel": "obligation", "title": "The open obligation, exactly",
         "goal": "State the obligation exactly, as open: EightAperiodic (Rule30UOR.LeftBand), its exact forms, its chain to Problem 1, what rests on it, and the open leaves that would also close Problem 1.",
         "text": "Every proved reduction ends here. The bulk carries, with both edge bands stripped, are never the ruler background plus a periodic sequence. No closing argument is known; the register records what a periodic interior would have to satisfy (renormalization on every dyadic class, black-center absorption, the block tables of the freezing law) and calls none of it a proof. The other open leaves (horizon-criterion, center-infinite-kernel, no-dyadic-self-similarity, dyadic-column-aperiodic, some-base-dilation-aperiodic, dyadic-response-aperiodic) are each sufficient.",
         "evidence": ["aperiodic-compensation", "horizon-criterion", "center-infinite-kernel", "no-dyadic-self-similarity", "dyadic-column-aperiodic",
                      "some-base-dilation-aperiodic", "dyadic-response-aperiodic"]},
        {"id": "ma-refuted", "pole": "withdrawn", "panel": "refutations", "title": "Refuted routes",
         "goal": "Know the refuted routes toward the obligation and the Lean refutation or experiment behind each, so as not to walk them again.",
         "text": "A refuted claim stays in the register with its refutation: a Lean theorem that shows the route arithmetic or vacuous (routes A, B and C in Rule30UOR.Routes, the engine hypothesis bundles, the observer q-rank), or a finite experiment on the seed (q-adic descent, front slack, the evaluation point, the first-failure 2-adic law).",
         "evidence": ["q-adic-descent", "front-slack-descent", "evaluation-point", "gate-phase-opposition", "band-engines", "saturation-reexcitation",
                      "first-failure-2adic", "route-a-band-discharge", "route-c-rank-drop", "route-b-reset-mismatch"]},
        {"id": "ma-verify", "pole": "verification", "panel": "verify", "title": "Verify the paper",
         "goal": "Verify: the attestation identifiers of the paper, the PDF digests against pdf-manifest.json (also an in-toto statement), the provenance of every proved claim (PROV-O: theorem, module, attestation), bin/r30 claim <id> for any claim, bin/r30 axioms <Lean name> for its axioms; cite the paper from CITATION.cff.",
         "evidence": ["pdf-manifest", "paper-pdf", "statements", "register-json", "attestations", "provenance", "citation"]},
    ],
    "prize-review": [
        {"id": "pr-tree", "pole": "sensual-object", "panel": "reduction-tree", "title": "The proof as a tree",
         "goal": "See the whole effort as one tree from problem1: every arrow a theorem, every leaf an open sufficient condition, every cross a refuted route.",
         "evidence": ["chain", "problem1"]},
        {"id": "pr-leaves", "pole": "sensual-quality", "panel": "open-leaves", "title": "The open leaves",
         "goal": "Read the open leaves: each is a statement that would close Problem 1 through the proved arrows above it, and nothing else is claimed.",
         "evidence": ["register-json", "horizon-criterion", "center-infinite-kernel", "no-dyadic-self-similarity", "dyadic-column-aperiodic",
                      "some-base-dilation-aperiodic", "dyadic-response-aperiodic"]},
        {"id": "pr-register", "pole": "real-quality", "panel": "register", "title": "Proved, against the kernel",
         "goal": "Check that every proved claim names a Lean theorem, kernel-checked under propext and Quot.sound and published as a lexeme; filter the register by proved.",
         "evidence": ["register-json", "register-module", "frontier-module"]},
        {"id": "pr-obligation", "pole": "withdrawn", "panel": "obligation", "title": "The remaining obligation",
         "goal": "Read the one open obligation every proved reduction ends at, EightAperiodic, stated as open with its chain to Problem 1.",
         "evidence": ["aperiodic-compensation"]},
        {"id": "pr-verify", "pole": "verification", "panel": "verify", "title": "Reproduce the evidence",
         "goal": "Reproduce the register's evidence: bin/r30 frontier check reads every proved claim against the kernel, bin/r30 axioms <Lean name> prints its axioms, the PDFs carry the attested paper, and provenance.jsonld records for every proved claim the theorem, the module and the attestation it rests on.",
         "evidence": ["frontier", "pdf-manifest", "paper-pdf", "provenance", "attestations"]},
    ],
    "research-session": [
        {"id": "rs-leaves", "pole": "sensual-object", "panel": "open-leaves", "title": "Where to work",
         "goal": "Start where the register allows work: the open leaves, the only places a session works (bin/r30 brief lists them).",
         "evidence": ["register-json", "dyadic-response-aperiodic", "dyadic-column-aperiodic", "horizon-criterion"]},
        {"id": "rs-sheet", "pole": "sensual-quality", "panel": "interface-sheets", "title": "The sheet of a leaf",
         "goal": "Read a leaf's interface sheet: its chain to problem1, its notions, the exact facts about them and the handles to continue (bin/r30 interface <id>).",
         "evidence": ["interfaces", "dyadic-response-aperiodic"]},
        {"id": "rs-quality", "pole": "sensual-quality", "panel": "quality", "title": "The gate and its budget",
         "goal": "Know the cost model: one module checks in seconds, the gate runs once per batch, CI only renders; each measure names its threshold and the command that reports it.",
         "evidence": ["architecture-module", "agents"]},
        {"id": "rs-reductions", "pole": "real-quality", "panel": "register", "title": "Proved reductions: use them",
         "goal": "Use the proved reductions as equivalent forms of the goal and do not re-derive them; the register is the plan and the kernel is the judge.",
         "evidence": ["register-json", "interior-aperiodicity", "three-diagonal-band", "left-band", "kernel-law"]},
        {"id": "rs-obligation", "pole": "withdrawn", "panel": "obligation", "title": "The obligation and its exact forms",
         "goal": "Read the obligation in its exact forms (center t = rulerBackground t XOR interiorEightDiagonal t; the dyadic form) and what is known about it.",
         "evidence": ["aperiodic-compensation"]},
        {"id": "rs-refuted", "pole": "withdrawn", "panel": "refutations", "title": "Routes not to walk again",
         "goal": "Know the refuted routes and the refutation of each, so the session does not walk them again.",
         "evidence": ["route-a-band-discharge", "route-b-reset-mismatch", "route-c-rank-drop", "band-engines", "q-adic-descent"]},
        {"id": "rs-verify", "pole": "verification", "panel": "verify", "title": "Run the loop",
         "goal": "Run the loop: bin/r30 brief, bin/r30 claim <id>, check or verify one module, bin/r30 kappa for the replay labels, and commit through the gate once per batch.",
         "evidence": ["agents", "strategy"]},
    ],
    "reading": [
        {"id": "rd-tree", "pole": "sensual-object", "panel": "reduction-tree", "title": "The map",
         "goal": "Read the register as a tree: what rests on what, which arrows are theorems, which leaves are open.",
         "evidence": ["chain", "problem1"]},
        {"id": "rd-map", "pole": "sensual-object", "panel": "sitemap", "title": "Every vantage and its steps",
         "goal": "Find any lesson of this site: the six vantages, every step of each with its pole, and the step you are on; the primary navigation reaches the same places from every page.",
         "evidence": ["site", "presentation-module"]},
        {"id": "rd-sheet", "pole": "sensual-quality", "panel": "interface-sheets", "title": "A claim, labeled",
         "goal": "Read a claim's labeled sheet, written to be reused: chain, notions, exact facts, handles.",
         "evidence": ["interfaces"]},
        {"id": "rd-register", "pole": "real-quality", "panel": "register", "title": "Every claim with its evidence",
         "goal": "Find any claim, its status, its Lean name and lexeme, what it rests on and what rests on it; search by notion.",
         "evidence": ["register-json", "frontier"]},
        {"id": "rd-obligation", "pole": "withdrawn", "panel": "obligation", "title": "What is open",
         "goal": "Read the open obligation as open, with its Lean predicate, and the open leaves that would also close Problem 1.",
         "evidence": ["aperiodic-compensation"]},
        {"id": "rd-standards", "pole": "verification", "panel": "standards", "title": "The standards it implements",
         "goal": "See which external standard governs each part of what you have read (accessibility, navigation, markup, graphics, metadata, provenance, citation), what realizes it here and the check that confirms it; filter by kind and follow any authority.",
         "evidence": ["standards", "standards-module", "site"]},
        {"id": "rd-verify", "pole": "verification", "panel": "verify", "title": "Reproduce the view",
         "goal": "Reproduce the view: bin/r30 view render writes these artifacts, the PDFs and their digests are the attested paper, the modules are verified with lexlean; the standards the view implements, with what realizes each and how it is checked, are standards.json, and the site is described for machines (schema.org, the sitemap) and for citation (CITATION.cff).",
         "evidence": ["readme", "pdf-manifest", "site", "standards", "jsonld", "sitemap", "citation"]},
    ],
    "stdlib-feedback": [
        {"id": "sf-modules", "pole": "sensual-object", "panel": "modules", "title": "The application as modules",
         "goal": "Read the application as LexLean semantic modules on prism-stdlib: the command surface, the register, the architecture, the presentation, the application, the Observer and the standards register, each data plus theorems the kernel decides.",
         "evidence": ["api-module", "register-module", "architecture-module", "presentation-module", "application-module", "standards-module"]},
        {"id": "sf-model", "pole": "sensual-object", "panel": "model", "title": "One model, many parts",
         "goal": "Read the whole repository as one PrismPM model: each stakeholder holds concerns, each viewpoint frames one, each journey is a vantage through panels, and the Observer records for each vantage what it sees proved, what it shows and what stays withdrawn; select a vantage to trace its quadruple.",
         "evidence": ["observer-module", "presentation-module", "architecture-module", "register-module"]},
        {"id": "sf-quality", "pole": "sensual-quality", "panel": "quality", "title": "What optimal means here",
         "goal": "Read the quality model on Foundation.Qual: the measures, their thresholds and the command that reports each, the pedagogy among them.",
         "evidence": ["architecture-module"]},
        {"id": "sf-design", "pole": "sensual-quality", "panel": "design", "title": "The design system, decided",
         "goal": "Read the design system as data: every colour token in both themes, every text and control pair with its contrast ratio, which the kernel decides in integer arithmetic over relative luminance against WCAG 2.2, and the type, spacing and motion scales the stylesheet is generated from.",
         "evidence": ["tokens", "presentation-module"]},
        {"id": "sf-register", "pole": "real-quality", "panel": "register", "title": "The register, decided",
         "goal": "Read the register as Register.lex.tex restates it (every depends target a claim, every proved claim a Lean theorem, decided by the kernel): the same rows as register.json under its schema.",
         "evidence": ["register-json", "register-module", "frontier-module"]},
        {"id": "sf-obligation", "pole": "withdrawn", "panel": "obligation", "title": "The obligation as data",
         "goal": "Read the obligation as Presentation names it and Application decides it to be an open claim (obligationIsOpen): the Observer's withdrawn core.",
         "evidence": ["aperiodic-compensation", "presentation-module", "application-module"]},
        {"id": "sf-verify", "pole": "verification", "panel": "verify", "title": "Drive the surface as a machine",
         "goal": "Drive the same surface as a machine: every command is an MCP tool and an operation of openapi.json, --json reports validate against the published schemas, bin/r30 kappa prints the kappa-labels of the modules, bin/r30 api check refuses drift; standards.json names every standard the surface implements and the check behind each.",
         "evidence": ["api-module", "readme", "openapi", "standards", "standards-module"]},
    ],
}

_JOURNEYS = [
    {"id": "prize-review", "stakeholder": "wolfram"},
    {"id": "research-session", "stakeholder": "researcher"},
    {"id": "reading", "stakeholder": "community"},
    {"id": "stdlib-feedback", "stakeholder": "uor-foundation"},
    {"id": "mathematics", "stakeholder": "mathematician"},
    {"id": "first-visit", "stakeholder": "layperson"},
]


_STEPS = with_viz_steps(_STEPS)


def _steps():
    rows = []
    for j in _JOURNEYS:
        seq = _STEPS[j["id"]]
        for k, st in enumerate(seq):
            rows.append({"id": st["id"], "journey": j["id"], "order": k + 1, "pole": st["pole"], "panel": st["panel"],
                         "title": st["title"], "goal": st["goal"], "text": st.get("text", ""),
                         "paragraphs": list(st.get("paragraphs", [])), "evidence": list(st["evidence"]),
                         "next": seq[k + 1]["id"] if k + 1 < len(seq) else ""})
    return rows


STEPS = _steps()


def _distinct_in_order(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


# A journey's panels are its steps' panels in order of first use: what the
# Observer reads as the vantage's sensual qualities.
JOURNEYS = [{"id": j["id"], "stakeholder": j["stakeholder"],
             "panels": _distinct_in_order(st["panel"] for st in STEPS if st["journey"] == j["id"])} for j in _JOURNEYS]

# The central navigation as an implementation of the WAI-ARIA Authoring
# Practices (APG): each navigation realizes one declared pattern, each item
# names the pattern it is rendered with and targets a journey, a step, an
# artifact or an external authority (the standards the site implements).
# `nav-primary` is the site-wide disclosure navigation menu in the banner
# (Vantages, Register, Modules, Verify, Standards; the verify step of every
# vantage is reachable from it, WCAG 2.2 consistent help); `nav-breadcrumb`
# is the breadcrumb of the current step (vantage > pole > step; its items are
# a template over the current step, so their kind is their meaning and their
# target empty); `nav-stepper` is the disclosure sequence of a vantage's
# steps. Decided: ids distinct, every journey reachable from the primary
# navigation and listed by the stepper, every item names a declared pattern,
# targets resolve, the breadcrumb trail is vantage > pole > step and resolves
# for every step, the verification step of every journey is a primary target.
NAV_PATTERNS = [
    {"id": "disclosure-navigation-menu", "authority": "https://www.w3.org/WAI/ARIA/apg/patterns/disclosure/examples/disclosure-navigation/",
     "statement": "A navigation landmark of top-level disclosure buttons (aria-expanded, aria-controls), each revealing a list of links; Escape closes the open list and returns focus to its button; the arrow keys, Home and End move focus among the buttons and the links; one list is open at a time."},
    {"id": "breadcrumb", "authority": "https://www.w3.org/WAI/ARIA/apg/patterns/breadcrumb/",
     "statement": "A navigation landmark labeled Breadcrumb holding an ordered list of links from the vantage through its pole to the current step, which carries aria-current=page."},
    {"id": "stepper", "authority": "https://www.w3.org/WAI/ARIA/apg/patterns/disclosure/",
     "statement": "A disclosure sequence: a navigation landmark holding the ordered list of the vantage's steps with the current step aria-current=step, the previous and the next step as links, and a disclosure button that reveals the title of every step."},
    {"id": "combobox", "authority": "https://www.w3.org/WAI/ARIA/apg/patterns/combobox/",
     "statement": "An editable combobox with a listbox popup (aria-expanded, aria-controls, aria-activedescendant, aria-autocomplete=list): typing filters the register, the arrow keys move the active option, Enter opens it, Escape closes the list, and a live region reports the number of matches."},
]

NAVIGATIONS = [
    {"id": "nav-primary", "label": "Site", "pattern": "disclosure-navigation-menu",
     "statement": "The site-wide navigation in the banner of every page: Vantages, Register, Modules, Verify, Standards."},
    {"id": "nav-breadcrumb", "label": "Breadcrumb", "pattern": "breadcrumb",
     "statement": "Where the reader is: the vantage, its pole, the current step."},
    {"id": "nav-stepper", "label": "Steps of this vantage", "pattern": "stepper",
     "statement": "The steps of the current vantage in order, the current one marked, with the previous and the next."},
]

# How the primary navigation names each vantage (the README's table).
JOURNEY_LABELS = {
    "prize-review": "The prize committee",
    "research-session": "The researcher (developer view)",
    "reading": "The community",
    "stdlib-feedback": "The UOR Foundation (machine view)",
    "mathematics": "The mathematician",
    "first-visit": "First visit: no background needed",
}

# The external authorities the Standards group links to; S1's standards
# panel declares what each governs, the navigation only reaches them.
NAV_AUTHORITIES = [
    {"id": "nav-standard-apg", "label": "WAI-ARIA Authoring Practices (APG)", "target": "https://www.w3.org/WAI/ARIA/apg/"},
    {"id": "nav-standard-aria", "label": "WAI-ARIA 1.2", "target": "https://www.w3.org/TR/wai-aria-1.2/"},
    {"id": "nav-standard-wcag", "label": "WCAG 2.2", "target": "https://www.w3.org/TR/WCAG22/"},
    {"id": "nav-standard-html", "label": "HTML Living Standard", "target": "https://html.spec.whatwg.org/multipage/"},
    {"id": "nav-standard-42010", "label": "ISO/IEC/IEEE 42010 (architecture description)", "target": "https://www.iso.org/standard/74393.html"},
    {"id": "nav-standard-25010", "label": "ISO/IEC 25010 (product quality)", "target": "https://www.iso.org/standard/78176.html"},
]


def _nav_items():
    rows = []
    disclosure = "disclosure-navigation-menu"

    def item(id_, navigation, parent, label, kind, target, order, pattern=disclosure):
        rows.append({"id": id_, "navigation": navigation, "parent": parent, "label": label, "pattern": pattern,
                     "kind": kind, "target": target, "order": order})

    def group(id_, label, order, children):
        item(id_, "nav-primary", "", label, "group", "", order)
        for k, (cid, clabel, kind, target, *pattern) in enumerate(children):
            item(cid, "nav-primary", id_, clabel, kind, target, k + 1, *pattern)

    last = {j["id"]: [st for st in STEPS if st["journey"] == j["id"]][-1] for j in JOURNEYS}
    modules = [a for a in ARTIFACTS if a["media"] == "text/x-lexlean"]
    group("nav-vantages", "Vantages", 1,
          [(f"nav-vantage-{j['id']}", JOURNEY_LABELS[j["id"]], "journey", j["id"]) for j in JOURNEYS] +
          [("nav-sitemap", "Site map: every vantage and its steps", "step", "rd-map")])
    group("nav-register", "Register", 2,
          [("nav-search", "Search the register", "step", "rd-register", "combobox"),
           ("nav-register-claims", "Every claim with its evidence", "step", "rd-register"),
           ("nav-register-tree", "Reduction tree", "step", "rd-tree"),
           ("nav-register-leaves", "Open leaves", "step", "pr-leaves"),
           ("nav-register-obligation", "Open obligation", "step", "rd-obligation"),
           ("nav-register-json", "register.json", "artifact", "register-json")])
    group("nav-modules", "Modules", 3,
          [("nav-modules-step", "The LexLean modules, read", "step", "sf-modules"),
           ("nav-model", "The model of the site (PrismPM, Observer)", "step", "sf-model"),
           ("nav-design", "The design system, decided", "step", "sf-design")] +
          [(f"nav-module-{a['id']}", a["path"], "artifact", a["id"]) for a in modules])
    group("nav-verify", "Verify", 4,
          [(f"nav-verify-{j['id']}", "Verify: " + JOURNEY_LABELS[j["id"]], "step", last[j["id"]]["id"]) for j in JOURNEYS])
    group("nav-standards", "Standards", 5,
          [("nav-standards-step", "Every standard this site implements", "step", "rd-standards"),
           ("nav-standards-json", "standards.json", "artifact", "standards")] +
          [(a["id"], a["label"], "authority", a["target"]) for a in NAV_AUTHORITIES])
    for k, (cid, label, kind) in enumerate((("nav-crumb-vantage", "Vantage", "journey"), ("nav-crumb-pole", "Pole", "pole"),
                                            ("nav-crumb-step", "Step", "step"))):
        item(cid, "nav-breadcrumb", "", label, kind, "", k + 1, "breadcrumb")
    for k, j in enumerate(JOURNEYS):
        item(f"nav-steps-{j['id']}", "nav-stepper", "", "Steps: " + JOURNEY_LABELS[j["id"]], "journey", j["id"], k + 1, "stepper")
    return rows


NAV_ITEMS = _nav_items()


def nav_problems(steps=None, journeys=None, artifacts=None, items=None, navigations=None, patterns=None):
    """What `Presentation.lex.tex` decides about the navigation, checked in
    Python first so a failure names the item: ids distinct, every item in a
    declared navigation with a declared pattern and a parent that is an item,
    targets that resolve (journeys, steps, artifacts; an authority is a URL),
    every journey reachable from the primary navigation and listed by the
    stepper, the breadcrumb trail vantage > pole > step, the verification step
    of every journey a primary target, the search item on a register step,
    and the orders under each parent consecutive from 1."""
    steps = STEPS if steps is None else steps
    journeys = JOURNEYS if journeys is None else journeys
    items = NAV_ITEMS if items is None else items
    navigations = NAVIGATIONS if navigations is None else navigations
    pattern_ids = {x["id"] for x in (NAV_PATTERNS if patterns is None else patterns)}
    artifact_ids = {a["id"] for a in (ARTIFACTS if artifacts is None else artifacts)}
    journey_ids = [j["id"] for j in journeys]
    step_ids = {st["id"] for st in steps}
    nav_ids = [x["id"] for x in navigations]
    item_ids = [x["id"] for x in items]
    out = []
    if len(set(nav_ids + item_ids)) != len(nav_ids + item_ids):
        out.append("navigation: ids are not distinct")
    for x in navigations:
        if x["pattern"] not in pattern_ids:
            out.append(f"navigation {x['id']}: pattern {x['pattern']} is not declared")
    for x in items:
        if x["navigation"] not in nav_ids:
            out.append(f"item {x['id']}: navigation {x['navigation']} is not declared")
        if x["pattern"] not in pattern_ids:
            out.append(f"item {x['id']}: pattern {x['pattern']} is not declared")
        if x["parent"] and x["parent"] not in item_ids:
            out.append(f"item {x['id']}: parent {x['parent']} is not an item")
        if x["navigation"] == "nav-breadcrumb":
            continue
        if x["kind"] == "journey" and x["target"] not in journey_ids:
            out.append(f"item {x['id']}: journey {x['target']} is not a journey")
        if x["kind"] == "step" and x["target"] not in step_ids:
            out.append(f"item {x['id']}: step {x['target']} is not a step")
        if x["kind"] == "artifact" and x["target"] not in artifact_ids:
            out.append(f"item {x['id']}: artifact {x['target']} is not an artifact")
        if x["kind"] == "authority" and not x["target"].startswith("https://"):
            out.append(f"item {x['id']}: authority {x['target']} is not a URL")
    primary = [x for x in items if x["navigation"] == "nav-primary"]
    primary_targets = lambda kind: {x["target"] for x in primary if x["kind"] == kind}
    for j in journey_ids:
        if j not in primary_targets("journey"):
            out.append(f"journey {j}: not reachable from nav-primary")
        if j not in {x["target"] for x in items if x["navigation"] == "nav-stepper" and x["kind"] == "journey"}:
            out.append(f"journey {j}: not listed by nav-stepper")
        mine = [st for st in steps if st["journey"] == j]
        if mine and mine[-1]["id"] not in primary_targets("step"):
            out.append(f"journey {j}: its verification step is not a target of nav-primary")
    crumbs = sorted((x for x in items if x["navigation"] == "nav-breadcrumb"), key=lambda x: x["order"])
    if [x["kind"] for x in crumbs] != ["journey", "pole", "step"]:
        out.append("nav-breadcrumb: the trail is not vantage > pole > step")
    search = next((x for x in items if x["id"] == "nav-search"), None)
    panel = next((st["panel"] for st in steps if search and st["id"] == search["target"]), None)
    if panel != "register":
        out.append("nav-search: its target does not show the register")
    for nav in nav_ids:
        parents = {x["parent"] for x in items if x["navigation"] == nav}
        for parent in parents:
            orders = [x["order"] for x in items if x["navigation"] == nav and x["parent"] == parent]
            if orders != list(range(1, len(orders) + 1)):
                out.append(f"{nav}: the orders under {parent or 'the root'} are not 1..{len(orders)}")
    return out


# The plain-language panel, as data: short paragraphs a reader without Lean
# or LexLean can follow. `view render` writes them as explainer.json and the
# site renders them; the tests refuse formal vocabulary in them.
EXPLAINER = [
    {"id": "rule-30", "title": "What Rule 30 is",
     "text": "Rule 30 is a one-line machine. Start with a row of cells, all white except one black cell in the middle. To make the next row, look at each cell together with its left and right neighbours. If the left neighbour is black, the cell below turns black only when the cell and its right neighbour are both white; if the left neighbour is white, the cell below turns black when the cell or its right neighbour is black. Repeat, row after row, forever. The picture shows the first rows: a regular pattern grows on the left and a tangled one on the right."},
    {"id": "the-picture", "title": "Reading the picture",
     "text": "The picture shows the first 48 rows, rows 0 to 47, from the single black cell at the top; each row is one step of the machine, and the triangle widens by one cell on each side per row. The amber cells are the center column, read from the top down. If the center column eventually repeated, then from some row on the amber cells would show the same block of blacks and whites again and again, like a stripe. Nothing of the kind is visible here, but no number of rows could settle the question, because it asks about every row that will ever come."},
    {"id": "center-column", "title": "The center column",
     "text": "Read the cells straight down from the first black cell: black, black, white, black, black, black, white, white, black, black, white, white, white, black, white, black, and so on. This list of blacks and whites is the center column. It looks random. Nobody has found a pattern in it, and nobody has proved that there is none."},
    {"id": "problem-1", "title": "What Problem 1 asks",
     "text": "Stephen Wolfram's Rule 30 Prize asks three questions about the center column. Problem 1 asks whether it ever settles into a repeating pattern: whether there is a point after which the same block of blacks and whites repeats forever. The statement to be proved is that it never does."},
    {"id": "what-is-proved", "title": "What is proved here",
     "text": "This work has not solved Problem 1. What it has done is prove, in a form a computer checks, that Problem 1 is the same question as several other, more concrete questions. Each proved arrow in the reduction tree says: if you could prove the statement at the arrow's end, Problem 1 would follow. The next step says what the main ones are."},
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
    {"id": "the-register", "title": "The register",
     "text": "The register is the list of every statement this work keeps track of, each with a status: proved, open, refuted or retired. A proved statement names the theorem the kernel checked, so the status is not a promise but a pointer to a checked proof; an open statement names nothing of the kind, and the site never shows it as proved. Select a statement to see what it rests on and what rests on it."},
    {"id": "what-is-open", "title": "What remains open",
     "text": "The register names one remaining obligation, aperiodic-compensation. In plain words: the bulk of the pattern, with the few regular diagonals next to both edges stripped away, never reproduces the ruler rhythm plus a repeating pattern. It is open: nobody has proved it, and this site does not claim it. Proving it would close Problem 1, and so would proving any other open leaf of the tree, such as the sparser sequences of the previous step. Several tempting routes were tried and shown not to work; those are the refuted routes, kept so that nobody walks them again."},
    {"id": "kernel-checked", "title": "What kernel-checked means",
     "text": "Every proved statement here was written in a proof language called Lean and checked by its kernel, a small program that accepts a proof only when every step follows from the rules. A reader can misread a long argument; the kernel does not. Kernel-checked means the proof passed that check, using only two standard logical principles and no extra assumptions. The statements are also written in a controlled English that is itself translated to Lean and checked, so the sentence you read and the theorem the kernel checked are the same thing."},
    {"id": "how-to-read", "title": "How to read the tree",
     "text": "The reduction tree is the map: Problem 1 at the top and, below it, the statements it has been reduced to. A check mark is a proved arrow, a question mark an open statement, a cross a route that was tried and refuted. The small grey name beside a proved statement is the name of its checked theorem. Select a statement to see it in full. The other vantages on this site, for the mathematician, the researcher, the prize committee and the machine, read the same register from their own side."},
    {"id": "verify-yourself", "title": "What you can check yourself",
     "text": "Nothing here asks to be taken on trust. The commands below reproduce what this page shows from the repository: the briefing prints the current state in one screen, the claim command prints one statement with its checked theorem, and the register check reads every proved statement against the kernel. The PDFs carry the paper as it was verified, with digests so that a copy can be compared with the published one."},
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


def step_problems(claim_ids, steps=None, journeys=None, panels=None, poles=None, paragraphs=None, artifacts=None):
    """What `Presentation.lex.tex` decides about the pedagogy, checked in
    Python first so a failure names the step before `lexlean verify` reports
    a false `decide` and before `view render` publishes it: every step's
    panel is a panel and its journey a journey, the steps of a journey have
    consecutive orders from 1 linked by `next`, every journey covers the poles
    in their order and ends in verification, every evidence id is a claim or
    an artifact, every paragraph is declared, and a journey's panels are its
    steps' panels. Returns the problems, empty when none."""
    steps = STEPS if steps is None else steps
    journeys = JOURNEYS if journeys is None else journeys
    panel_ids = {x["id"] for x in (PANELS if panels is None else panels)}
    pole_ids = [x["id"] for x in (POLES if poles is None else poles)]
    paragraph_ids = {x["id"] for x in (EXPLAINER if paragraphs is None else paragraphs)}
    evidence_ids = set(claim_ids) | {a["id"] for a in (ARTIFACTS if artifacts is None else artifacts)}
    journey_ids = {j["id"] for j in journeys}
    out = []
    seen = set()
    for st in steps:
        if st["id"] in seen:
            out.append(f"step {st['id']}: duplicate id")
        seen.add(st["id"])
        if st["panel"] not in panel_ids:
            out.append(f"step {st['id']}: panel {st['panel']} is not a panel")
        if st["journey"] not in journey_ids:
            out.append(f"step {st['id']}: journey {st['journey']} is not a journey")
        if st["pole"] not in pole_ids:
            out.append(f"step {st['id']}: pole {st['pole']} is not a pole")
        for e in st["evidence"]:
            if e not in evidence_ids:
                out.append(f"step {st['id']}: evidence {e} is neither a claim nor an artifact")
        for q in st["paragraphs"]:
            if q not in paragraph_ids:
                out.append(f"step {st['id']}: paragraph {q} is not declared")
    for j in journeys:
        mine = [st for st in steps if st["journey"] == j["id"]]
        if not mine:
            out.append(f"journey {j['id']}: no steps")
            continue
        if [st["order"] for st in mine] != list(range(1, len(mine) + 1)):
            out.append(f"journey {j['id']}: orders are not 1..{len(mine)}")
        if [st["next"] for st in mine] != [st["id"] for st in mine[1:]] + [""]:
            out.append(f"journey {j['id']}: steps are not linked by next")
        indices = [pole_ids.index(st["pole"]) if st["pole"] in pole_ids else -1 for st in mine]
        if indices != sorted(indices):
            out.append(f"journey {j['id']}: poles are out of order")
        if set(pole_ids) - {st["pole"] for st in mine}:
            out.append(f"journey {j['id']}: poles not covered: " + ", ".join(sorted(set(pole_ids) - {st["pole"] for st in mine})))
        if mine[-1]["pole"] != "verification":
            out.append(f"journey {j['id']}: the last step is not the verification step")
        if set(j["panels"]) != {st["panel"] for st in mine}:
            out.append(f"journey {j['id']}: its panels are not its steps' panels")
    return out


def _distinct(name):
    return definition(name, BOOL,
                      match_list(var("xs"), b(True), "head", "tail",
                                 if_(call("memberString", var("head"), var("tail")), b(False), call(name, var("tail")))),
                      parameters=[("xs", list_t(STR))], recursive="xs")


def _each_journey(name, condition, extra=()):
    """`name js ss ...`: `condition` (over `head`, the journey, with `st`
    standing for the journey's steps) holds of every journey; the steps and
    the extra parameters are fixed through the recursion."""
    params = [("js", list_t(named("Journey"))), ("ss", list_t(named("Step")))] + list(extra)
    return definition(name, BOOL,
                      match_list(var("js"), b(True), "head", "tail",
                                 if_(condition, call(name, var("tail"), *[var(q) for q, _ in params[1:]]), b(False))),
                      parameters=params, recursive="js")


def presentation_declarations():
    br_t, ar_t, pa_t, jo_t, pg_t = named("Brand"), named("Artifact"), named("Panel"), named("Journey"), named("Paragraph")
    po_t, st_t, ve_t = named("Pole"), named("Step"), named("Verification")
    pt_t, nv_t, ni_t = named("Pattern"), named("Navigation"), named("NavItem")
    nil_s, nil_n = {"kind": "nil", "element": STR}, {"kind": "nil", "element": NAT}
    # the steps of the journey under `head`, inside an `_each_journey` condition
    steps_of_head = call("stepsOfJourney", proj(var("head"), "id"), var("ss"))
    return [
        structure("Brand", [("name", STR), ("tagline", STR), ("description", STR), ("logo", STR)]),
        structure("Artifact", [("id", STR), ("path", STR), ("mediaType", STR), ("command", STR)]),
        structure("Panel", [("id", STR), ("title", STR), ("viewpoint", STR), ("artifact", STR), ("statement", STR)]),
        structure("Journey", [("id", STR), ("stakeholder", STR), ("panels", list_t(STR))]),
        structure("Paragraph", [("id", STR), ("title", STR), ("text", STR)]),
        structure("Pole", [("id", STR), ("title", STR), ("statement", STR)]),
        structure("Step", [("id", STR), ("journey", STR), ("order", NAT), ("pole", STR), ("panel", STR), ("title", STR), ("goal", STR),
                           ("text", STR), ("paragraphs", list_t(STR)), ("evidence", list_t(STR)), ("next", STR)]),
        structure("Verification", [("command", STR), ("invocation", STR), ("statement", STR)]),
        structure("Pattern", [("id", STR), ("authority", STR), ("statement", STR)]),
        structure("Navigation", [("id", STR), ("label", STR), ("pattern", STR), ("statement", STR)]),
        structure("NavItem", [("id", STR), ("navigation", STR), ("parent", STR), ("label", STR), ("pattern", STR), ("kind", STR),
                              ("target", STR), ("order", NAT)]),
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
        definition("poles", list_t(po_t), lst([record("Pole", id=s(x["id"]), title=s(x["title"]), statement=s(x["statement"]))
                                              for x in POLES], po_t)),
        definition("steps", list_t(st_t), lst([
            record("Step", id=s(x["id"]), journey=s(x["journey"]), order=n(x["order"]), pole=s(x["pole"]), panel=s(x["panel"]),
                   title=s(x["title"]), goal=s(x["goal"]), text=s(x["text"]), paragraphs=strings(x["paragraphs"]),
                   evidence=strings(x["evidence"]), next=s(x["next"])) for x in STEPS], st_t)),
        definition("verifications", list_t(ve_t), lst([
            record("Verification", command=s(x["command"]), invocation=s(x["invocation"]), statement=s(x["statement"]))
            for x in VERIFICATIONS], ve_t)),
        definition("navPatterns", list_t(pt_t), lst([
            record("Pattern", id=s(x["id"]), authority=s(x["authority"]), statement=s(x["statement"])) for x in NAV_PATTERNS], pt_t)),
        definition("navigations", list_t(nv_t), lst([
            record("Navigation", id=s(x["id"]), label=s(x["label"]), pattern=s(x["pattern"]), statement=s(x["statement"]))
            for x in NAVIGATIONS], nv_t)),
        definition("navItems", list_t(ni_t), lst([
            record("NavItem", id=s(x["id"]), navigation=s(x["navigation"]), parent=s(x["parent"]), label=s(x["label"]),
                   pattern=s(x["pattern"]), kind=s(x["kind"]), target=s(x["target"]), order=n(x["order"])) for x in NAV_ITEMS], ni_t)),
        member_string(), all_members(), index_of(), _append_strings(), _distinct("distinctStrings"),
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
        # the pedagogy: the steps of each journey, their orders, poles, panels, links
        field_of_each("journeyIds", jo_t, "id"),
        field_of_each("poleIds", po_t, "id"),
        field_of_each("stepIds", st_t, "id"),
        field_of_each("stepJourneys", st_t, "journey"),
        field_of_each("stepPoles", st_t, "pole"),
        field_of_each("stepPanels", st_t, "panel"),
        field_of_each("stepOrders", st_t, "order", result=NAT),
        field_of_each("verificationCommands", ve_t, "command"),
        definition("stepParagraphs", list_t(STR),
                   match_list(var("xs"), nil_s, "head", "tail",
                              call("appendStrings", proj(var("head"), "paragraphs"), call("stepParagraphs", var("tail")))),
                   parameters=[("xs", list_t(st_t))], recursive="xs"),
        definition("stepEvidence", list_t(STR),
                   match_list(var("xs"), nil_s, "head", "tail",
                              call("appendStrings", proj(var("head"), "evidence"), call("stepEvidence", var("tail")))),
                   parameters=[("xs", list_t(st_t))], recursive="xs"),
        definition("stepsOfJourney", list_t(st_t),
                   match_list(var("xs"), {"kind": "nil", "element": st_t}, "head", "tail",
                              if_(eq_string(var("journey"), proj(var("head"), "journey")),
                                  {"kind": "cons", "head": var("head"), "tail": call("stepsOfJourney", var("journey"), var("tail"))},
                                  call("stepsOfJourney", var("journey"), var("tail")))),
                   parameters=[("journey", STR), ("xs", list_t(st_t))], recursive="xs"),
        # the orders are next, next+1, ...
        definition("consecutiveFrom", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(beq(var("head"), var("next")), call("consecutiveFrom", var("tail"), add(var("next"), n(1))), b(False))),
                   parameters=[("xs", list_t(NAT)), ("next", NAT)], recursive="xs"),
        # the position of each step's pole in the canonical order
        definition("poleIndices", list_t(NAT),
                   match_list(var("xs"), nil_n, "head", "tail",
                              {"kind": "cons", "head": call("indexOf", var("head"), var("ids")), "tail": call("poleIndices", var("tail"), var("ids"))}),
                   parameters=[("xs", list_t(STR)), ("ids", list_t(STR))], recursive="xs"),
        definition("nonDecreasing", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(ble(var("previous"), var("head")), call("nonDecreasing", var("tail"), var("head")), b(False))),
                   parameters=[("xs", list_t(NAT)), ("previous", NAT)], recursive="xs"),
        definition("lastString", STR,
                   match_list(var("xs"), var("default"), "head", "tail", call("lastString", var("tail"), var("head"))),
                   parameters=[("xs", list_t(STR)), ("default", STR)], recursive="xs"),
        definition("firstStepId", STR,
                   match_list(var("xs"), s(""), "head", "tail", proj(var("head"), "id")),
                   parameters=[("xs", list_t(st_t))]),
        # each step's `next` is the id of the step after it, "" at the end
        definition("linkedByNext", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(eq_string(proj(var("head"), "next"), call("firstStepId", var("tail"))),
                                  call("linkedByNext", var("tail")), b(False))),
                   parameters=[("xs", list_t(st_t))], recursive="xs"),
        definition("sameMembers", BOOL, if_(call("allMembers", var("xs"), var("ys")), call("allMembers", var("ys"), var("xs")), b(False)),
                   parameters=[("xs", list_t(STR)), ("ys", list_t(STR))]),
        _each_journey("stepsConsecutive", call("consecutiveFrom", call("stepOrders", steps_of_head), n(1))),
        _each_journey("stepsLinked", call("linkedByNext", steps_of_head)),
        _each_journey("polesInOrder",
                      if_(call("nonDecreasing", call("poleIndices", call("stepPoles", steps_of_head), var("ps")), n(0)),
                          call("allMembers", var("ps"), call("stepPoles", steps_of_head)), b(False)),
                      extra=[("ps", list_t(STR))]),
        _each_journey("endInVerification", eq_string(call("lastString", call("stepPoles", steps_of_head), s("")), s("verification"))),
        _each_journey("panelsAreStepPanels", call("sameMembers", proj(var("head"), "panels"), call("stepPanels", steps_of_head))),
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
        # the pedagogy, decided: steps show panels of journeys at declared poles,
        # in consecutive linked order covering the poles in their canonical order,
        # ending in verification, on declared evidence and paragraphs
        holds("stepIdsDistinct", call("distinctStrings", call("stepIds", call("steps")))),
        holds("stepPanelsArePanels", call("allMembers", call("stepPanels", call("steps")), call("panelIds", call("panels")))),
        holds("stepJourneysAreJourneys", call("allMembers", call("stepJourneys", call("steps")), call("journeyIds", call("journeys")))),
        holds("everyJourneyHasSteps", call("allMembers", call("journeyIds", call("journeys")), call("stepJourneys", call("steps")))),
        holds("everyPanelInAStep", call("allMembers", call("panelIds", call("panels")), call("stepPanels", call("steps")))),
        holds("stepPolesDeclared", call("allMembers", call("stepPoles", call("steps")), call("poleIds", call("poles")))),
        holds("journeysStepsConsecutive", call("stepsConsecutive", call("journeys"), call("steps"))),
        holds("journeysStepsLinked", call("stepsLinked", call("journeys"), call("steps"))),
        holds("journeysCoverPolesInOrder", call("polesInOrder", call("journeys"), call("steps"), call("poleIds", call("poles")))),
        holds("journeysEndInVerification", call("endInVerification", call("journeys"), call("steps"))),
        holds("journeyPanelsAreStepPanels", call("panelsAreStepPanels", call("journeys"), call("steps"))),
        holds("stepParagraphsDeclared", call("allMembers", call("stepParagraphs", call("steps")), call("paragraphIds", call("explainer")))),
        holds("stepEvidenceDeclared",
              call("allMembers", call("stepEvidence", call("steps")),
                   call("appendStrings", call("idsOf", call("claims", module="Register"), module="Register"), call("artifactIds", call("artifacts"))))),
        holds("verificationsAreCommands",
              call("allMembers", call("verificationCommands", call("verifications")),
                   call("commandNames", call("commands", module="Api"), module="Architecture"))),
        # the navigation (WAI-ARIA APG): its ids, patterns, targets and trails
        field_of_each("patternIds", pt_t, "id"),
        field_of_each("navigationIds", nv_t, "id"),
        field_of_each("navigationPatterns", nv_t, "pattern"),
        field_of_each("navItemIds", ni_t, "id"),
        field_of_each("navItemNavigations", ni_t, "navigation"),
        field_of_each("navItemParents", ni_t, "parent"),
        field_of_each("navItemPatterns", ni_t, "pattern"),
        field_of_each("navItemKinds", ni_t, "kind"),
        field_of_each("navItemTargets", ni_t, "target"),
        field_of_each("navItemOrders", ni_t, "order", result=NAT),
        definition("navItemsOf", list_t(ni_t),
                   match_list(var("xs"), {"kind": "nil", "element": ni_t}, "head", "tail",
                              if_(eq_string(var("navigation"), proj(var("head"), "navigation")),
                                  {"kind": "cons", "head": var("head"), "tail": call("navItemsOf", var("navigation"), var("tail"))},
                                  call("navItemsOf", var("navigation"), var("tail")))),
                   parameters=[("navigation", STR), ("xs", list_t(ni_t))], recursive="xs"),
        definition("navItemsUnder", list_t(ni_t),
                   match_list(var("xs"), {"kind": "nil", "element": ni_t}, "head", "tail",
                              if_(eq_string(var("parent"), proj(var("head"), "parent")),
                                  {"kind": "cons", "head": var("head"), "tail": call("navItemsUnder", var("parent"), var("tail"))},
                                  call("navItemsUnder", var("parent"), var("tail")))),
                   parameters=[("parent", STR), ("xs", list_t(ni_t))], recursive="xs"),
        definition("navItemsOfKind", list_t(ni_t),
                   match_list(var("xs"), {"kind": "nil", "element": ni_t}, "head", "tail",
                              if_(eq_string(var("kind"), proj(var("head"), "kind")),
                                  {"kind": "cons", "head": var("head"), "tail": call("navItemsOfKind", var("kind"), var("tail"))},
                                  call("navItemsOfKind", var("kind"), var("tail")))),
                   parameters=[("kind", STR), ("xs", list_t(ni_t))], recursive="xs"),
        # the targets of the items of one kind in one navigation
        definition("navTargets", list_t(STR),
                   call("navItemTargets", call("navItemsOfKind", var("kind"), call("navItemsOf", var("navigation"), var("xs")))),
                   parameters=[("kind", STR), ("navigation", STR), ("xs", list_t(ni_t))]),
        lookup_field("navItemTarget", ni_t, "id", "target", STR, s("")),
        lookup_field("stepPanel", st_t, "id", "panel", STR, s("")),
        # the breadcrumb of a step: its vantage, its pole, itself
        definition("breadcrumbOf", list_t(STR),
                   {"kind": "cons", "head": proj(var("st"), "journey"),
                    "tail": {"kind": "cons", "head": proj(var("st"), "pole"),
                             "tail": {"kind": "cons", "head": proj(var("st"), "id"), "tail": nil_s}}},
                   parameters=[("st", st_t)]),
        definition("trailResolves", BOOL,
                   match_list(var("trail"), b(False), "j", "rest",
                              match_list(var("rest"), b(False), "p", "rest2",
                                         match_list(var("rest2"), b(False), "sid", "rest3",
                                                    if_(call("memberString", var("j"), var("js")),
                                                        if_(call("memberString", var("p"), var("ps")),
                                                            call("memberString", var("sid"), var("ids")), b(False)), b(False))))),
                   parameters=[("trail", list_t(STR)), ("js", list_t(STR)), ("ps", list_t(STR)), ("ids", list_t(STR))]),
        definition("breadcrumbsResolve", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(call("trailResolves", call("breadcrumbOf", var("head")), var("js"), var("ps"), var("ids")),
                                  call("breadcrumbsResolve", var("tail"), var("js"), var("ps"), var("ids")), b(False))),
                   parameters=[("xs", list_t(st_t)), ("js", list_t(STR)), ("ps", list_t(STR)), ("ids", list_t(STR))], recursive="xs"),
        # under every top-level item of a navigation, the orders are 1, 2, ...
        definition("groupsOrdered", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_(call("consecutiveFrom", call("navItemOrders", call("navItemsUnder", proj(var("head"), "id"), var("all"))), n(1)),
                                  call("groupsOrdered", var("tail"), var("all")), b(False))),
                   parameters=[("xs", list_t(ni_t)), ("all", list_t(ni_t))], recursive="xs"),
        _each_journey("verifyReachable", call("memberString", call("lastString", call("stepIds", steps_of_head), s("")), var("ts")),
                      extra=[("ts", list_t(STR))]),
        holds("navIdsDistinct", call("distinctStrings", call("appendStrings", call("navigationIds", call("navigations")), call("navItemIds", call("navItems"))))),
        holds("navigationsNamePatterns", call("allMembers", call("navigationPatterns", call("navigations")), call("patternIds", call("navPatterns")))),
        holds("navItemsNamePatterns", call("allMembers", call("navItemPatterns", call("navItems")), call("patternIds", call("navPatterns")))),
        holds("navItemsInNavigations", call("allMembers", call("navItemNavigations", call("navItems")), call("navigationIds", call("navigations")))),
        holds("navItemParentsAreItems",
              call("allMembers", call("navItemParents", call("navItems")), {"kind": "cons", "head": s(""), "tail": call("navItemIds", call("navItems"))})),
        holds("everyJourneyInPrimaryNavigation",
              call("allMembers", call("journeyIds", call("journeys")), call("navTargets", s("journey"), s("nav-primary"), call("navItems")))),
        holds("stepperListsEveryJourney",
              call("allMembers", call("journeyIds", call("journeys")), call("navTargets", s("journey"), s("nav-stepper"), call("navItems")))),
        holds("navJourneyTargetsAreJourneys",
              call("allMembers", call("appendStrings", call("navTargets", s("journey"), s("nav-primary"), call("navItems")),
                                      call("navTargets", s("journey"), s("nav-stepper"), call("navItems"))),
                   call("journeyIds", call("journeys")))),
        holds("navStepTargetsAreSteps",
              call("allMembers", call("navTargets", s("step"), s("nav-primary"), call("navItems")), call("stepIds", call("steps")))),
        holds("navArtifactTargetsAreArtifacts",
              call("allMembers", call("navTargets", s("artifact"), s("nav-primary"), call("navItems")), call("artifactIds", call("artifacts")))),
        theorem("breadcrumbIsVantagePoleStep",
                call("navItemKinds", call("navItemsOf", s("nav-breadcrumb"), call("navItems"))), strings(["journey", "pole", "step"])),
        holds("everyBreadcrumbResolves",
              call("breadcrumbsResolve", call("steps"), call("journeyIds", call("journeys")), call("poleIds", call("poles")), call("stepIds", call("steps")))),
        holds("verifyReachableFromEveryJourney",
              call("verifyReachable", call("journeys"), call("steps"), call("navTargets", s("step"), s("nav-primary"), call("navItems")))),
        holds("searchOpensTheRegister",
              eq_string(call("stepPanel", call("navItemTarget", s("nav-search"), call("navItems")), call("steps")), s("register"))),
        holds("navGroupsOrdered",
              call("groupsOrdered", call("navItemsUnder", s(""), call("navItemsOf", s("nav-primary"), call("navItems"))),
                   call("navItemsOf", s("nav-primary"), call("navItems")))),
        holds("navTopLevelOrdered",
              call("consecutiveFrom", call("navItemOrders", call("navItemsUnder", s(""), call("navItemsOf", s("nav-primary"), call("navItems")))), n(1))),
    ] + designmodel.declarations() + viz_declarations()


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
    return lexmod.module("Presentation", presentation_declarations(), imports=["Api", "Architecture", "Register"])


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
    return {"module": str(PRESENTATION.relative_to(repo.ROOT)), "panels": len(PANELS), "steps": len(STEPS), "navItems": len(NAV_ITEMS),
            "changed": p or a}


def check():
    for path, text in ((PRESENTATION, render_presentation()), (APPLICATION, render_application())):
        if not path.exists():
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} is missing; run `bin/r30 api sync`"}
        if path.read_text() != text:
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} drifted; run `bin/r30 api sync`"}
    return {"ok": True, "reason": None}
