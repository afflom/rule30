"""The visualizations of the registered claims, as data.

Six panels of the site are computed in the reader's browser, each from the
one rule (`y -> y XOR ((y << 1) OR (y << 2))` on BigInt rows) and each a
picture of proved claims of the register:

- `viz-triangle`: the rows, a cell read as (time, position, bit), the right
  diagonals coloured by their period (a divisor of `2^(j-1)`), the center;
- `viz-tower`: the tower of words, the anti-diagonal, the recursion, the
  exposed masks (left run-ends) and the Lucas frame of the center;
- `viz-ledger`: `center = rulerBackground XOR interiorEightDiagonal` on
  aligned rows, the four rulers separable;
- `viz-rays`: the kernel law on the ray `2^k u + r`, the residue dichotomy,
  the second table;
- `viz-defects`: the lag-P defect field, the gated columns, the collisions;
- `viz-dyadic`: the dyadic column and the block parities of `dyadicRow`.

`VIZ_PANELS` are panels of `Presentation` (`presentationmodel` concatenates
them into `PANELS`); each names the script artifact that renders it and the
claims it `renders`. `VIZ_ARTIFACTS` are the scripts (`application/javascript`,
copied by `view render`). `VIZ_STEPS` place each panel in the journeys at the
sensual-quality pole (`with_viz_steps` inserts them after their anchor step).
`viz_declarations` are the declarations `Presentation.lex.tex` gains: the
`VizPanel` rows and the decided theorems that every viz panel is a panel of
a step, its script a published artifact, and that what it renders is a
non-empty list of proved claims of `Register` (`Register::idsOf`). `publish`
is the hook `site.render_view` calls; `problems` is the same decision in
Python, so a bad row is named before the kernel refuses the module.

Each script registers `window.r30viz[panelId] = function (slot, viewData)`
on the shared core `viz/core.js`; the page loads the scripts the view data
lists as `application/javascript` artifacts under `viz/`."""

import shutil

from . import frontier, repo
from .semantic import BOOL, STR, b, call, definition, eq_string, field_of_each, holds, if_, list_t, lookup_field, lst, match_list, named, proj, record, s, strings, structure, var

VIZ_DIR = "rule30-api/site/viz"
SCRIPTS = ["core", "triangle", "tower", "ledger", "rays", "defects", "dyadic"]

# The scripts, in load order (the core first): published beside the page.
VIZ_ARTIFACTS = [
    {"id": f"viz-{name}-js", "path": f"viz/{name}.js", "media": "application/javascript", "command": "view_render",
     "source": f"{VIZ_DIR}/{name}.js"} for name in SCRIPTS
]

# The claims each panel renders, as declared. A declared id the register
# does not hold yet (a claim landing in a concurrent batch) is left out of
# the generated rows until it is registered, so the kernel's decision stays
# true and the row grows by itself on the next `api sync`.
_DECLARED = {
    "viz-triangle": ["antidiagonal", "diagonal-halving", "edge-parity"],
    "viz-tower": ["antidiagonal", "diagonal-halving", "mask-transport", "lucas-frame"],
    "viz-ledger": ["left-band", "three-diagonal-band", "edge-parity"],
    "viz-rays": ["kernel-law", "residue-dichotomy", "second-table"],
    "viz-defects": ["coupling-law", "left-defect-sourcing", "recurrent-central-collision"],
    "viz-dyadic": ["scale-free-rows", "dyadic-response-reduction"],
}


def _registered():
    try:
        return {c["id"] for c in frontier.load()["claim"]}
    except (OSError, KeyError):
        return set()


_REGISTERED = _registered()


def declared(panel_id):
    """The claims a panel is declared to render, registered or not."""
    return list(_DECLARED[panel_id])


def _renders(panel_id):
    return [i for i in _DECLARED[panel_id] if i in _REGISTERED]


VIZ_PANELS = [
    {"id": "viz-triangle", "title": "The triangle, explored", "viewpoint": "plain", "artifact": "viz-triangle-js",
     "renders": _renders("viz-triangle"),
     "statement": "Rule 30 from a single black cell, rows 0 to N (N up to 256), computed in your browser: move through it with the keyboard, read any cell as a time, a position and a bit, colour the right diagonals by their period (it always divides 2^(j-1)), and follow the center column, which is the diagonal t = j of that table."},
    {"id": "viz-tower", "title": "The tower of words", "viewpoint": "paper", "artifact": "viz-tower-js",
     "renders": _renders("viz-tower"),
     "statement": "Each right diagonal rdiag j as one word of length 2^(j-1) (j up to 10), generated from the words above it by towerWord (k+2) (s+1) = towerWord (k+2) s XOR (towerWord (k+1) s OR towerWord k s), stepped on demand; the anti-diagonal towerWord t t = center t marked; the exposed masks (the left ends of black runs) toggled; and center t = not lucasSum (t-2) t recomputed from the masks with their Lucas weights."},
    {"id": "viz-ledger", "title": "The center as rulers plus deep bulk", "viewpoint": "plain", "artifact": "viz-ledger-js",
     "renders": _renders("viz-ledger"),
     "statement": "Aligned bit rows for t up to 512: the center, the ruler background with its four rulers separable, and the deep bulk interiorEightDiagonal computed from its own ledger, with center t = rulerBackground t XOR interiorEightDiagonal t checked at every t from 6 and the three-diagonal form from 2."},
    {"id": "viz-rays", "title": "The kernel law on a dyadic ray", "viewpoint": "paper", "artifact": "viz-rays-js",
     "renders": _renders("viz-rays"),
     "statement": "Choose a scale k and a residue r: the times 2^k u + r, the frozen prefix, the second table over every residue (0, 0, 0, 1 on the first four), the late tail, and the kernel law checked at each u; the residues 1 and 2, where the ruler background moves with u, highlighted."},
    {"id": "viz-defects", "title": "The lag-P defect field", "viewpoint": "paper", "artifact": "viz-defects-js",
     "renders": _renders("viz-defects"),
     "statement": "Choose a lag P (1 to 64): where row t and row t+P differ in the cone for t up to 256, the center, column -1 and column +1 highlighted, the collisions marked, and the coupling law checked wherever the center agrees at lag P."},
    {"id": "viz-dyadic", "title": "The dyadic column", "viewpoint": "paper", "artifact": "viz-dyadic-js",
     "renders": _renders("viz-dyadic"),
     "statement": "The column center (2^j), the scale-free sequence dyadicRow m with its blocks [2^j, 2^(j+1)) and their parities, and center (2^(j+1)) = center (2^j) XOR blockParity j checked at every scale shown."},
]

_BY_ID = {p["id"]: p for p in VIZ_PANELS}


def _evidence(panel_id):
    p = _BY_ID[panel_id]
    return [p["artifact"]] + p["renders"]


def _artifact_evidence(panel_id):
    """Evidence for a visualization the mathematician meets before its claims are introduced
    (that journey reads claims in dependency order at the real-quality pole): the published
    script only; the claims it renders stay linked through the panel's decided `renders` list."""
    return [_BY_ID[panel_id]["artifact"]]


# The steps, by journey, all at the sensual-quality pole: how the proof
# appears from the vantage. `after` is the step a viz step follows; when the
# journey no longer has it, the step goes after the journey's last step at or
# before the sensual-quality pole.
VIZ_STEPS = {
    "first-visit": [
        {"after": "fv-tree", "id": "fv-explore", "pole": "sensual-quality", "panel": "viz-triangle", "title": "Explore the triangle yourself",
         "goal": "Move through the rows with the keyboard, read any cell as a time, a position and a black or white bit, and see the diagonals on the right edge repeat with periods that double as you move inward, while the center column shows no such repetition.",
         "text": "Everything in this picture is computed in your browser from the one rule, row by row. Switch on the diagonals of the right edge: each repeats, the first with period 2, then 2, 4, 8, 8, 16, 32, 32, and the period of the j-th always divides 2^(j-1), which is proved. The center column cuts across all of them, one cell from each: its value at row t is the cell where row t meets diagonal t. That is why the regular edge says nothing yet about the center, and it is exactly the question Problem 1 asks.",
         "evidence": _evidence("viz-triangle")},
        {"after": "fv-reductions", "id": "fv-bands", "pole": "sensual-quality", "panel": "viz-ledger", "title": "See the bands stripped away",
         "goal": "See the center column as two rows added bit by bit: a background made of four simple rulers, and what remains, the deep bulk; the remaining obligation is a statement about that last row alone.",
         "text": "The top row is the center column itself. The middle row is the ruler background: four rhythms, each switchable on its own, that the proved statements identify exactly. The bottom row is what is left once the background is taken away, computed separately from the rule, and the page checks at every time from 6 to 512 that the top row equals the other two combined. Nothing in the bottom row is claimed to repeat or not to repeat; that is the open question.",
         "evidence": _evidence("viz-ledger")},
    ],
    "mathematics": [
        {"after": "ma-tree", "id": "ma-tower", "pole": "sensual-quality", "panel": "viz-tower", "title": "The right half-plane as a tower of words",
         "goal": "See every right diagonal as a word of length 2^(j-1) generated by one local recursion from the words 1 and the time parity, the center as the anti-diagonal towerWord t t, the exposed masks as the left ends of black runs, and center t = not lucasSum (t-2) t as a Lucas-weighted sum of those masks.",
         "text": "rdiag j t = cell t (t-j) is bit j of row t, so the words are read off the rows; the recursion rebuilds each word from the two above it and the panel checks the two agree. Each word is periodic from time 0 with period dividing 2^(j-1) (diagonal-halving), Problem 1 is the statement that the anti-diagonal of this table is not eventually periodic (antidiagonal), the OR of the recursion splits into the previous word plus the exposed mask, whose transport gives center t = not maskTransport (t-2) t (mask-transport), and its weights are binomial parities C(t-1-j, t-2-i) mod 2 (lucas-frame). Choose t to see the cells that carry weight.",
         "evidence": _artifact_evidence("viz-tower")},
        {"after": "ma-tower", "id": "ma-ledger", "pole": "sensual-quality", "panel": "viz-ledger", "title": "The center against the rulers",
         "goal": "Read center t = rulerBackground t XOR interiorEightDiagonal t on aligned rows for t up to 512, the four rulers trailingParity (t-2), not timeParity t, trailingParity (t-4) and trailingParity ((t-4)/2) separable, the deep bulk computed from its own ledger.",
         "text": "The deep bulk row is the diagonal of the ledger of the carries on right diagonals at least 3 and left diagonals at least 8, not derived from the identity, and the identity is checked at every t from 6: a finite replay in the browser of center_eq_rulerBackground_bxor_eight. The open obligation EightAperiodic is a statement about the bottom row against the middle one.",
         "evidence": _artifact_evidence("viz-ledger")},
        {"after": "ma-ledger", "id": "ma-defects", "pole": "sensual-quality", "panel": "viz-defects", "title": "The defect field of a lag",
         "goal": "Choose a lag P and see where row t and row t+P differ, the center, the gated column -1 and column +1, and the collisions; check the coupling law wherever the center agrees at lag P.",
         "text": "The defect field is where the nonlinear facts bite: where the center agrees at lag P, the next center defect is leftDefect t 1 XOR (not center t AND rightDefect t 1), so a center period is exactly this coupling at every later time (coupling-law); every left defect is sourced from column +1 within its depth (left-defect-sourcing); and Problem 1 is the statement that no period admits recurrent collisions in the central band (recurrent-central-collision). The panel computes the field and marks every collision.",
         "evidence": _artifact_evidence("viz-defects")},
        {"after": "ma-defects", "id": "ma-rays", "pole": "sensual-quality", "panel": "viz-rays", "title": "The kernel law on a ray",
         "goal": "Choose k and r and read center (2^k u + r) as the kernel law writes it: the frozen prefix, the ruler term trailingParity (u-1) AND secondPrefix k r, the late tail; see the second table over the residues and the residues 1 and 2 where the ruler background moves with u.",
         "text": "frozenPrefix, secondPrefix and lateTail are read off the interior ledger exactly as Rule30UOR.KernelLaw defines them, and the law is checked at each u shown. The second table reads 0 on residues 0, 1, 2 and 1 on residue 3 at every scale (second-table), and the ruler background depends on u only on residues 1 and 2 (residue-dichotomy): there the late tail must supply the ruler, on residue 3 it must cancel the one the frozen rows carry.",
         "evidence": _artifact_evidence("viz-rays")},
        {"after": "ma-rays", "id": "ma-dyadic-column", "pole": "sensual-quality", "panel": "viz-dyadic", "title": "The dyadic column and its block parities",
         "goal": "Read the dyadic column center (2^j) as the prefix parity of the scale-free sequence dyadicRow, block by block: center (2^(j+1)) = center (2^j) XOR blockParity j.",
         "text": "dyadicRow m is row m's term at any dyadic time beyond m (scale-free-rows), the blocks [2^j, 2^(j+1)) are marked with their parities, and the step identity is checked at every scale shown. The open leaf dyadic-column-aperiodic says this column is not eventually periodic (dyadic-response-reduction carries it to Problem 1); the panel shows the column, it does not decide it.",
         "evidence": _artifact_evidence("viz-dyadic")},
    ],
    "prize-review": [
        {"after": "pr-leaves", "id": "pr-antidiagonal", "pole": "sensual-quality", "panel": "viz-tower", "title": "Problem 1 as one diagonal of a table",
         "goal": "See Problem 1 in the form with no free input: two constant words, one local recursion, and the anti-diagonal read; Problem 1 holds exactly when that anti-diagonal is not eventually periodic.",
         "evidence": _evidence("viz-tower")},
    ],
    "reading": [
        {"after": "rd-sheet", "id": "rd-triangle", "pole": "sensual-quality", "panel": "viz-triangle", "title": "The pattern itself",
         "goal": "Compute the triangle in the browser, read any cell, and see the right diagonals repeat with periods dividing 2^(j-1) while the center column, which meets each of them once, does not.",
         "evidence": _evidence("viz-triangle")},
        {"after": "rd-triangle", "id": "rd-tower", "pole": "sensual-quality", "panel": "viz-tower", "title": "The tower behind the pattern",
         "goal": "See the right diagonals as words generated by one local recursion, the center as the anti-diagonal, and the left ends of black runs as the masks the center is a weighted sum of.",
         "evidence": _evidence("viz-tower")},
    ],
}

_EARLY_POLES = ("sensual-object", "sensual-quality")


def with_viz_steps(steps):
    """The journeys' step lists with the viz steps inserted: each after its
    anchor, or after the journey's last step at or before the
    sensual-quality pole. Returns a new dict; `steps` is not changed."""
    out = {j: list(seq) for j, seq in steps.items()}
    for journey, extra in VIZ_STEPS.items():
        if journey not in out:
            continue
        seq = out[journey]
        for st in extra:
            row = {k: v for k, v in st.items() if k != "after"}
            ids = [x["id"] for x in seq]
            if st["after"] in ids:
                at = ids.index(st["after"]) + 1
            else:
                early = [i for i, x in enumerate(seq) if x["pole"] in _EARLY_POLES]
                at = early[-1] + 1 if early else 0
            seq.insert(at, row)
    return out


def problems(claims=None, panels=None, steps=None, artifacts=None):
    """What `viz_declarations` decides, in Python: every viz panel is a panel
    shown by some step, its script is a published artifact, and it renders a
    non-empty list of proved claims of the register."""
    from . import presentationmodel as pm
    claims = frontier.load()["claim"] if claims is None else claims
    status = {c["id"]: c["status"] for c in claims}
    panel_ids = {p["id"] for p in (pm.PANELS if panels is None else panels)}
    step_panels = {st["panel"] for st in (pm.STEPS if steps is None else steps)}
    artifact_ids = {a["id"] for a in (pm.ARTIFACTS if artifacts is None else artifacts)}
    out = []
    for p in VIZ_PANELS:
        if p["id"] not in panel_ids:
            out.append(f"viz panel {p['id']} is not a panel")
        if p["id"] not in step_panels:
            out.append(f"viz panel {p['id']} is shown by no step")
        if p["artifact"] not in artifact_ids:
            out.append(f"viz panel {p['id']}: script {p['artifact']} is not an artifact")
        if not p["renders"]:
            out.append(f"viz panel {p['id']} renders no claim")
        for r in p["renders"]:
            if r not in status:
                out.append(f"viz panel {p['id']} renders {r}, which is not a claim")
            elif status[r] != "proved":
                out.append(f"viz panel {p['id']} renders {r}, which is {status[r]}, not proved")
    return out


def viz_declarations():
    """The declarations `Presentation.lex.tex` gains for the visualizations.
    They use the module's `allMembers`, `appendStrings`, `panelIds`,
    `artifactIds`, `stepPanels`, `panels`, `artifacts` and `steps`."""
    vp_t = named("VizPanel")
    claim_t = named("Claim", "Register")
    return [
        structure("VizPanel", [("id", STR), ("script", STR), ("renders", list_t(STR))]),
        definition("vizPanels", list_t(vp_t), lst([
            record("VizPanel", id=s(p["id"]), script=s(p["artifact"]), renders=strings(p["renders"])) for p in VIZ_PANELS], vp_t)),
        field_of_each("vizPanelIds", vp_t, "id"),
        field_of_each("vizScripts", vp_t, "script"),
        # every claim id the visualizations render
        definition("vizRenders", list_t(STR),
                   match_list(var("xs"), {"kind": "nil", "element": STR}, "head", "tail",
                              call("appendStrings", proj(var("head"), "renders"), call("vizRenders", var("tail")))),
                   parameters=[("xs", list_t(vp_t))], recursive="xs"),
        # every viz panel renders at least one claim
        definition("vizEachRenders", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              match_list(proj(var("head"), "renders"), b(False), "r", "rs", call("vizEachRenders", var("tail")))),
                   parameters=[("xs", list_t(vp_t))], recursive="xs"),
        # the status of a claim of Register, and every id of a list proved
        lookup_field("vizClaimStatus", claim_t, "id", "status", STR, s("")),
        definition("vizAllProved", BOOL,
                   match_list(var("ids"), b(True), "head", "tail",
                              if_(eq_string(call("vizClaimStatus", var("head"), var("cs")), s("proved")),
                                  call("vizAllProved", var("tail"), var("cs")), b(False))),
                   parameters=[("ids", list_t(STR)), ("cs", list_t(claim_t))], recursive="ids"),
        holds("vizPanelsArePanels", call("allMembers", call("vizPanelIds", call("vizPanels")), call("panelIds", call("panels")))),
        holds("vizPanelsAreSteps", call("allMembers", call("vizPanelIds", call("vizPanels")), call("stepPanels", call("steps")))),
        holds("vizScriptsArePublished", call("allMembers", call("vizScripts", call("vizPanels")), call("artifactIds", call("artifacts")))),
        holds("vizPanelsRender", call("vizEachRenders", call("vizPanels"))),
        holds("vizRendersAreClaims",
              call("allMembers", call("vizRenders", call("vizPanels")), call("idsOf", call("claims", module="Register"), module="Register"))),
        holds("vizRendersAreProved", call("vizAllProved", call("vizRenders", call("vizPanels")), call("claims", module="Register"))),
    ]


def publish(out):
    """The hook `site.render_view` calls before it writes the artifacts:
    refuses a viz row the kernel would refuse, and makes the scripts'
    directory, into which the artifact loop copies them."""
    bad = problems()
    if bad:
        raise ValueError("; ".join(bad))
    (out / "viz").mkdir(parents=True, exist_ok=True)
    for a in VIZ_ARTIFACTS:
        shutil.copyfile(repo.ROOT / a["source"], out / a["path"])
    return [a["path"] for a in VIZ_ARTIFACTS]
