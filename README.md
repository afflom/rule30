# Rule 30 — LexLean & Lean 4 Formalization (`v0.1`)

**Working here:** read [AGENTS.md](AGENTS.md). The command surface is `bin/r30`
(`status`, `frontier`, `lexicon search`, `theorem add`, `check`, `verify`, `axioms`,
`commit`); it generates glossary entries and statements from Lean declarations, checks
one module in seconds, and is also an MCP server. The claim register is
[`frontier.toml`](frontier.toml).

**Research status on `main`: Problem 1 remains unproved.** The `v0.1` tag and release artifacts
are unchanged. Subsequent host Lean work audits the refutation engines and formalizes exact
temporal differences, their aperiodic compensation constraint, and a physically aligned Witt
pair evolution. See the [current proof frontier](rule30-lexlean/STRATEGY.md#current-proof-frontier-2026-10-28).
Run `make check-research` to build and independently kernel-check these additions and enforce
the allowed axiom set across every `Rule30UOR` theorem. Module coverage is checked before
building: every host source must be a Lake root and an axiom-audit import, and kernel replay
uses that same root list. The current research statements are published in the observations PDF below.
The additional LexLean entrypoint [Observations.lex.tex](rule30-paper/src/Observations.lex.tex)
contains the checked masked-observation, information-bound, and central-collision recurrence results; packaging renders
it as [Rule30-Observations.pdf](Rule30-Observations.pdf) and `dist/Observations.pdf`. Its `r30.frontier` vocabulary also exports the exact
equivalences between Problem 1, the Witt center condition, and the collision obstruction.

Kernel-checked [LexLean](https://github.com/afflom) and Lean 4 formalization of Wolfram's **Rule 30** cellular automaton (`Rule 30 Prize Problem 1` program) using the UOR Atlas, 2-adic Witt / carry-algebra coordinates, left-diagonal doubling theory, and driven right-half (`kit [33]`) spatio-temporal self-similarity.

The authored statements in [Paper](Rule30-Paper.pdf), [Core](Rule30-Core.pdf), and
[Observations](Rule30-Observations.pdf) are verified by the Lean 4 kernel
(`leanprover/lean4:v4.32.1`) and `leanchecker` under only the axioms `{propext, Quot.sound}`,
with zero `sorry`s and zero custom axioms. **`Classical.choice` is not used anywhere in the
authored proof surfaces.** The kernel audits of the research library and of the bridge reject
any theorem that depends on it, every LexLean statement declares `\allowaxioms{Quot.sound;propext}`,
and `scripts/check_no_choice.py` rejects classical constants in the Lean sources. Where the prize
kit's own proofs use choice, the kit is kept unchanged and the results used here are reproved
under the kit's definitions in `Rule30UOR.KitConstructive`.

---

## Primary Deliverables & Release Artifacts

| Artifact | Path | Description |
| :--- | :--- | :--- |
| **`Rule30-Paper.pdf`** (`Paper.pdf`) | [`Rule30-Paper.pdf`](Rule30-Paper.pdf) / [`rule30-paper/Paper.pdf`](rule30-paper/Paper.pdf) | Current LexLean-generated mathematical paper |
| **`Rule30-Core.pdf`** (`Core.pdf`) | [`Rule30-Core.pdf`](Rule30-Core.pdf) / [`rule30-lexlean/Core.pdf`](rule30-lexlean/Core.pdf) | LexLean-generated foundational core (`Core.lex.tex`) |
| **`Rule30-Observations.pdf`** | [`Rule30-Observations.pdf`](Rule30-Observations.pdf) / [`rule30-paper/Observations.pdf`](rule30-paper/Observations.pdf) | Current research statements, including the phase and collision results |
| **`Paper.lex.tex`** | [`rule30-paper/src/Paper.lex.tex`](rule30-paper/src/Paper.lex.tex) | LexLean source document for the main paper |
| **Verified Lean & TeX outputs** | CI artifacts in `dist/`; TeX mirrors in [`rule30-paper/pdf/`](rule30-paper/pdf/) and [`rule30-lexlean/pdf/`](rule30-lexlean/pdf/) | Outputs from the current verification; `verified-latest/` retains historical proof records |
| **PDF provenance** | [`pdf-manifest.json`](pdf-manifest.json) | Source fingerprint, generation time, and PDF/TeX checksums checked by CI |
| **`Rule30Bridge.lean`** | [`rule30-bridge/Rule30Bridge.lean`](rule30-bridge/Rule30Bridge.lean) | Bridge module connecting every LexLean paper theorem directly to `Ruliology.CellularAutomata.Rule30Prize` (`Rule30PrizeKit`) |

---

## Repository Structure

```text
.
├── Rule30-Paper.pdf          # Current compiled LexLean paper PDF
├── Rule30-Core.pdf           # Latest compiled LexLean core PDF
├── Rule30-Observations.pdf   # Current research statements
├── pdf-manifest.json         # Source provenance and checksums for every PDF mirror
├── Makefile                  # Build targets for core, lexlean, pdf, bridge, and release artifacts
├── rule30-lexlean/           # LexLean core specification (src/Core.lex.tex, glossary/, STRATEGY.md)
│   └── verified-latest/      # Attested LexLean output (0c4efc6363c6...)
├── rule30-core-lean/         # Lean 4 host package (Rule30UOR.*; Interfaces is split into Interfaces/PartNN)
├── rule30-paper/             # LexLean paper (src/Paper.lex.tex) & 9 domain glossaries (glossary/r30.*)
│   └── verified-latest/      # Historical attested LexLean output
├── rule30-bridge/            # Bridge package (54 targets) linking Rule30Paper.Paper to Rule30PrizeKit
├── Rule30PrizeKit/           # Wolfram Institute Rule 30 Prize Kit (Lean 4 definitions & equivalents catalog)
├── scripts/                  # Validation gate, packaging and policy checks
├── tools/r30/                # The `r30` command surface and MCP server (see AGENTS.md)
├── experiments/              # Finite diagnostics on the seeded orbit (not proof inputs)
└── .github/workflows/        # Automated GitHub Actions build & release pipeline (release.yml)
```

## Centerline: the current view and the API modules

`rule30-api/` is the LexLean application model of this work and its PrismPM
project model: the `r30` command surface (`src/Api.lex.tex`), the claim
register as data (`src/Register.lex.tex`), the architecture and quality model
on the vendored prism-stdlib (`src/Architecture.lex.tex`), and the stakeholder
view with its publication (`src/Presentation.lex.tex`, `src/Application.lex.tex`),
every one of them generated by `bin/r30 api sync` from the parser, `frontier.toml`
and the model data in `tools/r30/`, verified by `lexlean` like the paper, and
drift-checked by `bin/r30 api check`. **Centerline** is the view they declare:
the reduction tree, the register, the open leaves, the interface sheets, the
modules and the quality measures for the researcher; the paper's statements
with their Lean names, the attested PDFs, the open obligation and the refuted
routes for the mathematician; a picture of Rule 30 and a plain-language guide
for everyone else. The view is a lesson from six vantages: each journey is an
ordered sequence of steps that `Presentation.lex.tex` declares and the kernel
decides to run through the Observer's poles in order (what the vantage is, how
the proof appears from it, what is proved, what is open) and to end in what
the reader can verify, shown one step at a time. It is published at <https://afflom.github.io/rule30/> (GitHub
Pages, deployed by `.github/workflows/view.yml` on every push to `main`) and
kept as the `rule30-current-view` artifact of the same workflow.

```bash
bin/r30 view render --out view     # the view locally: open view/index.html (no server, no dependency)
bin/r30 api check                  # the modules, registers, schemas and features match their sources
bin/r30 api production             # certified Engine/API roots through rule30-api/engine.toml
```

The registers, schemas, Gherkin suites and `CONFORMANCE.md` of the model live
in `rule30-api/model/`, `schemas/`, `features/suites/` and `rule30-api/CONFORMANCE.md`;
`rule30-api/README.md` describes them.

The Engine exports its 15 runtime roots through `rule30-api/engine.toml`, whose
five entry modules select their complete imported dependency closure. This avoids
rebuilding unrelated research-verification fixtures during production export.
The full API manifest remains the acceptance-gate input; production export still
performs preservation checks and artifact replay. Changes to the production profile,
lock, workspace, or compiler invalidate the bundle cache and trigger the Engine.

---

## The engine: the work runs on GitHub Actions

`.github/workflows/engine.yml` runs the proof engine on GitHub's runners, with no
one at the keyboard: every thirty minutes (minutes 17 and 47), on a manual dispatch,
and on every push to `main` that touches its inputs. One run is one **tick**
(`bin/r30 engine tick`): it builds the research library (as the gate's `make core` does:
`LexLeanRuntime.Laws`, which no Lake root covers, then `lake build`), runs **induction**
(`sequences --write` when the evaluation program or the κ-labels of what it reads
changed, then `discover --write`: new relations among the basis sequences become
`observed` claims), **pruning** (`audit --write`), **deduction** (`deduce`: each observed
claim attempted for every time with a fixed portfolio of Lean proof templates, a
proof accepted only when Lean checks it under `propext` and `Quot.sound`, appended to
`Rule30UOR.Deduced`, published and recorded as `proved`; a relation that fails beyond
its window becomes `refuted` by a decided counterexample) and **learning** (integer
strategy weights per relation family, a bounded Hebbian rule decided in
`rule30-api/src/Engine.lex.tex` and run through its certified Rust roots). It then
commits through the unchanged pre-commit gate and pushes only if `main` has not
moved meanwhile (otherwise the next tick redoes the work; never a force push), and
dispatches the view. Nothing in a tick calls a remote or hosted model: the only
models are the LexLean modules compiled into it. When nothing is left to do the tick
ends idle without a commit, and later ticks on the same commit stop after the
checkout, until a developer pushes a new feature (the same holds after a tick the
gate refused, a stage failed on, or whose push the remote rejected while `main` had
not moved: it needs a person, and the job log carries the gate's log). A tick its
budget cut (a rebuild that outlasted its share, attempts left for the next tick)
settles nothing, so the next tick continues on the same commit; a run whose commit
is no longer the tip of `main` stops after the checkout. A relation the library
already proves is recorded `proved` with the existing theorem (outcome `known`),
never proved a second time, whichever strategy the learned weights rank first; and
`library-rewrite` is attempted again on a claim once the library changed (a lemma
pushed since, or a relation the engine proved since). Before caching, `bin/r30 engine
prune --apply` keeps of the gate's evidence only what the next run can use (the
current tools key's Lake builds and replay receipts, the newest LexLean attestation
of each project, the current κ memo, never a certificate), and each cache family
keeps its newest entry. The workflow file is data the
model decides about: `bin/r30 api sync` renders it from `Engine.lex.tex`, and `bin/r30
api check` refuses drift, any secret but `GITHUB_TOKEN`, permissions beyond
`contents: write` and `actions: write`, an action the repository did not already
use, and a pull-request trigger.

```bash
bin/r30 engine status              # the last tick, the network (units, synapses, events), the learned weights
bin/r30 deduce --dry-run           # the attempts the next tick would make, rendered, neither checked nor recorded
bin/r30 engine tick --budget-minutes 30   # one tick locally, without --commit/--push: nothing leaves the tree
bin/r30 engine prune               # what of the gate's evidence a next run can use; --apply deletes the rest (the workflow does)
```

**What only the owner does.** Nothing beyond pushing: the engine runs on
`GITHUB_TOKEN` alone, and the owner's own credentials (an HTTPS token with the
`workflow` scope, or SSH) already push the workflow file. New work reaches the engine
as features pushed to `main` (a new notion in the basis, a template, a library
theorem): the push starts a tick. The kill switch is the repository variable
`R30_ENGINE`: set it to `off` (Settings, Secrets and variables, Actions, Variables)
and no tick runs; delete it or set anything else to resume. GitHub disables a public
repository's scheduled workflows after sixty days without repository activity, and a
disabled workflow runs on no event, pushes included, until it is re-enabled (Actions
tab, Engine, Enable workflow, or `gh workflow enable engine.yml`). A long settled
stretch, when the engine has nothing to do and commits nothing, is when this happens.

---

## Highlights of Verified Results (`v0.1`, through `9.1386`)

1. **The Doubling Law & Unbounded Left-Diagonal Periods (`9.892`–`9.900`, `9.824`):**
   - Settled left diagonal `d` repeats with period dividing $2^d$ (`9.892`, `D_periodic`).
   - For every $e \in \mathbb{N}$, there exists a zero diagonal $z \ge e$ with $\text{DoublesAt}(2^e, z)$ (`9.897`, `9.900`), and for every $m, P > 0$ there exists a zero diagonal $z$ with $\text{DoublesAt}(mP, z)$ (`9.898`).
   - Combined with `9.824`, diagonal $z+1$ flips under shift $2^e$ and therefore has exact minimal period $2^{e+1}$, settling unboundedness of left-diagonal periods in the Lean kernel.
2. **Short Horizon Refutation Engines (`9.905`–`9.924`, `9.1004`–`9.1018`):**
   - **Near a Doubling Zero Diagonal (`9.905`, `9.906`, `9.912`, `9.922`, `9.924`):** At a zero diagonal $z$ at depth $p+1$ with $\text{DoublesAt}(mP, z)$, agreement of column $1$ or $\text{maskparity}(\cdot, 0)$ with its $mP$-shift over a $t$-independent horizon of length $p + 3mP$ refutes `CenterPeriodic T P`.
   - **Dyadic Windows (`9.1004`, `9.1005`, `9.1018`):** When $t + mP = 2^k$, $\text{maskparity}(\cdot, 0)$ agreement over length $2^k$ refutes `CenterPeriodic T P`.
   - **Zero-Diagonal Pairs (`9.1007`, `9.1009`, `9.1011`):** Pairs of zero diagonals separated by $mP - 2$ refute `CenterPeriodic T P` over dyadic windows.
3. **Driven Right-Half (`kit [33]`) Dynamics & Gate-Free Inward Light-Cone Determination (`9.1072`–`9.1266`):**
   - Formalizes the driven right-half evolution `rdrv td tx k p` and proves the **Inward Light-Cone Determination Theorem** (`9.1252`–`9.1261`): single-slice right-half agreement `RhBandAgree t (m * P) 1 B` at time $t \ge T$ under `CenterPeriodic T P` deterministically forces `rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1` and `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for all $s \le B$, yielding single-slice refutations of `CenterPeriodic` (`9.1262`–`9.1264`).
   - Support-width expansion (`9.1357`–`9.1371`): because `rhCenter t q = false` outside the light cone $q > t$, support-width agreement `RhBandAgree t Q 1 (t + Q)` automatically implies `RhBandAgree t Q 1 B` for all $B \in \mathbb{N}$ (`9.1361`).
4. **Universal $2^{tx + c}$-Periodicity & Two-Sided Full-Lattice Embedding Inside the Right Half (`9.1267`–`9.1386`):**
   - **Hypothesis-Free Sub-Diagonal Periodicity (`9.1342`–`9.1356`):** Every sub-diagonal $c$ of `rdrv td tx` is unconditionally $2^{tx + c}$-periodic in $u$:
     $$\text{rdrv}(td, tx, (u + 2^{tx + c}) + c, u + 2^{tx + c}) = \text{rdrv}(td, tx, u + c, u),$$
     and every horizontal row of `rhCenter` satisfies $\text{rhCenter}(t + v \cdot 2^t, v \cdot 2^t + q) = \text{rhCenter}(t, q)$ (`9.1353`).
   - **Full Two-Sided Embedding of `lhCenter` and `rhCenter` Around Dyadic Centers $U = v \cdot 2^{t + C}$ (`9.1372`–`9.1386`):**
     For $1 \le v$, $d \le U = v \cdot 2^{t + C}$, and $j + d \le C$:
     - Right of $U$: $\text{rhCenter}(t + (U + j), U + q) = \text{rhCenter}(t + j, q)$ (`9.1352`).
     - At $U$: $\text{rhCenter}(t + (U + j), U) = \text{center}(t + j)$ (`9.1345`).
     - Left of $U$: $\text{rhCenter}(t + (U + j), U - d) = \text{lhCenter}(t + j, d)$ (`9.1380`), with a left-side white isolation corridor $\text{rhCenter}(t + (U + j), U - d) = \text{false}$ for $t + j < d \le C - j$ (`9.1382`–`9.1385`).

---

## Building from Source

### Prerequisites
- **Python 3.11+** for repository tooling and packaging checks
- **Lean 4** (`leanprover/lean4:v4.32.1` via [`elan`](https://github.com/leanprover/elan))
- **TeX Live** (`pdflatex`) or the `lexlean-tex:latest` Docker image
- **LexLean** (`v0.4+`, optional if building from the pre-verified `verified-latest/` bundles)

### Quick Build
```bash
# 1. Build the 24-module Lean 4 core library
make core

# 2. Build the Wolfram Rule 30 Prize Kit and the 54-target bridge library
make bridge

# 3. Compile the PDFs and package all release artifacts into dist/
make release-artifacts
```

### LexLean-First Authoring Policy

This repository treats LexLean documents as the authoring surface for proof content.

- Source-of-truth proof text lives in `rule30-paper/src/*.lex.tex` and `rule30-lexlean/src/*.lex.tex`.
- Host Lean modules in `rule30-core-lean/Rule30UOR` and bridge Lean in `rule30-bridge` are bridge/derived surfaces used to reuse the Rule30PrizeKit and related Lean ecosystems.
- Generated artifacts (PDFs, `verified-latest`, lockfiles, and `dist`) should be produced from LexLean verification/build steps, not hand-edited.

To enforce this locally, install the repository-managed git hooks:

```bash
make hooks
```

The pre-commit hook first blocks proof-surface host Lean or non-PDF generated artifact edits without
accompanying LexLean source changes, then runs `make check-ci` on a clean snapshot of the
**staged tree**. This includes tooling tests, Lean builds, research audits and kernel replay,
the bridge, both LexLean projects, lockfile reproducibility, and PDF packaging. It then copies
and stages the freshly rendered Core, Paper, and Observations PDFs, their TeX mirrors, and
`pdf-manifest.json` into the same commit. This happens for tooling commits too. Unstaged
source edits are preserved; unstaged edits to generated files block the commit rather than
being overwritten. Unstaged fixes cannot hide a broken staged source.
The pre-push hook and CI check the actual outgoing sources against the PDF manifest and
verified TeX, and check every PDF mirror's checksum. A commit made without hooks that leaves
stale PDFs is rejected. Source fingerprints exclude only these generated outputs, avoiding
a circular dependency between the PDFs and their commit.
Both CI workflows use the same gate. Successful local results are cached under
`.git/rule30-validation`, keyed by the exact tree, validator, and proof tools; failures are
never cached. PR validation invokes the same immutable-tree validator as pre-push,
restoring the Engine's gate-evidence cache and retaining it only after success.
Before upload, the existing pruning procedure removes whole-tree pass markers;
each new run establishes its own acceptance while reusing exact-input project evidence.
Two finer caches under the same key make a typical commit take minutes rather
than twenty: the snapshot starts from the last accepted run's Lake build directories (Lake
rebuilds exactly what its content traces say changed), and a LexLean project whose tracked
inputs (its sources and glossaries, the host Lean its probe elaborates against, the kit, and
the verify script) have the digest of an accepted verification reuses that attestation bundle
instead of verifying again. A failed verification is never cached. The final tree containing the generated PDFs is certified, so a matching push
reuses the successful result without a second proof build.
`make check-research-coverage` provides a quick check that new host modules are included in
the build, axiom audit, and kernel replay.
Compiler maintenance is the narrow exception: a staged `.github/lexlean-revision` change may
accompany lockfile edits that change only `compiler_semantics` fingerprints. Proof edits and
other generated artifacts still require LexLean source changes. Automatically refreshed PDFs
and their TeX mirrors are handled by the validation gate. Deletions are checked too.
For exceptional maintenance-only commits, you can bypass the authoring policy once with:

```bash
ALLOW_NON_LEXLEAN_AUTHORING=1 git commit ...
```

This override still runs the full validation gate. Hooks can be disabled by Git clients;
CI remains the independent remote check.

Install the compiler pinned in `.github/lexlean-revision` locally:

```bash
cargo install --locked --git https://github.com/UOR-Foundation/LexLean.git \
  --rev "$(cat .github/lexlean-revision)" --root "$PWD/.local" lexlean
make check-ci
```

Alternatively set `LEXLEAN_BIN=/absolute/path/to/lexlean` or
`git config rule30.lexlean /absolute/path/to/lexlean` for hooks. The hook rejects compilers
whose semantics do not match the staged locks. `.local/` is ignored. For manual builds:

```bash
make check-ci LEXLEAN=/path/to/lexlean
```

Main CI and releases install the compiler revision in `.github/lexlean-revision`, including
the unbounded `Nat` bitwise extension. `make check-tooling` tests the authoring hook and
packaging rules. `make lexlean` records the successful verification IDs in each project's
ignored `.lexlean/latest-verified.json`; packaging uses those exact bundles. Offline
`--package-only` builds can use a single committed `verified-latest` bundle when no local
verification has been attempted. These historical bundles retain their original proof
records; their old PDF copies have been retired. Rendering requires TeX and always compiles
the selected verified TeX rather than falling back to an existing PDF. Standalone packaging
writes to `dist/`; the pre-commit gate publishes those outputs to all tracked PDF mirrors.

### Automated Releases
Pushing any version tag `v*` (e.g. `v0.1`) triggers [`.github/workflows/release.yml`](.github/workflows/release.yml), which builds `rule30-core-lean`, `Rule30PrizeKit/lean`, and `rule30-bridge`, compiles `Rule30-Paper.pdf` and `Rule30-Core.pdf`, packages the verified LexLean bundles, and attaches all PDFs and LexLean artifacts to the GitHub Release.

The compiler development pin follows LexLean `release/v0.5` through
[the Host interface contribution](https://github.com/UOR-Foundation/LexLean/pull/396)
and [native command execution](https://github.com/UOR-Foundation/LexLean/pull/439).
That source package ports the actual interface from
[LexLean #389](https://github.com/UOR-Foundation/LexLean/pull/389) to v0.5,
including fallible startup paths, timed child waits and byte output. Native Host
step roots can export a generated executable with explicit file/process effects
and child cleanup; pure roots remain libraries.
The API imports `LexLeanStd.Host` from the pinned source package; its local
`Host` module contains only the application harness. The attention catalog
covers all 70 application and library modules. `ResearchRunner` connects the
controller to the local-tool supervisor in `ResearchExecution`: it binds each
job to the outstanding request, drains cancelled host requests, preserves child
ownership on cleanup failure, and requires report review after a successful
process exit. External checked answers are refused: proof jobs use the owned
`ResearchCandidate` lifecycle, which obtains an owned local compiler snapshot before starting the
`ResearchProof` verifier. Maintenance reports must cover the requested sources. Dependency changes invalidate both
active work and remembered evidence.

The `Json` and `VerificationReport` modules decode tool reports with explicit
resource limits, exact tool identities, declaration axiom checks and module
kernel-replay records. The decoder recomputes the attestation content identity;
`ResearchVerification` owns the fixed local verify job, reads its command output
before the matching attestation, and returns a receipt only after decoding it.
Cancellation drains pending reads; unexpected replies halt dispatch with ownership
retained, as do failed process cleanups.
`CompilerSnapshot` reconstructs the full linked IR and exact lexicon closure from
`lexlean snapshot`, checks the compiler and recomputes its semantic identity.
`ResearchCandidate` owns that command and output read, derives the verification
pins, checks the requested contextual goal, and starts verification in the same
isolated project. A snapshot alone is metadata; only the subsequent verifier can
produce proof evidence. Cancellation cannot cross the handoff into verification.
`ResearchProof` then binds the receipt to the candidate's actual native declaration.
`ArtifactIdentity` recomputes the semantic identity from canonical linked IR and
lexicon closure; `CandidateBinding` selects the unique audited theorem and
`CoreBinding` compares its type with the selected source premise, closed over
preceding binders only. Refutation negates the premise inside that context.
Binder names may differ; variables, universes, constants and binder visibility
must agree. The runner retains verifier ownership through cancellation and
blocks dispatch after failed cleanup.
UTF-8 chunk, parser-state and SHA-256 block facts keep the complete report
acceptance proof compositional; lifecycle traces reuse that checked receipt and verify rejection,
cancellation, ownership and terminal behavior.

The tool supervisor reads the monotonic host clock before spawning. Spawn replies
carry a process ID, which is never used as time; spawn latency counts against
the job budget. Normal completion releases direct-child ownership, while failed
cleanup retains it.

`rule30-api/production/research-request.json` exports the research controller,
catalog initializer, candidate source constructor and runner component libraries,
plus the native `ResearchCommand.step` and `ResearchCohortCommand.step` executables.
Session operations remain executable internal components; their behavior is
certified through these command roots without duplicate standalone exports.

`CandidateSource.construct` emits one unverified `.lex.tex` native-core theorem
for the selected goal, with explicit imports, universe parameters and an exact
axiom policy. It uses native LexLean 1.2 notation and a fixed candidate theorem
name; the local compiler checks the proposed term. The output budget includes
the complete document. `ResearchProject` supplies an isolated project and owns
its source writes, fixed manifests, pinned toolchain and locally generated lock.

Closed goals and conditional premises have separate request identities.
For the six open claims with defined propositions, the catalog constructs the
canonical named goal, including the prize kit's `Problem1`; mismatched register
metadata blocks the task without changing its target. A closed proof has no
extra assumptions, and a closed refutation must prove that exact proposition
implies `False`. Dependency changes reopen the same goal for verification.
`ResearchWorkspace` checks out a fresh detached worktree at a full revision,
compares its tree with the requested library snapshot, builds the retained
library, and checks tracked sources again before making the workspace ready.

`ResearchSession` owns one candidate attempt through preparation, snapshot,
verification, evidence retention and release. It captures the exact report
reads consumed by verification. `ResearchRecord` retains the request, source,
project inputs, linked IR, lexicon closure, tool identities and reports.
`ResearchEvidence` stores canonical evidence in Git, retains the library commit
under `refs/r30/libraries/<revision>`, and checks both the library reference and
`refs/r30/evidence/<record-sha256>` before completion. Existing identical references
are idempotent. A record is replay input; reading it grants no proof authority.
A standalone checked answer is delivered only after retention and workspace removal.
Failed archival, failed cleanup, or interrupted tools retain the workspace for
recovery. Direct-child cleanup does not establish that tool descendants have
stopped. Cancellation drains outstanding replies and suppresses checked results.

`ResearchCommand.step` is the native Host entry for one owned attempt. The generated
`rule30_research_command` executable accepts one request file (or `--help`).
`ResearchInput` admits the exact `r30/research-attempt/1` JSON schema: the complete
controller request, repository and full revision, output/error paths, four tool
digests, core arena and proof node, imports, universe levels, axioms, and bounds.
For local constructive synthesis, use `r30/research-synthesis/1` with the same
fields except `arena` and `proof`, which must be omitted. The command derives its
only target from the request and constructs implication introductions, contextual
assumptions, `True`, and reflexive equality locally. Search is bounded to 4,096
input nodes and 64 introductions; unsupported goals return input exit 2 without
marking the research task exhausted. Successful construction still runs the same
owned compiler, kernel replay, axiom audit and evidence-retention lifecycle.
No remote model is involved. Both forms are accepted inside a cohort.

The task must be ready and its prove/refute intent must agree with its purpose.
The snapshot carries the library tree and compiler/model digests. Admission
checks JSON shape and budgets; it grants no premise provenance or proof authority.
The process environment is supplied by the native Host. Paths and environment
values must use printable ASCII for lossless conversion by the current adapter;
log parent directories must already exist. The input parser admits at most 8 MiB;
the underlying Host file read itself is not size-limited.

The command drives the session through actual Host replies and emits
`r30/research-result/1` JSON. Exit 0 means a checked answer with retained evidence
and completed workspace removal; nonzero attempt outcomes carry their status,
and blocked operations include the retained workspace location. Optional evidence
and recovery paths use an empty string when absent, so output remains compatible
with the project's canonical JSON profile. Input errors
exit 2 and host protocol errors exit 70. Receipt injection and restarting a
terminal command are rejected. The command supports this structural strategy but does not schedule the full
research portfolio or publish a claim. Source inspection into the binding schema, strategy scheduling,
durable failure diagnostics, recovery, and publication into the claim register
remain required for the new components to replace the legacy engine.

`ResearchCohortCommand.step` provides the `rule30_research_cohort` executable for
up to 64 sequential attempts sharing one prepared library. Its input is
`{"spec":"r30/research-cohort/1","first":<attempt>,"rest":[<attempt>,...]}`;
each attempt uses the complete schema above. All attempts must share the library,
tool identities, environment, logs and workspace execution bounds, and must have
distinct serials. Each keeps its own candidate request, project directory and
proof evidence. The first request owns the library; subsequent requests borrow
it. Tracked library sources are checked again between attempts without rebuilding.

An ordinary failed candidate permits the next attempt. Interrupted or uncertain
operations stop the cohort and retain its library for recovery. Borrowed sessions
return retained evidence without removing the shared library; the cohort removes
it once all attempts finish. `r30/research-cohort-result/1` reports every completed
attempt separately. A completed cohort can contain failed candidates: exit 0
requires every result to be checked, with no cancellation. This bounded executor
does not schedule an autonomous strategy portfolio or provide durable restart recovery.
CI and runtime use deterministic local tools and no remote models.

The native research cohort now uses the LexLean `ResearchFactory` planner before
starting host operations. It checks all candidate sources before constructing the
shared library and reports rejected attempt serials together. The library is a
shared prerequisite with an exact workspace, snapshot and tool closure; candidate
verification remains separate. Only an owned ready library can be reused, and the
existing cleanliness check still runs between attempts. Factory readiness never
marks a theorem proved. This integration does not cache compiler verification
across runs or implement durable recovery; those capabilities remain incomplete.
