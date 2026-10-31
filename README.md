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
never cached. Two finer caches under the same key make a typical commit take minutes rather
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
