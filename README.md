# Rule 30 — LexLean & Lean 4 Formalization (`v0.1`)

Kernel-checked [LexLean](https://github.com/afflom) and Lean 4 formalization of Wolfram's **Rule 30** cellular automaton (`Rule 30 Prize Problem 1` program) using the UOR Atlas, 2-adic Witt / carry-algebra coordinates, left-diagonal doubling theory, and driven right-half (`kit [33]`) spatio-temporal self-similarity.

Every theorem in [`Paper.pdf`](Rule30-Paper.pdf) (**280 pages**, **1,386 kernel-checked statements** through `9.1386`) and [`Core.pdf`](Rule30-Core.pdf) is verified by the Lean 4 kernel (`leanprover/lean4:v4.32.1`) and `leanchecker` under only the standard Lean axioms (`{propext, Classical.choice, Quot.sound}`), with zero `sorry`s and zero custom axioms.

---

## Primary Deliverables & Release Artifacts

| Artifact | Path | Description |
| :--- | :--- | :--- |
| **`Rule30-Paper.pdf`** (`Paper.pdf`) | [`Rule30-Paper.pdf`](Rule30-Paper.pdf) / [`rule30-paper/Paper.pdf`](rule30-paper/Paper.pdf) | **280-page** LexLean-generated mathematical paper (`9.1`–`9.1386`) |
| **`Rule30-Core.pdf`** (`Core.pdf`) | [`Rule30-Core.pdf`](Rule30-Core.pdf) / [`rule30-lexlean/Core.pdf`](rule30-lexlean/Core.pdf) | LexLean-generated foundational core (`Core.lex.tex`) |
| **`Paper.lex.tex`** | [`rule30-paper/src/Paper.lex.tex`](rule30-paper/src/Paper.lex.tex) | LexLean source document for the main paper |
| **`Paper.lean` & `Paper.tex`** | [`rule30-paper/verified-latest/cf8daedd319c5849f628cc49d6ed7bdee6f940685bb77a31d1db0a86fdc01c9e/modules/Rule30Paper/`](rule30-paper/verified-latest/cf8daedd319c5849f628cc49d6ed7bdee6f940685bb77a31d1db0a86fdc01c9e/modules/Rule30Paper/) | Verified Lean 4 and LaTeX outputs emitted by `lexlean verify` (attestation `cf8daedd319c...`) |
| **`Core.lean` & `Core.tex`** | [`rule30-lexlean/verified-latest/0c4efc6363c642730fbc09cb826a8a9f66ee6a39b11b1c2f3e9b6bc9aeb20a6a/modules/Rule30UOR/`](rule30-lexlean/verified-latest/0c4efc6363c642730fbc09cb826a8a9f66ee6a39b11b1c2f3e9b6bc9aeb20a6a/modules/Rule30UOR/) | Verified Lean 4 and LaTeX outputs for the core module (attestation `0c4efc6363c6...`) |
| **`Rule30Bridge.lean`** | [`rule30-bridge/Rule30Bridge.lean`](rule30-bridge/Rule30Bridge.lean) | Bridge module connecting every LexLean paper theorem directly to `Ruliology.CellularAutomata.Rule30Prize` (`Rule30PrizeKit`) |

---

## Repository Structure

```text
.
├── Rule30-Paper.pdf          # Latest 280-page compiled LexLean paper PDF (9.1–9.1386)
├── Rule30-Core.pdf           # Latest compiled LexLean core PDF
├── Makefile                  # Build targets for core, lexlean, pdf, bridge, and release artifacts
├── rule30-lexlean/           # LexLean core specification (src/Core.lex.tex, glossary/, STRATEGY.md)
│   └── verified-latest/      # Attested LexLean output (0c4efc6363c6...)
├── rule30-core-lean/         # Lean 4 host package (24 modules: Rule30UOR.Core, Kit, Scale, Interfaces, ...)
├── rule30-paper/             # LexLean paper (src/Paper.lex.tex) & 9 domain glossaries (glossary/r30.*)
│   └── verified-latest/      # Attested LexLean output (cf8daedd319c...)
├── rule30-bridge/            # Bridge package (54 targets) linking Rule30Paper.Paper to Rule30PrizeKit
├── Rule30PrizeKit/           # Wolfram Institute Rule 30 Prize Kit (Lean 4 definitions & equivalents catalog)
├── scripts/                  # Release packaging script (build_release.sh) & exploratory measurement scripts
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

If `lexlean` is installed:
```bash
make LEXLEAN=/path/to/lexlean all
```

### Automated Releases
Pushing any version tag `v*` (e.g. `v0.1`) triggers [`.github/workflows/release.yml`](.github/workflows/release.yml), which builds `rule30-core-lean`, `Rule30PrizeKit/lean`, and `rule30-bridge`, compiles `Rule30-Paper.pdf` and `Rule30-Core.pdf`, packages the verified LexLean bundles, and attaches all PDFs and LexLean artifacts to the GitHub Release.
