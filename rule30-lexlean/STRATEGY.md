# Rule 30, Problem 1 — proof strategy

## Target
`Rule30Submission.problem1 : Ruliology.CellularAutomata.Rule30Prize.Problem1`, one module,
axioms within {propext, Classical.choice, Quot.sound}, kit commit named by the verifier.

## Current proof frontier (2026-10-28)
Problem 1 remains open in this repository. The sections below record the development of the
strategy; earlier proposed obligations are not assumptions or established consequences of a
periodic center.

Batch 86 (host Lean, `Rule30UOR.Interfaces`, 9.1582–9.1587) audits the zero-diagonal engines:
four left-band/prefix-tail hypothesis bundles already imply `False` without a center-periodicity
assumption. `engine_input_iff_not_centerPeriodic` and `problem1_iff_engine_input` prove the exact
remaining obligation. Rephrasing these impossible agreement bundles is not a discharge of it.

`cd rule30-core-lean && lake build && lake env lean scripts/AuditVacuous.lean` checks the audit
and writes `.lake/build/vacuity-audit.txt`. The conservative proof-term analysis classifies 26
of 184 refutation theorems as vacuous; the other 158 are **unclassified**, not certified
nonvacuous. The six audit theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
These host additions are not yet included in the attested LexLean paper or release PDFs.

The active question is whether forced temporal disagreements can remain compatible with an
eventually periodic center in the **single-seed** orbit. Work on the exact difference field
must retain the nonlinear cancellation term and both halves' initial conditions. A periodic
external driver alone does not force periodicity of the driven left half: the kit proves the
opposite for finite nonzero left starts. No measured damage speed or density is a premise.

`Rule30UOR.TemporalDefect` implements the exact temporal difference of physical columns.
Its update includes the quadratic difference term; an equivalent linear form uses a
coefficient from the later row, so it does not assert a periodic-coefficient linear system.
For every Boolean sequence `f` and `Q > 0`, `difference_eventuallyPeriodic_iff` proves that
`t ↦ f(t+Q) XOR f(t)` is eventually periodic iff `f` is. Specifically, an `R`-periodic
`Q`-difference integrates to period `2*R*Q` from the same starting time.
Under a hypothetical periodic center, Jen therefore forces every positive-shift difference
on every other column to be aperiodic. `masked_defect_not_eventuallyPeriodic` strengthens
this to the masked right-neighbor signal at every positive multiple of the center period.
This rules out periodic compensation; it does not yet rule out aperiodic compensation.
`make check-research` builds the core, runs both audits, and independently kernel-checks
the research modules. The axiom audit fails on any dependency outside the three allowed axioms.

`Rule30UOR.WittDefect` retains physical alignment in the integer encoding:
`alignedDefect Q t = row (t+Q) XOR (row t << Q)`. It reuses the existing bilinear cross-carry
and proves the exact update `d' = phi d XOR (crossCarry b d << 1)` with
`b = row t << Q`, `b' = phi b`. The autonomous pair starts at
`(1 << Q, row Q XOR (1 << Q))`; `pairOrbit_eq` connects every step to the actual seeded rows.
Bit `j+Q` reads the physical-column defect at `t-j`. In particular, the center is bit `t+Q`.
The persistent nonzero bit zero is at the moving right edge and does not establish a center
disagreement. `problem1_iff_pairOrbit_center` states the exact open target: for each `Q > 0`
and every `T`, some `t >= T` has pair-defect bit `t+Q` equal to one.
This implementation provides an exact system for the non-cancellation question; it does not
prove that the required center witnesses exist. The new modules remain host Lean results,
separate from the release's attested LexLean paper.

`Rule30UOR.Collision` proves finite-horizon carry collisions: incompatible paired colors at
distance `d` force a nonzero adjacent determinant `collision Q t x` between rows `t` and `t+Q`
within an explicit `d`-step rectangle. The two distinct left edges force one every `Q+1`
slices (`left_edge_collision`), but near the moving left edge, not necessarily near the center.

`Rule30UOR.DefectSource` connects the two modules exactly. `defect_source_law` proves
`defect Q (t+1) p = rule (defect Q t (p-1)) (defect Q t p) (defect Q t (p+1)) XOR collision Q t p`:
the temporal defect is an ordinary Rule 30 history except at collision sites, which act as
sources. Under center agreement at `t` the center collision is `center t && defect Q t 1`
(`collision_center_of_agree`), and at `t, t+1` there is no collision at column `-1`
(`collision_neg_one_of_agree`).

Audit result (negative): under center agreement, defect column `-2` is the first difference
of column `-1` (`defect_neg_two_of_agree`), but `left_triple_eq_center_pair` proves
unconditionally that the underlying single-column quantity equals `center t && center (t+1)`.
The center-adjacent layer therefore carries no information beyond the center column. A
contradiction from a periodic center cannot come from columns `-2..1`; it must use deeper
columns, the global edge data, or the collision sources away from the center.

`Rule30UOR.DefectFront` formalizes exact front transport in this sourced defect field.
`defect_front_propagates` gives unconditional rightward transport through clean windows,
`defect_center_of_leftHeavy` turns a left-heavy profile into a forced center disagreement, and
`problem1_of_leftHeavy_recurrence` proves Problem 1 from a recurring left-heavy witness at
period multiples. At any clean site `p`, `defect_succ_of_clean`, `defect_left_front_step`, and
`defect_pinch_step` show that left defects enter with coefficient `1` while right defects are
gated by `!cell t p`. Under a hypothetical periodic center, `rightmost_left_defect_propagates`
uses the clean center column `p = 0` as a one-way barrier so the rightmost left-half defect
propagates deterministically to `-1`, forcing a unit defect pair at `-1` and `1` and a white
center cell (`center_white_and_right_defect_of_rightmost_left`,
`exists_unit_defect_and_white_center_of_left_defect`, `right_shield_of_periodic`). Together with
the unconditional moving-edge defect `left_edge_defect`, this gives
`exists_right_shield_of_periodic` and `exists_unit_defect_and_white_center_of_periodic`, while
`exists_defect_true_of_periodic` and `exists_defect_false_of_periodic` show that every nonzero
column alternates infinitely often between `true` and `false` defects. Earlier intermediate
`Prop` wrappers in `DefectFront` (`ZeroDiagDoubles*`, `PrimitiveDoubles*`, including the
unsatisfiable universal clean-window upgrade `PrimitiveDoublesCleanWindowFromWitness`) were
removed during cleanup so `DefectFront` contains only unconditional transport theorems and
satisfiable consequences of a periodic center.

### Masked observation and exact information bound (2026-10-29)

The standalone LexLean source `rule30-paper/src/Observations.lex.tex` now states the new
observation theorems, with host proofs in `Rule30UOR.MaskedObservation` and vocabulary owned
by the acyclic `r30.observation` package. Both paper entrypoints are verified by the normal
pipeline; the supplement is rendered as `Observations.pdf` during packaging.

`CenterWindowAgree t1 t2 n` means center agreement at offsets `0..n`.
`LeftPrefixAgree t1 t2 n` means row agreement on columns `-1..-n`.
`WhiteTraceAgree t1 t2 n` compares column `-1` at offsets `0..n-1` only where the common
center is white. `prefix_agreement_iff_white_trace` proves the exact equivalence of the latter
two agreements under the first: light-cone determination gives one direction, and black
center times fix column `-1` from the next center value in the other.

`whiteCount t n = W(t,n)` counts the white center times in that window. The compressed
trace is a Boolean list of exactly that length. Under `CenterPeriodic T P`, all samples
`t + a*P` (`t >= T`) use the same mask. `separated_prefix_bound` bounds every separated
family of width-`n` prefixes by `2^W(t,n)`. `compressed_prefix_repeat` therefore produces
`a < b <= 2^W(t,n)` whose left prefixes of width `n` agree. It uses only pigeonhole, not
independence or a halving assumption. Reading the later sample's moving left edge against
the earlier sample gives `edge_information_bound`:

    n < t + P * 2^W(t,n).

This is a proved necessary constraint on a hypothetical periodic center. It does not
exclude periodic words containing white phases: their white counts can grow linearly, so
the exponential upper bound is compatible with the moving edge. No lower complexity
bound, death clock after the available initial bits, or recurrence of a left-heavy profile
has been established. The outstanding step still concerns the actual nonlinear carry
values and their coupling to the seed.
`information_bound_audit` separately proves that `n < (w+1)*P` already implies the
numerical edge inequality, so that inequality alone cannot provide the missing contradiction.

### Central localization of collision sources (2026-10-29)

`Rule30UOR.CentralCollision` adds a seed-specific localization consequence to the same
LexLean supplement. If `defect Q t (-1)` is true and both compared histories have a black
center at `t+r`, then one history has a black ancestor in `[-r,r]` incompatible with the
paired color at `-1`. The finite XOR-rigidity rectangle then forces a collision within
`r+1` steps and radius `2(r+1)` (`unit_defect_forces_near_collision`). These are finite
premises with actual examples; the local theorem does not assume a periodic center.

Under `CenterPeriodic T P`, black centers recur within `P` steps (otherwise the actual
center would be eventually white). For each positive `m`, a unit defect for lag `m*P`
therefore forces a collision within `P` steps in `[-2P,2P]`. The previously proved
recurrence of unit defects gives `periodic_central_collisions`: arbitrarily late sources
in that fixed strip. Finite choice strengthens it to `periodic_recurrent_central_column`:
one fixed column of the strip, distinct from `-1`, has nonzero collision arbitrarily late.
The radius is independent of the time, transient, and period multiplier.

This rules out explaining all collision recurrence solely by sources escaping along the
moving edges. It does not refute a periodic center: the sources are precisely what can
maintain cancellation, and the finite central strip receives inputs from outside. No
periodicity or finite-state closure of its source signal follows. A seed-specific
obstruction to sustaining that central cancellation is still unproved.

## Method: orthogonal facets, joint statements
No facet is reduced to another, and no simple relation between facets is assumed. Each facet owns
its vocabulary (one LexLean glossary package per facet, acyclic imports, one owner per surface,
following PrismPM's facet packages). Statements that need more than one facet live only in the
joint owner, as cross-facet theorems.

| Facet | Package | Owns | Proved content (ours / kit) |
|---|---|---|---|
| local | `r30.local` | the rule as a point of {0,1}^8, its algebra | barrier plane 30 = 90 ⊕ 150 ⊕ 210; left-permutivity; local Bool laws |
| real | `r30.real` | integer order, the left half, its edge, integrality | neighbour maps; order facts; left edge; realization (kit); wedge of eventually periodic left diagonals (measured: period 16 from depth 400 to 8191) |
| 2-adic | `r30.adic` | Φ on Z_2, right diagonals, odometer | right diagonals periodic from time 0 (kit); Mahler valuations grow like log k (measured) |
| time | `r30.time` | evolution, columns, periodicity, the center | `cell`, its unfolding; run laws on `cell` (white run shrinks) |
| meaning | `r30.code` | tails, automata, effort | Myhill–Nerode form of Problem 1; Problem 3 ⇒ Problem 1 (kit) |
| joint | `r30.joint` | cross-facet statements only | center = middle digit of Φ^t(1) (real ∩ 2-adic ∩ time); Jen (real ∩ time ∩ local); Duhamel (local ∩ time) |

Facet consistency with an eventually periodic center (word w), each cell a theorem or a witness:
- time ∧ local: consistent for every w (every column is realizable, kit).
- time ∧ 2-adic (finite right half): consistent for every w (realizable with any right half, kit).
- real ∧ 2-adic (finite on both sides): consistent (finite configurations exist).
- time ∧ real (finite left half): open — the kit's LHC; Q01 is w = 10.
- time ∧ real ∧ 2-adic: open — FinConf; the single seed is a member.
So the proof is a joint statement in time ∧ real (∧ 2-adic); every pair that drops the real facet is
consistent, so the real facet's integrality (the left edge) is indispensable, and it is not
sufficient by itself through any finite or local relaxation (kit barriers).

## Current decomposition (data-led, 2026-10-24)
Measure of perturbation from zero: the set of left-half cells where the rule's nonlinear part fires.
- LAD (Left Activity Dichotomy, conjecture; joint: time ∧ real ∧ local). For a left-permutive rule
  that is not reflection-symmetric, from a single seed: if the center column is eventually periodic,
  the left-half cells where the nonlinear part fires have density zero.
  Data: radius-2 left-permutive degree ≤ 2 family, 328 periodic centers: 310 no late left activity,
  16 thinning like T^-0.41 (dimension ≈ log2 3) or 1/T, 2 reflection-symmetric (density 0.37, center
  constant by symmetry). Random degree ≤ 3 family: 156/156 periodic non-symmetric centers thinning.
  Barrier rules 90, 150, 210: activity identically zero on the seed orbit.
- RLD (real facet alone). Rule 30's left-half activity (c ∧ r = 1) has positive upper density.
  Data: 0.240, 0.246, 0.250, 0.252, 0.250 at T = 300 … 4800. Candidate route: the left periodic
  region (left diagonals settled, period 16 to depth 8191) covers a positive fraction of the left
  half and contains black pairs with positive frequency.
- LAD + RLD ⇒ Problem 1.

## Zero-state decomposition (2026-10-24, supersedes LAD/RLD as the working route)
Coordinates: D_j(t) = cell(t, j - t), the left diagonal at depth j. The rule reads
D_j(t+1) = D_{j-2}(t) ⊕ (D_{j-1}(t) ∨ D_j(t)); depths ≤ J form a closed system (no input from the right).
Two diagonal laws (proved, `Paper::reset`, `Paper::toggle`, from `rule_reset`, `rule_toggle`):
- reset: if D_{j-1}(t) = 1 then D_j(t+1) = ¬D_{j-2}(t); the history of D_j is forgotten.
- toggle: if D_{j-1}(t) = 0 then D_j(t+1) = D_{j-2}(t) ⊕ D_j(t).

**The zero-state (eternal ether) 𝔈.** Let E_j be the eventual periodic pattern of D_j (kit: `D_periodic`).
By reset, E_j is determined by (E_{j-2}, E_{j-1}) whenever E_{j-1} ≠ 0, and then its period divides
theirs. At a zero diagonal (E_{j-1} ≡ 0), toggle makes E_j the running sum of E_{j-2}: the period
doubles iff E_{j-2} has odd weight over its period, and the phase is the only free choice. So 𝔈 is
canonical: generated from E_0 ≡ 1 by the rule, with choices only at zero diagonals. Periods are
powers of two and grow only at zero diagonals. Data (exact simulation to depth 10^5): zero diagonals
2, 7, 28, 399, 53207, 58286, 87866; odd weight (doubling) at 2, 7, 28, 399, 87866, even at 53207,
58286; periods 1, 2, 4, 8, 16, 32 from depths 0, 3, 8, 29, 400, 87867 (matches OEIS A364239). 𝔈 is
the same for every finite seed tested (10 seeds, depth 3000, all diagonals identical): universality.
𝔈 does not cycle in depth to 10^5: on a period-16 cylinder it is rule 30 run sideways, density 0.500,
c∧r activity 0.250.

**Perturbation from zero.** Δ = D ⊕ 𝔈 is the damage between the orbit and the zero-state. Undamaged
depths persist (light cone), so the damage edge e(t) = min{j : Δ_j(t) = 1} is non-decreasing and the
settling time is τ_j = min{t : e(t) > j}. Measured: τ_j = 1.3340 j + O(1) on [10^3, 10^5] (mean
increment 1.3332), i.e. e(t) ≈ 3t/4. This is the left damage speed of rule 30: 0.2496 measured in a
random background, and 1/(1 − 1/4) = 4/3. Same slope for every seed tested. The center (depth t at
time t) is damaged: c(t) ≠ E_t(t) at rate 0.50.

- Front Conjecture (FC; joint time ∧ real ∧ local). Left-permutive radius-r rule, single seed: if the
  center is eventually periodic, the zero-state reaches the center: τ_{rt} ≤ t + o(t).
  Data: radius-2 left-permutive deg ≤ 2 (all 1023) and deg ≤ 3 (550 random): 505 of 505 resolved
  non-symmetric EP centers have front slope ≤ 1.025 (lag ≤ 1.5 in 497, ≤ 19.5 in all); radius 1:
  3/3. The converse fails (7 aperiodic centers lie inside the zero-state, with growing periods).
- Front(30) (real facet, closed system). e(t) ≤ (1 − ε) t for all large t. Data: e(t)/t → 3/4.
- FC + Front(30) ⇒ Problem 1. Both statements hold for every finite seed in the data, so this route
  would also give FinConf.

**Sharper split: the transparency condition.** Readouts of the zero-state: z(j) = E_j(j) (its
center) and S = {j : E_{j-1}(j) = 0} (its transparent times). By reset/toggle at column −1:
the left half is eventually the zero-state ⇔ eventually c(j) = z(j) for every j ∈ S.
(Proof: x_{t+1}(−1) = E_{t−2}(t) ⊕ (E_{t−1}(t) ∨ c(t)) against E_t(t+1) = E_{t−2}(t) ⊕ (E_{t−1}(t) ∨ E_t(t)).)
A wrong center value at a transparent time is exactly where damage enters the left half.
- FC* (cross-rule). EP center ⇒ the left half is eventually the zero-state. Data: in the EP rules
  examined, the damage edge sits exactly at the center (edge − center = 0 at every sampled time).
  Caveat: the EP rules in the data are the degenerate ones (left activity zero or thinning), so the
  data do not yet show a mechanism; FC* has the same evidential base as LAD.
- Z (zero-state only). No eventually periodic sequence agrees with z on S eventually. Data: z on S
  (density of S 0.498) disagrees with the best q-periodic fit in ≥ 45.7% of places for every q ≤ 512.
- FC* fails for finite seeds (2026-10-24): in the radius-2 left-permutive rule
  a + d + bc + bd + cd + de (offsets a=−2 … e=2), the seed 101 has an eventually constant column 1
  while the damage edge sits at depth t (position −t), with sparse regular damage (density 0.02–0.04)
  between it and the column. So FC* is at most a single-seed statement, and the cross-rule evidence
  for it is weaker than it looked. Kept for the record; not the working route.
- FC*(30) ∧ Z ⇒ Problem 1. Z is a statement about the canonical object 𝔈 alone: rule 30 run
  sideways on cylinders of size 2^k, renormalized (k → k+1) at the odd-weight zero diagonals.

## Formal results (Lean 4.35, kit imports only, axioms ⊆ {propext, Classical.choice, Quot.sound})
`rule30-bridge/Rule30ZeroState.lean`
- `Ld_reset`, `Ld_toggle`: the two regimes of a left diagonal, every configuration.
- `agree_after_reset`, `rigid`: eventual agreement propagates past a recurrent diagonal.
- `universal`: two configurations, each white left of a black cell, agree eventually on every left
  diagonal up to the first eventually white one (the zero-state is fixed by the rule).
- `zero_diag_xor_const`: one bit of freedom per zero diagonal. `toggle_shift`: period doubling.
- `agree_persists`: the damage edge never moves back. `entry_iff`: damage enters only at
  transparent times.
- Kernel certificate to depth 401: `D_eq_pat` (period-16 table from t = 501), `zero_diagonals`
  (2, 7, 28, 399), `antiperiods` (3, 8, 29, 400: periods exactly 2, 4, 8, 16), `period_eight_below`.
`rule30-bridge/Rule30ZeroStateDeep.lean` (kernel run of the closed left system, 117,357 steps,
checkpoints every 15,000; compiles in 14 s, peak 1.7 GB)
- `periodic_32` (all depths ≤ 87,868 from T0 = 117,325), `periodic_16_below` (depths ≤ 87,866),
  `antiperiod_87867` (record: period exactly 32), `zero_diagonals_87866`
  (2, 7, 28, 399, 53207, 58286, 87866). These are the OEIS A364239 records through 87,868, now
  kernel-checked, with the mechanism (odd-weight zero diagonal) visible in the statements.

## Pipeline
LexLean core (`rule30-lexlean`) → verified Lean + runtime as a library (`rule30-core-lean`) →
LexLean paper with facet glossaries (`rule30-paper`) → integration with the kit
(`rule30-bridge`: `rule_eq_kit`, `cell_eq_kit`, `center_eq_kit`, `white_run_shrinks_kit`) →
single-module submission. Version matters are deferred until the mathematics is in place.

## Honesty
The joint theorem is open. No headline `problem1` is claimed until it is a kernel-checked theorem.

## UOR-Framework invariants applied (2026-10-24)
Source: github.com/UOR-Foundation/uor-framework (ring Z/2^n, involutions neg and bnot, critical identity
succ = neg ∘ bnot, dihedral group, carry/Witt algebra, Ostrowski–Archimedean bridge).
- Additive invariants: none beyond the trivial ones for rule 30, forward windows ≤ 8, sideways
  windows ≤ 4, over Q and F2 (`conserve.py`, `sideconserve.py`).
- Involutions on the orbit: on the seed's orbit closure Φ is conjugate to succ via h(t) = Φ^t(1)
  (kit, odometer). By the critical identity Φ = (h neg h⁻¹) ∘ (h bnot h⁻¹) there: two involutions,
  y_t ↦ y_{−t} and y_t ↦ y_{−1−t}. The backward orbit Φ^{−t}(1) is rational in Z_2 (eventually periodic
  digits: −1, …100100, …011011, …). Bit t of y_{−t} agrees with c(t) at rate 0.52 (no relation).
- Ostrowski balance: digit t of the (2t+1)-digit y_t has Archimedean weight 2^t / 2^{2t} = 2^{−t}
  relative to y_t and 2-adic weight |2^t|_2 = 2^{−t}. The center is the digit where the product
  formula balances; statement 1 (top factor) and the odometer (bottom factor) meet there.
- Mirror and complement: digit reversal maps rule 30 to 86 (swapping the left zero-state and the
  odometer, fixing the center); complement maps 30 to 135 (Nersissian: translated complement).
- Carry tower (diagonal readout bit t of F^t(1), t < 4000): x ⊕ 2x ⊕ 4x (no carry, rule 150)
  constant 1; x ⊕ (2x ∨ 4x) (rule 30: carry kept in place), x ⊕ (2x + 4x), 7x, 3x: no eventual
  period. Rule 30's nonlinear term is exactly the first Witt carry a·b left in its own digit.

## Intent register and all-depth theorems (2026-10-25)
- `Rule30Intent.gate : ObFront → ObZero → Problem1` (kernel-checked; LexLean `gate-theorem`).
  ObFront: a periodic center forces the left half to be the zero-state. ObZero: no eventually
  periodic sequence matches the zero-state's center at all large transparent times. ObZero is
  equivalent to: the zero-state's left half cannot be driven by an eventually periodic boundary.
- `Rule30ZeroStateOrbit`: the zero-state is a rule-30 orbit with a left edge (`evol_ezero`), so the
  kit's Jen family holds for it (`zero_no_constant_column`, `zero_jen`, `zero_masked_jen`).
  ObZero's constant cases are the zero-boundary (u = 0) and all-black-boundary (u = 1) problems
  for the zero-state, the same family as the kit's open Q01.
- `Rule30ZeroDiagonals` (reversibility of the depth step, `E_back`, `bwd_det`, `fwd_det`,
  `period_prop`):
  - `infinitely_many_zero_diagonals`: zero diagonals at unbounded depth (LexLean `recompile-points`).
  - `unbounded_periods`: no common period for all left diagonals (LexLean `unbounded-periods`).
    Proof: a common period makes a consecutive pair repeat; backward determinism carries it to the
    edge pair (black, black), which then recurs at some depth d ≥ 1; two black diagonals force
    every diagonal below them white, against the black edge. Self-contained; Nersissian 2026
    states unbounded periods, this is a kernel-checked proof of it for rule 30's left diagonals.
- Measured, no structure: depth-direction window invariants (w ≤ 8: closures are everything);
  zero-state self-similarity under depth/phase scalings (agreement 0.497–0.503); center lag-2^k
  agreement 0.4994–0.5008 (|z| ≤ 1.7, k ≤ 16).
- Census (radius-2 left-permutive, finite seeds): chaotic rules show only period-1 columns
  (1245/1245, all in quiescent pockets or outside the cone); non-chaotic rules show periods
  1, 2, 4, 8, 256.
- Correction: right-diagonal least periods are A094605 (1,2,2,4,8,8,16,32,32,64×6,128,256×8,…),
  not 2^k; the center reads right diagonal t in its first period iff that period exceeds t
  (true for 3 ≤ t ≤ 30; proved bound only > t/2).

## Compile points and the vacuum tree (2026-10-25, continued)
- `Rule30CompilePoints` (4.35, kit imports; host copy `Rule30UOR.CompilePoints` on 4.32.1;
  LexLean section `compile-points`, attestation a0147063…; axioms propext, Classical.choice,
  Quot.sound):
  - `black_after_zero`, `zero_before_black`: black diagonals past depth 1 are exactly the zero
    diagonals shifted by 2. `no_adjacent_zero`: zero diagonals are isolated.
    `twin_before_zero`: E(z-2) = E(z-1) before a zero diagonal z. `accumulate_after_zero`.
  - `period_passes`, `period_at_most_doubles`: the common period passes behind nonzero diagonals
    and at most doubles behind a zero diagonal.
  - `doubling_point`: for every P > 0 a zero diagonal z has all diagonals ≤ z P-periodic and
    diagonal z+1 not. The common period changes only at zero diagonals, infinitely often.
  - `compile_bit`: if τ (≥ settle z) is the last black cell of real diagonal z+1, then real
    diagonal z+2 equals the zero-state from τ+1 on and E(z+2)(τ+1) = ¬E z τ. The single bit the
    depth step leaves free at a zero diagonal is the phase of the last black cell τ.
- Measured compile points (real orbit, `taus.py`): zero diagonals 2, 7, 28, 399, 53207, 58286,
  87866 (doubling at 2, 7, 28, 399, 87866; 53207 and 58286 keep period 16); last black cells
  τ = 1, none, 30, 500, 71115, 77909, 117323; τ/z → 4/3 (1.3366, 1.3367, 1.3352). The compile
  moment is when the damage front (slope 4/3) crosses the zero diagonal.
- Vacuum tree (`vt.c`, `vactree.py`). In C-world (diagonals of period dividing C) the backward
  depth map B(x, y) = (y(·+1) ⊕ (x ∨ y), x) is total; its fixed point (0, 0) is the white region
  left of the edge, and B(1,1) = (0,1), B(0,1) = (0,0). The zero-state is a forward path out of the
  vacuum in the tree of B-preimages; branch nodes are (a, 0) with a of even C-weight (two
  children: the compile bit), leaves are (a, 0) with odd C-weight (the path continues in
  2C-world). `unbounded_periods` = "the C-tree is finite, the path is infinite".
  Basin sizes and heights: C=1: 4, 3; C=2: 14, 8; C=4: 98, 29; C=8: 3066, 400;
  C=16: 34,541,082, 894,235. The zero-state leaves C-world at depth 3, 8, 29, 400, 87867: the tree
  height for C ≤ 8, but not for C = 16. At the two period-16 branch nodes the real orbit takes the
  shallower child (subtree heights 176129 vs 841026 at 53207; 29579 vs 171050 at 58286; the
  58286 subtree is a bare path ending exactly at the leaf 87867). The compile bits are external
  information supplied by the damage front, not a extremal rule of the tree.
- Information channel. The frozen left region (settled diagonals, p ≲ −t/4) is the vacuum-tree
  path, fixed by one compile bit per zero diagonal (7 bits by depth 10^5). The center reaches the
  frozen region only through those bits. So the left zero-state carries almost no information
  about the center, and the measured front slope 4/3 > 1 makes ObFront's conclusion false for the
  real orbit: ObFront is equivalent to Problem 1 once the front is proved to lag the center.
  The gate is bookkeeping; the content sits in the damage band −t/4 ≲ p ≤ 0 and the right half.
- Right system (kit `Rule30RightPeriods`): every right diagonal is periodic from time 0, center =
  R t t, anchored running sums R(j+2)(t+1) = R(j+2)(t) ⊕ (R(j+1) t ∨ R j t), R j 0 = 0: a canonical
  depth orbit with no free bits. Its periods (2^{e_j}, e_j ≈ 0.4 j) exceed j, so the center is read
  inside the first period of its right diagonal; left periods are tiny (≤ 32 to depth 10^5) but the
  center sits in the left damage band. Both per-diagonal periodicities are silent at the center.

## The 2-adic phase of the frozen left structure (2026-10-25)
- `Rule30Phase.phase_universal` (4.35, kit imports; axioms propext, Quot.sound): every
  configuration white left of a black cell (any start, any right half, so any driver of the left
  half) agrees eventually, on every consecutive pair of left diagonals of depth ≤ 401, with the
  single seed's pair shifted in time by one offset a < pb(n+1) ∈ {1,2,4,8,16}. The offset changes
  only at the doubling zero diagonals 2, 7, 28, 399, by 0 or the half period 1, 2, 4, 8
  (`rot_zero`); elsewhere it propagates unchanged (`rot_rigid`). So the frozen left structure is
  one universal object Ξ read at a phase whose binary digits are fixed one per doubling compile
  point. "Later acts on earlier": digit k is set at τ ≈ 4z_k/3 and rotates the whole epoch k.
- Measured (`drivenfront.py`, `phase.py`): drivers real, 0, 1, alternating, periods 3, 4, 5, 7,
  and random finite starts with drivers 0, 1, alternating all give the reference structure up to
  a phase through depth 2000, the same zero diagonals {2, 7, 28, 399}, and the same front: settle
  lag ≈ j/3 (e.g. 503–563 at j = 1800). A periodic center changes neither the frozen left
  structure (beyond the phase) nor the front speed. The left side sees the center only through
  the phase digits α ∈ Z_2; under an eventually periodic center the phase of the system restarted
  at time T is T, the same as for the real center. The left side gives no lever; the content is
  in the right system and the band.

## Later acts on earlier: the left-only obligation (2026-10-25)
- `Rule30LeftMask.problem1_of_leftMask : LeftMask → Problem1` (4.35, kit imports). At a black
  center time, column −1 is fixed by the next center value (`left_of_black`); the real left half
  is the half driven by the center (`cell_eq_L`). `LeftMask`: no finite nonzero start and no
  eventually periodic driver black infinitely often make column −1 of the driven left half equal
  ¬c(t+1) at every late black time of c. No right-half data enters.
- `LeftMask` is the uniform form of the kit's per-word conditions: period 2 is `Q01` (open in the
  kit), periods 3 and 4 are `C3w`, `C3`. The constant-1 case is the kit's
  `col_neg_one_not_periodic`.
- Measured (`maskleft.py`, 12000 steps, seed start): for all 98 primitive periodic words of period
  ≤ 6, column −1 of the driven left half is not eventually periodic on any residue class where the
  driver is black; the mask condition fails for every word.
- `LeftMask` is the catalog's **LHC** (equivalents/CATALOG.md: "for every primitive word w, no
  finite driven left half is consistent with w^∞"; LHC ⟹ NumberLike ⟹ FinConf ⟹ Problem 1;
  open; searches to width ≈ 36 found no survivors; Q01 kernel-checked to width 52).
  `problem1_of_leftMask` is a direct one-step proof of LHC ⟹ Problem 1 from `cell_eq_L` and
  `left_of_black`.
- Transport reading (from "Transport-Optimal Inference", Theorem 1): a start of width W carries
  W − 1 free bits (the barrier bijection), and each black driver time consumes one bit. Measured
  death clock (`lhcclock.c`, every start of width W ≤ 22, every phase, mask from time 0): the latest
  first violation is ≈ W/ρ, ρ = black density of the word: 10: 41 at W = 22 (ρ = 1/2); 110: 33
  (2/3); 1110: 29 (3/4); 11010: 37 (3/5); 10100: 49 (2/5); 1100: 42 (1/2); 100: 87 (1/3); 1000: 75
  (1/4). Survival time ≤ capacity ÷ constraint rate, up to a bounded excess. LHC(w) is exactly
  "every finite start dies"; a proved clock of any form, uniform in W or not, proves LHC(w).
- Survivor counts (`lhccount.c`, word 10, starts of width exactly 22, phase 0): exact halving at
  every black step to t = 20 (barrier bijection), then 509, 249, 113, 61, 38, 21, 6, 6, 6, 0 at
  t = 22, 24, …, 40. Past the free bits the pinned bit is not balanced on the survivors: no
  halving lemma holds. (Correction: an earlier reply said these counts were recorded here before
  they were.)

## Exactness audit (2026-10-25)
Rule from here on: an obligation enters the intent register only with its exact logical
relation to Problem 1 stated and proved; measurements are never premises.
- Exact equivalents (proved or definitional): Problem1 ⟺ ¬EP(lcenter) (`problem1_iff_lcenter`);
  center = R t t with R the anchored right system (kit `center_eq_R`, `R_eq_parity`); Problem1 ⟺
  for every primitive word w and every T, the center is not w^∞ from T.
- Implied by Problem 1, carrying all its content: ObFront (vacuous under Problem 1; its
  conclusion contradicts the measured front, so it cannot be discharged without Problem 1).
- Strictly stronger than needed (they drop data the seed supplies): LHC/LeftMask (drops the right
  half), FinConf/CQ01 (replace the seed by any finite row), ObZero (drops the right-half
  coupling at white times). Proving one of them would prove Problem 1, but each discards the
  seed-specific structure.
- Measurements, not premises: front slope 4/3, death clock W/ρ, survivor counts, vacuum-tree
  heights, phase digits beyond depth 401, driver-independence of the front.
- Seed-specific exact structure available: right diagonals periodic from time 0 with R_j(0) = 0
  (kit), doubling rule e_{j+1} = e_j + R_{j+1}(2^{e_j}) and rows at powers of two (kit), the left
  zero-state with phase 0 and its compile points (`Rule30CompilePoints`, `Rule30Phase`), the
  identity D_j(t) = R_{2t−j}(t) joining the two systems.

## Form and function in LexLean: the right system (2026-10-25)
- LexLean core (`src/Core.lex.tex`, attestation eb887c9a…): `rdiag` defined by its anchored law
  (rdiag j 0 = [j = 0]; rdiag 0 ≡ true; rdiag 1 (s+1) = ¬rdiag 1 s;
  rdiag (k+2) (s+1) = bxor (rdiag (k+2) s) (rdiag (k+1) s ∨ rdiag k s)), `rcenter t = rdiag t t`,
  laws `rdiag_step`, `rdiag_zero`, `rdiag_one` by reflexivity.
- Host `Rule30UOR.Right` (4.32.1): `rdiag_eq_R` (the LexLean form is the kit's right array),
  `center_eq_rcenter`, `col1_readout` (column 1 at t+1 is rdiag t (t+1)), `rdiag_periodic`.
  Intent: `CenterPer T P`, `MaskedPer T P`, `MaskPos := ∀ T P, 0 < P → CenterPer T P →
  MaskedPer T P`; `problem1_iff_maskPos` (masked Jen one way, vacuous the other).
- Paper section "The right system" (attestation b2b558bc…): right-law, right-periods,
  mask-form, mask-sufficient (MaskPos → Problem 1), mask-necessary (Problem 1 → MaskPos).
- The intent register now holds one obligation, exactly equivalent to Problem 1, stated on the
  LexLean-defined right system with nothing of the seed dropped: derive MaskedPer T P from
  CenterPer T P using the right system's laws.
- Symmetric form (`Rule30UOR.Right`): `colm1_readout` (column −1 at t is rdiag (t+1) t),
  `LeftPer`, `LeftPos := ∀ T P, 0 < P → CenterPer T P → LeftPer T P`, `problem1_iff_leftPos`
  (Jen's adjacent-column theorem one way, vacuous the other). The three readouts rdiag (t−1) t,
  rdiag t t, rdiag (t+1) t are columns 1, 0, −1.
- Fixed point (`Rule30UOR.Fixed`; paper theorems center-reproduces, fixed-sufficient,
  fixed-necessary, attestation 168e1c1c…): `Lh c`, `Rh c` are the two halves run from the seed's
  white halves, fed at 0 by a column c; Φ c (t) = rule (Lh c t (−1)) (c t) (Rh c t 1).
  `center_fixed`: the center reproduces itself; `fixed_unique`: it is the only fixed point with
  c 0 = true; `problem1_iff_no_periodic_fixed`. Structure of the form: the left half receives c
  through OR (c t ∨ ·), the right half through XOR (c t ⊕ ·). An eventually periodic fixed point
  needs, at black times of c, Lh c t (−1) = ¬c (t+1) (the left condition), and at white times
  Lh c t (−1) ⊕ Rh c t 1 = c (t+1) (the coupling); neither half alone is the obligation.
- Module reuse (2026-10-25): every proved repetition is reuse of a module along a light-like
  direction: right diagonals (2^k, +2^k), restart (`row_restart`, `center_restart`), left
  zero-state Ξ (C, −C) (`phase_universal`). Measured: the center does not reuse its own prefix
  vertically (c(2^k + s) = c(s) holds for at most s ≤ 5, k = 4..19). Correction to the reply of
  08:22: two light-like reuses composing to a vertical one is only a sufficient mechanism for a
  periodic center, so "the overlap never contains the center" is implied by Problem 1, not
  equivalent to it. It does not enter the register. The equivalent reuse statement is the fixed
  point: Problem 1 ⟺ no eventually periodic column (a reused module) is reproduced by Φ, the
  two driven halves (each reusing the rule module) recombined at position 0.

## Projection onto the known rules (2026-10-25)
- LexLean core (attestation 77dca5b9…): `rule60`, `rule15`; `split150`, `split90`, `split60`,
  `split15` (rule 30 = neighbour ⊕ one carry; carries b∧c, b∧¬c, ¬b∧c, ¬b∧¬c);
  `carries_cover`, `carries_orthogonal` (the four carries are the four minterms of (b, c));
  `aff`, `miss`, `dist30`; `deep_hole` (rule 30 is at Hamming distance ≥ 2 from every affine
  rule, i.e. at the covering radius of RM(1,3), the affine code that is E8 mod 2 under
  Construction A); `nearest_affine` (distance exactly 2 from rules 150, 90, 60, 15).
- Host `Rule30UOR.Project` (4.32.1): Duhamel accumulators defined by their laws,
  acc (t+1) = L_k (acc t) ⊕ q_k t; `cell_eq_proj60` (cell = rule-60 evolution of the seed ⊕
  acc60), `lin60_center` (rule 60's center is always black), `problem1_iff_resp60`;
  `cell_eq_proj15`, `lin15_gen`, `lin15_center`, `problem1_iff_resp15`; `resp_relation`
  (for t ≥ 1, resp60 ⊕ resp15 = [t even]).
- Paper section "Projection onto known rules" (attestation f6729ac0…): the four splits,
  deep-hole, center-response (center = ¬resp60), orthogonal-responses, and both directions of
  Problem 1 ⟺ resp60 aperiodic and Problem 1 ⟺ resp15 aperiodic.

## The dyadic scale (2026-10-25): steps 1–3 verified, step 4 open
- LexLean core (attestation 63a26b01…): `carry60 s p = ¬cell s p ∧ cell s (p+1)`,
  `window60 t0 n p` (rule-60 accumulation of the carries over [t0, t0+n), by its law), `twopow`;
  laws `window60_step`, `twopow_succ` by reflexivity. Function-typed parameters are not
  admitted in the semantic module, so the kernel operator L and its powers live in the host.
- Host `Rule30UOR.Scale` (4.32.1): `cell_eq_kit` (the core's cell is the kit's); step 1
  `freshman`: L^(2^k) x p = x p ⊕ x (p − 2^k); step 2 `duhamel`, `scale`, `scale_center`:
  center (t + 2^k) = center t ⊕ cell t (−2^k) ⊕ window60 t (2^k) 0; step 3 `periodic_scale`,
  `periodic_scale_cone`: under CenterPeriodic T P, for T ≤ t < 2^k,
  window60 t (2^k) 0 = center (t + 2^k mod P) ⊕ center t. Split `window_split`:
  window60 t n 0 = leftwin t n 0 ⊕ maskcount t n (carries at positions ≥ 1 never reach 0; the
  position-0 carries ¬c(s) ∧ cell s 1 enter with coefficient 1 at every step), hence
  `periodic_mask`: the masked column-1 parity over each dyadic window inside the cone is fixed by
  the left response and the center's phase. `problem1_iff` (Problem 1 ⟺ ∀ T P>0, ¬CenterPeriodic).
- Paper section "The dyadic scale" (attestation abcd487a…): window-law, scale-doubles,
  scale-identity, periodic-scale, periodic-scale-cone, response-split, periodic-mask,
  noperiod-sufficient/necessary.
- Step 4, checked exactly: every identity derivable from the rule-60 linear structure together
  with the periodicity hypothesis is tautological relative to that hypothesis (the dyadic
  recursions of the window response, of the left response, and of the masked parity all reduce
  to the scale identity at the shifted position and to c(t + 2^k) = c(t + 2^k mod P)). The
  closing argument must use the values of the carry field; the exact facts in hand about it
  (edge carry q(s, −s−1) = 1, Jen, masked Jen, periodic_window, phase universality, unbounded
  periods, compile bits) do not combine with the scale constraint into a contradiction by any
  derivation found. The register is unchanged: one obligation, Problem 1, in its exact forms.

## Rule 30 in the Atlas frame; Problem 1 as irrationality (2026-10-25)
- LexLean core (attestation c3034014…): `displacement a b c = rule ⊕ rule150`,
  `displacement_is_carry` (= b ∧ c), `frame_direction` (the displacement does not change when the
  left input flips), `affine_left_linear` (rule 150 complements when the left input flips),
  `nearest_exactly` (dist30 = 2 only at rules 150, 90, 60, 15); `ldrem`, `lddig` (base-two long
  division of r / b by its law). E8 reading: weight-2 vectors of F2^8 lift to D8 roots
  ±e_i ± e_j; the four carries are supported on the pairs {x, x ⊕ e_left}, four disjoint pairs:
  an orthogonal frame of four roots whose direction is the left input. Left-permutivity is the
  statement that the displacement is constant along that direction.
- Host `Rule30UOR.Rational`: `periodic_digits` (digits of r / b repeat; pigeonhole on the
  remainders), `win_shift` and `digits_of_periodic` (a tail of period P from T is the expansion of
  V / (2^P − 1), from 2 V_t = c(T+t)(2^P − 1) + V_{t+1}; the white case uses that 2^P − 1 is
  odd), `problem1_iff_irrational`: Problem 1 ⟺ no tail of the center is the binary expansion of a
  rational number (x₃₀ irrational). Axioms propext, Classical.choice, Quot.sound.
- Paper (attestation 4d2b1361…): displacement-carry, frame-direction, affine-left-linear,
  irrational-sufficient, irrational-necessary.
- Register: one obligation, Problem 1, now also in the form "x₃₀ is irrational". The hypothesis
  that x₃₀ (or the 2-adic orbit Φ^t(1) it is read from) is an Atlas function of an Atlas constant
  is the open meaning-layer identification; no such identity is established.
- Frame projection (core attestation cfef201c…, paper attestation 337b4e7f…):
  `frame_projection`: 2·sgn(rule 30) = sgn(rule 150) + sgn(rule 90) + sgn(rule 60) + sgn(rule 15)
  at every input (sgn b = −1 for black, +1 for white); `one_dissent` (core): exactly one of the
  four neighbours disagrees with rule 30 at each input, so rule 30 is their majority. In sign
  variables this is rule 30's Walsh expansion: σ' = ½ σ_l (σ_c σ_r + σ_c + σ_r − 1); the four
  characters are the four nearest affine rules, each with coefficient ±½. In the Atlas's
  coordinates (half-integer roots = even-weight points of the 8-cube) the even affine rules give
  pairwise orthogonal root classes (Hamming weight-4 words are at distance 4 or 8, inner product
  2 − d/2 ∈ {0, −2}), and rule 30's root is half the sum of its four nearest affine roots.
  `frame_orthogonal` (core attestation 247406d5…): the sign vectors of two affine rules with
  different linear parts have correlation 0 over the eight inputs: the affine rules form an
  orthogonal frame, and rule 30 is its half-sum over the four nearest members.

## Witt forms on unbounded Nat and linear interfaces (2026-10-25, LexLean #317)
- LexLean compiler & runtime (`lexlean-v04`, Issue #317): Language 1.2 bitwise primitives
  (`BitAnd`, `BitOr`, `BitXor`, `ShiftLeft`, `ShiftRight`) extended to unbounded `Nat` in semantic
  modules (`Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`), refused by the
  production backend (`Nat` is not a fixed-width machine word), with eight kernel-verified runtime
  laws (`nat_bit_and`, `nat_bit_or`, `nat_bit_xor`, `nat_bit_shift_right`, `nat_bit_shift_left`,
  `nat_or_xor_and`, `nat_witt_step`, `nat_bit_ext`) in `LexLeanLaws`.
- LexLean core (`src/Core.lex.tex`, attestation 0c4efc63…): `phi`, `carry`, `phiLinear`,
  `phi_split` (`phi y = phiLinear y ⊕ (carry y ≪ 1)`), `or_witt_split` (`(a | b) = (a ⊕ b) ⊕ (a & b)`),
  `bit` (`(n ≫ k) mod 2`), `bit_and_law`, `bit_or_law`, `bit_xor_law`, `bit_shift_right_law`,
  `bit_shift_left_law`, `row` (`row 0 = 1`, `row (t+1) = phi (row t)`), `rowCenter` (`bit (row t) t`),
  `row_center_prefix` (`1, 1, 0, 1`), `phiLinearPow`, `phiLinearPow_step`, `phiScale`
  (`y ⊕ (y ≪ 2^k) ⊕ (y ≪ 2^{k+1})`), `winWitt`, `winWitt_step`, `wittResponse`.
- Host `Rule30UOR.Interfaces` (4.32.1): reuses `Core.phi`, `Core.carry`, `Core.phiLinear`,
  `Core.phi_split`, `Core.phiLinearPow`, `Core.phiScale`, `Core.winWitt`; proves the `Φ₃`
  cyclotomic interface over `F₄` (`val_phi : val (phi y) = ω · val (carry y)`, `valA_phi`,
  `valB_phi`, `valB_phi_bxor`) and the `1 + x` parity interface (`par_phi`, `par_phi_bxor`);
  bridges the Witt integer orbit `row t` to the right-diagonal system and center column
  (`row_testBit : (row t).testBit j = rdiag j t`, `bit_row_bton`, `rowCenter_bton`,
  `rowCenter_eq_center`, `rdiag_left_edge`, `rdiag_gt_two_mul`, `carry_row_testBit_succ`); and
  establishes the exact intent-register equivalence `problem1_iff_noRowCenterPeriod`
  (`Problem1 ⟺ NoRowCenterPeriod`).
- **The Two-Place Witt Scale & Dyadic Coboundary (`Rule30UOR.Interfaces`):**
  - **Freshman & Duhamel on `Nat` (`phiLinear_freshman`, `row_duhamel`, `row_scale`):**
    `phiLinearPow (2^k) y = phiScale k y` and `row (t0 + 2^k) = phiScale k (row t0) ⊕ winWitt t0 (2^k)`.
  - **Cone Duality (`center_witt_scale_cone`, `wittRespBool_eq_response_cone`):**
    Inside the dyadic cone (`t < 2^k`), both wings of `Φ₃(x)^(2^k)` lie outside the light cone of
    `row t`, so the symmetric Rule-150 carry response `wittRespBool t k` and the one-sided Rule-60
    carry response `response t k` coincide identically at the center (`wittRespBool t k = response t k`).
  - **Outside-the-Cone Duality & Late Readout of Early Center (`wittRespBool_xor_response_ge`, `center_from_late_responses`):**
    For `t ≥ 2^k`, `wittRespBool t k ⊕ response t k = rdiag (t - 2^k) t`. At `t = d + 2^k` with
    `d ≤ k`, 2-adic periodicity `2^d ∣ 2^k` from time `0` gives the right wing
    `rdiag d (d + 2^k) = rdiag d d = center d`, so `center d = wittRespBool (d + 2^k) k ⊕ response (d + 2^k) k`.
  - **The Two-Place Identity (`two_places_witt_scale`, `ldiag_settled_eq_zcenter`, `two_places_settled`, `zcenter_from_late_scale`):**
    At `t = d + 2^k` (`d ≤ k`), the left wing of `Φ₃(x)^(2^k)` reads the Archimedean left diagonal
    `ldiag d (d + 2^k)` while the right wing reads the 2-adic right diagonal `center d = rdiag d d`:
    `center d ⊕ ldiag d (d + 2^k) = center (d + 2^{k+1}) ⊕ center (d + 2^k) ⊕ wittRespBool (d + 2^k) k`.
    Crucially, because `ldiag d` is read at late time `d + 2^k`, for every `d` and every `k ≥ d`
    with `settle d ≤ d + 2^k` (holding for all sufficiently large `k` at every depth `d`, even inside
    the damage band where `settle d > d`), `ldiag d (d + 2^k) = E d (d + 2^k) = E d d = zcenter d`.
    Hence `zcenter d` and the center damage `center d ⊕ zcenter d` are read directly from the late
    scale increments at `d + 2^k`.
  - **Dyadic Coboundary & Exact `maskparity` Cancellation (`ldiag_eq_response_coboundary`, `two_places_eq_witt_coboundary`, `maskparity_coboundary`, `ldiag_eq_leftresponse_coboundary`, `zcenter_eq_leftresponse_coboundary`):**
    Across the dyadic triangle `d → d + 2^k → d + 2^{k+1}` (`d ≤ k`), `d` lies inside both the `2^k`-
    and `2^{k+1}`-cones while `d + 2^k` crosses the `2^k`-cone. The Rule-60 coboundary defect
    `response d (k+1) ⊕ response d k ⊕ response (d + 2^k) k` equals `ldiag d (d + 2^k)` (`= zcenter d`),
    and the Witt coboundary defect `wittRespBool d (k+1) ⊕ wittRespBool d k ⊕ wittRespBool (d + 2^k) k`
    equals `center d ⊕ ldiag d (d + 2^k)` (`= center d ⊕ zcenter d`). Moreover, because `maskcount`
    is a 1D running sum (`maskcount_add`), its dyadic coboundary vanishes identically
    (`maskparity_coboundary = false`), isolating `ldiag d (d + 2^k)` and `zcenter d` purely in terms
    of the left-half carry coboundary `leftresponse d (k+1) ⊕ leftresponse d k ⊕ leftresponse (d + 2^k) k`.
  - **Ostrowski–Archimedean Support of `winWitt` (`winWitt_testBit_low`, `winWitt_testBit_gt_two_mul`, `winWitt_testBit_archimedean`):**
    Every bit `j ≤ k` of `winWitt t0 (2^k)` vanishes (`2^{k+1} ∣ winWitt t0 (2^k)`), every bit
    `j > 2(t0 + 2^k)` vanishes, bit `d + 2^k` is `wittRespBool d k`, and for `d ≤ k` the Archimedean
    wing bit `d + 2^{k+1}` of `winWitt d (2^k)` is `center d ⊕ ldiag d (d + 2^k)`.
  - **Antiperiodicity & Coboundary Oscillation at Unbounded Zero Diagonals (`antiperiodic_of_doubles`, `ldiag_antiperiodic_of_doubles`, `zcenter_oscillates`, `leftresponse_coboundary_at_zero_diag`, `leftresponse_coboundary_after_zero_diag`, `witt_coboundary_at_zero_diag`, `witt_coboundary_after_zero_diag`):**
    At every doubling zero diagonal `z` for period `P` (`DoublesAt P z`), the running sum of
    `E (z - 1)` over `P` has odd weight (`rs_periodic_const`), so `E (z + 1) (t + P) = !E (z + 1) t`
    everywhere (`antiperiodic_of_doubles`), and on the real orbit `ldiag (z + 1) ((s + P) + 2^k) = !ldiag (z + 1) (s + 2^k)`
    for all `k ≥ z + 1` with `settle (z + 1) ≤ s + 2^k`. Moreover, at every zero diagonal `z`
    (unbounded by `infinitely_many_zero_diagonals`), `zcenter z = false` while `zcenter (z + 2) = true`
    (`zcenter_oscillates`). Consequently, for all settled scales `k`, the `leftresponse` dyadic
    coboundary vanishes at `z` and equals `true` at `z + 2`, while the `wittRespBool` dyadic
    coboundary directly reads `center z` at `z` and `!center (z + 2)` at `z + 2`.
  - **Repeat Scales & Left–Right Parity Lock (`periodic_response_eq_of_lag_eq`, `periodic_witt_eq_of_lag_eq`, `periodic_left_eq_mask_of_lag_eq`, `periodic_coboundary_collapse`, `lag_succ_eq_of_lag_eq`, `periodic_late_response_eq_of_lag_eq`, `periodic_late_witt_eq_of_lag_eq`, `periodic_late_left_eq_mask_of_lag_eq`):**
    Under `CenterPeriodic T P` (for any `P > 0`), at any two scales `k1, k2` with `2^k1 ≡ 2^k2 (mod P)` (`lag P k1 = lag P k2`), the inside-the-cone responses at `T ≤ t < min(2^k1, 2^k2)` coincide (`response t k1 = response t k2` and `wittRespBool t k1 = wittRespBool t k2`), locking the pure left-half response difference to the right-half column-1 masked parity difference:
    `leftresponse t k1 ⊕ leftresponse t k2 = maskparity t k1 ⊕ maskparity t k2`. Furthermore, because `lag P k1 = lag P k2` implies `lag P (k1+1) = lag P (k2+1)` and both `zcenter d` and `center d` are scale-independent, for any `T ≤ d ≤ min(k1, k2)` with `SettledAt d k1` and `SettledAt d k2`, the **outside-the-cone** responses at the two-place times `d + 2^k1` and `d + 2^k2` also coincide (`response (d + 2^k1) k1 = response (d + 2^k2) k2` and `wittRespBool (d + 2^k1) k1 = wittRespBool (d + 2^k2) k2`), locking `leftresponse (d + 2^k1) k1 ⊕ leftresponse (d + 2^k2) k2 = maskparity (d + 2^k1) k1 ⊕ maskparity (d + 2^k2) k2` across all repeat scales.
  - **Three-Ray Characteristic Decomposition & 2-Adic / Archimedean Zero-Gap Pinch of `winWitt` (`winWitt_testBit_lt_twopow`, `winWitt_testBit_middle_ray`, `winWitt_testBit_left_ray`, `winWitt_testBit_left_damage`, `winWitt_testBit_left_settled_zero`, `exists_right_threshold`, `winWitt_zero_gap_of_threshold`, `winWitt_leading_bit_of_threshold`, `threshold_lt_of_center_true`, `threshold_succ_lt_twopow_of_center_pred_false`):**
    The three monomials `1`, `x^(2^k)`, `x^(2^(k+1))` of `Φ₃(x)^(2^k)` correspond to the three characteristic rays of the Rule 30 light cone in sheared right-diagonal coordinates:
    1. **Ray 0 (`1`, `j < 2^k`):** `(winWitt t0 (2^k)).testBit j = rdiag j (t0 + 2^k) ⊕ rdiag j t0` (`2^k`-step shift along right diagonal `j`). By `Rule30RightPeriods.exists_last`, for every `k` there is a unique right-period threshold `J(k)` (`k ≤ J(k) ≤ 2^(k+1) - 2`, `IsRightThreshold k J`) such that bits `0 ≤ j ≤ J(k)` (with `j < 2^k`) vanish for all `t0`, while bit `J(k) + 1` (when `J(k) + 1 < 2^k`, which is forced whenever `center (2^k - 1) = false`) is universally `true` for **every** `t0 ∈ ℕ`. Moreover, any black center cell `center t = true` at `t ≥ 2^k` bounds `J(k) < t`.
    2. **Ray 1 (`x^(2^k)`, `i < 2^k` with `2 * t0 < i + 2^k`):** `(winWitt t0 (2^k)).testBit (i + 2^k) = rdiag (i + 2^k) (t0 + 2^k) ⊕ rdiag i t0 = cell (t0 + 2^k) (t0 - i) ⊕ cell t0 (t0 - i)` (`2^k`-step vertical shift along column `x = t0 - i`, reducing at `i = t0` to `wittRespBool t0 k`).
    3. **Ray 2 (`x^(2^(k+1))`, `d + m < 2^k`):** `(winWitt (d + m) (2^k)).testBit (d + 2m + 2^(k+1)) = ldiag d (d + m) ⊕ ldiag d ((d + m) + 2^k)` (`2^k`-step shift along left diagonal `d`). Once left diagonal `d ≤ k` has settled (`settle d ≤ d + m`), this bit vanishes identically (`winWitt_testBit_left_settled_zero`), creating an Archimedean zero gap at the top of `winWitt` mirror-dual to the 2-adic zero gap `[0, J(k)]` at the bottom, and isolating the unsettled damage band `ldiag d (d + m) ⊕ E d (d + m)`.
  - **Cyclotomic (`Φ₃`, `1 + x`) Interfaces & Nonlinear Rule 30 Cone Evolution of `winWitt` (`val_phiScale`, `val_winWitt`, `par_phiScale`, `par_winWitt`, `crossCarry`, `carry_xor`, `phi_xor`, `winWitt_base_step`, `carry_phiScale_row_cone`, `winWitt_cone_step`):**
    Because `Φ₃(ω)^(2^k) = 0` in `F₄` and `Φ₃(1)^(2^k) = 1` in `F₂`, `val (winWitt t0 (2^k)) = val (row (t0 + 2^k))` and `par (winWitt t0 (2^k)) = par (row (t0 + 2^k)) ⊕ par (row t0)`. Furthermore, the quadratic polarization of `carry` (`carry (a ^^^ b) = carry a ^^^ carry b ^^^ crossCarry a b`, where `crossCarry a b = (a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))`) and the disjointness of the three copies of `row t0` in `phiScale k (row t0)` for `2 * t0 + 1 < 2^k` (`carry (phiScale k (row t0)) = phiScale k (carry (row t0))`) prove that inside the light cone, `winWitt t0 (2^k)` evolves in `t0` by the full nonlinear Rule 30 step `phi` perturbed only by the bilinear cross-carry:
    `winWitt (t0 + 1) (2^k) = phi (winWitt t0 (2^k)) ^^^ (crossCarry (phiScale k (row t0)) (winWitt t0 (2^k)) <<< 1)`.
  - **Sigmatics Triality Ray-Sector Decomposition (`Z_3 × Z_{2^k}`), D-Coupling, and Threshold-Center Resonance (`trialityAddr`, `winWitt_testBit_triality_outside`, `winWitt_testBit_sector_one_cone`, `winWitt_testBit_sector_zero_xor_one`, `winWitt_testBit_center_slot`, `winWitt_testBit_sector_one_below_threshold`, `winWitt_testBit_sector_one_at_threshold`, `threshold_center_resonance`, `threshold_center_antiperiod`, `threshold_center_witt_response`):**
    Realizing the Categorical-X / Sigmatics CRT split (`D=2` dyadic scale `2^k` × `T=3` triality modality `d ∈ {0,1,2}` via `trialityAddr k d r = d * 2^k + r`), inside the light cone (`2 * t0 < 2^k`) `winWitt t0 (2^k)` vanishes identically outside the three triality sectors (`j ≥ 3 * 2^k`), and every slot `r < 2^k` of Sector 1 (`j = r + 2^k`) is unconditionally in the middle ray. XORing Sector 0 (`j = r`) and Sector 1 (`j = r + 2^k`) at slot `r < 2^k` (`2 * t0 < r + 2^k`) cancels the early-time state `rdiag r t0` identically, leaving the pure late-time spatial difference `rdiag r (t0 + 2^k) ⊕ rdiag (r + 2^k) (t0 + 2^k)`. Consequently, for `r ≤ J(k)` (below the 2-adic right-period threshold) Sector 1 reduces directly to that late-time spatial difference, whereas at `r = J(k) + 1 < 2^k` Sector 1 is its exact logical negation. At the center slot `r = t0 < 2^k`, Sector 1 reads `center (t0 + 2^k) ⊕ center t0`; specializing to the threshold time `t0 = J(k) + 1 < 2^k` forces `rdiag (J + 1) ((J + 1) + 2^k) = !center (J + 1)` and locks `wittRespBool (J + 1) k = !(center ((J + 1) + 2^k) ⊕ rdiag (J + 1) ((J + 1) + 2^k))`.
  - **Exact Rule 30 Evolution of `phiScale`, Wronskian Cross-Carry Localization, and Unified Left-Diagonal Sector Laws (`phiScale_row_cone_step`, `winWitt_cone_step_unperturbed_sector_zero`, `winWitt_cone_step_unperturbed_sector_one_gap`, `crossCarry_collision_at_threshold`, `winWitt_collision_flip_at_threshold`, `winWitt_testBit_sector_one_gap_ldiag`, `winWitt_testBit_sector_one_cone_edge`, `crossCarry_sector_one_cone_edge`, `ldiag_eq_rdiag`, `rdiag_threshold_sub_eq_ldiag`, `rdiag_threshold_succ_eq_not_ldiag`, `winWitt_testBit_sector_zero_ldiag`, `winWitt_testBit_sector_one_ldiag`, `winWitt_testBit_sector_one_xor_two`, `winWitt_testBit_sector_zero_xor_two`, `winWitt_testBit_top_edge_zero`, `winWitt_testBit_second_edge_zero`, `winWitt_testBit_third_edge_zero`):**
    Inside the cone (`2 * t0 + 1 < 2^k`), `phiScale k (row t0)` is an exact Rule 30 trajectory (`phiScale k (row (t0 + 1)) = phi (phiScale k (row t0))`), and before the cone reaches the 2-adic threshold (`2 * t0 < J(k)`), `crossCarry` vanishes on the entire first sector `[0, 2^k]`, so `(winWitt (t0 + 1) (2^k)).testBit j = (phi (winWitt t0 (2^k))).testBit j` for all `j ≤ 2^k` (and likewise in the Sector-1 gap `2 * t0 + 2 < r ≤ 2^k`). At `2 * t0 = J(k)`, the `2×2` Wronskian matrix at `(J, J+1)` is `[[1,0],[0,1]]`, injecting a `1`-bit into bit `J + 2` of `winWitt (t0 + 1) (2^k)`. In Sector 1 above the shifted cone edge (`j = 2 * t0 + m + 2^k`, `1 ≤ m < 2^k - 2 * t0`), `winWitt t0 (2^k)` directly reads the late left diagonal `ldiag (2^k - m) (t0 + 2^k)`. Using the fundamental two-place diagonal shear `ldiag d (d + s) = rdiag (d + 2 * s) (d + s)`, all three triality sectors at slot `r = d + 2 * s < 2^k` (`t0 = d + s`) share the exact same early-time term `ldiag d (d + s)` and compare it against `rdiag (d + 2 * s) (d + s + 2^k)` (Sector 0), `ldiag (d + 2^k) (d + s + 2^k)` (Sector 1), and `ldiag d (d + s + 2^k)` (Sector 2), so every pairwise XOR cancels the early-time state identically.
  - **2-Adic Threshold Spacetime Geometry & Archimedean Sector-2 Settling / Repeat-Lag Laws (`rdiag_threshold_late_false_window`, `rdiag_threshold_late_true_plateau`, `rdiag_threshold_late_false_odd_hit`, `rdiag_threshold_late_false_even_hit`, `rdiag_threshold_plus_two_step_neg`, `winWitt_testBit_threshold_plus_two_step_neg`, `winWitt_testBit_threshold_plus_two_collision_freeze`, `ldiag_two_eq_false`, `ldiag_three_step_neg`, `winWitt_testBit_sector_one_settled`, `rdiag_eq_ldiag_of_settled_below_threshold`, `rdiag_eq_not_ldiag_of_settled_at_threshold`, `winWitt_testBit_sector_two_scale_eq`, `center_late_xor_ldiag_eq_witt_cross_scale`, `periodic_ldiag_xor_eq_late_witt_xor_of_lag_eq`):**
    For `2 * t0 ≤ J(k)`, the late spacetime slice at `t0 + 2^k` exhibits a white window `rdiag j (t0 + 2^k) = false` (`2 * t0 < j ≤ J`), a black plateau `rdiag (J + 1) (t0 + 2^k) = true` that terminates at cone arrival (`2 * t0 = J + 1` for odd `J`, or `(t0 + 1) + 2^k` for even `J = 2 * t0`), and strict period-2 alternation `rdiag (J + 2) ((t0 + 1) + 2^k) = !rdiag (J + 2) (t0 + 2^k)`, causing bit `J + 2` of `winWitt` to alternate for `2 * t0 < J` and freeze at the exact Wronskian collision `2 * t0 = J`. Dually, on settled left diagonals (`SettledBy d (d + s)`, `d ≤ k`), Sector 2 vanishes, reducing Sector 1 to `ldiag (d + 2^k) (d + s + 2^k) ⊕ ldiag d (d + s + 2^k)` and locking `rdiag (d + 2 * s) (d + s + 2^k) = ldiag d (d + s + 2^k)` for `d + 2 * s ≤ J(k)` (and `!ldiag` at `J + 1`). Even before `d + s` settles, Sector 2 in the Archimedean damage band (`SettledBy d (d + s + 2^k)`) is completely scale-invariant across `k1, k2 ≥ d`, and at `s = 0` (`t0 = d ≤ k`) the Sector-1 ⊕ Sector-2 coupling yields the unsettled cross-scale identity `center (d + 2^k) ⊕ ldiag d (d + 2^k) = wittRespBool d (k + 1) ⊕ wittRespBool (d + 2^k) k`, locking `ldiag d (d + 2^k1) ⊕ ldiag d (d + 2^k2) = wittRespBool (d + 2^k1) k1 ⊕ wittRespBool (d + 2^k2) k2` across all repeat scales `lag P k1 = lag P k2` without any settling hypothesis.
  - **Step 1–3 Reduction of the Late Term, Bridge to `ZCenterPeriodic`, and Zero-State Non-Periodicity Anchors (`periodic_response_shift_P`, `periodic_witt_shift_P`, `periodic_winWitt_sector_one_shift_P`, `periodic_late_response_unsettled_decomp`, `periodic_late_response_settled_decomp`, `periodic_zcenter_from_lag_and_late_response`, `periodic_zcenter_shift_xor_eq_late_response_xor`, `periodic_zcenter_shift_xor_eq_late_witt_xor`, `periodic_zcenter_shift_xor_eq_sector_two_xor`, `exists_settled_scale_pair`, `ZCenterPeriodic`, `zcenter_periodic_of_late_response_shift`, `zcenter_periodic_of_late_witt_shift`, `zcenter_not_periodic_one`, `zcenter_not_periodic_two`, `zcenter_periodic_not_zero_diag_shift`):**
    1. **Step 1 (Late-Term Reduction under `CenterPeriodic T P`):** Inside the cone (`T ≤ t`, `t + P < 2^k`), `response (t + P) k = response t k`, `wittRespBool (t + P) k = wittRespBool t k`, and Sector 1 of `winWitt` at the center slot is `P`-periodic. Outside the cone (`T ≤ d ≤ k`), `response (d + 2^k) k` decomposes into the pure `(d mod P, lag P k)` component `center (d + lag P (k + 1)) ⊕ center (d + lag P k)` XORed with `ldiag d (d + 2^k)` (unsettled) or `zcenter d` (`SettledAt d k`). Consequently, at any jointly settled scale `k ≥ d + P` (`exists_settled_scale_pair`), the `(d mod P, lag P k)` terms cancel identically between `d` and `d + P`, reducing the periodicity defect `zcenter (d + P) ⊕ zcenter d` to `response (d + P + 2^k) k ⊕ response (d + 2^k) k = wittRespBool (d + P + 2^k) k ⊕ wittRespBool (d + 2^k) k = (winWitt (d + P) (2^k)).testBit (d + P + 2^(k+1)) ⊕ (winWitt d (2^k)).testBit (d + 2^(k+1))`.
    2. **Step 2 (Bridge to `ZCenterPeriodic`):** Whenever the late response is shift-invariant by `P` at jointly settled scales `k ≥ d + P`, `CenterPeriodic T P` implies `ZCenterPeriodic T P` (`zcenter_periodic_of_late_response_shift`, `zcenter_periodic_of_late_witt_shift`).
    3. **Step 3 (Zero-State Non-Periodicity on `zcenter` Alone):** Using only `zcenter_oscillates` on the universal settled structure `E`, `zcenter` is unconditionally proved to have no eventual period `1` (`zcenter_not_periodic_one`) and no eventual period `2` (`zcenter_not_periodic_two`), and any hypothetical `ZCenterPeriodic T Q` forbids zero diagonals at all shifted compile positions `(z + 2) + m * Q` (`zcenter_periodic_not_zero_diag_shift`).
  - **Exact `Nat`-Level 1-Cocycle of `winWitt`, Triality Sector Readouts, Vacuum-Tree `zcenter` Laws, and the XOR Channel (`winWitt_scale_cocycle`, `phiScale_testBit_triality`, `phiScale_testBit_sector_one`, `winWitt_late_testBit_triality`, `wittRespBool_late_from_early_triality`, `periodic_late_witt_from_lag_and_sector_two`, `periodic_late_maskparity_decomp`, `zcenter_periodic_of_leftresponse_coboundary_shift`, `zcenter_periodic_of_sector_two_shift`, `zcenter_step`, `zcenter_back`, `zcenter_twin_before_zero_diag`, `zcenter_three_after_zero_diag`, `zcenter_antiperiodic_after_doubles`, `zcenter_toggle_of_transparent`, `zcenter_reset_of_opaque`, `zcenter_left_of_black`, `zcenter_periodic_offdiag_eq_of_black`, `zcenter_black_pair_forces_offdiag_false`, `NoZCenterPeriod`, `maskcount_one`, `maskparity_zero`, `leftresponse_zero`, `response_zero_eq_maskparity_zero`, `maskparity_shift_diff`, `maskparity_step_diff`, `maskparity_step_diff_zero`, `carry60_succ_zero_eq_rdiag`, `maskparity_succ_zero_eq_rdiag`, `maskedPer_iff_carry60_periodic`, `maskedPer_iff_maskparity_zero_periodic`, `maskparity_periodic_of_maskedPer`, `periodic_maskparity_shift_P_cone`, `periodic_maskcount_P_dyadic_jump_cone`, `periodic_carry60_dyadic_jump_cone`, `periodic_carry60_defect_dyadic_jump_cone`, `periodic_late_maskparity_shift_P`, `periodic_late_carry60_dyadic_jump`, `periodic_late_carry60_defect_dyadic_jump`, `periodic_late_leftresponse_unsettled_decomp`, `periodic_zcenter_from_lag_and_late_left_mask`, `periodic_carry60_defect_eq_colm1_defect`, `maskedPer_iff_colm1_periodic`):**
    1. **Why `ZCenterBridgeObligation` Is Retired:** By `phase_universal`, the settled left structure of every pattern with a left edge is the same universal object `Ξ` up to a time shift, including a left half driven by any periodic column. Thus any gate of the form "periodic center ⇒ property X of a fixed object" has the same retired shape as `ObFront`, and left-half identities alone cannot prove the bridge. What a periodic driver of the left half does not supply is the coupling at position `0` through column `1` — the XOR channel (`maskparity` / `carry60 · 0` / `MaskPos`).
    2. **Exact `Nat`-Level 1-Cocycle (`winWitt_scale_cocycle`):** Across every dyadic scale `k` and base time `t0`, the late Witt window integer satisfies `winWitt (t0 + 2^k) (2^k) = winWitt t0 (2^(k+1)) ^^^ phiScale k (winWitt t0 (2^k))`. Reading bit `r + 2^(k+1)` (`phiScale_testBit_triality`, `winWitt_late_testBit_triality`) expresses every late Sector-1 bit purely in terms of bit `r + 2^(k+1)` of `winWitt t0 (2^(k+1))` XORed with the three Triality Sectors `0, 1, 2` of `winWitt t0 (2^k)` at slot `r`. At `r = t0 = d ≤ k`, Sector 0 vanishes (`winWitt_testBit_low`), yielding `wittRespBool (d + 2^k) k = wittRespBool d (k + 1) ⊕ wittRespBool d k ⊕ (winWitt d (2^k)).testBit (d + 2^(k+1))` (`wittRespBool_late_from_early_triality`) and, under `CenterPeriodic T P`, `wittRespBool (d + 2^k) k = center (d + lag P (k + 1)) ⊕ center (d + lag P k) ⊕ (winWitt d (2^k)).testBit (d + 2^(k+1))` (`periodic_late_witt_from_lag_and_sector_two`). Dually, `periodic_late_maskparity_decomp` (9.103) reduces `maskparity (d + 2^k) k = leftresponse d (k + 1) ⊕ leftresponse d k ⊕ center (d + lag P (k + 1)) ⊕ center (d + lag P k)`.
    3. **The XOR Channel (`maskparity` / `carry60 · 0`) and `MaskPos` across Dyadic Scales:**
       - **Scale-0 Readout & Equivalence to `MaskedPer`:** At scale `k = 0` (`2^0 = 1`), `leftresponse t 0 = false` (`leftresponse_zero`), so `response t 0 = maskparity t 0 = carry60 t 0` (`response_zero_eq_maskparity_zero`, `maskparity_zero`), and `maskparity (s + 1) 0 = (!rdiag (s + 1) (s + 1)) && rdiag s (s + 1)` (`maskparity_succ_zero_eq_rdiag`). Under `CenterPeriodic T P`, Section 6's `MaskedPer T P` is **equivalent** to `P`-periodicity of `maskparity (s + 1) 0` for all `s ≥ T` (`maskedPer_iff_maskparity_zero_periodic`, `maskparity_zero_periodic_of_maskedPer`, `maskedPer_of_maskparity_zero_periodic`), which in turn implies `maskparity (t + P) k = maskparity t k` at all scales `k` for `t ≥ T + 1` (`maskparity_periodic_of_maskedPer`). Moreover, at scale `0`, the `P`-periodicity defect of `maskparity · 0` equals the `P`-periodicity defect of column `-1`: `maskparity (t + P) 0 ⊕ maskparity t 0 = cell (t + P) (-1) ⊕ cell t (-1)` (`periodic_maskparity_zero_defect_eq_colm1_defect`).
       - **1-Step Discrete Derivative & Dyadic Jumps of the XOR Channel:** Because `maskparity t k = maskcount t (2^k)` is a running sum of `maskparity · 0 = carry60 · 0`, stepping `t ↦ t + 1` differentiates `maskparity` and extracts the exact dyadic jump of the single-step XOR channel across `2^k`: `maskparity (t + 1) k ⊕ maskparity t k = maskparity (t + 2^k) 0 ⊕ maskparity t 0` (`maskparity_step_diff_zero`). Inside the cone (`T ≤ t`, `t + P < 2^k`), `maskparity (t + P) k ⊕ maskparity t k = leftresponse (t + P) k ⊕ leftresponse t k` (`periodic_maskparity_shift_P_cone`), and the `P`-periodicity defect `δ_P(s) = maskparity (s + P) 0 ⊕ maskparity s 0` jumps across `2^k` (`t + P + 1 < 2^k`) purely by the second difference of `leftresponse · k` (`periodic_maskparity_zero_defect_dyadic_jump_cone`). Outside the cone (`T ≤ d ≤ k`), shifting 9.103 (`periodic_late_maskparity_decomp`) by `P` (`d + P ≤ k`) cancels all center lag terms to give `maskparity (d + P + 2^k) k ⊕ maskparity (d + 2^k) k = (leftresponse (d + P) (k + 1) ⊕ leftresponse (d + P) k) ⊕ (leftresponse d (k + 1) ⊕ leftresponse d k)` (`periodic_late_maskparity_shift_P`), while differentiating 9.103 with respect to `d ↦ d + 1` gives the exact late dyadic jump `maskparity (d + 2^(k+1)) 0 ⊕ maskparity (d + 2^k) 0` (`periodic_late_maskparity_zero_dyadic_jump`) and the late `P`-defect jump `δ_P(d + 2^(k+1)) ⊕ δ_P(d + 2^k)` (`periodic_late_maskparity_zero_defect_dyadic_jump`).
    4. **Vacuum-Tree & Zero-State Orbit Laws (`zcenter_step`, `zcenter_back`, `Rule30ZeroStateOrbit`):** On `E` alone, `zcenter (d + 2) = E d (d + 1) ⊕ (zcenter (d + 1) || E (d + 2) (d + 1))` and `E d (d + 1) = zcenter (d + 2) ⊕ (zcenter (d + 1) || E (d + 2) (d + 1))`, with `zcenter (z + 3) = !E (z + 1) (z + 2)` at every zero diagonal `z`, `E (z + 1) ((z + 1) + P) = !zcenter (z + 1)` at every `P`-doubling zero diagonal, and `E (d + Q) ((d + Q) + 1) = E d (d + 1)` at every black `zcenter (d + 1) = true` under `ZCenterPeriodic T Q` (`zcenter_periodic_offdiag_eq_of_black`). In `Rule30ZeroStateOrbit`, `zcenter_not_eventually_constant`, `zcenter_jen`, `zcenter_masked_jen_right`, and `zcenter_masked_jen_left` establish Jen's theorem and masked Jen directly for `zcenter` on the zero-state orbit `Ecell`.
  - **Theorem 9.152 Outside the Cone (Fixed `k`, Unbounded `t0 ≥ 2^k`) and Fixed-Scale `m * P`-Shift Laws (`phiScale_row_testBit_outside_cone`, `winWitt_testBit_outside_cone`, `periodic_crossCarry_colm1_outside_cone_and`, `periodic_crossCarry_colm1_outside_cone_wronskian`, `periodic_crossCarry_colm1_outside_cone_at_white_center`, `periodic_crossCarry_colm1_outside_cone_at_both_white_centers`, `crossCarry_colm1_at_white_late_center_eq_and_witt`, `crossCarry_colm1_outside_cone_at_white_late_center_via_response`, `crossCarry_row_scale_at_center_bit_outside_cone_and`, `crossCarry_at_white_center_outside_cone_noncenter_and`, `crossCarry_at_center_bit_outside_cone_wronskian`, `periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity`, `crossCarry_at_white_late_center_eq_witt_and_maskparity`, `periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul`, `wittRespBool_xor_response_shift_mul_outside_cone`, `periodic_wittRespBool_shift_mul_outside_cone`, `periodic_crossCarry_colm1_shift_mul_at_white_late_center`, `periodic_crossCarry_center_bit_shift_mul_at_white_late_center`):**
    When `k` is fixed and `t0 = d + 1 ≥ 2^k` (or `s + 1 > 2^k`) runs over all large times outside the cone, all three shifted copies of `row t0` in `phiScale k (row t0)` reach the center slot and column-`±1` slots. Consequently:
    1. At bit `(d + 2) + 2^k` (column `-1` of the center slot), when `center (d + 1) = false`, the second AND-term in `crossCarry` does **not** vanish as it did inside the cone; instead, `center (d + 1) = false` drops out and leaves the non-center AND-product `ldiag (d + 2^k) ((d + 1) + 2^k) && (ldiag ((d + 1) - 2^k) (d + 1) ⊕ rdiag ((d + 1) - 2^k) (d + 1))`. When `center ((d + 1) + lag P k) = false` as well, the first branch vanishes and the cross-carry collapses to that pure non-center AND-product (`periodic_crossCarry_colm1_outside_cone_at_both_white_centers`).
    2. At bit `(s + 1) + 2^k` (the exact center bit), when `center (s + 1) = false` and `center ((s + 1) + lag P k) = false`, the cross-carry collapses to `(ldiag ((s + 1) - 2^k) (s + 1) ⊕ rdiag ((s + 1) - 2^k) (s + 1)) && maskparity ((s + 1) + 2^k) 0` (`periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity`), and universally for all `s` with `center ((s + 1) + 2^k) = false` to `wittRespBool (s + 1) k && maskparity ((s + 1) + 2^k) 0` (`crossCarry_at_white_late_center_eq_witt_and_maskparity`).
    3. Under `CenterPeriodic T P`, shifting unbounded `d` or `s` by any fixed period multiple `P' = m * P` at fixed scale `k` gives equations in the exact form required by masked Jen (one fixed period `m * P` for all large times), coupling the `m * P`-defect `maskparity (t + m * P) 0 ⊕ maskparity t 0` directly with `wittRespBool · k`, whose `m * P`-defect outside the cone is `(ldiag ((t + m * P) - 2^k) (t + m * P) ⊕ ldiag (t - 2^k) t) ⊕ (rdiag ((t + m * P) - 2^k) (t + m * P) ⊕ rdiag (t - 2^k) t)` (`periodic_wittRespBool_shift_mul_outside_cone`).
  - **Frobenius Defect `frobDefect k`, Outside-the-Cone Window Step, and Tying the In-Cone Seed Laws (`R_periodic`, `frobDefect = 0`) to `zcenter`, `maskparity`, and Column `-1` Uniformly in `m` (`frobDefect_row_cone_eq_zero`, `winWitt_step_frobDefect`, `winWitt_step_frobDefect_testBit_succ`, `frobDefect_row_testBit_outside_cone`, `frobDefect_row_center_slot_outside_cone`, `frobDefect_row_center_slot_at_white_center_outside_cone`, `frobDefect_row_colm1_slot_outside_cone`, `frobDefect_row_colm1_slot_at_white_center_outside_cone`, `frobDefect_row_col1_slot_outside_cone`, `frobDefect_row_col1_slot_at_white_center_outside_cone`, `periodic_winWitt_step_center_slot_outside_cone`, `periodic_winWitt_step_center_slot_at_white_late_center_outside_cone`, `periodic_winWitt_step_center_slot_at_both_white_centers_outside_cone`, `periodic_winWitt_step_colm1_slot_outside_cone`, `periodic_winWitt_step_colm1_slot_at_both_white_centers_outside_cone`, `periodic_winWitt_step_col1_slot_outside_cone`, `periodic_winWitt_step_center_slot_shift_mul_at_white_late_center`, `frobDefect_xor`, `frobDefect_phiScale_row_cone_eq_zero`, `frobDefect_row_late_from_cone`, `frobDefect_row_late_center_slot_rperiodic`, `frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump`, `frobDefect_row_late_colm1_slot_rperiodic`, `frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage`, `frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers`, `periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality`, `periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality`, `wittRespBool_late_eq_zcenter_xor_center_triality`, `wittRespBool_late_at_white_centers_eq_zcenter`, `periodic_wittRespBool_late_shift_mul_eq_zcenter_xor`, `periodic_crossCarry_late_center_bit_shift_mul_at_white_centers`, `periodic_crossCarry_late_colm1_shift_mul_at_white_centers`, `periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers`):**
    1. **Unconditional Window Step with Frobenius Defect:** For every `t0` and `k`, `winWitt (t0 + 1) (2^k) = phi (winWitt t0 (2^k)) ^^^ (crossCarry (phiScale k (row t0)) (winWitt t0 (2^k)) <<< 1) ^^^ (frobDefect k (row t0) <<< 1)`, where `frobDefect k a = carry (phiScale k a) ^^^ phiScale k (carry a)`. Inside the cone (`2 * t0 + 1 < 2^k`), `frobDefect k (row t0) = 0` and `frobDefect k (phiScale k (row t0)) = 0` because the scaled copies of `row t0` do not overlap (`frobDefect_row_cone_eq_zero`, `frobDefect_phiScale_row_cone_eq_zero`). Consequently, at `t0 + 2^k` (`2 * t0 + 1 < 2^k`), the late row's Frobenius defect decomposes purely into `frobDefect k w ^^^ crossCarry (phiScale (k + 1) (row t0)) (phiScale k w) ^^^ phiScale k (crossCarry (phiScale k (row t0)) w)` (`frobDefect_row_late_from_cone`).
    2. **Folding Outside-the-Cone `frobDefect` and `wittRespBool` by `R_periodic` at `t0 = (d + 1) + 2^k` (`d + 1 ≤ k`):** At `t0 = (d + 1) + 2^k` (`d + 1 ≤ k`, `SettledAt (d + 1) k`), `t0 ≥ 2^k` lies outside the cone of scale `k`, while its right-wing cells at distance `2^k` have depth `t0 - 2^k = d + 1 ≤ k`. The in-cone single-cell seed law `R_periodic` folds `rdiag (d + 1) ((d + 1) + 2^k) = center (d + 1)` and `rdiag d ((d + 1) + 2^k) = rdiag d (d + 1)`. As a result:
       - `wittRespBool ((d + 1) + 2^k) k = zcenter (d + 1) ⊕ center ((d + 1) + 2^(k+1)) ⊕ center ((d + 1) + 2^k) ⊕ center (d + 1)` (`wittRespBool_late_eq_zcenter_xor_center_triality`), collapsing on white centers to `zcenter (d + 1)` (`wittRespBool_late_at_white_centers_eq_zcenter`);
       - At the center slot on white centers at `d + 1` and `(d + 1) + 2^k`, `(frobDefect k (row ((d + 1) + 2^k))).testBit (((d + 1) + 2^k) + 2^k) = zcenter (d + 1) && (maskparity ((d + 1) + 2^k) 0 ⊕ maskparity (d + 1) 0)` (`frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump`);
       - At column `-1` (`d + 2 ≤ k`, in-phase `center ((d + 1) + 2^k) = center (d + 1)`), `(frobDefect k (row ((d + 1) + 2^k))).testBit (((d + 2) + 2^k) + 2^k) = (ldiag (d + 2^k) ((d + 1) + 2^k) ⊕ ldiag d (d + 1)) && (zcenter (d + 1) ⊕ center (d + 1))` (`frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage`), and its XOR with the center-slot defect on white centers equals `zcenter (d + 1) && (center ((d + 2) + 2^k) ⊕ center (d + 2))` (`frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers`).
    3. **Uniform-in-`m` Shifts from the In-Cone Seed Anchor (`periodic_wittRespBool_late_shift_mul_eq_zcenter_xor`, `periodic_crossCarry_late_center_bit_shift_mul_at_white_centers`, `periodic_crossCarry_late_colm1_shift_mul_at_white_centers`, `periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers`):** Shifting the `R_periodic`-folded anchor `(d + 1) + 2^k` by `m * P` for arbitrary `m ≥ 0` at fixed scale `k` ties `zcenter (d + 1)` and `center (d + 1)` directly to the `m * P`-defects of `maskparity (· + 2^k) 0`, `ldiag`, `rdiag`, and the outside-the-cone window step across all `m`.
    4. **Uniform-in-`u` Restart Folding, Exact Sector-1 & Sector-2 Late-Row Frobenius Defect Equivalence, and Target Refutation Bridges (`rdiag_restart`, `rdiag_restart_of_threshold`, `center_restart_rdiag`, `frobDefect_row_testBit_lt_twopow`, `frobDefect_row_testBit_sector_one`, `frobDefect_row_sector_one_restart`, `frobDefect_row_sector_two_restart`, `frobDefect_winWitt_sector_two_wronskian`, `crossCarry_scale_row_winWitt_sector_two_cone_eq`, `frobDefect_row_late_eq_frobDefect_winWitt_sector_two`, `frobDefect_row_late_eq_winWitt_sector_two_wronskian`, `periodic_ldiag_shift_mul_eq_response_shift_mul`, `not_periodic_maskparity_zero_mul`, `not_periodic_colm1_mul`, `phiScale_row_late_sector_one_eq_winWitt_cone`, `frobDefect_row_late_sector_one_eq_crossCarry_cone`, `frobDefect_row_late_sector_one_center_slot_wronskian`, `crossCarry_row_winWitt_sector_two_center_slot`):**
       - **Uniform-in-`u` `restart` folding:** For all `u ∈ ℕ` and `j ≤ k` (or `j ≤ J(k)`), `rdiag j (s + u * 2^k) = rdiag j s` and `rdiag s (s + u * 2^k) = center s`. Sector 0 (`j < 2^k`) of `frobDefect k (row t0)` vanishes identically for all `t0 ∈ ℕ`, while Sector 1 (`(d + 1) + 2^k`) and Sector 2 (`(d + 1) + 2^(k+1)`) at `t_u = (d + 1) + u * 2^k` (`d + 1 ≤ k`) freeze their Sector-0 factors to `center (d + 1)` and `rdiag d (d + 1)` uniformly in `u`.
       - **Exact Sector-1 & Sector-2 identities from `δ_k = 0` inside the cone + `R_periodic`:** For `2 * t0 + 1 < 2^k` and `r + 1 ≤ k`, in Sector 1 `(phiScale k (row (t0 + 2^k))).testBit (j + 2^k) = (winWitt t0 (2^k)).testBit (j + 2^k)` (`j ≤ k`) and `(frobDefect k (row (t0 + 2^k))).testBit ((r + 1) + 2^k) = (crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit ((r + 1) + 2^k)` (evaluating at `r = d` to the `(center, rdiag)` Wronskian between `d + 1` and `d + 1 + 2^k`); in Sector 2 the two cross-carry terms cancel identically (`crossCarry_scale_row_winWitt_sector_two_cone_eq`), so `(frobDefect k (row (t0 + 2^k))).testBit ((r + 1) + 2^(k+1)) = (frobDefect k (winWitt t0 (2^k))).testBit ((r + 1) + 2^(k+1))`, which equals the `2 × 2` Wronskian between Sector 2 and Sector 1 of `winWitt t0 (2^k)`. Furthermore, at a white center `center (d + 1) = false`, bit `(d + 1) + 2^(k+1)` of the in-cone cross-carry `crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (2^k))` equals `zcenter (d + 1) && maskparity (d + 1) 0` (independent of `k`).
       - **Target refutation bridges:** Under `CenterPeriodic T P` (`0 < P`), for any `T'` and `m > 0`, `¬ MaskParityZeroPeriodic T' (m * P)` (Target 2) and `¬ ColNegOnePeriodic T' (m * P)` (Target 1), and for `t ≥ max(T, 2^k)`, the `m * P`-defect of column `-2^k` (`ldiag (t - 2^k) t`) equals the `m * P`-defect of `response t k`.
    5. **Shrinking-Neighbourhood Window-Step Propagation (Theorem 9.204), Symmetric Doubling Across the Periodic Center, and Carrying `Q = lcm(P, 2^k)`-Periodicity from Sector Times Across All Residues `mod 2^k` (`RowAgree`, `WinWittAgree`, `SectorRowAgree`, `SectorRightRowAgree`, `SectorWinWittAgree`, `lcmPeriod`, `ldiag_settled_restart`, `zcenter_restart_ldiag`, `frobDefect_row_late_center_slot_of_zcenter_true`, `periodic_winWitt_step_late_center_slot_of_zcenter_true`, `periodic_winWitt_step_late_colm1_slot_of_zcenter_true`, `rowAgree_mono`, `winWittAgree_mono`, `rowAgree_step`, `rowAgree_steps`, `phiScale_row_testBit_eq_of_rowAgree`, `frobDefect_row_testBit_eq_of_rowAgree`, `crossCarry_testBit_eq_of_rowAgree_winWittAgree`, `winWittAgree_step`, `winWittAgree_steps`, `wittRespBool_eq_of_winWittAgree_steps`, `colm1_eq_of_rowAgree_steps`, `maskparity_zero_eq_of_rowAgree_steps`, `colNegOnePeriodic_of_sector_rowAgree`, `not_sector_rowAgree_mul`, `rdiag_lcmPeriod_eq`, `ldiag_lcmPeriod_eq`, `center_lcmPeriod_eq`, `not_sector_rowAgree_lcmPeriod`, `rowAgree_extend_right`, `periodic_rowAgree_center`, `periodic_rowAgree_black_center`, `periodic_rowAgree_symm_of_right`, `periodic_rowAgree_lcmPeriod_symm_of_right`, `colNegOnePeriodic_of_sector_right_rowAgree`, `not_sector_right_rowAgree_lcmPeriod`, `winWittAgree_extend_right`, `winWittAgree_of_rowAgree_three_and_late`, `rowAgree_late_of_winWittAgree_and_three`, `wittRespBool_periodic_of_sector_winWittAgree`, `right_boundary_row_lcmPeriod_eq`, `left_boundary_row_lcmPeriod_eq`, `frobDefect_row_sector_one_lcmPeriod_xor`):**
       - **Left-Wing Settled `restart` and Sector-Time Unmasking (`zcenter (d + 1) = true`):** For `j ≤ k` and `settle j ≤ t`, `ldiag j (t + v * 2^k) = ldiag j t` uniformly for all `v ∈ ℕ`, and for `d ≤ k`, `1 ≤ u`, `SettledAt d k`, `ldiag d (d + u * 2^k) = zcenter d`. At sector times `t ≡ d + 1 (mod 2^k)` (`d + 1 ≤ k`) where `zcenter (d + 1) = true`, the AND with `zcenter (d + 1)` unmasks the Frobenius defect jump (`maskparity ((d + 1) + 2^k) 0 ⊕ maskparity (d + 1) 0`), the center-slot window step (`maskparity` triality), and the column-`-1` window step (`ldiag` triality).
       - **Generic Window-Step Propagation via Theorem 9.204 (`winWitt_step_frobDefect_testBit_succ`):** `RowAgree t Q a L` and `WinWittAgree t k Q a L` express bit-agreement of `row (t + Q)` at `[a + Q, a + L + Q]` with `row t` at `[a, a + L]` (the same spatial columns `x ∈ [t - (a + L), t - a]`), and likewise for `winWitt · (2^k)`. Under three-sector `RowAgree` at time `t`, `WinWittAgree t k Q a L` is equivalent to `RowAgree (t + 2^k) Q a L` (`winWittAgree_of_rowAgree_three_and_late`, `rowAgree_late_of_winWittAgree_and_three`). Each forward step loses one cell of agreement on each side around the moving center (`[a, a + L + 2] ↦ [a + 2, a + 2 + L]`), so `s` steps propagate `[a, a + L + 2 * s]` at time `t` to `[a + 2 * s, a + 2 * s + L]` at time `t + s` (`rowAgree_steps`, `winWittAgree_steps`). Specializing to `L = 0` (radius `s`, width `2 * s`) carries `Q`-agreement of `wittRespBool · k`, `ldiag`, and `maskparity · 0` forward by `s` steps (`wittRespBool_eq_of_winWittAgree_steps`, `colm1_eq_of_rowAgree_steps`, `maskparity_zero_eq_of_rowAgree_steps`).
       - **Leftward Bijectivity and Symmetric Doubling of Right-Half Agreement Across the Periodic Center:** Leftward bijectivity of Rule 30 (`row_testBit_add_two_of_step`) and of Theorem 9.204 extends `RowAgree` and `WinWittAgree` by 1 cell leftward in space (`[a, a + L + 1] ↦ [a, a + L + 2]`) whenever bit `a + L + 2` agrees at time `t + 1` (`rowAgree_extend_right`, `winWittAgree_extend_right`). Under `CenterPeriodic T P`, `RowAgree t (m * P) t 0` holds at every `t ≥ T` (`periodic_rowAgree_center`), `RowAgree (t + 1) (m * P) (t + 1) 1` holds at every black center `center (t + 1) = true` (`periodic_rowAgree_black_center`), and by induction on `R ≤ t`, **one-sided right-wing agreement `RowAgree t Q (t - R) R` on `[t - R, t]` (spatial columns `x ∈ [0, R]`) automatically doubles across the periodic center to full two-sided symmetric agreement `RowAgree t Q (t - R) (2 * R)` on `[t - R, t + R]` (`x ∈ [-R, +R]`)** (`periodic_rowAgree_symm_of_right`, `periodic_rowAgree_lcmPeriod_symm_of_right`).
       - **Sector Times to All Residues `mod 2^k` at `Q = lcm(P, 2^k)`:** If `SectorRowAgree k d U Q` (or one-sided `SectorRightRowAgree k d U Q` via symmetric doubling) holds at all sector times `(d + 1) + u * 2^k` (`u ≥ U ≥ 1`), Euclidean division by `2^k` writes every `t ≥ d + U * 2^k` as `(d + (U + q) * 2^k) + s` with `s < 2^k`, carrying `Q`-periodicity across every residue `mod 2^k` to establish `ColNegOnePeriodic (d + U * 2^k) Q` (`colNegOnePeriodic_of_sector_rowAgree`, `colNegOnePeriodic_of_sector_right_rowAgree`), and similarly `SectorWinWittAgree k d U Q` carries `wittRespBool (t + Q) k = wittRespBool t k` to all residues `mod 2^k` via Window Step 9.204 (`wittRespBool_periodic_of_sector_winWittAgree`). For `Q = lcmPeriod P k = lcm(P, 2^k)`, both `P ∣ Q` and `2^k ∣ Q`, so `Q` simultaneously preserves the right-boundary row neighbourhood `j ≤ k` (`rdiag_lcmPeriod_eq`, `right_boundary_row_lcmPeriod_eq`), the settled left-boundary row neighbourhood `j ≤ k` (`ldiag_lcmPeriod_eq`, `left_boundary_row_lcmPeriod_eq`), and the center column (`center_lcmPeriod_eq`), factors the Sector-1 `frobDefect` `Q`-difference at sector times (`frobDefect_row_sector_one_lcmPeriod_xor`), and refutes both `SectorRowAgree` and `SectorRightRowAgree` at `Q = lcm(P, 2^k)` (`not_sector_rowAgree_lcmPeriod`, `not_sector_right_rowAgree_lcmPeriod`).
    6. **The §6 Driven Right-Half / `Φ` Fixed-Point Inward & Center-Bounce Calculus (`rhCenter`, `lhCenter`, `RhBandAgree`, `SectorRhBandAgree`, `SectorWideRowAgree`, `SectorWideRightRowAgree`, `rhCenter_eq_rdiag`, `rhCenter_eq_row_testBit`, `lhCenter_eq_ldiag`, `lhCenter_eq_row_testBit`, `rhCenter_zero_eq_center`, `rhCenter_self_eq_true`, `rhCenter_gt_eq_false`, `phiCenter_eq_lhCenter_rhCenter`, `lhCenter_one_eq_of_center_fixed`, `periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect`, `rhCenter_step_succ`, `rhCenter_inward_step`, `rhBandAgree_extend_inward`, `rhBandAgree_step`, `rowAgree_right_of_rhBandAgree`, `rhBandAgree_of_rowAgree_right`, `sectorRightRowAgree_of_rhBandAgree`, `not_sector_rhBandAgree_lcmPeriod`, `rhCenter_right_edge_lcmPeriod_eq`, `colNegOnePeriodic_of_sector_winWittAgree`, `not_sector_winWittAgree_lcmPeriod`, `sectorWinWittAgree_of_sectorWideRowAgree`, `sectorWinWittAgree_of_sectorWideRightRowAgree`, `not_sectorWideRightRowAgree_lcmPeriod`, `lhCenter_zero_eq_center`, `lhCenter_self_eq_true`, `lhCenter_gt_eq_false`, `lhCenter_step_succ`, `lhCenter_outward_step`, `center_eq_rhCenter_inward_zero`, `periodic_rhCenter_step_one_eq_of_or_eq`, `periodic_rhCenter_or_eq_of_step_one_eq`, `rhBandAgree_steps`, `periodic_rhBandAgree_zero_of_one`, `periodic_rhBandAgree_zero_step`, `periodic_rhBandAgree_zero_steps`, `rhBandAgree_extend_inward_steps`, `rhBandAgree_zero_of_edge_and_succ`, `periodic_rhBandAgree_bounce_zero`, `periodic_rhBandAgree_bounce_succ`, `rhCenter_one_periodic_of_sector_rhBandAgree`, `lhCenter_one_periodic_of_sector_rhBandAgree`, `rhCenter_diag_shift_twopow_eq`, `rhCenter_sector_diag_eq_center`, `rhCenter_scale_step`, `rhCenter_scale_inward_step`):**
       - **Unfolding the §6 `Φ` Recombination Operator (`Phi`, `Lh`, `Rh`):** Exposes the §6 driven right half `rhCenter t p = Rh center t p` (`= rdiag (t - p) t = (row t).testBit (t - p)`) and driven left half `lhCenter t p = Lh center t (-p)` (`= ldiag (t - p) t = (row t).testBit (t + p)`), unfolds `phiCenter t = bxor (lhCenter t 1) (center t || rhCenter t 1)`, and solves the `Φ` fixed-point law `center (t + 1) = phiCenter t` (`center_fixed_readout`) for `lhCenter t 1 = bxor (center (t + 1)) (center t || rhCenter t 1)`. Under `CenterPeriodic T P`, this locks the `m * P`-defect of `lhCenter · 1` to `!center t && (rhCenter (t + m * P) 1 ⊕ rhCenter t 1)`.
       - **Inward Step Law in the Right Half & Pure Right-Half Center Law:** Because Rule 30 is left-permutive, in the right half `rhCenter (t + 1) (p + 1) = bxor (rhCenter t p) (rhCenter t (p + 1) || rhCenter t (p + 2))` solves **inward from the right edge toward column 1**: `rhCenter t p = bxor (rhCenter (t + 1) (p + 1)) (rhCenter t (p + 1) || rhCenter t (p + 2))` (`rhCenter_inward_step`), while in the left half it solves **outward from the center toward the left edge** (`lhCenter_outward_step`). Evaluating `rhCenter_inward_step` at `p = 0` yields the pure right-half center identity `center t = bxor (rhCenter (t + 1) 1) (rhCenter t 1 || rhCenter t 2)` (`center_eq_rhCenter_inward_zero`). At scale `2^k`, `rhCenter (t + 2^k) (p + 2^k)` evolves linearly (via `bxor`) from `rhCenter t p`, `rhCenter t (p + 2^k)`, and `rhCenter t (p + 2^(k+1))` plus `(winWitt t (2^k)).testBit (t - p)` (`rhCenter_scale_step`, `rhCenter_scale_inward_step`).
       - **Center-Anchored Forward Propagation & Center-Bounce Inward Extension of `RhBandAgree`:** While a generic right-half band `RhBandAgree t Q p0 (L + 2)` shifts `p0 ↦ p0 + 1` and loses 2 columns per forward step (`rhBandAgree_step`, `rhBandAgree_steps`), at `p0 = 0` under `CenterPeriodic T P` (`Q = m * P`), column `0` (`rhCenter · 0 = center ·`) is resupplied at every step, so `RhBandAgree t (m * P) 0 (L + s)` steps forward to `RhBandAgree (t + s) (m * P) 0 L` losing only 1 column on the right and 0 on the left (`periodic_rhBandAgree_zero_step`, `periodic_rhBandAgree_zero_steps`). Dually, `S` inward steps (`rhBandAgree_extend_inward_steps`) combine with `periodic_rhBandAgree_zero_of_one` so that agreement starting at column `2` at time `t + 1` (`RhBandAgree (t + 1) (m * P) 2 S`) plus `RhBandAgree t (m * P) (S + 1) (L + 1)` marches inward to column `1` at time `t`, picks up column `0` from the periodic center (`periodic_rhBandAgree_bounce_zero`), and bounces forward off `(t, 0)` to determine column `1` and column `0` at time `t + 1` (`periodic_rhBandAgree_bounce_succ`).
       - **Direct Right-Half-to-`Φ` Sector Propagation & Window Step 9.204 Sector Refutations:** `periodic_rhBandAgree_zero_steps` carries `SectorRhBandAgree k d U (m * P)` across all residues `mod 2^k` purely inside the right half to establish `rhCenter (t + m * P) 1 = rhCenter t 1` for every `t ≥ (d + U * 2^k) + 1` (`rhCenter_one_periodic_of_sector_rhBandAgree`), and `lhCenter_one_eq_of_center_fixed` immediately transfers this across the `Φ` fixed point to `lhCenter (t + m * P) 1 = lhCenter t 1` (`lhCenter_one_periodic_of_sector_rhBandAgree`), refuting `SectorRhBandAgree` at `Q = lcm(P, 2^k)` (`not_sector_rhBandAgree_lcmPeriod`). Likewise, `s < 2^k` steps of Window Step 9.204 (`winWittAgree_steps` with `L = 1`) carry `SectorWinWittAgree k d U Q` (and `SectorWideRowAgree` / `SectorWideRightRowAgree`) across all residues `mod 2^k` to `ColNegOnePeriodic (d + (U + 1) * 2^k) Q`, refuting `SectorWinWittAgree` and `SectorWideRightRowAgree` at `Q = lcm(P, 2^k)` (`not_sector_winWittAgree_lcmPeriod`, `not_sectorWideRightRowAgree_lcmPeriod`).
       - **Inward Column-and-OR Time-Trace Determination, Outside-the-Cone Zero Band, and Scale-Step Band Calculus (`RhColAgree`, `RhOrAgree`, `rhBandAgree_mono`, `rhColAgree_mono`, `rhOrAgree_mono`, `rhOrAgree_of_col_agree`, `periodic_rhOrAgree_one_of_col_one`, `periodic_col_one_of_rhOrAgree_one`, `rhCenter_inward_determine_step`, `rhCenter_inward_determine`, `rhBandAgree_of_inward_determine`, `rhBandAgree_outside_cone`, `rhBandAgree_scale_step`, `rhBandAgree_scale_inward_step`, `winWittAgree_of_rhBandAgree_scale`, `sectorRhBandAgree_of_inward_determine`, `not_sector_inward_determine_lcmPeriod`):**
         - `RhColAgree t Q p0 S` and `RhOrAgree t Q p0 S` track `Q`-agreement of column `p0` over `0 ≤ s ≤ S` and of the adjacent OR `rhCenter · p0 || rhCenter · (p0 + 1)` over `0 ≤ s < S`. Under `CenterPeriodic T P` (`Q = m * P`), at `p0 = 1`, `RhOrAgree t (m * P) 1 S` is **equivalent** to `RhColAgree (t + 1) (m * P) 1 (S - 1)` (`periodic_rhOrAgree_one_of_col_one`, `periodic_col_one_of_rhOrAgree_one`), and `RhColAgree t Q (p0 + K) (S + K)` plus `RhOrAgree t Q (p0 + K) (S + K)` determines every intermediate column and OR inward down to `p0` (`rhCenter_inward_determine_step`, `rhCenter_inward_determine`), yielding `RhBandAgree t Q p0 K` (`rhBandAgree_of_inward_determine`), `SectorRhBandAgree` (`sectorRhBandAgree_of_inward_determine`), and a direct refutation at `Q = lcm(P, 2^k)` (`not_sector_inward_determine_lcmPeriod`).
         - Outside the light cone (`t < p0`), `rhCenter (t + Q) (p0 + j) = false = rhCenter t (p0 + j)` for all `j` (`2^k ∣ Q`, `Q = v * 2^k`), giving unconditional `RhBandAgree t (v * 2^k) p0 L` (`rhBandAgree_outside_cone`), while across scale `2^k`, `RhBandAgree` and `WinWittAgree` mutually determine one another (`rhBandAgree_scale_step`, `rhBandAgree_scale_inward_step`, `winWittAgree_of_rhBandAgree_scale`).
       - **Unrestricted `2^k`-Scale `rhCenter` Laws (`p ≤ t`), Multi-Band Inward Scale Iteration, Black-Cell Masking, `Z_down` Splitting, and Right-Threshold Geometry in `rhCenter` (`rhCenter_scale_step_le`, `rhCenter_scale_inward_step_le`, `rhBandAgree_scale_step_le`, `rhBandAgree_scale_inward_step_le`, `winWittAgree_of_rhBandAgree_scale_le`, `rhBandAgree_scale_inward_steps`, `rhCenter_inward_of_black_left`, `rhCenter_inward_of_black_right`, `rhCenter_agree_of_black_left`, `rhCenter_white_pair_of_diag_eq`, `rhCenter_diag_eq_of_white_pair`, `rhCenter_diag_shift_twopow_eq_of_threshold`, `rhCenter_sector_diag_eq_center_of_threshold`, `rhCenter_zero_gap_of_threshold`, `rhCenter_last_one_of_threshold`):**
         - Because `rhCenter t q = false` outside the light cone (`q > t`), the `2^k`-scale step and inward step identities hold for ALL `p ≤ t` right up to the right edge (`rhCenter_scale_step_le`, `rhCenter_scale_inward_step_le`), weakening `p0 + L + 2^(k+1) ≤ t` to `p0 + L ≤ t` (`rhBandAgree_scale_step_le`, `rhBandAgree_scale_inward_step_le`, `winWittAgree_of_rhBandAgree_scale_le`) and iterating `M` scale steps inward across `M * 2^k` columns (`rhBandAgree_scale_inward_steps`).
         - A black cell at `p + 1` or `p + 2` masks its neighbour in the inward step (`rhCenter t p = !rhCenter (t + 1) (p + 1)`), allowing inward `Q`-agreement across a black column without needing column `p + 2` (`rhCenter_inward_of_black_left`, `rhCenter_inward_of_black_right`, `rhCenter_agree_of_black_left`), whereas a constant diagonal step `rhCenter (t + 1) (p + 1) = rhCenter t p` splits into both `rhCenter t (p + 1) = false` and `rhCenter t (p + 2) = false` (`rhCenter_white_pair_of_diag_eq`, `rhCenter_diag_eq_of_white_pair`).
         - Below the right-period threshold `IsRightThreshold k J` (`J ≥ k`), `rhCenter` satisfies diagonal shift invariance (`rhCenter_diag_shift_twopow_eq_of_threshold`), sector-column center readout (`rhCenter_sector_diag_eq_center_of_threshold`), a white zero-gap of width `J` at every multiple `u * 2^k` (`rhCenter_zero_gap_of_threshold`), and a black run of width `J + 1` at `(u + 1) * 2^k - 1` (`rhCenter_last_one_of_threshold`).
- Paper section "Witt forms and linear interfaces" (`glossary/r30.witt`, `src/Paper.lex.tex`,
  attestation 99c102da03e58403d0240f12cdee3cac699532b85d13b58dcf11700d0d255668, 486 theorems in Section 9):
  `witt-split`, `parity-interface`, `cyclotomic-first-interface`,
  `cyclotomic-second-interface`, `witt-row-rdiag`, `witt-center-rcenter`, `witt-center-cell`,
  `witt-noperiod-sufficient`, `witt-noperiod-necessary`, `witt-freshman`, `witt-duhamel`,
  `witt-scale-row`, `witt-scale-cone`, `witt-cone-duality`, `witt-late-center`, `two-places-witt`,
  `maskparity-coboundary`, `ldiag-response-coboundary`, `ldiag-leftresponse-coboundary`,
  `two-places-witt-coboundary`, `rdiag-scale`, `two-places-settled`,
  `zcenter-leftresponse-coboundary`, `damage-witt-coboundary`, `zcenter-zero`,
  `zcenter-after-zero`, `zcenter-oscillates`, `leftresponse-coboundary-zero`,
  `leftresponse-coboundary-after-zero`, `witt-coboundary-zero`, `witt-coboundary-after-zero`,
  `periodic-response-lag`, `periodic-witt-lag`, `periodic-left-mask-lag`,
  `periodic-late-response-lag`, `periodic-late-witt-lag`, `periodic-late-left-mask-lag`,
  `winwitt-ray-zero`, `winwitt-low-zero`, `winwitt-ray-one`, `winwitt-ray-two`,
  `winwitt-archimedean`, `winwitt-settled-zero`, `winwitt-degree`, `right-threshold-exists`,
  `winwitt-threshold-gap`, `winwitt-threshold-lead`, `threshold-lt-center-black`,
  `winwitt-cyclotomic-first`, `winwitt-cyclotomic-second`, `winwitt-parity`,
  `witt-carry-xor`, `witt-phi-xor`, `winwitt-base-step`, `winwitt-cone-step`,
  `winwitt-triality-outside`, `winwitt-sector-one-cone`, `winwitt-center-slot`,
  `winwitt-sector-one-below-thresh`, `winwitt-sector-one-at-thresh`,
  `threshold-center-antiperiod`, `threshold-center-witt-resp`,
  `phiscale-row-cone-step`, `winwitt-unperturbed-sector-zero`,
  `winwitt-unperturbed-sector-one-gap`, `winwitt-sector-one-gap-ldiag`,
  `winwitt-sector-one-cone-edge`, `ldiag-eq-rdiag`, `rdiag-threshold-sub-ldiag`,
  `rdiag-threshold-succ-not-ldiag`, `winwitt-sector-one-ldiag`,
  `winwitt-top-edge-zero`, `winwitt-second-edge-zero`,
  `rdiag-threshold-late-false-window`, `rdiag-threshold-late-true-plateau`,
  `rdiag-threshold-late-false-odd-hit`, `rdiag-threshold-late-false-even-hit`,
  `rdiag-threshold-plus-two-step-neg`, `winwitt-thresh-plus-two-freeze`,
  `ldiag-two-false`, `winwitt-third-edge-zero`, `ldiag-three-step-neg`,
  `winwitt-sector-one-settled`, `rdiag-eq-ldiag-settled-below-thresh`,
  `rdiag-not-ldiag-settled-at-thresh`, `winwitt-sector-two-scale-eq`,
  `center-late-xor-ldiag-witt`, `periodic-ldiag-xor-late-witt-lag`,
  `periodic-response-shift-p`, `periodic-witt-shift-p`,
  `periodic-winwitt-sector-one-shift-p`, `periodic-late-response-unsettled-decomp`,
  `periodic-zcenter-from-lag-late-response`, `periodic-zcenter-shift-xor-late-response`,
  `periodic-zcenter-shift-xor-late-witt`, `exists-settled-scale-pair`,
  `zcenter-not-periodic-one`, `zcenter-not-periodic-two`,
  `zcenter-periodic-not-zero-diag-shift`, `winwitt-scale-cocycle`,
  `witt-resp-late-from-early-triality`, `periodic-late-witt-from-lag-sector-two`,
  `periodic-late-maskparity-decomp`, `leftresponse-zero`, `response-zero-maskparity`,
  `maskparity-step-diff`, `maskparity-succ-zero-rdiag`,
  `maskparity-zero-periodic-of-maskedper`, `maskedper-of-maskparity-zero-periodic`,
  `maskparity-periodic-of-maskedper`, `periodic-maskparity-shift-p-cone`,
  `periodic-maskparity-zero-dyadic-jump-cone`,
  `periodic-maskparity-zero-defect-dyadic-jump-cone`,
  `periodic-late-maskparity-shift-p`, `periodic-late-maskparity-zero-dyadic-jump`,
  `periodic-late-maskparity-zero-defect-dyadic-jump`,
  `periodic-late-leftresponse-unsettled-decomp`,
  `periodic-zcenter-from-lag-late-left-mask`,
  `periodic-maskparity-zero-defect-colm1-defect`,
  `rdiag-late-eq-witt-xor-left-mask`, `two-halves-witt-scale`,
  `ldiag-leftresponse-coboundary-cone`, `two-halves-witt-coboundary-cone`,
  `periodic-maskparity-late-cone`, `periodic-two-halves-scale-eq`,
  `periodic-rdiag-late-from-left-and-center`, `rdiag-below-threshold-eq-center`,
  `periodic-two-halves-below-threshold`, `periodic-center-xor-witt-below-threshold`,
  `periodic-two-halves-at-threshold`, `periodic-not-center-xor-witt-at-threshold`,
  `threshold-center-left-mask-eq-not-rdiag`,
  `sector-one-below-threshold-eq-left-settled`,
  `sector-one-at-threshold-eq-left-settled`,
  `rdiag-defect-step-below-threshold`, `rdiag-threshold-plus-two-defect-step`,
  `rdiag-threshold-plus-two-defect-step-ldiag`,
  `rdiag-threshold-plus-two-center-decomp`,
  `periodic-two-halves-at-threshold-plus-two`,
  `periodic-center-xor-witt-at-threshold-plus-two`,
  `ldiag-damage-step-of-settled`,
  `ldiag-damage-step-of-settled-pair`,
  `two-halves-off-center-witt-scale`,
  `off-center-witt-scale-settled-below-threshold`,
  `off-center-witt-scale-settled-at-threshold`,
  `colm1-dyadic-jump-eq-maskparity-zero-jump`,
  `periodic-colm1-dyadic-jump-eq-leftresponse-diff`,
  `periodic-off-center-witt-below-threshold-eq-leftresponse`,
  `periodic-off-center-witt-at-threshold-eq-not-leftresponse`,
  `rdiag-threshold-plus-two-defect-cone`,
  `rdiag-threshold-plus-two-defect-two-step`,
  `carry-row-scale-decomp`,
  `carry-row-scale-cone`,
  `carry-winwitt-late-decomp`,
  `periodic-crosscarry-center-slot-and`,
  `periodic-crosscarry-colm1-and`,
  `crosscarry-row-scale-at-threshold-eq-rdiag`,
  `carry-row-scale-at-threshold`,
  `periodic-winwitt-step-center-slot-expanded`,
  `periodic-crosscarry-at-center-bit-and`,
  `periodic-crosscarry-at-white-center-eq-maskparity`,
  `carry-row-xor-maskparity-zero-eq-col1`,
  `periodic-crosscarry-colm1-at-white-center`,
  `periodic-crosscarry-colm1-white-center-lag-eq`,
  `crosscarry-row-scale-sector-two-colm1-and`,
  `crosscarry-row-scale-sector-two-colm1-at-white-center`,
  `periodic-crosscarry-sector-one-xor-two-colm1-and`,
  `phiscale-winwitt-triality-low`,
  `periodic-crosscarry-winwitt-cocycle-colm1-and`,
  `carry-row-late-at-threshold-center-eq-maskparity`,
  `maskparity-zero-dyadic-jump-eq-witt-carry-crosscarry`,
  `maskparity-zero-dyadic-jump-eq-not-witt-and-xor-crosscarry`,
  `maskparity-dyadic-jump-eq-crosscarry-of-wittresp-true`,
  `maskparity-dyadic-jump-eq-not-center-and-witt-of-wittresp-false`,
  `periodic-leftresponse-step-diff-eq-crosscarry-of-out-of-phase`,
  `crosscarry-winwitt-cocycle-at-threshold-succ`,
  `crosscarry-row-scale-eq-crosscarry-late-row`,
  `periodic-crosscarry-colm1-wronskian`,
  `crosscarry-row-scale-sector-two-colm1-wronskian`,
  `maskparity-zero-and-center-eq-false`,
  `periodic-colm1-defect-and-center-eq-false`,
  `periodic-crosscarry-colm1-shift-p-eq-leftresponse-and-witt`,
  `periodic-crosscarry-colm1-shift-p-eq-of-wittresp-false`,
  `periodic-leftresponse-step-diff-eq-witt-of-in-phase-black`,
  `phiscale-row-testbit-outside-cone`,
  `winwitt-testbit-outside-cone`,
  `periodic-crosscarry-colm1-outside-cone-and`,
  `periodic-crosscarry-colm1-outside-cone-wronskian`,
  `periodic-crosscarry-colm1-outside-cone-at-white-center`,
  `periodic-crosscarry-colm1-outside-cone-at-both-white-centers`,
  `crosscarry-colm1-at-white-late-center-eq-and-witt`,
  `crosscarry-colm1-outside-cone-at-white-late-center-via-response`,
  `crosscarry-row-scale-at-center-bit-outside-cone-and`,
  `crosscarry-at-white-center-outside-cone-noncenter-and`,
  `crosscarry-at-center-bit-outside-cone-wronskian`,
  `periodic-crosscarry-at-both-white-centers-outside-cone-eq-maskparity`,
  `crosscarry-at-white-late-center-eq-witt-and-maskparity`,
  `periodic-maskparity-zero-defect-mul-eq-colm1-defect-mul`,
  `wittresp-xor-response-shift-mul-outside-cone`,
  `periodic-wittresp-shift-mul-outside-cone`,
  `periodic-crosscarry-colm1-shift-mul-at-white-late-center`,
  `periodic-crosscarry-center-bit-shift-mul-at-white-late-center`,
  `frobdefect-row-cone-eq-zero`,
  `winwitt-step-frobdefect`,
  `winwitt-step-frobdefect-testbit-succ`,
  `frobdefect-row-testbit-outside-cone`,
  `frobdefect-row-center-slot-outside-cone`,
  `frobdefect-row-center-slot-at-white-center-outside-cone`,
  `frobdefect-row-colm1-slot-outside-cone`,
  `frobdefect-row-colm1-slot-at-white-center-outside-cone`,
  `frobdefect-row-col1-slot-outside-cone`,
  `frobdefect-row-col1-slot-at-white-center-outside-cone`,
  `periodic-winwitt-step-center-slot-outside-cone`,
  `periodic-winwitt-step-center-slot-at-white-late-center-outside-cone`,
  `periodic-winwitt-step-center-slot-at-both-white-centers-outside-cone`,
  `periodic-winwitt-step-colm1-slot-outside-cone`,
  `periodic-winwitt-step-colm1-slot-at-both-white-centers-outside-cone`,
  `periodic-winwitt-step-col1-slot-outside-cone`,
  `periodic-winwitt-step-center-slot-shift-mul-at-white-late-center`,
  `frobdefect-xor`,
  `frobdefect-phiscale-row-cone-eq-zero`,
  `frobdefect-row-late-from-cone`,
  `frobdefect-row-late-center-slot-rperiodic`,
  `frobdefect-row-late-center-slot-at-both-white-centers-eq-zcenter-and-maskparity-jump`,
  `frobdefect-row-late-colm1-slot-rperiodic`,
  `frobdefect-row-late-colm1-slot-of-in-phase-eq-colm1-jump-and-damage`,
  `frobdefect-row-late-colm1-xor-center-slot-at-both-white-centers`,
  `periodic-winwitt-step-late-center-slot-at-white-centers-eq-zcenter-and-maskparity-triality`,
  `periodic-winwitt-step-late-colm1-slot-at-white-centers-eq-zcenter-and-colm1-triality`,
  `wittresp-late-eq-zcenter-xor-center-triality`,
  `wittresp-late-at-white-centers-eq-zcenter`,
  `periodic-wittresp-late-shift-mul-eq-zcenter-xor`,
  `periodic-crosscarry-late-center-bit-shift-mul-at-white-centers`,
  `periodic-crosscarry-late-colm1-shift-mul-at-white-centers`,
  `periodic-winwitt-step-late-center-slot-shift-mul-at-white-centers`,
  `rdiag-restart`,
  `rdiag-restart-of-threshold`,
  `center-restart-rdiag`,
  `frobdefect-row-lt-twopow`,
  `frobdefect-row-sector-one`,
  `frobdefect-row-sector-one-restart`,
  `frobdefect-row-sector-two-restart`,
  `frobdefect-winwitt-sector-two-wronskian`,
  `crosscarry-scale-row-winwitt-sector-two-cone-eq`,
  `frobdefect-row-late-eq-frobdefect-winwitt-sector-two`,
  `frobdefect-row-late-eq-winwitt-sector-two-wronskian`,
  `periodic-ldiag-shift-mul-eq-response-shift-mul`,
  `not-periodic-maskparity-zero-mul`,
  `not-periodic-colm1-mul`,
  `phiscale-row-late-sector-one-eq-winwitt-cone`,
  `frobdefect-row-late-sector-one-eq-crosscarry-cone`,
  `frobdefect-row-late-sector-one-center-slot-wronskian`,
  `crosscarry-row-winwitt-sector-two-center-slot`,
  `ldiag-settled-restart`,
  `zcenter-restart-ldiag`,
  `frobdefect-row-late-center-slot-of-zcenter-true`,
  `periodic-winwitt-step-late-center-slot-of-zcenter-true`,
  `periodic-winwitt-step-late-colm1-slot-of-zcenter-true`,
  `rowagree-mono`,
  `winwittagree-mono`,
  `rowagree-step`,
  `rowagree-steps`,
  `phiscale-row-testbit-eq-of-rowagree`,
  `frobdefect-row-testbit-eq-of-rowagree`,
  `crosscarry-testbit-eq-of-rowagree-winwittagree`,
  `winwittagree-step`,
  `winwittagree-steps`,
  `wittrespbool-eq-of-winwittagree-steps`,
  `colm1-eq-of-rowagree-steps`,
  `maskparity-zero-eq-of-rowagree-steps`,
  `colnegoneperiodic-of-sector-rowagree`,
  `not-sector-rowagree-mul`,
  `rdiag-lcmperiod-eq`,
  `ldiag-lcmperiod-eq`,
  `center-lcmperiod-eq`,
  `not-sector-rowagree-lcmperiod`,
  `rowagree-extend-right`,
  `periodic-rowagree-center`,
  `periodic-rowagree-black-center`,
  `periodic-rowagree-symm-of-right`,
  `periodic-rowagree-lcmperiod-symm-of-right`,
  `colnegoneperiodic-of-sector-right-rowagree`,
  `not-sector-right-rowagree-lcmperiod`,
  `winwittagree-extend-right`,
  `winwittagree-of-rowagree-three-and-late`,
  `rowagree-late-of-winwittagree-and-three`,
  `wittrespbool-periodic-of-sector-winwittagree`,
  `right-boundary-row-lcmperiod-eq`,
  `left-boundary-row-lcmperiod-eq`,
  `frobdefect-row-sector-one-lcmperiod-xor`,
  `rhcenter-eq-rdiag`,
  `rhcenter-eq-row-testbit`,
  `lhcenter-eq-ldiag`,
  `lhcenter-eq-row-testbit`,
  `rhcenter-zero-eq-center`,
  `rhcenter-self-eq-true`,
  `rhcenter-gt-eq-false`,
  `phicenter-eq-lhcenter-rhcenter`,
  `lhcenter-one-eq-of-center-fixed`,
  `periodic-lhcenter-one-defect-eq-not-center-and-rhcenter-one-defect`,
  `rhcenter-step-succ`,
  `rhcenter-inward-step`,
  `rhbandagree-extend-inward`,
  `rhbandagree-step`,
  `rowagree-right-of-rhbandagree`,
  `rhbandagree-of-rowagree-right`,
  `sectorrightrowagree-of-rhbandagree`,
  `not-sector-rhbandagree-lcmperiod`,
  `rhcenter-right-edge-lcmperiod-eq`,
  `colnegoneperiodic-of-sector-winwittagree`,
  `not-sector-winwittagree-lcmperiod`,
  `sectorwinwittagree-of-sectorwiderowagree`,
  `sectorwinwittagree-of-sectorwiderightrowagree`,
  `not-sectorwiderightrowagree-lcmperiod`,
  `lhcenter-zero-eq-center`,
  `lhcenter-self-eq-true`,
  `lhcenter-gt-eq-false`,
  `lhcenter-step-succ`,
  `lhcenter-outward-step`,
  `center-eq-rhcenter-inward-zero`,
  `periodic-rhcenter-step-one-eq-of-or-eq`,
  `periodic-rhcenter-or-eq-of-step-one-eq`,
  `rhbandagree-steps`,
  `periodic-rhbandagree-zero-of-one`,
  `periodic-rhbandagree-zero-step`,
  `periodic-rhbandagree-zero-steps`,
  `rhbandagree-extend-inward-steps`,
  `rhbandagree-zero-of-edge-and-succ`,
  `periodic-rhbandagree-bounce-zero`,
  `periodic-rhbandagree-bounce-succ`,
  `rhcenter-one-periodic-of-sector-rhbandagree`,
  `lhcenter-one-periodic-of-sector-rhbandagree`,
  `rhcenter-diag-shift-twopow-eq`,
  `rhcenter-sector-diag-eq-center`,
  `rhcenter-scale-step`,
  `rhcenter-scale-inward-step`,
  `rhbandagree-mono`,
  `rhcolagree-mono`,
  `rhoragree-mono`,
  `rhoragree-of-col-agree`,
  `periodic-rhoragree-one-of-col-one`,
  `periodic-col-one-of-rhoragree-one`,
  `rhcenter-inward-determine-step`,
  `rhcenter-inward-determine`,
  `rhbandagree-of-inward-determine`,
  `rhbandagree-outside-cone`,
  `rhbandagree-scale-step`,
  `rhbandagree-scale-inward-step`,
  `winwittagree-of-rhbandagree-scale`,
  `sectorrhbandagree-of-inward-determine`,
  `not-sector-inward-determine-lcmperiod`,
  `rhcenter-scale-step-le`,
  `rhcenter-scale-inward-step-le`,
  `rhbandagree-scale-step-le`,
  `rhbandagree-scale-inward-step-le`,
  `winwittagree-of-rhbandagree-scale-le`,
  `rhbandagree-scale-inward-steps`,
  `rhcenter-inward-of-black-left`,
  `rhcenter-inward-of-black-right`,
  `rhcenter-agree-of-black-left`,
  `rhcenter-white-pair-of-diag-eq`,
  `rhcenter-diag-eq-of-white-pair`,
  `rhcenter-diag-shift-twopow-eq-of-threshold`,
  `rhcenter-sector-diag-eq-center-of-threshold`,
  `rhcenter-zero-gap-of-threshold`,
  `rhcenter-last-one-of-threshold` (attestation `0b7fdeae…`), plus
  `antiperiodic-doubling` in section `compile-points`.
- Bridge `Rule30Bridge` (54/54 targets built): `row_testBit_eq_R`, `rowCenter_eq_kit_center`,
  `problem1_iff_noRowCenterPeriod`, `two_places_witt_kit`, `two_places_witt_coboundary_kit`,
  `winwitt_ray_zero_kit`, `winwitt_ray_one_kit`, `winwitt_ray_two_kit`, `winwitt_cone_step_kit`,
  `winwitt_triality_outside_kit`, `winwitt_center_slot_kit`, `threshold_center_antiperiod_kit`,
  `phiscale_row_cone_step_kit`, `winwitt_unperturbed_sector_zero_kit`, `ldiag_eq_rdiag_kit`,
  `winwitt_sector_one_ldiag_kit`, `rdiag_threshold_late_true_plateau_kit`,
  `winwitt_thresh_plus_two_freeze_kit`, `rdiag_eq_ldiag_settled_below_thresh_kit`,
  `winwitt_sector_two_scale_eq_kit`, `center_late_xor_ldiag_witt_kit`,
  `periodic_ldiag_xor_late_witt_lag_kit`, `periodic_late_response_unsettled_decomp_kit`,
  `periodic_zcenter_from_lag_late_response_kit`, `periodic_zcenter_shift_xor_late_response_kit`,
  `zcenter_not_periodic_one_kit`, `zcenter_not_periodic_two_kit`,
  `zcenter_periodic_not_zero_diag_shift_kit`, `winwitt_scale_cocycle_kit`,
  `witt_resp_late_from_early_triality_kit`, `periodic_late_witt_from_lag_sector_two_kit`,
  `periodic_late_maskparity_decomp_kit`, `leftresponse_zero_kit`,
  `response_zero_maskparity_kit`, `maskparity_step_diff_kit`,
  `maskparity_succ_zero_rdiag_kit`, `maskparity_zero_periodic_of_maskedper_kit`,
  `maskedper_of_maskparity_zero_periodic_kit`, `maskparity_periodic_of_maskedper_kit`,
  `periodic_maskparity_shift_p_cone_kit`, `periodic_maskparity_zero_dyadic_jump_cone_kit`,
  `periodic_maskparity_zero_defect_dyadic_jump_cone_kit`,
  `periodic_late_maskparity_shift_p_kit`, `periodic_late_maskparity_zero_dyadic_jump_kit`,
  `periodic_late_maskparity_zero_defect_dyadic_jump_kit`,
  `periodic_late_leftresponse_unsettled_decomp_kit`,
  `periodic_zcenter_from_lag_late_left_mask_kit`,
  `periodic_maskparity_zero_defect_colm1_defect_kit`,
  `rdiag_late_eq_witt_xor_left_mask_kit`, `two_halves_witt_scale_kit`,
  `ldiag_leftresponse_coboundary_cone_kit`, `two_halves_witt_coboundary_cone_kit`,
  `periodic_two_halves_scale_eq_kit`, `periodic_rdiag_late_from_left_and_center_kit`,
  `periodic_two_halves_below_threshold_kit`, `periodic_two_halves_at_threshold_kit`,
  `periodic_not_center_xor_witt_at_threshold_kit`,
  `sector_one_below_threshold_eq_left_settled_kit`,
  `sector_one_at_threshold_eq_left_settled_kit`,
  `rdiag_threshold_plus_two_defect_step_kit`,
  `rdiag_threshold_plus_two_defect_step_ldiag_kit`,
  `rdiag_threshold_plus_two_center_decomp_kit`,
  `periodic_two_halves_at_threshold_plus_two_kit`,
  `ldiag_damage_step_of_settled_pair_kit`,
  `two_halves_off_center_witt_scale_kit`,
  `off_center_witt_scale_settled_below_threshold_kit`,
  `off_center_witt_scale_settled_at_threshold_kit`,
  `colm1_dyadic_jump_eq_maskparity_zero_jump_kit`,
  `periodic_colm1_dyadic_jump_eq_leftresponse_diff_kit`,
  `periodic_off_center_witt_below_threshold_eq_leftresponse_kit`,
  `periodic_off_center_witt_at_threshold_eq_not_leftresponse_kit`,
  `rdiag_threshold_plus_two_defect_cone_kit`,
  `rdiag_threshold_plus_two_defect_two_step_kit`,
  `carry_row_scale_decomp_kit`,
  `carry_row_scale_cone_kit`,
  `carry_winwitt_late_decomp_kit`,
  `periodic_crosscarry_center_slot_and_kit`,
  `periodic_crosscarry_colm1_and_kit`,
  `crosscarry_row_scale_at_threshold_eq_rdiag_kit`,
  `carry_row_scale_at_threshold_kit`,
  `periodic_winwitt_step_center_slot_expanded_kit`,
  `periodic_crosscarry_at_center_bit_and_kit`,
  `periodic_crosscarry_at_white_center_eq_maskparity_kit`,
  `carry_row_xor_maskparity_zero_eq_col1_kit`,
  `periodic_crosscarry_colm1_at_white_center_kit`,
  `periodic_crosscarry_colm1_white_center_lag_eq_kit`,
  `crosscarry_row_scale_sector_two_colm1_and_kit`,
  `crosscarry_row_scale_sector_two_colm1_at_white_center_kit`,
  `periodic_crosscarry_sector_one_xor_two_colm1_and_kit`,
  `phiscale_winwitt_triality_low_kit`,
  `periodic_crosscarry_winwitt_cocycle_colm1_and_kit`,
  `carry_row_late_at_threshold_center_eq_maskparity_kit`,
  `maskparity_zero_dyadic_jump_eq_witt_carry_crosscarry_kit`,
  `maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crosscarry_kit`,
  `maskparity_dyadic_jump_eq_crosscarry_of_wittresp_true_kit`,
  `maskparity_dyadic_jump_eq_not_center_and_witt_of_wittresp_false_kit`,
  `periodic_leftresponse_step_diff_eq_crosscarry_of_out_of_phase_kit`,
  `crosscarry_winwitt_cocycle_at_threshold_succ_kit`,
  `crosscarry_row_scale_eq_crosscarry_late_row_kit`,
  `periodic_crosscarry_colm1_wronskian_kit`,
  `crosscarry_row_scale_sector_two_colm1_wronskian_kit`,
  `maskparity_zero_and_center_eq_false_kit`,
  `periodic_colm1_defect_and_center_eq_false_kit`,
  `periodic_crosscarry_colm1_shift_p_eq_leftresponse_and_witt_kit`,
  `periodic_crosscarry_colm1_shift_p_eq_of_wittresp_false_kit`,
  `periodic_leftresponse_step_diff_eq_witt_of_in_phase_black_kit`,
  `phiscale_row_testbit_outside_cone_kit`,
  `winwitt_testbit_outside_cone_kit`,
  `periodic_crosscarry_colm1_outside_cone_and_kit`,
  `periodic_crosscarry_colm1_outside_cone_wronskian_kit`,
  `periodic_crosscarry_colm1_outside_cone_at_white_center_kit`,
  `periodic_crosscarry_colm1_outside_cone_at_both_white_centers_kit`,
  `crosscarry_colm1_at_white_late_center_eq_and_witt_kit`,
  `crosscarry_colm1_outside_cone_at_white_late_center_via_response_kit`,
  `crosscarry_row_scale_at_center_bit_outside_cone_and_kit`,
  `crosscarry_at_white_center_outside_cone_noncenter_and_kit`,
  `crosscarry_at_center_bit_outside_cone_wronskian_kit`,
  `periodic_crosscarry_at_both_white_centers_outside_cone_eq_maskparity_kit`,
  `crosscarry_at_white_late_center_eq_witt_and_maskparity_kit`,
  `periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul_kit`,
  `wittresp_xor_response_shift_mul_outside_cone_kit`,
  `periodic_wittresp_shift_mul_outside_cone_kit`,
  `periodic_crosscarry_colm1_shift_mul_at_white_late_center_kit`,
  `periodic_crosscarry_center_bit_shift_mul_at_white_late_center_kit`,
  `frobdefect_row_cone_eq_zero_kit`,
  `winwitt_step_frobdefect_kit`,
  `winwitt_step_frobdefect_testbit_succ_kit`,
  `frobdefect_row_testbit_outside_cone_kit`,
  `frobdefect_row_center_slot_outside_cone_kit`,
  `frobdefect_row_center_slot_at_white_center_outside_cone_kit`,
  `frobdefect_row_colm1_slot_outside_cone_kit`,
  `frobdefect_row_colm1_slot_at_white_center_outside_cone_kit`,
  `frobdefect_row_col1_slot_outside_cone_kit`,
  `frobdefect_row_col1_slot_at_white_center_outside_cone_kit`,
  `periodic_winwitt_step_center_slot_outside_cone_kit`,
  `periodic_winwitt_step_center_slot_at_white_late_center_outside_cone_kit`,
  `periodic_winwitt_step_center_slot_at_both_white_centers_outside_cone_kit`,
  `periodic_winwitt_step_colm1_slot_outside_cone_kit`,
  `periodic_winwitt_step_colm1_slot_at_both_white_centers_outside_cone_kit`,
  `periodic_winwitt_step_col1_slot_outside_cone_kit`,
  `periodic_winwitt_step_center_slot_shift_mul_at_white_late_center_kit`,
  `frobdefect_xor_kit`,
  `frobdefect_phiscale_row_cone_eq_zero_kit`,
  `frobdefect_row_late_from_cone_kit`,
  `frobdefect_row_late_center_slot_rperiodic_kit`,
  `frobdefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump_kit`,
  `frobdefect_row_late_colm1_slot_rperiodic_kit`,
  `frobdefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage_kit`,
  `frobdefect_row_late_colm1_xor_center_slot_at_both_white_centers_kit`,
  `periodic_winwitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality_kit`,
  `periodic_winwitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality_kit`,
  `wittresp_late_eq_zcenter_xor_center_triality_kit`,
  `wittresp_late_at_white_centers_eq_zcenter_kit`,
  `periodic_wittresp_late_shift_mul_eq_zcenter_xor_kit`,
  `periodic_crosscarry_late_center_bit_shift_mul_at_white_centers_kit`,
  `periodic_crosscarry_late_colm1_shift_mul_at_white_centers_kit`,
  `periodic_winwitt_step_late_center_slot_shift_mul_at_white_centers_kit`,
  `rdiag_restart_kit`,
  `rdiag_restart_of_threshold_kit`,
  `center_restart_rdiag_kit`,
  `frobdefect_row_lt_twopow_kit`,
  `frobdefect_row_sector_one_kit`,
  `frobdefect_row_sector_one_restart_kit`,
  `frobdefect_row_sector_two_restart_kit`,
  `frobdefect_winwitt_sector_two_wronskian_kit`,
  `crosscarry_scale_row_winwitt_sector_two_cone_eq_kit`,
  `frobdefect_row_late_eq_frobdefect_winwitt_sector_two_kit`,
  `frobdefect_row_late_eq_winwitt_sector_two_wronskian_kit`,
  `periodic_ldiag_shift_mul_eq_response_shift_mul_kit`,
  `not_periodic_maskparity_zero_mul_kit`,
  `not_periodic_colm1_mul_kit`,
  `phiscale_row_late_sector_one_eq_winwitt_cone_kit`,
  `frobdefect_row_late_sector_one_eq_crosscarry_cone_kit`,
  `frobdefect_row_late_sector_one_center_slot_wronskian_kit`,
  `crosscarry_row_winwitt_sector_two_center_slot_kit`,
  `ldiag_settled_restart_kit`,
  `zcenter_restart_ldiag_kit`,
  `frobdefect_row_late_center_slot_of_zcenter_true_kit`,
  `periodic_winwitt_step_late_center_slot_of_zcenter_true_kit`,
  `periodic_winwitt_step_late_colm1_slot_of_zcenter_true_kit`,
  `rowagree_mono_kit`,
  `winwittagree_mono_kit`,
  `rowagree_step_kit`,
  `rowagree_steps_kit`,
  `phiscale_row_testbit_eq_of_rowagree_kit`,
  `frobdefect_row_testbit_eq_of_rowagree_kit`,
  `crosscarry_testbit_eq_of_rowagree_winwittagree_kit`,
  `winwittagree_step_kit`,
  `winwittagree_steps_kit`,
  `wittrespbool_eq_of_winwittagree_steps_kit`,
  `colm1_eq_of_rowagree_steps_kit`,
  `maskparity_zero_eq_of_rowagree_steps_kit`,
  `colnegoneperiodic_of_sector_rowagree_kit`,
  `not_sector_rowagree_mul_kit`,
  `rdiag_lcmperiod_eq_kit`,
  `ldiag_lcmperiod_eq_kit`,
  `center_lcmperiod_eq_kit`,
  `not_sector_rowagree_lcmperiod_kit`,
  `rowagree_extend_right_kit`,
  `periodic_rowagree_center_kit`,
  `periodic_rowagree_black_center_kit`,
  `periodic_rowagree_symm_of_right_kit`,
  `periodic_rowagree_lcmperiod_symm_of_right_kit`,
  `colnegoneperiodic_of_sector_right_rowagree_kit`,
  `not_sector_right_rowagree_lcmperiod_kit`,
  `winwittagree_extend_right_kit`,
  `winwittagree_of_rowagree_three_and_late_kit`,
  `rowagree_late_of_winwittagree_and_three_kit`,
  `wittrespbool_periodic_of_sector_winwittagree_kit`,
  `right_boundary_row_lcmperiod_eq_kit`,
  `left_boundary_row_lcmperiod_eq_kit`,
  `frobdefect_row_sector_one_lcmperiod_xor_kit`,
  `rhcenter_eq_rdiag_kit`,
  `rhcenter_eq_row_testbit_kit`,
  `lhcenter_eq_ldiag_kit`,
  `lhcenter_eq_row_testbit_kit`,
  `rhcenter_zero_eq_center_kit`,
  `rhcenter_self_eq_true_kit`,
  `rhcenter_gt_eq_false_kit`,
  `phicenter_eq_lhcenter_rhcenter_kit`,
  `lhcenter_one_eq_of_center_fixed_kit`,
  `periodic_lhcenter_one_defect_eq_not_center_and_rhcenter_one_defect_kit`,
  `rhcenter_step_succ_kit`,
  `rhcenter_inward_step_kit`,
  `rhbandagree_extend_inward_kit`,
  `rhbandagree_step_kit`,
  `rowagree_right_of_rhbandagree_kit`,
  `rhbandagree_of_rowagree_right_kit`,
  `sectorrightrowagree_of_rhbandagree_kit`,
  `not_sector_rhbandagree_lcmperiod_kit`,
  `rhcenter_right_edge_lcmperiod_eq_kit`,
  `colnegoneperiodic_of_sector_winwittagree_kit`,
  `not_sector_winwittagree_lcmperiod_kit`,
  `sectorwinwittagree_of_sectorwiderowagree_kit`,
  `sectorwinwittagree_of_sectorwiderightrowagree_kit`,
  `not_sectorwiderightrowagree_lcmperiod_kit`,
  `lhcenter_zero_eq_center_kit`,
  `lhcenter_self_eq_true_kit`,
  `lhcenter_gt_eq_false_kit`,
  `lhcenter_step_succ_kit`,
  `lhcenter_outward_step_kit`,
  `center_eq_rhcenter_inward_zero_kit`,
  `periodic_rhcenter_step_one_eq_of_or_eq_kit`,
  `periodic_rhcenter_or_eq_of_step_one_eq_kit`,
  `rhbandagree_steps_kit`,
  `periodic_rhbandagree_zero_of_one_kit`,
  `periodic_rhbandagree_zero_step_kit`,
  `periodic_rhbandagree_zero_steps_kit`,
  `rhbandagree_extend_inward_steps_kit`,
  `rhbandagree_zero_of_edge_and_succ_kit`,
  `periodic_rhbandagree_bounce_zero_kit`,
  `periodic_rhbandagree_bounce_succ_kit`,
  `rhcenter_one_periodic_of_sector_rhbandagree_kit`,
  `lhcenter_one_periodic_of_sector_rhbandagree_kit`,
  `rhcenter_diag_shift_twopow_eq_kit`,
  `rhcenter_sector_diag_eq_center_kit`,
  `rhcenter_scale_step_kit`,
  `rhcenter_scale_inward_step_kit`,
  `rhbandagree_mono_kit`,
  `rhcolagree_mono_kit`,
  `rhoragree_mono_kit`,
  `rhoragree_of_col_agree_kit`,
  `periodic_rhoragree_one_of_col_one_kit`,
  `periodic_col_one_of_rhoragree_one_kit`,
  `rhcenter_inward_determine_step_kit`,
  `rhcenter_inward_determine_kit`,
  `rhbandagree_of_inward_determine_kit`,
  `rhbandagree_outside_cone_kit`,
  `rhbandagree_scale_step_kit`,
  `rhbandagree_scale_inward_step_kit`,
  `winwittagree_of_rhbandagree_scale_kit`,
  `sectorrhbandagree_of_inward_determine_kit`,
  `not_sector_inward_determine_lcmperiod_kit`,
  `rhcenter_scale_step_le_kit`,
  `rhcenter_scale_inward_step_le_kit`,
  `rhbandagree_scale_step_le_kit`,
  `rhbandagree_scale_inward_step_le_kit`,
  `winwittagree_of_rhbandagree_scale_le_kit`,
  `rhbandagree_scale_inward_steps_kit`,
  `rhcenter_inward_of_black_left_kit`,
  `rhcenter_inward_of_black_right_kit`,
  `rhcenter_agree_of_black_left_kit`,
  `rhcenter_white_pair_of_diag_eq_kit`,
  `rhcenter_diag_eq_of_white_pair_kit`,
  `rhcenter_diag_shift_twopow_eq_of_threshold_kit`,
  `rhcenter_sector_diag_eq_center_of_threshold_kit`,
  `rhcenter_zero_gap_of_threshold_kit`,
  `rhcenter_last_one_of_threshold_kit`,
  `rhcenter_scale_step_uncond_kit`,
  `rhcenter_scale_inward_step_uncond_kit`,
  `rhwinwittagree_of_winwittagree_kit`,
  `rhwinwittagree_outside_cone_kit`,
  `rhbandagree_scale_inward_step_uncond_kit`,
  `rhbandagree_scale_inward_steps_uncond_kit`,
  `rhbandagree_of_scale_inward_cone_kit`,
  `rhcenter_diag_diff_eq_or_kit`,
  `rhcenter_defect_diag_step_kit`,
  `rhcenter_defect_diag_step_of_col_eq_kit`,
  `rhcenter_defect_inward_of_col_eq_two_kit`,
  `rhcenter_outward_of_white_mid_kit`,
  `rhcenter_agree_outward_of_white_mid_kit`,
  `rhcenter_defect_inward_of_white_mid_kit`,
  `rhcenter_agree_inward_of_col_eq_two_kit`,
  `not_lhbandagree_of_lt_add_kit`,
  `lhcenter_outward_determine_step_kit`,
  `lhcenter_outward_determine_kit`,
  `lhbandagree_of_outward_determine_kit`,
  `not_lhcolagree_zero_one_of_pos_kit`,
  `periodic_lhcolagree_zero_kit`,
  `not_periodic_lhcolagree_one_horizon_kit`,
  `periodic_lhcolagree_one_of_rhcolagree_one_kit`,
  `not_periodic_rhcolagree_one_horizon_kit`,
  `periodic_rhcolagree_one_of_rhbandagree_zero_kit`,
  `periodic_rhcolagree_one_of_finite_sectors_kit`,
  `not_periodic_finite_sector_rhbandagree_mul_kit`,
  `not_periodic_finite_sector_rhbandagree_lcmperiod_kit`,
  `periodic_lhcenter_or_zero_defect_eq_kit`,
  `periodic_lhcenter_two_defect_eq_kit`,
  `lhcenter_eq_row_testbit_uncond_kit`,
  `lhcenter_scale_step_uncond_kit`,
  `lhcenter_scale_outward_step_uncond_kit`,
  `lhcenter_scale_cross_step_kit`,
  `rhcenter_eq_lhcenter_scale_cross_kit`,
  `rhbandagree_of_lhbandagree_scale_cross_kit`,
  `winwittagree_of_rhbandagree_lhbandagree_scale_cross_kit`,
  `periodic_rhbandagree_of_lhcolagree_one_and_winwittagree_kit`,
  `periodic_winwittagree_of_lhcolagree_one_and_rhbandagree_kit`,
  `lhbandagree_scale_step_uncond_kit`,
  `lhbandagree_scale_outward_step_uncond_kit`,
  `lhcenter_diag_diff_eq_or_kit`,
  `lhcenter_defect_outward_step_kit`,
  `lhcenter_defect_outward_of_col_eq_kit`,
  `lhcenter_defect_outward_of_black_kit`,
  `winwitt_testbit_left_edge_kit`,
  `winwitt_testbit_gt_left_edge_kit`,
  `winwitt_testbit_ge_left_edge_kit`,
  `winwitt_testbit_settled_left_kit`,
  `lhbandagree_outside_cone_kit`,
  `lhbandagree_mono_kit`,
  `lhcolagree_mono_kit`,
  `lhbandagree_step_kit`,
  `lhbandagree_steps_kit`,
  `periodic_lhbandagree_zero_of_one_kit`,
  `periodic_rhbandagree_of_rhcolagree_one_and_winwittagree_kit`,
  `periodic_winwittagree_of_rhcolagree_one_and_rhbandagree_kit`,
  `lhcenter_scale_inward_step_uncond_kit`,
  `lhbandagree_scale_inward_step_uncond_kit`,
  `winwittagree_outside_left_cone_kit`,
  `rdiag_add_eq_lhcenter_uncond_kit`,
  `winwitt_testbit_eq_lhcenter_scale_uncond_kit`,
  `winwittagree_of_lhbandagree_scale_uncond_kit`,
  `lhcenter_scale_mid_step_uncond_kit`,
  `lhbandagree_scale_mid_step_uncond_kit`,
  `lhcenter_scale_step_outer_strip_kit`,
  `lhcenter_scale_inward_outer_strip_kit`,
  `winwitt_testbit_outer_left_strip_kit`,
  `winwitt_testbit_outer_left_strip_eq_ldiag_xor_kit`,
  `lhbandagree_scale_inward_outer_strip_kit`,
  `lhbandagree_scale_step_outer_strip_kit`,
  `winwittagree_outer_left_strip_kit`,
  `not_lhbandagree_and_winwittagree_of_lt_twopow_kit`,
  `frobdefect_row_testbit_lhcenter_uncond_kit`,
  `frobdefect_row_testbit_lhcenter_outer_strip_eq_false_kit`,
  `phiscale_row_testbit_lhcenter_uncond_kit`,
  `phiscale_row_testbit_lhcenter_outer_strip_kit`,
  `crosscarry_row_scale_lhcenter_outer_strip_kit`,
  `winwitt_step_outer_left_strip_kit`,
  `winwittagree_step_outer_left_strip_kit`,
  `winwittagree_steps_outer_left_strip_kit`,
  `winwitt_outward_step_outer_left_strip_kit`,
  `winwittagree_extend_outer_left_strip_kit`,
  `winwittagree_outward_step_outer_left_strip_kit`,
  `rhcenter_eq_lhcenter_scale_cross_outer_kit`,
  `rhbandagree_of_lhbandagree_scale_cross_outer_kit`,
  `winwittagree_of_rhbandagree_lhbandagree_scale_cross_outer_kit`,
  `periodic_rhbandagree_of_lhcolagree_one_and_winwittagree_outer_kit`,
  `periodic_winwittagree_of_lhcolagree_one_and_rhbandagree_outer_kit`,
  `rhcenter_eq_lhcenter_scale_cross_cone_kit`,
  `lhcenter_scale_cross_cone_kit`,
  `winwitt_testbit_scale_cross_cone_kit`,
  `winwitt_testbit_scale_cross_zero_gap_kit`,
  `winwitt_testbit_zero_gap_eq_lhcenter_late_kit`,
  `lhbandagree_of_winwittagree_zero_gap_kit`,
  `winwittagree_of_lhbandagree_zero_gap_kit`,
  `rhbandagree_of_lhbandagree_and_winwittagree_cross_cone_kit`,
  `winwittagree_of_rhbandagree_and_lhbandagree_cross_cone_kit`,
  `lhbandagree_of_rhbandagree_and_winwittagree_cross_cone_kit`,
  `periodic_rhbandagree_of_lhcolagree_late_and_winwittagree_cone_kit`,
  `periodic_winwittagree_of_lhcolagree_late_and_rhbandagree_cone_kit`,
  `lhcenter_step_outer_strip_from_winwitt_kit`,
  `winwitt_step_lhcenter_defect_uncond_kit`,
  `winwittagree_step_of_lhbandagree_scale_uncond_kit`,
  `winwittagree_outward_of_lhbandagree_scale_uncond_kit`,
  `phiscale_row_testbit_lhcenter_sector_one_kit`,
  `lhcenter_scale_same_col_cone_kit`,
  `lhcenter_scale_inward_same_col_cone_kit`,
  `winwitt_testbit_sector_one_lhcenter_kit`,
  `lhbandagree_scale_same_col_cone_kit`,
  `lhbandagree_scale_inward_same_col_cone_kit`,
  `winwittagree_sector_one_lhcenter_kit`,
  `not_lhbandagree_late_and_winwittagree_sector_one_kit`,
  `frobdefect_row_testbit_lhcenter_sector_one_eq_false_kit`,
  `crosscarry_row_scale_lhcenter_sector_one_kit`,
  `winwitt_step_sector_one_lhcenter_kit`,
  `winwittagree_step_sector_one_lhcenter_kit`,
  `winwittagree_outward_step_sector_one_lhcenter_kit`,
  `periodic_winwitt_sector_one_zero_eq_kit`,
  `periodic_winwitt_sector_one_two_defect_eq_kit`.
- **Batch 5 (9.367–9.381, attestation `c6170cdb3f6233a808bb4272ff8618ec85ebefe31dfb1a063734ed7073d00ee2`)**:
  - **Unconditional `2^k`-Scale Step & Inward Cone Reduction (`9.367`–`9.373`)**: Because `(winWitt t n).testBit 0 = false` (`winWitt_testBit_zero`) and `rhCenter t q = false` for `q > t`, `rhCenter_scale_step_uncond` (9.367) and `rhCenter_scale_inward_step_uncond` (9.368) hold for **all** `t, k, p ∈ ℕ` with zero light-cone bounds! Introducing `RhWinWittAgree t k Q p0 L` (connected inside the cone by `rhWinWittAgree_of_winWittAgree`, 9.369, and vanishing unconditionally outside the cone `t + Q ≤ p0` by `rhWinWittAgree_outside_cone`, 9.370) yields `rhBandAgree_scale_inward_step_uncond` (9.371), `rhBandAgree_scale_inward_steps_uncond` (9.372), and `rhBandAgree_of_scale_inward_cone` (9.373): whenever `t + Q < p0 + M * 2^k`, both outer boundary bands at time `t` lie outside the light cone of `t + Q` and are discharged automatically by `rhBandAgree_outside_cone`.
  - **Right-Half Diagonal Defect Conservation & Generalized Masked-Jen Gate (`9.374`–`9.381`)**: From `rhCenter_diag_diff_eq_or` (9.374), the diagonal step of the right-half `Q`-defect satisfies `rhCenter_defect_diag_step` (9.375). Whenever column `p + 1` agrees at time `t`, the diagonal defect step collapses to the generalized Masked-Jen gate `(!rhCenter t (p + 1)) && (rhCenter (t + Q) (p + 2) ⊕ rhCenter t (p + 2))` (`rhCenter_defect_diag_step_of_col_eq`, 9.376). Under two-time agreement at column `p + 1` (`t` and `t + 1`), the inward defect at `(t, p)` equals this masked defect (`rhCenter_defect_inward_of_col_eq_two`, 9.377), while across a white cell `rhCenter t (p + 1) = false`, `rhCenter` is locally right-permutive (`rhCenter_outward_of_white_mid`, 9.378; `rhCenter_agree_outward_of_white_mid`, 9.379; `rhCenter_defect_inward_of_white_mid`, 9.380; `rhCenter_agree_inward_of_col_eq_two`, 9.381).
- **Batch 6 (9.382–9.396, attestation `2e146290a0c8038b52f07642cedb3c83d1b82b3f989d8fa0ac516b1bca2a3354`)**:
  - **Finite-Horizon Left-Light-Cone Refutation Engine & Proved Death Clock (`9.382`–`9.390`)**: Because `lhCenter (t + Q) (t + Q) = true` while `lhCenter t (t + Q) = false` (`0 < Q`), `LhBandAgree t Q 0 L` is impossible whenever `t + Q ≤ L` (`not_lhBandAgree_of_lt_add`, 9.382). By left-permutivity (`lhCenter_outward_step`), time-trace agreement `LhColAgree` at columns `p0` and `p0 + 1` over `[t, t + L]` marches outward (`lhCenter_outward_determine_step`, 9.383; `lhCenter_outward_determine`, 9.384) to establish spatial band agreement `LhBandAgree t Q p0 (L + 1)` (`lhBandAgree_of_outward_determine`, 9.385). Consequently, `LhColAgree t Q 0 S` and `LhColAgree t Q 1 S` cannot both hold once `t + Q ≤ S + 1` (`not_lhColAgree_zero_one_of_pos`, 9.386). Under `CenterPeriodic T P` (`0 < P`), `periodic_lhColAgree_zero` (9.387) supplies `LhColAgree t (m * P) 0 S` for all `t ≥ T`, yielding a self-contained finite-horizon death clock `¬ LhColAgree t (m * P) 1 S` for column `-1` (`not_periodic_lhColAgree_one_horizon`, 9.388) and — via the §6 `Φ` fixed-point transfer `periodic_lhColAgree_one_of_rhColAgree_one` (9.389) — the finite-horizon death clock `¬ RhColAgree t (m * P) 1 S` for right-half column `+1` whenever `t + m * P ≤ S + 1` (`not_periodic_rhColAgree_one_horizon`, 9.390)!
  - **Finite-Sector Refutation of `RhBandAgree` (`9.391`–`9.394`)**: Directly addressing the reviewer's observation that infinite-sector engines require unboundedly many `u ≥ U`, gluing `M` finite sector bands (`j < M`) via `periodic_rhColAgree_one_of_rhBandAgree_zero` (9.391) and `periodic_rhColAgree_one_of_finite_sectors` (9.392) refutes `RhBandAgree ((d + (U + j) * 2^k) + 1) Q 0 (2^k + 1)` over a **finite** number `M` of sectors as soon as `(d + U * 2^k) + Q ≤ M * 2^k` (`not_periodic_finite_sector_rhBandAgree_mul`, 9.393; `not_periodic_finite_sector_rhBandAgree_lcmPeriod`, 9.394).
  - **Exact Linear Defect Derivative at Column `-2` via the `Φ` Fixed-Point Law (`9.395`–`9.396`)**: Under `CenterPeriodic T P` (`t ≥ T`), because `lhCenter_one_eq_of_center_fixed` forces the `m * P`-defect of `lhCenter · 1` to vanish whenever `center t = true`, the nonlinear OR `lhCenter · 1 || lhCenter · 0` has the exact same `m * P`-defect as `lhCenter · 1` (`periodic_lhCenter_or_zero_defect_eq`, 9.395), and therefore the `m * P`-defect of column `-2` (`lhCenter · 2`) is the exact linear discrete time-derivative of the column `-1` defect (`periodic_lhCenter_two_defect_eq`, 9.396).
- **Batch 7 (9.397–9.411, attestation `ff34d213d8f1d4bc1b8bb285452bd81bf01d4ab64e9867fd53fc82e4faf5b6c9`)**:
  - **Unconditional `lhCenter` Row Readout & `2^k`-Scale Step Laws (`9.397`–`9.399`, `9.406`–`9.407`)**: Because `(row t).testBit (t + p) = false` when `t < p` (by `rdiag_gt_two_mul`), `lhCenter t p = (row t).testBit (t + p)` holds **unconditionally for all `t, p ∈ ℕ`** (`lhCenter_eq_row_testBit_uncond`, 9.397). Consequently, `lhCenter_scale_step_uncond` (9.398), `lhCenter_scale_outward_step_uncond` (9.399), `lhBandAgree_scale_step_uncond` (9.406), and `lhBandAgree_scale_outward_step_uncond` (9.407) hold for all `t, k, p ∈ ℕ` with zero light-cone bounds!
  - **Unconditional Cross-Center `2^k`-Scale Duality Between `rhCenter` and `lhCenter` (`9.400`–`9.405`)**: For all `t, k, r ∈ ℕ` with `r ≤ 2^k` (no light-cone bound `r ≤ t` required!), `lhCenter_scale_cross_step` (9.400) and `rhCenter_eq_lhCenter_scale_cross` (9.401) express every right-half column `rhCenter t r` (`r ∈ [0, 2^k]`) directly in terms of `lhCenter (t + 2^k) (2^k - r)`, `lhCenter t (2^k - r)`, `lhCenter t (2^(k+1) - r)`, and `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)`. Under `CenterPeriodic T P`, finite-window column-`-1` agreement `LhColAgree t (m * P) 1 (2^(k+1))` supplies all three `LhBandAgree` terms via `lhBandAgree_of_outward_determine`, proving the exact equivalence between `RhBandAgree t (m * P) 0 (2^k)` and `WinWittAgree t k (m * P) (t + 2^k) (2^k)` (`periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree`, 9.404; `periodic_winWittAgree_of_lhColAgree_one_and_rhBandAgree`, 9.405).
  - **Linearized Outward Defect Step & Black-Cell Shielding in `lhCenter` (`9.408`–`9.411`)**: Whenever `lhCenter (t + Q) p = lhCenter t p` (already known when marching outward from the center!), the outward `Q`-defect at `p + 2` is linear in the column-`p + 1` defects (`lhCenter_defect_outward_of_col_eq`, 9.410), and vanishes completely at `t` whenever `lhCenter t p = true` (`lhCenter_defect_outward_of_black`, 9.411).
- **Batch 8 (9.412–9.426, attestation `4ece9440fb426c6f33d6dc9a47ed1bb3fde6c7d62fb2f36cce4b5fb618c063fe`)**:
  - **Left-Edge and Settled Left-Wing Vanishing of `winWitt` (`9.412`–`9.415`, `9.426`)**: Evaluating `lhCenter_scale_step_uncond` at `p = t`, `p > t`, and `p = t - j` (`j ≤ k`, `settle j ≤ t`) proves that `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = false` for all `p ≥ t` (`winWitt_testBit_left_edge`, 9.412; `winWitt_testBit_gt_left_edge`, 9.413; `winWitt_testBit_ge_left_edge`, 9.414) AND for all settled left diagonals `p = t - j` (`winWitt_testBit_settled_left`, 9.415 — the exact left-wing counterpart of `winWitt_testBit_low`), yielding unconditional `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` outside the left light cone (`winWittAgree_outside_left_cone`, 9.426).
  - **Left-Half Band Calculus & Right-to-Left Cross-Center Equivalence (`9.416`–`9.425`)**: Establishes `lhBandAgree_outside_cone` (9.416), `lhBandAgree_mono` (9.417), `lhColAgree_mono` (9.418), `lhBandAgree_step` (9.419), `lhBandAgree_steps` (9.420), `periodic_lhBandAgree_zero_of_one` (9.421), `periodic_rhBandAgree_of_rhColAgree_one_and_winWittAgree` (9.422), `periodic_winWittAgree_of_rhColAgree_one_and_rhBandAgree` (9.423), `lhCenter_scale_inward_step_uncond` (9.424), and `lhBandAgree_scale_inward_step_uncond` (9.425).
- **Batch 9 (9.427–9.441, attestation `9043446034903985da5654f02c80951a8ee4204a18a5fbc4bd8814f8af6ac773`)**:
  - **Complete 5-Term `2^k`-Scale Left-Half Calculus (`9.427`–`9.431`)**: Establishes `rdiag_add_eq_lhCenter_uncond` (9.427), `winWitt_testBit_eq_lhCenter_scale_uncond` (9.428), `winWittAgree_of_lhBandAgree_scale_uncond` (9.429), `lhCenter_scale_mid_step_uncond` (9.430), and `lhBandAgree_scale_mid_step_uncond` (9.431), completing all five directions of the unconditional `2^k`-scale `lhCenter`/`winWitt` relation.
  - **Outer `$2^k$`-Strip 3-Term Collapse & Finite-Scale Obstruction (`9.432`–`9.439`)**: Whenever `t < p + 2^k` (the outer `2^k`-strip of the left cone and beyond, valid at ANY time `t` regardless of whether `t ≥ 2^k`!), both `lhCenter t (p + 2^k)` and `lhCenter t (p + 2^(k+1))` lie outside the light cone and vanish, collapsing the 5-term relation to the exact 3-term laws `lhCenter_scale_step_outer_strip` (9.432), `lhCenter_scale_inward_outer_strip` (9.433), `winWitt_testBit_outer_left_strip` (9.434), and `winWitt_testBit_outer_left_strip_eq_ldiag_xor` (9.435). At the band level (`t + Q < p0 + 2^k`), any two of `LhBandAgree t Q p0 L`, `LhBandAgree (t + 2^k) Q (p0 + 2^k) L`, and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` imply the third (`lhBandAgree_scale_inward_outer_strip`, 9.436; `lhBandAgree_scale_step_outer_strip`, 9.437; `winWittAgree_outer_left_strip`, 9.438), and at `p0 = 0` (`0 < Q`, `t + Q ≤ L`, `t + Q < 2^k`), `LhBandAgree (t + 2^k) Q (2^k) L` and `WinWittAgree t k Q (t + 2^(k+1)) L` are mutually incompatible (`not_lhBandAgree_and_winWittAgree_of_lt_twopow`, 9.439).
  - **Unconditional `frobDefect` Readout & Outer `$2^k$`-Strip Vanishing in `lhCenter` Coordinates (`9.440`–`9.441`)**: Expresses `(frobDefect k (row t)).testBit ((t + p + 1) + 2^(k+1))` unconditionally for all `t, k, p ∈ ℕ` in terms of `lhCenter t` (`frobDefect_row_testBit_lhCenter_uncond`, 9.440) and proves that it vanishes identically (`= false`) across the entire outer `2^k`-strip `t < p + 2^k` at ANY time `t` (`frobDefect_row_testBit_lhCenter_outer_strip_eq_false`, 9.441).
- **Batch 10 (9.442–9.456, attestation `88e4dc8ec84debd6d42cce1175545e01c18f5c0519fbf1a1f73b944c6f165e7b`)**:
  - **Single-Sector Window Evolution in the Outer `$2^k$`-Strip (`9.442`–`9.450`)**: Expresses `(phiScale k (row t)).testBit (t + p + 2^(k+1))` unconditionally in `lhCenter` coordinates (`phiScale_row_testBit_lhCenter_uncond`, 9.442) and proves that across the outer `2^k`-strip (`t < p + 2^k`, valid at ANY time `t`), `phiScale k (row t)` collapses to the single cell `lhCenter t p` (`phiScale_row_testBit_lhCenter_outer_strip`, 9.443) and `crossCarry` collapses to a single-sector bilinear pairing (`crossCarry_row_scale_lhCenter_outer_strip`, 9.444). Combined with `frobDefect = false` (`9.441`), the universal window step `winWitt_step_frobDefect_testBit_succ` collapses to `winWitt_step_outer_left_strip` (9.445) and `winWitt_outward_step_outer_left_strip` (9.448), so `WinWittAgree` propagates forward (`winWittAgree_step_outer_left_strip`, 9.446; `winWittAgree_steps_outer_left_strip`, 9.447) and extends/steps outward (`winWittAgree_extend_outer_left_strip`, 9.449; `winWittAgree_outward_step_outer_left_strip`, 9.450) using **only** the single inner band `LhBandAgree t Q p0`!
  - **Outer `$2^{k+1}$`-Regime & In-Cone Cross-Center `$2^k$`-Scale Duality (`9.451`–`9.456`)**: For `r ≤ 2^k` and `t + r < 2^(k+1)`, `lhCenter t (2^(k+1) - r) = false`, reducing cross-center duality to the 3-term law `rhCenter_eq_lhCenter_scale_cross_outer` (9.451) and its band/half-horizon consequences (`9.452`–`9.455`), and for `t + r < 2^k` to the 2-term law `rhCenter_eq_lhCenter_scale_cross_cone` (9.456).
- **Batch 11 (9.457–9.471, attestation `e44bcd94f48c8da1073163002fa55dd485fb6a0fbf39070a744bd614d0c36d1d`)**:
  - **In-Cone Cross-Center Triality & Direct Readout of Late `lhCenter` in the Inter-Cone Zero Gap (`9.457`–`9.467`)**: Completes the 2-term in-cone cross-center triality (`lhCenter_scale_cross_cone`, 9.457; `winWitt_testBit_scale_cross_cone`, 9.458) and its band equivalences (`9.463`–`9.467`), where under `CenterPeriodic T P` (`T ≤ t`, `t + m * P + L < 2^k`) only the **late** trace `LhColAgree (t + 2^k) (m * P) 1 (2^k)` is required to equate `RhBandAgree t (m * P) 0 L` and `WinWittAgree t k (m * P) ((t + 2^(k+1)) - L) L` (`9.466`–`9.467`). Specializing to the inter-cone zero gap (`t < p` and `t + p < 2^k`, where `rhCenter t (2^k - p) = false`) yields `(winWitt t (2^k)).testBit (t + p + 2^k) = lhCenter (t + 2^k) p` (`winWitt_testBit_zero_gap_eq_lhCenter_late`, 9.460) and the direct band equivalence `LhBandAgree (t + 2^k) Q p0 L ↔ WinWittAgree t k Q (t + p0 + 2^k) L` with zero hypotheses at time `t` (`lhBandAgree_of_winWittAgree_zero_gap`, 9.461; `winWittAgree_of_lhBandAgree_zero_gap`, 9.462).
  - **Outer-Strip Single-Step `lhCenter` Evolution & Unconditional Window-Step Transfer (`9.468`–`9.471`)**: Combines `lhCenter_scale_step_outer_strip` (`9.432`) and `winWitt_step_outer_left_strip` (`9.445`) to express `lhCenter (t + 1 + 2^k) (p + 1 + 2^k)` directly from `lhCenter t` and `winWitt t (2^k)` (`lhCenter_step_outer_strip_from_winWitt`, 9.468), proves the unconditional `winWitt` step defect identity in `lhCenter` coordinates (`winWitt_step_lhCenter_defect_uncond`, 9.469), and transfers 3-sector `LhBandAgree` at time `t` directly into `WinWittAgree (t + 1)` and `WinWittAgree` extension (`winWittAgree_step_of_lhBandAgree_scale_uncond`, 9.470; `winWittAgree_outward_of_lhBandAgree_scale_uncond`, 9.471).
- **Batch 12 (9.472–9.486, attestation `99c102da03e58403d0240f12cdee3cac699532b85d13b58dcf11700d0d255668`)**:
  - **Same-Column `$2^k$`-Scale Left-Half Calculus & Sub-Light-Cone Late Obstruction (`9.472`–`9.479`)**: For all `t, k, p ∈ ℕ` with `t + p < 2^k` (including `p = 0`, the center column!), `(phiScale k (row t)).testBit (t + p + 2^k) = lhCenter t p` (`phiScale_row_testBit_lhCenter_sector_one`, 9.472), so `lhCenter (t + 2^k) p = lhCenter t p ⊕ (winWitt t (2^k)).testBit (t + p + 2^k)` at the **same spatial column `p`** (`lhCenter_scale_same_col_cone`, 9.473; `lhCenter_scale_inward_same_col_cone`, 9.474; `winWitt_testBit_sector_one_lhCenter`, 9.475; band forms `9.476`–`9.478`). Pulling `LhBandAgree (t + 2^k) Q 0 L` back to time `t` via `WinWittAgree t k Q (t + 2^k) L` refutes their conjunction as soon as `t + Q ≤ L` (`not_lhBandAgree_late_and_winWittAgree_sector_one`, 9.479) — even though `L < 2^k` lies strictly inside the late light cone at `t + 2^k`!
  - **Sector-1 `frobDefect` Vanishing, Single-Sector Window Step, and Linearized Periodic Window Defect Law (`9.480`–`9.486`)**: For all `t, k, p ∈ ℕ` with `t + p + 1 < 2^k`, `(frobDefect k (row t)).testBit ((t + p + 1) + 2^k) = false` (`frobDefect_row_testBit_lhCenter_sector_one_eq_false`, 9.480), collapsing Sector-1 `crossCarry` and the Sector-1 window step to single-sector recurrences (`crossCarry_row_scale_lhCenter_sector_one`, 9.481; `winWitt_step_sector_one_lhCenter`, 9.482; `winWittAgree_step_sector_one_lhCenter`, 9.483; `winWittAgree_outward_step_sector_one_lhCenter`, 9.484). Under `CenterPeriodic T P` (`0 < P`, `T ≤ t`, `t + m * P + 2 < 2^k`), `(winWitt · (2^k)).testBit (· + 2^k)` is automatically `m * P`-invariant (`periodic_winWitt_sector_one_zero_eq`, 9.485), and the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 2 + 2^k)` equals the exact linear discrete time-derivative of the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 1 + 2^k)` (`periodic_winWitt_sector_one_two_defect_eq`, 9.486).
- **Batch 13 (9.487–9.501, attestation `3dfd98d7a1ebe50b70c4c4f003802021a7c908f710ee3a3ff5a1d096bcb443b9`)**:
  - **Same-Column `$2^k$`-Scale Right-Half Calculus & Inter-Cone Zero-Gap Readout (`9.487`–`9.496`)**: Proves the finite-horizon right-light-cone refutation `¬ RhBandAgree t Q 0 L` whenever `0 < Q` and `t + Q ≤ L` (`not_rhBandAgree_of_lt_add`, 9.487) and establishes for all `t, k, p ∈ ℕ` with `t + p < 2^k` (**with no bound `p ≤ t` required**, since for `p > t` bit `(t + 2^k) - p` crosses into the Sector-0 inter-cone zero gap where both sides are `false`!) that `(phiScale k (row t)).testBit ((t + 2^k) - p) = rhCenter t p` (`phiScale_row_testBit_rhCenter_cone`, 9.488) and `rhCenter (t + 2^k) p = rhCenter t p ⊕ (winWitt t (2^k)).testBit ((t + 2^k) - p)` at the **same spatial column `p`** in the right half (`rhCenter_scale_same_col_cone`, 9.489; `rhCenter_scale_inward_same_col_cone`, 9.490; `winWitt_testBit_rhCenter_same_col_cone`, 9.491; band forms `9.493`–`9.495`), reducing in the inter-cone zero gap (`t < p`, `t + p < 2^k`) to direct readout `(winWitt t (2^k)).testBit ((t + 2^k) - p) = rhCenter (t + 2^k) p` (`winWitt_testBit_zero_gap_eq_rhCenter_late`, 9.492) and refuting simultaneous `RhBandAgree (t + 2^k) Q 0 L` and `WinWittAgree t k Q ((t + 2^k) - (L - 1)) L` for `t + Q ≤ L` (`not_rhBandAgree_late_and_winWittAgree_cone`, 9.496).
  - **Unconditional Late-Time Symmetric Doubling Across a Periodic Center (`9.497`–`9.501`)**: Extracts `LhBandAgree t Q 0 R` from `RowAgree t Q R` (`lhBandAgree_of_rowAgree_symm`, 9.497), doubles `RhBandAgree t (m * P) 0 R` to `LhBandAgree t (m * P) 0 R` for `R ≤ t` (`periodic_lhBandAgree_zero_of_rhBandAgree_zero`, 9.498), and proves that at late time `t + 2^k`, because `R ≤ 2^k ≤ t + 2^k` holds **with no bound `R ≤ t`**, `RhBandAgree (t + 2^k) (m * P) 0 R` automatically doubles across the periodic center to `LhBandAgree (t + 2^k) (m * P) 0 R` (`periodic_lhBandAgree_late_of_rhBandAgree_late`, 9.499), refuting simultaneous `RhBandAgree (t + 2^k) (m * P) 0 L` and `WinWittAgree t k (m * P) (t + 2^k) L` for `t + m * P ≤ L` (`not_periodic_rhBandAgree_late_and_winWittAgree_sector_one`, 9.500) and doubling Sector-1 `WinWittAgree` from the right wing `((t + 2^k) - R)` to the left wing `(t + 2^k)` (`periodic_winWittAgree_sector_one_left_of_right`, 9.501).
- **Batch 14 (9.502–9.516, attestation `3d7d2ad0a1b678ce7d33b705077cc96c331c7fdf660153b97dbb31ba4ae51019`)**:
  - **Universal Inter-Cone & Sector-1 `frobDefect` Vanishing, Right-Half Window Step, and Pure-`Φ` Zero-Gap Evolution (`9.502`–`9.510`)**: Proves that `(frobDefect k (row t)).testBit b = false` for **every** `b` satisfying `2 * t + 1 < b < 2^k + 2^k` (`frobDefect_row_testBit_gt_two_mul_eq_false`, 9.502 — without requiring `2 * t + 1 < 2^k`!), and in particular `(frobDefect k (row t)).testBit ((t + 2^k) - p) = false` for all `t + p + 1 < 2^k` (`frobDefect_row_testBit_rhCenter_cone_eq_false`, 9.503). Consequently, across the right half and center (`t + p + 1 < 2^k`, including `p = 0`), `crossCarry` (`crossCarry_row_scale_rhCenter_cone`, 9.504) and the window step (`winWitt_step_rhCenter_cone`, 9.505; band forms `winWittAgree_step_rhCenter_cone`, 9.508; `winWittAgree_inward_step_rhCenter_cone`, 9.509; center-slot specialization `winWitt_step_sector_one_center_slot`, 9.510) collapse to single-sector recurrences in `rhCenter`, and in the inter-cone/outer zero gaps (`t < p`, `t + p + 1 < 2^k`) `winWitt` evolves by the **pure Witt-row map `phi`** (`winWitt_step_zero_gap_eq_phi`, 9.506; `winWitt_step_lhCenter_zero_gap_eq_phi`, 9.507).
  - **`Φ`-Coupled Sector-1 Window Defect Laws & Horizon-Free Center Doubling (`9.511`–`9.516`)**: Fuses the dyadic decomposition of `lhCenter · 1` and `rhCenter · 1` with the coupled-halves fixed-point defect law (`periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect`, 9.311) at `t` and `t + 2^k` to express the `m * P`-defect of the left column-`-1` window bit `(winWitt · (2^k)).testBit (· + 1 + 2^k)` in terms of the center-slot window bit `w_0`, the right column-`+1` defect `rhCenter · 1`, and the right column-`+1` window bit `(winWitt · (2^k)).testBit ((· + 2^k) - 1)` in both late-center (`periodic_winWitt_sector_one_one_defect_eq_late`, 9.511) and early-center (`periodic_winWitt_sector_one_one_defect_eq_early`, 9.512) forms, yielding direct gated reductions when `w_0 = false` (`9.513`) or when the right window slot agrees (`9.514`), and proving width-`1` and width-`2` left Sector-1 `WinWittAgree` from right column-`+1` agreement with **no** `1 ≤ t` or `2 ≤ t` horizon requirement (`periodic_winWittAgree_sector_one_two_of_right_one`, 9.515; `periodic_winWittAgree_sector_one_three_of_right_one_step`, 9.516).
- **Batch 15 (9.517–9.531, attestation `e737aca059299c0935ee327793cd2fbfabda5702c9e271ef45cc82ab9e7ed5a3`)**:
  - **Universal Sideways (Left-Permutive) Inversion of `winWitt` (`9.517`–`9.522`)**: Because `(phi w).testBit (b + 1)` is linear in `w.testBit (b + 1)` while `(crossCarry (phiScale k (row t)) w).testBit b` and `(frobDefect k (row t)).testBit b` depend only on bits `≤ b`, the universal window step `winWitt_step_frobDefect_testBit_succ` inverts sideways at every bit `b + 1` (`1 ≤ b`) to express `(winWitt t (2^k)).testBit (b + 1)` from `(winWitt (t + 1) (2^k)).testBit (b + 1)` and bits `b, b - 1` at time `t` (`winWitt_inward_step_frobDefect_testBit_succ`, 9.517). Specializing to `2 * t + 1 < b < 2^k + 2^k` where `frobDefect = false` (`winWitt_inward_step_gt_two_mul`, 9.518) yields exact single-sector sideways inversions at the center slot (`winWitt_sector_one_one_from_center_and_right`, 9.519), across the left half of Sector 1 (`winWitt_inward_step_sector_one_lhCenter`, 9.520), across the right half of Sector 1 (`winWitt_inward_step_rhCenter_cone`, 9.521), and in the right inter-cone zero gap (`t ≤ p`, `t + p + 2 < 2^k`), where it collapses to a pure-`Φ` sideways inversion (`winWitt_inward_step_zero_gap`, 9.522).
  - **Unconditional Zero-Gap Window Propagation & Multi-Step Sector-1 Window Calculus (`9.523`–`9.531`)**: Proves unconditional forward step and inward/outward extension of `WinWittAgree` in the right inter-cone zero gap (`winWittAgree_step_zero_gap`, 9.523; `winWittAgree_inward_step_zero_gap`, 9.524) and left outer cone gap (`winWittAgree_step_lhCenter_zero_gap`, 9.525; `winWittAgree_outward_step_lhCenter_zero_gap`, 9.526) with **zero** row or band hypotheses at time `t`, and establishes `s`-step forward propagation of Sector-1 `WinWittAgree` and late band agreement across both the right half (`winWittAgree_steps_rhCenter_cone`, 9.527; `rhBandAgree_late_steps_cone`, 9.528; unconditional zero-gap form `winWittAgree_steps_zero_gap`, 9.529) and the left half (`winWittAgree_steps_sector_one_lhCenter`, 9.530; `lhBandAgree_late_steps_sector_one`, 9.531).
- **Batch 16 (9.532–9.546, attestation `1677988d29218b683e2e52da95fea094671f3ab8d86f5e1b501c343f4046418d`)**:
  - **Raw Inter-Cone Pure-`Φ` Window Evolution & Non-Overlapping 3-Sector Copy Laws of `phiScale` (`9.532`–`9.540`)**: In raw bit coordinates across the inter-cone gap `2 * t < b < 2^k`, `(phiScale k (row t)).testBit b = false` (`phiScale_row_testBit_inter_cone_gap_eq_false`, 9.532), so `(winWitt t (2^k)).testBit b = (row (t + 2^k)).testBit b` directly (`winWitt_testBit_inter_cone_gap_eq_row_late`, 9.533), `crossCarry` vanishes for `2 * t + 1 < b < 2^k` (`crossCarry_row_scale_inter_cone_gap_eq_false`, 9.534), and `winWitt` steps forward and inverts sideways by the pure Witt-row map `phi` up to and including the exact Sector-1 boundary bit `b + 1 = 2^k` (`winWitt_step_inter_cone_gap_eq_phi`, 9.535; `winWitt_inward_step_inter_cone_gap`, 9.536). Furthermore, whenever `2 * t < 2^k`, Sector 1 (`d + 2^k`, `d < 2^k`) and Sector 2 (`d + 2^(k+1)`, all `d`) of `phiScale k (row t)` are exact bit-for-bit shifted copies of `row t` (`phiScale_row_testBit_sector_one_eq_row`, 9.537; `phiScale_row_testBit_sector_two_eq_row`, 9.538; window forms `winWitt_testBit_sector_one_eq_row_xor`, 9.539; `winWitt_testBit_sector_two_eq_row_xor`, 9.540).
  - **Early-Free Cross-Sector Window Duality & Sector-1 Boundary Recurrence (`9.541`–`9.546`)**: Because the early seed bit `(row t).testBit d` appears identically in Sector 1 (`d + 2^k`) and Sector 2 (`d + 2^(k+1)`) of `phiScale k (row t)`, XORing the Sector-1 and Sector-2 bits of `winWitt t (2^k)` cancels the early row `row t` (`lhCenter t` / `rhCenter t`) identically for all `t + p < 2^k`, leaving the **early-free** late-only dualities `(winWitt t (2^k)).testBit ((t + 2^k) - p) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - p) = rhCenter (t + 2^k) p ⊕ lhCenter (t + 2^k) (2^k - p)` (`winWitt_sector_one_xor_sector_two_rhCenter_cone`, 9.541) and `(winWitt t (2^k)).testBit (t + p + 2^k) ⊕ (winWitt t (2^k)).testBit (t + p + 2^(k+1)) = lhCenter (t + 2^k) p ⊕ lhCenter (t + 2^k) (p + 2^k)` (`winWitt_sector_one_xor_sector_two_lhCenter_cone`, 9.542), along with their early-free band transfers (`lhBandAgree_late_shift_of_winWittAgree_sectors`, 9.543; `rhBandAgree_late_of_lhBandAgree_late_and_winWittAgree_sectors`, 9.544). Evaluating at the exact Sector-1 boundary bit `b = 2^k` (`p = t`, `2 * t < 2^k`) yields `(winWitt t (2^k)).testBit (2^k) = !rhCenter (t + 2^k) t` (`winWitt_testBit_twopow_eq_not_rhCenter_late`, 9.545) and the pure-`Φ` late-boundary recurrence `rhCenter (t + 2^k) t = rhCenter ((t + 1) + 2^k) (t + 1) ⊕ (rhCenter (t + 2^k) (t + 1) || rhCenter (t + 2^k) (t + 2))` (`rhCenter_late_self_from_zero_gap_step`, 9.546).
- **Batch 17 (9.547–9.561, attestation `a54047742d9c9a27c23c2ae32851f41174f0448bb1a1a98eb9a938bcfc6c77e5`)**:
  - **Scale-Independent Left-Diagonal Coordinates at `t + 2^k` & Cross-Sector `zcenter` Readouts (`9.547`–`9.551`)**: At time `t + 2^k`, the `2^k` spatial shift cancels the `2^k` shift in the left light-cone boundary `t + 2^k`: `lhCenter (t + 2^k) (p + 2^k) = ldiag (t - p) (t + 2^k)` for `p ≤ t` (`lhCenter_late_shift_eq_ldiag`, 9.547) and `lhCenter (t + 2^k) (2^k - r) = ldiag (t + r) (t + 2^k)` for `r ≤ 2^k` (`lhCenter_late_cross_eq_ldiag`, 9.548) — both on left diagonals `t - p` and `t + r` **independent of the scale `k`**. At `p = 0`, once `settle t ≤ t + 2^k` (`t ≤ k`), `lhCenter (t + 2^k) (2^k) = zcenter t` (`lhCenter_late_twopow_eq_zcenter`, 9.549), yielding both the Sector-2 readout `zcenter t = (winWitt t (2^k)).testBit (t + 2^(k+1)) ⊕ center t` (`winWitt_testBit_sector_two_center_slot_zcenter`, 9.550) and the **early-free** cross-sector readout `zcenter t = center (t + 2^k) ⊕ (winWitt t (2^k)).testBit (t + 2^k) ⊕ (winWitt t (2^k)).testBit (t + 2^(k+1))` (`winWitt_sector_one_xor_sector_two_center_slot_zcenter`, 9.551).
  - **Zero-Diagonal Window Mirrors (`9.552`–`9.561`)**: Along any settled zero diagonal (`IsZeroDiag (t - p)` or `IsZeroDiag (t + r)`, which occur for infinitely many indices by `zero_diagonals_unbounded`), the late left-half cell in `row (t + 2^k)` vanishes (`lhCenter_late_shift_of_zero_diag`, 9.552; `lhCenter_late_cross_of_zero_diag`, 9.553; center-slot `lhCenter_late_twopow_of_zero_diag`, 9.559). This turns Sector 2 of `winWitt t (2^k)` into a **direct mirror** of the early row: `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = lhCenter t p` (`winWitt_testBit_outer_left_strip_of_zero_diag`, 9.554), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = rhCenter t r` (`winWitt_testBit_scale_cross_of_zero_diag`, 9.555), `(winWitt z (2^k)).testBit (z + 2^(k+1)) = center z` (`winWitt_testBit_sector_two_center_slot_of_zero_diag`, 9.560), and in the inter-cone zero gap `t < r` the Sector-2 cross-center window bit vanishes identically (`winWitt_testBit_scale_cross_zero_gap_of_zero_diag`, 9.556). Simultaneously, the Sector-1 `⊕` Sector-2 window XOR simplifies to a direct single-cell readout of `lhCenter (t + 2^k) p` (`winWitt_sector_one_xor_sector_two_lhCenter_of_zero_diag`, 9.557), `rhCenter (t + 2^k) r` (`winWitt_sector_one_xor_sector_two_rhCenter_of_zero_diag`, 9.558), and `center (z + 2^k)` (`winWitt_sector_one_xor_sector_two_center_slot_of_zero_diag`, 9.561).
- **Batch 18 (9.562–9.576, attestation `6314fd5867637c88904e346ae3a49d31428bf925d980e26a84c9315d415fbd67`)**:
  - **Post-Zero Black-Diagonal Window Mirrors (`9.562`–`9.571`)**: Two diagonals past any zero diagonal (`z + 2` after `IsZeroDiag z`, where `E (z + 2) s = true` for all `s` by `black_after_zero_diag`), the late left-half cell in `row (· + 2^k)` is pinned to `true` (`lhCenter_late_shift_after_zero_diag`, 9.562; `lhCenter_late_cross_after_zero_diag`, 9.563; center-slot `lhCenter_late_twopow_after_zero_diag`, 9.569). This turns Sector 2 of `winWitt` into a **negated mirror** of the early row: `(winWitt (t + 2) (2^k)).testBit (((t + 2) + p) + 2^(k+1)) = !lhCenter (t + 2) p` (`winWitt_testBit_outer_left_strip_after_zero_diag`, 9.564), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !rhCenter t (r + 2)` (`winWitt_testBit_scale_cross_after_zero_diag`, 9.565), `(winWitt (z + 2) (2^k)).testBit ((z + 2) + 2^(k+1)) = !center (z + 2)` (`winWitt_testBit_sector_two_center_slot_after_zero_diag`, 9.570), and in the inter-cone zero gap `t < r + 2` it is pinned to the constant `true` (`winWitt_testBit_scale_cross_zero_gap_after_zero_diag`, 9.566 — at the exact same time `t` where bit `(t + 2^(k+1)) - r` is `false` by `9.556`!). Simultaneously, the Sector-1 `⊕` Sector-2 window XOR reads out `!lhCenter ((t + 2) + 2^k) p` (`winWitt_sector_one_xor_sector_two_lhCenter_after_zero_diag`, 9.567), `!rhCenter (t + 2^k) (r + 2)` (`winWitt_sector_one_xor_sector_two_rhCenter_after_zero_diag`, 9.568), and `!center ((z + 2) + 2^k)` (`winWitt_sector_one_xor_sector_two_center_slot_after_zero_diag`, 9.571).
  - **Real-Orbit Reset Complementarity & Unconditional 1-Step Sector-2 Window Bit Flip (`9.572`–`9.576`)**: Because `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`9.563`) and `lhCenter ((t + 2) + 2^k) (p + 2^k) = true` (`9.562`) force the OR gate in `lhCenter_step_succ` to `true`, the real-orbit cells on the adjacent diagonals `z + 1` and `z + 3` are exact bitwise complements across one time step **without requiring settlement of `z + 1` or `z + 3`**: `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_reset_after_zero_diag`, 9.572) and `lhCenter ((t + 3) + 2^k) ((p + 1) + 2^k) = !lhCenter ((t + 2) + 2^k) ((p + 2) + 2^k)` (`lhCenter_late_shift_reset_after_zero_diag`, 9.573). Since `(t, r + 1) ↦ (t + 1, r + 2)` keeps the bit indices `(t + 2^k) - (r + 1)` and `(t + 2^(k+1)) - (r + 1)` fixed, substituting `9.572` into `winWitt_testBit_scale_cross_cone` and `winWitt_sector_one_xor_sector_two_rhCenter_cone` cancels the unknown intermediate cell `lhCenter (t + 2^k) (2^k - (r + 1))`, proving `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) ⊕ (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(rhCenter t (r + 1) ⊕ rhCenter (t + 1) (r + 2))` (`winWitt_sector_two_step_complement_after_zero_diag`, 9.574), the **unconditional 1-step Sector-2 bit flip** `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` in the inter-cone zero gap `t ≤ r` (`winWitt_sector_two_step_flip_zero_gap_after_zero_diag`, 9.575), and the early-free cross-sector 1-step complementation of `rhCenter (t + 2^k) (r + 1) ⊕ rhCenter ((t + 1) + 2^k) (r + 2)` (`winWitt_sector_one_xor_sector_two_step_complement_after_zero_diag`, 9.576).
- **Batch 19 (9.577–9.591, attestation `ca39629569b51b9a00d6ebf0416514beac22066165b805628e2d291222236398`)**:
  - **1-Step Fixed-Bit Jump from Zero Diagonal to Post-Zero Black Diagonal (`9.577`–`9.582`)**: Because a fixed binary bit index `(t + 2^(k+1)) - r = ((t + 1) + 2^(k+1)) - (r + 1)` advances along a right diagonal while left diagonals move left, advancing `t ↦ t + 1` at the **same bit index** `(t + 2^(k+1)) - r` jumps by two left diagonals from `t + r` (`= false` when `IsZeroDiag (t + r)`) directly to `(t + 1) + (r + 1) = (t + r) + 2` (`= true` by `black_after_zero_diag`): `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true` (`lhCenter_late_cross_step_one_of_zero_diag`, 9.577), `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = !rhCenter (t + 1) (r + 1)` (`winWitt_testBit_scale_cross_step_one_of_zero_diag`, 9.578; zero-gap specialization `= true` for `t < r`, `winWitt_testBit_scale_cross_zero_gap_step_one_of_zero_diag`, 9.579), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) ⊕ (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = !(rhCenter t r ⊕ rhCenter (t + 1) (r + 1))` (`winWitt_sector_two_zero_to_black_step_of_zero_diag`, 9.580), and the early-free cross-sector readouts `winWitt_sector_one_xor_sector_two_rhCenter_step_one_of_zero_diag` (9.581) and `winWitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag` (9.582).
  - **Sector-2 Cross-Center Pure-`Φ` Zero-Gap Evolution & Linearization Before a Zero Diagonal (`9.583`–`9.591`)**: Establishes `(phiScale k (row t)).testBit ((t + 2^(k+1)) - r) = rhCenter t r` (`phiScale_row_testBit_scale_cross_cone`, 9.583; zero-gap `= false` for `t < r`, `phiScale_row_testBit_scale_cross_zero_gap_eq_false`, 9.584), `(crossCarry (phiScale k (row t)) (winWitt t (2^k))).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`crossCarry_row_scale_cross_zero_gap_eq_false`, 9.585), and pure-`Φ` Sector-2 step and sideways inversion in the inter-cone zero gap `t ≤ r` (`winWitt_step_scale_cross_zero_gap_eq_phi`, 9.586; `winWitt_inward_step_scale_cross_zero_gap`, 9.587). One and two diagonals before a zero diagonal (`IsZeroDiag ((t + r) + 1)` and `IsZeroDiag ((t + r) + 2)`), the vanishing cell on the zero diagonal kills one input of the OR gate in both `lhCenter_step_succ` and `Φ`, **linearizing** the step of `lhCenter` and `winWitt` to pure 2-term XORs (`lhCenter_late_cross_linear_step_one_before_zero_diag`, 9.588; `lhCenter_late_cross_linear_step_two_before_zero_diag`, 9.589; `winWitt_sector_two_linear_step_one_before_zero_diag`, 9.590; `winWitt_sector_two_linear_step_two_before_zero_diag`, 9.591).
- **Batch 20 (9.592–9.606, attestation `d76904a99bc17bb21ceedd2d555769564142fd950a547071e3ee192a68c10c94`)**:
  - **Real-Orbit Twin Identity Before a Zero Diagonal (`9.592`–`9.596`)**: Because a settled zero diagonal `(t + r) + 2` vanishes both at `(t + 2^k, 2^k - (r + 2))` and one step later at `((t + 1) + 2^k, 2^k - (r + 1))`, the linearized step `9.589` forces the two adjacent real-orbit cells on diagonals `t + r` and `(t + r) + 1` at time `t + 2^k` to be **identically equal** (`lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))`, `lhCenter_late_cross_twin_before_zero_diag`, 9.592; shifted form `lhCenter_late_shift_twin_before_zero_diag`, 9.593) **requiring only `settle ((t + r) + 2) ≤ t + 2^k` and no settling hypothesis on `t + r` or `(t + r) + 1`!** Substituting `9.592` into `winWitt_testBit_scale_cross_cone` and `winWitt_sector_one_xor_sector_two_rhCenter_cone` cancels the late `lhCenter` terms (`winWitt_sector_two_twin_before_zero_diag`, 9.594; `winWitt_sector_one_xor_sector_two_twin_before_zero_diag`, 9.596), proving that in the inter-cone zero gap `t < r`, the two adjacent Sector-2 window bits `(t + 2^(k+1)) - r` and `(t + 2^(k+1)) - (r + 1)` are identically equal (`winWitt_sector_two_twin_zero_gap_before_zero_diag`, 9.595).
  - **Antiperiodic Sector-2 Window Flips vs Below-Threshold Invariance at Doubling Zero Diagonals (`9.597`–`9.606`)**: At any doubling zero diagonal (`IsZeroDiag z` and `DoublesAt P z`, which exist for every `P > 0` by `doubling_points`), shifting by `P` along the doubling diagonal `z + 1` flips the late real-orbit cell `lhCenter` (`lhCenter_late_shift_antiperiodic_of_doubles`, 9.597; `lhCenter_late_cross_antiperiodic_of_doubles`, 9.598), yielding exact complementation of the Sector-2 and cross-sector window bits (`winWitt_outer_left_strip_antiperiodic_of_doubles`, 9.599; `winWitt_scale_cross_antiperiodic_of_doubles`, 9.600; `winWitt_sector_one_xor_sector_two_antiperiodic_of_doubles`, 9.602) and an unconditional Sector-2 bit flip `(winWitt (t + P) (2^k)).testBit (((t + P) + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + P + 1))` in the inter-cone zero gap `t + P ≤ r` (`winWitt_scale_cross_zero_gap_antiperiodic_of_doubles`, 9.601). By contrast, on every diagonal `d ≤ z` below the doubling threshold, `DoublesAt P z` enforces `P`-periodicity of `ldiag` (`ldiag_periodic_of_doubles_le`, 9.603), `lhCenter` (`lhCenter_late_cross_periodic_of_doubles_le`, 9.604), and the Sector-2 window bits (`winWitt_scale_cross_periodic_of_doubles_le`, 9.605; zero-gap equality `winWitt_scale_cross_zero_gap_periodic_of_doubles_le`, 9.606).
- **Batch 21 (9.607–9.621, attestation `48e09d6b14011291ff9ecbcc81b5f2a97ddbed57d76a7883831883b254d2c464`)**:
  - **Space-Time Equivalence of `(t + P, z + 1)` and `(t + 1, z + 3)` & Post-Black Reset Antiperiodicity Without Settling `z + 3` (`9.607`–`9.614`)**: At any doubling zero diagonal `z = (t + P) + r` (`IsZeroDiag z` and `DoublesAt P z`), both the `P`-shifted doubling cell `lhCenter ((t + P) + 2^k) (2^k - (r + 1))` on diagonal `z + 1` (`9.598`) and the 1-step post-black reset cell `lhCenter ((t + 1) + 2^k) (2^k - ((r + P) + 2))` on diagonal `z + 3` (`9.572`) negate the same base cell `lhCenter (t + 2^k) (2^k - ((r + P) + 1))`. Consequently, `lhCenter ((t + P) + 2^k) (2^k - (r + 1)) = lhCenter ((t + 1) + 2^k) (2^k - ((r + P) + 2))` (`lhCenter_late_cross_doubles_eq_reset_step`, 9.607) and diagonal `z + 3` inherits exact `P`-antiperiodicity on the real orbit (`lhCenter_late_cross_reset_antiperiodic_of_doubles`, 9.608) **requiring only `settle (z + 1)` and `settle (z + 2)` (and no settling hypothesis on `z + 3`)**. This yields exact space-time window equivalences and post-black reset `P`-antiperiodicity across Sector 2 (`winWitt_scale_cross_doubles_eq_reset_step`, 9.609; zero-gap equality `winWitt_scale_cross_zero_gap_doubles_eq_reset_step`, 9.610; `winWitt_scale_cross_reset_antiperiodic_of_doubles`, 9.611; zero-gap bit flip `winWitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles`, 9.612) and early-free Sector-1 `⊕` Sector-2 cross-sector readouts (`winWitt_sector_one_xor_sector_two_doubles_eq_reset_step`, 9.613; `winWitt_sector_one_xor_sector_two_reset_antiperiodic_of_doubles`, 9.614).
  - **Twin `2^k - 1` Readouts of `zcenter t` Before a Zero Diagonal & `!zcenter (z + 1)` vs `zcenter d` Doubling Dichotomy (`9.615`–`9.621`)**: Specializing `9.592` (`lhCenter_late_cross_twin_before_zero_diag`) to `r = 0` when `IsZeroDiag (t + 2)` proves `lhCenter (t + 2^k) (2^k - 1) = zcenter t` (`lhCenter_late_twopow_sub_one_eq_zcenter_before_zero_diag`, 9.615) **with no settling hypothesis on `t + 1`**, yielding Sector-2 (`winWitt_testBit_sector_two_sub_one_zcenter_before_zero_diag`, 9.616) and early-free cross-sector (`winWitt_sector_one_xor_sector_two_sub_one_zcenter_before_zero_diag`, 9.617) readouts of `zcenter t` at bit offset `- 1`. At any doubling zero diagonal `z`, `lhCenter ((d + P) + 2^k) (P + 2^k) = zcenter d` for all `d ≤ z` (`lhCenter_late_shift_twopow_periodic_zcenter_of_doubles_le`, 9.621), whereas at `d = z + 1` it flips to `!zcenter (z + 1)` (`lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles`, 9.618; window forms `winWitt_outer_left_strip_zcenter_antiperiodic_of_doubles`, 9.619; `winWitt_sector_one_xor_sector_two_zcenter_antiperiodic_of_doubles`, 9.620).
- **Batch 22 (9.622–9.636, attestation `4c8431a90b80e42791e951be2e02e68532fa66e6dcd852918546fbdada2c246f`)**:
  - **Center-Boundary Post-Black Reset Bridges (`2^k ↔ 2^k - 1` and `1 + 2^k ↔ 2^k`) & `!zcenter (z + 1)` Readouts at `z + 2` Without Settling `z + 3` (`9.622`–`9.631`)**: Completes the post-black reset bridge across column `2^k` between the cross-center (`2^k - r`) and left-strip (`p + 2^k`) coordinates: `lhCenter ((z + 2) + 2^k) (2^k - 1) = !lhCenter ((z + 1) + 2^k) (2^k)` (`lhCenter_late_twopow_sub_one_reset_after_zero_diag`, 9.622; window forms `winWitt_sector_two_center_to_sub_one_step_complement_after_zero_diag`, 9.623; `winWitt_sector_one_xor_sector_two_center_to_sub_one_step_complement_after_zero_diag`, 9.624) and `lhCenter ((z + 3) + 2^k) (2^k) = !lhCenter ((z + 2) + 2^k) (1 + 2^k)` (`lhCenter_late_twopow_reset_three_after_zero_diag`, 9.629; window forms `winWitt_sector_two_one_to_center_step_complement_after_zero_diag`, 9.630; `winWitt_sector_one_xor_sector_two_one_to_center_step_complement_after_zero_diag`, 9.631) — requiring **only** `settle (z + 2)`. When `z + 1` has also settled by `(z + 1) + 2^k`, `9.622` evaluates to `lhCenter ((z + 2) + 2^k) (2^k - 1) = !zcenter (z + 1)` **without requiring `z + 3` to settle** (`lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag`, 9.625; window readouts `winWitt_testBit_sector_two_sub_one_not_zcenter_after_zero_diag`, 9.626; `winWitt_sector_one_xor_sector_two_sub_one_not_zcenter_after_zero_diag`, 9.627), equating `lhCenter (((z + 1) + P) + 2^k) (P + 2^k)` with `lhCenter ((z + 2) + 2^k) (2^k - 1)` at any doubling zero diagonal `z` (`lhCenter_late_shift_twopow_doubles_eq_after_zero_diag_sub_one`, 9.628).
  - **Sector-2 Zero-Gap `WinWittAgree` Invariance, Refutations Across Zero Diagonals, and Single-Window Spatial `Q`-Flips at Doubling Diagonals (`9.632`–`9.636`)**: Because `WinWittAgree t k Q a L` shifts `(t, b) ↦ (t + Q, b + Q)` at fixed spatial column `r` (`b = (t + 2^(k+1)) - r ↦ b + Q = ((t + Q) + 2^(k+1)) - r`), in the inter-cone zero gap `t + Q < r` it forces same-column late `lhCenter` invariance `lhCenter ((t + Q) + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - r)` (`lhCenter_late_cross_eq_of_winWittAgree_zero_gap`, 9.632 — requiring no settling hypothesis!). This immediately refutes `WinWittAgree t k 2 a L` across any settled zero diagonal `t + r` (`not_winWittAgree_two_scale_cross_zero_gap_of_zero_diag`, 9.633) and refutes `WinWittAgree t k Q a L` whenever `IsZeroDiag (t + r)` and `(t + Q) + r = z + 2` for any zero diagonal `z` (`not_winWittAgree_scale_cross_zero_gap_of_zero_and_after_zero_diag`, 9.634). Furthermore, at any doubling zero diagonal `z = (t + Q) + r`, combining `WinWittAgree t k Q a L` with `9.601` / `9.598` forces an exact spatial `Q`-flip within the **single** window `winWitt t (2^k)` at time `t` (`winWitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winWittAgree`, 9.635) and within the **single** late row `lhCenter (t + 2^k)` (`lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap`, 9.636).
- **Batch 23 (9.637–9.651, attestation `2d90bfcbf4b5d2742846515d61ed24e03b948926b0d18e4eb84cac932c1572ed`)**:
  - **Outer Left-Strip & Sector-2 Center-Slot `WinWittAgree` Invariance, `zcenter` Shift Laws, and Refutations (`9.637`–`9.643`)**: Extends same-column late `lhCenter` invariance under `WinWittAgree` to the outer left strip (`lhCenter ((t + Q) + 2^k) (p + 2^k) = lhCenter (t + 2^k) (p + 2^k)` when `lhCenter (t + Q) p = lhCenter t p`, `lhCenter_late_shift_eq_of_winWittAgree_outer_left_strip`, 9.637), refuting `WinWittAgree t k 2 a L` across any settled zero diagonal `t - p` when `lhCenter (t + 2) p = lhCenter t p` (`not_winWittAgree_two_outer_left_strip_of_zero_diag`, 9.638). At the Sector-2 center slot `t + 2^(k+1)`, `WinWittAgree t k Q a L` locks the `zcenter` shift XOR to the center XOR (`zcenter (t + Q) ⊕ zcenter t = center (t + Q) ⊕ center t`, `zcenter_shift_xor_eq_center_xor_of_winWittAgree_sector_two_center_slot`, 9.639), forcing `zcenter (t + Q) = zcenter t` whenever `center (t + Q) = center t` (`zcenter_shift_eq_of_winWittAgree_sector_two_center_slot`, 9.640) and `zcenter (t + m * P) = zcenter t` under `CenterPeriodic T P` (`periodic_zcenter_shift_eq_of_winWittAgree_sector_two_center_slot`, 9.641). Since `zcenter z = false` (`9.45`) and `zcenter (z + 2) = true` (`9.46`), this refutes `WinWittAgree z k 2 a L` whenever `center (z + 2) = center z` (`not_winWittAgree_two_sector_two_center_slot_of_zero_diag`, 9.642) and refutes `WinWittAgree z1 k (m * P) a L` under `CenterPeriodic T P` whenever `IsZeroDiag z1`, `IsZeroDiag z2`, and `z1 + m * P = z2 + 2` (`not_periodic_winWittAgree_sector_two_center_slot_of_zero_and_after_zero_diag`, 9.643).
  - **Late-Window, Same-Bit, Post-Black Reset, and 1-Step Temporal Flips at Doubling Zero Diagonals Under `WinWittAgree` (`9.644`–`9.651`)**: At any doubling zero diagonal `z = (t + Q) + r` in the Sector-2 zero gap `t + Q ≤ r`, `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - ((r + Q) + 1)` forces spatial `Q`-flips in the late window `winWitt (t + Q) (2^k)` (`winWitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winWittAgree`, 9.644) and late row `lhCenter ((t + Q) + 2^k)` (`lhCenter_late_cross_late_shift_flip_of_doubles_and_winWittAgree_zero_gap`, 9.645), and combining `9.635` with `9.644` yields a same-bit temporal `Q`-flip `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winWittAgree`, 9.646). At the post-black reset step `t + 1` (requiring only `settle (z + 1)` and `settle (z + 2)`, with no settling hypothesis on `z + 3`), `WinWittAgree (t + 1) k Q a L` forces single-window (`winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winWittAgree`, 9.647) and single-row (`lhCenter_late_cross_reset_shift_flip_of_doubles_and_winWittAgree_zero_gap`, 9.648) spatial `Q`-flips, while `WinWittAgree t k Q a L` equates `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` with `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))` (`winWitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winWittAgree`, 9.649). Together, `WinWittAgree` at `t` and `t + 1` transport the 1-step post-black reset flip by `Q` diagonals to `(t + 2^(k+1)) - (r + 1)`: `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_scale_cross_zero_gap_step_flip_at_shift_of_doubles_and_winWittAgree`, 9.650) and `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap`, 9.651).
- **Batch 24 (9.652–9.666, attestation `ecdeba61fbf399c3d5471f717bf90dfe52549e62a765f486845ad1943c86b724`)**:
  - **Cross-Center `lhCenter` Step Law, Forced Two-Cell OR Gates, Twin-Propagated Pinning, and 2-Step `WinWittAgree` Refutations (`9.652`–`9.661`)**: Establishes the exact 1-step local Rule 30 law in cross-center coordinates `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ (lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3)))` (`lhCenter_late_cross_step`, 9.652), showing that any 1-step cross-center complementation forces the adjacent two-cell OR gate to `true` (`lhCenter_late_cross_or_eq_true_of_step_flip`, 9.653). Combining `9.651` with `9.653` at any doubling zero diagonal `z = (t + Q) + r` proves that `WinWittAgree` at `t` and `t + 1` at the **single** bit `(t + 2^(k+1)) - (r + 1)` forces `(lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3))) = true` (`lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap`, 9.654) and `((winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) || (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3))) = true` (`winWitt_scale_cross_zero_gap_or_eq_true_at_shift_of_doubles_and_winWittAgree`, 9.655), refuting `WinWittAgree (t + 1) k Q a L` whenever both cells vanish (`not_winWittAgree_step_pair_at_shift_of_doubles_and_both_false`, 9.661). When `(t + r) + 2` is a settled zero diagonal, `9.654` pins `lhCenter (t + 2^k) (2^k - (r + 3)) = true` (`lhCenter_late_cross_pin_r_plus_three_of_doubles_and_winWittAgree_and_zero_diag_two`, 9.656). Symmetrically, when `(t + r) + 3` is a settled zero diagonal (which holds automatically for `Q = 3`, where `(t + 3) + r = z` is the doubling zero diagonal itself!), `9.654` pins `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`lhCenter_late_cross_pin_r_plus_two_of_doubles_and_winWittAgree_and_zero_diag_three`, 9.657), which combines with the Twin Identity Before a Zero Diagonal (`9.592`) and the spatial `Q`-flip (`9.636`) to pin `lhCenter (t + 2^k) (2^k - (r + 1)) = true` (`lhCenter_late_cross_pin_r_plus_one_of_doubles_and_winWittAgree_and_zero_diag_three`, 9.658; `Q = 3` specialization `lhCenter_late_cross_pin_before_zero_diag_of_doubles_three_and_winWittAgree`, 9.660) and `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` (`lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_winWittAgree_and_zero_diag_three`, 9.659) **without requiring `(t + r) + 1` or `(t + r) + 2` to settle**.
  - **Late Post-Black Reset Spatial `Q`-Flips and Upward `Q`-Transported 1-Step Reset Complementation (`9.662`–`9.666`)**: At bit index `(t + 2^(k+1)) - ((r + Q) + 1)` (requiring only `settle (z + 1)` and `settle (z + 2)`), `WinWittAgree (t + 1) k Q a L` forces post-black reset spatial `Q`-flips in the late window `winWitt ((t + 1) + Q) (2^k)` (`winWitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winWittAgree`, 9.662) and late row `lhCenter (((t + 1) + Q) + 2^k)` (`lhCenter_late_cross_reset_late_shift_flip_of_doubles_and_winWittAgree_zero_gap`, 9.663), as well as a same-bit temporal `Q`-flip at `t + 1` (`winWitt_scale_cross_zero_gap_reset_same_bit_flip_of_doubles_and_winWittAgree`, 9.664). Combining `9.644`/`9.645` with `9.662`/`9.663` and `9.575`/`9.572` at time `t + Q` proves that `WinWittAgree` at `t` and `t + 1` also transports 1-step post-black reset complementation **upward** by `Q` diagonals to `z + Q + 1`: `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_scale_cross_zero_gap_late_step_flip_at_shift_of_doubles_and_winWittAgree`, 9.665) and `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 2)) = !lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 1))` (`lhCenter_late_cross_late_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap`, 9.666).
- **Batch 25 (9.667–9.681, attestation `adce207629c88dd3dec5081ab9d4dfcf0d84cab02e3119f47b6fddc9241ff032`)**:
  - **Upward `Q`-Transported Two-Cell OR Gates, Period-2 Doubling Triple-Zero/One Pinning, and Below-Threshold Spatial `Q`-Periodicity (`9.667`–`9.674`)**: Combining `9.666` (`lhCenter_late_cross_late_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap`) with `9.653` forces the upward `Q`-transported OR gates `(lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 2)) || lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 3))) = true` (`lhCenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap`, 9.667) and `((winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) || (winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 3))) = true` (`winWitt_scale_cross_zero_gap_late_or_eq_true_at_shift_of_doubles_and_winWittAgree`, 9.668) from `WinWittAgree` at `t` and `t + 1` at the single bit `(t + 2^(k+1)) - ((r + Q) + 1)`. For `Q = 2`, `(t + 2) + r = (t + r) + 2` is the doubling zero diagonal itself, so `WinWittAgree` at `t` and `t + 1` at `(t + 2^(k+1)) - (r + 1)` automatically pins `lhCenter (t + 2^k) (2^k - (r + 3)) = true` (`lhCenter_late_cross_pin_r_plus_three_of_doubles_two_and_winWittAgree`, 9.669), `lhCenter (t + 2^k) (2^k - (r + 1)) = false` (`lhCenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winWittAgree`, 9.670), and — via the Twin Identity Before a Zero Diagonal (`9.592`) — `lhCenter (t + 2^k) (2^k - r) = false` (`lhCenter_late_cross_pin_r_false_of_doubles_two_and_winWittAgree`, 9.671) **without requiring `z - 2` or `z - 1` to settle**. Below any doubling threshold `(t + Q) + r ≤ z`, `WinWittAgree t k Q a L` combines with `9.606`/`9.604` to force single-window (`winWitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winWittAgree`, 9.672) and single-row (`lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap`, 9.673) spatial `Q`-periodicity, as well as same-bit temporal `Q`-invariance (`winWitt_scale_cross_zero_gap_same_bit_eq_of_doubles_le_and_winWittAgree`, 9.674).
  - **Single-Time `WinWittAgree t k Q a L` Post-Black Reset Transport Without `WinWittAgree (t + 1)` (`9.675`–`9.681`)**: At any zero diagonal `z = (t + Q) + r` (with no `DoublesAt` hypothesis), a **single** `WinWittAgree t k Q a L` at time `t` transports `lhCenter ((t + Q) + 2^k) (2^k - r) = false` and `lhCenter ((t + Q) + 2^k) (2^k - (r + 2)) = true` down to row `t + 2^k`: `lhCenter (t + 2^k) (2^k - r) = false` (`lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap`, 9.675) and `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap`, 9.676). Substituting `9.676` into `lhCenter_late_cross_step` (`9.652`) forces 1-step complementation `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap`, 9.677) and `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winWittAgree`, 9.678) **from `WinWittAgree t k Q a L` at time `t` alone (with no `DoublesAt` and no `WinWittAgree (t + 1)`)!** Combining `9.675` and `9.676` with `lhCenter_step_succ` pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true` (`lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap`, 9.679), and at a doubling zero diagonal `z = (t + Q) + r`, combining `9.678`/`9.677` with `9.649`/`9.636` forces the post-black reset spatial `Q`-flip in `winWitt (t + 1) (2^k)` (`winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_single_winWittAgree`, 9.680) and `lhCenter ((t + 1) + 2^k)` (`lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap`, 9.681) from `WinWittAgree t k Q a L` at time `t` alone!
- **Batch 26 (9.682–9.696, attestation `dbcec62f38f5cb14d125b6181cf2161962fa8a7041bb256f22eb54fcc2bf624b`)**:
  - **Single-Time `WinWittAgree` Sector-2 Bit Transport, Simultaneous Adjacent Bit Flips, and Period-2 Refutation (`9.682`–`9.686`, `9.695`–`9.696`)**: Translates `9.675`, `9.676`, and `9.679` into exact Sector-2 bit evaluations under a **single** `WinWittAgree t k Q a L` at time `t` (with no `DoublesAt` and no `WinWittAgree (t + 1)`): `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false` (`winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree`, 9.682), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` (`winWitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winWittAgree`, 9.683), and `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = true` (`winWitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree`, 9.684), proving that bit `(t + 2^(k+1)) - r` flips at `t ↦ t + 1` (`winWitt_scale_cross_zero_gap_step_flip_at_shift_of_zero_diag_and_single_winWittAgree`, 9.685) **simultaneously** with the adjacent bit `(t + 2^(k+1)) - (r + 1)` (`9.678`). Furthermore, `9.676` refutes `WinWittAgree t k Q a L` at `(t + 2^(k+1)) - (r + 2)` whenever both `(t + Q) + r` and `(t + r) + 2` are settled zero diagonals (`not_winWittAgree_at_shift_after_zero_diag_of_zero_diag_two`, 9.686), which for `Q = 2` (`(t + r) + 2 = (t + 2) + r = z`!) unconditionally refutes `WinWittAgree t k 2 a L` at `(t + 2^(k+1)) - (r + 2)` across **any** zero diagonal `z = (t + 2) + r` (`not_winWittAgree_two_at_shift_after_zero_diag`, 9.695), while `9.646` refutes `WinWittAgree t k Q a L` across a `Q`-span at any doubling zero diagonal whenever `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`not_winWittAgree_of_doubles_and_same_bit_eq`, 9.696).
  - **Single-Time `WinWittAgree` Twin-Propagated Pinning Without `WinWittAgree (t + 1)` (`9.687`–`9.694`)**: Because `9.676` already pins `lhCenter (t + 2^k) (2^k - (r + 2)) = true` from a **single** `WinWittAgree t k Q a L` at time `t`, combining `9.676` with the Twin Identity Before a Zero Diagonal (`9.592`) when `IsZeroDiag ((t + r) + 3)` pins `lhCenter (t + 2^k) (2^k - (r + 1)) = true` (`lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three`, 9.687) and `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`lhCenter_late_cross_step_one_pin_r_plus_two_false_of_single_winWittAgree_and_zero_diag_three`, 9.688) **with no `DoublesAt` and no `WinWittAgree (t + 1)`**, and — when `DoublesAt Q ((t + Q) + r)` holds — pins `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` (`lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three`, 9.689) and `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = true` on diagonal `z + 3` (`lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three`, 9.690) from `WinWittAgree t k Q a L` at time `t` alone. For `Q = 3`, `(t + 3) + r = (t + r) + 3` is the zero diagonal itself, yielding unconditional single-time `WinWittAgree t k 3 a L` pinnings across **any** zero diagonal (`9.691`, `9.692`) and any period-3 doubling zero diagonal (`9.693`, `9.694`).
- **Batch 27 (9.697–9.711, attestation `9e600494c667f42bdd192200f55b52644d582cff557919d2fc56b646550fa363`)**:
  - **Single-Time `WinWittAgree` Twin-Propagated Sector-2 Window Bit Pinning & Late-Row Pinning (`9.697`–`9.705`)**: Translates the single-time `WinWittAgree t k Q a L` twin-propagated `lhCenter` pinnings (`9.687`–`9.694`) into exact Sector-2 window bit evaluations in `winWitt t (2^k)` and `winWitt (t + 1) (2^k)` (with no `WinWittAgree (t + 1)`): `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` (`winWitt_scale_cross_zero_gap_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three`, 9.697; `Q = 3` unconditional form `winWitt_scale_cross_zero_gap_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree`, 9.702), `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_three`, 9.698; `Q = 3` unconditional form `winWitt_scale_cross_zero_gap_step_one_pin_before_zero_diag_false_of_zero_diag_three_and_single_winWittAgree`, 9.703), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` (`winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three`, 9.699; `Q = 3` unconditional form `winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree`, 9.704), `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = true` on `z + 1` at time `(t + Q) + 2^k` (`lhCenter_late_cross_late_pin_doubling_diag_true_of_single_winWittAgree_and_zero_diag_three`, 9.700), and `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = true` on the post-black reset diagonal `z + 3` without `settle (z + 3)` (`winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three`, 9.701; `Q = 3` unconditional form `winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree`, 9.705).
  - **Period-1 Doubling Pinning & Unconditional Single-Time Refutation `not_winWittAgree_one_of_doubles` (`9.706`–`9.711`)**: For `Q = 1` at any period-1 doubling zero diagonal `z = (t + 1) + r` (`IsZeroDiag ((t + 1) + r)` and `DoublesAt 1 ((t + 1) + r)`, which exists by `doubling_points 1`), `lhCenter (t + 2^k) (2^k - (r + 1))` lies on `z` itself (`= false`), so the single-time spatial 1-flip `9.636` pins `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`lhCenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree`, 9.706; window form `winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree`, 9.707) from `WinWittAgree t k 1 a L` at the **single** bit `(t + 2^(k+1)) - (r + 1)`! Similarly, at time `t + 1`, `lhCenter ((t + 1) + 2^k) (2^k - (r + 2))` lies on the post-zero black diagonal `z + 2` (`= true`), so `9.681` (`Q = 1`) pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false` on diagonal `z + 3` (`lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree`, 9.708; window form `winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree`, 9.709) **without `WinWittAgree (t + 1)` or `settle (z + 3)`**. However, `WinWittAgree t k 1 a L` at `(t + 2^(k+1)) - (r + 3)` equates `lhCenter ((t + 1) + 2^k) (2^k - (r + 3))` (`= false` by `9.708`) with `lhCenter (t + 2^k) (2^k - (r + 3))`, which lies on `t + (r + 3) = z + 2` (`= true` by `lhCenter_late_cross_after_zero_diag`), yielding the **unconditional single-time refutation** `¬ WinWittAgree t k 1 a L` across the 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at **any** period-1 doubling zero diagonal (`not_winWittAgree_one_of_doubles`, 9.710), alongside the general-`Q` single-time refutation `not_winWittAgree_of_doubles_and_zero_diag_three_and_after_three` (9.711).
- **Batch 28 (9.712–9.726, attestation `b34de3ad6c07835ea3a54605296e087b2f0b574b417ac902b6331a2599f4f0e8`)**:
  - **Single-Time `WinWittAgree` `Q`-Transported Twin Identity & Linearized Steps Without `DoublesAt` or `WinWittAgree (t + 1)` (`9.712`–`9.717`, `9.726`)**: Combining the Twin Identity Before a Zero Diagonal (`9.592`, requiring only `settle (((t + Q) + r) + 2) ≤ (t + Q) + 2^k`) with `lhCenter_late_cross_eq_of_winWittAgree_zero_gap` (`9.632`) at `r` and `r + 1` proves that a **single** `WinWittAgree t k Q a L` at time `t` transports the Twin Identity down by `Q` diagonals to `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_twin_at_shift_of_zero_diag_and_winWittAgree_zero_gap`, 9.712) and `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_scale_cross_zero_gap_twin_at_shift_of_zero_diag_and_winWittAgree`, 9.713) **with no `DoublesAt` and no `WinWittAgree (t + 1)`**. Combining `9.675` with `lhCenter_late_cross_step` (`9.652`) linearizes the Rule 30 step `Q` diagonals below any zero diagonal to `lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 2))` (`lhCenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winWittAgree_zero_gap`, 9.714) and `lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 3))` (`lhCenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winWittAgree_zero_gap`, 9.715). Combining `9.714` with `9.712` at `r + 1` cancels the two equal XOR terms (`x ⊕ x = false`), pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`lhCenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap`, 9.716) and `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`winWitt_scale_cross_zero_gap_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree`, 9.717) from a single 3-bit `WinWittAgree t k Q a L` at time `t` whenever `((t + Q) + r) + 3` is a settled zero diagonal — which immediately refutes `WinWittAgree t k Q a L` whenever `(t + r) + 1` is also a settled zero diagonal (`not_winWittAgree_of_zero_diag_one_and_shift_three`, 9.726).
  - **Unconditional 1-Step Forward Propagation of 3-Bit `WinWittAgree t k Q a L`, Doubling-Diagonal 1-Step Spatial `Q`-Flips, and Upward `Q`-Transport (`9.718`–`9.725`)**: Because `winWitt (t + 1) (2^k)` in the Sector-2 zero gap evolves by pure `Φ` (`lhCenter_late_cross_step`), `WinWittAgree t k Q a L` across a 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at time `t` **automatically** propagates 1 step forward in time to `lhCenter (((t + 1) + Q) + 2^k) (2^k - (r + 2)) = lhCenter ((t + 1) + 2^k) (2^k - (r + 2))` (`lhCenter_late_cross_step_one_eq_of_winWittAgree_three_zero_gap`, 9.718) and `(winWitt ((t + 1) + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - (r + 1)) = (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_scale_cross_zero_gap_step_one_eq_of_winWittAgree_three`, 9.719) **with no `IsZeroDiag`, `DoublesAt`, `settle`, or `WinWittAgree (t + 1)` hypothesis**. At any doubling zero diagonal `z = ((t + Q) + r) + 2`, combining Linearization 2 (`9.715`) with below-threshold spatial `Q`-periodicity (`9.673` on `z - 1`) and doubling spatial `Q`-antiperiodicity (`9.636` on `z + 1`) forces a 1-step spatial `Q`-flip on `z + 1` in row `(t + 1) + 2^k` (`lhCenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree_zero_gap`, 9.720) and `winWitt (t + 1) (2^k)` (`winWitt_scale_cross_zero_gap_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree`, 9.721) from `WinWittAgree t k Q a L` at time `t` alone. Finally, at any zero diagonal `z = (t + Q) + r = t + (r + Q)`, a single `WinWittAgree t k Q a L` at time `t` transports `z` (`= false`) and `z + 2` (`= true`) **upward** by `Q` steps in time to `lhCenter ((t + Q) + 2^k) (2^k - (r + Q)) = false` (`lhCenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap`, 9.722) and `lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 2)) = true` (`lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap`, 9.723), upgrading `9.666` and `9.665` to `lhCenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap` (9.724) and `winWitt_scale_cross_zero_gap_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree` (9.725) by dropping **both** `DoublesAt` and `WinWittAgree (t + 1)`.
- **Batch 29 (9.727–9.741, attestation `9bbfd6f218957b589ecd0ef2d683c208e4c9777acc036d0b6052b087c8c9a0d6`)**:
  - **Sharp Zero-Diagonal Minimum Depth (`2 ≤ z`), Non-Constancy of `z + 1` and `z + 3`, and Minimum Gap (`z₁ + 5 ≤ z₂`) (`9.727`–`9.733`)**: Establishes pure zero-state structural laws around every zero diagonal `z` with **zero `settle`, `k`, or `t` hypotheses**: every zero diagonal satisfies `2 ≤ z` (`zero_diag_ge_two`, 9.727 — sharp at `z = 2`); `¬ IsZeroDiag (z + 2)` (`not_isZeroDiag_add_two`, 9.728); `¬ IsBlackDiag (z + 1)` (`not_isBlackDiag_add_one_of_zero_diag`, 9.729, since `IsBlackDiag (z + 1)` and `accumulate_after_zero` would force `IsZeroDiag (z - 1)`, contradicting `zero_then_nonzero`); `¬ IsZeroDiag (z + 3)` (`not_isZeroDiag_add_three`, 9.730, since `IsZeroDiag (z + 3)` and `twin_before_zero` would force `IsBlackDiag (z + 1)`); `¬ IsBlackDiag (z + 3)` (`not_isBlackDiag_add_three_of_zero_diag`, 9.731, since `IsBlackDiag (z + 3)` and `reset_three_after_zero` would force `IsZeroDiag (z + 1)`); and `¬ IsZeroDiag (z + 4)` (`not_isZeroDiag_add_four`, 9.732, since `IsZeroDiag (z + 4)` and `twin_before_zero` would force `IsBlackDiag (z + 3)`). Together with `zero_then_nonzero`, these prove the **Sharp Zero-Diagonal Minimum Gap Theorem**: for all zero diagonals `z₁ < z₂`, `z₁ + 5 ≤ z₂` (`zero_diag_gap_ge_five`, 9.733 — sharp at `z₁ = 2, z₂ = 7`), and prove that both `z + 1` and `z + 3` are neither all-white nor all-black.
  - **Upward `Q`-Transported Sector-2 Bit Evaluations & Unconditional Single-Time Period-3 Refutation `not_winWittAgree_three_of_doubles` (`9.734`–`9.741`)**: Translates `9.722` and `9.723` into Sector-2 window bit evaluations where the `+ Q` time shift and `+ Q` spatial shift cancel: `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = false` (`winWitt_scale_cross_zero_gap_late_eq_false_at_shift_of_zero_diag_and_winWittAgree`, 9.734), `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` (`winWitt_scale_cross_zero_gap_late_eq_true_at_shift_after_zero_diag_and_winWittAgree`, 9.735), `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 1)) = true` (`lhCenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap`, 9.736), and `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = true` (`winWitt_scale_cross_zero_gap_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree`, 9.737). Finally, at **any** period-3 doubling zero diagonal `z = (t + 3) + r` (`IsZeroDiag ((t + 3) + r)` and `DoublesAt 3 ((t + 3) + r)`, which exists by `doubling_points 3`), a **single** `WinWittAgree t k 3 a L` at time `t` pins a 3-step light-cone cascade: `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = true` (`lhCenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree`, 9.738), `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false` (`lhCenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winWittAgree`, 9.739), and — via the Post-Black Reset Identity `9.572` — `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = true` (`lhCenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree`, 9.740). Since `lhCenter (t + 2^k) (2^k - (r + 3)) = false` on `z`, this contradicts `WinWittAgree t k 3 a L` at `(t + 2^(k+1)) - (r + 3)`, proving the **unconditional single-time refutation** `¬ WinWittAgree t k 3 a L` (`not_winWittAgree_three_of_doubles`, 9.741) without `WinWittAgree (t + 1)`, `WinWittAgree (t + 2)`, or `settle (z + 3)`!
- **Batch 30 (9.742–9.756, attestation `0124ed736fab85c2f1d9a130a23ed091f8cfff15976114979f45856d367e65a8`)**:
  - **Period-3 Doubling Sector-2 Window Light-Cone Cascade & 3-Step Same-Bit Negation (`9.742`–`9.745`)**: Translates the 3-step `lhCenter` light-cone cascade (`9.738`–`9.740`) at any period-3 doubling zero diagonal `z = (t + 3) + r` into Sector-2 `winWitt` window bit evaluations from a **single** 3-bit `WinWittAgree t k 3 a L` at time `t` (with no `WinWittAgree (t + 1..2)` or `settle (z + 3)`): `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` (`winWitt_scale_cross_zero_gap_step_one_pin_r_plus_two_true_of_doubles_three_and_single_winWittAgree`, 9.742), `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - r) = false` (`winWitt_scale_cross_zero_gap_step_two_pin_r_false_of_doubles_three_and_single_winWittAgree`, 9.743), and `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = true` (`winWitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winWittAgree`, 9.744). Consequently, at fixed bit index `(t + 2^(k+1)) - r`, `winWitt (t + m) (2^k)` alternates `(false, true, false, true)` across `m = 0, 1, 2, 3`, so `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` (`winWitt_scale_cross_zero_gap_same_bit_r_flip_three_of_doubles_three_and_single_winWittAgree`, 9.745).
  - **General-`Q` `(t + r) + 4` Zero-Diagonal Pinning & Period-4 Doubling 3-Step Light-Cone Cascade (`9.746`–`9.756`)**: Whenever both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals (which holds automatically for `Q = 4`, where `(t + r) + 4 = (t + 4) + r = z`!), in row `(t + 1) + 2^k` cell `2^k - (r + 3)` lies on `(t + r) + 4`, so the Twin Identity Before a Zero Diagonal (`9.592`) equates `lhCenter ((t + 1) + 2^k) (2^k - (r + 2))` with `lhCenter ((t + 1) + 2^k) (2^k - (r + 1))` (`= true` by `9.679`), pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` (`lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four`, 9.746; `Q = 4` specialization `9.750`) and — via `9.677` — `lhCenter (t + 2^k) (2^k - (r + 1)) = false` (`lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four`, 9.747; `Q = 4` specialization `9.751`) **with no `DoublesAt` and no `WinWittAgree (t + 1)`**, and — when `DoublesAt Q ((t + Q) + r)` holds — pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = true` on `z + 1` (`lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four`, 9.748; `Q = 4` specialization `9.752`). For `Q = 4`, the Twin Identity at time `t` also pins `lhCenter (t + 2^k) (2^k - (r + 3)) = true` (`lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree`, 9.749) and — via `9.632` and the Post-Black Reset Identity `9.572` at `t + 3` — `lhCenter ((t + 3) + 2^k) (2^k - (r + 2)) = false` on `z + 1` (`lhCenter_late_cross_step_three_pin_r_plus_two_false_of_zero_diag_four_and_single_winWittAgree`, 9.756) across **any** zero diagonal `z = (t + 4) + r`, while at a period-4 doubling zero diagonal `9.752` cascades through `t + 1`, `t + 2`, and `t + 3` to pin `lhCenter ((t + 1) + 2^k) (2^k - (r + 4)) = false` (`9.753`), `lhCenter ((t + 2) + 2^k) (2^k - (r + 3)) = true` (`9.754`), and `lhCenter ((t + 3) + 2^k) (2^k - (r + 4)) = false` on `z + 3` without `settle (z + 3)` (`9.755`).
- **Batch 31 (9.757–9.771, attestation `bac6bb1ea80bf829da07b993b06f7444435ad49d89df46bcfa211160d426a439`)**:
  - **Post-Zero OR-Absorption Laws on Diagonal `z + 4` & Unconditional Single-Time Period-4 Refutation `not_winWittAgree_four_of_doubles` (`9.757`–`9.762`)**: Establishes the 1-step post-zero OR-absorption law on diagonal `z + 4` (`lhCenter_late_cross_step_absorb_false_after_zero_diag`, 9.757: whenever `z = t + r` is a zero diagonal with `settle (z + 2) ≤ t + 2^k` and `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on `z + 3`, the OR gate in `lhCenter_late_cross_step` absorbs `lhCenter (t + 2^k) (2^k - (r + 4))` via `true || _ = true` and combines with `lhCenter (t + 2^k) (2^k - (r + 2)) = true` on `z + 2` to force `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false` on `z + 4` **without `settle (z + 3)` or `settle (z + 4)`**) and the 2-step post-zero reset-and-absorption law from `z + 1` to `z + 4` (`lhCenter_late_cross_two_step_absorb_false_after_zero_diag`, 9.758: whenever `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on `z + 1`, `9.572` forces `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` on `z + 3`, which then forces `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false` on `z + 4`). At any period-4 doubling zero diagonal `z = (t + 4) + r` (`IsZeroDiag ((t + 4) + r)` and `DoublesAt 4 ((t + 4) + r)`, which exists by `doubling_points 4`), applying `9.572` and `9.758` to `9.753` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 4)) = false` on `z + 1`) pins `lhCenter ((t + 2) + 2^k) (2^k - (r + 5)) = true` on `z + 3` (`lhCenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winWittAgree`, 9.759) and `lhCenter ((t + 3) + 2^k) (2^k - (r + 5)) = false` on `z + 4` (`lhCenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winWittAgree`, 9.760). Combining `9.755` (`lhCenter ((t + 3) + 2^k) (2^k - (r + 4)) = false` on `z + 3`), `9.760`, and `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = true` (on `z + 2`) in `lhCenter_late_cross_step (t + 3) k (r + 2)` pins `lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true` on `z + 4` (`lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winWittAgree`, 9.761). Since `lhCenter (t + 2^k) (2^k - (r + 4)) = false` on `z`, this contradicts `WinWittAgree t k 4 a L` at `(t + 2^(k+1)) - (r + 4)`, proving the **unconditional single-time refutation** `¬ WinWittAgree t k 4 a L` (`not_winWittAgree_four_of_doubles`, 9.762) across the 5-bit interval `[(t + 2^(k+1)) - (r + 4), (t + 2^(k+1)) - r]` **without `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)`**!
  - **General-`Q` `(t + r) + 4` and Period-4 Sector-2 Window Bit Pinning & 4-Step Same-Bit Negation (`9.763`–`9.771`)**: Translates `9.746`–`9.752` and `9.761` into exact Sector-2 `winWitt` window bit evaluations from a single 3-bit `WinWittAgree t k Q a L` at time `t`: `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` (`winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winWittAgree_and_zero_diag_four`, 9.763; `Q = 4` specialization `9.767`), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four`, 9.764; `Q = 4` specialization `9.768`), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = true` on `z + 1` (`winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four`, 9.765; `Q = 4` specialization `9.769`), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` for `Q = 4` (`winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree`, 9.766), and `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = true` at a period-4 doubling zero diagonal (`winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winWittAgree`, 9.770), proving the 4-step same-bit negation `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` (`winWitt_scale_cross_zero_gap_same_bit_r_flip_four_of_doubles_four_and_single_winWittAgree`, 9.771).
- **Batch 32 (9.772–9.786, attestation `3bd177654d675ba28dfa34824867dbf359b9001854d7745e3b0d78c7c0feb91d`)**:
  - **Algebraic Uniqueness of the Gap-5 Zero-Diagonal Pair `(2, 7)` & Sharp Gap `z₁ + 6 ≤ z₂` Above `z = 2` (`9.772`–`9.779`)**: Using only pure zero-state `CompilePoints` laws (`zero_before_black_diag`, `twin_before_zero`, `E_step`, `black_after_zero_diag`, `reset_three_after_zero`, `accumulate_after_zero`) with **zero `settle`, `k`, or `t` hypotheses**, proves around every zero diagonal `z`: `¬ IsBlackDiag (z + 4)` (`not_isBlackDiag_add_four_of_zero_diag`, 9.772), `¬ IsBlackDiag (z + 5)` (`not_isBlackDiag_add_five_of_zero_diag`, 9.773), and `¬ IsBlackDiag (z + 6)` (`not_isBlackDiag_add_six_of_zero_diag`, 9.774), since `zero_before_black_diag` would otherwise contradict `not_isZeroDiag_add_two/three/four` (`9.728`, `9.730`, `9.732`). Furthermore, if both `z` and `z + 5` are zero diagonals, `twin_before_zero` equates `z + 3` and `z + 4`, so `E_step (z + 2)` behind the all-black diagonal `z + 2` forces `z + 3` (and hence `z + 1`, by `reset_three_after_zero`) to alternate at every time step, which by `accumulate_after_zero` forces `IsBlackDiag (z - 1)` (`isBlackDiag_sub_one_of_zero_diag_and_add_five`, 9.775). For `z ≥ 3`, `IsBlackDiag (z - 1)` forces `IsZeroDiag (z - 3)` (`zero_before_black_diag`), contradicting `zero_diag_gap_ge_five (z - 3) z` (`9.733`), so **`z ≤ 2`** (`zero_diag_le_two_of_add_five`, 9.776 — algebraically pinning `(2, 7)` as the unique gap-5 zero-diagonal pair in all of Rule 30!). Consequently, for every zero diagonal `z > 2`, `¬ IsZeroDiag (z + 5)` (`not_isZeroDiag_add_five_of_gt_two`, 9.777) and `¬ IsBlackDiag (z + 7)` (`not_isBlackDiag_add_seven_of_gt_two_and_zero_diag`, 9.779), and for all zero diagonals `2 < z₁ < z₂`, **`z₁ + 6 ≤ z₂`** (`zero_diag_gap_ge_six_of_gt_two`, 9.778).
  - **Period-4 Doubling Intermediate Sector-2 Window Light-Cone Cascade & General-`Q` `(t + r) + 4` Reset-Diagonal Pinning (`9.780`–`9.786`)**: Translates the intermediate `lhCenter` light-cone cascade steps (`9.753`–`9.755`, `9.759`–`9.760`) at any period-4 doubling zero diagonal `z = (t + 4) + r` into Sector-2 `winWitt` window bit evaluations from a **single** 3-bit `WinWittAgree t k 4 a L` at time `t` (with no `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)`): `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = false` (`winWitt_scale_cross_zero_gap_step_one_pin_r_plus_three_false_of_doubles_four_and_single_winWittAgree`, 9.780), `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` (`winWitt_scale_cross_zero_gap_step_two_pin_r_plus_one_true_of_doubles_four_and_single_winWittAgree`, 9.781), `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`winWitt_scale_cross_zero_gap_step_three_pin_r_plus_one_false_of_doubles_four_and_single_winWittAgree`, 9.782), `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` (`winWitt_scale_cross_zero_gap_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree`, 9.783), and `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false` (`winWitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winWittAgree`, 9.784), proving the 3-step same-bit negation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2))` (`winWitt_scale_cross_zero_gap_same_bit_r_plus_two_flip_three_of_doubles_four_and_single_winWittAgree`, 9.785). Finally, for arbitrary `Q`, combining `9.748` (`lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = true` on `z + 1`) with the Post-Black Reset Identity `9.572` pins `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = false` on the reset diagonal `z + 3` (`lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four`, 9.786) from `WinWittAgree t k Q a L` at time `t` alone **without `settle (z + 3)` or `WinWittAgree (t + 1)`**.
- **Batch 33 (9.787–9.801, attestation `1c46f8fb9979e16268ff7ccaab47b4c4e96099348e4876d80dc309148e3efa92`)**:
  - **General-`Q` Reset-Diagonal Sector-2 Window Bit Pinning & 1-Step Same-Bit Negations (`9.787`–`9.789`)**: Translates `9.786` into the Sector-2 window bit evaluation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = false` (`winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four`, 9.787), and combines `(9.765, 9.787)` and `(9.699, 9.701)` to prove that at fixed bit index `(t + 2^(k+1)) - ((r + Q) + 1)`, `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))` from a single `WinWittAgree t k Q a L` at time `t` without `settle (z + 3)` whenever `(t + r) + 4` (`winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_four`, 9.788) or `(t + r) + 3` (`winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_three`, 9.789) is a settled zero diagonal.
  - **General-`Q` `(t + r) + 5` Zero-Diagonal Self-Canceling Parity Pinning & Unconditional Single-Time Period-5 Refutation `not_winWittAgree_five_of_doubles` (`9.790`–`9.801`)**: Whenever both `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals (which holds automatically for `Q = 5`, where `(t + 5) + r = (t + r) + 5 = z`), a single `WinWittAgree t k Q a L` at time `t` forces `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = !lhCenter (t + 2^k) (2^k - (r + 3))` (`lhCenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winWittAgree_and_zero_diag_five`, 9.790), the spatial stride-2 equality `lhCenter (t + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 3))` (`lhCenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winWittAgree_and_zero_diag_five`, 9.791), and the 2-step same-cell return `lhCenter ((t + 2) + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five`, 9.792). Combining `9.792` with `9.679` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true`) and `9.675` (`lhCenter (t + 2^k) (2^k - r) = false`) yields the self-canceling parity equation `B = !(A ⊕ B)` for `A = lhCenter (t + 2^k) (2^k - (r - 1))` and `B = lhCenter (t + 2^k) (2^k - (r + 1))`, which unconditionally pins **`lhCenter (t + 2^k) (2^k - (r - 1)) = true`** (`lhCenter_late_cross_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five`, 9.793) with **no `DoublesAt` and no `WinWittAgree (t + 1..2)`**. At any period-5 doubling zero diagonal `z = (t + 5) + r` (`IsZeroDiag ((t + 5) + r)` and `DoublesAt 5 ((t + 5) + r)`, which exists by `doubling_points 5`), below-threshold spatial 5-periodicity (`9.673`) transports `A = true` at `r - 1` by `+ 5` to `r + 4` on `z - 1 = (t + 4) + r`, pinning `lhCenter (t + 2^k) (2^k - (r + 4)) = true` (`9.794`), `lhCenter (t + 2^k) (2^k - (r + 3)) = true` (`9.795`), `lhCenter (t + 2^k) (2^k - (r + 1)) = true` (`9.796`), and — via doubling spatial 5-antiperiodicity (`9.636`) — `lhCenter (t + 2^k) (2^k - (r + 6)) = false` on `z + 1` (`9.797`). Propagating `z + 1` against `z - 1` across `t ↦ t + 1 ↦ t + 2 ↦ t + 3` pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 5)) = true` (`9.798`), `lhCenter ((t + 2) + 2^k) (2^k - (r + 4)) = true` (`9.799`), and `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = false` (`9.800`). Finally, the 2-step post-zero reset-and-absorption law (`9.758`) applied to `9.800` pins `lhCenter ((t + 5) + 2^k) (2^k - (r + 4)) = false` on `z + 4`, contradicting `lhCenter (t + 2^k) (2^k - (r + 4)) = true` (`9.794`) and proving the **unconditional single-time refutation** `¬ WinWittAgree t k 5 a L` (`not_winWittAgree_five_of_doubles`, 9.801) without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)`!
- **Batch 34 (9.802–9.816, attestation `25c55697918829bb244e600a5cc2aeb5eca4c3751fc2f1ce125eba3392b94fc1`)**:
  - **Period-5 Doubling Post-Black Reset Steps (`t + 4`, `t + 5`) & Complete Sector-2 Window Light-Cone Cascade (`9.802`–`9.816`)**: Explicitly records the two post-black reset steps (`lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true` on `z + 3`, `lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree`, 9.802; `lhCenter ((t + 5) + 2^k) (2^k - (r + 4)) = false` on `z + 4`, `lhCenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winWittAgree`, 9.803) and the 2-step return `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = true` on `z - 1` (`lhCenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree`, 9.814), and translates the entire `Q = 5` light-cone cascade (`9.793`–`9.803`, `9.814`) into Sector-2 `winWitt` window bit evaluations (`9.804`–`9.813`, `9.815`) and the 5-step same-bit negation `(winWitt (t + 5) (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r - 1))` (`winWitt_scale_cross_zero_gap_same_bit_r_sub_one_flip_five_of_doubles_five_and_single_winWittAgree`, 9.816) from a single `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)`.
- **Batch 35 (9.817–9.831, attestation `e2f2da7b657e9883dff12557c2bb4982dc80ef3bd3746f45c78472f559e71353`)**:
  - **Exact Finite Target Criteria for `¬ CenterPeriodic T P` (`9.817`–`9.822`)**: Directly formalizes the reviewer's Exact Finite Target in explicit `¬ CenterPeriodic T P` form for **every** period `P > 0` and multiple `m > 0` at once: whenever `T ≤ t` and `t + m * P ≤ S + 1`, `¬ CenterPeriodic T P` follows immediately from right-half column-`1` window agreement `RhColAgree t (m * P) 1 S` (`not_centerPeriodic_of_rhColAgree_one_horizon`, 9.817), left-half column-`-1` window agreement `LhColAgree t (m * P) 1 S` (`not_centerPeriodic_of_lhColAgree_one_horizon`, 9.818), single-time right-half spatial band agreement `RhBandAgree t (m * P) 0 (S + 1)` (`not_centerPeriodic_of_rhBandAgree_zero_horizon`, 9.819), `K`-column inward determination `RhColAgree t (m * P) (1 + K) (S + K) ∧ RhOrAgree t (m * P) (1 + K) (S + K)` from any outer column `1 + K` (`not_centerPeriodic_of_rhCenter_inward_determine_horizon`, 9.820), or `RhOrAgree t (m * P) 1 S` together with initial agreement `rhCenter (t + m * P) 1 = rhCenter t 1` at the single step `t` (`periodic_rhColAgree_one_of_rhOrAgree_one`, 9.821; `not_centerPeriodic_of_rhOrAgree_one_horizon`, 9.822).
  - **Scale-Free Real-Orbit Doubling Laws & Universal-in-`Q` Agreement Production Across the Settled Left Strip (`9.823`–`9.831`)**: Eliminates the dyadic scale `k` and `2^k` shift completely from the settled left-diagonal and `lhCenter` doubling laws so they hold for **every shift `Q` at once** directly on the real orbit: `ldiag d (t + Q) = ldiag d t` for all `d ≤ z` and `t ≥ settle d` under `DoublesAt Q z` (`ldiag_settled_periodic_of_doubles_le`, 9.823), `ldiag (z + 1) (t + Q) = !ldiag (z + 1) t` for all `t ≥ settle (z + 1)` (`ldiag_settled_antiperiodic_of_doubles`, 9.824), `lhCenter (t + Q) (p + Q) = lhCenter t p` for all `t, p` with `t - p ≤ z` and `settle (t - p) ≤ t` with no `p ≤ t` bound (`lhCenter_diag_shift_periodic_of_doubles_le`, 9.825), `lhCenter ((t + 1) + Q) (p + Q) = !lhCenter (t + 1) p` on `z + 1` (`lhCenter_diag_shift_antiperiodic_of_doubles`, 9.826), and single-row spatial `Q`-periodicity `lhCenter t (p + Q) = lhCenter t p` (`lhCenter_spatial_periodic_of_doubles_le_and_lhBandAgree`, 9.827) and `Q`-flip `lhCenter (t + 1) (p + Q) = !lhCenter (t + 1) p` (`lhCenter_spatial_antiperiodic_of_doubles_and_lhBandAgree`, 9.828) under `LhBandAgree`. Furthermore, proves that `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = false` for all `t - p ≤ k` with `settle (t - p) ≤ t` with no `p ≤ t` bound (`winWitt_testBit_settled_left_ge`, 9.829), which **produces `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` for every shift `Q` at once** across the settled left strip `(t + Q) - p0 ≤ k` (`winWittAgree_settled_left_strip`, 9.830) and transports `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` inward to `LhBandAgree t Q p0 L` **with no `WinWittAgree` premise** (`lhBandAgree_inward_of_settled_left_strip`, 9.831).
- **Batch 36 (9.832–9.846, attestation `f04350732fc6c400d8d5fd491f91c8e9547ae8959f46705a63a57e18553673c5`)**:
  - **Forward `2^k`-Scale Transport Across the Settled Left Strip & Scale-Free Real-Orbit Zero-Diagonal, Post-Zero Black, Twin, and Post-Black Reset Laws (`9.832`–`9.842`)**: Completes the forward `2^k`-scale transport `LhBandAgree t Q p0 L → LhBandAgree (t + 2^k) Q (p0 + 2^k) L` without `WinWittAgree` premise (`lhBandAgree_step_of_settled_left_strip`, 9.832) and the pointwise diagonal-shift identity `lhCenter (t + 2^k) (p + 2^k) = lhCenter t p` for `t - p ≤ k` (`lhCenter_scale_step_settled_left_ge`, 9.833). Eliminating `k` and `2^k` completely via `E_eq_D` and `zero_diag_ge_two`, proves directly on the real orbit (with **no `p ≤ t` bound and no scale `k`**): `ldiag z t = false` (`ldiag_of_zero_diag`, 9.834), `ldiag (z + 2) t = true` (`ldiag_after_zero_diag`, 9.835), `lhCenter t p = false` (`lhCenter_of_zero_diag`, 9.836), `lhCenter (t + 2) p = true` (`lhCenter_after_zero_diag`, 9.837), the **Scale-Free Real-Orbit Twin Identity** `lhCenter t (p + 2) = lhCenter t (p + 1)` before any settled zero diagonal `t - p` without settling `(t - p) - 2` or `(t - p) - 1` (`lhCenter_twin_before_zero_diag`, 9.838), the **Scale-Free Post-Black Reset Complementation** `lhCenter (t + 3) (p + 1) = !lhCenter (t + 2) (p + 2)` without settling `z + 1` or `z + 3` (`lhCenter_reset_after_zero_diag`, 9.839), the 2-step same-column flip `lhCenter (t + 2) p = !lhCenter t p` (`lhCenter_two_step_same_col_flip_of_zero_diag`, 9.840), and the scale-free `LhBandAgree` refutations `not_lhBandAgree_two_of_zero_diag` (9.841) and `not_lhBandAgree_of_zero_and_after_zero_diag` (9.842).
  - **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Transport Across Any Zero Diagonal (`9.843`–`9.846`)**: For **every shift `Q` at once**, a **single** `LhBandAgree t Q p0 L` at time `t` (with no `LhBandAgree (t + 1)`, no `DoublesAt`, no scale `k`, and no `winWitt`) transports zero-diagonal vanishing and post-zero blackness down by `Q` steps to row `t`: `lhCenter t p = false` when `IsZeroDiag ((t + Q) - p)` (`lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree`, 9.843) and `lhCenter t p = true` when `IsZeroDiag ((t + Q) - (p + 2))` (`lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree`, 9.844), which in turn forces 1-step post-black reset complementation `lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2)` when `IsZeroDiag ((t + Q) - (p + 3))` (`lhCenter_step_flip_at_shift_after_zero_diag_of_single_lhBandAgree`, 9.845) and pins `lhCenter (t + 1) (p + 1) = true` when `IsZeroDiag ((t + Q) - (p + 2))` (`lhCenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhBandAgree`, 9.846).
- **Batch 37 (9.847–9.861, attestation `95df469142c084af7453b0f9254623d5631b9c0cba3baf12d5742cb0e3cd843a`)**:
  - **Producing Center-Anchored `LhBandAgree` from `RhColAgree` & Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Twin/Linearization/OR-Absorption Laws (`9.847`–`9.855`)**: Under `CenterPeriodic T P` (`0 < P`), `RhColAgree t (m * P) 1 S` directly produces single-time left-half spatial band agreement `LhBandAgree t (m * P) 0 (S + 1)` (`periodic_lhBandAgree_zero_of_rhColAgree_one`, 9.847) and, more generally, center-anchored `LhBandAgree (t + s) (m * P) 0 (L + 1)` at **every** intermediate time `t + s` from `RhColAgree t (m * P) 1 (L + s)` (`periodic_lhBandAgree_steps_of_rhColAgree_one`, 9.848 — losing only `s` steps of width instead of `2 * s`). On the left half, for **every shift `Q` at once**, a **single** `LhBandAgree t Q p0 L` at time `t` (with no `LhBandAgree (t + 1)`, no `DoublesAt`, no scale `k`, and no `winWitt`) transports the twin identity down by `Q` steps to `lhCenter t (p + 2) = lhCenter t (p + 1)` when `IsZeroDiag ((t + Q) - p)` (`lhCenter_twin_at_shift_of_zero_diag_and_lhBandAgree`, 9.849), linearizes the 1-step Rule 30 evolution at row `t` into pure XOR when `IsZeroDiag ((t + Q) - p)` (`lhCenter_linear_step_one_at_shift_of_zero_diag_and_lhBandAgree`, 9.850) or `IsZeroDiag ((t + Q) - (p + 1))` (`lhCenter_linear_step_two_at_shift_of_zero_diag_and_lhBandAgree`, 9.851), cancels the twin pair to pin `lhCenter (t + 1) (p + 1) = false` (`lhCenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhBandAgree`, 9.852), and refutes `LhBandAgree t Q p0 L` whenever both `t - (p + 2)` and `(t + Q) - p` are zero diagonals (`not_lhBandAgree_of_zero_diag_two_and_shift_zero_diag`, 9.853). Also establishes the scale-free real-orbit 1-step and 2-step post-zero OR-absorption laws on diagonal `z + 4` (`lhCenter_step_absorb_false_after_zero_diag`, 9.854; `lhCenter_two_step_absorb_false_after_zero_diag`, 9.855) without settling `z + 1`, `z + 3`, or `z + 4`.
  - **Unconditional Cross-Center Zero-Diagonal and Doubling Laws Dropping the Exponential Scale Barrier `z ≤ k` (`9.856`–`9.861`)**: Removes the `t + r ≤ k` / `z ≤ k` constraint completely from the cross-center `lhCenter (t + 2^k) (2^k - r)` laws (replacing `t + r ≤ k` with the natural geometric coordinate condition `r ≤ 2^k` so `2^k` only needs to exceed `r` linearly, not `2^(t + r)` exponentially!): `lhCenter (t + 2^k) (2^k - r) = false` (`lhCenter_late_cross_of_zero_diag_uncond`, 9.856), `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`lhCenter_late_cross_after_zero_diag_uncond`, 9.857), `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_reset_after_zero_diag_uncond`, 9.858), `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))` (`lhCenter_late_cross_twin_before_zero_diag_uncond`, 9.859), `lhCenter ((t + Q) + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + Q))` (`lhCenter_late_cross_periodic_of_doubles_le_uncond`, 9.860), and `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = !lhCenter (t + 2^k) (2^k - ((r + Q) + 1))` (`lhCenter_late_cross_antiperiodic_of_doubles_uncond`, 9.861).
- **Batch 38 (9.862–9.876, attestation `af013936b8f5be1b1bd4eb0b576144945f66d665dc97cc9602f200e39860c6d1`)**:
  - **Unconditional Sector-2 `winWitt` Cross-Center & Inter-Cone Zero-Gap Laws Dropping `z ≤ k` (`9.862`–`9.871`)**: Combines `winWitt_testBit_scale_cross_cone` (which requires only the linear in-cone bound `t + r < 2^k`) with the unconditional cross-center laws `9.856`–`9.861` to eliminate `t + r ≤ k` and `z ≤ k` completely from the Sector-2 `winWitt` zero-diagonal and doubling laws: `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = rhCenter t r` (`winWitt_testBit_scale_cross_of_zero_diag_uncond`, 9.862) and `= false` for `t < r` (`winWitt_testBit_scale_cross_zero_gap_of_zero_diag_uncond`, 9.863); `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !rhCenter t (r + 2)` (`winWitt_testBit_scale_cross_after_zero_diag_uncond`, 9.864) and `= true` for `t < r + 2` (`winWitt_testBit_scale_cross_zero_gap_after_zero_diag_uncond`, 9.865); adjacent twin bit equality `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_testBit_scale_cross_zero_gap_twin_before_zero_diag_uncond`, 9.866); 1-step Sector-2 bit flip `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (`winWitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond`, 9.867); and universal-in-`Q` Sector-2 `Q`-periodicity (`winWitt_scale_cross_periodic_of_doubles_le_uncond`, 9.868; `winWitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond`, 9.869) and `Q`-antiperiodicity (`winWitt_scale_cross_antiperiodic_of_doubles_uncond`, 9.870; `winWitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond`, 9.871).
  - **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Doubling-Diagonal Cascade Directly at Row `t` (`9.872`–`9.876`)**: Because `zero_diag_ge_two` guarantees `2 ≤ z` for every zero diagonal `z`, any zero diagonal `z = t - (p + 2)` or `z = t - (p + 3)` already places `z + 1`, `z + 2`, and `z + 3` inside row `t` and row `t + 1` with **no `p ≤ t` bound, no `t + 2` offset, no scale `k`, and no `winWitt`**: `lhCenter t p = true` when `IsZeroDiag (t - (p + 2))` (`lhCenter_at_t_after_zero_diag`, 9.872), `lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2)` when `IsZeroDiag (t - (p + 3))` (`lhCenter_step_one_reset_after_zero_diag`, 9.873), `lhCenter (t + Q) (p + Q) = !lhCenter t p` when `IsZeroDiag (t - (p + 1))` and `DoublesAt Q (t - (p + 1))` (`lhCenter_diag_shift_antiperiodic_at_t_of_doubles`, 9.874), `lhCenter t (p + Q) = !lhCenter t p` under a single `LhBandAgree t Q p0 L` at time `t` (`lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree`, 9.875), and the space-time equivalence `lhCenter t ((p + 2) + Q) = lhCenter (t + 1) (p + 1)` equating `(t, (p + 2) + Q)` on `z + 1` with `(t + 1, p + 1)` on `z + 3` from `LhBandAgree t Q p0 L` at time `t` alone **without `settle (z + 3)` or `LhBandAgree (t + 1)`** (`lhCenter_spatial_doubles_eq_step_one_reset_of_lhBandAgree`, 9.876).
- **Batch 39 (9.877–9.891, attestation `6b1636b61493ee22a82a726988797dfe9724a7a4828512a0f0c012f34e7da782`)**:
  - **Scale-Free Universal-in-`Q` Post-Black Reset Antiperiodicity & Scale-Free Real-Orbit `Q = 1` Single-Time `LhBandAgree`/`RhColAgree` Refutations (`9.877`–`9.883`)**: Proves directly on the real orbit (with no scale `k`, no `2^k`, and no `winWitt`) the space-time equivalence `lhCenter (t + Q) ((p + 2) + Q) = lhCenter (t + 1) (p + 1)` (`lhCenter_doubles_eq_step_one_reset`, 9.877), diagonal-shift antiperiodicity `lhCenter ((t + Q) + 1) ((p + Q) + 1) = !lhCenter (t + 1) (p + 1)` on `z + 3` without `settle (z + 3)` (`lhCenter_step_one_reset_antiperiodic_of_doubles`, 9.878), and spatial `Q`-flip `lhCenter (t + 1) ((p + 1) + Q) = !lhCenter (t + 1) (p + 1)` at row `t + 1` from a **single** `LhBandAgree t Q p0 L` at time `t` (`lhCenter_step_one_reset_shift_flip_of_doubles_and_single_lhBandAgree`, 9.879). For `Q = 1`, under a single `LhBandAgree t 1 p0 L` at time `t`, pins `lhCenter t (p + 1) = true` on `z + 1` (`lhCenter_pin_doubling_diag_true_of_doubles_one_and_lhBandAgree`, 9.880) and `lhCenter (t + 1) (p + 1) = false` on `z + 3` (`lhCenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhBandAgree`, 9.881), proving the scale-free single-time refutations `¬ LhBandAgree t 1 p0 L` (`not_lhBandAgree_one_of_doubles`, 9.882) and `¬ RhColAgree t 1 1 S` under `CenterPeriodic T 1` (`not_periodic_rhColAgree_one_of_doubles_one`, 9.883) without `settle (z + 3)` or `LhBandAgree (t + 1)`.
  - **Scale-Free Universal-in-`Q` Shift-`3` Pinning & Scale-Free Real-Orbit `Q = 3` Single-Time `LhBandAgree` Cascade and Refutation (`9.884`–`9.891`)**: For arbitrary shift `Q`, whenever `IsZeroDiag (t - p)` and `IsZeroDiag ((t + Q) - (p + 3))` hold, a single `LhBandAgree t Q p0 L` at time `t` pins `lhCenter t (p + 2) = true` on `(t - p) - 2` (`lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three`, 9.884) and `lhCenter (t + 1) (p + 1) = false` on `(t - p) - 1` (`lhCenter_step_one_pin_plus_one_false_of_lhBandAgree_and_zero_diag_three`, 9.885). Since `(t + 3) - (p + 3) = t - p` is the **exact same zero diagonal `z = t - p`**, specializing to `Q = 3` pins `lhCenter t (p + 2) = true` (`lhCenter_pin_before_zero_diag_of_zero_diag_three_and_lhBandAgree`, 9.886) from `IsZeroDiag (t - p)` alone, and under `DoublesAt 3 (t - (p + 1))` pins `lhCenter t p = false` on `z + 1` (`lhCenter_pin_doubling_diag_false_of_doubles_three_and_lhBandAgree`, 9.887), `lhCenter (t + 1) (p + 1) = true` (`lhCenter_step_one_pin_plus_one_true_of_doubles_three_and_lhBandAgree`, 9.888), `lhCenter (t + 2) (p + 2) = false` (`lhCenter_step_two_pin_plus_two_false_of_doubles_three_and_lhBandAgree`, 9.889), and `lhCenter (t + 3) (p + 1) = true` on `z + 3` (`lhCenter_step_three_pin_plus_one_true_of_doubles_three_and_lhBandAgree`, 9.890), proving the scale-free single-time refutation `¬ LhBandAgree t 3 p0 L` (`not_lhBandAgree_three_of_doubles`, 9.891) directly on the real orbit with **no scale `k`, no `2^k`, no `winWitt`, no `settle (z + 3)`, and no `LhBandAgree (t + 1..2)`**.
- **Batch 40 (9.892–9.906, attestation `4034c2de10d44a13e1681d29a672e39fdb4198f475c6cce818118a491968e275`)**:
  - **The Zero-Diagonal Period-Doubling Laws & Unbounded Dyadic Doubling Zero Diagonals (`9.892`–`9.900`)**: Establishes the structural period-doubling and dyadic period laws on the settled left diagonals and zero diagonals: every settled left diagonal `d` has power-of-two period `2^d` (`ldiag d (t + twopow d) = ldiag d t`, `ldiag_settled_twopow_periodic`, 9.892), and all settled diagonals `d ≤ e` share common dyadic period `2^e` (`ldiag d (t + twopow e) = ldiag d t`, `ldiag_settled_twopow_periodic_le`, 9.893); at any doubling zero diagonal `z` (`IsZeroDiag z` and `DoublesAt Q z`), diagonal `z + 1` repeats at doubled period `Q + Q` (`ldiag_settled_two_mul_periodic_of_doubles`, 9.894), diagonal `z + 3` flips at half-period `Q` (`ldiag_settled_reset_antiperiodic_of_doubles`, 9.895), and every settled diagonal `d ≤ z + 3` repeats under `Q + Q` (`ldiag_settled_two_mul_periodic_le_add_three_of_doubles`, 9.896). Moreover, proves that for every dyadic exponent `e` there exists a zero diagonal `z` with `IsZeroDiag z ∧ DoublesAt (twopow e) z` (`exists_zero_diag_doublesAt_twopow`, 9.897), for every `m > 0` and `P > 0` there exists a zero diagonal `z` with `IsZeroDiag z ∧ DoublesAt (m * P) z` (`exists_zero_diag_doublesAt_mul`, 9.898), any dyadic doubling point satisfies `e ≤ z` (`doublesAt_twopow_le`, 9.899), and therefore dyadic doubling zero diagonals occur at arbitrarily large depth `e ≤ z` (`exists_zero_diag_doublesAt_twopow_ge`, 9.900).
  - **Universal-in-`Q` (`1 ≤ Q`) Zero-Diagonal Doubling Contradiction Shrinking the Required Horizon by `z` (`9.901`–`9.906`)**: Replaces fixed-`Q` blocks with a single 5-corner space-time contradiction that holds for **every shift `Q ≥ 1` at once** at a **single** doubling zero diagonal `z = t - (p + 1)`: shifting diagonally by `Q` twice on `z + 1` restores `lhCenter ((t + Q) + Q) ((p + Q) + Q) = lhCenter t p` (`lhCenter_two_shift_diag_periodic_of_doubles`, 9.901), while because `1 ≤ Q` places `(t, p + Q)` in the `Q`-periodic region `t - (p + Q) = (z + 1) - Q ≤ z`, a single `LhBandAgree t Q p0 L` at time `t` forces `lhCenter (t + Q) ((p + Q) + Q) = !lhCenter t p` (`lhCenter_shift_two_Q_flip_of_doubles_and_lhBandAgree`, 9.902) and hence a vertical `Q`-flip `lhCenter ((t + Q) + Q) ((p + Q) + Q) = !lhCenter (t + Q) ((p + Q) + Q)` at the fixed spatial column `(p + Q) + Q` (`lhCenter_same_col_two_Q_flip_of_doubles_and_lhBandAgree`, 9.903). This immediately refutes `LhBandAgree (t + Q) Q p1 L1` under `LhBandAgree t Q p0 L` for **every `Q ≥ 1` at once** (`not_lhBandAgree_step_Q_of_doubles`, 9.904), and via `9.847` and `9.848` refutes `RhColAgree t (m * P) 1 S` (`not_periodic_rhColAgree_one_of_doubles`, 9.905) and `CenterPeriodic T P` (`not_centerPeriodic_of_rhColAgree_one_doubles`, 9.906) for **every `P > 0` and `m > 0` at once** over the reduced horizon `p + 3 * (m * P) ≤ S + 1` (shrunk from the light-cone horizon `t + m * P` by the depth `z` of the zero diagonal).
- **Batch 41 (9.907–9.921, attestation `f18c1562e3e5b738615c156fc03fcaf49fa97af2ed843c82f032e796b2ef3f10`)**:
  - **Shrinking All Horizon Refutations (`9.818`–`9.820`, `9.822`) by Zero-Diagonal Depth `z` & Discharging `DoublesAt (m * P) z` Unconditionally (`9.907`–`9.914`)**: Proves the universal-in-`m, P` zero-diagonal refutations over the reduced horizon `p + 3 * (m * P) ≤ S + 1` (shrunk from the light-cone horizon `t + m * P` by the depth `z = t - (p + 1)` of the doubling zero diagonal) for left-half column-`-1` agreement `LhColAgree t (m * P) 1 S` (`not_periodic_lhColAgree_one_of_doubles`, 9.907; `not_centerPeriodic_of_lhColAgree_one_doubles`, 9.908), single-time right-half spatial band agreement `RhBandAgree t (m * P) 0 (S + 1)` (`not_centerPeriodic_of_rhBandAgree_zero_doubles`, 9.909), `K`-column inward determination `RhColAgree t (m * P) (1 + K) (S + K) ∧ RhOrAgree t (m * P) (1 + K) (S + K)` (`not_centerPeriodic_of_rhCenter_inward_determine_doubles`, 9.910), and `RhOrAgree t (m * P) 1 S` with initial agreement `rhCenter (t + m * P) 1 = rhCenter t 1` (`not_centerPeriodic_of_rhOrAgree_one_doubles`, 9.911), together with the direct `t = z + (p + 1)` coordinate form (`not_periodic_rhColAgree_one_at_zero_diag_doubles`, 9.912). Combining `9.898` (`exists_zero_diag_doublesAt_mul`) with `9.912` and `9.907` at `p = T + settle (z + 1) + settle ((z + 1) - m * P)` **discharges `IsZeroDiag z`, `DoublesAt (m * P) z`, `T ≤ t`, and `SettledBy` completely**, proving under `CenterPeriodic T P` (`0 < P`) and `0 < m` alone that there exist `z, p ∈ ℕ` with `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ ¬ RhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))` (`exists_zero_diag_not_periodic_rhColAgree_one`, 9.913) and `¬ LhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))` (`exists_zero_diag_not_periodic_lhColAgree_one`, 9.914).
  - **White-Center Column-`1` Readout `maskparity · 0`, Unconditional Black-Center Agreement, and Producing Left-Band Agreement from White Centers Alone (`9.915`–`9.921`)**: Proves that the first bit `maskparity t 0 = !center t && rhCenter t 1` (`maskparity_zero_eq_not_center_and_rhCenter_one`, 9.915) is the exact white-center column-`1` readout, and under `CenterPeriodic T P` (`0 < P`) for `t ≥ T`: at every **black** center (`center t = true`), `lhCenter (t + m * P) 1 = lhCenter t 1` holds **unconditionally** with no hypothesis on `rhCenter · 1` (`periodic_lhCenter_one_eq_of_black_center`, 9.916); at every **white** center (`center t = false`), `lhCenter (t + m * P) 1 = lhCenter t 1` holds from white-center column-`1` agreement `center t = false → rhCenter (t + m * P) 1 = rhCenter t 1` (`periodic_lhCenter_one_eq_of_white_center`, 9.917) or equivalently from `maskparity (t + m * P) 0 = maskparity t 0` (`periodic_lhCenter_one_eq_of_maskparity_zero_eq`, 9.918). Consequently, white-center column-`1` agreement (`periodic_lhBandAgree_zero_of_white_center_rhCenter_one`, 9.919) or `maskparity · 0` window agreement (`periodic_lhBandAgree_zero_of_maskparity_zero_agree`, 9.920) over `[t, t + S]` produces full `LhBandAgree t (m * P) 0 (S + 1)` across the entire left band and refutes `CenterPeriodic T P` over the reduced zero-diagonal horizon `p + 3 * (m * P) ≤ S + 1` (`not_centerPeriodic_of_white_center_rhCenter_one_doubles`, 9.921).
- **Batch 42 (9.922–9.936, attestation `1370b648859133351056c58de9ee6ee23b5e910aacd1afcf2eb414ed15887a33`)**:
  - **First-Bit `maskparity · 0` Horizon Refutations & Unconditional White-Center / `maskparity · 0` / `lhCenter · 1` Flip Witnesses Under `CenterPeriodic` Alone (`9.922`–`9.927`)**: Proves the universal-in-`m, P` zero-diagonal refutations of `CenterPeriodic T P` from `maskparity · 0` window agreement over `p + 3 * (m * P) ≤ S + 1` (`not_centerPeriodic_of_maskparity_zero_agree_doubles`, 9.922) and the direct `t = z + (p + 1)` coordinate forms for white-center column-`1` agreement (`not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_doubles`, 9.923) and `maskparity · 0` agreement (`not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles`, 9.924). Combining `9.898` (`exists_zero_diag_doublesAt_mul`) with `9.923`, `9.924`, and `9.914` at `p = T + settle (z + 1) + settle ((z + 1) - m * P)` proves under `CenterPeriodic T P` (`0 < P`) and `0 < m` **alone** (with zero agreement hypotheses!) that there exist `z, p, s ∈ ℕ` with `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ s ≤ p + 3 * (m * P)` where `center ((z + (p + 1)) + s) = false` and `rhCenter (((z + (p + 1)) + s) + m * P) 1 = !rhCenter ((z + (p + 1)) + s) 1` (`exists_zero_diag_white_center_rhCenter_one_flip_of_periodic`, 9.925), `maskparity (((z + (p + 1)) + s) + m * P) 0 = !maskparity ((z + (p + 1)) + s) 0` (`exists_zero_diag_maskparity_zero_flip_of_periodic`, 9.926), and `lhCenter (((z + (p + 1)) + s) + m * P) 1 = !lhCenter ((z + (p + 1)) + s) 1` (`exists_zero_diag_lhCenter_one_flip_of_periodic`, 9.927).
  - **Black-Column-`1` OR-Absorption Propagation & White-Center-Conditioned OR-Agreement (`9.928`–`9.936`)**: From the 1-step column-`1` evolution `rhCenter (t + 1) 1 = center t ⊕ (rhCenter t 1 || rhCenter t 2)` (`rhCenter_step_one_eq_center_xor_or`, 9.928), proves that whenever `rhCenter t 1 = true`, column `2` (`rhCenter t 2`) is completely absorbed by the boolean OR (`rhCenter (t + 1) 1 = !center t`, `rhCenter_step_one_eq_not_center_of_black_one`, 9.929), so `center t = false ∧ rhCenter t 1 = true` forces `rhCenter (t + 1) 1 = true` (`rhCenter_step_one_eq_true_of_white_center_and_black_one`, 9.930), and `maskparity t 0 = true` forces both `rhCenter (t + 1) 1 = true` (`rhCenter_step_one_eq_true_of_maskparity_zero_true`, 9.931) and `rhCenter (t + 2) 1 = !center (t + 1)` (`rhCenter_step_two_eq_not_center_of_maskparity_zero_true`, 9.932) with zero dependence on `rhCenter t 2` or `rhCenter (t + 1) 2`. Under `CenterPeriodic T P` (`0 < P`), this yields unconditional 1-step forward propagation of `rhCenter · 1` (`periodic_rhCenter_step_one_eq_of_black_one`, 9.933) and `lhCenter · 1` (`periodic_lhCenter_step_one_eq_of_black_one`, 9.934) across any black column-`1` cell, 2-step forward propagation of `lhCenter · 1` across `t + 1` and `t + 2` from `maskparity · 0 = true` at time `t` (`periodic_lhCenter_step_one_and_two_eq_of_maskparity_zero_true`, 9.935), and full left-band agreement `LhBandAgree t (m * P) 0 (S + 1)` from OR-agreement conditioned **solely on white next centers** `center (t + (s + 1)) = false` (`periodic_lhBandAgree_zero_of_white_center_rhOrAgree_one`, 9.936).
- **Batch 43 (9.937–9.951, attestation `b77efa898dcd8e325dd1b8f92da73fe33c064d5ff0ac90c89ff4d185534fc5b7`)**:
  - **White-Center OR-Agreement Horizon Refutation & White-Column-`1` Linearization (`9.937`–`9.940`)**: Refutes `CenterPeriodic T P` over the reduced zero-diagonal horizon `p + 3 * (m * P) ≤ S + 1` from initial white-center column-`1` agreement and OR-agreement conditioned solely on white next centers `center (t + (s + 1)) = false` (`not_centerPeriodic_of_white_center_rhOrAgree_one_doubles`, 9.937). Furthermore, proves that whenever `rhCenter t 1 = false`, `rhCenter (t + 1) 1 = center t ⊕ rhCenter t 2` is purely linear in column `2` (`rhCenter_step_one_eq_center_xor_two_of_white_one`, 9.938), propagating column-`1` agreement across a white column-`1` cell from column-`2` agreement (`periodic_rhCenter_step_one_eq_of_white_one_and_two_eq`, 9.939) and yielding a unified 1-step forward propagation law for `lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1` that requires column-`2` agreement **only** when `center (t + 1) = false` and `rhCenter t 1 = false` (`periodic_lhCenter_step_one_eq_of_white_or_black_one`, 9.940).
  - **Unconditional Dyadic Scale Laws for `lhCenter · (2^k)`, `response · k`, `leftresponse · k`, and `maskparity · k` (`9.941`–`9.951`)**: Identifies the dyadic left wing `cell t (negpow k) = lhCenter t (twopow k)` for **all** `t, k ∈ ℕ` with no `2^k ≤ t` bound (`cell_negpow_eq_lhCenter_twopow`, 9.941), rewriting the dyadic scale identity as `center (t + twopow k) = (center t ⊕ lhCenter t (twopow k)) ⊕ response t k` (`scale_center_lhCenter`, 9.942). Under `CenterPeriodic T P` (`0 < P`), proves for **all** `m, t, k ∈ ℕ` with `T ≤ t` (no `2^k ≤ t` bound!) the exact `m * P`-defect lock `lhCenter (t + m * P) (twopow k) ⊕ lhCenter t (twopow k) = response (t + m * P) k ⊕ response t k` (`periodic_lhCenter_twopow_defect_eq_response_defect`, 9.943) and `maskparity (t + m * P) k ⊕ maskparity t k = (lhCenter (t + m * P) (twopow k) ⊕ lhCenter t (twopow k)) ⊕ (leftresponse (t + m * P) k ⊕ leftresponse t k)` (`periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect`, 9.944). Specializing to `t + m * P < twopow k` gives `response (t + m * P) k = response t k` (`periodic_response_eq_cone_mul`, 9.945) and `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k` (`periodic_maskparity_defect_eq_leftresponse_defect_cone_mul`, 9.946), while specializing to the left light-cone boundary `t + m * P = twopow k` (`0 < m`) proves **unconditional** `m * P`-antiperiodicity `response (t + m * P) k = !response t k` (`periodic_response_flip_at_twopow_mul`, 9.947) and defect inversion `maskparity (t + m * P) k ⊕ maskparity t k = !(leftresponse (t + m * P) k ⊕ leftresponse t k)` (`periodic_maskparity_defect_eq_not_leftresponse_defect_at_twopow_mul`, 9.948). Finally, proves the exact pointwise `m * P`-defect equality `lhCenter (t + m * P) 1 ⊕ lhCenter t 1 = maskparity (t + m * P) 0 ⊕ maskparity t 0` (`periodic_lhCenter_one_defect_eq_maskparity_zero_defect`, 9.949), its converse `lhCenter (t + m * P) 1 = lhCenter t 1 → maskparity (t + m * P) 0 = maskparity t 0` (`periodic_maskparity_zero_eq_of_lhCenter_one_eq`, 9.950), and the unconditional dyadic jump identity equating the `2^k`-jump of `lhCenter (s + m * P) 1 ⊕ lhCenter s 1` with the 1-step time difference of `maskparity (s + m * P) k ⊕ maskparity s k` (`periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect`, 9.951).
- **Batch 44 (9.952–9.966, attestation `05a815057f237b9d5971b2310d943c1d45492a8e22db995764592de48416c2a6`)**:
  - **Dyadic Jump Defect Laws of `lhCenter · 1` via `leftresponse` & Unconditional Outside-the-Cone Scale Collapse at Zero Diagonals Dropping `z ≤ k` (`9.952`–`9.962`)**: Combines `9.951` (`periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect`) with `9.944`, `9.946`, and `9.948` to prove under `CenterPeriodic T P` (`0 < P`) for `T ≤ s` that the `2^k`-jump of `lhCenter (s + m * P) 1 ⊕ lhCenter s 1` equals the 1-step time difference of `leftresponse (s + m * P) k ⊕ leftresponse s k` inside the cone `(s + 1) + m * P < twopow k` (`periodic_lhCenter_one_dyadic_jump_defect_eq_leftresponse_step_defect_cone_mul`, 9.952), flips at the cone boundary `s + m * P = twopow k` (`periodic_lhCenter_one_dyadic_jump_defect_eq_not_leftresponse_step_defect_at_twopow_mul`, 9.953), and equals the 1-step time difference of `(lhCenter (s + m * P) (twopow k) ⊕ lhCenter s (twopow k)) ⊕ (leftresponse (s + m * P) k ⊕ leftresponse s k)` for **all** `s, k ∈ ℕ` with no cone bound (`periodic_lhCenter_one_dyadic_jump_defect_eq_lhCenter_twopow_step_xor_leftresponse_step_defect`, 9.954). Furthermore, because `lhCenter` on a settled zero diagonal `z` or `z + 2` requires no `z ≤ k` bound (`9.836`, `9.872`), proves for **all** `z, k ∈ ℕ` (dropping `z ≤ k` completely!) that `lhCenter (z + twopow k) (twopow k) = false` (`lhCenter_twopow_of_zero_diag`, 9.955) and `lhCenter ((z + 2) + twopow k) (twopow k) = true` (`lhCenter_twopow_after_zero_diag`, 9.956), collapsing the outside-the-cone scale identity at `z + twopow k` (`scale_center_at_zero_diag`, 9.957; `periodic_response_at_zero_diag`, 9.959; `periodic_response_defect_at_zero_diag_eq_lhCenter_twopow`, 9.961) and inverting it at `(z + 2) + twopow k` (`scale_center_after_zero_diag`, 9.958; `periodic_response_after_zero_diag`, 9.960; `periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow`, 9.962) without `z ≤ k`.
  - **Dyadic `response · k` and `maskparity · k` Agreement from Left-Band and White-Center Column-`1` Agreement (`9.963`–`9.966`)**: Under `CenterPeriodic T P` (`0 < P`), proves for **all** `m, t, k ∈ ℕ` with `T ≤ t` (no `2^k` cone bound!) that single-time left-band agreement `LhBandAgree t (m * P) p0 L` covering column `2^k` (`p0 ≤ twopow k` and `twopow k < p0 + L`) forces `response (t + m * P) k = response t k` (`periodic_response_eq_of_lhBandAgree_twopow`, 9.963) and `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k` (`periodic_maskparity_defect_eq_leftresponse_defect_of_lhBandAgree_twopow`, 9.964). Combining `9.963` and `9.964` with `9.919` (`periodic_lhBandAgree_zero_of_white_center_rhCenter_one`) shows that white-center column-`1` agreement over `[t, t + S]` (`twopow k ≤ s + 1`, `s ≤ S`) forces `response ((t + s) + m * P) k = response (t + s) k` (`periodic_response_eq_of_white_center_rhCenter_one_twopow`, 9.965) and `maskparity ((t + s) + m * P) k ⊕ maskparity (t + s) k = leftresponse ((t + s) + m * P) k ⊕ leftresponse (t + s) k` (`periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhCenter_one_twopow`, 9.966).
- **Batch 45 (9.967–9.981, attestation `454c9a92c2db3722c0bee95c90304c1f969011eff4d8ec518282fb2a467e73e0`)**:
  - **Universal Unconditional Dyadic Coboundaries of `response` and `leftresponse` Dropping `t ≤ k` (`9.967`–`9.973`)**: Using `scale_center_lhCenter` (`9.942`) at `(t, k)`, `(t + 2^k, k)`, and `(t, k + 1)` eliminates `center` identically for **every** `t, k ∈ ℕ` with **no `t ≤ k` or `t < 2^k` bound**, proving `(response t (k + 1) ⊕ response t k) ⊕ response (t + twopow k) k = (lhCenter (t + twopow k) (twopow k) ⊕ lhCenter t (twopow k)) ⊕ lhCenter t (twopow (k + 1))` (`response_coboundary_eq_lhCenter_twopow`, 9.967) and the exact same identity for `leftresponse` via `maskparity_coboundary` (`leftresponse_coboundary_eq_lhCenter_twopow`, 9.968). Inside the linear light cone `t < twopow k` (replacing the logarithmic `t ≤ k` bound with `t < 2^k`), `lhCenter t (2^k) = false` and `lhCenter t (2^(k+1)) = false`, so `lhCenter (t + twopow k) (twopow k)` equals the dyadic coboundary of `response` (`lhCenter_twopow_eq_response_coboundary_cone`, 9.969) and `leftresponse` (`lhCenter_twopow_eq_leftresponse_coboundary_cone`, 9.970), vanishing at `t = z` (`leftresponse_coboundary_at_zero_diag_cone`, 9.971) and equaling `true` at `t = z + 2` (`leftresponse_coboundary_after_zero_diag_cone`, 9.972). Crucially, for **every** `z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, and `settle (z + 1) ≤ (z + 1) + twopow k` (with **no `z ≤ k` or `z < 2^k` bound**!), proves the scale-step left-wing flip `lhCenter ((z + 1) + twopow (k + 1)) (twopow (k + 1)) = !lhCenter ((z + 1) + twopow k) (twopow k)` (`lhCenter_twopow_succ_antiperiodic_of_doubles`, 9.973).
  - **Outside-the-Cone `maskparity`/`response` Zero-Diagonal Laws & Late `leftresponse` Defect (`9.974`–`9.981`)**: Specializing `9.959`–`9.962` through `split_paper` proves outside-the-cone `maskparity` formulas at `z + twopow k` (`periodic_maskparity_at_zero_diag`, 9.974; `periodic_maskparity_defect_at_zero_diag_eq_lhCenter_twopow_xor_leftresponse_defect`, 9.976) and `(z + 2) + twopow k` (`periodic_maskparity_after_zero_diag`, 9.975; `periodic_maskparity_defect_after_zero_diag_eq_not_lhCenter_twopow_xor_leftresponse_defect`, 9.977) with no `z ≤ k` bound. Under `CenterPeriodic T P` (`0 < P`), proves the unconditional 2-step `response` inversion `response ((z + 2) + twopow k) k = !response (z + twopow k) k` at any zero diagonal `z` when `m * P = 2` (`periodic_response_flip_at_zero_diag_step_two`, 9.978), `response ((z + twopow k) + m * P) k = !response (z + twopow k) k` when `(z + m * P) - 2` is also a zero diagonal (`periodic_response_flip_of_two_zero_diags`, 9.979), `response ((z + twopow k) + m * P) k = response (z + twopow k) k` when `z + m * P` is also a zero diagonal (`periodic_response_eq_of_two_zero_diags`, 9.980), and the exact late `leftresponse` shift-defect identity inside `t + m * P < twopow k` (`late_leftresponse_defect_eq_lhCenter_twopow_defect_cone`, 9.981).
- **Batch 46 (9.982–9.996, attestation `2e3f6d48f6c37dfcd36f8349c5a604fb33e840548d9ae71819649c13a814ee61`)**:
  - **Universal-in-`Q` Determination of `maskcount`/`maskparity`/`leftresponse`/`response` from First-Bit `maskparity · 0` and White-Center Column-`1` Agreement (`9.982`–`9.991`)**: Establishes the exact recurrence `maskcount t (n + 1) = maskcount t n ⊕ maskparity (t + n) 0` (`maskcount_succ_eq_xor_maskparity_zero`, 9.982), proving by induction that first-bit `maskparity · 0` agreement over `[t, t + n)` determines `maskcount (t + Q) n = maskcount t n` (`maskcount_eq_of_maskparity_zero_agree`, 9.983) and over `[t, t + S]` (`twopow k ≤ S + 1`) determines `maskparity (t + Q) k = maskparity t k` (`maskparity_eq_of_maskparity_zero_agree`, 9.984) for **every** shift `Q`. Combining `9.984` with `9.966` (`periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhCenter_one_twopow`) and `9.963` (`periodic_response_eq_of_lhBandAgree_twopow`) under `CenterPeriodic T P` (`0 < P`) produces `maskparity (t + m * P) k = maskparity t k` (`periodic_maskparity_eq_of_white_center_rhCenter_one_twopow`, 9.985; `periodic_maskparity_eq_of_lhColAgree_one_twopow`, 9.990), `leftresponse (t + m * P) k = leftresponse t k` (`periodic_leftresponse_eq_of_white_center_rhCenter_one_twopow`, 9.986; `periodic_leftresponse_eq_of_maskparity_zero_agree_twopow`, 9.987; `periodic_leftresponse_eq_of_lhColAgree_one_twopow`, 9.989), and `response (t + m * P) k = response t k` (`periodic_response_eq_of_maskparity_zero_agree_twopow`, 9.988; `periodic_response_eq_of_lhColAgree_one_twopow`, 9.991) over any `twopow k ≤ S + 1` window.
  - **Unconditional Dyadic Left-Wing Identification & Scale-Step Laws Along Settled and Doubling Left Diagonals (`9.992`–`9.996`)**: Proves for **every** `d, k ∈ ℕ` (with no `d ≤ k` bound!) that `lhCenter (d + twopow k) (twopow k) = ldiag d (d + twopow k)` (`lhCenter_twopow_eq_ldiag`, 9.992). For `d ≤ k` and `SettledBy d (d + twopow k)`, this identifies `lhCenter (d + twopow k) (twopow k) = zcenter d` (`lhCenter_twopow_settled_eq_zcenter`, 9.993) and proves scale-step invariance `lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k)` (`lhCenter_twopow_settled_scale_invariant`, 9.994). Crucially, for **every** `z, d, k ∈ ℕ` with `DoublesAt (twopow k) z` (with **no `d ≤ k` or `z ≤ k` bound**!), proves scale-step invariance `lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k)` for all settled `d ≤ z` (`lhCenter_twopow_succ_periodic_of_doubles_le`, 9.995) and scale-step antiperiodicity `lhCenter ((z + 3) + twopow (k + 1)) (twopow (k + 1)) = !lhCenter ((z + 3) + twopow k) (twopow k)` along the settled reset diagonal `z + 3` (`lhCenter_twopow_reset_succ_antiperiodic_of_doubles`, 9.996).
- **Batch 47 (9.997–9.1011, attestation `113556ea70ecbffd587dcf28312807020c1701eeddad5f3215df155aacadf6db`)**:
  - **Unconditional Late Dyadic Scale Laws Along Settled & Doubling Left Diagonals Without `d ≤ k` or `DoublesAt (m * P) z` (`9.997`–`9.1003`)**: Identifies `lhCenter (d + twopow k) (twopow k) = (center (d + twopow (k + 1)) ⊕ center (d + twopow k)) ⊕ response (d + twopow k) k` for **every** `d, k ∈ ℕ` with no `d ≤ k` bound (`lhCenter_twopow_eq_late_scale_center`, 9.997). Combining `9.997` with `9.995`, `9.973`, and `9.996` proves scale-step invariance of the late scale increment for all settled `d ≤ z` below a dyadic doubling point `DoublesAt (twopow k) z` (`late_scale_center_periodic_of_doubles_le`, 9.998) and scale-step inversion along `z + 1` (`late_scale_center_antiperiodic_of_doubles`, 9.999) and `z + 3` (`late_scale_center_reset_antiperiodic_of_doubles`, 9.1000) with **no `z ≤ k` bound**. Under `CenterPeriodic T P` (`0 < P`), because the diagonal shift from `d + twopow k` to `d + twopow (k + 1)` is `twopow k` while the horizontal shift across diagonals is `m * P`, proves that `response ((d + twopow k) + m * P) k ⊕ response (d + twopow k) k` is invariant from scale `k` to `k + 1` whenever `d + m * P ≤ z` (`periodic_late_response_defect_eq_of_doubles_le`, 9.1001) and **flips** from scale `k` to `k + 1` whenever `d ≤ z` and `d + m * P = z + 1` (`periodic_late_response_defect_flip_of_doubles`, 9.1002; `periodic_late_response_flip_of_doubles_and_eq`, 9.1003) using **only `DoublesAt (twopow k) z`** (requiring **neither `DoublesAt (m * P) z` nor `z ≤ k`**!).
  - **Dyadic `2^k`-Window Refutations of `CenterPeriodic` at Cone Boundary, Zero-Diagonal, and Doubling Points (`9.1004`–`9.1011`)**: Refutes `CenterPeriodic T P` (`0 < P`) over a `twopow k ≤ S + 1` window from white-center column-`1` agreement or first-bit `maskparity · 0` agreement: at the light-cone boundary `t + m * P = twopow k` (`not_centerPeriodic_of_white_center_rhCenter_one_at_twopow`, 9.1004; `not_centerPeriodic_of_maskparity_zero_agree_at_twopow`, 9.1005); at `z + twopow k` when `m * P = 2` (`not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_step_two`, 9.1006; `not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_step_two`, 9.1007) or when `(z + m * P) - 2` is also a zero diagonal (`not_centerPeriodic_of_white_center_rhCenter_one_of_two_zero_diags`, 9.1008; `not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags`, 9.1009) with **no `z`-dependent addition to the horizon `2^k`**; and across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`, `d + m * P = z + 1`) from two-scale agreement at `d + twopow k` and `d + twopow (k + 1)` without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_white_center_rhCenter_one_scale_step_doubles`, 9.1010; `not_centerPeriodic_of_maskparity_zero_agree_scale_step_doubles`, 9.1011).
- **Batch 48 (9.1012–9.1026, attestation `0f9ccdf4f2acedada07e6a82c2cfc2a548ae853e63d51f3e575ea83658c181d0`)**:
  - **Strict Exponential Dominance `n < 2^n`, `LhColAgree` Dyadic Window Refutations, and Direct `2^k - m * P` Cone-Boundary Refutations (`9.1012`–`9.1018`)**: Proves `n < twopow n` for every `n ∈ ℕ` (`lt_twopow_self`, 9.1012), together with the `LhColAgree` counterparts of the `twopow k ≤ S + 1` window refutations at the cone boundary `t + m * P = twopow k` (`not_centerPeriodic_of_lhColAgree_one_at_twopow`, 9.1013), at `z + twopow k` for `m * P = 2` (`not_centerPeriodic_of_lhColAgree_one_at_zero_diag_step_two`, 9.1014), for two zero diagonals (`not_centerPeriodic_of_lhColAgree_one_of_two_zero_diags`, 9.1015), and across a dyadic doubling zero diagonal at scales `k` and `k + 1` (`not_centerPeriodic_of_lhColAgree_one_scale_step_doubles`, 9.1016). Specializing `9.1004` and `9.1005` to `t = twopow k - m * P` eliminates `t` and `t + m * P = twopow k` completely, refuting `CenterPeriodic T P` at **every** scale `k` with `T + m * P ≤ twopow k` from white-center column-`1` agreement (`not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow`, 9.1017) or `maskparity · 0` agreement (`not_centerPeriodic_of_maskparity_zero_agree_sub_twopow`, 9.1018) with **no `z`, `DoublesAt`, or `SettledBy` hypothesis**.
  - **Unconditional Flip-Witness Existence Theorems Over `2^k` Windows Under `CenterPeriodic` Alone (`9.1019`–`9.1026`)**: By contraposition of `9.1004`–`9.1007` and `9.1013`, proves under `CenterPeriodic T P` (`0 < P`) **alone** (with **zero agreement hypotheses**!) that at `t + m * P = twopow k` (`0 < m`, `T ≤ t`, `twopow k ≤ S + 1`) there exists `s ≤ S` where `center (t + s) = false ∧ rhCenter ((t + s) + m * P) 1 = !rhCenter (t + s) 1` (`exists_white_center_rhCenter_one_flip_at_twopow_of_periodic`, 9.1019), `maskparity ((t + s) + m * P) 0 = !maskparity (t + s) 0` (`exists_maskparity_zero_flip_at_twopow_of_periodic`, 9.1020), and `lhCenter ((t + s) + m * P) 1 = !lhCenter (t + s) 1` (`exists_lhCenter_one_flip_at_twopow_of_periodic`, 9.1021). Consequently, for **every** scale `k` with `T + m * P ≤ twopow k` (with no `t`, `S`, `z`, `DoublesAt`, or `SettledBy`!), there exists `s < twopow k` in `[twopow k - m * P, 2 * twopow k - m * P)` where white-center `rhCenter · 1` flips (`exists_white_center_rhCenter_one_flip_sub_twopow_of_periodic`, 9.1022), `maskparity · 0` flips (`exists_maskparity_zero_flip_sub_twopow_of_periodic`, 9.1023), and `lhCenter · 1` flips (`exists_lhCenter_one_flip_sub_twopow_of_periodic`, 9.1024), as well as within `twopow k ≤ S + 1` steps of `z + twopow k` when `m * P = 2` (`exists_white_center_rhCenter_one_flip_at_zero_diag_step_two_of_periodic`, 9.1025; `exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic`, 9.1026).
- **Batch 49 (9.1027–9.1041, attestation `3cf8d0972d7cbe8a43baff85ade7391c2901c9056bdb5e01c49114000a0282b9`)**:
  - **Monotonicity of `twopow` & Unconditional Fundamental-Period (`P` Itself, `m = 1`) Flip Witnesses at Every Scale `k ≥ T + P` Without `DoublesAt` or `SettledBy` (`9.1027`–`9.1036`)**: Proves `a ≤ b → twopow a ≤ twopow b` (`twopow_mono`, 9.1027) and `n ≤ k → n < twopow k` (`lt_twopow_of_le`, 9.1028), upgrading the `2^k - m * P` cone-boundary refutations (`not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow_ge`, 9.1029; `not_centerPeriodic_of_maskparity_zero_agree_sub_twopow_ge`, 9.1030) and unconditional flip-witness existence theorems (`exists_white_center_rhCenter_one_flip_sub_twopow_ge_of_periodic`, 9.1031; `exists_maskparity_zero_flip_sub_twopow_ge_of_periodic`, 9.1032; `exists_lhCenter_one_flip_sub_twopow_ge_of_periodic`, 9.1033) to hold for **every** scale `k ≥ T + m * P`. Setting `m = 1` eliminates the multiplier `m` completely, proving under `CenterPeriodic T P` (`0 < P`) **alone** (with no `m`, `t`, `S`, `z`, `DoublesAt`, or `SettledBy`!) that for **every** scale `k ≥ T + P`, the dyadic window `[twopow k - P, 2 * twopow k - P)` contains `s < twopow k` where `center ((twopow k - P) + s) = false ∧ rhCenter (((twopow k - P) + s) + P) 1 = !rhCenter ((twopow k - P) + s) 1` (`exists_white_center_rhCenter_one_flip_sub_twopow_P_of_periodic`, 9.1034), `maskparity (((twopow k - P) + s) + P) 0 = !maskparity ((twopow k - P) + s) 0` (`exists_maskparity_zero_flip_sub_twopow_P_of_periodic`, 9.1035), and `lhCenter (((twopow k - P) + s) + P) 1 = !lhCenter ((twopow k - P) + s) 1` (`exists_lhCenter_one_flip_sub_twopow_P_of_periodic`, 9.1036).
  - **Two-Zero-Diagonal Unconditional Flip Witnesses & Scale-Step `maskparity ⊕ leftresponse` Defect Flip Across Dyadic Doubling Zero Diagonals (`9.1037`–`9.1041`)**: Completes the unconditional `lhCenter · 1` flip witness at `z + twopow k` for `m * P = 2` (`exists_lhCenter_one_flip_at_zero_diag_step_two_of_periodic`, 9.1037) and proves unconditional white-center `rhCenter · 1` (`exists_white_center_rhCenter_one_flip_of_two_zero_diags_and_periodic`, 9.1038), `maskparity · 0` (`exists_maskparity_zero_flip_of_two_zero_diags_and_periodic`, 9.1039), and `lhCenter · 1` (`exists_lhCenter_one_flip_of_two_zero_diags_and_periodic`, 9.1040) flip witnesses within `twopow k ≤ S + 1` steps of `z + twopow k` whenever both `z` and `(z + m * P) - 2` are settled zero diagonals. Also proves through `split_paper` that across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`), the combined `(maskparity ⊕ maskparity) ⊕ (leftresponse ⊕ leftresponse)` shift defect flips from scale `k` at `d + twopow k` to scale `k + 1` at `d + twopow (k + 1)` without `DoublesAt (m * P) z` or `z ≤ k` (`periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles`, 9.1041).
