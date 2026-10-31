module

public import Rule30UOR.Interfaces.Part11

/-!
# `Rule30UOR.Interfaces`, part 12

* Batch 35: Exact Finite Target Criteria for `¬ CenterPeriodic`, Scale-Free Real-Orbit Doubling Laws, and Universal-in-`Q` Agreement Production Across the Settled Left Strip (9.817–9.831)
* Batch 36: Scale-Free Real-Orbit Zero-Diagonal, Post-Zero Black, Twin, and Post-Black Reset Laws & Single-Time `LhBandAgree` Transport for Every Shift `Q` (9.832–9.846)
* Batch 37: Producing `LhBandAgree` from `RhColAgree`, Scale-Free Real-Orbit `LhBandAgree` Twin/Linearization/OR-Absorption Laws, and Cross-Center Laws Dropping `z ≤ k` (9.847–9.861)
* Batch 38: Unconditional Sector-2 `winWitt` Laws Dropping `z ≤ k` and Scale-Free Real-Orbit `LhBandAgree` Doubling-Diagonal Cascade at Row `t` (9.862–9.876)
* Batch 39: Scale-Free Real-Orbit Reset Antiperiodicity, Period-1 Doubling Refutation `not_lhBandAgree_one_of_doubles`, and Period-3 Doubling Refutation `not_lhBandAgree_three_of_doubles` (9.877–9.891)
* Batch 40: The Zero-Diagonal Period-Doubling Laws, Unbounded Dyadic Doubling Points, and Universal-in-`Q` Zero-Diagonal Doubling Contradiction Shrinking the Horizon by `z` (9.892–9.906)
* Batch 41: Discharging `DoublesAt (m * P) z` via the Doubling Law & Producing Left-Band Agreement from White-Center Column-1 (`maskparity · 0`) Agreement Over the Reduced Horizon (9.907–9.921)
* Batch 42: First-Bit `maskparity · 0` Horizon Refutations, Unconditional White-Center Flip Witnesses Under `CenterPeriodic`, and Black-Column-1 OR-Absorption Propagation (9.922–9.936)
-/

@[expose] public section

namespace Rule30UOR.Interfaces
open Rule30UOR.Core (phi carry phiLinear)
open Rule30UOR.Core (phi carry phiLinear row rowCenter bit rdiag rcenter bxor)
open Rule30UOR.Core (phiLinearPow phiScale winWitt wittResponse twopow twopow_succ)
open Rule30UOR.Core (ldiag)
open Rule30UOR.Intent (settle E)
open Rule30UOR.ZeroDiagonals (IsZeroDiag)
open Rule30UOR.CompilePoints (IsBlackDiag DoublesAt black_after_zero_diag antiperiodic_of_doubles)

/-! ### Batch 35: Exact Finite Target Criteria for `¬ CenterPeriodic`, Scale-Free Real-Orbit Doubling Laws, and Universal-in-`Q` Agreement Production Across the Settled Left Strip (9.817–9.831) -/

/-- **Exact Finite Target Refutation of `CenterPeriodic T P` from Right-Half Column-`1` Agreement `RhColAgree t (m * P) 1 S` (`not_centerPeriodic_of_rhColAgree_one_horizon`, 9.817)**:
    for all `T, P, m, t, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, if `RhColAgree t (m * P) 1 S` holds (column `1` of the right half agrees with its shift by `m * P` over the finite window `[t, t + S]` of length `S + 1 ≥ t + m * P`), then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhColAgree_one_horizon
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hrh : RhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_horizon T P hP hper m t S hm ht hS hrh

/-- **Exact Finite Target Refutation of `CenterPeriodic T P` from Left-Half Column-`-1` Agreement `LhColAgree t (m * P) 1 S` (`not_centerPeriodic_of_lhColAgree_one_horizon`, 9.818)**:
    for all `T, P, m, t, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, if `LhColAgree t (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_horizon
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_lhColAgree_one_horizon T P hP hper m t S hm ht hS hlh

/-- **Exact Finite Target Refutation of `CenterPeriodic T P` from Single-Time Right-Half Spatial Band Agreement `RhBandAgree t (m * P) 0 (S + 1)` (`not_centerPeriodic_of_rhBandAgree_zero_horizon`, 9.819)**:
    for all `T, P, m, t, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, if `RhBandAgree t (m * P) 0 (S + 1)` holds at time `t`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_zero_horizon
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hband : RhBandAgree t (m * P) 0 (S + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_horizon T P hP hper m t S hm ht hS
    (periodic_rhColAgree_one_of_rhBandAgree_zero T P hP hper m t S ht hband)

/-- **Exact Finite Target Refutation of `CenterPeriodic T P` via `K`-Column Inward Determination from Column `1 + K` (`not_centerPeriodic_of_rhCenter_inward_determine_horizon`, 9.820)**:
    for all `T, P, m, t, S, K ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, if `RhColAgree t (m * P) (1 + K) (S + K)` and `RhOrAgree t (m * P) (1 + K) (S + K)` hold at column `1 + K`, then marching `K` columns inward via `rhCenter_inward_determine` produces `RhColAgree t (m * P) 1 S` and refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhCenter_inward_determine_horizon
    (T P m t S K : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hcol : RhColAgree t (m * P) (1 + K) (S + K))
    (hor : RhOrAgree t (m * P) (1 + K) (S + K)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_horizon T P hP hper m t S hm ht hS
    (rhCenter_inward_determine t (m * P) 1 S K hcol hor).1

/-- **Producing `RhColAgree t (m * P) 1 S` from `RhOrAgree t (m * P) 1 S` and Initial Agreement at `(t, 1)` Under `CenterPeriodic` (`periodic_rhColAgree_one_of_rhOrAgree_one`, 9.821)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S ∈ ℕ` with `T ≤ t`, if `rhCenter (t + m * P) 1 = rhCenter t 1` holds at the single initial step `t` and `RhOrAgree t (m * P) 1 S` holds over `[t, t + S)`, then `RhColAgree t (m * P) 1 S` holds across the entire window `[t, t + S]`! -/
theorem periodic_rhColAgree_one_of_rhOrAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h0 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : RhOrAgree t (m * P) 1 S) :
    RhColAgree t (m * P) 1 S := by
  intro s hs
  rcases s with _ | s
  · simpa using h0
  · exact periodic_col_one_of_rhOrAgree_one T P hP hper m t S ht hor s (by omega)

/-- **Exact Finite Target Refutation of `CenterPeriodic T P` from `RhOrAgree t (m * P) 1 S` and Initial Agreement at `(t, 1)` (`not_centerPeriodic_of_rhOrAgree_one_horizon`, 9.822)**:
    for all `T, P, m, t, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, if `rhCenter (t + m * P) 1 = rhCenter t 1` and `RhOrAgree t (m * P) 1 S` hold, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhOrAgree_one_horizon
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (h0 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : RhOrAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_horizon T P hP hper m t S hm ht hS
    (periodic_rhColAgree_one_of_rhOrAgree_one T P hP hper m t S ht h0 hor)

/-- **Scale-Free Universal-in-`Q` Settled `ldiag` Periodicity Below Any Doubling Point (`ldiag_settled_periodic_of_doubles_le`, 9.823)**:
    for EVERY shift `Q` and doubling threshold `z` (`DoublesAt Q z`), and for all `d, t ∈ ℕ` with `d ≤ z` and `settle d ≤ t` (with no scale `k` or `2^k` shift!), `ldiag d (t + Q) = ldiag d t`! -/
theorem ldiag_settled_periodic_of_doubles_le (Q z d t : Nat)
    (hd : DoublesAt Q z) (hdz : d ≤ z)
    (hset : settle d ≤ t) :
    ldiag d (t + Q) = ldiag d t := by
  have hsetQ : settle d ≤ t + Q := by omega
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Kit.ldiag_eq_D,
    ← Rule30UOR.Intent.E_eq_D d (t + Q) hsetQ,
    ← Rule30UOR.Intent.E_eq_D d t hset]
  exact hd.1 d hdz t

theorem ldiag_settled_periodic_of_doubles_le_prop (Q z d t : Nat)
    (hd : DoublesAt Q z) (hdz : d ≤ z)
    (hset : SettledBy d t) :
    ldiag d (t + Q) = ldiag d t :=
  ldiag_settled_periodic_of_doubles_le Q z d t hd hdz hset

/-- **Scale-Free Universal-in-`Q` Settled `ldiag` Antiperiodicity on the Doubling Diagonal `z + 1` (`ldiag_settled_antiperiodic_of_doubles`, 9.824)**:
    for EVERY shift `Q` and doubling zero diagonal `z` (`IsZeroDiag z` and `DoublesAt Q z`), and for all `t ∈ ℕ` with `settle (z + 1) ≤ t` (with no scale `k` or `2^k` shift!), `ldiag (z + 1) (t + Q) = !ldiag (z + 1) t`! -/
theorem ldiag_settled_antiperiodic_of_doubles (Q z t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : settle (z + 1) ≤ t) :
    ldiag (z + 1) (t + Q) = !ldiag (z + 1) t := by
  have hsetQ : settle (z + 1) ≤ t + Q := by omega
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Kit.ldiag_eq_D,
    ← Rule30UOR.Intent.E_eq_D (z + 1) (t + Q) hsetQ,
    ← Rule30UOR.Intent.E_eq_D (z + 1) t hset]
  exact antiperiodic_of_doubles Q z hz hd t

theorem ldiag_settled_antiperiodic_of_doubles_prop (Q z t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : SettledBy (z + 1) t) :
    ldiag (z + 1) (t + Q) = !ldiag (z + 1) t :=
  ldiag_settled_antiperiodic_of_doubles Q z t hz hd hset

/-- **Scale-Free Universal-in-`Q` Diagonal-Shift `lhCenter` Agreement Below Any Doubling Point (`lhCenter_diag_shift_periodic_of_doubles_le`, 9.825)**:
    for EVERY shift `Q` and doubling threshold `z` (`DoublesAt Q z`), and for all `t, p ∈ ℕ` with `t - p ≤ z` and `settle (t - p) ≤ t` (with NO bound `p ≤ t` and NO scale `k`!), `lhCenter (t + Q) (p + Q) = lhCenter t p`! -/
theorem lhCenter_diag_shift_periodic_of_doubles_le (Q z t p : Nat)
    (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : settle (t - p) ≤ t) :
    lhCenter (t + Q) (p + Q) = lhCenter t p := by
  by_cases hpt : p ≤ t
  · rw [lhCenter_eq_ldiag (t + Q) (p + Q) (by omega),
      lhCenter_eq_ldiag t p hpt,
      show (t + Q) - (p + Q) = t - p by omega]
    exact ldiag_settled_periodic_of_doubles_le Q z (t - p) t hd hdz hset
  · rw [lhCenter_gt_eq_false (t + Q) (p + Q) (by omega),
      lhCenter_gt_eq_false t p (by omega)]

theorem lhCenter_diag_shift_periodic_of_doubles_le_prop (Q z t p : Nat)
    (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : SettledBy (t - p) t) :
    lhCenter (t + Q) (p + Q) = lhCenter t p :=
  lhCenter_diag_shift_periodic_of_doubles_le Q z t p hd hdz hset

/-- **Scale-Free Universal-in-`Q` Diagonal-Shift `lhCenter` Antiperiodicity on the Doubling Diagonal `z + 1` (`lhCenter_diag_shift_antiperiodic_of_doubles`, 9.826)**:
    for EVERY shift `Q`, and for all `t, p ∈ ℕ` with `p ≤ t`, if `IsZeroDiag (t - p)`, `DoublesAt Q (t - p)`, and `settle ((t - p) + 1) ≤ t + 1`, then `lhCenter ((t + 1) + Q) (p + Q) = !lhCenter (t + 1) p`! -/
theorem lhCenter_diag_shift_antiperiodic_of_doubles (Q t p : Nat)
    (hp : p ≤ t)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt Q (t - p))
    (hset : settle ((t - p) + 1) ≤ t + 1) :
    lhCenter ((t + 1) + Q) (p + Q) = !lhCenter (t + 1) p := by
  rw [lhCenter_eq_ldiag ((t + 1) + Q) (p + Q) (by omega),
    lhCenter_eq_ldiag (t + 1) p (by omega),
    show ((t + 1) + Q) - (p + Q) = (t - p) + 1 by omega,
    show (t + 1) - p = (t - p) + 1 by omega]
  exact ldiag_settled_antiperiodic_of_doubles Q (t - p) (t + 1) hz hd hset

theorem lhCenter_diag_shift_antiperiodic_of_doubles_prop (Q t p : Nat)
    (hp : p ≤ t)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt Q (t - p))
    (hset : SettledBy ((t - p) + 1) (t + 1)) :
    lhCenter ((t + 1) + Q) (p + Q) = !lhCenter (t + 1) p :=
  lhCenter_diag_shift_antiperiodic_of_doubles Q t p hp hz hd hset

/-- **Scale-Free Universal-in-`Q` Single-Row Spatial `Q`-Periodicity on the Real Orbit Under `LhBandAgree` (`lhCenter_spatial_periodic_of_doubles_le_and_lhBandAgree`, 9.827)**:
    for EVERY shift `Q` and doubling threshold `z` (`DoublesAt Q z`), and for all `t, p, p0, L ∈ ℕ` with `t - p ≤ z`, `settle (t - p) ≤ t`, `p0 ≤ p + Q`, and `p + Q ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t`, then `lhCenter t (p + Q) = lhCenter t p` inside the single row `row t` (with no scale `k` or `winWitt`!)! -/
theorem lhCenter_spatial_periodic_of_doubles_le_and_lhBandAgree (Q z t p p0 L : Nat)
    (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : settle (t - p) ≤ t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + Q) = lhCenter t p := by
  have hb := hband ((p + Q) - p0) (by omega)
  rw [show p0 + ((p + Q) - p0) = p + Q by omega] at hb
  rw [← hb]
  exact lhCenter_diag_shift_periodic_of_doubles_le Q z t p hd hdz hset

theorem lhCenter_spatial_periodic_of_doubles_le_and_lhBandAgree_prop (Q z t p p0 L : Nat)
    (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : SettledBy (t - p) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + Q) = lhCenter t p :=
  lhCenter_spatial_periodic_of_doubles_le_and_lhBandAgree Q z t p p0 L hd hdz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Row Spatial `Q`-Flip on `z + 1` Under `LhBandAgree` (`lhCenter_spatial_antiperiodic_of_doubles_and_lhBandAgree`, 9.828)**:
    for EVERY shift `Q`, and for all `t, p, p0, L ∈ ℕ` with `p ≤ t`, `IsZeroDiag (t - p)`, `DoublesAt Q (t - p)`, `settle ((t - p) + 1) ≤ t + 1`, `p0 ≤ p + Q`, and `p + Q ≤ p0 + L`, if `LhBandAgree (t + 1) Q p0 L` holds at time `t + 1`, then `lhCenter (t + 1) (p + Q) = !lhCenter (t + 1) p` inside the single row `row (t + 1)` (with no scale `k` or `winWitt`!)! -/
theorem lhCenter_spatial_antiperiodic_of_doubles_and_lhBandAgree (Q t p p0 L : Nat)
    (hp : p ≤ t)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt Q (t - p))
    (hset : settle ((t - p) + 1) ≤ t + 1)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree (t + 1) Q p0 L) :
    lhCenter (t + 1) (p + Q) = !lhCenter (t + 1) p := by
  have hb := hband ((p + Q) - p0) (by omega)
  rw [show p0 + ((p + Q) - p0) = p + Q by omega] at hb
  rw [← hb]
  exact lhCenter_diag_shift_antiperiodic_of_doubles Q t p hp hz hd hset

theorem lhCenter_spatial_antiperiodic_of_doubles_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hp : p ≤ t)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt Q (t - p))
    (hset : SettledBy ((t - p) + 1) (t + 1))
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree (t + 1) Q p0 L) :
    lhCenter (t + 1) (p + Q) = !lhCenter (t + 1) p :=
  lhCenter_spatial_antiperiodic_of_doubles_and_lhBandAgree Q t p p0 L hp hz hd hset hp0 hL hband

/-- **Unconditional Vanishing of `winWitt t (2^k)` Across the Settled Left Wing and Outside the Cone (`winWitt_testBit_settled_left_ge`, 9.829)**:
    for all `t, k, p ∈ ℕ` with `t - p ≤ k` and `settle (t - p) ≤ t` (no bound `p ≤ t` required!), `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = false`! -/
theorem winWitt_testBit_settled_left_ge (t k p : Nat)
    (hk : t - p ≤ k) (hset : settle (t - p) ≤ t) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) = false := by
  by_cases hpt : p ≤ t
  · have h := winWitt_testBit_settled_left t k (t - p) hk (by omega) hset
    rwa [show t - (t - p) = p by omega] at h
  · exact winWitt_testBit_gt_left_edge t k p (by omega)

theorem winWitt_testBit_settled_left_ge_prop (t k p : Nat)
    (hk : t - p ≤ k) (hset : SettledBy (t - p) t) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) = false :=
  winWitt_testBit_settled_left_ge t k p hk hset

/-- **Universal-in-`Q` Production of `WinWittAgree` Across the Settled Left Strip (`winWittAgree_settled_left_strip`, 9.830)**:
    for EVERY shift `Q` at once, and for all `t, k, p0, L ∈ ℕ` with `(t + Q) - p0 ≤ k`, if `∀ d ≤ (t + Q) - p0, settle d ≤ t`, then `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` holds unconditionally! -/
theorem winWittAgree_settled_left_strip (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → settle d ≤ t) :
    WinWittAgree t k Q (t + p0 + twopow (k + 1)) L := by
  intro i _hi
  have h1 := winWitt_testBit_settled_left_ge (t + Q) k (p0 + i)
    (by omega) (by have := hset ((t + Q) - (p0 + i)) (by omega); omega)
  have h0 := winWitt_testBit_settled_left_ge t k (p0 + i)
    (by omega) (hset (t - (p0 + i)) (by omega))
  rw [show (t + p0 + twopow (k + 1)) + i + Q = (t + Q) + (p0 + i) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + i = t + (p0 + i) + twopow (k + 1) by omega,
    h1, h0]

theorem winWittAgree_settled_left_strip_prop (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → SettledBy d t) :
    WinWittAgree t k Q (t + p0 + twopow (k + 1)) L :=
  winWittAgree_settled_left_strip t k Q p0 L hk hset

/-- **Universal-in-`Q` Inward `2^k`-Scale Transport of `LhBandAgree` Across the Settled Left Strip Without `WinWittAgree` Premise (`lhBandAgree_inward_of_settled_left_strip`, 9.831)**:
    for EVERY shift `Q` at once, and for all `t, k, p0, L ∈ ℕ` with `(t + Q) - p0 ≤ k` and `∀ d ≤ (t + Q) - p0, settle d ≤ t`, `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` alone implies `LhBandAgree t Q p0 L` (with no `WinWittAgree` premise, since `winWittAgree_settled_left_strip` produces `WinWittAgree` automatically for every `Q`!)! -/
theorem lhBandAgree_inward_of_settled_left_strip (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → settle d ≤ t)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L) :
    LhBandAgree t Q p0 L := by
  have hk_lt : k < twopow k := twopow_gt_self k
  exact lhBandAgree_scale_inward_outer_strip t k Q p0 L (by omega) hlate
    (winWittAgree_settled_left_strip t k Q p0 L hk hset)

theorem lhBandAgree_inward_of_settled_left_strip_prop (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → SettledBy d t)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L) :
    LhBandAgree t Q p0 L :=
  lhBandAgree_inward_of_settled_left_strip t k Q p0 L hk hset hlate

/-! ### Batch 36: Scale-Free Real-Orbit Zero-Diagonal, Post-Zero Black, Twin, and Post-Black Reset Laws & Single-Time `LhBandAgree` Transport for Every Shift `Q` (9.832–9.846) -/

/-- **Universal-in-`Q` Forward `2^k`-Scale Transport of `LhBandAgree` Across the Settled Left Strip Without `WinWittAgree` Premise (`lhBandAgree_step_of_settled_left_strip`, 9.832)**:
    for EVERY shift `Q` at once, and for all `t, k, p0, L ∈ ℕ` with `(t + Q) - p0 ≤ k` and `∀ d ≤ (t + Q) - p0, settle d ≤ t`, `LhBandAgree t Q p0 L` alone implies `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` (with no `WinWittAgree` premise, since `winWittAgree_settled_left_strip` produces `WinWittAgree` automatically for every `Q`!)! -/
theorem lhBandAgree_step_of_settled_left_strip (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → settle d ≤ t)
    (h0 : LhBandAgree t Q p0 L) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  have hk_lt : k < twopow k := twopow_gt_self k
  exact lhBandAgree_scale_step_outer_strip t k Q p0 L (by omega) h0
    (winWittAgree_settled_left_strip t k Q p0 L hk hset)

theorem lhBandAgree_step_of_settled_left_strip_prop (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → SettledBy d t)
    (h0 : LhBandAgree t Q p0 L) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L :=
  lhBandAgree_step_of_settled_left_strip t k Q p0 L hk hset h0

/-- **Unconditional `2^k`-Scale Diagonal-Shift Identity of `lhCenter` Across the Settled Left Wing and Outside the Cone (`lhCenter_scale_step_settled_left_ge`, 9.833)**:
    for all `t, k, p ∈ ℕ` with `t - p ≤ k` and `settle (t - p) ≤ t` (no bound `p ≤ t` required!), `lhCenter (t + 2^k) (p + 2^k) = lhCenter t p`! -/
theorem lhCenter_scale_step_settled_left_ge (t k p : Nat)
    (hk : t - p ≤ k) (hset : settle (t - p) ≤ t) :
    lhCenter (t + twopow k) (p + twopow k) = lhCenter t p := by
  have hk_lt : k < twopow k := twopow_gt_self k
  rw [lhCenter_scale_step_outer_strip t k p (by omega),
    winWitt_testBit_settled_left_ge t k p hk hset]
  cases lhCenter t p <;> rfl

theorem lhCenter_scale_step_settled_left_ge_prop (t k p : Nat)
    (hk : t - p ≤ k) (hset : SettledBy (t - p) t) :
    lhCenter (t + twopow k) (p + twopow k) = lhCenter t p :=
  lhCenter_scale_step_settled_left_ge t k p hk hset

/-- **Scale-Free Settled `ldiag` Vanishing on Any Zero Diagonal (`ldiag_of_zero_diag`, 9.834)**:
    for all `z, t ∈ ℕ` with `IsZeroDiag z` and `settle z ≤ t` (with no scale `k` or `2^k` shift!), `ldiag z t = false`! -/
theorem ldiag_of_zero_diag (z t : Nat)
    (hz : IsZeroDiag z) (hset : settle z ≤ t) :
    ldiag z t = false := by
  rw [Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D z t hset]
  exact hz t

theorem ldiag_of_zero_diag_prop (z t : Nat)
    (hz : IsZeroDiag z) (hset : SettledBy z t) :
    ldiag z t = false :=
  ldiag_of_zero_diag z t hz hset

/-- **Scale-Free Settled `ldiag` Blackness Two Diagonals After Any Zero Diagonal (`ldiag_after_zero_diag`, 9.835)**:
    for all `z, t ∈ ℕ` with `IsZeroDiag z` and `settle (z + 2) ≤ t` (with no scale `k` or `2^k` shift!), `ldiag (z + 2) t = true`! -/
theorem ldiag_after_zero_diag (z t : Nat)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ t) :
    ldiag (z + 2) t = true := by
  rw [Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D (z + 2) t hset]
  exact black_after_zero_diag z hz t

theorem ldiag_after_zero_diag_prop (z t : Nat)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) t) :
    ldiag (z + 2) t = true :=
  ldiag_after_zero_diag z t hz hset

/-- **Scale-Free Real-Orbit `lhCenter` Vanishing on Any Zero Diagonal (`lhCenter_of_zero_diag`, 9.836)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - p)` and `settle (t - p) ≤ t` (no bound `p ≤ t` and no scale `k` required, since `IsZeroDiag (t - p)` implies `2 ≤ t - p` by `zero_diag_ge_two`!), `lhCenter t p = false`! -/
theorem lhCenter_of_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - p)) (hset : settle (t - p) ≤ t) :
    lhCenter t p = false := by
  have hz2 := zero_diag_ge_two (t - p) hz
  rw [lhCenter_eq_ldiag t p (by omega)]
  exact ldiag_of_zero_diag (t - p) t hz hset

theorem lhCenter_of_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - p)) (hset : SettledBy (t - p) t) :
    lhCenter t p = false :=
  lhCenter_of_zero_diag t p hz hset

/-- **Scale-Free Real-Orbit `lhCenter` Blackness Two Diagonals After Any Zero Diagonal (`lhCenter_after_zero_diag`, 9.837)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - p)` and `settle ((t - p) + 2) ≤ t + 2` (no bound `p ≤ t` and no scale `k` required!), `lhCenter (t + 2) p = true`! -/
theorem lhCenter_after_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - p)) (hset : settle ((t - p) + 2) ≤ t + 2) :
    lhCenter (t + 2) p = true := by
  have hz2 := zero_diag_ge_two (t - p) hz
  rw [lhCenter_eq_ldiag (t + 2) p (by omega),
    show (t + 2) - p = (t - p) + 2 by omega]
  exact ldiag_after_zero_diag (t - p) (t + 2) hz hset

theorem lhCenter_after_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - p)) (hset : SettledBy ((t - p) + 2) (t + 2)) :
    lhCenter (t + 2) p = true :=
  lhCenter_after_zero_diag t p hz hset

/-- **Scale-Free Real-Orbit Twin Identity Before Any Zero Diagonal (`lhCenter_twin_before_zero_diag`, 9.838)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - p)` and `settle (t - p) ≤ t` (no bound `p ≤ t`, no scale `k`, and no settling hypothesis on `(t - p) - 2` or `(t - p) - 1`!), `lhCenter t (p + 2) = lhCenter t (p + 1)`! -/
theorem lhCenter_twin_before_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - p)) (hset : settle (t - p) ≤ t) :
    lhCenter t (p + 2) = lhCenter t (p + 1) := by
  have hz0 := lhCenter_of_zero_diag t p hz hset
  have hz1 : lhCenter (t + 1) (p + 1) = false := by
    exact lhCenter_of_zero_diag (t + 1) (p + 1)
      (by rwa [show (t + 1) - (p + 1) = t - p by omega])
      (by rw [show (t + 1) - (p + 1) = t - p by omega]; omega)
  have hstep := lhCenter_step_succ t p
  rw [hz1, hz0] at hstep
  revert hstep
  simp only [bxor_eq_xor]
  cases lhCenter t (p + 2) <;> cases lhCenter t (p + 1) <;> decide

theorem lhCenter_twin_before_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - p)) (hset : SettledBy (t - p) t) :
    lhCenter t (p + 2) = lhCenter t (p + 1) :=
  lhCenter_twin_before_zero_diag t p hz hset

/-- **Scale-Free Real-Orbit Post-Black Reset Complementation (`lhCenter_reset_after_zero_diag`, 9.839)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 1))` and `settle ((t - (p + 1)) + 2) ≤ t + 2` (no `p` bound, no scale `k`, and no settling hypothesis on `(t - (p + 1)) + 1` or `(t - (p + 1)) + 3`!), `lhCenter (t + 3) (p + 1) = !lhCenter (t + 2) (p + 2)`! -/
theorem lhCenter_reset_after_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - (p + 1)))
    (hset : settle ((t - (p + 1)) + 2) ≤ t + 2) :
    lhCenter (t + 3) (p + 1) = !lhCenter (t + 2) (p + 2) := by
  have hb := lhCenter_after_zero_diag t (p + 1) hz hset
  have hstep := lhCenter_step_succ (t + 2) p
  rw [show (t + 2) + 1 = t + 3 by omega, hb] at hstep
  rw [hstep]
  simp only [bxor_eq_xor]
  cases lhCenter (t + 2) (p + 2) <;> cases lhCenter (t + 2) p <;> rfl

theorem lhCenter_reset_after_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - (p + 1)))
    (hset : SettledBy ((t - (p + 1)) + 2) (t + 2)) :
    lhCenter (t + 3) (p + 1) = !lhCenter (t + 2) (p + 2) :=
  lhCenter_reset_after_zero_diag t p hz hset

/-- **Scale-Free Real-Orbit 2-Step Same-Column Flip Across Any Zero Diagonal (`lhCenter_two_step_same_col_flip_of_zero_diag`, 9.840)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - p)`, `settle (t - p) ≤ t`, and `settle ((t - p) + 2) ≤ t + 2` (no `p ≤ t` bound and no scale `k`!), `lhCenter (t + 2) p = !lhCenter t p` at the same spatial column `p`! -/
theorem lhCenter_two_step_same_col_flip_of_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - p))
    (hset0 : settle (t - p) ≤ t)
    (hset2 : settle ((t - p) + 2) ≤ t + 2) :
    lhCenter (t + 2) p = !lhCenter t p := by
  rw [lhCenter_after_zero_diag t p hz hset2,
    lhCenter_of_zero_diag t p hz hset0]
  rfl

theorem lhCenter_two_step_same_col_flip_of_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - p))
    (hset0 : SettledBy (t - p) t)
    (hset2 : SettledBy ((t - p) + 2) (t + 2)) :
    lhCenter (t + 2) p = !lhCenter t p :=
  lhCenter_two_step_same_col_flip_of_zero_diag t p hz hset0 hset2

/-- **Scale-Free Refutation of `LhBandAgree t 2 p0 L` Across Any Settled Zero Diagonal (`not_lhBandAgree_two_of_zero_diag`, 9.841)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - p)`, `settle (t - p) ≤ t`, `settle ((t - p) + 2) ≤ t + 2`, `p0 ≤ p`, and `p ≤ p0 + L` (no scale `k` or `winWitt`!), `¬ LhBandAgree t 2 p0 L`! -/
theorem not_lhBandAgree_two_of_zero_diag (t p p0 L : Nat)
    (hz : IsZeroDiag (t - p))
    (hset0 : settle (t - p) ≤ t)
    (hset2 : settle ((t - p) + 2) ≤ t + 2)
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L) :
    ¬ LhBandAgree t 2 p0 L := by
  intro hband
  have hb := hband (p - p0) (by omega)
  rw [show p0 + (p - p0) = p by omega] at hb
  rw [lhCenter_after_zero_diag t p hz hset2,
    lhCenter_of_zero_diag t p hz hset0] at hb
  cases hb

theorem not_lhBandAgree_two_of_zero_diag_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - p))
    (hset0 : SettledBy (t - p) t)
    (hset2 : SettledBy ((t - p) + 2) (t + 2))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L) :
    ¬ LhBandAgree t 2 p0 L :=
  not_lhBandAgree_two_of_zero_diag t p p0 L hz hset0 hset2 hp0 hL

/-- **Scale-Free General-`Q` Refutation of `LhBandAgree t Q p0 L` When `(t + Q) - p = z + 2` (`not_lhBandAgree_of_zero_and_after_zero_diag`, 9.842)**:
    for all `Q, t, p, z, p0, L ∈ ℕ` with `IsZeroDiag (t - p)`, `IsZeroDiag z`, `(t + Q) - p = z + 2`, `settle (t - p) ≤ t`, `settle (z + 2) ≤ t + Q`, `p0 ≤ p`, and `p ≤ p0 + L` (no scale `k` or `winWitt`!), `¬ LhBandAgree t Q p0 L`! -/
theorem not_lhBandAgree_of_zero_and_after_zero_diag (Q t p z p0 L : Nat)
    (hz1 : IsZeroDiag (t - p)) (hz2 : IsZeroDiag z)
    (hrel : (t + Q) - p = z + 2)
    (hset1 : settle (t - p) ≤ t)
    (hset2 : settle (z + 2) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L) :
    ¬ LhBandAgree t Q p0 L := by
  intro hband
  have hb := hband (p - p0) (by omega)
  rw [show p0 + (p - p0) = p by omega] at hb
  have hz2_ge := zero_diag_ge_two z hz2
  have hQ : lhCenter (t + Q) p = true := by
    rw [lhCenter_eq_ldiag (t + Q) p (by omega), hrel]
    exact ldiag_after_zero_diag z (t + Q) hz2 hset2
  rw [hQ, lhCenter_of_zero_diag t p hz1 hset1] at hb
  cases hb

theorem not_lhBandAgree_of_zero_and_after_zero_diag_prop (Q t p z p0 L : Nat)
    (hz1 : IsZeroDiag (t - p)) (hz2 : IsZeroDiag z)
    (hrel : (t + Q) - p = z + 2)
    (hset1 : SettledBy (t - p) t)
    (hset2 : SettledBy (z + 2) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L) :
    ¬ LhBandAgree t Q p0 L :=
  not_lhBandAgree_of_zero_and_after_zero_diag Q t p z p0 L hz1 hz2 hrel hset1 hset2 hp0 hL

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Transport of Zero-Diagonal Vanishing Down to Row `t` (`lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree`, 9.843)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - p)`, `settle ((t + Q) - p) ≤ t + Q`, `p0 ≤ p`, and `p ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (with no `DoublesAt`, no `LhBandAgree (t + 1)`, no scale `k`, and no `winWitt`!), then `lhCenter t p = false`! -/
theorem lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : settle ((t + Q) - p) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t p = false := by
  have hb := hband (p - p0) (by omega)
  rw [show p0 + (p - p0) = p by omega] at hb
  rw [← hb]
  exact lhCenter_of_zero_diag (t + Q) p hz hset

theorem lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t p = false :=
  lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Transport of Post-Zero Blackness Down to Row `t` (`lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree`, 9.844)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - (p + 2))`, `settle (((t + Q) - (p + 2)) + 2) ≤ t + Q`, `p0 ≤ p`, and `p ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone, then `lhCenter t p = true`! -/
theorem lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 2)))
    (hset : settle (((t + Q) - (p + 2)) + 2) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t p = true := by
  have hb := hband (p - p0) (by omega)
  rw [show p0 + (p - p0) = p by omega] at hb
  have hz2 := zero_diag_ge_two ((t + Q) - (p + 2)) hz
  rw [← hb, lhCenter_eq_ldiag (t + Q) p (by omega),
    show (t + Q) - p = ((t + Q) - (p + 2)) + 2 by omega]
  exact ldiag_after_zero_diag ((t + Q) - (p + 2)) (t + Q) hz hset

theorem lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 2)))
    (hset : SettledBy (((t + Q) - (p + 2)) + 2) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t p = true :=
  lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` 1-Step Post-Black Reset Complementation (`lhCenter_step_flip_at_shift_after_zero_diag_of_single_lhBandAgree`, 9.845)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - (p + 3))`, `settle (((t + Q) - (p + 3)) + 2) ≤ t + Q`, `p0 ≤ p + 1`, and `p + 1 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (with no `LhBandAgree (t + 1)`, no `DoublesAt`, no scale `k`, and no `winWitt`!), then `lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2)`! -/
theorem lhCenter_step_flip_at_shift_after_zero_diag_of_single_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 3)))
    (hset : settle (((t + Q) - (p + 3)) + 2) ≤ t + Q)
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2) := by
  have hb := lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree Q t (p + 1) p0 L
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    hp0 hL hband
  have hstep := lhCenter_step_succ t p
  rw [hb] at hstep
  rw [hstep]
  simp only [bxor_eq_xor]
  cases lhCenter t (p + 2) <;> cases lhCenter t p <;> rfl

theorem lhCenter_step_flip_at_shift_after_zero_diag_of_single_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 3)))
    (hset : SettledBy (((t + Q) - (p + 3)) + 2) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2) :=
  lhCenter_step_flip_at_shift_after_zero_diag_of_single_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` 1-Step Fixed-Column Jump to `true` (`lhCenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhBandAgree`, 9.846)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - (p + 2))`, `settle ((t + Q) - (p + 2)) ≤ t + Q`, `settle (((t + Q) - (p + 2)) + 2) ≤ t + Q`, `p0 ≤ p`, and `p + 2 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (with no `LhBandAgree (t + 1)`, no `DoublesAt`, no scale `k`, and no `winWitt`!), then `lhCenter (t + 1) (p + 1) = true`! -/
theorem lhCenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 2)))
    (hset0 : settle ((t + Q) - (p + 2)) ≤ t + Q)
    (hset2 : settle (((t + Q) - (p + 2)) + 2) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = true := by
  have hz_false := lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree Q t (p + 2) p0 L
    hz hset0 (by omega) hL hband
  have hb_true := lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree Q t p p0 L
    hz hset2 hp0 (by omega) hband
  have hstep := lhCenter_step_succ t p
  rw [hz_false, hb_true] at hstep
  rw [hstep]
  cases lhCenter t (p + 1) <;> rfl

theorem lhCenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 2)))
    (hset0 : SettledBy ((t + Q) - (p + 2)) (t + Q))
    (hset2 : SettledBy (((t + Q) - (p + 2)) + 2) (t + Q))
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = true :=
  lhCenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhBandAgree
    Q t p p0 L hz hset0 hset2 hp0 hL hband

/-! ### Batch 37: Producing `LhBandAgree` from `RhColAgree`, Scale-Free Real-Orbit `LhBandAgree` Twin/Linearization/OR-Absorption Laws, and Cross-Center Laws Dropping `z ≤ k` (9.847–9.861) -/

/-- **Producing `LhBandAgree t (m * P) 0 (S + 1)` Directly from `RhColAgree t (m * P) 1 S` Under `CenterPeriodic` (`periodic_lhBandAgree_zero_of_rhColAgree_one`, 9.847)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S ∈ ℕ` with `T ≤ t`, if `RhColAgree t (m * P) 1 S` holds, then `LhBandAgree t (m * P) 0 (S + 1)` holds! -/
theorem periodic_lhBandAgree_zero_of_rhColAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hrh : RhColAgree t (m * P) 1 S) :
    LhBandAgree t (m * P) 0 (S + 1) := by
  exact lhBandAgree_of_outward_determine t (m * P) 0 S
    (periodic_lhColAgree_zero T P hP hper m t S ht)
    (periodic_lhColAgree_one_of_rhColAgree_one T P hP hper m t S ht hrh)

/-- **Producing Center-Anchored `LhBandAgree (t + s) (m * P) 0 (L + 1)` at Every Intermediate Step `t + s` from `RhColAgree t (m * P) 1 (L + s)` (`periodic_lhBandAgree_steps_of_rhColAgree_one`, 9.848)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, L, s ∈ ℕ` with `T ≤ t`, if `RhColAgree t (m * P) 1 (L + s)` holds over `[t, t + L + s]`, then `LhBandAgree (t + s) (m * P) 0 (L + 1)` holds at time `t + s` (keeping `p0 = 0` anchored at the center and losing only `s` steps of horizon instead of `2 * s`!)! -/
theorem periodic_lhBandAgree_steps_of_rhColAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L s : Nat) (ht : T ≤ t)
    (hrh : RhColAgree t (m * P) 1 (L + s)) :
    LhBandAgree (t + s) (m * P) 0 (L + 1) := by
  have hsub := rhColAgree_mono t (m * P) 1 (L + s) s L (by omega) hrh
  exact periodic_lhBandAgree_zero_of_rhColAgree_one T P hP hper m (t + s) L (by omega) hsub

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Transport of the Twin Identity Down by `Q` Steps (`lhCenter_twin_at_shift_of_zero_diag_and_lhBandAgree`, 9.849)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - p)`, `settle ((t + Q) - p) ≤ t + Q`, `p0 ≤ p + 1`, and `p + 2 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (with no `DoublesAt`, no `LhBandAgree (t + 1)`, no scale `k`, and no `winWitt`!), then `lhCenter t (p + 2) = lhCenter t (p + 1)`! -/
theorem lhCenter_twin_at_shift_of_zero_diag_and_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : settle ((t + Q) - p) ≤ t + Q)
    (hp0 : p0 ≤ p + 1) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + 2) = lhCenter t (p + 1) := by
  have h1 := hband ((p + 1) - p0) (by omega)
  have h2 := hband ((p + 2) - p0) (by omega)
  rw [show p0 + ((p + 1) - p0) = p + 1 by omega] at h1
  rw [show p0 + ((p + 2) - p0) = p + 2 by omega] at h2
  rw [← h2, ← h1]
  exact lhCenter_twin_before_zero_diag (t + Q) p hz hset

theorem lhCenter_twin_at_shift_of_zero_diag_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + 2) = lhCenter t (p + 1) :=
  lhCenter_twin_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Linearization 1 Below Any Zero Diagonal (`lhCenter_linear_step_one_at_shift_of_zero_diag_and_lhBandAgree`, 9.850)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - p)`, `settle ((t + Q) - p) ≤ t + Q`, `p0 ≤ p`, and `p ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone, then `lhCenter (t + 1) (p + 1) = lhCenter t (p + 2) ⊕ lhCenter t (p + 1)`! -/
theorem lhCenter_linear_step_one_at_shift_of_zero_diag_and_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : settle ((t + Q) - p) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = bxor (lhCenter t (p + 2)) (lhCenter t (p + 1)) := by
  have hz0 := lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 hL hband
  rw [lhCenter_step_succ t p, hz0, Bool.or_false]

theorem lhCenter_linear_step_one_at_shift_of_zero_diag_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = bxor (lhCenter t (p + 2)) (lhCenter t (p + 1)) :=
  lhCenter_linear_step_one_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Linearization 2 Below Any Zero Diagonal (`lhCenter_linear_step_two_at_shift_of_zero_diag_and_lhBandAgree`, 9.851)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - (p + 1))`, `settle ((t + Q) - (p + 1)) ≤ t + Q`, `p0 ≤ p + 1`, and `p + 1 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone, then `lhCenter (t + 1) (p + 1) = lhCenter t (p + 2) ⊕ lhCenter t p`! -/
theorem lhCenter_linear_step_two_at_shift_of_zero_diag_and_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 1)))
    (hset : settle ((t + Q) - (p + 1)) ≤ t + Q)
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = bxor (lhCenter t (p + 2)) (lhCenter t p) := by
  have hz1 := lhCenter_eq_false_at_shift_of_zero_diag_and_lhBandAgree Q t (p + 1) p0 L hz hset hp0 hL hband
  rw [lhCenter_step_succ t p, hz1, Bool.false_or]

theorem lhCenter_linear_step_two_at_shift_of_zero_diag_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - (p + 1)))
    (hset : SettledBy ((t + Q) - (p + 1)) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = bxor (lhCenter t (p + 2)) (lhCenter t p) :=
  lhCenter_linear_step_two_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Twin Cancellation Pinning `lhCenter (t + 1) (p + 1) = false` (`lhCenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhBandAgree`, 9.852)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag ((t + Q) - p)`, `settle ((t + Q) - p) ≤ t + Q`, `p0 ≤ p`, and `p + 2 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (with no `DoublesAt`, no `LhBandAgree (t + 1)`, no scale `k`, and no `winWitt`!), then `lhCenter (t + 1) (p + 1) = false`! -/
theorem lhCenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : settle ((t + Q) - p) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = false := by
  rw [lhCenter_linear_step_one_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset hp0 (by omega) hband,
    lhCenter_twin_at_shift_of_zero_diag_and_lhBandAgree Q t p p0 L hz hset (by omega) hL hband]
  cases lhCenter t (p + 1) <;> rfl

theorem lhCenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag ((t + Q) - p))
    (hset : SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = false :=
  lhCenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhBandAgree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-Free General-`Q` Single-Time Refutation of `LhBandAgree t Q p0 L` When Both `t - (p + 2)` and `(t + Q) - p` Are Zero Diagonals (`not_lhBandAgree_of_zero_diag_two_and_shift_zero_diag`, 9.853)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 2))`, `IsZeroDiag ((t + Q) - p)`, `settle ((t - (p + 2)) + 2) ≤ t + 1`, `settle ((t + Q) - p) ≤ t + Q`, `p0 ≤ p`, and `p + 2 ≤ p0 + L` (no `DoublesAt`, no `LhBandAgree (t + 1)`, no scale `k`, and no `winWitt`!), `¬ LhBandAgree t Q p0 L`! -/
theorem not_lhBandAgree_of_zero_diag_two_and_shift_zero_diag (Q t p p0 L : Nat)
    (hz1 : IsZeroDiag (t - (p + 2)))
    (hz2 : IsZeroDiag ((t + Q) - p))
    (hset1 : settle ((t - (p + 2)) + 2) ≤ t + 1)
    (hset2 : settle ((t + Q) - p) ≤ t + Q)
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L) :
    ¬ LhBandAgree t Q p0 L := by
  intro hband
  have hf := lhCenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhBandAgree Q t p p0 L hz2 hset2 hp0 hL hband
  have hz1_ge := zero_diag_ge_two (t - (p + 2)) hz1
  have ht : lhCenter (t + 1) (p + 1) = true := by
    rw [lhCenter_eq_ldiag (t + 1) (p + 1) (by omega),
      show (t + 1) - (p + 1) = (t - (p + 2)) + 2 by omega]
    exact ldiag_after_zero_diag (t - (p + 2)) (t + 1) hz1 hset1
  rw [ht] at hf
  cases hf

theorem not_lhBandAgree_of_zero_diag_two_and_shift_zero_diag_prop (Q t p p0 L : Nat)
    (hz1 : IsZeroDiag (t - (p + 2)))
    (hz2 : IsZeroDiag ((t + Q) - p))
    (hset1 : SettledBy ((t - (p + 2)) + 2) (t + 1))
    (hset2 : SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L) :
    ¬ LhBandAgree t Q p0 L :=
  not_lhBandAgree_of_zero_diag_two_and_shift_zero_diag Q t p p0 L hz1 hz2 hset1 hset2 hp0 hL

/-- **Scale-Free Real-Orbit 1-Step Post-Zero OR-Absorption Law on `z + 4` (`lhCenter_step_absorb_false_after_zero_diag`, 9.854)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 2))` and `settle ((t - (p + 2)) + 2) ≤ t + 2` (with no settling hypothesis on `z + 3` or `z + 4` and no scale `k`!), if `lhCenter (t + 2) (p + 1) = true`, then `lhCenter (t + 3) (p + 1) = false`! -/
theorem lhCenter_step_absorb_false_after_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - (p + 2)))
    (hset : settle ((t - (p + 2)) + 2) ≤ t + 2)
    (h3 : lhCenter (t + 2) (p + 1) = true) :
    lhCenter (t + 3) (p + 1) = false := by
  have hb := lhCenter_after_zero_diag t (p + 2) hz hset
  have hstep := lhCenter_step_succ (t + 2) p
  rw [show (t + 2) + 1 = t + 3 by omega, hb, h3] at hstep
  rw [hstep]
  cases lhCenter (t + 2) p <;> rfl

theorem lhCenter_step_absorb_false_after_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - (p + 2)))
    (hset : SettledBy ((t - (p + 2)) + 2) (t + 2))
    (h3 : lhCenter (t + 2) (p + 1) = true) :
    lhCenter (t + 3) (p + 1) = false :=
  lhCenter_step_absorb_false_after_zero_diag t p hz hset h3

/-- **Scale-Free Real-Orbit 2-Step Post-Zero Reset-and-Absorption Law from `z + 1` to `z + 4` (`lhCenter_two_step_absorb_false_after_zero_diag`, 9.855)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 2))` and `settle ((t - (p + 2)) + 2) ≤ t + 2` (with no settling hypothesis on `z + 1`, `z + 3`, or `z + 4` and no scale `k`!), if `lhCenter (t + 2) (p + 3) = false`, then `lhCenter (t + 4) (p + 2) = false`! -/
theorem lhCenter_two_step_absorb_false_after_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - (p + 2)))
    (hset : settle ((t - (p + 2)) + 2) ≤ t + 2)
    (h1 : lhCenter (t + 2) (p + 3) = false) :
    lhCenter (t + 4) (p + 2) = false := by
  have hrst := lhCenter_reset_after_zero_diag t (p + 1)
    (by rwa [show (p + 1) + 1 = p + 2 by omega])
    (by rwa [show (p + 1) + 1 = p + 2 by omega])
  rw [show (p + 1) + 1 = p + 2 by omega, show (p + 1) + 2 = p + 3 by omega, h1] at hrst
  have habs := lhCenter_step_absorb_false_after_zero_diag (t + 1) (p + 1)
    (by rwa [show (t + 1) - ((p + 1) + 2) = t - (p + 2) by omega])
    (by rw [show (t + 1) - ((p + 1) + 2) = t - (p + 2) by omega]; omega)
    (by rw [show (t + 1) + 2 = t + 3 by omega, show (p + 1) + 1 = p + 2 by omega]; exact hrst)
  rwa [show (t + 1) + 3 = t + 4 by omega, show (p + 1) + 1 = p + 2 by omega] at habs

theorem lhCenter_two_step_absorb_false_after_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - (p + 2)))
    (hset : SettledBy ((t - (p + 2)) + 2) (t + 2))
    (h1 : lhCenter (t + 2) (p + 3) = false) :
    lhCenter (t + 4) (p + 2) = false :=
  lhCenter_two_step_absorb_false_after_zero_diag t p hz hset h1

/-- **Unconditional Cross-Center Zero-Diagonal Vanishing Without `t + r ≤ k` (`lhCenter_late_cross_of_zero_diag_uncond`, 9.856)**:
    for all `t, k, r ∈ ℕ` with `r ≤ 2^k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k` (dropping `t + r ≤ k`!), `lhCenter (t + 2^k) (2^k - r) = false`! -/
theorem lhCenter_late_cross_of_zero_diag_uncond (t k r : Nat)
    (hr : r ≤ twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - r) = false := by
  rw [lhCenter_late_cross_eq_ldiag t k r hr]
  exact ldiag_of_zero_diag (t + r) (t + twopow k) hz hset

theorem lhCenter_late_cross_of_zero_diag_uncond_prop (t k r : Nat)
    (hr : r ≤ twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    lhCenter (t + twopow k) (twopow k - r) = false :=
  lhCenter_late_cross_of_zero_diag_uncond t k r hr hz hset

/-- **Unconditional Cross-Center Post-Zero Blackness Without `(t + r) + 2 ≤ k` (`lhCenter_late_cross_after_zero_diag_uncond`, 9.857)**:
    for all `t, k, r ∈ ℕ` with `r + 2 ≤ 2^k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `lhCenter (t + 2^k) (2^k - (r + 2)) = true`! -/
theorem lhCenter_late_cross_after_zero_diag_uncond (t k r : Nat)
    (hr : r + 2 ≤ twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true := by
  rw [lhCenter_late_cross_eq_ldiag t k (r + 2) hr,
    show t + (r + 2) = (t + r) + 2 by omega]
  exact ldiag_after_zero_diag (t + r) (t + twopow k) hz hset

theorem lhCenter_late_cross_after_zero_diag_uncond_prop (t k r : Nat)
    (hr : r + 2 ≤ twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_after_zero_diag_uncond t k r hr hz hset

/-- **Unconditional Cross-Center Post-Black Reset Complementation Without `(t + r) + 2 ≤ k` (`lhCenter_late_cross_reset_after_zero_diag_uncond`, 9.858)**:
    for all `t, k, r ∈ ℕ` with `r + 3 ≤ 2^k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`! -/
theorem lhCenter_late_cross_reset_after_zero_diag_uncond (t k r : Nat)
    (hr : r + 3 ≤ twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have hb := lhCenter_late_cross_after_zero_diag_uncond t k r (by omega) hz hset
  have hstep := lhCenter_late_cross_step t k r hr
  rw [hb] at hstep
  rw [hstep]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases lhCenter (t + twopow k) (twopow k - (r + 3)) <;> rfl

theorem lhCenter_late_cross_reset_after_zero_diag_uncond_prop (t k r : Nat)
    (hr : r + 3 ≤ twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_reset_after_zero_diag_uncond t k r hr hz hset

/-- **Unconditional Cross-Center Twin Identity Before Any Zero Diagonal Without `(t + r) + 2 ≤ k` (`lhCenter_late_cross_twin_before_zero_diag_uncond`, 9.859)**:
    for all `t, k, r ∈ ℕ` with `r + 2 ≤ 2^k`, `IsZeroDiag ((t + r) + 2)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))`! -/
theorem lhCenter_late_cross_twin_before_zero_diag_uncond (t k r : Nat)
    (hr : r + 2 ≤ twopow k) (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have htw := lhCenter_twin_before_zero_diag (t + twopow k) (twopow k - (r + 2))
    (by rwa [show (t + twopow k) - (twopow k - (r + 2)) = (t + r) + 2 by omega])
    (by rwa [show (t + twopow k) - (twopow k - (r + 2)) = (t + r) + 2 by omega])
  rwa [show (twopow k - (r + 2)) + 2 = twopow k - r by omega,
    show (twopow k - (r + 2)) + 1 = twopow k - (r + 1) by omega] at htw

theorem lhCenter_late_cross_twin_before_zero_diag_uncond_prop (t k r : Nat)
    (hr : r + 2 ≤ twopow k) (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_twin_before_zero_diag_uncond t k r hr hz hset

/-- **Unconditional Cross-Center `Q`-Periodicity Below Any Doubling Point Without `z ≤ k` (`lhCenter_late_cross_periodic_of_doubles_le_uncond`, 9.860)**:
    for EVERY shift `Q` at once, and for all `z, t, k, r ∈ ℕ` with `r + Q ≤ 2^k`, `(t + Q) + r ≤ z`, `DoublesAt Q z`, and `settle ((t + Q) + r) ≤ t + 2^k` (dropping `z ≤ k`!), `lhCenter ((t + Q) + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + Q))`! -/
theorem lhCenter_late_cross_periodic_of_doubles_le_uncond (Q z t k r : Nat)
    (hr : r + Q ≤ twopow k) (hdz : (t + Q) + r ≤ z)
    (hd : DoublesAt Q z)
    (hset : settle ((t + Q) + r) ≤ t + twopow k) :
    lhCenter ((t + Q) + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + Q)) := by
  rw [lhCenter_late_cross_eq_ldiag (t + Q) k r (by omega),
    lhCenter_late_cross_eq_ldiag t k (r + Q) hr,
    show t + (r + Q) = (t + Q) + r by omega,
    show (t + Q) + twopow k = (t + twopow k) + Q by omega]
  exact ldiag_settled_periodic_of_doubles_le Q z ((t + Q) + r) (t + twopow k) hd hdz hset

theorem lhCenter_late_cross_periodic_of_doubles_le_uncond_prop (Q z t k r : Nat)
    (hr : r + Q ≤ twopow k) (hdz : (t + Q) + r ≤ z)
    (hd : DoublesAt Q z)
    (hset : SettledBy ((t + Q) + r) (t + twopow k)) :
    lhCenter ((t + Q) + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + Q)) :=
  lhCenter_late_cross_periodic_of_doubles_le_uncond Q z t k r hr hdz hd hset

/-- **Unconditional Cross-Center `Q`-Antiperiodicity on the Doubling Diagonal `z + 1` Without `z + 1 ≤ k` (`lhCenter_late_cross_antiperiodic_of_doubles_uncond`, 9.861)**:
    for EVERY shift `Q` at once, and for all `t, k, r ∈ ℕ` with `(r + Q) + 1 ≤ 2^k`, `IsZeroDiag ((t + Q) + r)`, `DoublesAt Q ((t + Q) + r)`, and `settle (((t + Q) + r) + 1) ≤ t + 2^k` (dropping `((t + Q) + r) + 1 ≤ k`!), `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = !lhCenter (t + 2^k) (2^k - ((r + Q) + 1))`! -/
theorem lhCenter_late_cross_antiperiodic_of_doubles_uncond (Q t k r : Nat)
    (hr : (r + Q) + 1 ≤ twopow k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + 1)) =
      !lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) := by
  rw [lhCenter_late_cross_eq_ldiag (t + Q) k (r + 1) (by omega),
    lhCenter_late_cross_eq_ldiag t k ((r + Q) + 1) hr,
    show t + ((r + Q) + 1) = ((t + Q) + r) + 1 by omega,
    show (t + Q) + (r + 1) = ((t + Q) + r) + 1 by omega,
    show (t + Q) + twopow k = (t + twopow k) + Q by omega]
  exact ldiag_settled_antiperiodic_of_doubles Q ((t + Q) + r) (t + twopow k) hz hd hset

theorem lhCenter_late_cross_antiperiodic_of_doubles_uncond_prop (Q t k r : Nat)
    (hr : (r + Q) + 1 ≤ twopow k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k)) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + 1)) =
      !lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) :=
  lhCenter_late_cross_antiperiodic_of_doubles_uncond Q t k r hr hz hd hset

/-! ### Batch 38: Unconditional Sector-2 `winWitt` Laws Dropping `z ≤ k` and Scale-Free Real-Orbit `LhBandAgree` Doubling-Diagonal Cascade at Row `t` (9.862–9.876) -/

/-- **Unconditional Sector-2 Cross-Center Window Mirror Along Any Zero Diagonal Without `t + r ≤ k` (`winWitt_testBit_scale_cross_of_zero_diag_uncond`, 9.862)**:
    for all `t, k, r ∈ ℕ` with `t + r < 2^k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k` (dropping `t + r ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = rhCenter t r`! -/
theorem winWitt_testBit_scale_cross_of_zero_diag_uncond (t k r : Nat)
    (hlt : t + r < twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) = rhCenter t r := by
  rw [winWitt_testBit_scale_cross_cone t k r hlt,
    lhCenter_late_cross_of_zero_diag_uncond t k r (by omega) hz hset]
  cases rhCenter t r <;> rfl

theorem winWitt_testBit_scale_cross_of_zero_diag_uncond_prop (t k r : Nat)
    (hlt : t + r < twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) = rhCenter t r :=
  winWitt_testBit_scale_cross_of_zero_diag_uncond t k r hlt hz hset

/-- **Unconditional Sector-2 Inter-Cone Zero-Gap `false` Pinning Along Any Zero Diagonal Without `t + r ≤ k` (`winWitt_testBit_scale_cross_zero_gap_of_zero_diag_uncond`, 9.863)**:
    for all `t, k, r ∈ ℕ` with `t < r`, `t + r < 2^k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k` (dropping `t + r ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false`! -/
theorem winWitt_testBit_scale_cross_zero_gap_of_zero_diag_uncond (t k r : Nat)
    (htr : t < r) (hlt : t + r < twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) = false := by
  rw [winWitt_testBit_scale_cross_of_zero_diag_uncond t k r hlt hz hset,
    rhCenter_gt_eq_false t r htr]

theorem winWitt_testBit_scale_cross_zero_gap_of_zero_diag_uncond_prop (t k r : Nat)
    (htr : t < r) (hlt : t + r < twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) = false :=
  winWitt_testBit_scale_cross_zero_gap_of_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional Sector-2 Cross-Center Negated Window Mirror Along the Post-Zero Black Diagonal Without `(t + r) + 2 ≤ k` (`winWitt_testBit_scale_cross_after_zero_diag_uncond`, 9.864)**:
    for all `t, k, r ∈ ℕ` with `(t + r) + 2 < 2^k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !rhCenter t (r + 2)`! -/
theorem winWitt_testBit_scale_cross_after_zero_diag_uncond (t k r : Nat)
    (hlt : (t + r) + 2 < twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) =
      !rhCenter t (r + 2) := by
  rw [winWitt_testBit_scale_cross_cone t k (r + 2) (by omega),
    lhCenter_late_cross_after_zero_diag_uncond t k r (by omega) hz hset]
  cases rhCenter t (r + 2) <;> rfl

theorem winWitt_testBit_scale_cross_after_zero_diag_uncond_prop (t k r : Nat)
    (hlt : (t + r) + 2 < twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) =
      !rhCenter t (r + 2) :=
  winWitt_testBit_scale_cross_after_zero_diag_uncond t k r hlt hz hset

/-- **Unconditional Sector-2 Inter-Cone Zero-Gap `true` Pinning Along the Post-Zero Black Diagonal Without `(t + r) + 2 ≤ k` (`winWitt_testBit_scale_cross_zero_gap_after_zero_diag_uncond`, 9.865)**:
    for all `t, k, r ∈ ℕ` with `t < r + 2`, `(t + r) + 2 < 2^k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true`! -/
theorem winWitt_testBit_scale_cross_zero_gap_after_zero_diag_uncond (t k r : Nat)
    (htr : t < r + 2) (hlt : (t + r) + 2 < twopow k) (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  rw [winWitt_testBit_scale_cross_after_zero_diag_uncond t k r hlt hz hset,
    rhCenter_gt_eq_false t (r + 2) htr]
  rfl

theorem winWitt_testBit_scale_cross_zero_gap_after_zero_diag_uncond_prop (t k r : Nat)
    (htr : t < r + 2) (hlt : (t + r) + 2 < twopow k) (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_testBit_scale_cross_zero_gap_after_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional Sector-2 Inter-Cone Zero-Gap Adjacent Twin Equality Before Any Zero Diagonal Without `(t + r) + 2 ≤ k` (`winWitt_testBit_scale_cross_zero_gap_twin_before_zero_diag_uncond`, 9.866)**:
    for all `t, k, r ∈ ℕ` with `t < r`, `(t + r) + 2 ≤ 2^k`, `IsZeroDiag ((t + r) + 2)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`! -/
theorem winWitt_testBit_scale_cross_zero_gap_twin_before_zero_diag_uncond (t k r : Nat)
    (htr : t < r) (hlt : (t + r) + 2 ≤ twopow k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  rw [winWitt_testBit_scale_cross_cone t k r (by omega),
    winWitt_testBit_scale_cross_cone t k (r + 1) (by omega),
    rhCenter_gt_eq_false t r htr,
    rhCenter_gt_eq_false t (r + 1) (by omega),
    lhCenter_late_cross_twin_before_zero_diag_uncond t k r (by omega) hz hset]

theorem winWitt_testBit_scale_cross_zero_gap_twin_before_zero_diag_uncond_prop (t k r : Nat)
    (htr : t < r) (hlt : (t + r) + 2 ≤ twopow k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) :=
  winWitt_testBit_scale_cross_zero_gap_twin_before_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional 1-Step Sector-2 Bit Flip in the Inter-Cone Zero Gap Across the Post-Zero Black Diagonal Without `(t + r) + 2 ≤ k` (`winWitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond`, 9.867)**:
    for all `t, k, r ∈ ℕ` with `t ≤ r`, `(t + r) + 3 < 2^k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (dropping `(t + r) + 2 ≤ k`!), `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`! -/
theorem winWitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond (t k r : Nat)
    (htr : t ≤ r) (hlt : (t + r) + 3 < twopow k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h1 := winWitt_testBit_scale_cross_cone t k (r + 1) (by omega)
  have h2 := winWitt_testBit_scale_cross_cone (t + 1) k (r + 2) (by omega)
  rw [show ((t + 1) + twopow (k + 1)) - (r + 2) = (t + twopow (k + 1)) - (r + 1) by omega,
    lhCenter_late_cross_reset_after_zero_diag_uncond t k r (by omega) hz hset,
    rhCenter_gt_eq_false (t + 1) (r + 2) (by omega)] at h2
  rw [rhCenter_gt_eq_false t (r + 1) (by omega)] at h1
  rw [h1, h2]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> rfl

theorem winWitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond_prop (t k r : Nat)
    (htr : t ≤ r) (hlt : (t + r) + 3 < twopow k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) :=
  winWitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional Sector-2 Cross-Center `winWitt` `Q`-Periodicity Below Any Doubling Point Without `z ≤ k` (`winWitt_scale_cross_periodic_of_doubles_le_uncond`, 9.868)**:
    for EVERY shift `Q` at once, and for all `z, t, k, r ∈ ℕ` with `(t + Q) + r < 2^k`, `(t + Q) + r ≤ z`, `DoublesAt Q z`, and `settle ((t + Q) + r) ≤ t + 2^k` (dropping `z ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + Q)) ⊕ (winWitt (t + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - r) = rhCenter t (r + Q) ⊕ rhCenter (t + Q) r`! -/
theorem winWitt_scale_cross_periodic_of_doubles_le_uncond (Q z t k r : Nat)
    (hlt : (t + Q) + r < twopow k) (hdz : (t + Q) + r ≤ z)
    (hd : DoublesAt Q z)
    (hset : settle ((t + Q) + r) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + Q)))
      ((winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - r)) =
      bxor (rhCenter t (r + Q)) (rhCenter (t + Q) r) := by
  rw [winWitt_testBit_scale_cross_cone t k (r + Q) (by omega),
    winWitt_testBit_scale_cross_cone (t + Q) k r hlt,
    lhCenter_late_cross_periodic_of_doubles_le_uncond Q z t k r (by omega) hdz hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + Q)) <;>
    cases rhCenter t (r + Q) <;>
    cases rhCenter (t + Q) r <;> decide

theorem winWitt_scale_cross_periodic_of_doubles_le_uncond_prop (Q z t k r : Nat)
    (hlt : (t + Q) + r < twopow k) (hdz : (t + Q) + r ≤ z)
    (hd : DoublesAt Q z)
    (hset : SettledBy ((t + Q) + r) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + Q)))
      (wittBitBool (winWitt (t + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - r)) =
      bxor (rhCenter t (r + Q)) (rhCenter (t + Q) r) :=
  winWitt_scale_cross_periodic_of_doubles_le_uncond Q z t k r hlt hdz hd hset

/-- **Unconditional Sector-2 Inter-Cone Zero-Gap `Q`-Periodicity Below Any Doubling Point Without `z ≤ k` (`winWitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond`, 9.869)**:
    for EVERY shift `Q` at once, and for all `z, t, k, r ∈ ℕ` with `t + Q < r`, `(t + Q) + r < 2^k`, `(t + Q) + r ≤ z`, `DoublesAt Q z`, and `settle ((t + Q) + r) ≤ t + 2^k` (dropping `z ≤ k`!), `(winWitt (t + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + Q))`! -/
theorem winWitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond (Q z t k r : Nat)
    (ht : t + Q < r) (hlt : (t + Q) + r < twopow k) (hdz : (t + Q) + r ≤ z)
    (hd : DoublesAt Q z)
    (hset : settle ((t + Q) + r) ≤ t + twopow k) :
    (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + Q)) := by
  have h := winWitt_scale_cross_periodic_of_doubles_le_uncond Q z t k r hlt hdz hd hset
  rw [rhCenter_gt_eq_false t (r + Q) (by omega),
    rhCenter_gt_eq_false (t + Q) r ht] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + Q)) <;>
    cases (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - r) <;> decide

theorem winWitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond_prop (Q z t k r : Nat)
    (ht : t + Q < r) (hlt : (t + Q) + r < twopow k) (hdz : (t + Q) + r ≤ z)
    (hd : DoublesAt Q z)
    (hset : SettledBy ((t + Q) + r) (t + twopow k)) :
    wittBitBool (winWitt (t + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + Q)) :=
  winWitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond Q z t k r ht hlt hdz hd hset

/-- **Unconditional Sector-2 Cross-Center `winWitt` `Q`-Antiperiodicity on the Doubling Diagonal `z + 1` Without `z + 1 ≤ k` (`winWitt_scale_cross_antiperiodic_of_doubles_uncond`, 9.870)**:
    for EVERY shift `Q` at once, and for all `t, k, r ∈ ℕ` with `((t + Q) + r) + 1 < 2^k`, `IsZeroDiag ((t + Q) + r)`, `DoublesAt Q ((t + Q) + r)`, and `settle (((t + Q) + r) + 1) ≤ t + 2^k` (dropping `((t + Q) + r) + 1 ≤ k`!), `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) ⊕ (winWitt (t + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - (r + 1)) = !(rhCenter t ((r + Q) + 1) ⊕ rhCenter (t + Q) (r + 1))`! -/
theorem winWitt_scale_cross_antiperiodic_of_doubles_uncond (Q t k r : Nat)
    (hlt : ((t + Q) + r) + 1 < twopow k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)))
      ((winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter t ((r + Q) + 1)) (rhCenter (t + Q) (r + 1))) := by
  rw [winWitt_testBit_scale_cross_cone t k ((r + Q) + 1) (by omega),
    winWitt_testBit_scale_cross_cone (t + Q) k (r + 1) (by omega),
    lhCenter_late_cross_antiperiodic_of_doubles_uncond Q t k r (by omega) hz hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) <;>
    cases rhCenter t ((r + Q) + 1) <;>
    cases rhCenter (t + Q) (r + 1) <;> decide

theorem winWitt_scale_cross_antiperiodic_of_doubles_uncond_prop (Q t k r : Nat)
    (hlt : ((t + Q) + r) + 1 < twopow k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)))
      (wittBitBool (winWitt (t + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter t ((r + Q) + 1)) (rhCenter (t + Q) (r + 1))) :=
  winWitt_scale_cross_antiperiodic_of_doubles_uncond Q t k r hlt hz hd hset

/-- **Unconditional Sector-2 Inter-Cone Zero-Gap `Q`-Antiperiodicity on the Doubling Diagonal `z + 1` Without `z + 1 ≤ k` (`winWitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond`, 9.871)**:
    for EVERY shift `Q` at once, and for all `t, k, r ∈ ℕ` with `t + Q ≤ r`, `((t + Q) + r) + 1 < 2^k`, `IsZeroDiag ((t + Q) + r)`, `DoublesAt Q ((t + Q) + r)`, and `settle (((t + Q) + r) + 1) ≤ t + 2^k` (dropping `((t + Q) + r) + 1 ≤ k`!), `(winWitt (t + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))`! -/
theorem winWitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond (Q t k r : Nat)
    (ht : t + Q ≤ r) (hlt : ((t + Q) + r) + 1 < twopow k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k) :
    (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  have h := winWitt_scale_cross_antiperiodic_of_doubles_uncond Q t k r hlt hz hd hset
  rw [rhCenter_gt_eq_false t ((r + Q) + 1) (by omega),
    rhCenter_gt_eq_false (t + Q) (r + 1) (by omega)] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) <;>
    cases (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond_prop (Q t k r : Nat)
    (ht : t + Q ≤ r) (hlt : ((t + Q) + r) + 1 < twopow k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k)) :
    wittBitBool (winWitt (t + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - (r + 1)) =
      !wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) :=
  winWitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond Q t k r ht hlt hz hd hset

/-- **Scale-Free Real-Orbit Post-Zero Blackness Directly at Row `t` (`lhCenter_at_t_after_zero_diag`, 9.872)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 2))` and `settle ((t - (p + 2)) + 2) ≤ t` (no `p ≤ t` bound, no `t + 2` offset, and no scale `k`!), `lhCenter t p = true`! -/
theorem lhCenter_at_t_after_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - (p + 2)))
    (hset : settle ((t - (p + 2)) + 2) ≤ t) :
    lhCenter t p = true := by
  have hz_ge := zero_diag_ge_two (t - (p + 2)) hz
  rw [lhCenter_eq_ldiag t p (by omega),
    show t - p = (t - (p + 2)) + 2 by omega]
  exact ldiag_after_zero_diag (t - (p + 2)) t hz hset

theorem lhCenter_at_t_after_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - (p + 2)))
    (hset : SettledBy ((t - (p + 2)) + 2) t) :
    lhCenter t p = true :=
  lhCenter_at_t_after_zero_diag t p hz hset

/-- **Scale-Free Real-Orbit 1-Step Post-Black Reset Complementation Directly from Row `t` (`lhCenter_step_one_reset_after_zero_diag`, 9.873)**:
    for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 3))` and `settle ((t - (p + 3)) + 2) ≤ t` (no `p ≤ t` bound, no `t + 2` offset, no settling on `z + 1` or `z + 3`, and no scale `k`!), `lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2)`! -/
theorem lhCenter_step_one_reset_after_zero_diag (t p : Nat)
    (hz : IsZeroDiag (t - (p + 3)))
    (hset : settle ((t - (p + 3)) + 2) ≤ t) :
    lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2) := by
  have hb := lhCenter_at_t_after_zero_diag t (p + 1)
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
  have hstep := lhCenter_step_succ t p
  rw [hb, Bool.true_or] at hstep
  rw [hstep]
  cases lhCenter t (p + 2) <;> rfl

theorem lhCenter_step_one_reset_after_zero_diag_prop (t p : Nat)
    (hz : IsZeroDiag (t - (p + 3)))
    (hset : SettledBy ((t - (p + 3)) + 2) t) :
    lhCenter (t + 1) (p + 1) = !lhCenter t (p + 2) :=
  lhCenter_step_one_reset_after_zero_diag t p hz hset

/-- **Scale-Free Universal-in-`Q` Diagonal-Shift Antiperiodicity Directly at Row `t` Without `p ≤ t` (`lhCenter_diag_shift_antiperiodic_at_t_of_doubles`, 9.874)**:
    for EVERY shift `Q` at once, and for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt Q (t - (p + 1))`, and `settle ((t - (p + 1)) + 1) ≤ t` (no `p ≤ t` bound and no scale `k`!), `lhCenter (t + Q) (p + Q) = !lhCenter t p`! -/
theorem lhCenter_diag_shift_antiperiodic_at_t_of_doubles (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset : settle ((t - (p + 1)) + 1) ≤ t) :
    lhCenter (t + Q) (p + Q) = !lhCenter t p := by
  have hz_ge := zero_diag_ge_two (t - (p + 1)) hz
  rw [lhCenter_eq_ldiag (t + Q) (p + Q) (by omega),
    lhCenter_eq_ldiag t p (by omega),
    show (t + Q) - (p + Q) = (t - (p + 1)) + 1 by omega,
    show t - p = (t - (p + 1)) + 1 by omega]
  exact ldiag_settled_antiperiodic_of_doubles Q (t - (p + 1)) t hz hd hset

theorem lhCenter_diag_shift_antiperiodic_at_t_of_doubles_prop (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset : SettledBy ((t - (p + 1)) + 1) t) :
    lhCenter (t + Q) (p + Q) = !lhCenter t p :=
  lhCenter_diag_shift_antiperiodic_at_t_of_doubles Q t p hz hd hset

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Spatial `Q`-Flip on `z + 1` Directly at Row `t` (`lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree`, 9.875)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt Q (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `p0 ≤ p + Q`, and `p + Q ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (no `p ≤ t` bound, no `LhBandAgree (t + 1)`, and no scale `k`!), then `lhCenter t (p + Q) = !lhCenter t p`! -/
theorem lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset : settle ((t - (p + 1)) + 1) ≤ t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + Q) = !lhCenter t p := by
  have hb := hband ((p + Q) - p0) (by omega)
  rw [show p0 + ((p + Q) - p0) = p + Q by omega] at hb
  rw [← hb]
  exact lhCenter_diag_shift_antiperiodic_at_t_of_doubles Q t p hz hd hset

theorem lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset : SettledBy ((t - (p + 1)) + 1) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + Q) = !lhCenter t p :=
  lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree Q t p p0 L hz hd hset hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Space-Time Equivalence of `(t, (p + 2) + Q)` and `(t + 1, p + 1)` (`lhCenter_spatial_doubles_eq_step_one_reset_of_lhBandAgree`, 9.876)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 3))`, `DoublesAt Q (t - (p + 3))`, `settle ((t - (p + 3)) + 1) ≤ t`, `settle ((t - (p + 3)) + 2) ≤ t`, `p0 ≤ (p + 2) + Q`, and `(p + 2) + Q ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (no `LhBandAgree (t + 1)`, no `settle (z + 3)`, no scale `k`, and no `winWitt`!), then `lhCenter t ((p + 2) + Q) = lhCenter (t + 1) (p + 1)`! -/
theorem lhCenter_spatial_doubles_eq_step_one_reset_of_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t)
    (hp0 : p0 ≤ (p + 2) + Q) (hL : (p + 2) + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t ((p + 2) + Q) = lhCenter (t + 1) (p + 1) := by
  rw [lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree Q t (p + 2) p0 L
      (by rwa [show (p + 2) + 1 = p + 3 by omega])
      (by rwa [show (p + 2) + 1 = p + 3 by omega])
      (by rwa [show (p + 2) + 1 = p + 3 by omega]) hp0 hL hband,
    lhCenter_step_one_reset_after_zero_diag t p hz hset2]

theorem lhCenter_spatial_doubles_eq_step_one_reset_of_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ (p + 2) + Q) (hL : (p + 2) + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t ((p + 2) + Q) = lhCenter (t + 1) (p + 1) :=
  lhCenter_spatial_doubles_eq_step_one_reset_of_lhBandAgree Q t p p0 L hz hd hset1 hset2 hp0 hL hband

/-! ### Batch 39: Scale-Free Real-Orbit Reset Antiperiodicity, Period-1 Doubling Refutation `not_lhBandAgree_one_of_doubles`, and Period-3 Doubling Refutation `not_lhBandAgree_three_of_doubles` (9.877–9.891) -/

/-- **Scale-Free Universal-in-`Q` Real-Orbit Space-Time Equivalence of `(t + Q, (p + 2) + Q)` on `z + 1` and `(t + 1, p + 1)` on `z + 3` (`lhCenter_doubles_eq_step_one_reset`, 9.877)**:
    for EVERY shift `Q` at once, and for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 3))`, `DoublesAt Q (t - (p + 3))`, `settle ((t - (p + 3)) + 1) ≤ t`, and `settle ((t - (p + 3)) + 2) ≤ t` (no `settle (z + 3)` and no scale `k`!), `lhCenter (t + Q) ((p + 2) + Q) = lhCenter (t + 1) (p + 1)`! -/
theorem lhCenter_doubles_eq_step_one_reset (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t) :
    lhCenter (t + Q) ((p + 2) + Q) = lhCenter (t + 1) (p + 1) := by
  rw [lhCenter_diag_shift_antiperiodic_at_t_of_doubles Q t (p + 2)
      (by rwa [show (p + 2) + 1 = p + 3 by omega])
      (by rwa [show (p + 2) + 1 = p + 3 by omega])
      (by rwa [show (p + 2) + 1 = p + 3 by omega]),
    lhCenter_step_one_reset_after_zero_diag t p hz hset2]

theorem lhCenter_doubles_eq_step_one_reset_prop (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t) :
    lhCenter (t + Q) ((p + 2) + Q) = lhCenter (t + 1) (p + 1) :=
  lhCenter_doubles_eq_step_one_reset Q t p hz hd hset1 hset2

/-- **Scale-Free Universal-in-`Q` Real-Orbit Antiperiodicity on the Post-Black Reset Diagonal `z + 3` Without `settle (z + 3)` (`lhCenter_step_one_reset_antiperiodic_of_doubles`, 9.878)**:
    for EVERY shift `Q` at once, and for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 3))`, `DoublesAt Q (t - (p + 3))`, `settle ((t - (p + 3)) + 1) ≤ t`, and `settle ((t - (p + 3)) + 2) ≤ t` (no `settle (z + 3)` and no scale `k`!), `lhCenter ((t + Q) + 1) ((p + Q) + 1) = !lhCenter (t + 1) (p + 1)`! -/
theorem lhCenter_step_one_reset_antiperiodic_of_doubles (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t) :
    lhCenter ((t + Q) + 1) ((p + Q) + 1) = !lhCenter (t + 1) (p + 1) := by
  have hrst := lhCenter_step_one_reset_after_zero_diag (t + Q) (p + Q)
    (by rwa [show (t + Q) - ((p + Q) + 3) = t - (p + 3) by omega])
    (by rw [show (t + Q) - ((p + Q) + 3) = t - (p + 3) by omega]; omega)
  rw [hrst, show (p + Q) + 2 = (p + 2) + Q by omega,
    lhCenter_doubles_eq_step_one_reset Q t p hz hd hset1 hset2]

theorem lhCenter_step_one_reset_antiperiodic_of_doubles_prop (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t) :
    lhCenter ((t + Q) + 1) ((p + Q) + 1) = !lhCenter (t + 1) (p + 1) :=
  lhCenter_step_one_reset_antiperiodic_of_doubles Q t p hz hd hset1 hset2

/-- **Scale-Free Universal-in-`Q` Single-Time `LhBandAgree` Spatial `Q`-Flip on `z + 3` at Time `t + 1` Without `LhBandAgree (t + 1)` or `settle (z + 3)` (`lhCenter_step_one_reset_shift_flip_of_doubles_and_single_lhBandAgree`, 9.879)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 3))`, `DoublesAt Q (t - (p + 3))`, `settle ((t - (p + 3)) + 1) ≤ t`, `settle ((t - (p + 3)) + 2) ≤ t`, `p0 ≤ (p + 1) + Q`, and `(p + 2) + Q ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (no `LhBandAgree (t + 1)`, no `settle (z + 3)`, no scale `k`, and no `winWitt`!), then `lhCenter (t + 1) ((p + 1) + Q) = !lhCenter (t + 1) (p + 1)`! -/
theorem lhCenter_step_one_reset_shift_flip_of_doubles_and_single_lhBandAgree (Q t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t)
    (hp0 : p0 ≤ (p + 1) + Q) (hL : (p + 2) + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) ((p + 1) + Q) = !lhCenter (t + 1) (p + 1) := by
  have hfl := lhCenter_step_flip_at_shift_after_zero_diag_of_single_lhBandAgree Q t (p + Q) p0 L
    (by rwa [show (t + Q) - ((p + Q) + 3) = t - (p + 3) by omega])
    (by rw [show (t + Q) - ((p + Q) + 3) = t - (p + 3) by omega]; omega)
    (by omega) (by omega) hband
  rw [show (p + Q) + 1 = (p + 1) + Q by omega,
    show (p + Q) + 2 = (p + 2) + Q by omega,
    lhCenter_spatial_doubles_eq_step_one_reset_of_lhBandAgree Q t p p0 L hz hd hset1 hset2 (by omega) hL hband] at hfl
  exact hfl

theorem lhCenter_step_one_reset_shift_flip_of_doubles_and_single_lhBandAgree_prop (Q t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt Q (t - (p + 3)))
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ (p + 1) + Q) (hL : (p + 2) + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) ((p + 1) + Q) = !lhCenter (t + 1) (p + 1) :=
  lhCenter_step_one_reset_shift_flip_of_doubles_and_single_lhBandAgree Q t p p0 L hz hd hset1 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Period-1 Doubling Pinning `lhCenter t (p + 1) = true` on `z + 1` from a Single-Cell `LhBandAgree t 1 p0 L` (`lhCenter_pin_doubling_diag_true_of_doubles_one_and_lhBandAgree`, 9.880)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 2))`, `DoublesAt 1 (t - (p + 2))`, `settle (t - (p + 2)) ≤ t`, `settle ((t - (p + 2)) + 1) ≤ t`, `p0 ≤ p + 2`, and `p + 2 ≤ p0 + L`, if `LhBandAgree t 1 p0 L` holds at time `t` alone (no `LhBandAgree (t + 1)` and no scale `k`!), then `lhCenter t (p + 1) = true`! -/
theorem lhCenter_pin_doubling_diag_true_of_doubles_one_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 2))) (hd : DoublesAt 1 (t - (p + 2)))
    (hset0 : settle (t - (p + 2)) ≤ t)
    (hset1 : settle ((t - (p + 2)) + 1) ≤ t)
    (hp0 : p0 ≤ p + 2) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t 1 p0 L) :
    lhCenter t (p + 1) = true := by
  have hfl := lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree 1 t (p + 1) p0 L
    (by rwa [show (p + 1) + 1 = p + 2 by omega])
    (by rwa [show (p + 1) + 1 = p + 2 by omega])
    (by rwa [show (p + 1) + 1 = p + 2 by omega])
    (by omega) (by omega) hband
  have hz0 := lhCenter_of_zero_diag t (p + 2) hz hset0
  rw [show (p + 1) + 1 = p + 2 by omega, hz0] at hfl
  cases h : lhCenter t (p + 1)
  · rw [h] at hfl; cases hfl
  · rfl

theorem lhCenter_pin_doubling_diag_true_of_doubles_one_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 2))) (hd : DoublesAt 1 (t - (p + 2)))
    (hset0 : SettledBy (t - (p + 2)) t)
    (hset1 : SettledBy ((t - (p + 2)) + 1) t)
    (hp0 : p0 ≤ p + 2) (hL : p + 2 ≤ p0 + L)
    (hband : LhBandAgree t 1 p0 L) :
    lhCenter t (p + 1) = true :=
  lhCenter_pin_doubling_diag_true_of_doubles_one_and_lhBandAgree t p p0 L hz hd hset0 hset1 hp0 hL hband

/-- **Scale-Free Real-Orbit Period-1 Doubling Post-Black Reset Pinning `lhCenter (t + 1) (p + 1) = false` on `z + 3` Without `LhBandAgree (t + 1)` or `settle (z + 3)` (`lhCenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhBandAgree`, 9.881)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 3))`, `DoublesAt 1 (t - (p + 3))`, `settle (t - (p + 3)) ≤ t`, `settle ((t - (p + 3)) + 1) ≤ t`, `settle ((t - (p + 3)) + 2) ≤ t`, `p0 ≤ p + 3`, and `p + 3 ≤ p0 + L`, if `LhBandAgree t 1 p0 L` holds at time `t` alone, then `lhCenter (t + 1) (p + 1) = false`! -/
theorem lhCenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt 1 (t - (p + 3)))
    (hset0 : settle (t - (p + 3)) ≤ t)
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t)
    (hp0 : p0 ≤ p + 3) (hL : p + 3 ≤ p0 + L)
    (hband : LhBandAgree t 1 p0 L) :
    lhCenter (t + 1) (p + 1) = false := by
  have htr := lhCenter_pin_doubling_diag_true_of_doubles_one_and_lhBandAgree t (p + 1) p0 L
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by omega) (by omega) hband
  rw [lhCenter_step_one_reset_after_zero_diag t p hz hset2,
    show p + 2 = (p + 1) + 1 by omega, htr]
  rfl

theorem lhCenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt 1 (t - (p + 3)))
    (hset0 : SettledBy (t - (p + 3)) t)
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ p + 3) (hL : p + 3 ≤ p0 + L)
    (hband : LhBandAgree t 1 p0 L) :
    lhCenter (t + 1) (p + 1) = false :=
  lhCenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhBandAgree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Single-Time Refutation `¬ LhBandAgree t 1 p0 L` at Any Period-1 Doubling Zero Diagonal `z = t - (p + 3)` Without `LhBandAgree (t + 1)`, `settle (z + 3)`, or Scale `k` (`not_lhBandAgree_one_of_doubles`, 9.882)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 3))`, `DoublesAt 1 (t - (p + 3))`, `settle (t - (p + 3)) ≤ t`, `settle ((t - (p + 3)) + 1) ≤ t`, `settle ((t - (p + 3)) + 2) ≤ t`, `p0 ≤ p + 1`, and `p + 3 ≤ p0 + L`, `¬ LhBandAgree t 1 p0 L`! -/
theorem not_lhBandAgree_one_of_doubles (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt 1 (t - (p + 3)))
    (hset0 : settle (t - (p + 3)) ≤ t)
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t)
    (hp0 : p0 ≤ p + 1) (hL : p + 3 ≤ p0 + L) :
    ¬ LhBandAgree t 1 p0 L := by
  intro hband
  have hf := lhCenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhBandAgree
    t p p0 L hz hd hset0 hset1 hset2 (by omega) hL hband
  have ht := lhCenter_at_t_after_zero_diag t (p + 1)
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
  have heq := hband ((p + 1) - p0) (by omega)
  rw [show p0 + ((p + 1) - p0) = p + 1 by omega, hf, ht] at heq
  cases heq

theorem not_lhBandAgree_one_of_doubles_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt 1 (t - (p + 3)))
    (hset0 : SettledBy (t - (p + 3)) t)
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ p + 1) (hL : p + 3 ≤ p0 + L) :
    ¬ LhBandAgree t 1 p0 L :=
  not_lhBandAgree_one_of_doubles t p p0 L hz hd hset0 hset1 hset2 hp0 hL

/-- **Scale-Free Real-Orbit Refutation of `RhColAgree t 1 1 S` Under `CenterPeriodic T 1` at Any Period-1 Doubling Zero Diagonal `z = t - (p + 3)` (`not_periodic_rhColAgree_one_of_doubles_one`, 9.883)**:
    under `CenterPeriodic T 1`, for all `t, p, S ∈ ℕ` with `T ≤ t`, `IsZeroDiag (t - (p + 3))`, `DoublesAt 1 (t - (p + 3))`, `settle (t - (p + 3)) ≤ t`, `settle ((t - (p + 3)) + 1) ≤ t`, `settle ((t - (p + 3)) + 2) ≤ t`, and `p + 2 ≤ S`, `¬ RhColAgree t 1 1 S`! -/
theorem not_periodic_rhColAgree_one_of_doubles_one
    (T : Nat) (hper : Rule30UOR.Scale.CenterPeriodic T 1)
    (t p S : Nat) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt 1 (t - (p + 3)))
    (hset0 : settle (t - (p + 3)) ≤ t)
    (hset1 : settle ((t - (p + 3)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 3)) + 2) ≤ t)
    (hS : p + 2 ≤ S) :
    ¬ RhColAgree t 1 1 S := by
  intro hrh
  have hband := periodic_lhBandAgree_zero_of_rhColAgree_one T 1 (by omega) hper 1 t S ht
    (by rwa [Nat.mul_one])
  rw [Nat.mul_one] at hband
  exact not_lhBandAgree_one_of_doubles t p 0 (S + 1) hz hd hset0 hset1 hset2 (by omega) (by omega) hband

theorem not_periodic_rhColAgree_one_of_doubles_one_prop
    (T : Nat) (hper : Rule30UOR.Scale.CenterPeriodic T 1)
    (t p S : Nat) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 3))) (hd : DoublesAt 1 (t - (p + 3)))
    (hset0 : SettledBy (t - (p + 3)) t)
    (hset1 : SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : SettledBy ((t - (p + 3)) + 2) t)
    (hS : p + 2 ≤ S) :
    ¬ RhColAgree t 1 1 S :=
  not_periodic_rhColAgree_one_of_doubles_one T hper t p S ht hz hd hset0 hset1 hset2 hS

/-- **Scale-Free Universal-in-`Q` Single-Cell `LhBandAgree` Twin-Propagated Pinning `lhCenter t (p + 2) = true` (`lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three`, 9.884)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - p)`, `IsZeroDiag ((t + Q) - (p + 3))`, `settle (t - p) ≤ t`, `settle (((t + Q) - (p + 3)) + 2) ≤ t + Q`, `p0 ≤ p + 1`, and `p + 1 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (requiring `LhBandAgree` only at the single cell `p + 1`!), then `lhCenter t (p + 2) = true`! -/
theorem lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three (Q t p p0 L : Nat)
    (hz0 : IsZeroDiag (t - p))
    (hzQ : IsZeroDiag ((t + Q) - (p + 3)))
    (hset0 : settle (t - p) ≤ t)
    (hsetQ : settle (((t + Q) - (p + 3)) + 2) ≤ t + Q)
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + 2) = true := by
  rw [lhCenter_twin_before_zero_diag t p hz0 hset0]
  exact lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree Q t (p + 1) p0 L
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    hp0 hL hband

theorem lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three_prop (Q t p p0 L : Nat)
    (hz0 : IsZeroDiag (t - p))
    (hzQ : IsZeroDiag ((t + Q) - (p + 3)))
    (hset0 : SettledBy (t - p) t)
    (hsetQ : SettledBy (((t + Q) - (p + 3)) + 2) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter t (p + 2) = true :=
  lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three Q t p p0 L hz0 hzQ hset0 hsetQ hp0 hL hband

/-- **Scale-Free Universal-in-`Q` Single-Cell `LhBandAgree` 1-Step Pinning `lhCenter (t + 1) (p + 1) = false` (`lhCenter_step_one_pin_plus_one_false_of_lhBandAgree_and_zero_diag_three`, 9.885)**:
    for EVERY shift `Q` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - p)`, `IsZeroDiag ((t + Q) - (p + 3))`, `settle (t - p) ≤ t`, `settle (((t + Q) - (p + 3)) + 2) ≤ t + Q`, `p0 ≤ p + 1`, and `p + 1 ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone (requiring `LhBandAgree` only at the single cell `p + 1`!), then `lhCenter (t + 1) (p + 1) = false`! -/
theorem lhCenter_step_one_pin_plus_one_false_of_lhBandAgree_and_zero_diag_three (Q t p p0 L : Nat)
    (hz0 : IsZeroDiag (t - p))
    (hzQ : IsZeroDiag ((t + Q) - (p + 3)))
    (hset0 : settle (t - p) ≤ t)
    (hsetQ : settle (((t + Q) - (p + 3)) + 2) ≤ t + Q)
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = false := by
  have h1 := lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree Q t (p + 1) p0 L
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    (by rwa [show (p + 1) + 2 = p + 3 by omega])
    hp0 hL hband
  have h2 := lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three
    Q t p p0 L hz0 hzQ hset0 hsetQ hp0 hL hband
  rw [lhCenter_step_succ t p, h1, h2, Bool.true_or]
  rfl

theorem lhCenter_step_one_pin_plus_one_false_of_lhBandAgree_and_zero_diag_three_prop (Q t p p0 L : Nat)
    (hz0 : IsZeroDiag (t - p))
    (hzQ : IsZeroDiag ((t + Q) - (p + 3)))
    (hset0 : SettledBy (t - p) t)
    (hsetQ : SettledBy (((t + Q) - (p + 3)) + 2) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + 1) (p + 1) = false :=
  lhCenter_step_one_pin_plus_one_false_of_lhBandAgree_and_zero_diag_three Q t p p0 L hz0 hzQ hset0 hsetQ hp0 hL hband

/-- **Scale-Free Real-Orbit Period-3 Single-Cell `LhBandAgree` Twin-Propagated Pinning `lhCenter t (p + 2) = true` Before Any Zero Diagonal `z = t - p` (`lhCenter_pin_before_zero_diag_of_zero_diag_three_and_lhBandAgree`, 9.886)**:
    when `Q = 3`, `(t + 3) - (p + 3) = t - p` is the zero diagonal itself, so `LhBandAgree t 3 p0 L` at the single cell `p + 1` pins `lhCenter t (p + 2) = true` with no `DoublesAt` and no scale `k`! -/
theorem lhCenter_pin_before_zero_diag_of_zero_diag_three_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - p))
    (hset0 : settle (t - p) ≤ t)
    (hset2 : settle ((t - p) + 2) ≤ t + 3)
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter t (p + 2) = true :=
  lhCenter_pin_plus_two_true_of_lhBandAgree_and_zero_diag_three 3 t p p0 L hz
    (by rwa [show (t + 3) - (p + 3) = t - p by omega])
    hset0
    (by rwa [show (t + 3) - (p + 3) = t - p by omega])
    hp0 hL hband

theorem lhCenter_pin_before_zero_diag_of_zero_diag_three_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - p))
    (hset0 : SettledBy (t - p) t)
    (hset2 : SettledBy ((t - p) + 2) (t + 3))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter t (p + 2) = true :=
  lhCenter_pin_before_zero_diag_of_zero_diag_three_and_lhBandAgree t p p0 L hz hset0 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Period-3 Doubling Pinning `lhCenter t p = false` on `z + 1` from a Single `LhBandAgree t 3 p0 L` (`lhCenter_pin_doubling_diag_false_of_doubles_three_and_lhBandAgree`, 9.887)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt 3 (t - (p + 1))`, `settle (t - (p + 1)) ≤ t`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle ((t - (p + 1)) + 2) ≤ t + 3`, `p0 ≤ p + 2`, and `p + 3 ≤ p0 + L`, if `LhBandAgree t 3 p0 L` holds at time `t` alone, then `lhCenter t p = false`! -/
theorem lhCenter_pin_doubling_diag_false_of_doubles_three_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : settle (t - (p + 1)) ≤ t)
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 1)) + 2) ≤ t + 3)
    (hp0 : p0 ≤ p + 2) (hL : p + 3 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter t p = false := by
  have htr := lhCenter_pin_before_zero_diag_of_zero_diag_three_and_lhBandAgree
    t (p + 1) p0 L hz hset0 hset2 hp0 (by omega) hband
  have hfl := lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree
    3 t p p0 L hz hd hset1 (by omega) hL hband
  rw [show (p + 1) + 2 = p + 3 by omega] at htr
  rw [htr] at hfl
  cases h : lhCenter t p
  · rfl
  · rw [h] at hfl; cases hfl

theorem lhCenter_pin_doubling_diag_false_of_doubles_three_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : SettledBy (t - (p + 1)) t)
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : SettledBy ((t - (p + 1)) + 2) (t + 3))
    (hp0 : p0 ≤ p + 2) (hL : p + 3 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter t p = false :=
  lhCenter_pin_doubling_diag_false_of_doubles_three_and_lhBandAgree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Period-3 Doubling 1-Step Pinning `lhCenter (t + 1) (p + 1) = true` on `z + 1` Without `LhBandAgree (t + 1)` (`lhCenter_step_one_pin_plus_one_true_of_doubles_three_and_lhBandAgree`, 9.888)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt 3 (t - (p + 1))`, `settle (t - (p + 1)) ≤ t`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle ((t - (p + 1)) + 2) ≤ t + 3`, `p0 ≤ p + 2`, and `p + 3 ≤ p0 + L`, if `LhBandAgree t 3 p0 L` holds at time `t` alone, then `lhCenter (t + 1) (p + 1) = true`! -/
theorem lhCenter_step_one_pin_plus_one_true_of_doubles_three_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : settle (t - (p + 1)) ≤ t)
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 1)) + 2) ≤ t + 3)
    (hp0 : p0 ≤ p + 2) (hL : p + 3 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter (t + 1) (p + 1) = true := by
  have hx0 := lhCenter_pin_doubling_diag_false_of_doubles_three_and_lhBandAgree
    t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband
  have hx1 := lhCenter_of_zero_diag t (p + 1) hz hset0
  have hx2 := lhCenter_eq_true_at_shift_after_zero_diag_and_lhBandAgree 3 t (p + 2) p0 L
    (by rwa [show (t + 3) - ((p + 2) + 2) = t - (p + 1) by omega])
    (by rwa [show (t + 3) - ((p + 2) + 2) = t - (p + 1) by omega])
    hp0 (by omega) hband
  rw [lhCenter_step_succ t p, hx0, hx1, hx2]
  rfl

theorem lhCenter_step_one_pin_plus_one_true_of_doubles_three_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : SettledBy (t - (p + 1)) t)
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : SettledBy ((t - (p + 1)) + 2) (t + 3))
    (hp0 : p0 ≤ p + 2) (hL : p + 3 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter (t + 1) (p + 1) = true :=
  lhCenter_step_one_pin_plus_one_true_of_doubles_three_and_lhBandAgree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Period-3 Doubling 2-Step Pinning `lhCenter (t + 2) (p + 2) = false` on `z + 1` Without `LhBandAgree (t + 1..2)` (`lhCenter_step_two_pin_plus_two_false_of_doubles_three_and_lhBandAgree`, 9.889)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt 3 (t - (p + 1))`, `settle (t - (p + 1)) ≤ t`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle ((t - (p + 1)) + 2) ≤ t + 3`, `p0 ≤ p + 2`, and `p + 4 ≤ p0 + L`, if `LhBandAgree t 3 p0 L` holds at time `t` alone, then `lhCenter (t + 2) (p + 2) = false`! -/
theorem lhCenter_step_two_pin_plus_two_false_of_doubles_three_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : settle (t - (p + 1)) ≤ t)
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 1)) + 2) ≤ t + 3)
    (hp0 : p0 ≤ p + 2) (hL : p + 4 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter (t + 2) (p + 2) = false := by
  have hy1 := lhCenter_step_one_pin_plus_one_true_of_doubles_three_and_lhBandAgree
    t p p0 L hz hd hset0 hset1 hset2 hp0 (by omega) hband
  have hy3 := lhCenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhBandAgree
    3 t (p + 2) p0 L
    (by rwa [show (t + 3) - ((p + 2) + 2) = t - (p + 1) by omega])
    (by rw [show (t + 3) - ((p + 2) + 2) = t - (p + 1) by omega]; omega)
    (by rwa [show (t + 3) - ((p + 2) + 2) = t - (p + 1) by omega])
    hp0 hL hband
  have hstep := lhCenter_step_succ (t + 1) (p + 1)
  rw [show (t + 1) + 1 = t + 2 by omega,
    show (p + 1) + 1 = p + 2 by omega,
    show (p + 1) + 2 = p + 3 by omega,
    hy1, hy3, Bool.or_true] at hstep
  exact hstep

theorem lhCenter_step_two_pin_plus_two_false_of_doubles_three_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : SettledBy (t - (p + 1)) t)
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : SettledBy ((t - (p + 1)) + 2) (t + 3))
    (hp0 : p0 ≤ p + 2) (hL : p + 4 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter (t + 2) (p + 2) = false :=
  lhCenter_step_two_pin_plus_two_false_of_doubles_three_and_lhBandAgree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Period-3 Doubling 3-Step Pinning `lhCenter (t + 3) (p + 1) = true` on `z + 3` Without `LhBandAgree (t + 1..2)` or `settle (z + 3)` (`lhCenter_step_three_pin_plus_one_true_of_doubles_three_and_lhBandAgree`, 9.890)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt 3 (t - (p + 1))`, `settle (t - (p + 1)) ≤ t`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle ((t - (p + 1)) + 2) ≤ t + 2`, `p0 ≤ p + 2`, and `p + 4 ≤ p0 + L`, if `LhBandAgree t 3 p0 L` holds at time `t` alone, then `lhCenter (t + 3) (p + 1) = true`! -/
theorem lhCenter_step_three_pin_plus_one_true_of_doubles_three_and_lhBandAgree (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : settle (t - (p + 1)) ≤ t)
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 1)) + 2) ≤ t + 2)
    (hp0 : p0 ≤ p + 2) (hL : p + 4 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter (t + 3) (p + 1) = true := by
  rw [lhCenter_reset_after_zero_diag t p hz hset2,
    lhCenter_step_two_pin_plus_two_false_of_doubles_three_and_lhBandAgree
      t p p0 L hz hd hset0 hset1 (by omega) hp0 hL hband]
  rfl

theorem lhCenter_step_three_pin_plus_one_true_of_doubles_three_and_lhBandAgree_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : SettledBy (t - (p + 1)) t)
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : SettledBy ((t - (p + 1)) + 2) (t + 2))
    (hp0 : p0 ≤ p + 2) (hL : p + 4 ≤ p0 + L)
    (hband : LhBandAgree t 3 p0 L) :
    lhCenter (t + 3) (p + 1) = true :=
  lhCenter_step_three_pin_plus_one_true_of_doubles_three_and_lhBandAgree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-Free Real-Orbit Single-Time Refutation `¬ LhBandAgree t 3 p0 L` at Any Period-3 Doubling Zero Diagonal `z = t - (p + 1)` Without `LhBandAgree (t + 1..2)`, `settle (z + 3)`, or Scale `k` (`not_lhBandAgree_three_of_doubles`, 9.891)**:
    for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt 3 (t - (p + 1))`, `settle (t - (p + 1)) ≤ t`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle ((t - (p + 1)) + 2) ≤ t + 2`, `p0 ≤ p + 1`, and `p + 4 ≤ p0 + L`, `¬ LhBandAgree t 3 p0 L`! -/
theorem not_lhBandAgree_three_of_doubles (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : settle (t - (p + 1)) ≤ t)
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hset2 : settle ((t - (p + 1)) + 2) ≤ t + 2)
    (hp0 : p0 ≤ p + 1) (hL : p + 4 ≤ p0 + L) :
    ¬ LhBandAgree t 3 p0 L := by
  intro hband
  have ht := lhCenter_step_three_pin_plus_one_true_of_doubles_three_and_lhBandAgree
    t p p0 L hz hd hset0 hset1 hset2 (by omega) hL hband
  have hf := lhCenter_of_zero_diag t (p + 1) hz hset0
  have heq := hband ((p + 1) - p0) (by omega)
  rw [show p0 + ((p + 1) - p0) = p + 1 by omega, ht, hf] at heq
  cases heq

theorem not_lhBandAgree_three_of_doubles_prop (t p p0 L : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt 3 (t - (p + 1)))
    (hset0 : SettledBy (t - (p + 1)) t)
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : SettledBy ((t - (p + 1)) + 2) (t + 2))
    (hp0 : p0 ≤ p + 1) (hL : p + 4 ≤ p0 + L) :
    ¬ LhBandAgree t 3 p0 L :=
  not_lhBandAgree_three_of_doubles t p p0 L hz hd hset0 hset1 hset2 hp0 hL

/-! ### Batch 40: The Zero-Diagonal Period-Doubling Laws, Unbounded Dyadic Doubling Points, and Universal-in-`Q` Zero-Diagonal Doubling Contradiction Shrinking the Horizon by `z` (9.892–9.906) -/

/-- **Scale-Free Dyadic `2^d`-Periodicity of Every Settled Left Diagonal (`ldiag_settled_twopow_periodic`, 9.892)**:
    every settled left diagonal `d` has power-of-two period `2^d` (`twopow d`): for all `d, t ∈ ℕ` with `settle d ≤ t`, `ldiag d (t + twopow d) = ldiag d t`! -/
theorem ldiag_settled_twopow_periodic (d t : Nat)
    (hset : settle d ≤ t) :
    ldiag d (t + twopow d) = ldiag d t := by
  have hset1 : settle d ≤ t + twopow d := by omega
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Kit.ldiag_eq_D,
    ← Rule30UOR.Intent.E_eq_D d (t + twopow d) hset1,
    ← Rule30UOR.Intent.E_eq_D d t hset,
    twopow_eq_pow d]
  exact Rule30UOR.ZeroDiagonals.E_per d t

theorem ldiag_settled_twopow_periodic_prop (d t : Nat)
    (hset : SettledBy d t) :
    ldiag d (t + twopow d) = ldiag d t :=
  ldiag_settled_twopow_periodic d t hset

/-- **Scale-Free Common Power-of-Two `2^e`-Periodicity of All Settled Left Diagonals `d ≤ e` (`ldiag_settled_twopow_periodic_le`, 9.893)**:
    for all `e, d, t ∈ ℕ` with `d ≤ e` and `settle d ≤ t`, `ldiag d (t + twopow e) = ldiag d t`! -/
theorem ldiag_settled_twopow_periodic_le (e d t : Nat)
    (hde : d ≤ e) (hset : settle d ≤ t) :
    ldiag d (t + twopow e) = ldiag d t := by
  have hset1 : settle d ≤ t + twopow e := by omega
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Kit.ldiag_eq_D,
    ← Rule30UOR.Intent.E_eq_D d (t + twopow e) hset1,
    ← Rule30UOR.Intent.E_eq_D d t hset,
    twopow_eq_pow e]
  have hpow : 2 ^ e = 2 ^ (e - d) * 2 ^ d := by
    rw [← Nat.pow_add, show e - d + d = e by omega]
  rw [hpow]
  exact Rule30UOR.ZeroDiagonals.E_per_mul d (2 ^ (e - d)) t

theorem ldiag_settled_twopow_periodic_le_prop (e d t : Nat)
    (hde : d ≤ e) (hset : SettledBy d t) :
    ldiag d (t + twopow e) = ldiag d t :=
  ldiag_settled_twopow_periodic_le e d t hde hset

/-- **Scale-Free Universal-in-`Q` Period-Doubling `Q + Q`-Periodicity on the Doubling Diagonal `z + 1` (`ldiag_settled_two_mul_periodic_of_doubles`, 9.894)**:
    at any doubling zero diagonal `z` (`IsZeroDiag z` and `DoublesAt Q z`), diagonal `z + 1` flips at half-period `Q` (`9.824`) and repeats at the doubled period `Q + Q`: for all `Q, z, t ∈ ℕ` with `settle (z + 1) ≤ t`, `ldiag (z + 1) (t + (Q + Q)) = ldiag (z + 1) t`! -/
theorem ldiag_settled_two_mul_periodic_of_doubles (Q z t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : settle (z + 1) ≤ t) :
    ldiag (z + 1) (t + (Q + Q)) = ldiag (z + 1) t := by
  rw [show t + (Q + Q) = (t + Q) + Q by omega,
    ldiag_settled_antiperiodic_of_doubles Q z (t + Q) hz hd (by omega),
    ldiag_settled_antiperiodic_of_doubles Q z t hz hd hset,
    Bool.not_not]

theorem ldiag_settled_two_mul_periodic_of_doubles_prop (Q z t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : SettledBy (z + 1) t) :
    ldiag (z + 1) (t + (Q + Q)) = ldiag (z + 1) t :=
  ldiag_settled_two_mul_periodic_of_doubles Q z t hz hd hset

/-- **Scale-Free Universal-in-`Q` Settled `ldiag` Antiperiodicity on the Post-Black Reset Diagonal `z + 3` (`ldiag_settled_reset_antiperiodic_of_doubles`, 9.895)**:
    for EVERY shift `Q` and doubling zero diagonal `z` (`IsZeroDiag z` and `DoublesAt Q z`), and for all `t ∈ ℕ` with `settle (z + 3) ≤ t`, `ldiag (z + 3) (t + Q) = !ldiag (z + 3) t`! -/
theorem ldiag_settled_reset_antiperiodic_of_doubles (Q z t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : settle (z + 3) ≤ t) :
    ldiag (z + 3) (t + Q) = !ldiag (z + 3) t := by
  have hsetQ : settle (z + 3) ≤ t + Q := by omega
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Kit.ldiag_eq_D,
    ← Rule30UOR.Intent.E_eq_D (z + 3) (t + Q) hsetQ,
    ← Rule30UOR.Intent.E_eq_D (z + 3) t hset]
  have hpos : 1 ≤ 2 ^ (z + 3) := Nat.two_pow_pos (z + 3)
  let s := t + 2 ^ (z + 3) - 1
  have hs : s + 1 = t + 2 ^ (z + 3) := by omega
  have hsQ : (s + Q) + 1 = (t + Q) + 2 ^ (z + 3) := by omega
  rw [← Rule30UOR.ZeroDiagonals.E_per (z + 3) (t + Q),
    ← Rule30UOR.ZeroDiagonals.E_per (z + 3) t,
    ← hsQ, ← hs,
    Rule30UOR.CompilePoints.reset_three_after_zero z hz (s + Q),
    Rule30UOR.CompilePoints.reset_three_after_zero z hz s,
    antiperiodic_of_doubles Q z hz hd s]

theorem ldiag_settled_reset_antiperiodic_of_doubles_prop (Q z t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : SettledBy (z + 3) t) :
    ldiag (z + 3) (t + Q) = !ldiag (z + 3) t :=
  ldiag_settled_reset_antiperiodic_of_doubles Q z t hz hd hset

/-- **Scale-Free Universal-in-`Q` Common Doubled Period `Q + Q` Through `z + 3` at Any Doubling Zero Diagonal (`ldiag_settled_two_mul_periodic_le_add_three_of_doubles`, 9.896)**:
    at any doubling zero diagonal `z` (`IsZeroDiag z` and `DoublesAt Q z`), every settled left diagonal `d ≤ z + 3` repeats under the doubled shift `Q + Q`: for all `Q, z, d, t ∈ ℕ` with `d ≤ z + 3` and `settle d ≤ t`, `ldiag d (t + (Q + Q)) = ldiag d t`! -/
theorem ldiag_settled_two_mul_periodic_le_add_three_of_doubles (Q z d t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hdz : d ≤ z + 3) (hset : settle d ≤ t) :
    ldiag d (t + (Q + Q)) = ldiag d t := by
  by_cases hle : d ≤ z
  · rw [show t + (Q + Q) = (t + Q) + Q by omega,
      ldiag_settled_periodic_of_doubles_le Q z d (t + Q) hd hle (by omega),
      ldiag_settled_periodic_of_doubles_le Q z d t hd hle hset]
  · by_cases h1 : d = z + 1
    · subst h1
      exact ldiag_settled_two_mul_periodic_of_doubles Q z t hz hd hset
    · by_cases h2 : d = z + 2
      · subst h2
        rw [ldiag_after_zero_diag z (t + (Q + Q)) hz (by omega),
          ldiag_after_zero_diag z t hz hset]
      · have hd3 : d = z + 3 := by omega
        subst hd3
        rw [show t + (Q + Q) = (t + Q) + Q by omega,
          ldiag_settled_reset_antiperiodic_of_doubles Q z (t + Q) hz hd (by omega),
          ldiag_settled_reset_antiperiodic_of_doubles Q z t hz hd hset,
          Bool.not_not]

theorem ldiag_settled_two_mul_periodic_le_add_three_of_doubles_prop (Q z d t : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hdz : d ≤ z + 3) (hset : SettledBy d t) :
    ldiag d (t + (Q + Q)) = ldiag d t :=
  ldiag_settled_two_mul_periodic_le_add_three_of_doubles Q z d t hz hd hdz hset

/-- **Existence of a Zero-Diagonal Doubling Point for Every Power-of-Two Period `2^e` (`exists_zero_diag_doublesAt_twopow`, 9.897)**:
    for every dyadic exponent `e ∈ ℕ`, there exists a zero diagonal `z` such that `IsZeroDiag z` and `DoublesAt (twopow e) z`! -/
theorem exists_zero_diag_doublesAt_twopow (e : Nat) :
    ∃ z : Nat, IsZeroDiag z ∧ DoublesAt (twopow e) z :=
  Rule30UOR.CompilePoints.doubling_points (twopow e) (by rw [twopow_eq_pow]; exact Nat.two_pow_pos e)

/-- **Existence of a Zero-Diagonal Doubling Point for Every Period Multiple `m * P` (`exists_zero_diag_doublesAt_mul`, 9.898)**:
    for every positive multiplier `0 < m` and positive period `0 < P`, there exists a zero diagonal `z` such that `IsZeroDiag z` and `DoublesAt (m * P) z`! -/
theorem exists_zero_diag_doublesAt_mul (m P : Nat) (hm : 0 < m) (hP : 0 < P) :
    ∃ z : Nat, IsZeroDiag z ∧ DoublesAt (m * P) z :=
  Rule30UOR.CompilePoints.doubling_points (m * P) (Nat.mul_pos hm hP)

/-- **Dyadic Doubling Depth Lower Bound `e ≤ z` (`doublesAt_twopow_le`, 9.899)**:
    for all `e, z ∈ ℕ`, if `DoublesAt (twopow e) z` holds, then `e ≤ z` (since every diagonal `d ≤ e` has period dividing `2^e` by `E_per_mul`)! -/
theorem doublesAt_twopow_le (e z : Nat)
    (hd : DoublesAt (twopow e) z) :
    e ≤ z := by
  by_cases h : e ≤ z
  · exact h
  · exfalso
    apply hd.2
    intro t
    rw [twopow_eq_pow e]
    have hpow : 2 ^ e = 2 ^ (e - (z + 1)) * 2 ^ (z + 1) := by
      rw [← Nat.pow_add, show e - (z + 1) + (z + 1) = e by omega]
    rw [hpow]
    exact Rule30UOR.ZeroDiagonals.E_per_mul (z + 1) (2 ^ (e - (z + 1))) t

/-- **Unbounded Depth of Dyadic Doubling Zero Diagonals (`exists_zero_diag_doublesAt_twopow_ge`, 9.900)**:
    for every dyadic exponent `e ∈ ℕ`, there exists a zero diagonal `z` at depth `e ≤ z` such that `IsZeroDiag z` and `DoublesAt (twopow e) z`! -/
theorem exists_zero_diag_doublesAt_twopow_ge (e : Nat) :
    ∃ z : Nat, e ≤ z ∧ IsZeroDiag z ∧ DoublesAt (twopow e) z := by
  obtain ⟨z, hz, hd⟩ := exists_zero_diag_doublesAt_twopow e
  exact ⟨z, doublesAt_twopow_le e z hd, hz, hd⟩

/-- **Scale-Free Universal-in-`Q` 2-Shift Diagonal Periodicity on the Doubling Diagonal `z + 1` (`lhCenter_two_shift_diag_periodic_of_doubles`, 9.901)**:
    for EVERY shift `Q` at once, and for all `t, p ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt Q (t - (p + 1))`, and `settle ((t - (p + 1)) + 1) ≤ t`, shifting diagonally by `Q` twice on `z + 1 = t - p` flips the bit twice and restores `lhCenter ((t + Q) + Q) ((p + Q) + Q) = lhCenter t p`! -/
theorem lhCenter_two_shift_diag_periodic_of_doubles (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset : settle ((t - (p + 1)) + 1) ≤ t) :
    lhCenter ((t + Q) + Q) ((p + Q) + Q) = lhCenter t p := by
  have h1 := lhCenter_diag_shift_antiperiodic_at_t_of_doubles Q (t + Q) (p + Q)
    (by rwa [show (t + Q) - ((p + Q) + 1) = t - (p + 1) by omega])
    (by rwa [show (t + Q) - ((p + Q) + 1) = t - (p + 1) by omega])
    (by rw [show (t + Q) - ((p + Q) + 1) = t - (p + 1) by omega]; omega)
  have h0 := lhCenter_diag_shift_antiperiodic_at_t_of_doubles Q t p hz hd hset
  rw [h1, h0, Bool.not_not]

theorem lhCenter_two_shift_diag_periodic_of_doubles_prop (Q t p : Nat)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset : SettledBy ((t - (p + 1)) + 1) t) :
    lhCenter ((t + Q) + Q) ((p + Q) + Q) = lhCenter t p :=
  lhCenter_two_shift_diag_periodic_of_doubles Q t p hz hd hset

/-- **Scale-Free Universal-in-`Q` (`1 ≤ Q`) Single-Time `LhBandAgree` Flip at `(t + Q, (p + Q) + Q)` (`lhCenter_shift_two_Q_flip_of_doubles_and_lhBandAgree`, 9.902)**:
    for EVERY shift `Q ≥ 1` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt Q (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + Q)) ≤ t`, `p0 ≤ p + Q`, and `p + Q ≤ p0 + L`, if `LhBandAgree t Q p0 L` holds at time `t` alone, then because `1 ≤ Q` places `(t, p + Q)` in the `Q`-periodic region `t - (p + Q) ≤ t - (p + 1) = z`, diagonal periodicity (`9.825`) and spatial `Q`-antiperiodicity (`9.875`) give `lhCenter (t + Q) ((p + Q) + Q) = !lhCenter t p`! -/
theorem lhCenter_shift_two_Q_flip_of_doubles_and_lhBandAgree (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + Q)) ≤ t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + Q) ((p + Q) + Q) = !lhCenter t p := by
  rw [lhCenter_diag_shift_periodic_of_doubles_le Q (t - (p + 1)) t (p + Q) hd (by omega) hsetQ]
  exact lhCenter_spatial_antiperiodic_at_t_of_doubles_and_lhBandAgree
    Q t p p0 L hz hd hset1 hp0 hL hband

theorem lhCenter_shift_two_Q_flip_of_doubles_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter (t + Q) ((p + Q) + Q) = !lhCenter t p :=
  lhCenter_shift_two_Q_flip_of_doubles_and_lhBandAgree
    Q t p p0 L hQ hz hd hset1 hsetQ hp0 hL hband

/-- **Scale-Free Universal-in-`Q` (`1 ≤ Q`) Single-Time `LhBandAgree` Same-Column Vertical `Q`-Flip at Column `(p + Q) + Q` (`lhCenter_same_col_two_Q_flip_of_doubles_and_lhBandAgree`, 9.903)**:
    for EVERY shift `Q ≥ 1` at once, and for all `t, p, p0, L ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt Q (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + Q)) ≤ t`, `p0 ≤ p + Q`, and `p + Q ≤ p0 + L`, `LhBandAgree t Q p0 L` at time `t` alone forces `lhCenter ((t + Q) + Q) ((p + Q) + Q) = !lhCenter (t + Q) ((p + Q) + Q)` at the fixed spatial column `(p + Q) + Q`! -/
theorem lhCenter_same_col_two_Q_flip_of_doubles_and_lhBandAgree (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + Q)) ≤ t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter ((t + Q) + Q) ((p + Q) + Q) = !lhCenter (t + Q) ((p + Q) + Q) := by
  rw [lhCenter_two_shift_diag_periodic_of_doubles Q t p hz hd hset1,
    lhCenter_shift_two_Q_flip_of_doubles_and_lhBandAgree Q t p p0 L hQ hz hd hset1 hsetQ hp0 hL hband,
    Bool.not_not]

theorem lhCenter_same_col_two_Q_flip_of_doubles_and_lhBandAgree_prop (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : LhBandAgree t Q p0 L) :
    lhCenter ((t + Q) + Q) ((p + Q) + Q) = !lhCenter (t + Q) ((p + Q) + Q) :=
  lhCenter_same_col_two_Q_flip_of_doubles_and_lhBandAgree
    Q t p p0 L hQ hz hd hset1 hsetQ hp0 hL hband

/-- **Scale-Free Universal-in-`Q` (`1 ≤ Q`) Refutation of `LhBandAgree (t + Q) Q` Under `LhBandAgree t Q` at Any Doubling Zero Diagonal `z = t - (p + 1)` (`not_lhBandAgree_step_Q_of_doubles`, 9.904)**:
    for EVERY shift `Q ≥ 1` at once, and for all `t, p, p0, L, p1, L1 ∈ ℕ` with `IsZeroDiag (t - (p + 1))`, `DoublesAt Q (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + Q)) ≤ t`, `p0 ≤ p + Q`, `p + Q ≤ p0 + L`, `p1 ≤ (p + Q) + Q`, and `(p + Q) + Q ≤ p1 + L1`, if `LhBandAgree t Q p0 L` holds at time `t`, then `¬ LhBandAgree (t + Q) Q p1 L1`! -/
theorem not_lhBandAgree_step_Q_of_doubles (Q t p p0 L p1 L1 : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + Q)) ≤ t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hp1 : p1 ≤ (p + Q) + Q) (hL1 : (p + Q) + Q ≤ p1 + L1)
    (hband0 : LhBandAgree t Q p0 L) :
    ¬ LhBandAgree (t + Q) Q p1 L1 := by
  intro hband1
  have hflip := lhCenter_same_col_two_Q_flip_of_doubles_and_lhBandAgree
    Q t p p0 L hQ hz hd hset1 hsetQ hp0 hL hband0
  have heq := hband1 (((p + Q) + Q) - p1) (by omega)
  rw [show p1 + (((p + Q) + Q) - p1) = (p + Q) + Q by omega] at heq
  rw [heq] at hflip
  revert hflip
  cases lhCenter (t + Q) ((p + Q) + Q) <;> decide

theorem not_lhBandAgree_step_Q_of_doubles_prop (Q t p p0 L p1 L1 : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hp1 : p1 ≤ (p + Q) + Q) (hL1 : (p + Q) + Q ≤ p1 + L1)
    (hband0 : LhBandAgree t Q p0 L) :
    ¬ LhBandAgree (t + Q) Q p1 L1 :=
  not_lhBandAgree_step_Q_of_doubles Q t p p0 L p1 L1 hQ hz hd hset1 hsetQ hp0 hL hp1 hL1 hband0

/-- **Scale-Free Universal-in-`m, P` Refutation of `RhColAgree t (m * P) 1 S` Under `CenterPeriodic T P` at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_periodic_rhColAgree_one_of_doubles`, 9.905)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY positive multiplier `0 < m` and all `t ≥ T`, `p`, and `S` with `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, `¬ RhColAgree t (m * P) 1 S`! -/
theorem not_periodic_rhColAgree_one_of_doubles (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t p S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ RhColAgree t (m * P) 1 S := by
  intro hcol
  have hmP : 1 ≤ m * P := Nat.mul_pos hm hP
  have hband0 : LhBandAgree t (m * P) 0 (S + 1) :=
    periodic_lhBandAgree_zero_of_rhColAgree_one T P hP hper m t S ht hcol
  have hcol_split : RhColAgree t (m * P) 1 ((S - m * P) + m * P) := by
    rwa [show (S - m * P) + m * P = S by omega]
  have hband1 : LhBandAgree (t + m * P) (m * P) 0 ((S - m * P) + 1) :=
    periodic_lhBandAgree_steps_of_rhColAgree_one T P hP hper m t (S - m * P) (m * P) ht hcol_split
  exact not_lhBandAgree_step_Q_of_doubles
    (m * P) t p 0 (S + 1) 0 ((S - m * P) + 1)
    hmP hz hd hset1 hsetQ
    (Nat.zero_le _) (by omega) (Nat.zero_le _) (by omega) hband0 hband1

theorem not_periodic_rhColAgree_one_of_doubles_prop (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t p S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ RhColAgree t (m * P) 1 S :=
  not_periodic_rhColAgree_one_of_doubles T P hP hper m t p S hm ht hz hd hset1 hsetQ hS

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from `RhColAgree t (m * P) 1 S` at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_rhColAgree_one_doubles`, 9.906)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1` (requiring reach `p + 3 * (m * P) = (t - z) + 3 * (m * P) - 1` instead of the light-cone horizon `t + m * P`!), if `RhColAgree t (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhColAgree_one_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hrh : RhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS hrh

theorem not_centerPeriodic_of_rhColAgree_one_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hrh : RhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhColAgree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hrh

/-! ### Batch 41: Discharging `DoublesAt (m * P) z` via the Doubling Law & Producing Left-Band Agreement from White-Center Column-1 (`maskparity · 0`) Agreement Over the Reduced Horizon (9.907–9.921) -/

/-- **Scale-Free Universal-in-`m, P` Refutation of `LhColAgree t (m * P) 1 S` at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_periodic_lhColAgree_one_of_doubles`, 9.907)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY multiple `m > 0` and all `t, p, S ∈ ℕ` with `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, `¬ LhColAgree t (m * P) 1 S`! -/
theorem not_periodic_lhColAgree_one_of_doubles (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t p S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ LhColAgree t (m * P) 1 S := by
  intro hlh
  have hmP : 1 ≤ m * P := Nat.mul_pos hm hP
  have hband0 : LhBandAgree t (m * P) 0 (S + 1) :=
    lhBandAgree_of_outward_determine t (m * P) 0 S
      (periodic_lhColAgree_zero T P hP hper m t S ht) hlh
  have hlh1 : LhColAgree (t + m * P) (m * P) 1 (S - m * P) := by
    intro s hs
    rw [show (t + m * P) + s = t + (m * P + s) by omega]
    exact hlh (m * P + s) (by omega)
  have hband1 : LhBandAgree (t + m * P) (m * P) 0 ((S - m * P) + 1) :=
    lhBandAgree_of_outward_determine (t + m * P) (m * P) 0 (S - m * P)
      (periodic_lhColAgree_zero T P hP hper m (t + m * P) (S - m * P) (by omega)) hlh1
  exact not_lhBandAgree_step_Q_of_doubles
    (m * P) t p 0 (S + 1) 0 ((S - m * P) + 1)
    hmP hz hd hset1 hsetQ
    (Nat.zero_le _) (by omega) (Nat.zero_le _) (by omega) hband0 hband1

theorem not_periodic_lhColAgree_one_of_doubles_prop (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t p S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ LhColAgree t (m * P) 1 S :=
  not_periodic_lhColAgree_one_of_doubles T P hP hper m t p S hm ht hz hd hset1 hsetQ hS

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from `LhColAgree t (m * P) 1 S` at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_lhColAgree_one_doubles`, 9.908)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `LhColAgree t (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_lhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS hlh

theorem not_centerPeriodic_of_lhColAgree_one_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhColAgree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hlh

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from Single-Time Right-Half Spatial Band Agreement `RhBandAgree t (m * P) 0 (S + 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_rhBandAgree_zero_doubles`, 9.909)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `RhBandAgree t (m * P) 0 (S + 1)` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_zero_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree t (m * P) 0 (S + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS
    (periodic_rhColAgree_one_of_rhBandAgree_zero T P hP hper m t S ht hband)

theorem not_centerPeriodic_of_rhBandAgree_zero_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree t (m * P) 0 (S + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_zero_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hband

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` via `K`-Column Inward Determination from Column `1 + K` Shrinking the Horizon by `z` (`not_centerPeriodic_of_rhCenter_inward_determine_doubles`, 9.910)**:
    for EVERY `T, P, m, t, p, S, K ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `RhColAgree t (m * P) (1 + K) (S + K)` and `RhOrAgree t (m * P) (1 + K) (S + K)` hold, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhCenter_inward_determine_doubles
    (T P m t p S K : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hcol : RhColAgree t (m * P) (1 + K) (S + K))
    (hor : RhOrAgree t (m * P) (1 + K) (S + K)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS
    (rhCenter_inward_determine t (m * P) 1 S K hcol hor).1

theorem not_centerPeriodic_of_rhCenter_inward_determine_doubles_prop
    (T P m t p S K : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hcol : RhColAgree t (m * P) (1 + K) (S + K))
    (hor : RhOrAgree t (m * P) (1 + K) (S + K)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhCenter_inward_determine_doubles
    T P m t p S K hP hm ht hz hd hset1 hsetQ hS hcol hor

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from `RhOrAgree t (m * P) 1 S` and Initial Agreement at `(t, 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_rhOrAgree_one_doubles`, 9.911)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `rhCenter (t + m * P) 1 = rhCenter t 1` and `RhOrAgree t (m * P) 1 S` hold, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhOrAgree_one_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h0 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : RhOrAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  exact not_periodic_rhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS
    (periodic_rhColAgree_one_of_rhOrAgree_one T P hP hper m t S ht h0 hor)

theorem not_centerPeriodic_of_rhOrAgree_one_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h0 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : RhOrAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhOrAgree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS h0 hor

/-- **Direct `z + (p + 1)` Coordinate Refutation of `RhColAgree (z + (p + 1)) (m * P) 1 S` at Any Doubling Zero Diagonal `z` (`not_periodic_rhColAgree_one_at_zero_diag_doubles`, 9.912)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, z, p, S ∈ ℕ` with `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, `¬ RhColAgree (z + (p + 1)) (m * P) 1 S`! -/
theorem not_periodic_rhColAgree_one_at_zero_diag_doubles (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z p S : Nat) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ RhColAgree (z + (p + 1)) (m * P) 1 S := by
  exact not_periodic_rhColAgree_one_of_doubles
    T P hP hper m (z + (p + 1)) p S hm ht
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show ((z + (p + 1)) - (p + 1)) + 1 = z + 1 by omega])
    (by rwa [show (z + (p + 1)) - (p + m * P) = (z + 1) - m * P by omega])
    hS

theorem not_periodic_rhColAgree_one_at_zero_diag_doubles_prop (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z p S : Nat) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ RhColAgree (z + (p + 1)) (m * P) 1 S :=
  not_periodic_rhColAgree_one_at_zero_diag_doubles T P hP hper m z p S hm ht hz hd hset1 hsetQ hS

/-- **Unconditional Existence of a Doubling Zero Diagonal `z` and Settled Column `p` Refuting `RhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))` Under `CenterPeriodic T P` Alone (`exists_zero_diag_not_periodic_rhColAgree_one`, 9.913)**:
    combining the Zero-Diagonal Doubling Law `exists_zero_diag_doublesAt_mul` (`9.898`) with `not_periodic_rhColAgree_one_at_zero_diag_doubles` (`9.912`) discharges `IsZeroDiag`, `DoublesAt (m * P) z`, `T ≤ t`, and `SettledBy` completely: under `CenterPeriodic T P` (`0 < P`), for EVERY `m > 0`, there exist `z, p ∈ ℕ` such that `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ ¬ RhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))`! -/
theorem exists_zero_diag_not_periodic_rhColAgree_one (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p : Nat, IsZeroDiag z ∧ DoublesAt (m * P) z ∧
      ¬ RhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P)) := by
  obtain ⟨z, hz, hd⟩ := exists_zero_diag_doublesAt_mul m P hm hP
  let p := T + settle (z + 1) + settle ((z + 1) - m * P)
  refine ⟨z, p, hz, hd, ?_⟩
  exact not_periodic_rhColAgree_one_at_zero_diag_doubles
    T P hP hper m z p (p + 3 * (m * P))
    hm (by dsimp [p]; omega) hz hd
    (by dsimp [p]; omega) (by dsimp [p]; omega) (by omega)

/-- **Unconditional Existence of a Doubling Zero Diagonal `z` and Settled Column `p` Refuting `LhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))` Under `CenterPeriodic T P` Alone (`exists_zero_diag_not_periodic_lhColAgree_one`, 9.914)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m > 0`, there exist `z, p ∈ ℕ` such that `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ ¬ LhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))`! -/
theorem exists_zero_diag_not_periodic_lhColAgree_one (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p : Nat, IsZeroDiag z ∧ DoublesAt (m * P) z ∧
      ¬ LhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P)) := by
  obtain ⟨z, hz, hd⟩ := exists_zero_diag_doublesAt_mul m P hm hP
  let p := T + settle (z + 1) + settle ((z + 1) - m * P)
  refine ⟨z, p, hz, hd, ?_⟩
  exact not_periodic_lhColAgree_one_of_doubles
    T P hP hper m (z + (p + 1)) p (p + 3 * (m * P))
    hm (by dsimp [p]; omega)
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rw [show ((z + (p + 1)) - (p + 1)) + 1 = z + 1 by omega]; dsimp [p]; omega)
    (by rw [show (z + (p + 1)) - (p + m * P) = (z + 1) - m * P by omega]; dsimp [p]; omega)
    (by omega)

/-- **Scale-`0` Masked Parity `maskparity t 0` as the Exact White-Center Column-`1` Readout `!center t && rhCenter t 1` (`maskparity_zero_eq_not_center_and_rhCenter_one`, 9.915)**:
    for every `t ∈ ℕ`, the first bit `maskparity t 0` equals `!center t && rhCenter t 1` (vanishing at black centers `center t = true` and reading out `rhCenter t 1` at white centers `center t = false`)! -/
theorem maskparity_zero_eq_not_center_and_rhCenter_one (t : Nat) :
    Rule30UOR.Scale.maskparity t 0 =
      (!Rule30UOR.Core.center t && rhCenter t 1) := by
  rw [maskparity_zero]
  show (!Rule30UOR.Core.center t && Rule30UOR.Core.cell t (LexLeanRuntime.subtract 0 (-1))) =
    (!Rule30UOR.Core.center t && rhCenter t 1)
  rw [Rule30UOR.Scale.sub_neg_one, show (0 : Int) + 1 = 1 by rfl,
    Rule30UOR.Scale.cell_eq_kit t 1]
  unfold rhCenter
  rw [show ((1 : Nat) : Int) = 1 by rfl, Rule30UOR.Fixed.Rh_center t 1 (by omega)]

/-- **Unconditional Left-Half Column-`-1` Agreement `lhCenter (t + m * P) 1 = lhCenter t 1` at Every Black Center `center t = true` (`periodic_lhCenter_one_eq_of_black_center`, 9.916)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t` and `center t = true`, the `Φ` fixed-point law forces `lhCenter (t + m * P) 1 = lhCenter t 1` unconditionally (requiring NO agreement on `rhCenter · 1` at black centers!)! -/
theorem periodic_lhCenter_one_eq_of_black_center (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hb : Rule30UOR.Core.center t = true) :
    lhCenter (t + m * P) 1 = lhCenter t 1 := by
  have hdef := periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect T P hP hper m t ht
  rw [hb, Bool.not_true, Bool.false_and] at hdef
  revert hdef
  cases lhCenter (t + m * P) 1 <;> cases lhCenter t 1 <;> decide

/-- **Producing Left-Half Column-`-1` Agreement `lhCenter (t + m * P) 1 = lhCenter t 1` from White-Center Column-`1` Agreement Alone (`periodic_lhCenter_one_eq_of_white_center`, 9.917)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `center t = false → rhCenter (t + m * P) 1 = rhCenter t 1` (column-`1` agreement conditioned solely on a white center!), then `lhCenter (t + m * P) 1 = lhCenter t 1`! -/
theorem periodic_lhCenter_one_eq_of_white_center (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hw : Rule30UOR.Core.center t = false → rhCenter (t + m * P) 1 = rhCenter t 1) :
    lhCenter (t + m * P) 1 = lhCenter t 1 := by
  cases hc : Rule30UOR.Core.center t
  · have hr := hw hc
    have hdef := periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect T P hP hper m t ht
    rw [hc, hr] at hdef
    revert hdef
    cases lhCenter (t + m * P) 1 <;> cases lhCenter t 1 <;> cases rhCenter t 1 <;> decide
  · exact periodic_lhCenter_one_eq_of_black_center T P hP hper m t ht hc

/-- **Producing Left-Half Column-`-1` Agreement `lhCenter (t + m * P) 1 = lhCenter t 1` from First-Bit `maskparity · 0` Agreement (`periodic_lhCenter_one_eq_of_maskparity_zero_eq`, 9.918)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `maskparity (t + m * P) 0 = maskparity t 0`, then `lhCenter (t + m * P) 1 = lhCenter t 1`! -/
theorem periodic_lhCenter_one_eq_of_maskparity_zero_eq (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hm0 : Rule30UOR.Scale.maskparity (t + m * P) 0 = Rule30UOR.Scale.maskparity t 0) :
    lhCenter (t + m * P) 1 = lhCenter t 1 := by
  apply periodic_lhCenter_one_eq_of_white_center T P hP hper m t ht
  intro hc
  have hcQ : Rule30UOR.Core.center (t + m * P) = false := by
    rw [Rule30UOR.Scale.center_mul hper m t ht, hc]
  have hm' := hm0
  rw [maskparity_zero_eq_not_center_and_rhCenter_one (t + m * P),
    maskparity_zero_eq_not_center_and_rhCenter_one t,
    hcQ, hc] at hm'
  simpa using hm'

/-- **Producing Full Left-Band Agreement `LhBandAgree t (m * P) 0 (S + 1)` from White-Center Column-`1` Agreement Alone (`periodic_lhBandAgree_zero_of_white_center_rhCenter_one`, 9.919)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S ∈ ℕ` with `T ≤ t`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1` (column-`1` agreement at white centers only across `[t, t + S]`), then `LhBandAgree t (m * P) 0 (S + 1)` holds across the entire left band! -/
theorem periodic_lhBandAgree_zero_of_white_center_rhCenter_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    LhBandAgree t (m * P) 0 (S + 1) := by
  have hlh : LhColAgree t (m * P) 1 S := by
    intro s hs
    exact periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + s) (by omega) (hw s hs)
  exact lhBandAgree_of_outward_determine t (m * P) 0 S
    (periodic_lhColAgree_zero T P hP hper m t S ht) hlh

/-- **Producing Full Left-Band Agreement `LhBandAgree t (m * P) 0 (S + 1)` from Window Agreement of `maskparity · 0` (`periodic_lhBandAgree_zero_of_maskparity_zero_agree`, 9.920)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S ∈ ℕ` with `T ≤ t`, if `∀ s ≤ S, maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`, then `LhBandAgree t (m * P) 0 (S + 1)` holds across the entire left band! -/
theorem periodic_lhBandAgree_zero_of_maskparity_zero_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    LhBandAgree t (m * P) 0 (S + 1) := by
  have hlh : LhColAgree t (m * P) 1 S := by
    intro s hs
    exact periodic_lhCenter_one_eq_of_maskparity_zero_eq T P hP hper m (t + s) (by omega) (hm0 s hs)
  exact lhBandAgree_of_outward_determine t (m * P) 0 S
    (periodic_lhColAgree_zero T P hP hper m t S ht) hlh

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from White-Center Column-`1` Agreement at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_white_center_rhCenter_one_doubles`, 9.921)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1` (column-`1` agreement at white centers ONLY over the reduced horizon!), then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hlh : LhColAgree t (m * P) 1 S := by
    intro s hs
    exact periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + s) (by omega) (hw s hs)
  exact not_periodic_lhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS hlh

theorem not_centerPeriodic_of_white_center_rhCenter_one_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_doubles
    T P m t p S hP hm ht hz hd hset1 hsetQ hS hw

/-! ### Batch 42: First-Bit `maskparity · 0` Horizon Refutations, Unconditional White-Center Flip Witnesses Under `CenterPeriodic`, and Black-Column-1 OR-Absorption Propagation (9.922–9.936) -/

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from Window Agreement of `maskparity · 0` at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_maskparity_zero_agree_doubles`, 9.922)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `∀ s ≤ S, maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hlh : LhColAgree t (m * P) 1 S := by
    intro s hs
    exact periodic_lhCenter_one_eq_of_maskparity_zero_eq T P hP hper m (t + s) (by omega) (hm0 s hs)
  exact not_periodic_lhColAgree_one_of_doubles
    T P hP hper m t p S hm ht hz hd hset1 hsetQ hS hlh

theorem not_centerPeriodic_of_maskparity_zero_agree_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_doubles
    T P m t p S hP hm ht hz hd hset1 hsetQ hS hm0

/-- **Direct `z + (p + 1)` Coordinate Refutation of `CenterPeriodic T P` from White-Center Column-`1` Agreement at Any Doubling Zero Diagonal `z` (`not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_doubles`, 9.923)**:
    for EVERY `T, P, m, z, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if `∀ s ≤ S, center ((z + (p + 1)) + s) = false → rhCenter (((z + (p + 1)) + s) + m * P) 1 = rhCenter ((z + (p + 1)) + s) 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_doubles
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rhCenter (((z + (p + 1)) + s) + m * P) 1 = rhCenter ((z + (p + 1)) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  exact not_centerPeriodic_of_white_center_rhCenter_one_doubles
    T P m (z + (p + 1)) p S hP hm ht
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show ((z + (p + 1)) - (p + 1)) + 1 = z + 1 by omega])
    (by rwa [show (z + (p + 1)) - (p + m * P) = (z + 1) - m * P by omega])
    hS hw

theorem not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_doubles_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rhCenter (((z + (p + 1)) + s) + m * P) 1 = rhCenter ((z + (p + 1)) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hsetQ hS hw

/-- **Direct `z + (p + 1)` Coordinate Refutation of `CenterPeriodic T P` from `maskparity · 0` Agreement at Any Doubling Zero Diagonal `z` (`not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles`, 9.924)**:
    for EVERY `T, P, m, z, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if `∀ s ≤ S, maskparity (((z + (p + 1)) + s) + m * P) 0 = maskparity ((z + (p + 1)) + s) 0`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  exact not_centerPeriodic_of_maskparity_zero_agree_doubles
    T P m (z + (p + 1)) p S hP hm ht
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show ((z + (p + 1)) - (p + 1)) + 1 = z + 1 by omega])
    (by rwa [show (z + (p + 1)) - (p + m * P) = (z + 1) - m * P by omega])
    hS hm0

theorem not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hsetQ hS hm0

/-- **Unconditional Existence of a White Center `s ≤ p + 3 * (m * P)` Where `rhCenter · 1` Flips Under `CenterPeriodic T P` Alone (`exists_zero_diag_white_center_rhCenter_one_flip_of_periodic`, 9.925)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m > 0`, there exist `z, p, s ∈ ℕ` such that `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ s ≤ p + 3 * (m * P) ∧ center ((z + (p + 1)) + s) = false ∧ rhCenter (((z + (p + 1)) + s) + m * P) 1 = !rhCenter ((z + (p + 1)) + s) 1`! -/
theorem exists_zero_diag_white_center_rhCenter_one_flip_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p s : Nat, IsZeroDiag z ∧ DoublesAt (m * P) z ∧
      s ≤ p + 3 * (m * P) ∧
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false ∧
      rhCenter (((z + (p + 1)) + s) + m * P) 1 = !rhCenter ((z + (p + 1)) + s) 1 := by
  obtain ⟨z, hz, hd⟩ := exists_zero_diag_doublesAt_mul m P hm hP
  let p := T + settle (z + 1) + settle ((z + 1) - m * P)
  have hnot : ¬ ∀ s : Nat, s ≤ p + 3 * (m * P) →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rhCenter (((z + (p + 1)) + s) + m * P) 1 = rhCenter ((z + (p + 1)) + s) 1 := by
    intro hw
    exact not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_doubles
      T P m z p (p + 3 * (m * P)) hP hm (by dsimp [p]; omega) hz hd
      (by dsimp [p]; omega) (by dsimp [p]; omega) (by omega) hw hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ p + 3 * (m * P) := by
    by_cases hns : s ≤ p + 3 * (m * P)
    · exact hns
    · exfalso
      exact hs_not (fun h => absurd h hns)
  have hc : Rule30UOR.Core.center ((z + (p + 1)) + s) = false := by
    cases hc' : Rule30UOR.Core.center ((z + (p + 1)) + s)
    · rfl
    · exfalso
      exact hs_not (fun _ h => by rw [hc'] at h; cases h)
  have hne : rhCenter (((z + (p + 1)) + s) + m * P) 1 ≠ rhCenter ((z + (p + 1)) + s) 1 := by
    intro heq
    exact hs_not (fun _ _ => heq)
  refine ⟨z, p, s, hz, hd, hs, hc, ?_⟩
  revert hne
  cases rhCenter (((z + (p + 1)) + s) + m * P) 1 <;>
    cases rhCenter ((z + (p + 1)) + s) 1 <;> decide

/-- **Unconditional Existence of a Step `s ≤ p + 3 * (m * P)` Where `maskparity · 0` Flips Under `CenterPeriodic T P` Alone (`exists_zero_diag_maskparity_zero_flip_of_periodic`, 9.926)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m > 0`, there exist `z, p, s ∈ ℕ` such that `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ s ≤ p + 3 * (m * P) ∧ maskparity (((z + (p + 1)) + s) + m * P) 0 = !maskparity ((z + (p + 1)) + s) 0`! -/
theorem exists_zero_diag_maskparity_zero_flip_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p s : Nat, IsZeroDiag z ∧ DoublesAt (m * P) z ∧
      s ≤ p + 3 * (m * P) ∧
      Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0 := by
  obtain ⟨z, hz, hd⟩ := exists_zero_diag_doublesAt_mul m P hm hP
  let p := T + settle (z + 1) + settle ((z + 1) - m * P)
  have hnot : ¬ ∀ s : Nat, s ≤ p + 3 * (m * P) →
      Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0 := by
    intro hm0
    exact not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
      T P m z p (p + 3 * (m * P)) hP hm (by dsimp [p]; omega) hz hd
      (by dsimp [p]; omega) (by dsimp [p]; omega) (by omega) hm0 hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ p + 3 * (m * P) := by
    by_cases hns : s ≤ p + 3 * (m * P)
    · exact hns
    · exfalso
      exact hs_not (fun h => absurd h hns)
  have hne : Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 ≠
      Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0 := by
    intro heq
    exact hs_not (fun _ => heq)
  refine ⟨z, p, s, hz, hd, hs, ?_⟩
  revert hne
  cases Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 <;>
    cases Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0 <;> decide

/-- **Unconditional Existence of a Step `s ≤ p + 3 * (m * P)` Where `lhCenter · 1` Flips Under `CenterPeriodic T P` Alone (`exists_zero_diag_lhCenter_one_flip_of_periodic`, 9.927)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m > 0`, there exist `z, p, s ∈ ℕ` such that `IsZeroDiag z ∧ DoublesAt (m * P) z ∧ s ≤ p + 3 * (m * P) ∧ lhCenter (((z + (p + 1)) + s) + m * P) 1 = !lhCenter ((z + (p + 1)) + s) 1`! -/
theorem exists_zero_diag_lhCenter_one_flip_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p s : Nat, IsZeroDiag z ∧ DoublesAt (m * P) z ∧
      s ≤ p + 3 * (m * P) ∧
      lhCenter (((z + (p + 1)) + s) + m * P) 1 = !lhCenter ((z + (p + 1)) + s) 1 := by
  obtain ⟨z, p, hz, hd, hnot⟩ := exists_zero_diag_not_periodic_lhColAgree_one T P hP hper m hm
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ p + 3 * (m * P) := by
    by_cases hns : s ≤ p + 3 * (m * P)
    · exact hns
    · exfalso
      exact hs_not (fun h => absurd h hns)
  have hne : lhCenter (((z + (p + 1)) + s) + m * P) 1 ≠ lhCenter ((z + (p + 1)) + s) 1 := by
    intro heq
    exact hs_not (fun _ => heq)
  refine ⟨z, p, s, hz, hd, hs, ?_⟩
  revert hne
  cases lhCenter (((z + (p + 1)) + s) + m * P) 1 <;>
    cases lhCenter ((z + (p + 1)) + s) 1 <;> decide

/-- **1-Step Evolution of Right-Half Column `1` Driven by the Center (`rhCenter_step_one_eq_center_xor_or`, 9.928)**:
    for every `t ∈ ℕ`, `rhCenter (t + 1) 1 = center t ⊕ (rhCenter t 1 || rhCenter t 2)`! -/
theorem rhCenter_step_one_eq_center_xor_or (t : Nat) :
    rhCenter (t + 1) 1 =
      bxor (Rule30UOR.Core.center t) (rhCenter t 1 || rhCenter t 2) := by
  rw [rhCenter_step_succ t 0, rhCenter_zero_eq_center t]

/-- **Black Column-`1` OR-Absorption Law (`rhCenter_step_one_eq_not_center_of_black_one`, 9.929)**:
    for every `t ∈ ℕ`, whenever `rhCenter t 1 = true`, column `2` (`rhCenter t 2`) is completely absorbed by the boolean OR (`true || rhCenter t 2 = true`), forcing `rhCenter (t + 1) 1 = !center t` unconditionally! -/
theorem rhCenter_step_one_eq_not_center_of_black_one (t : Nat)
    (hb : rhCenter t 1 = true) :
    rhCenter (t + 1) 1 = !Rule30UOR.Core.center t := by
  rw [rhCenter_step_one_eq_center_xor_or t, hb, Bool.true_or]
  cases Rule30UOR.Core.center t <;> rfl

/-- **White-Center + Black-Column-`1` Persistence Law (`rhCenter_step_one_eq_true_of_white_center_and_black_one`, 9.930)**:
    for every `t ∈ ℕ`, if `center t = false` and `rhCenter t 1 = true`, then `rhCenter (t + 1) 1 = true` unconditionally (with zero dependence on `rhCenter t 2`!)! -/
theorem rhCenter_step_one_eq_true_of_white_center_and_black_one (t : Nat)
    (hc : Rule30UOR.Core.center t = false)
    (hb : rhCenter t 1 = true) :
    rhCenter (t + 1) 1 = true := by
  rw [rhCenter_step_one_eq_not_center_of_black_one t hb, hc]
  rfl

/-- **1-Step Column-`1` Black Pinning from `maskparity t 0 = true` (`rhCenter_step_one_eq_true_of_maskparity_zero_true`, 9.931)**:
    for every `t ∈ ℕ`, if `maskparity t 0 = true`, then `rhCenter (t + 1) 1 = true` unconditionally! -/
theorem rhCenter_step_one_eq_true_of_maskparity_zero_true (t : Nat)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    rhCenter (t + 1) 1 = true := by
  have hm' := hm0
  rw [maskparity_zero_eq_not_center_and_rhCenter_one t] at hm'
  have hc : Rule30UOR.Core.center t = false := by
    revert hm'; cases Rule30UOR.Core.center t <;> cases rhCenter t 1 <;> decide
  have hb : rhCenter t 1 = true := by
    revert hm'; cases Rule30UOR.Core.center t <;> cases rhCenter t 1 <;> decide
  exact rhCenter_step_one_eq_true_of_white_center_and_black_one t hc hb

/-- **2-Step Column-`1` Determination from `maskparity t 0 = true` Absorbing Both `rhCenter t 2` and `rhCenter (t + 1) 2` (`rhCenter_step_two_eq_not_center_of_maskparity_zero_true`, 9.932)**:
    for every `t ∈ ℕ`, if `maskparity t 0 = true`, then `rhCenter (t + 1) 1 = true` absorbs `rhCenter (t + 1) 2` at the next step as well, forcing `rhCenter (t + 2) 1 = !center (t + 1)` unconditionally! -/
theorem rhCenter_step_two_eq_not_center_of_maskparity_zero_true (t : Nat)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    rhCenter (t + 2) 1 = !Rule30UOR.Core.center (t + 1) := by
  have h1 := rhCenter_step_one_eq_true_of_maskparity_zero_true t hm0
  exact rhCenter_step_one_eq_not_center_of_black_one (t + 1) h1

/-- **Unconditional 1-Step Forward Propagation of Right-Half Column-`1` Agreement Across a Black Column-`1` Cell (`periodic_rhCenter_step_one_eq_of_black_one`, 9.933)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `rhCenter (t + m * P) 1 = true` and `rhCenter t 1 = true`, then `rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1` holds unconditionally without any hypothesis on column `2` (`rhCenter · 2`)! -/
theorem periodic_rhCenter_step_one_eq_of_black_one (T P : Nat) (_hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hbQ : rhCenter (t + m * P) 1 = true)
    (hb0 : rhCenter t 1 = true) :
    rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1 := by
  rw [show (t + 1) + m * P = (t + m * P) + 1 by omega,
    rhCenter_step_one_eq_not_center_of_black_one (t + m * P) hbQ,
    rhCenter_step_one_eq_not_center_of_black_one t hb0,
    Rule30UOR.Scale.center_mul hper m t ht]

/-- **Unconditional 1-Step Forward Propagation of Left-Half Column-`-1` Agreement Across a Black Column-`1` Cell (`periodic_lhCenter_step_one_eq_of_black_one`, 9.934)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `rhCenter (t + m * P) 1 = true` and `rhCenter t 1 = true`, then `lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1` holds unconditionally without any hypothesis on column `2`! -/
theorem periodic_lhCenter_step_one_eq_of_black_one (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hbQ : rhCenter (t + m * P) 1 = true)
    (hb0 : rhCenter t 1 = true) :
    lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1 := by
  apply periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + 1) (by omega)
  intro _hc
  exact periodic_rhCenter_step_one_eq_of_black_one T P hP hper m t ht hbQ hb0

/-- **2-Step Forward Propagation of Left-Half Column-`-1` Agreement from `maskparity · 0 = true` at Time `t` Alone (`periodic_lhCenter_step_one_and_two_eq_of_maskparity_zero_true`, 9.935)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `maskparity (t + m * P) 0 = true` and `maskparity t 0 = true` at time `t`, then `lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1 ∧ lhCenter ((t + 2) + m * P) 1 = lhCenter (t + 2) 1` holds across both `t + 1` and `t + 2` without any hypothesis on column `2`! -/
theorem periodic_lhCenter_step_one_and_two_eq_of_maskparity_zero_true (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hmQ : Rule30UOR.Scale.maskparity (t + m * P) 0 = true)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1 ∧
      lhCenter ((t + 2) + m * P) 1 = lhCenter (t + 2) 1 := by
  have h1Q : rhCenter ((t + 1) + m * P) 1 = true := by
    rw [show (t + 1) + m * P = (t + m * P) + 1 by omega]
    exact rhCenter_step_one_eq_true_of_maskparity_zero_true (t + m * P) hmQ
  have h10 : rhCenter (t + 1) 1 = true :=
    rhCenter_step_one_eq_true_of_maskparity_zero_true t hm0
  refine ⟨?_, ?_⟩
  · apply periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + 1) (by omega)
    intro _hc
    rw [h1Q, h10]
  · have hstep2 := periodic_lhCenter_step_one_eq_of_black_one T P hP hper m (t + 1) (by omega) h1Q h10
    rwa [show (t + 1) + 1 = t + 2 by omega] at hstep2

/-- **Producing Full Left-Band Agreement `LhBandAgree t (m * P) 0 (S + 1)` from OR-Agreement Conditioned Solely on White Next Centers (`periodic_lhBandAgree_zero_of_white_center_rhOrAgree_one`, 9.936)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S ∈ ℕ` with `T ≤ t`, if `center t = false → rhCenter (t + m * P) 1 = rhCenter t 1` at the initial step `t` and `∀ s < S, center (t + (s + 1)) = false → (rhCenter ((t + s) + m * P) 1 || rhCenter ((t + s) + m * P) 2) = (rhCenter (t + s) 1 || rhCenter (t + s) 2)` (requiring OR-agreement ONLY at steps `s` whose next center `center (t + (s + 1)) = false` is white!), then `LhBandAgree t (m * P) 0 (S + 1)` holds across the entire left band! -/
theorem periodic_lhBandAgree_zero_of_white_center_rhOrAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h0 : Rule30UOR.Core.center t = false → rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : ∀ s : Nat, s < S →
      Rule30UOR.Core.center (t + (s + 1)) = false →
        (rhCenter ((t + s) + m * P) 1 || rhCenter ((t + s) + m * P) 2) =
          (rhCenter (t + s) 1 || rhCenter (t + s) 2)) :
    LhBandAgree t (m * P) 0 (S + 1) := by
  apply periodic_lhBandAgree_zero_of_white_center_rhCenter_one T P hP hper m t S ht
  intro s hs hc
  rcases s with _ | s
  · rw [Nat.add_zero] at hc ⊢
    exact h0 hc
  · have hstep := periodic_rhCenter_step_one_eq_of_or_eq
      T P hP hper m (t + s) (by omega) (hor s (by omega) hc)
    rwa [show (t + s) + 1 = t + (s + 1) by omega] at hstep

end Rule30UOR.Interfaces
