module
public import Rule30UOR.Core
public import Rule30Paper.Paper
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals
@[expose] public section
namespace Rule30Bridge
open Ruliology.CellularAutomata

/-- The runtime's Int comparison is the standard one. -/
theorem lessThan_int (a b : Int) : LexLeanCollections.lessThan a b = decide (a < b) := by
  unfold LexLeanCollections.lessThan
  show (match (compare a b) with | Ordering.lt => true | _ => false) = _
  by_cases h : a < b
  · have : compare a b = .lt := by simp [compare, compareOfLessAndEq, h]
    rw [this]; simp [h]
  · by_cases h2 : a = b
    · subst h2; simp [compare, compareOfLessAndEq]
    · have : compare a b = .gt := by simp [compare, compareOfLessAndEq, h, h2]
      rw [this]; simp [h]

theorem rule_eq_kit : ∀ a b c : Bool, Rule30UOR.Core.rule a b c = Rule30Jen.rule a b c := by decide

theorem cell_eq_kit : ∀ t p, Rule30UOR.Core.cell t p = Rule30Jen.cell t p := by
  intro t
  induction t with
  | zero =>
    intro p
    simp only [Rule30UOR.Core.cell, Rule30Jen.cell, lessThan_int]
    by_cases h : p = 0
    · subst h; decide
    · rcases Int.lt_or_gt_of_ne h with h' | h'
      · simp [h, h']
      · simp [h, h', Int.not_lt.mpr (Int.le_of_lt h')]
  | succ s ih =>
    intro p
    simp only [Rule30UOR.Core.cell, Rule30Jen.cell, rule_eq_kit, ih, LexLeanRuntime.subtract]
    rfl


theorem center_eq_kit : ∀ t, Rule30UOR.Core.center t = Rule30Prize.center t := fun t => cell_eq_kit t 0
/-- The white-run interior law, transported to the kit's `cell`. -/
theorem white_run_interior_kit (t : Nat) (p : Int)
    (hl : Rule30Jen.cell t (p - 1) = false) (hc : Rule30Jen.cell t p = false)
    (hr : Rule30Jen.cell t (p + 1) = false) : Rule30Jen.cell (t + 1) p = false := by
  rw [← cell_eq_kit] at hl hc hr ⊢
  exact Rule30Paper.Paper.white_run_interior t p (by simpa [Rule30UOR.Core.leftOf, LexLeanRuntime.subtract] using hl) hc
    (by simpa [Rule30UOR.Core.rightOf, LexLeanRuntime.subtract] using hr)

/-- A white run shrinks by one cell at each end, in the kit's notation. -/
theorem white_run_shrinks_kit (t : Nat) (a b : Int)
    (h : ∀ q, a ≤ q → q ≤ b → Rule30Jen.cell t q = false) :
    ∀ q, a + 1 ≤ q → q ≤ b - 1 → Rule30Jen.cell (t + 1) q = false := by
  intro q h1 h2
  rw [← cell_eq_kit]
  exact Rule30Paper.Paper.white_run_shrinks t a b
    (fun q h1 h2 => by rw [cell_eq_kit]; exact h q h1 h2) q h1 h2

end Rule30Bridge

namespace Rule30Bridge
open Ruliology.CellularAutomata

/-- The LexLean closed left system is the kit's left-diagonal array. -/
theorem ldiag_eq_D : ∀ t j, Rule30UOR.Core.ldiag j t = Rule30Diagonals.D j t := by
  intro t
  induction t with
  | zero =>
    intro j
    rcases j with _ | j
    · rfl
    · show false = Rule30Jen.cell 0 (((j + 1 : Nat) : Int) - ((0 : Nat) : Int))
      simp only [Rule30Jen.cell]; exact (decide_eq_false (by omega)).symm
  | succ t ih =>
    intro j
    rcases j with _ | _ | k
    · exact (Rule30Diagonals.D_zero (t + 1)).symm
    · exact (Rule30Diagonals.D_one t).symm
    · rw [Rule30UOR.Core.ldiag_step, ih k, ih (k + 1), ih (k + 2), Rule30Diagonals.D_step]
      simp only [Rule30UOR.Core.bxor]; cases Rule30Diagonals.D k t <;> simp

end Rule30Bridge

namespace Rule30Bridge
open Ruliology.CellularAutomata

/-- The kit's center column is the LexLean left system read on its diagonal. -/
theorem center_eq_lcenter : Rule30Prize.center = Rule30UOR.Core.lcenter := by
  funext t
  show Rule30Jen.cell t 0 = Rule30UOR.Core.ldiag t t
  rw [ldiag_eq_D, ← Rule30Diagonals.center_eq_D]

/-- **Problem 1, stated on the LexLean left system.** -/
theorem problem1_iff_lcenter :
    Rule30Prize.Problem1 ↔ ¬ Rule30Jen.EventuallyPeriodic Rule30UOR.Core.lcenter := by
  unfold Rule30Prize.Problem1; rw [center_eq_lcenter]

/-- Bit `j` of the LexLean Witt integer `row t` is the kit's right-diagonal array `R j t`. -/
theorem row_testBit_eq_R (t j : Nat) :
    (Rule30UOR.Core.row t).testBit j = Rule30Diagonals.R j t := by
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Right.rdiag_eq_R]

/-- The LexLean Witt `rowCenter t` is the `0`/`1` encoding of the kit's `center t`. -/
theorem rowCenter_eq_kit_center (t : Nat) :
    Rule30UOR.Core.rowCenter t = if Rule30Prize.center t then 1 else 0 := by
  rw [Rule30UOR.Interfaces.rowCenter_eq_center, center_eq_kit]
  rfl

/-- **Problem 1, stated on the LexLean Witt center bit sequence.** -/
theorem problem1_iff_noRowCenterPeriod :
    Rule30Prize.Problem1 ↔ Rule30UOR.Interfaces.NoRowCenterPeriod :=
  Rule30UOR.Interfaces.problem1_iff_noRowCenterPeriod

/-- **The two-place Witt scale identity on the kit's center and left-diagonal arrays**: for `d ≤ k`, `xor (center d) (D d (d + 2^k))` equals the Witt scale increment at `d + 2^k`. -/
theorem two_places_witt_kit (d k : Nat) (hk : d ≤ k) :
    Rule30UOR.Core.bxor (Rule30UOR.Core.center d) (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((d + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.two_places_witt d k hk

/-- **The two-place Witt dyadic coboundary**: for `d ≤ k`, `bxor (center d) (ldiag d (d + 2^k))` equals the dyadic coboundary defect of `wittRespBool`. -/
theorem two_places_witt_coboundary_kit (d k : Nat) (hk : d ≤ k) :
    Rule30UOR.Core.bxor (Rule30UOR.Core.center d) (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool d (k + 1))
          (Rule30UOR.Interfaces.wittRespBool d k))
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.two_places_witt_coboundary d k hk

/-- **Ray 0 (Right-diagonal ray) of `winWitt` from the verified paper**: for `j < 2^k`, bit `j` of `winWitt t0 (2^k)` is `bton (bxor (rdiag j (t0 + 2^k)) (rdiag j t0))`. -/
theorem winwitt_ray_zero_kit (t0 k j : Nat) (hj : j < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) j =
      Rule30UOR.Interfaces.bton
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag j (t0 + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.rdiag j t0)) :=
  Rule30Paper.Paper.winwitt_ray_zero t0 k j hj

/-- **Ray 1 (Vertical-column ray) of `winWitt` from the verified paper**: for `i < 2^k` and `2 * t0 < i + 2^k`, bit `i + 2^k` of `winWitt t0 (2^k)` is `bton (bxor (rdiag (i + 2^k) (t0 + 2^k)) (rdiag i t0))`. -/
theorem winwitt_ray_one_kit (t0 k i : Nat) (hi : i < Rule30UOR.Core.twopow k)
    (hcone : 2 * t0 < i + Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
        (i + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.bton
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag (i + Rule30UOR.Core.twopow k) (t0 + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.rdiag i t0)) :=
  Rule30Paper.Paper.winwitt_ray_one t0 k i hi hcone

/-- **Ray 2 (Left-diagonal ray) of `winWitt` from the verified paper**: for `d + m < 2^k`, bit `d + 2m + 2^(k+1)` of `winWitt (d + m) (2^k)` is `bton (bxor (ldiag d (d + m)) (ldiag d (d + m + 2^k)))`. -/
theorem winwitt_ray_two_kit (d m k : Nat) (hdm : d + m < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt (d + m) (Rule30UOR.Core.twopow k))
        (d + 2 * m + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.bton
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag d (d + m))
          (Rule30UOR.Core.ldiag d (d + m + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.winwitt_ray_two d m k hdm

/-- **Nonlinear Rule 30 cone step of `winWitt` from the verified paper**. -/
theorem winwitt_cone_step_kit (t0 k : Nat) (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.winWitt (t0 + 1) (Rule30UOR.Core.twopow k) =
      (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) ^^^
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) <<< 1)) :=
  Rule30Paper.Paper.winwitt_cone_step t0 k hcone

/-- **Sigmatics Triality Sector Exhaustion inside the cone (`2 * t0 < 2^k`)**: every bit `j ≥ 3 * 2^k` vanishes. -/
theorem winwitt_triality_outside_kit (t0 k j : Nat)
    (hcone : 2 * t0 < Rule30UOR.Core.twopow k) (hj : 3 * Rule30UOR.Core.twopow k ≤ j) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) j = 0 :=
  Rule30Paper.Paper.winwitt_triality_outside t0 k j hcone hj

/-- **Sigmatics Sector 1 Center-Slot Readout (`t0 < 2^k`)**: bit `t0 + 2^k` of `winWitt t0 (2^k)` is `bton (bxor (center (t0 + 2^k)) (center t0))`. -/
theorem winwitt_center_slot_kit (t0 k : Nat) (ht0 : t0 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
        (t0 + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.bton
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (t0 + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.center t0)) :=
  Rule30Paper.Paper.winwitt_center_slot t0 k ht0

/-- **Threshold-Center Antiperiodicity from the verified paper**: at `t0 = J + 1 < 2^k`, `rdiag (J + 1) (J + 1 + 2^k) = !center (J + 1)`. -/
theorem threshold_center_antiperiod_kit (k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hJlt : J + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.rdiag (J + 1) (J + 1 + Rule30UOR.Core.twopow k) =
      !Rule30UOR.Core.center (J + 1) :=
  Rule30Paper.Paper.threshold_center_antiperiod k J hJ hJlt

/-- **Exact Rule 30 Evolution of `phiScale k (row t0)` inside the Cone from the verified paper**. -/
theorem phiscale_row_cone_step_kit (t0 k : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (t0 + 1)) =
      Rule30UOR.Core.phi (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0)) :=
  Rule30Paper.Paper.phiscale_row_cone_step t0 k hcone

/-- **Complete Unperturbed Sector-0 Rule 30 Evolution before Collision (`2 * t0 < J`) from the verified paper**. -/
theorem winwitt_unperturbed_sector_zero_kit (t0 k J j : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (htJ : 2 * t0 < J) (hj : j ≤ Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt (t0 + 1) (Rule30UOR.Core.twopow k)) j =
      Rule30UOR.Core.bit (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) j :=
  Rule30Paper.Paper.winwitt_unperturbed_sector_zero t0 k J j hcone hJ htJ hj

/-- **Fundamental Two-Place Diagonal Shear (`ldiag d (d + s) = rdiag (d + 2 * s) (d + s)`) from the verified paper**. -/
theorem ldiag_eq_rdiag_kit (d s : Nat) :
    Rule30UOR.Core.ldiag d (d + s) = Rule30UOR.Core.rdiag (d + 2 * s) (d + s) :=
  Rule30Paper.Paper.ldiag_eq_rdiag d s

/-- **Unified Triality Sector 1 Left-Diagonal Readout from the verified paper**. -/
theorem winwitt_sector_one_ldiag_kit (d s k : Nat)
    (hds : d + 2 * s < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt (d + s) (Rule30UOR.Core.twopow k))
        (d + 2 * s + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.bton
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) (d + s + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag d (d + s))) :=
  Rule30Paper.Paper.winwitt_sector_one_ldiag d s k hds

/-- **Universal Late Black Plateau at `J + 1` before Cone Arrival (`2 * t0 ≤ J`) from the verified paper**. -/
theorem rdiag_threshold_late_true_plateau_kit (t0 k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htJ : 2 * t0 ≤ J) :
    Rule30UOR.Core.rdiag (J + 1) (t0 + Rule30UOR.Core.twopow k) = true :=
  Rule30Paper.Paper.rdiag_threshold_late_true_plateau t0 k J hJ htJ

/-- **Collision Freeze of Bit `J + 2` of `winWitt` at `2 * t0 = J` from the verified paper**. -/
theorem winwitt_thresh_plus_two_freeze_kit (t0 k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (htJ : 2 * t0 = J) (hJlt : J + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt (t0 + 1) (Rule30UOR.Core.twopow k)) (J + 2) =
      Rule30UOR.Core.bit (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) (J + 2) :=
  Rule30Paper.Paper.winwitt_thresh_plus_two_freeze t0 k J hJ htJ hJlt

/-- **Two-Place Late Diagonal Agreement below Both Thresholds from the verified paper**. -/
theorem rdiag_eq_ldiag_settled_below_thresh_kit (d s k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s ≤ J) (hds : d + 2 * s < Rule30UOR.Core.twopow k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + s)) :
    Rule30UOR.Core.rdiag (d + 2 * s) (d + s + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.ldiag d (d + s + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.rdiag_eq_ldiag_settled_below_thresh d s k J hJ hk hdJ hds hset

/-- **Universal Scale Invariance of Triality Sector 2 in the Archimedean Damage Band from the verified paper**. -/
theorem winwitt_sector_two_scale_eq_kit (d s k1 k2 : Nat)
    (hk1 : d ≤ k1) (hk2 : d ≤ k2)
    (hds1 : d + s < Rule30UOR.Core.twopow k1)
    (hds2 : d + s < Rule30UOR.Core.twopow k2)
    (hset1 : Rule30UOR.Interfaces.SettledBy d (d + s + Rule30UOR.Core.twopow k1))
    (hset2 : Rule30UOR.Interfaces.SettledBy d (d + s + Rule30UOR.Core.twopow k2)) :
    Rule30UOR.Core.bit (Rule30UOR.Core.winWitt (d + s) (Rule30UOR.Core.twopow k1))
        (d + 2 * s + Rule30UOR.Core.twopow (k1 + 1)) =
      Rule30UOR.Core.bit (Rule30UOR.Core.winWitt (d + s) (Rule30UOR.Core.twopow k2))
        (d + 2 * s + Rule30UOR.Core.twopow (k2 + 1)) :=
  Rule30Paper.Paper.winwitt_sector_two_scale_eq d s k1 k2 hk1 hk2 hds1 hds2 hset1 hset2

/-- **Cross-Scale Witt Identity for the Late Two-Place Difference from the verified paper**. -/
theorem center_late_xor_ldiag_witt_kit (d k : Nat) (hk : d ≤ k) :
    Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool d (k + 1))
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.center_late_xor_ldiag_witt d k hk

/-- **Unsettled Repeat-Lag Lock between Left Diagonals and Late Witt Responses from the verified paper**. -/
theorem periodic_ldiag_xor_late_witt_lag_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d) (hk1 : d ≤ k1) (hk2 : d ≤ k2) :
    Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k1))
        (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k2)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k1) k1)
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k2) k2) :=
  Rule30Paper.Paper.periodic_ldiag_xor_late_witt_lag T P hP h d k1 k2 hlag ht hk1 hk2

/-- **Step 1: Unsettled Reduction of the Late Term `response (d + 2^k) k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_late_response_unsettled_decomp_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.periodic_late_response_unsettled_decomp T P hP h d k ht hk

/-- **Step 1: Zero-State Diagonal Readout `zcenter d` from Lag Class and Late Response from the verified paper**. -/
theorem periodic_zcenter_from_lag_late_response_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k)
    (hset : Rule30UOR.Interfaces.SettledAt d k) :
    Rule30UOR.Interfaces.ZCenterEq d
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_zcenter_from_lag_late_response T P hP h d k ht hk hset

/-- **Step 1–2: Exact Shift-by-`P` Defect Reduction for `zcenter` via Late Rule-60 Response from the verified paper**. -/
theorem periodic_zcenter_shift_xor_late_response_kit (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k)
    (hset1 : Rule30UOR.Interfaces.SettledAt d k)
    (hset2 : Rule30UOR.Interfaces.SettledAt (d + P) k) :
    Rule30UOR.Interfaces.ZCenterXorEq (d + P) d
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.response (d + P + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_zcenter_shift_xor_late_response T P h d k ht hk hset1 hset2

/-- **Step 3 Anchor 1: `zcenter` is never periodic of period `1` from the verified paper**. -/
theorem zcenter_not_periodic_one_kit (T : Nat) :
    ¬ Rule30UOR.Interfaces.ZCenterPeriodic T 1 :=
  Rule30Paper.Paper.zcenter_not_periodic_one T

/-- **Step 3 Anchor 2: `zcenter` is never periodic of period `2` from the verified paper**. -/
theorem zcenter_not_periodic_two_kit (T : Nat) :
    ¬ Rule30UOR.Interfaces.ZCenterPeriodic T 2 :=
  Rule30Paper.Paper.zcenter_not_periodic_two T

/-- **Step 3 Anchor 3: Zero-Diagonal Resonance Obstruction to `ZCenterPeriodic T Q` from the verified paper**. -/
theorem zcenter_periodic_not_zero_diag_shift_kit (T Q : Nat)
    (h : Rule30UOR.Interfaces.ZCenterPeriodic T Q)
    (z m : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hzT : T ≤ z) :
    ¬ Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 2 + m * Q) :=
  Rule30Paper.Paper.zcenter_periodic_not_zero_diag_shift T Q h z m hz hzT

/-- **Step 1: Exact `Nat`-Level 1-Cocycle Law for `winWitt` Across Dyadic Scales from the verified paper**. -/
theorem winwitt_scale_cocycle_kit (t0 k : Nat) :
    Rule30UOR.Core.winWitt (t0 + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow (k + 1))) ^^^
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.winwitt_scale_cocycle t0 k

/-- **Step 1: Exact Early-Window Triality Decomposition of the Late Witt Response from the verified paper**. -/
theorem witt_resp_late_from_early_triality_kit (d k : Nat) (hk : d ≤ k) :
    Rule30UOR.Interfaces.BitWinWittEq d (Rule30UOR.Core.twopow k)
      (d + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool d (k + 1))
          (Rule30UOR.Interfaces.wittRespBool d k))) :=
  Rule30Paper.Paper.witt_resp_late_from_early_triality d k hk

/-- **Step 1: Reduction of the Late Witt Term under `CenterPeriodic T P` via Lag Class and Triality Sector 2 from the verified paper**. -/
theorem periodic_late_witt_from_lag_sector_two_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Interfaces.BitWinWittEq d (Rule30UOR.Core.twopow k)
      (d + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool (d + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))) :=
  Rule30Paper.Paper.periodic_late_witt_from_lag_sector_two T P hP h d k ht hk

/-- **Step 1: Reduction of the Late Masked Column-1 Parity `maskparity (d + 2^k) k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_late_maskparity_decomp_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse d (k + 1))
          (Rule30UOR.Scale.leftresponse d k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k))) :=
  Rule30Paper.Paper.periodic_late_maskparity_decomp T P hP h d k ht hk

/-- **XOR Channel: Scale-0 `leftresponse` Vanishes Identically from the verified paper**. -/
theorem leftresponse_zero_kit (t : Nat) :
    Rule30UOR.Scale.leftresponse t 0 = false :=
  Rule30Paper.Paper.leftresponse_zero t

/-- **XOR Channel: Scale-0 `response` Equals `maskparity t 0` from the verified paper**. -/
theorem response_zero_maskparity_kit (t : Nat) :
    Rule30UOR.Scale.response t 0 = Rule30UOR.Scale.maskparity t 0 :=
  Rule30Paper.Paper.response_zero_maskparity t

/-- **XOR Channel: 1-Step Discrete Derivative of `maskparity` Extracts Dyadic Jump of `maskparity · 0` from the verified paper**. -/
theorem maskparity_step_diff_kit (t k : Nat) :
    Rule30UOR.Core.bxor (Rule30UOR.Scale.maskparity (t + 1) k) (Rule30UOR.Scale.maskparity t k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity (t + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity t 0) :=
  Rule30Paper.Paper.maskparity_step_diff t k

/-- **XOR Channel: Right-System Readout of `maskparity (s + 1) 0` from the verified paper**. -/
theorem maskparity_succ_zero_rdiag_kit (s : Nat) :
    Rule30UOR.Scale.maskparity (s + 1) 0 =
      ((!Rule30UOR.Core.rdiag (s + 1) (s + 1)) && Rule30UOR.Core.rdiag s (s + 1)) :=
  Rule30Paper.Paper.maskparity_succ_zero_rdiag s

/-- **XOR Channel: `MaskedPer T P` Implies `MaskParityZeroPeriodic T P` under `CenterPeriodic T P` from the verified paper**. -/
theorem maskparity_zero_periodic_of_maskedper_kit (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hm : Rule30UOR.Right.MaskedPer T P) :
    Rule30UOR.Interfaces.MaskParityZeroPeriodic T P :=
  Rule30Paper.Paper.maskparity_zero_periodic_of_maskedper T P h hm

/-- **XOR Channel: `MaskParityZeroPeriodic T P` Implies `MaskedPer T P` under `CenterPeriodic T P` from the verified paper**. -/
theorem maskedper_of_maskparity_zero_periodic_kit (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hmp : Rule30UOR.Interfaces.MaskParityZeroPeriodic T P) :
    Rule30UOR.Right.MaskedPer T P :=
  Rule30Paper.Paper.maskedper_of_maskparity_zero_periodic T P h hmp

/-- **XOR Channel: `MaskedPer T P` Implies `P`-Periodicity of `maskparity · k` at All Scales from the verified paper**. -/
theorem maskparity_periodic_of_maskedper_kit (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hm : Rule30UOR.Right.MaskedPer T P)
    (t k : Nat) (ht : T + 1 ≤ t) :
    Rule30UOR.Scale.maskparity (t + P) k = Rule30UOR.Scale.maskparity t k :=
  Rule30Paper.Paper.maskparity_periodic_of_maskedper T P h hm t k ht

/-- **XOR Channel: Inside-the-Cone `P`-Shift of `maskparity` Equals `P`-Shift of `leftresponse` from the verified paper**. -/
theorem periodic_maskparity_shift_p_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor (Rule30UOR.Scale.maskparity (t + P) k) (Rule30UOR.Scale.maskparity t k) =
      Rule30UOR.Core.bxor (Rule30UOR.Scale.leftresponse (t + P) k) (Rule30UOR.Scale.leftresponse t k) :=
  Rule30Paper.Paper.periodic_maskparity_shift_p_cone T P hP h t k ht htP

/-- **XOR Channel: Inside-the-Cone Dyadic Jump of `maskparity · 0` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_maskparity_zero_dyadic_jump_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (hk : t + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (t + Rule30UOR.Core.twopow k) 0)
      (Rule30UOR.Scale.maskparity t 0) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (t + 1) k)
          (Rule30UOR.Scale.leftresponse t k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((t + 1) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (t + 1))
            (Rule30UOR.Core.center t))) :=
  Rule30Paper.Paper.periodic_maskparity_zero_dyadic_jump_cone T P hP h t k ht hk

/-- **XOR Channel: Inside-the-Cone Dyadic Jump of the `P`-Periodicity Defect of `maskparity · 0` from the verified paper**. -/
theorem periodic_maskparity_zero_defect_dyadic_jump_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((t + P) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity (t + Rule30UOR.Core.twopow k) 0))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity (t + P) 0)
        (Rule30UOR.Scale.maskparity t 0)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse ((t + P) + 1) k)
          (Rule30UOR.Scale.leftresponse (t + 1) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (t + P) k)
          (Rule30UOR.Scale.leftresponse t k)) :=
  Rule30Paper.Paper.periodic_maskparity_zero_defect_dyadic_jump_cone T P hP h t k ht htP

/-- **XOR Channel: Outside-the-Cone `P`-Shift of Late `maskparity (d + 2^k) k` from the verified paper**. -/
theorem periodic_late_maskparity_shift_p_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity ((d + P) + Rule30UOR.Core.twopow k) k)
      (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + P) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + P) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse d (k + 1))
          (Rule30UOR.Scale.leftresponse d k)) :=
  Rule30Paper.Paper.periodic_late_maskparity_shift_p T P hP h d k ht hk

/-- **XOR Channel: Outside-the-Cone Dyadic Jump of `maskparity · 0` Across `[d + 2^k, d + 2^(k+1)]` from the verified paper**. -/
theorem periodic_late_maskparity_zero_dyadic_jump_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + 1 ≤ k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow (k + 1)) 0)
      (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) 0) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
            (Rule30UOR.Scale.leftresponse (d + 1) k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse d (k + 1))
            (Rule30UOR.Scale.leftresponse d k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))) :=
  Rule30Paper.Paper.periodic_late_maskparity_zero_dyadic_jump T P hP h d k ht hk

/-- **XOR Channel: Outside-the-Cone Dyadic Jump of the `P`-Periodicity Defect of `maskparity · 0` from the verified paper**. -/
theorem periodic_late_maskparity_zero_defect_dyadic_jump_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P + 1 ≤ k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + P) + Rule30UOR.Core.twopow (k + 1)) 0)
        (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow (k + 1)) 0))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + P) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) 0)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse ((d + P) + 1) (k + 1))
            (Rule30UOR.Scale.leftresponse (d + 1) (k + 1)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (d + P) (k + 1))
            (Rule30UOR.Scale.leftresponse d (k + 1))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse ((d + P) + 1) k)
            (Rule30UOR.Scale.leftresponse (d + 1) k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (d + P) k)
            (Rule30UOR.Scale.leftresponse d k))) :=
  Rule30Paper.Paper.periodic_late_maskparity_zero_defect_dyadic_jump T P hP h d k ht hk

/-- **XOR Channel: Outside-the-Cone Late `leftresponse` Decomposition under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_late_leftresponse_unsettled_decomp_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow k) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k))
          (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_late_leftresponse_unsettled_decomp T P hP h d k ht hk

/-- **XOR Channel: Settled Late `leftresponse` + `maskparity` Decomposition of `zcenter d` from the verified paper**. -/
theorem periodic_zcenter_from_lag_late_left_mask_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) (hset : Rule30UOR.Interfaces.SettledAt d k) :
    Rule30UOR.Interfaces.ZCenterEq d
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow k) k)
          (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) k))) :=
  Rule30Paper.Paper.periodic_zcenter_from_lag_late_left_mask T P hP h d k ht hk hset

/-- **XOR Channel: `P`-Periodicity Defect of `maskparity · 0` Equals `P`-Periodicity Defect of Column `-1` from the verified paper**. -/
theorem periodic_maskparity_zero_defect_colm1_defect_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor (Rule30UOR.Scale.maskparity (t + P) 0) (Rule30UOR.Scale.maskparity t 0) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.cell (t + P) (Rule30UOR.Scale.negpow 0))
        (Rule30UOR.Core.cell t (Rule30UOR.Scale.negpow 0)) :=
  Rule30Paper.Paper.periodic_maskparity_zero_defect_colm1_defect T P hP h t ht

/-- **Two-Half Dyadic Scale Equation: General Late `rdiag` from `wittRespBool`, `leftresponse`, and `maskparity` from the verified paper**. -/
theorem rdiag_late_eq_witt_xor_left_mask_kit (r k : Nat) :
    Rule30UOR.Core.rdiag r (r + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool (r + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (r + Rule30UOR.Core.twopow k) k)
          (Rule30UOR.Scale.maskparity (r + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.rdiag_late_eq_witt_xor_left_mask r k

/-- **Two-Half Dyadic Scale Equation: Universal Two-Half Witt Scale Identity from the verified paper**. -/
theorem two_halves_witt_scale_kit (r k : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag r (r + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.ldiag r (r + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((r + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.center (r + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.wittRespBool (r + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.two_halves_witt_scale r k

/-- **Two-Half Dyadic Scale Equation: Cone-Wide Pure Left-Half Response Coboundary from the verified paper**. -/
theorem ldiag_leftresponse_coboundary_cone_kit (r k : Nat) (hr : r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.ldiag r (r + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse r (k + 1))
          (Rule30UOR.Scale.leftresponse r k))
        (Rule30UOR.Scale.leftresponse (r + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.ldiag_leftresponse_coboundary_cone r k hr

/-- **Two-Half Dyadic Scale Equation: Cone-Wide Two-Half Witt Dyadic Coboundary from the verified paper**. -/
theorem two_halves_witt_coboundary_cone_kit (r k : Nat) (hr : r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag r (r + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.ldiag r (r + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool r (k + 1))
          (Rule30UOR.Interfaces.wittRespBool r k))
        (Rule30UOR.Interfaces.wittRespBool (r + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.two_halves_witt_coboundary_cone r k hr

/-- **Two-Half Dyadic Scale Equation: Master Two-Half Scale Equation under `CenterPeriodic T P` (`T ≤ r < 2^k`) from the verified paper**. -/
theorem periodic_two_halves_scale_eq_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k : Nat) (ht : T ≤ r) (hr : r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag r (r + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.ldiag r (r + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Interfaces.wittRespBool (r + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_two_halves_scale_eq T P hP h r k ht hr

/-- **Two-Half Dyadic Scale Equation: Master Two-Half Scale Equation via `leftresponse` under `CenterPeriodic T P` (`T ≤ r < 2^k`) from the verified paper**. -/
theorem periodic_rdiag_late_from_left_and_center_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k : Nat) (ht : T ≤ r) (hr : r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag r (r + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittRespBool (r + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse r (k + 1))
            (Rule30UOR.Scale.leftresponse r k))
          (Rule30UOR.Scale.leftresponse (r + Rule30UOR.Core.twopow k) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k))) :=
  Rule30Paper.Paper.periodic_rdiag_late_from_left_and_center T P hP h r k ht hr

/-- **Two-Half Dyadic Scale Equation Below the Right Threshold (`r ≤ J`, `T ≤ r < 2^k`) from the verified paper**. -/
theorem periodic_two_halves_below_threshold_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k J : Nat) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (ht : T ≤ r) (hrJ : r ≤ J) (hr : r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.center r)
      (Rule30UOR.Core.ldiag r (r + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Interfaces.wittRespBool (r + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_two_halves_below_threshold T P hP h r k J hJ ht hrJ hr

/-- **Two-Half Dyadic Scale Equation At the Right Threshold (`r = J + 1`, `T ≤ J + 1 < 2^k`) from the verified paper**. -/
theorem periodic_two_halves_at_threshold_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (ht : T ≤ J + 1) (hJlt : J + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (!Rule30UOR.Core.center (J + 1))
      (Rule30UOR.Core.ldiag (J + 1) ((J + 1) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Interfaces.wittRespBool ((J + 1) + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_two_halves_at_threshold T P hP h k J hJ ht hJlt

/-- **Two-Half Dyadic Scale Equation via `leftresponse` At the Right Threshold (`r = J + 1`, `T ≤ J + 1 < 2^k`) from the verified paper**. -/
theorem periodic_not_center_xor_witt_at_threshold_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (ht : T ≤ J + 1) (hJlt : J + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (!Rule30UOR.Core.center (J + 1))
      (Rule30UOR.Interfaces.wittRespBool ((J + 1) + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (J + 1) (k + 1))
            (Rule30UOR.Scale.leftresponse (J + 1) k))
          (Rule30UOR.Scale.leftresponse ((J + 1) + Rule30UOR.Core.twopow k) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P k))) :=
  Rule30Paper.Paper.periodic_not_center_xor_witt_at_threshold T P hP h k J hJ ht hJlt

/-- **Triality Sector 1 Equating the Right Threshold Law (`d + 2 * s ≤ J`) and the Left Settled Law (`SettledBy d (d + s)`) from the verified paper**. -/
theorem sector_one_below_threshold_eq_left_settled_kit (d s k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s ≤ J) (hds : d + 2 * s < Rule30UOR.Core.twopow k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + s)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag ((d + 2 * s) + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.rdiag (d + 2 * s) ((d + s) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d ((d + s) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.sector_one_below_threshold_eq_left_settled d s k J hJ hk hdJ hds hset

/-- **Triality Sector 1 Equating the Right Antiperiodic Threshold Law (`d + 2 * s = J + 1`) and the Left Settled Law (`SettledBy d (d + s)`) from the verified paper**. -/
theorem sector_one_at_threshold_eq_left_settled_kit (d s k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s = J + 1) (hJlt : J + 1 < Rule30UOR.Core.twopow k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + s)) :
    (!Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag ((J + 1) + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.rdiag (J + 1) ((d + s) + Rule30UOR.Core.twopow k))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d ((d + s) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.sector_one_at_threshold_eq_left_settled d s k J hJ hk hdJ hJlt hset

/-- **Universal Right-System `2^k`-Defect Step Law At the Threshold (`j = J`) from the verified paper**. -/
theorem rdiag_threshold_plus_two_defect_step_kit (t k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) ((t + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag (J + 2) (t + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) (t + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag (J + 2) t)) =
      !Rule30UOR.Core.rdiag J t :=
  Rule30Paper.Paper.rdiag_threshold_plus_two_defect_step t k J hJ

/-- **Universal Right-System `2^k`-Defect Step Law At the Threshold in Left-Diagonal Coordinates (`d + 2 * s = J`) from the verified paper**. -/
theorem rdiag_threshold_plus_two_defect_step_ldiag_kit (d s k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (hdJ : d + 2 * s = J) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) (((d + s) + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag (J + 2) ((d + s) + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) ((d + s) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag (J + 2) (d + s))) =
      !Rule30UOR.Core.ldiag d (d + s) :=
  Rule30Paper.Paper.rdiag_threshold_plus_two_defect_step_ldiag d s k J hJ hdJ

/-- **Right-Diagonal Late Readout at `r = J + 2` from the verified paper**. -/
theorem rdiag_threshold_plus_two_center_decomp_kit (k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) :
    Rule30UOR.Core.rdiag (J + 2) ((J + 2) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (J + 2))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (J + 2) (J + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag (J + 2) J)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center J)
          (Rule30UOR.Core.rdiag J (J + 1))) :=
  Rule30Paper.Paper.rdiag_threshold_plus_two_center_decomp k J hJ

/-- **Two-Half Dyadic Scale Equation At `r = J + 2` under `CenterPeriodic T P` (`T ≤ J + 2 < 2^k`) from the verified paper**. -/
theorem periodic_two_halves_at_threshold_plus_two_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (ht : T ≤ J + 2) (hJlt : J + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (J + 2))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (J + 2) (J + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag (J + 2) J)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center J)
          (Rule30UOR.Core.rdiag J (J + 1))))
      (Rule30UOR.Core.ldiag (J + 2) ((J + 2) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((J + 2) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((J + 2) + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Interfaces.wittRespBool ((J + 2) + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_two_halves_at_threshold_plus_two T P hP h k J hJ ht hJlt

/-- **Left-System `2^k`-Damage Gating at the Settling Front (`SettledBy d s`, `SettledBy (d + 1) s`, `d + 1 ≤ k`) from the verified paper**. -/
theorem ldiag_damage_step_of_settled_pair_kit (d s k : Nat) (hk : d + 1 ≤ k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d s)
    (hset1 : Rule30UOR.Interfaces.SettledBy (d + 1) s) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.ldiag (d + 2) ((s + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.ldiag (d + 2) (s + 1)) =
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + 2) (s + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag (d + 2) s) &&
        !Rule30UOR.Core.ldiag (d + 1) s) :=
  Rule30Paper.Paper.ldiag_damage_step_of_settled_pair d s k hk hset0 hset1

/-- **Off-Center Two-Half Witt Scale Identity (`d + 2 * s < 2^k`) from the verified paper**. -/
theorem two_halves_off_center_witt_scale_kit (d s k : Nat)
    (hds : d + 2 * s < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitWinWittEq
      ((d + s) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.twopow k)
      ((d + 2 * s) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag (d + 2 * s) ((d + s) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag d ((d + s) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + s) + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k)))) :=
  Rule30Paper.Paper.two_halves_off_center_witt_scale d s k hds

/-- **Late Off-Center Witt Bit Below the Right Threshold on Settled Left Diagonals (`d + 2 * s ≤ J`) from the verified paper**. -/
theorem off_center_witt_scale_settled_below_threshold_kit (d s k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s ≤ J) (hds : d + 2 * s < Rule30UOR.Core.twopow k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + s)) :
    Rule30UOR.Interfaces.BitWinWittEq
      ((d + s) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.twopow k)
      ((d + 2 * s) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + s) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.off_center_witt_scale_settled_below_threshold d s k J hJ hk hdJ hds hset

/-- **Late Off-Center Witt Bit Inversion At the Right Threshold on Settled Left Diagonals (`d + 2 * s = J + 1`) from the verified paper**. -/
theorem off_center_witt_scale_settled_at_threshold_kit (d s k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s = J + 1) (hJlt : J + 1 < Rule30UOR.Core.twopow k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + s)) :
    Rule30UOR.Interfaces.BitWinWittEq
      ((d + s) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.twopow k)
      ((J + 1) + Rule30UOR.Core.twopow (k + 1))
      (!Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + s) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.off_center_witt_scale_settled_at_threshold d s k J hJ hk hdJ hJlt hset

/-- **Universal Dyadic Scale Jump of Column `-1` via `center` and `maskparity · 0` from the verified paper**. -/
theorem colm1_dyadic_jump_eq_maskparity_zero_jump_kit (d k : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
          (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (((d + 1) + Rule30UOR.Core.twopow (k + 1)) + 1))
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow (k + 1))))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (((d + 1) + Rule30UOR.Core.twopow k) + 1))
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k)))) :=
  Rule30Paper.Paper.colm1_dyadic_jump_eq_maskparity_zero_jump d k

/-- **Under `CenterPeriodic T P`, Dyadic Scale Jump of Column `-1` Equals `leftresponse` Second Difference from the verified paper**. -/
theorem periodic_colm1_dyadic_jump_eq_leftresponse_diff_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 2) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k)) :=
  Rule30Paper.Paper.periodic_colm1_dyadic_jump_eq_leftresponse_diff T P hP h d k ht hk

/-- **Exact Early `leftresponse` Formula for Late Off-Center Witt Bit Below the Right Threshold (`s = 1`, `d + 2 ≤ J`) from the verified paper**. -/
theorem periodic_off_center_witt_below_threshold_eq_leftresponse_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k J : Nat) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hdJ : d + 2 ≤ J)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + 1)) :
    Rule30UOR.Interfaces.BitWinWittEq
      ((d + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.twopow k)
      ((d + 2) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 2) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k))) :=
  Rule30Paper.Paper.periodic_off_center_witt_below_threshold_eq_leftresponse T P hP h d k J hJ ht hk hdJ hset

/-- **Exact Early `leftresponse` Inversion for Late Off-Center Witt Bit At the Right Threshold (`s = 1`, `d + 2 = J + 1`) from the verified paper**. -/
theorem periodic_off_center_witt_at_threshold_eq_not_leftresponse_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k J : Nat) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hdJ : d + 2 = J + 1)
    (hJlt : J + 1 < Rule30UOR.Core.twopow k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + 1)) :
    Rule30UOR.Interfaces.BitWinWittEq
      ((d + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.twopow k)
      ((J + 1) + Rule30UOR.Core.twopow (k + 1))
      (!Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 2) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k))) :=
  Rule30Paper.Paper.periodic_off_center_witt_at_threshold_eq_not_leftresponse T P hP h d k J hJ ht hk hdJ hJlt hset

/-- **Early-Time Evaluation of the Threshold Defect `rdiag (J + 2) (t0 + 2^k) ⊕ rdiag (J + 2) t0` Before Cone Arrival (`2 * t0 ≤ J + 1`) from the verified paper**. -/
theorem rdiag_threshold_plus_two_defect_cone_kit (t0 k J : Nat)
    (htJ : 2 * t0 ≤ J + 1) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag (J + 2) (t0 + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.rdiag (J + 2) t0) =
      Rule30UOR.Core.rdiag (J + 2) (t0 + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.rdiag_threshold_plus_two_defect_cone t0 k J htJ

/-- **2-Step Running Transport of the `rdiag (J + 2)` Defect (`t ↦ t + 2`) from the verified paper**. -/
theorem rdiag_threshold_plus_two_defect_two_step_kit (t k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) ((t + 2) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag (J + 2) (t + 2)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) (t + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag (J + 2) t)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag J t)
        (Rule30UOR.Core.rdiag J (t + 1)) :=
  Rule30Paper.Paper.rdiag_threshold_plus_two_defect_two_step t k J hJ

/-- **Exact Cross-Carry Decomposition of `carry (row (t0 + 2^k))` (Theorem 9.53 applied to Theorem 9.12) from the verified paper**. -/
theorem carry_row_scale_decomp_kit (t0 k : Nat) :
    Rule30UOR.Core.carry (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k)) =
      (Rule30UOR.Core.carry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0)) ^^^
        Rule30UOR.Core.carry (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) ^^^
        Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.carry_row_scale_decomp t0 k

/-- **Inside-the-Cone Cross-Carry Decomposition of `carry (row (t0 + 2^k))` from the verified paper**. -/
theorem carry_row_scale_cone_kit (t0 k : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.carry (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k)) =
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.carry (Rule30UOR.Core.row t0)) ^^^
        Rule30UOR.Core.carry (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) ^^^
        Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.carry_row_scale_cone t0 k hcone

/-- **Exact Cross-Carry Decomposition of the `winWitt` 1-Cocycle from the verified paper**. -/
theorem carry_winwitt_late_decomp_kit (t0 k : Nat) :
    Rule30UOR.Core.carry (Rule30UOR.Core.winWitt (t0 + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)) =
      (Rule30UOR.Core.carry (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow (k + 1))) ^^^
        Rule30UOR.Core.carry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)))) ^^^
        Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.carry_winwitt_late_decomp t0 k

/-- **Exact Center-Slot Cross-Carry Formula under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_crosscarry_center_slot_and_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (ht0 : t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
      (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
      ((t0 + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (t0 + 1) t0 &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.center t0))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag ((t0 + 1) + Rule30UOR.Core.twopow k) (t0 + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center t0)) :=
  Rule30Paper.Paper.periodic_crosscarry_center_slot_and T P hP h t0 k ht ht0

/-- **Exact Column-`-1` Cross-Carry Formula under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_crosscarry_colm1_and_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag d (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.center (d + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag d (d + 1)) &&
          Rule30UOR.Core.center (d + 1))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_and T P hP h d k ht hd

/-- **Exact Cross-Carry at the Right Threshold `J + 1` from the verified paper**. -/
theorem crosscarry_row_scale_at_threshold_eq_rdiag_kit (t0 k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hJlt : J + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
      (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
      (J + 1)
      (Rule30UOR.Core.rdiag J t0) :=
  Rule30Paper.Paper.crosscarry_row_scale_at_threshold_eq_rdiag t0 k J hJ hJlt

/-- **Exact Late-Row Carry at the Right Threshold `J + 1` from the verified paper**. -/
theorem carry_row_scale_at_threshold_kit (t0 k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hJlt : J + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCarryEq
      (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k))
      (J + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 1) t0 && Rule30UOR.Core.rdiag J t0)
        (Rule30UOR.Core.rdiag J t0)) :=
  Rule30Paper.Paper.carry_row_scale_at_threshold t0 k J hJ hJlt

/-- **Fully Expanded Center-Slot Step Law of `winWitt (t0 + 1) (2^k)` at `(t0 + 2) + 2^k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_winwitt_step_center_slot_expanded_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (hcone : 2 * t0 + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitWinWittEq
      (t0 + 1)
      (Rule30UOR.Core.twopow k)
      ((t0 + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag ((t0 + 2) + Rule30UOR.Core.twopow k) (t0 + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag (t0 + 2) t0))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.rdiag ((t0 + 1) + Rule30UOR.Core.twopow k) (t0 + Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.rdiag (t0 + 1) t0))
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
              (Rule30UOR.Core.center t0))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag ((t0 + 1) + Rule30UOR.Core.twopow k) (t0 + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag (t0 + 1) t0) &&
            Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.rdiag (t0 + 1) t0 &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
              (Rule30UOR.Core.center t0)))) :=
  Rule30Paper.Paper.periodic_winwitt_step_center_slot_expanded T P hP h t0 k ht hcone

/-- **Exact Cross-Carry at the Center Bit `(s + 1) + 2^k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_crosscarry_at_center_bit_and_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (s + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag s (s + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (s + 1)) &&
          Rule30UOR.Core.rdiag s (s + 1))) :=
  Rule30Paper.Paper.periodic_crosscarry_at_center_bit_and T P hP h s k ht hcone

/-- **Exact Cross-Carry at the Center Bit on White Center Steps (`maskparity (s + 1) 0` Channel) from the verified paper**. -/
theorem periodic_crosscarry_at_white_center_eq_maskparity_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) &&
        Rule30UOR.Scale.maskparity (s + 1) 0) :=
  Rule30Paper.Paper.periodic_crosscarry_at_white_center_eq_maskparity T P hP h s k ht hcone hw

/-- **Universal Complementary AND-Projection of Column `1` via `carry (row (s + 1))` and `maskparity (s + 1) 0` from the verified paper**. -/
theorem carry_row_xor_maskparity_zero_eq_col1_kit (s : Nat) :
    Rule30UOR.Interfaces.BitCarryEq
      (Rule30UOR.Core.row (s + 1))
      (s + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag s (s + 1))
        (Rule30UOR.Scale.maskparity (s + 1) 0)) :=
  Rule30Paper.Paper.carry_row_xor_maskparity_zero_eq_col1 s

/-- **White-Center Annihilation of the Late Column-`-1` Term in `crossCarry` from the verified paper**. -/
theorem periodic_crosscarry_colm1_at_white_center_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.ldiag d (d + 1) &&
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_at_white_center T P hP h d k ht hd hw

/-- **Repeat-Lag Scale Invariance of `crossCarry` at `(d + 2) + 2^k` on White Center Steps from the verified paper**. -/
theorem periodic_crosscarry_colm1_white_center_lag_eq_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d + 1) (hd1 : d + 2 < Rule30UOR.Core.twopow k1) (hd2 : d + 2 < Rule30UOR.Core.twopow k2)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    Rule30UOR.Core.bit
      (Rule30UOR.Interfaces.crossCarry
        (Rule30UOR.Core.phiScale k1 (Rule30UOR.Core.row (d + 1)))
        (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k1)))
      ((d + 2) + Rule30UOR.Core.twopow k1) =
    Rule30UOR.Core.bit
      (Rule30UOR.Interfaces.crossCarry
        (Rule30UOR.Core.phiScale k2 (Rule30UOR.Core.row (d + 1)))
        (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k2)))
      ((d + 2) + Rule30UOR.Core.twopow k2) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_white_center_lag_eq T P hP h d k1 k2 hlag ht hd1 hd2 hw

/-- **Exact Sector-2 Cross-Carry at Bit `(d + 2) + 2^(k+1)` from the verified paper**. -/
theorem crosscarry_row_scale_sector_two_colm1_and_kit (d k : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag d (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (d + 1))
            (Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag d (d + 1))
          (Rule30UOR.Core.ldiag d ((d + 1) + Rule30UOR.Core.twopow k)) &&
          Rule30UOR.Core.center (d + 1))) :=
  Rule30Paper.Paper.crosscarry_row_scale_sector_two_colm1_and d k hk

/-- **White-Center Annihilation in Sector 2 at `(d + 2) + 2^(k+1)` from the verified paper**. -/
theorem crosscarry_row_scale_sector_two_colm1_at_white_center_kit (d k : Nat) (hk : d + 1 ≤ k)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.ldiag d (d + 1) &&
        Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.crosscarry_row_scale_sector_two_colm1_at_white_center d k hk hw

/-- **Homogeneous Triality Sector 1 ⊕ Sector 2 Cross-Carry Coupling under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_crosscarry_sector_one_xor_two_colm1_and_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hd : d + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryXorEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      ((d + 2) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag d (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag d ((d + 1) + Rule30UOR.Core.twopow k)) &&
          Rule30UOR.Core.center (d + 1))) :=
  Rule30Paper.Paper.periodic_crosscarry_sector_one_xor_two_colm1_and T P hP h d k ht hk hd

/-- **Pure Late-Slice Readout of `phiScale k (winWitt (d + s) (2^k))` in the Low-Bit Zone (`d + 2 * s ≤ k`) from the verified paper**. -/
theorem phiscale_winwitt_triality_low_kit (d s k : Nat) (hk : d + 2 * s ≤ k) :
    Rule30UOR.Core.bit
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt (d + s) (Rule30UOR.Core.twopow k)))
      ((d + 2 * s) + Rule30UOR.Core.twopow (k + 1)) =
    Rule30UOR.Interfaces.bton
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + s) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d ((d + s) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.phiscale_winwitt_triality_low d s k hk

/-- **Exact Bilinear Cross-Carry of the `winWitt` 1-Cocycle at Bit `(d + 2) + 2^(k+1)` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_crosscarry_winwitt_cocycle_colm1_and_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k)))
      ((d + 2) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Core.ldiag d (d + 1)) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag d ((d + 1) + Rule30UOR.Core.twopow k)) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + 1)))) :=
  Rule30Paper.Paper.periodic_crosscarry_winwitt_cocycle_colm1_and T P hP h d k ht hk

/-- **Exact Swap of Witt Row Carry and Rule-60 Masked Carry at the Right-Period Threshold from the verified paper**. -/
theorem carry_row_late_at_threshold_center_eq_maskparity_kit (k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (hJlt : J + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCarryEq
      (Rule30UOR.Core.row ((J + 1) + Rule30UOR.Core.twopow k))
      (J + 1)
      (Rule30UOR.Scale.maskparity (J + 1) 0) :=
  Rule30Paper.Paper.carry_row_late_at_threshold_center_eq_maskparity k J hJ hJlt

/-- **Unconditional Decomposition of the `maskparity · 0` Dyadic Jump via `carry` and `crossCarry` from the verified paper**. -/
theorem maskparity_zero_dyadic_jump_eq_witt_carry_crosscarry_kit (s k : Nat)
    (hcone : s + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitWinWittEq
      (s + 1) (Rule30UOR.Core.twopow k) (s + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)
          (Rule30UOR.Scale.maskparity (s + 1) 0))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag s (s + 1)) &&
            Rule30UOR.Interfaces.wittRespBool (s + 1) k)
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (s + 1) &&
              Rule30UOR.Core.bxor
                (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
                (Rule30UOR.Core.rdiag s (s + 1)))
            (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
              Rule30UOR.Core.rdiag s (s + 1))))) :=
  Rule30Paper.Paper.maskparity_zero_dyadic_jump_eq_witt_carry_crosscarry s k hcone

/-- **Factored AND-Structure of the `maskparity · 0` Dyadic Jump from the verified paper**. -/
theorem maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crosscarry_kit (s k : Nat)
    (hcone : s + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)
          (Rule30UOR.Scale.maskparity (s + 1) 0))
        ((!Rule30UOR.Interfaces.wittRespBool (s + 1) k) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag s (s + 1)))) :=
  Rule30Paper.Paper.maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crosscarry s k hcone

/-- **Exact Equality of the `maskparity · 0` Dyadic Jump and `crossCarry` on Out-of-Phase Steps from the verified paper**. -/
theorem maskparity_dyadic_jump_eq_crosscarry_of_wittresp_true_kit (s k : Nat)
    (hcone : s + 2 < Rule30UOR.Core.twopow k) (hw : Rule30UOR.Interfaces.wittRespBool (s + 1) k = true) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity (s + 1) 0)) :=
  Rule30Paper.Paper.maskparity_dyadic_jump_eq_crosscarry_of_wittresp_true s k hcone hw

/-- **Exact Equality of the `maskparity · 0` Dyadic Jump on In-Phase Steps from the verified paper**. -/
theorem maskparity_dyadic_jump_eq_not_center_and_witt_of_wittresp_false_kit (s k : Nat)
    (hcone : s + 2 < Rule30UOR.Core.twopow k) (hw : Rule30UOR.Interfaces.wittRespBool (s + 1) k = false) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)
      (Rule30UOR.Scale.maskparity (s + 1) 0) =
    ((!Rule30UOR.Core.center (s + 1)) &&
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.rdiag s (s + 1))) :=
  Rule30Paper.Paper.maskparity_dyadic_jump_eq_not_center_and_witt_of_wittresp_false s k hcone hw

/-- **Direct Two-Halves Bridge Locking `leftresponse` Derivative to `crossCarry` on Out-of-Phase Steps from the verified paper**. -/
theorem periodic_leftresponse_step_diff_eq_crosscarry_of_out_of_phase_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.wittRespBool (s + 1) k = true) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (s + 2) k)
          (Rule30UOR.Scale.leftresponse (s + 1) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((s + 2) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center (s + 2))
            (Rule30UOR.Core.center (s + 1))))) :=
  Rule30Paper.Paper.periodic_leftresponse_step_diff_eq_crosscarry_of_out_of_phase T P hP h s k ht hcone hw

/-- **1-Cocycle Cross-Carry Collapse at `J + 2` from the verified paper**. -/
theorem crosscarry_winwitt_cocycle_at_threshold_succ_kit (t0 k J : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (hJlt : J + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)))
      (J + 2)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (J + 2) (t0 + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.rdiag (J + 2) t0)) :=
  Rule30Paper.Paper.crosscarry_winwitt_cocycle_at_threshold_succ t0 k J hJ hJlt

/-- **Exact Equality of Scaled-Window Cross-Carry and Early-Late Row Cross-Carry from the verified paper**. -/
theorem crosscarry_row_scale_eq_crosscarry_late_row_kit (t0 k : Nat) :
    Rule30UOR.Interfaces.crossCarry
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
      (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) =
    Rule30UOR.Interfaces.crossCarry
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
      (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.crosscarry_row_scale_eq_crosscarry_late_row t0 k

/-- **Pure 2×2 Wronskian Formula for Column-`-1` Cross-Carry under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_crosscarry_colm1_wronskian_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag d (d + 1) &&
          Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.center (d + 1))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_wronskian T P hP h d k ht hd

/-- **Pure 2×2 Wronskian Formula for Sector-2 Column-`-1` Cross-Carry from the verified paper**. -/
theorem crosscarry_row_scale_sector_two_colm1_wronskian_kit (d k : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag d (d + 1) &&
          Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d ((d + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.center (d + 1))) :=
  Rule30Paper.Paper.crosscarry_row_scale_sector_two_colm1_wronskian d k hk

/-- **Universal Annihilation of `maskparity · 0` by `center` from the verified paper**. -/
theorem maskparity_zero_and_center_eq_false_kit (t : Nat) :
    (Rule30UOR.Scale.maskparity t 0 && Rule30UOR.Core.center t) = false :=
  Rule30Paper.Paper.maskparity_zero_and_center_eq_false t

/-- **Black-Center Annihilation of the Column-`-1` `P`-Periodicity Defect under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_colm1_defect_and_center_eq_false_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d : Nat) (ht : T ≤ d + 1) :
    (Rule30UOR.Core.bxor
      (Rule30UOR.Core.ldiag (d + P) ((d + P) + 1))
      (Rule30UOR.Core.ldiag d (d + 1)) &&
      Rule30UOR.Core.center (d + 1)) = false :=
  Rule30Paper.Paper.periodic_colm1_defect_and_center_eq_false T P hP h d ht

/-- **Factored `P`-Shift Defect of the Column-`-1` Cross-Carry via `leftresponse` and `wittRespBool` from the verified paper**. -/
theorem periodic_crosscarry_colm1_shift_p_eq_leftresponse_and_witt_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row ((d + P) + 1)))
      (Rule30UOR.Core.winWitt ((d + P) + 1) (Rule30UOR.Core.twopow k))
      (((d + P) + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag d (d + 1) &&
            Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.center (d + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse ((d + P) + 2) k)
            (Rule30UOR.Scale.leftresponse (d + 2) k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse ((d + P) + 1) k)
            (Rule30UOR.Scale.leftresponse (d + 1) k)) &&
          Rule30UOR.Interfaces.wittRespBool (d + 1) k)) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_shift_p_eq_leftresponse_and_witt T P hP h d k ht hdP

/-- **Exact `P`-Periodicity of the Column-`-1` Cross-Carry on In-Phase Steps from the verified paper**. -/
theorem periodic_crosscarry_colm1_shift_p_eq_of_wittresp_false_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.wittRespBool (d + 1) k = false) :
    Rule30UOR.Core.bit
      (Rule30UOR.Interfaces.crossCarry
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row ((d + P) + 1)))
        (Rule30UOR.Core.winWitt ((d + P) + 1) (Rule30UOR.Core.twopow k)))
      (((d + P) + 2) + Rule30UOR.Core.twopow k) =
    Rule30UOR.Core.bit
      (Rule30UOR.Interfaces.crossCarry
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
        (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k)))
      ((d + 2) + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_shift_p_eq_of_wittresp_false T P hP h d k ht hdP hw

/-- **Exact Locking of 1-Step `leftresponse` Derivative to `wittRespBool (s + 2) k` on In-Phase Black Center Steps from the verified paper**. -/
theorem periodic_leftresponse_step_diff_eq_witt_of_in_phase_black_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < Rule30UOR.Core.twopow k)
    (hblk : Rule30UOR.Core.center (s + 1) = true)
    (hw : Rule30UOR.Interfaces.wittRespBool (s + 1) k = false) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.leftresponse (s + 2) k)
      (Rule30UOR.Scale.leftresponse (s + 1) k) =
    Rule30UOR.Interfaces.wittRespBool (s + 2) k :=
  Rule30Paper.Paper.periodic_leftresponse_step_diff_eq_witt_of_in_phase_black T P hP h s k ht hcone hblk hw

/-- **Three-Copy Readout of `phiScale k (row t0)` Outside the Cone (`twopow k ≤ r`) from the verified paper**. -/
theorem phiscale_row_testbit_outside_cone_kit (t0 k r : Nat)
    (hr : Rule30UOR.Core.twopow k ≤ r) :
    Rule30UOR.Core.bit
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
      (r + Rule30UOR.Core.twopow k) =
    Rule30UOR.Interfaces.bton
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag (r + Rule30UOR.Core.twopow k) t0)
          (Rule30UOR.Core.rdiag r t0))
        (Rule30UOR.Core.rdiag (r - Rule30UOR.Core.twopow k) t0)) :=
  Rule30Paper.Paper.phiscale_row_testbit_outside_cone t0 k r hr

/-- **Four-Term Readout of `winWitt t0 (2^k)` Outside the Cone (`twopow k ≤ r`) from the verified paper**. -/
theorem winwitt_testbit_outside_cone_kit (t0 k r : Nat)
    (hr : Rule30UOR.Core.twopow k ≤ r) :
    Rule30UOR.Interfaces.BitWinWittEq t0 (Rule30UOR.Core.twopow k)
      (r + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag (r + Rule30UOR.Core.twopow k) (t0 + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (r + Rule30UOR.Core.twopow k) t0)
            (Rule30UOR.Core.rdiag r t0))
          (Rule30UOR.Core.rdiag (r - Rule30UOR.Core.twopow k) t0))) :=
  Rule30Paper.Paper.winwitt_testbit_outside_cone t0 k r hr

/-- **Direct Scaled-Row × Window Cross-Carry at `(d + 2) + 2^k` Outside the Cone from the verified paper**. -/
theorem periodic_crosscarry_colm1_outside_cone_and_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : Rule30UOR.Core.twopow k ≤ d) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1))
            (Rule30UOR.Core.ldiag d (d + 1)))
          (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1)) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.bxor
                (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
                (Rule30UOR.Core.center (d + 1)))
              (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.ldiag d (d + 1)))
            (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1))) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.center (d + 1)))
            (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_outside_cone_and T P hP h d k ht hd

/-- **Wronskian Form of Column-`-1` Cross-Carry Outside the Cone from the verified paper**. -/
theorem periodic_crosscarry_colm1_outside_cone_wronskian_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : Rule30UOR.Core.twopow k ≤ d) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1))
            (Rule30UOR.Core.ldiag d (d + 1)))
          (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1)) &&
          Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.center (d + 1)))
            (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_outside_cone_wronskian T P hP h d k ht hd

/-- **Theorem 9.152 Outside the Cone (`periodic_crosscarry_colm1_outside_cone_at_white_center`) from the verified paper**. -/
theorem periodic_crosscarry_colm1_outside_cone_at_white_center_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : Rule30UOR.Core.twopow k ≤ d)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1))
            (Rule30UOR.Core.ldiag d (d + 1)))
          (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1)) &&
          Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
            (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_outside_cone_at_white_center T P hP h d k ht hd hw

/-- **Pure Non-Center AND-Product at `(d + 2) + 2^k` Outside the Cone on White Early and Late Centers from the verified paper**. -/
theorem periodic_crosscarry_colm1_outside_cone_at_both_white_centers_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : Rule30UOR.Core.twopow k ≤ d)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
        Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
          (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_outside_cone_at_both_white_centers T P hP h d k ht hd hw1 hw2

/-- **Universal Reduction of Column-`-1` Cross-Carry on White Late Center Steps from the verified paper**. -/
theorem crosscarry_colm1_at_white_late_center_eq_and_witt_kit (d k : Nat)
    (hw : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
        Rule30UOR.Interfaces.wittRespBool (d + 1) k) :=
  Rule30Paper.Paper.crosscarry_colm1_at_white_late_center_eq_and_witt d k hw

/-- **Outside-the-Cone Column-`-1` Cross-Carry on White Late Center Steps via `response` and `rdiag` from the verified paper**. -/
theorem crosscarry_colm1_outside_cone_at_white_late_center_via_response_kit (d k : Nat)
    (hd : Rule30UOR.Core.twopow k ≤ d + 1)
    (hw : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
      (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k))
      ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
        Rule30UOR.Core.bxor
          (Rule30UOR.Scale.response (d + 1) k)
          (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))) :=
  Rule30Paper.Paper.crosscarry_colm1_outside_cone_at_white_late_center_via_response d k hd hw

/-- **Exact Cross-Carry at the Center Bit `(s + 1) + 2^k` Outside the Cone from the verified paper**. -/
theorem crosscarry_row_scale_at_center_bit_outside_cone_and_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1))
            (Rule30UOR.Core.center (s + 1)))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1)) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.bxor
                (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
                (Rule30UOR.Core.rdiag s (s + 1)))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1))))
        (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Core.rdiag s (s + 1)))
            (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))) :=
  Rule30Paper.Paper.crosscarry_row_scale_at_center_bit_outside_cone_and s k hs

/-- **Theorem 9.152 Outside the Cone at the Center Slot on White Center Steps from the verified paper**. -/
theorem crosscarry_at_white_center_outside_cone_noncenter_and_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1)) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.bxor
                (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
                (Rule30UOR.Core.rdiag s (s + 1)))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1))))
        (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Core.rdiag s (s + 1)))
            (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))) :=
  Rule30Paper.Paper.crosscarry_at_white_center_outside_cone_noncenter_and s k hs hw

/-- **Universal Wronskian Form of the Center-Slot Cross-Carry Outside the Cone from the verified paper**. -/
theorem crosscarry_at_center_bit_outside_cone_wronskian_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1))
            (Rule30UOR.Core.center (s + 1)))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1)) &&
          Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Core.rdiag s (s + 1)))
            (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))) :=
  Rule30Paper.Paper.crosscarry_at_center_bit_outside_cone_wronskian s k hs

/-- **Pure Non-Center AND-Product at the Center Slot `(s + 1) + 2^k` Outside the Cone on White Early and Late Centers from the verified paper**. -/
theorem periodic_crosscarry_at_both_white_centers_outside_cone_eq_maskparity_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : Rule30UOR.Core.twopow k ≤ s)
    (hw1 : Rule30UOR.Core.center (s + 1) = false)
    (hw2 : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1))
        (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1)) &&
        Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0) :=
  Rule30Paper.Paper.periodic_crosscarry_at_both_white_centers_outside_cone_eq_maskparity T P hP h s k ht hs hw1 hw2

/-- **Universal Reduction of Center-Slot Cross-Carry on White Late Center Steps from the verified paper**. -/
theorem crosscarry_at_white_late_center_eq_witt_and_maskparity_kit (s k : Nat)
    (hw : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 1)))
      (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k))
      ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
        Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0) :=
  Rule30Paper.Paper.crosscarry_at_white_late_center_eq_witt_and_maskparity s k hw

/-- **Under `CenterPeriodic T P`, `m * P`-Periodicity of `maskparity · 0` Equals `m * P`-Periodicity of Column `-1` from the verified paper**. -/
theorem periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d : Nat) (ht : T ≤ d + 1) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity ((d + m * P) + 1) 0)
      (Rule30UOR.Scale.maskparity (d + 1) 0) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.ldiag (d + m * P) ((d + m * P) + 1))
      (Rule30UOR.Core.ldiag d (d + 1)) :=
  Rule30Paper.Paper.periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul T P hP h m d ht

/-- **Fixed-`k` Unbounded-`t` Outside-the-Cone `m * P`-Shift of `wittRespBool` vs `response` from the verified paper**. -/
theorem wittresp_xor_response_shift_mul_outside_cone_kit (t k m P : Nat)
    (hk : Rule30UOR.Core.twopow k ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool (t + m * P) k)
        (Rule30UOR.Interfaces.wittRespBool t k))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.response (t + m * P) k)
        (Rule30UOR.Scale.response t k)) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.rdiag ((t + m * P) - Rule30UOR.Core.twopow k) (t + m * P))
      (Rule30UOR.Core.rdiag (t - Rule30UOR.Core.twopow k) t) :=
  Rule30Paper.Paper.wittresp_xor_response_shift_mul_outside_cone t k m P hk

/-- **Fixed-`k` Unbounded-`t` Outside-the-Cone `m * P`-Shift of `wittRespBool` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_wittresp_shift_mul_outside_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k m : Nat) (ht : T ≤ t) (hk : Rule30UOR.Core.twopow k ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittRespBool (t + m * P) k)
      (Rule30UOR.Interfaces.wittRespBool t k) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag ((t + m * P) - Rule30UOR.Core.twopow k) (t + m * P))
        (Rule30UOR.Core.ldiag (t - Rule30UOR.Core.twopow k) t))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag ((t + m * P) - Rule30UOR.Core.twopow k) (t + m * P))
        (Rule30UOR.Core.rdiag (t - Rule30UOR.Core.twopow k) t)) :=
  Rule30Paper.Paper.periodic_wittresp_shift_mul_outside_cone T P hP h t k m ht hk

/-- **Fixed-`k` Unbounded-`d` `m * P`-Shift of Column-`-1` Cross-Carry on White Late Centers from the verified paper**. -/
theorem periodic_crosscarry_colm1_shift_mul_at_white_late_center_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1)
    (hw : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (((d + m * P) + 1))))
      (Rule30UOR.Core.winWitt (((d + m * P) + 1)) (Rule30UOR.Core.twopow k))
      ((((d + m * P) + 2) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Interfaces.wittRespBool (d + 1) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + Rule30UOR.Core.twopow k) 0)
            (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0) &&
            Rule30UOR.Interfaces.wittRespBool ((d + m * P) + 1) k)
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Interfaces.wittRespBool ((d + m * P) + 1) k)
              (Rule30UOR.Interfaces.wittRespBool (d + 1) k)))) :=
  Rule30Paper.Paper.periodic_crosscarry_colm1_shift_mul_at_white_late_center T P hP h m d k ht hw

/-- **Fixed-`k` Unbounded-`s` `m * P`-Shift of Center-Slot Cross-Carry on White Late Centers from the verified paper**. -/
theorem periodic_crosscarry_center_bit_shift_mul_at_white_late_center_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m s k : Nat) (ht : T ≤ s + 1)
    (hw : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (((s + m * P) + 1))))
      (Rule30UOR.Core.winWitt (((s + m * P) + 1)) (Rule30UOR.Core.twopow k))
      ((((s + m * P) + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
          Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.wittRespBool ((s + m * P) + 1) k)
            (Rule30UOR.Interfaces.wittRespBool (s + 1) k) &&
            Rule30UOR.Scale.maskparity (((s + m * P) + 1) + Rule30UOR.Core.twopow k) 0)
          (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Scale.maskparity (((s + m * P) + 1) + Rule30UOR.Core.twopow k) 0)
              (Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)))) :=
  Rule30Paper.Paper.periodic_crosscarry_center_bit_shift_mul_at_white_late_center T P hP h m s k ht hw

/-- **In-Cone Vanishing of the Frobenius Defect from the verified paper**. -/
theorem frobdefect_row_cone_eq_zero_kit (t0 k : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t0) = 0 :=
  Rule30Paper.Paper.frobdefect_row_cone_eq_zero t0 k hcone

/-- **Universal Window Step Equation with the Frobenius Defect from the verified paper**. -/
theorem winwitt_step_frobdefect_kit (t0 k : Nat) :
    Rule30UOR.Core.winWitt (t0 + 1) (Rule30UOR.Core.twopow k) =
      ((Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) ^^^
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) <<< 1)) ^^^
        (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t0) <<< 1)) :=
  Rule30Paper.Paper.winwitt_step_frobdefect t0 k

/-- **Bitwise Universal Window Step at Bit `j + 1` from the verified paper**. -/
theorem winwitt_step_frobdefect_testbit_succ_kit (t0 k j : Nat) :
    Rule30UOR.Interfaces.BitWinWittEq (t0 + 1) (Rule30UOR.Core.twopow k) (j + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) (j + 1))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
              (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) j))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t0)) j)) :=
  Rule30Paper.Paper.winwitt_step_frobdefect_testbit_succ t0 k j

/-- **General Outside-the-Cone Bit Readout of `frobDefect k (row t0)` at `(r + 1) + 2^k` from the verified paper**. -/
theorem frobdefect_row_testbit_outside_cone_kit (t0 k r : Nat)
    (hr : Rule30UOR.Core.twopow k ≤ r) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row t0) ((r + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag ((r + 1) + Rule30UOR.Core.twopow k) t0 &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag r t0) (Rule30UOR.Core.rdiag (r - Rule30UOR.Core.twopow k) t0))
          (Rule30UOR.Core.rdiag (r + 1) t0 &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (r + Rule30UOR.Core.twopow k) t0)
              (Rule30UOR.Core.rdiag (r - Rule30UOR.Core.twopow k) t0)))
        (Rule30UOR.Core.rdiag ((r + 1) - Rule30UOR.Core.twopow k) t0 &&
          Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (r + Rule30UOR.Core.twopow k) t0)
            (Rule30UOR.Core.rdiag r t0))) :=
  Rule30Paper.Paper.frobdefect_row_testbit_outside_cone t0 k r hr

/-- **Center-Slot Frobenius Defect Outside the Cone from the verified paper**. -/
theorem frobdefect_row_center_slot_outside_cone_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (s + 1)) ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag s (s + 1))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))
          (Rule30UOR.Core.center (s + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1))))
        (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
          Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
            (Rule30UOR.Core.rdiag s (s + 1)))) :=
  Rule30Paper.Paper.frobdefect_row_center_slot_outside_cone s k hs

/-- **White-Center Center-Slot Frobenius Defect Outside the Cone from the verified paper**. -/
theorem frobdefect_row_center_slot_at_white_center_outside_cone_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (s + 1)) ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
          Rule30UOR.Core.bxor (Rule30UOR.Scale.maskparity (s + 1) 0)
            (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))
        (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
          Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
            (Rule30UOR.Scale.maskparity (s + 1) 0))) :=
  Rule30Paper.Paper.frobdefect_row_center_slot_at_white_center_outside_cone s k hs hw

/-- **Column-`-1` Slot Frobenius Defect Outside the Cone from the verified paper**. -/
theorem frobdefect_row_colm1_slot_outside_cone_kit (d k : Nat)
    (hd : Rule30UOR.Core.twopow k ≤ d) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (d + 1)) ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.center (d + 1))
              (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))
          (Rule30UOR.Core.ldiag d (d + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))))
        (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1) &&
          Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
            (Rule30UOR.Core.center (d + 1)))) :=
  Rule30Paper.Paper.frobdefect_row_colm1_slot_outside_cone d k hd

/-- **White-Center Column-`-1` Slot Frobenius Defect Outside the Cone from the verified paper**. -/
theorem frobdefect_row_colm1_slot_at_white_center_outside_cone_kit (d k : Nat)
    (hd : Rule30UOR.Core.twopow k ≤ d)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (d + 1)) ((d + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1) &&
            Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
          (Rule30UOR.Core.ldiag d (d + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))))
        (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1) &&
          Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))) :=
  Rule30Paper.Paper.frobdefect_row_colm1_slot_at_white_center_outside_cone d k hd hw

/-- **Column-`+1` Slot Frobenius Defect Outside the Cone from the verified paper**. -/
theorem frobdefect_row_col1_slot_outside_cone_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (s + 2)) ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((s + 3) - Rule30UOR.Core.twopow k) (s + 2) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag s (s + 2))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 2)))
          (Rule30UOR.Core.rdiag (s + 1) (s + 2) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) (s + 2))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 2))))
        (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 2) &&
          Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) (s + 2))
            (Rule30UOR.Core.rdiag s (s + 2)))) :=
  Rule30Paper.Paper.frobdefect_row_col1_slot_outside_cone s k hs

/-- **White-Center Column-`+1` Slot Frobenius Defect Outside the Cone from the verified paper**. -/
theorem frobdefect_row_col1_slot_at_white_center_outside_cone_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 2) = false) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (s + 2)) ((s + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((s + 3) - Rule30UOR.Core.twopow k) (s + 2) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag s (s + 2))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 2)))
          (Rule30UOR.Scale.maskparity (s + 2) 0 &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) (s + 2))
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 2))))
        (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 2) &&
          Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) (s + 2))
            (Rule30UOR.Core.rdiag s (s + 2)))) :=
  Rule30Paper.Paper.frobdefect_row_col1_slot_at_white_center_outside_cone s k hs hw

/-- **Periodic Window Step Outside the Cone at the Center Slot from the verified paper**. -/
theorem periodic_winwitt_step_center_slot_outside_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : Rule30UOR.Core.twopow k ≤ s) :
    Rule30UOR.Interfaces.wittRespBool (s + 2) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k)))
            ((s + 2) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.bxor
                (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1))
                (Rule30UOR.Core.center (s + 1)))
              (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1)) &&
              Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) ((s + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) &&
              Rule30UOR.Core.bxor
                (Rule30UOR.Core.bxor
                  (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
                  (Rule30UOR.Core.rdiag s (s + 1)))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag s (s + 1))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))
            (Rule30UOR.Core.center (s + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1))))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Core.rdiag s (s + 1)))) :=
  Rule30Paper.Paper.periodic_winwitt_step_center_slot_outside_cone T P hP h s k ht hs

/-- **Periodic Window Step Outside the Cone at the Center Slot on White Late Center Steps from the verified paper**. -/
theorem periodic_winwitt_step_center_slot_at_white_late_center_outside_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : Rule30UOR.Core.twopow k ≤ s)
    (hw : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.wittRespBool (s + 2) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k)))
            ((s + 2) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
            Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag s (s + 1))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))
            (Rule30UOR.Core.center (s + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1))))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Core.rdiag s (s + 1)))) :=
  Rule30Paper.Paper.periodic_winwitt_step_center_slot_at_white_late_center_outside_cone T P hP h s k ht hs hw

/-- **Periodic Window Step Outside the Cone at the Center Slot on White Early and Late Centers from the verified paper**. -/
theorem periodic_winwitt_step_center_slot_at_both_white_centers_outside_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : Rule30UOR.Core.twopow k ≤ s)
    (hw1 : Rule30UOR.Core.center (s + 1) = false)
    (hw2 : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.wittRespBool (s + 2) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k)))
            ((s + 2) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1))
            (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1)) &&
            Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Scale.maskparity (s + 1) 0)
              (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 1)))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((s + 2) - Rule30UOR.Core.twopow k) (s + 1))
              (Rule30UOR.Scale.maskparity (s + 1) 0))) :=
  Rule30Paper.Paper.periodic_winwitt_step_center_slot_at_both_white_centers_outside_cone T P hP h s k ht hs hw1 hw2

/-- **Periodic Window Step Outside the Cone at the Column-`-1` Slot from the verified paper**. -/
theorem periodic_winwitt_step_colm1_slot_outside_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : Rule30UOR.Core.twopow k ≤ d) :
    Rule30UOR.Interfaces.BitWinWittEq (d + 2) (Rule30UOR.Core.twopow k) ((d + 3) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k)))
            ((d + 3) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Core.bxor
                (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1))
                (Rule30UOR.Core.ldiag d (d + 1)))
              (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1)) &&
              Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
            (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
              Rule30UOR.Core.bxor
                (Rule30UOR.Core.bxor
                  (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
                  (Rule30UOR.Core.center (d + 1)))
                (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.center (d + 1))
                (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))
            (Rule30UOR.Core.ldiag d (d + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
                (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))))
          (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.center (d + 1))))) :=
  Rule30Paper.Paper.periodic_winwitt_step_colm1_slot_outside_cone T P hP h d k ht hd

/-- **Periodic Window Step Outside the Cone at the Column-`-1` Slot on White Early and Late Centers from the verified paper**. -/
theorem periodic_winwitt_step_colm1_slot_at_both_white_centers_outside_cone_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : Rule30UOR.Core.twopow k ≤ d)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Interfaces.BitWinWittEq (d + 2) (Rule30UOR.Core.twopow k) ((d + 3) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k)))
            ((d + 3) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
              (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d - Rule30UOR.Core.twopow k) (d + 1) &&
              Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
            (Rule30UOR.Core.ldiag d (d + 1) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))
                (Rule30UOR.Core.rdiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1))))
          (Rule30UOR.Core.rdiag ((d + 2) - Rule30UOR.Core.twopow k) (d + 1) &&
            Rule30UOR.Core.ldiag ((d + 1) - Rule30UOR.Core.twopow k) (d + 1)))) :=
  Rule30Paper.Paper.periodic_winwitt_step_colm1_slot_at_both_white_centers_outside_cone T P hP h d k ht hd hw1 hw2

/-- **Periodic Window Step Outside the Cone at the Column-`+1` Slot from the verified paper**. -/
theorem periodic_winwitt_step_col1_slot_outside_cone_kit (s k : Nat)
    (hs : Rule30UOR.Core.twopow k ≤ s) :
    Rule30UOR.Interfaces.BitWinWittEq (s + 3) (Rule30UOR.Core.twopow k) ((s + 2) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (s + 2) (Rule30UOR.Core.twopow k)))
            ((s + 2) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (s + 2)))
              (Rule30UOR.Core.winWitt (s + 2) (Rule30UOR.Core.twopow k)))
            ((s + 1) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag ((s + 3) - Rule30UOR.Core.twopow k) (s + 2) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag s (s + 2))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 2)))
            (Rule30UOR.Core.rdiag (s + 1) (s + 2) &&
              Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) (s + 2))
                (Rule30UOR.Core.rdiag (s - Rule30UOR.Core.twopow k) (s + 2))))
          (Rule30UOR.Core.rdiag ((s + 1) - Rule30UOR.Core.twopow k) (s + 2) &&
            Rule30UOR.Core.bxor (Rule30UOR.Core.rdiag (s + Rule30UOR.Core.twopow k) (s + 2))
              (Rule30UOR.Core.rdiag s (s + 2))))) :=
  Rule30Paper.Paper.periodic_winwitt_step_col1_slot_outside_cone s k hs

/-- **Multi-Period Shift (`+ m * P`) of the Window Step at the Center Slot on White Late Center Steps from the verified paper**. -/
theorem periodic_winwitt_step_center_slot_shift_mul_at_white_late_center_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m s k : Nat) (ht : T ≤ s + 1)
    (hw : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool ((s + m * P) + 2) k)
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt ((s + m * P) + 1) (Rule30UOR.Core.twopow k)))
            (((s + m * P) + 2) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row ((s + m * P) + 1)))
          (((s + m * P) + 1) + Rule30UOR.Core.twopow k)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool (s + 2) k)
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (s + 1) (Rule30UOR.Core.twopow k)))
            ((s + 2) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row (s + 1)))
          ((s + 1) + Rule30UOR.Core.twopow k))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool ((s + m * P) + 1) k)
          (Rule30UOR.Interfaces.wittRespBool (s + 1) k) &&
          Rule30UOR.Scale.maskparity (((s + m * P) + 1) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Interfaces.wittRespBool (s + 1) k &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Scale.maskparity (((s + m * P) + 1) + Rule30UOR.Core.twopow k) 0)
            (Rule30UOR.Scale.maskparity ((s + 1) + Rule30UOR.Core.twopow k) 0)) :=
  Rule30Paper.Paper.periodic_winwitt_step_center_slot_shift_mul_at_white_late_center T P hP h m s k ht hw

/-- **Bilinear Polarization of the Frobenius Defect (`frobdefect_xor`) from the verified paper**. -/
theorem frobdefect_xor_kit (k a b : Nat) :
    Rule30UOR.Interfaces.frobDefect k (a ^^^ b) =
      (Rule30UOR.Interfaces.frobDefect k a ^^^ Rule30UOR.Interfaces.frobDefect k b) ^^^
        (Rule30UOR.Interfaces.crossCarry (Rule30UOR.Core.phiScale k a) (Rule30UOR.Core.phiScale k b) ^^^
          Rule30UOR.Core.phiScale k (Rule30UOR.Interfaces.crossCarry a b)) :=
  Rule30Paper.Paper.frobdefect_xor k a b

/-- **In-Cone Vanishing of `δ_k(S_k(row t0))` from the verified paper**. -/
theorem frobdefect_phiscale_row_cone_eq_zero_kit (t0 k : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0)) = 0 :=
  Rule30Paper.Paper.frobdefect_phiscale_row_cone_eq_zero t0 k hcone

/-- **Outside-the-Cone Frobenius Defect `δ_k(row (t0 + 2^k))` from In-Cone `δ_k = 0` from the verified paper**. -/
theorem frobdefect_row_late_from_cone_kit (t0 k : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)) ^^^
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale (k + 1) (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))) ^^^
          Rule30UOR.Core.phiScale k
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
              (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)))) :=
  Rule30Paper.Paper.frobdefect_row_late_from_cone t0 k hcone

/-- **Tying `R_periodic` to the Center-Slot Frobenius Defect at `t0 = (d + 1) + 2^k` from the verified paper**. -/
theorem frobdefect_row_late_center_slot_rperiodic_kit (d k : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k
      (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k))
      (((d + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.rdiag d (d + 1)))
          (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag (d + 2) ((d + 1) + Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.rdiag d (d + 1))))
        (Rule30UOR.Core.center (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d + 2) ((d + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k)))) :=
  Rule30Paper.Paper.frobdefect_row_late_center_slot_rperiodic d k hk

/-- **Single-Product Collapse of the Late Center-Slot Frobenius Defect from the verified paper**. -/
theorem frobdefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump_kit
    (d k : Nat) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0))
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k)))
        (((d + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.frobdefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump
    d k hk hset hw1 hw2

/-- **Tying `R_periodic` to the Column-`-1` Frobenius Defect at `t0 = (d + 1) + 2^k` from the verified paper**. -/
theorem frobdefect_row_late_colm1_slot_rperiodic_kit (d k : Nat) (hk : d + 2 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k
      (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k))
      (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag d ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.center (d + 1)))
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.center (d + 1))))
        (Rule30UOR.Core.ldiag d (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d + 1) ((d + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k)))) :=
  Rule30Paper.Paper.frobdefect_row_late_colm1_slot_rperiodic d k hk

/-- **In-Phase Factorization of the Late Column-`-1` Frobenius Defect from the verified paper**. -/
theorem frobdefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage_kit
    (d k : Nat) (hk : d + 2 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hphase : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = Rule30UOR.Core.center (d + 1)) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d (d + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k)))
          (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.center (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.ldiag d (d + 1)))) :=
  Rule30Paper.Paper.frobdefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage d k hk hset hphase

/-- **Exact Difference Between the Column-`-1` and Center-Slot Frobenius Defects on White Centers from the verified paper**. -/
theorem frobdefect_row_late_colm1_xor_center_slot_at_both_white_centers_kit
    (d k : Nat) (hk : d + 2 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((d + 2) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.center (d + 2)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k)))
          (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k)))
          (((d + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.frobdefect_row_late_colm1_xor_center_slot_at_both_white_centers d k hk hset hw1 hw2

/-- **Factored Window Step at `t0 = (d + 1) + 2^k` Tying `zcenter` to the Triality of `maskparity · 0` from the verified paper**. -/
theorem periodic_winwitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0)
          (Rule30UOR.Scale.maskparity (d + 1) 0)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool ((d + 2) + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
          (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.periodic_winwitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality
    T P hP h d k ht hk hset hw0 hw1 hw2

/-- **Factored Window Step at `t0 = (d + 1) + 2^k` Tying `zcenter` to the Triality of Column `-1` from the verified paper**. -/
theorem periodic_winwitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.ldiag d (d + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt ((d + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k))
          (((d + 3) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
          (((d + 3) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.periodic_winwitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality
    T P hP h d k ht hk hset hw0 hw1 hw2

/-- **Exact Evaluation of `wittRespBool ((d + 1) + 2^k) k` via `R_periodic` and `zcenter` from the verified paper**. -/
theorem wittresp_late_eq_zcenter_xor_center_triality_kit
    (d k : Nat) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k) :
    Rule30UOR.Interfaces.ZCenterEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool ((d + 1) + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.center (d + 1))))) :=
  Rule30Paper.Paper.wittresp_late_eq_zcenter_xor_center_triality d k hk hset

/-- **Direct Readout of `zcenter (d + 1)` by `wittRespBool ((d + 1) + 2^k) k` on White Centers from the verified paper**. -/
theorem wittresp_late_at_white_centers_eq_zcenter_kit
    (d k : Nat) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow (k + 1)) = false) :
    Rule30UOR.Interfaces.ZCenterEq (d + 1)
      (Rule30UOR.Interfaces.wittRespBool ((d + 1) + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.wittresp_late_at_white_centers_eq_zcenter d k hk hset hw0 hw1 hw2

/-- **Uniform-in-`m` Shift of `wittRespBool` from the `R_periodic` Anchor `t0 = (d + 1) + 2^k` from the verified paper**. -/
theorem periodic_wittresp_late_shift_mul_eq_zcenter_xor_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k) :
    Rule30UOR.Interfaces.ZCenterEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool (((d + m * P) + 1) + Rule30UOR.Core.twopow k) k)
          (Rule30UOR.Interfaces.wittRespBool ((d + 1) + Rule30UOR.Core.twopow k) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.ldiag ((d + m * P) + 1) (((d + m * P) + 1) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag ((d + m * P) + 1) (((d + m * P) + 1) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.center (d + 1))))) :=
  Rule30Paper.Paper.periodic_wittresp_late_shift_mul_eq_zcenter_xor T P hP h m d k ht hk hset

/-- **Uniform-in-`m` Shift of Center-Slot Cross-Carry Tying `zcenter (d + 1)` to `maskparity` from the verified paper**. -/
theorem periodic_crosscarry_late_center_bit_shift_mul_at_white_centers_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (((d + m * P) + 1) + Rule30UOR.Core.twopow k)))
              (Rule30UOR.Core.winWitt (((d + m * P) + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
            ((((d + m * P) + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k)))
              (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
            (((d + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.wittRespBool (((d + m * P) + 1) + Rule30UOR.Core.twopow k) k &&
          Rule30UOR.Scale.maskparity (((d + m * P) + 1) + Rule30UOR.Core.twopow (k + 1)) 0)) :=
  Rule30Paper.Paper.periodic_crosscarry_late_center_bit_shift_mul_at_white_centers
    T P hP h m d k ht hk hset hw0 hw1 hw2

/-- **Uniform-in-`m` Shift of Column-`-1` Cross-Carry Tying `zcenter (d + 1)` to `maskparity` from the verified paper**. -/
theorem periodic_crosscarry_late_colm1_shift_mul_at_white_centers_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (((d + m * P) + 1) + Rule30UOR.Core.twopow k)))
              (Rule30UOR.Core.winWitt (((d + m * P) + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
            ((((d + m * P) + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry
              (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k)))
              (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
            (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
            (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow (k + 1)) 0) &&
            Rule30UOR.Interfaces.wittRespBool (((d + m * P) + 1) + Rule30UOR.Core.twopow k) k)
          (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)) &&
            Rule30UOR.Interfaces.wittRespBool (((d + m * P) + 1) + Rule30UOR.Core.twopow k) k))) :=
  Rule30Paper.Paper.periodic_crosscarry_late_colm1_shift_mul_at_white_centers
    T P hP h m d k ht hk hset hw0 hw1 hw2

/-- **Uniform-in-`m` Window Step from the `R_periodic` Anchor `t0 = (d + 1) + 2^k` from the verified paper**. -/
theorem periodic_winwitt_step_late_center_slot_shift_mul_at_white_centers_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0)
          (Rule30UOR.Scale.maskparity (d + 1) 0)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittRespBool (((d + m * P) + 2) + Rule30UOR.Core.twopow k) k)
          (Rule30UOR.Interfaces.wittRespBool ((d + 2) + Rule30UOR.Core.twopow k) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt (((d + m * P) + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
              ((((d + m * P) + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
              (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.wittRespBool (((d + m * P) + 1) + Rule30UOR.Core.twopow k) k &&
              Rule30UOR.Scale.maskparity (((d + m * P) + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
            (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row (((d + m * P) + 1) + Rule30UOR.Core.twopow k)))
              ((((d + m * P) + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))))) :=
  Rule30Paper.Paper.periodic_winwitt_step_late_center_slot_shift_mul_at_white_centers
    T P hP h m d k ht hk hset hw0 hw1 hw2

/-- **Uniform-in-`u` right-diagonal restart from the verified paper**. -/
theorem rdiag_restart_kit (k j u s : Nat) (hj : j ≤ k) :
    Rule30UOR.Core.rdiag j (s + u * Rule30UOR.Core.twopow k) = Rule30UOR.Core.rdiag j s :=
  Rule30Paper.Paper.rdiag_restart k j u s hj

/-- **Threshold form of right-diagonal restart from the verified paper**. -/
theorem rdiag_restart_of_threshold_kit (k J j u s : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (hj : j ≤ J) :
    Rule30UOR.Core.rdiag j (s + u * Rule30UOR.Core.twopow k) = Rule30UOR.Core.rdiag j s :=
  Rule30Paper.Paper.rdiag_restart_of_threshold k J j u s hJ hj

/-- **Center restart in `rdiag` coordinates from the verified paper**. -/
theorem center_restart_rdiag_kit (k s u : Nat) (hs : s ≤ k) :
    Rule30UOR.Core.rdiag s (s + u * Rule30UOR.Core.twopow k) = Rule30UOR.Core.center s :=
  Rule30Paper.Paper.center_restart_rdiag k s u hs

/-- **Sector-0 vanishing of `frobDefect k (row t0)` uniformly for all `t0 : Nat` from the verified paper**. -/
theorem frobdefect_row_lt_twopow_kit (t0 k j : Nat) (hj : j < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row t0) j false :=
  Rule30Paper.Paper.frobdefect_row_lt_twopow t0 k j hj

/-- **Sector-1 Wronskian of `frobDefect k (row t0)` uniformly for all `t0 : Nat` from the verified paper**. -/
theorem frobdefect_row_sector_one_kit (t0 k r : Nat) (hr : r + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row t0) ((r + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag ((r + 1) + Rule30UOR.Core.twopow k) t0 && Rule30UOR.Core.rdiag r t0)
        (Rule30UOR.Core.rdiag (r + 1) t0 && Rule30UOR.Core.rdiag (r + Rule30UOR.Core.twopow k) t0)) :=
  Rule30Paper.Paper.frobdefect_row_sector_one t0 k r hr

/-- **Uniform-in-`u` Sector-1 Frobenius defect folding via `restart` from the verified paper**. -/
theorem frobdefect_row_sector_one_restart_kit (d k u : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row ((d + 1) + u * Rule30UOR.Core.twopow k))
      ((d + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.rdiag ((d + 1) + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) &&
          Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.frobdefect_row_sector_one_restart d k u hk

/-- **Uniform-in-`u` Sector-2 Frobenius defect folding via `restart` from the verified paper**. -/
theorem frobdefect_row_sector_two_restart_kit (d k u : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row ((d + 1) + u * Rule30UOR.Core.twopow k))
      (((d + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag ((d + 1) + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + u * Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.rdiag d (d + 1)))
          (Rule30UOR.Core.rdiag ((d + 1) + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + u * Rule30UOR.Core.twopow k))
              (Rule30UOR.Core.rdiag d (d + 1))))
        (Rule30UOR.Core.center (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + u * Rule30UOR.Core.twopow k))
            (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k)))) :=
  Rule30Paper.Paper.frobdefect_row_sector_two_restart d k u hk

/-- **Sector-2 Wronskian of `frobDefect k (winWitt t0 (2^k))` from `R_periodic` from the verified paper**. -/
theorem frobdefect_winwitt_sector_two_wronskian_kit (t0 k r : Nat) (hr : r + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
      ((r + 1) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
          ((r + 1) + Rule30UOR.Core.twopow (k + 1)) &&
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
            (r + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
          ((r + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
            (r + Rule30UOR.Core.twopow (k + 1)))) :=
  Rule30Paper.Paper.frobdefect_winwitt_sector_two_wronskian t0 k r hr

/-- **Exact Sector-2 cross-carry equivariance inside the cone from the verified paper**. -/
theorem crosscarry_scale_row_winwitt_sector_two_cone_eq_kit (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) (hr : r + 1 ≤ k) :
    Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale (k + 1) (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))))
        ((r + 1) + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.phiScale k
          (Rule30UOR.Interfaces.crossCarry
            (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
            (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))))
        ((r + 1) + Rule30UOR.Core.twopow (k + 1)) :=
  Rule30Paper.Paper.crosscarry_scale_row_winwitt_sector_two_cone_eq t0 k r hcone hr

/-- **Exact Sector-2 identity between late row Frobenius defect and in-cone window Frobenius defect from the verified paper**. -/
theorem frobdefect_row_late_eq_frobdefect_winwitt_sector_two_kit (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) (hr : r + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k))
      ((r + 1) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)))
        ((r + 1) + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.frobdefect_row_late_eq_frobdefect_winwitt_sector_two t0 k r hcone hr

/-- **Exact Sector-2 Wronskian of late row Frobenius defect in terms of the in-cone window from the verified paper**. -/
theorem frobdefect_row_late_eq_winwitt_sector_two_wronskian_kit (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) (hr : r + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k))
      ((r + 1) + Rule30UOR.Core.twopow (k + 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
          ((r + 1) + Rule30UOR.Core.twopow (k + 1)) &&
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
            (r + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
          ((r + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
            (r + Rule30UOR.Core.twopow (k + 1)))) :=
  Rule30Paper.Paper.frobdefect_row_late_eq_winwitt_sector_two_wronskian t0 k r hcone hr

/-- **Fixed-scale `m * P`-defect equivalence between column `-2^k` and `response` from the verified paper**. -/
theorem periodic_ldiag_shift_mul_eq_response_shift_mul_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hk : Rule30UOR.Core.twopow k ≤ t) :
    Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag ((t + m * P) - Rule30UOR.Core.twopow k) (t + m * P))
        (Rule30UOR.Core.ldiag (t - Rule30UOR.Core.twopow k) t) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.response (t + m * P) k)
        (Rule30UOR.Scale.response t k) :=
  Rule30Paper.Paper.periodic_ldiag_shift_mul_eq_response_shift_mul T P hP h m t k ht hk

/-- **Refutation of Target 2 (`not_periodic_maskparity_zero_mul`) from the verified paper**. -/
theorem not_periodic_maskparity_zero_mul_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (T1 m : Nat) (hm : 0 < m) :
    ¬ Rule30UOR.Interfaces.MaskParityZeroPeriodic T1 (m * P) :=
  Rule30Paper.Paper.not_periodic_maskparity_zero_mul T P hP h T1 m hm

/-- **Refutation of Target 1 (`not_periodic_colm1_mul`) from the verified paper**. -/
theorem not_periodic_colm1_mul_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (T1 m : Nat) (hm : 0 < m) :
    ¬ Rule30UOR.Interfaces.ColNegOnePeriodic T1 (m * P) :=
  Rule30Paper.Paper.not_periodic_colm1_mul T P hP h T1 m hm

/-- **Sector-1 identity of late-row scaled copy from the verified paper**. -/
theorem phiscale_row_late_sector_one_eq_winwitt_cone_kit (t0 k j : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) (hj : j ≤ k) :
    Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k)))
        (j + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k))
        (j + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.phiscale_row_late_sector_one_eq_winwitt_cone t0 k j hcone hj

/-- **Exact Sector-1 late-row Frobenius defect as in-cone cross-carry from the verified paper**. -/
theorem frobdefect_row_late_sector_one_eq_crosscarry_cone_kit (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < Rule30UOR.Core.twopow k) (hr : r + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (t0 + Rule30UOR.Core.twopow k))
      ((r + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t0))
          (Rule30UOR.Core.winWitt t0 (Rule30UOR.Core.twopow k)))
        ((r + 1) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.frobdefect_row_late_sector_one_eq_crosscarry_cone t0 k r hcone hr

/-- **Exact Wronskian of `(center, rdiag)` in Sector 1 of late-row Frobenius defect from the verified paper**. -/
theorem frobdefect_row_late_sector_one_center_slot_wronskian_kit (d k : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k))
      ((d + 1) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) && Rule30UOR.Core.rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) &&
          Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.frobdefect_row_late_sector_one_center_slot_wronskian d k hk

/-- **In-cone Sector-2 cross-carry at a white center from the verified paper**. -/
theorem crosscarry_row_winwitt_sector_two_center_slot_kit (d k : Nat)
    (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hc : Rule30UOR.Core.center (d + 1) = false) :
    Rule30UOR.Interfaces.ZCenterAndEq (d + 1) (Rule30UOR.Scale.maskparity (d + 1) 0)
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (d + 1)))
          (Rule30UOR.Core.winWitt (d + 1) (Rule30UOR.Core.twopow k)))
        ((d + 1) + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.crosscarry_row_winwitt_sector_two_center_slot d k hk hset hc

/-- **Left-wing settled `restart` from the verified paper**. -/
theorem ldiag_settled_restart_kit (k j v t : Nat) (hj : j ≤ k)
    (hset : Rule30UOR.Interfaces.SettledBy j t) :
    Rule30UOR.Core.ldiag j (t + v * Rule30UOR.Core.twopow k) = Rule30UOR.Core.ldiag j t :=
  Rule30Paper.Paper.ldiag_settled_restart k j v t hj hset

/-- **Zero-state center `restart` in `ldiag` coordinates from the verified paper**. -/
theorem zcenter_restart_ldiag_kit (k d u : Nat) (hd : d ≤ k) (hu : 1 ≤ u)
    (hset : Rule30UOR.Interfaces.SettledAt d k) :
    Rule30UOR.Interfaces.ZCenterEq d
      (Rule30UOR.Core.ldiag d (d + u * Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.zcenter_restart_ldiag k d u hd hu hset

/-- **Unmasking the late center-slot Frobenius defect at `zcenter (d + 1) = true` from the verified paper**. -/
theorem frobdefect_row_late_center_slot_of_zcenter_true_kit
    (d k : Nat) (hk : d + 1 ≤ k) (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hz : Rule30UOR.Interfaces.ZCenterEq (d + 1) true)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Interfaces.BitFrobDefectEq k
      (Rule30UOR.Core.row ((d + 1) + Rule30UOR.Core.twopow k))
      (((d + 1) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0)) :=
  Rule30Paper.Paper.frobdefect_row_late_center_slot_of_zcenter_true d k hk hset hz hw1 hw2

/-- **Unmasking the window step triality of `maskparity · 0` at `zcenter (d + 1) = true` from the verified paper**. -/
theorem periodic_winwitt_step_late_center_slot_of_zcenter_true_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k)
    (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hz : Rule30UOR.Interfaces.ZCenterEq (d + 1) true)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow (k + 1)) 0)
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + 1) + Rule30UOR.Core.twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittRespBool ((d + 2) + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
          (((d + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.periodic_winwitt_step_late_center_slot_of_zcenter_true
    T P hP h d k ht hk hset hz hw0 hw1 hw2

/-- **Unmasking the window step triality of column `-1` at `zcenter (d + 1) = true` from the verified paper**. -/
theorem periodic_winwitt_step_late_colm1_slot_of_zcenter_true_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k)
    (hset : Rule30UOR.Interfaces.SettledAt (d + 1) k)
    (hz : Rule30UOR.Interfaces.ZCenterEq (d + 1) true)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow (k + 1)) ((d + 1) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (d + Rule30UOR.Core.twopow k) ((d + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag d (d + 1))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt ((d + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k))
          (((d + 3) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt ((d + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
          (((d + 3) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.periodic_winwitt_step_late_colm1_slot_of_zcenter_true
    T P hP h d k ht hk hset hz hw0 hw1 hw2

/-- **Sub-interval monotonicity of `RowAgree` from the verified paper**. -/
theorem rowagree_mono_kit (t Q a L a1 L1 : Nat) (ha : a ≤ a1) (hL : a1 + L1 ≤ a + L)
    (h : Rule30UOR.Interfaces.RowAgree t Q a L) :
    Rule30UOR.Interfaces.RowAgree t Q a1 L1 :=
  Rule30Paper.Paper.rowagree_mono t Q a L a1 L1 ha hL h

/-- **Sub-interval monotonicity of `WinWittAgree` from the verified paper**. -/
theorem winwittagree_mono_kit (t k Q a L a1 L1 : Nat) (ha : a ≤ a1) (hL : a1 + L1 ≤ a + L)
    (h : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q a1 L1 :=
  Rule30Paper.Paper.winwittagree_mono t k Q a L a1 L1 ha hL h

/-- **One-step Rule 30 propagation of `RowAgree` from the verified paper**. -/
theorem rowagree_step_kit (t Q a L : Nat)
    (h : Rule30UOR.Interfaces.RowAgree t Q a (L + 2)) :
    Rule30UOR.Interfaces.RowAgree (t + 1) Q (a + 2) L :=
  Rule30Paper.Paper.rowagree_step t Q a L h

/-- **`s`-step Rule 30 propagation of `RowAgree` from the verified paper**. -/
theorem rowagree_steps_kit (t Q a L s : Nat)
    (h : Rule30UOR.Interfaces.RowAgree t Q a (L + 2 * s)) :
    Rule30UOR.Interfaces.RowAgree (t + s) Q (a + 2 * s) L :=
  Rule30Paper.Paper.rowagree_steps t Q a L s h

/-- **Scaled-row agreement from three-sector `RowAgree` from the verified paper**. -/
theorem phiscale_row_testbit_eq_of_rowagree_kit (t k Q a L i : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a) (hi : i ≤ L)
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) L)
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a L) :
    Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (t + Q))) (a + i + Q) =
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t)) (a + i) :=
  Rule30Paper.Paper.phiscale_row_testbit_eq_of_rowagree t k Q a L i ha hi h0 h1 h2

/-- **Frobenius defect agreement from three-sector `RowAgree` from the verified paper**. -/
theorem frobdefect_row_testbit_eq_of_rowagree_kit (t k Q a L i : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a) (hi : i ≤ L)
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) (L + 1))
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a (L + 1)) :
    Rule30UOR.Interfaces.BitFrobDefectEq k (Rule30UOR.Core.row (t + Q)) (a + i + 1 + Q)
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t)) (a + i + 1)) :=
  Rule30Paper.Paper.frobdefect_row_testbit_eq_of_rowagree t k Q a L i ha hi h0 h1 h2

/-- **Cross-carry agreement from three-sector `RowAgree` and `WinWittAgree` from the verified paper**. -/
theorem crosscarry_testbit_eq_of_rowagree_winwittagree_kit (t k Q a L i : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a) (hi : i ≤ L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a (L + 1))
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) (L + 1))
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a (L + 1)) :
    Rule30UOR.Interfaces.BitCrossCarryEq
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row (t + Q)))
      (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
      (a + i + 1 + Q)
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.crossCarry
          (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
        (a + i + 1)) :=
  Rule30Paper.Paper.crosscarry_testbit_eq_of_rowagree_winwittagree t k Q a L i ha hi hw h0 h1 h2

/-- **One-step window propagation of `WinWittAgree` via Theorem 9.204 from the verified paper**. -/
theorem winwittagree_step_kit (t k Q a L : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a (L + 2))
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) (L + 1))
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a (L + 1)) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q (a + 2) L :=
  Rule30Paper.Paper.winwittagree_step t k Q a L ha hw h0 h1 h2

/-- **`s`-step window propagation of `WinWittAgree` via Theorem 9.204 from the verified paper**. -/
theorem winwittagree_steps_kit (t k Q a L s : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a (L + 2 * s))
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) (L + 2 * s))
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) (L + 2 * s))
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a (L + 2 * s)) :
    Rule30UOR.Interfaces.WinWittAgree (t + s) k Q (a + 2 * s) L :=
  Rule30Paper.Paper.winwittagree_steps t k Q a L s ha hw h0 h1 h2

/-- **Carrying `Q`-periodicity of `wittRespBool` forward by `s` steps via window step 9.204 from the verified paper**. -/
theorem wittresp_eq_of_winwittagree_steps_kit (t0 k Q s : Nat)
    (ht0 : Rule30UOR.Core.twopow k + s ≤ t0)
    (hw : Rule30UOR.Interfaces.WinWittAgree t0 k Q ((t0 + Rule30UOR.Core.twopow k) - s) (2 * s))
    (h0 : Rule30UOR.Interfaces.RowAgree t0 Q (((t0 + Rule30UOR.Core.twopow k) - s) - Rule30UOR.Core.twopow (k + 1)) (2 * s))
    (h1 : Rule30UOR.Interfaces.RowAgree t0 Q (((t0 + Rule30UOR.Core.twopow k) - s) - Rule30UOR.Core.twopow k) (2 * s))
    (h2 : Rule30UOR.Interfaces.RowAgree t0 Q ((t0 + Rule30UOR.Core.twopow k) - s) (2 * s)) :
    Rule30UOR.Interfaces.wittRespBool ((t0 + s) + Q) k =
      Rule30UOR.Interfaces.wittRespBool (t0 + s) k :=
  Rule30Paper.Paper.wittresp_eq_of_winwittagree_steps t0 k Q s ht0 hw h0 h1 h2

/-- **Carrying `Q`-periodicity of column `-1` forward by `s` steps from the verified paper**. -/
theorem colm1_eq_of_rowagree_steps_kit (t0 Q s : Nat) (hs : s ≤ t0 + 2)
    (h : Rule30UOR.Interfaces.RowAgree (t0 + 1) Q ((t0 + 2) - s) (2 * s)) :
    Rule30UOR.Core.ldiag ((t0 + s) + Q) ((t0 + s + 1) + Q) =
      Rule30UOR.Core.ldiag (t0 + s) (t0 + s + 1) :=
  Rule30Paper.Paper.colm1_eq_of_rowagree_steps t0 Q s hs h

/-- **Carrying `m * P`-periodicity of `maskparity · 0` forward by `s` steps from the verified paper**. -/
theorem maskparity_zero_eq_of_rowagree_steps_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t0 s : Nat) (ht : T ≤ t0 + s + 1) (hs : s ≤ t0 + 2)
    (h : Rule30UOR.Interfaces.RowAgree (t0 + 1) (m * P) ((t0 + 2) - s) (2 * s)) :
    Rule30UOR.Scale.maskparity ((t0 + s + 1) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t0 + s + 1) 0 :=
  Rule30Paper.Paper.maskparity_zero_eq_of_rowagree_steps T P hP hper m t0 s ht hs h

/-- **Carrying `Q`-periodicity from a sector residue class to every residue `mod 2^k` from the verified paper**. -/
theorem colnegoneperiodic_of_sector_rowagree_kit (k d U Q : Nat) (hU : 1 ≤ U)
    (hsec : Rule30UOR.Interfaces.SectorRowAgree k d U Q) :
    Rule30UOR.Interfaces.ColNegOnePeriodic (d + U * Rule30UOR.Core.twopow k) Q :=
  Rule30Paper.Paper.colnegoneperiodic_of_sector_rowagree k d U Q hU hsec

/-- **Refutation of sector-time radius-`2^k` neighbourhood agreement at `m * P` from the verified paper**. -/
theorem not_sector_rowagree_mul_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (hU : 1 ≤ U) (hm : 0 < m) :
    ¬ Rule30UOR.Interfaces.SectorRowAgree k d U (m * P) :=
  Rule30Paper.Paper.not_sector_rowagree_mul T P hP h k d U m hU hm

/-- **Right-wing `Q`-invariance at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem rdiag_lcmperiod_eq_kit (P k j t : Nat) (hj : j ≤ k) :
    Rule30UOR.Core.rdiag j (t + Rule30UOR.Interfaces.lcmPeriod P k) =
      Rule30UOR.Core.rdiag j t :=
  Rule30Paper.Paper.rdiag_lcmperiod_eq P k j t hj

/-- **Left-wing settled `Q`-invariance at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem ldiag_lcmperiod_eq_kit (P k j t : Nat) (hj : j ≤ k)
    (hset : Rule30UOR.Interfaces.SettledBy j t) :
    Rule30UOR.Core.ldiag j (t + Rule30UOR.Interfaces.lcmPeriod P k) =
      Rule30UOR.Core.ldiag j t :=
  Rule30Paper.Paper.ldiag_lcmperiod_eq P k j t hj hset

/-- **Center `Q`-invariance at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem center_lcmperiod_eq_kit (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P) (k t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.center (t + Rule30UOR.Interfaces.lcmPeriod P k) =
      Rule30UOR.Core.center t :=
  Rule30Paper.Paper.center_lcmperiod_eq T P hP h k t ht

/-- **Refutation of sector-time radius-`2^k` neighbourhood agreement at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem not_sector_rowagree_lcmperiod_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) :
    ¬ Rule30UOR.Interfaces.SectorRowAgree k d U (Rule30UOR.Interfaces.lcmPeriod P k) :=
  Rule30Paper.Paper.not_sector_rowagree_lcmperiod T P hP h k d U hU

/-- **1-cell leftward spatial extension of `RowAgree` from the verified paper**. -/
theorem rowagree_extend_right_kit (t Q a L : Nat)
    (h : Rule30UOR.Interfaces.RowAgree t Q a (L + 1))
    (hstep : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row ((t + 1) + Q)) (((a + L) + 2) + Q) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row (t + 1)) ((a + L) + 2)) :
    Rule30UOR.Interfaces.RowAgree t Q a (L + 2) :=
  Rule30Paper.Paper.rowagree_extend_right t Q a L h hstep

/-- **Unconditional radius-`0` center `RowAgree` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_rowagree_center_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P) (m t : Nat) (ht : T ≤ t) :
    Rule30UOR.Interfaces.RowAgree t (m * P) t 0 :=
  Rule30Paper.Paper.periodic_rowagree_center T P hP hper m t ht

/-- **Unconditional column-`0` and column-`-1` `RowAgree` at every black center from the verified paper**. -/
theorem periodic_rowagree_black_center_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P) (m t : Nat) (ht : T ≤ t + 1)
    (hblk : Rule30UOR.Core.center (t + 1) = true) :
    Rule30UOR.Interfaces.RowAgree (t + 1) (m * P) (t + 1) 1 :=
  Rule30Paper.Paper.periodic_rowagree_black_center T P hP hper m t ht hblk

/-- **Symmetric doubling of right-half `RowAgree` across the periodic center from the verified paper**. -/
theorem periodic_rowagree_symm_of_right_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P) (m R t : Nat)
    (ht : T ≤ t) (hR : R ≤ t)
    (hright : Rule30UOR.Interfaces.RowAgree t (m * P) (t - R) R) :
    Rule30UOR.Interfaces.RowAgree t (m * P) (t - R) (2 * R) :=
  Rule30Paper.Paper.periodic_rowagree_symm_of_right T P hP hper m R t ht hR hright

/-- **Symmetric doubling of right-half `RowAgree` at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem periodic_rowagree_lcmperiod_symm_of_right_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P) (k R t : Nat)
    (ht : T ≤ t) (hR : R ≤ t)
    (hright : Rule30UOR.Interfaces.RowAgree t (Rule30UOR.Interfaces.lcmPeriod P k) (t - R) R) :
    Rule30UOR.Interfaces.RowAgree t (Rule30UOR.Interfaces.lcmPeriod P k) (t - R) (2 * R) :=
  Rule30Paper.Paper.periodic_rowagree_lcmperiod_symm_of_right T P hP hper k R t ht hR hright

/-- **Carrying one-sided right sector agreement to every residue `mod 2^k` from the verified paper**. -/
theorem colnegoneperiodic_of_sector_right_rowagree_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P) (k d U m : Nat)
    (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hsec : Rule30UOR.Interfaces.SectorRightRowAgree k d U (m * P)) :
    Rule30UOR.Interfaces.ColNegOnePeriodic (d + U * Rule30UOR.Core.twopow k) (m * P) :=
  Rule30Paper.Paper.colnegoneperiodic_of_sector_right_rowagree T P hP hper k d U m hU hd ht hsec

/-- **Refutation of one-sided right sector agreement at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem not_sector_right_rowagree_lcmperiod_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P) (k d U : Nat)
    (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * Rule30UOR.Core.twopow k) :
    ¬ Rule30UOR.Interfaces.SectorRightRowAgree k d U (Rule30UOR.Interfaces.lcmPeriod P k) :=
  Rule30Paper.Paper.not_sector_right_rowagree_lcmperiod T P hP hper k d U hU hd ht

/-- **1-cell leftward spatial extension of `WinWittAgree` via Theorem 9.204 from the verified paper**. -/
theorem winwittagree_extend_right_kit (t k Q a L : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a (L + 1))
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) (L + 1))
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a (L + 1))
    (hstep : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k)) (((a + L) + 2) + Q) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k)) ((a + L) + 2)) :
    Rule30UOR.Interfaces.WinWittAgree t k Q a (L + 2) :=
  Rule30Paper.Paper.winwittagree_extend_right t k Q a L ha hw h0 h1 h2 hstep

/-- **Equivalence of `WinWittAgree` and late `RowAgree` under three-sector `RowAgree` from the verified paper**. -/
theorem winwittagree_of_rowagree_three_and_late_kit (t k Q a L : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a)
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) L)
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a L)
    (hlate : Rule30UOR.Interfaces.RowAgree (t + Rule30UOR.Core.twopow k) Q a L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q a L :=
  Rule30Paper.Paper.winwittagree_of_rowagree_three_and_late t k Q a L ha h0 h1 h2 hlate

/-- **Converse equivalence (`rowAgree_late_of_winWittAgree_and_three`) from the verified paper**. -/
theorem rowagree_late_of_winwittagree_and_three_kit (t k Q a L : Nat)
    (ha : Rule30UOR.Core.twopow (k + 1) ≤ a)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (h0 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow (k + 1)) L)
    (h1 : Rule30UOR.Interfaces.RowAgree t Q (a - Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RowAgree t Q a L) :
    Rule30UOR.Interfaces.RowAgree (t + Rule30UOR.Core.twopow k) Q a L :=
  Rule30Paper.Paper.rowagree_late_of_winwittagree_and_three t k Q a L ha hw h0 h1 h2

/-- **Carrying `wittRespBool` `Q`-periodicity from sector times across every residue `mod 2^k` via Window Step 9.204 from the verified paper**. -/
theorem wittrespbool_periodic_of_sector_winwittagree_kit (k d U Q : Nat) (hU : 2 ≤ U)
    (hsec : Rule30UOR.Interfaces.SectorWinWittAgree k d U Q)
    (t : Nat) (ht : d + U * Rule30UOR.Core.twopow k ≤ t) :
    Rule30UOR.Interfaces.wittRespBool (t + Q) k = Rule30UOR.Interfaces.wittRespBool t k :=
  Rule30Paper.Paper.wittrespbool_periodic_of_sector_winwittagree k d U Q hU hsec t ht

/-- **Right-boundary row neighbourhood `Q`-invariance at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem right_boundary_row_lcmperiod_eq_kit (P k j t : Nat) (hj : j ≤ k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row (t + Rule30UOR.Interfaces.lcmPeriod P k)) j =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) j :=
  Rule30Paper.Paper.right_boundary_row_lcmperiod_eq P k j t hj

/-- **Left-boundary settled row neighbourhood `Q`-invariance at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem left_boundary_row_lcmperiod_eq_kit (P k j t : Nat)
    (hj : j ≤ k) (hjt : j ≤ t) (hset : Rule30UOR.Interfaces.SettledBy j t) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row (t + Rule30UOR.Interfaces.lcmPeriod P k))
        (2 * (t + Rule30UOR.Interfaces.lcmPeriod P k) - j) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) (2 * t - j) :=
  Rule30Paper.Paper.left_boundary_row_lcmperiod_eq P k j t hj hjt hset

/-- **Sector-1 `frobDefect` `Q`-difference factored by `Q = lcm(P, 2^k)` at sector times from the verified paper**. -/
theorem frobdefect_row_sector_one_lcmperiod_xor_kit (P d k u : Nat) (hk : d + 1 ≤ k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row (((d + 1) + u * Rule30UOR.Core.twopow k) + Rule30UOR.Interfaces.lcmPeriod P k)))
        ((d + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row ((d + 1) + u * Rule30UOR.Core.twopow k)))
        ((d + 1) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.rdiag ((d + 1) + Rule30UOR.Core.twopow k) (((d + 1) + u * Rule30UOR.Core.twopow k) + Rule30UOR.Interfaces.lcmPeriod P k))
          (Rule30UOR.Core.rdiag ((d + 1) + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k)) &&
          Rule30UOR.Core.rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) (((d + 1) + u * Rule30UOR.Core.twopow k) + Rule30UOR.Interfaces.lcmPeriod P k))
            (Rule30UOR.Core.rdiag (d + Rule30UOR.Core.twopow k) ((d + 1) + u * Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.frobdefect_row_sector_one_lcmperiod_xor P d k u hk

/-- **Exact identity between `rhCenter` and `rdiag` from the verified paper**. -/
theorem rhcenter_eq_rdiag_kit (t p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.rhCenter t p = Rule30UOR.Core.rdiag (t - p) t :=
  Rule30Paper.Paper.rhcenter_eq_rdiag t p hp

/-- **Exact identity between `rhCenter` and `row` bit readout from the verified paper**. -/
theorem rhcenter_eq_row_testbit_kit (t p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) (t - p) :=
  Rule30Paper.Paper.rhcenter_eq_row_testbit t p hp

/-- **Exact identity between `lhCenter` and `ldiag` from the verified paper**. -/
theorem lhcenter_eq_ldiag_kit (t p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.lhCenter t p = Rule30UOR.Core.ldiag (t - p) t :=
  Rule30Paper.Paper.lhcenter_eq_ldiag t p hp

/-- **Exact identity between `lhCenter` and `row` bit readout from the verified paper**. -/
theorem lhcenter_eq_row_testbit_kit (t p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.lhCenter t p =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) (t + p) :=
  Rule30Paper.Paper.lhcenter_eq_row_testbit t p hp

/-- **Boundary readout `rhCenter t 0 = center t` from the verified paper**. -/
theorem rhcenter_zero_eq_center_kit (t : Nat) :
    Rule30UOR.Interfaces.rhCenter t 0 = Rule30UOR.Core.center t :=
  Rule30Paper.Paper.rhcenter_zero_eq_center t

/-- **Right-edge readout `rhCenter t t = true` from the verified paper**. -/
theorem rhcenter_self_eq_true_kit (t : Nat) :
    Rule30UOR.Interfaces.rhCenter t t = true :=
  Rule30Paper.Paper.rhcenter_self_eq_true t

/-- **Outside-cone readout `rhCenter t p = false` (`t < p`) from the verified paper**. -/
theorem rhcenter_gt_eq_false_kit (t p : Nat) (h : t < p) :
    Rule30UOR.Interfaces.rhCenter t p = false :=
  Rule30Paper.Paper.rhcenter_gt_eq_false t p h

/-- **Structural unfolding of the §6 `Φ` recombination operator from the verified paper**. -/
theorem phicenter_eq_lhcenter_rhcenter_kit (t : Nat) :
    Rule30UOR.Fixed.phiCenter t =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter t 1)
        (Rule30UOR.Core.center t || Rule30UOR.Interfaces.rhCenter t 1) :=
  Rule30Paper.Paper.phicenter_eq_lhcenter_rhcenter t

/-- **The §6 `Φ` fixed-point law solved for `lhCenter t 1` from the verified paper**. -/
theorem lhcenter_one_eq_of_center_fixed_kit (t : Nat) :
    Rule30UOR.Interfaces.lhCenter t 1 =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center (t + 1))
        (Rule30UOR.Core.center t || Rule30UOR.Interfaces.rhCenter t 1) :=
  Rule30Paper.Paper.lhcenter_one_eq_of_center_fixed t

/-- **Period-shift defect of the §6 `Φ` fixed-point law under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_lhcenter_one_defect_eq_not_center_and_rhcenter_one_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
      (Rule30UOR.Interfaces.lhCenter t 1) =
    (!Rule30UOR.Core.center t &&
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + m * P) 1)
        (Rule30UOR.Interfaces.rhCenter t 1)) :=
  Rule30Paper.Paper.periodic_lhcenter_one_defect_eq_not_center_and_rhcenter_one_defect T P hP hper m t ht

/-- **Evolution law of the driven right half `rhCenter` from the verified paper**. -/
theorem rhcenter_step_succ_kit (t p : Nat) :
    Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t p)
        (Rule30UOR.Interfaces.rhCenter t (p + 1) || Rule30UOR.Interfaces.rhCenter t (p + 2)) :=
  Rule30Paper.Paper.rhcenter_step_succ t p

/-- **Inward step law of the driven right half from the right edge toward column 1 from the verified paper**. -/
theorem rhcenter_inward_step_kit (t p : Nat) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1))
        (Rule30UOR.Interfaces.rhCenter t (p + 1) || Rule30UOR.Interfaces.rhCenter t (p + 2)) :=
  Rule30Paper.Paper.rhcenter_inward_step t p

/-- **Inward extension of right-half band agreement `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_extend_inward_kit (t Q p0 L : Nat)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + 1) (L + 1))
    (hstep : Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p0 + 1) =
      Rule30UOR.Interfaces.rhCenter (t + 1) (p0 + 1)) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 2) :=
  Rule30Paper.Paper.rhbandagree_extend_inward t Q p0 L h hstep

/-- **Forward time step of right-half band agreement `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_step_kit (t Q p0 L : Nat)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 2)) :
    Rule30UOR.Interfaces.RhBandAgree (t + 1) Q (p0 + 1) L :=
  Rule30Paper.Paper.rhbandagree_step t Q p0 L h

/-- **Conversion from `RhBandAgree` to `RowAgree` on the right half from the verified paper**. -/
theorem rowagree_right_of_rhbandagree_kit (t Q p0 L : Nat) (hp : p0 + L ≤ t)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.RowAgree t Q (t - (p0 + L)) L :=
  Rule30Paper.Paper.rowagree_right_of_rhbandagree t Q p0 L hp h

/-- **Conversion from `RowAgree` on the right half to `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_of_rowagree_right_kit (t Q p0 L : Nat) (hp : p0 + L ≤ t)
    (h : Rule30UOR.Interfaces.RowAgree t Q (t - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_of_rowagree_right t Q p0 L hp h

/-- **`SectorRhBandAgree` implies `SectorRightRowAgree` from the verified paper**. -/
theorem sectorrightrowagree_of_rhbandagree_kit (k d U Q : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d)
    (hsec : Rule30UOR.Interfaces.SectorRhBandAgree k d U Q) :
    Rule30UOR.Interfaces.SectorRightRowAgree k d U Q :=
  Rule30Paper.Paper.sectorrightrowagree_of_rhbandagree k d U Q hU hd hsec

/-- **Refutation of `SectorRhBandAgree` at `Q = lcm(P, 2^k)` under `CenterPeriodic T P` from the verified paper**. -/
theorem not_sector_rhbandagree_lcmperiod_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d)
    (ht : T ≤ d + U * Rule30UOR.Core.twopow k) :
    ¬ Rule30UOR.Interfaces.SectorRhBandAgree k d U (Rule30UOR.Interfaces.lcmPeriod P k) :=
  Rule30Paper.Paper.not_sector_rhbandagree_lcmperiod T P hP hper k d U hU hd ht

/-- **Right-edge `Q`-invariance of `rhCenter` at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem rhcenter_right_edge_lcmperiod_eq_kit (P k j t : Nat) (hj : j ≤ k) (hjt : j ≤ t) :
    Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Interfaces.lcmPeriod P k)
        ((t + Rule30UOR.Interfaces.lcmPeriod P k) - j) =
      Rule30UOR.Interfaces.rhCenter t (t - j) :=
  Rule30Paper.Paper.rhcenter_right_edge_lcmperiod_eq P k j t hj hjt

/-- **Carrying `SectorWinWittAgree` to `ColNegOnePeriodic` via Window Step 9.204 from the verified paper**. -/
theorem colnegoneperiodic_of_sector_winwittagree_kit (k d U Q : Nat) (hU : 2 ≤ U)
    (hsec : Rule30UOR.Interfaces.SectorWinWittAgree k d U Q) :
    Rule30UOR.Interfaces.ColNegOnePeriodic (d + (U + 1) * Rule30UOR.Core.twopow k) Q :=
  Rule30Paper.Paper.colnegoneperiodic_of_sector_winwittagree k d U Q hU hsec

/-- **Refutation of `SectorWinWittAgree` at `Q = lcm(P, 2^k)` under `CenterPeriodic T P` from the verified paper**. -/
theorem not_sector_winwittagree_lcmperiod_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 2 ≤ U) :
    ¬ Rule30UOR.Interfaces.SectorWinWittAgree k d U (Rule30UOR.Interfaces.lcmPeriod P k) :=
  Rule30Paper.Paper.not_sector_winwittagree_lcmperiod T P hP hper k d U hU

/-- **Construction of `SectorWinWittAgree` from `SectorWideRowAgree` from the verified paper**. -/
theorem sectorwinwittagree_of_sectorwiderowagree_kit (k d U Q : Nat) (hU : 2 ≤ U)
    (hsec : Rule30UOR.Interfaces.SectorWideRowAgree k d U Q) :
    Rule30UOR.Interfaces.SectorWinWittAgree k d U Q :=
  Rule30Paper.Paper.sectorwinwittagree_of_sectorwiderowagree k d U Q hU hsec

/-- **Construction of `SectorWinWittAgree` from `SectorWideRightRowAgree` under `CenterPeriodic T P` from the verified paper**. -/
theorem sectorwinwittagree_of_sectorwiderightrowagree_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (hU : 2 ≤ U)
    (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hsec : Rule30UOR.Interfaces.SectorWideRightRowAgree k d U (m * P)) :
    Rule30UOR.Interfaces.SectorWinWittAgree k d U (m * P) :=
  Rule30Paper.Paper.sectorwinwittagree_of_sectorwiderightrowagree T P hP hper k d U m hU ht hsec

/-- **Refutation of `SectorWideRightRowAgree` at `Q = lcm(P, 2^k)` under `CenterPeriodic T P` from the verified paper**. -/
theorem not_sectorwiderightrowagree_lcmperiod_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 2 ≤ U)
    (ht : T ≤ d + U * Rule30UOR.Core.twopow k) :
    ¬ Rule30UOR.Interfaces.SectorWideRightRowAgree k d U (Rule30UOR.Interfaces.lcmPeriod P k) :=
  Rule30Paper.Paper.not_sectorwiderightrowagree_lcmperiod T P hP hper k d U hU ht

/-- **Boundary readout `lhCenter t 0 = center t` from the verified paper**. -/
theorem lhcenter_zero_eq_center_kit (t : Nat) :
    Rule30UOR.Interfaces.lhCenter t 0 = Rule30UOR.Core.center t :=
  Rule30Paper.Paper.lhcenter_zero_eq_center t

/-- **Left-edge readout `lhCenter t t = true` from the verified paper**. -/
theorem lhcenter_self_eq_true_kit (t : Nat) :
    Rule30UOR.Interfaces.lhCenter t t = true :=
  Rule30Paper.Paper.lhcenter_self_eq_true t

/-- **Outside-cone readout `lhCenter t p = false` (`t < p`) from the verified paper**. -/
theorem lhcenter_gt_eq_false_kit (t p : Nat) (h : t < p) :
    Rule30UOR.Interfaces.lhCenter t p = false :=
  Rule30Paper.Paper.lhcenter_gt_eq_false t p h

/-- **Evolution law of the driven left half `lhCenter` from the verified paper**. -/
theorem lhcenter_step_succ_kit (t p : Nat) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter t (p + 2))
        (Rule30UOR.Interfaces.lhCenter t (p + 1) || Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_step_succ t p

/-- **Outward step law of the driven left half from the center toward the left edge from the verified paper**. -/
theorem lhcenter_outward_step_kit (t p : Nat) :
    Rule30UOR.Interfaces.lhCenter t (p + 2) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1))
        (Rule30UOR.Interfaces.lhCenter t (p + 1) || Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_outward_step t p

/-- **Pure right-half unfolding of the center column from the verified paper**. -/
theorem center_eq_rhcenter_inward_zero_kit (t : Nat) :
    Rule30UOR.Core.center t =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + 1) 1)
        (Rule30UOR.Interfaces.rhCenter t 1 || Rule30UOR.Interfaces.rhCenter t 2) :=
  Rule30Paper.Paper.center_eq_rhcenter_inward_zero t

/-- **Periodic center-bounce implication from OR-agreement at `(1, 2)` to column-1 agreement at `t + 1` from the verified paper**. -/
theorem periodic_rhcenter_step_one_eq_of_or_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hor : (Rule30UOR.Interfaces.rhCenter (t + m * P) 1 || Rule30UOR.Interfaces.rhCenter (t + m * P) 2) =
      (Rule30UOR.Interfaces.rhCenter t 1 || Rule30UOR.Interfaces.rhCenter t 2)) :
    Rule30UOR.Interfaces.rhCenter ((t + 1) + m * P) 1 =
      Rule30UOR.Interfaces.rhCenter (t + 1) 1 :=
  Rule30Paper.Paper.periodic_rhcenter_step_one_eq_of_or_eq T P hP hper m t ht hor

/-- **Converse periodic center-bounce implication from column-1 agreement at `t + 1` to OR-agreement at `(1, 2)` from the verified paper**. -/
theorem periodic_rhcenter_or_eq_of_step_one_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hstep : Rule30UOR.Interfaces.rhCenter ((t + 1) + m * P) 1 =
      Rule30UOR.Interfaces.rhCenter (t + 1) 1) :
    (Rule30UOR.Interfaces.rhCenter (t + m * P) 1 || Rule30UOR.Interfaces.rhCenter (t + m * P) 2) =
      (Rule30UOR.Interfaces.rhCenter t 1 || Rule30UOR.Interfaces.rhCenter t 2) :=
  Rule30Paper.Paper.periodic_rhcenter_or_eq_of_step_one_eq T P hP hper m t ht hstep

/-- **Multi-step forward propagation of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_steps_kit (t Q p0 L s : Nat)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 2 * s)) :
    Rule30UOR.Interfaces.RhBandAgree (t + s) Q (p0 + s) L :=
  Rule30Paper.Paper.rhbandagree_steps t Q p0 L s h

/-- **Free inward extension of `RhBandAgree` from column 1 to column 0 under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_rhbandagree_zero_of_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 L) :
    Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (L + 1) :=
  Rule30Paper.Paper.periodic_rhbandagree_zero_of_one T P hP hper m t L ht h

/-- **Center-anchored 1-step forward propagation of `RhBandAgree` at `p0 = 0` from the verified paper**. -/
theorem periodic_rhbandagree_zero_step_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (L + 1)) :
    Rule30UOR.Interfaces.RhBandAgree (t + 1) (m * P) 0 L :=
  Rule30Paper.Paper.periodic_rhbandagree_zero_step T P hP hper m t L ht h

/-- **Center-anchored multi-step forward propagation of `RhBandAgree` at `p0 = 0` from the verified paper**. -/
theorem periodic_rhbandagree_zero_steps_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L s : Nat) (ht : T ≤ t)
    (h : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (L + s)) :
    Rule30UOR.Interfaces.RhBandAgree (t + s) (m * P) 0 L :=
  Rule30Paper.Paper.periodic_rhbandagree_zero_steps T P hP hper m t L s ht h

/-- **Multi-step inward extension of `RhBandAgree` from the right edge toward the center from the verified paper**. -/
theorem rhbandagree_extend_inward_steps_kit (t Q p0 S L : Nat)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + S) (L + 1))
    (hstep : Rule30UOR.Interfaces.RhBandAgree (t + 1) Q (p0 + 1) S) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 ((L + 1) + S) :=
  Rule30Paper.Paper.rhbandagree_extend_inward_steps t Q p0 S L h hstep

/-- **Right-to-center full band agreement from right-boundary pair and next-step interior from the verified paper**. -/
theorem rhbandagree_zero_of_edge_and_succ_kit (t Q S L : Nat)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q S (L + 1))
    (hstep : Rule30UOR.Interfaces.RhBandAgree (t + 1) Q 1 S) :
    Rule30UOR.Interfaces.RhBandAgree t Q 0 ((L + 1) + S) :=
  Rule30Paper.Paper.rhbandagree_zero_of_edge_and_succ t Q S L h hstep

/-- **Center-bounce inward extension of `RhBandAgree` at time `t` from the verified paper**. -/
theorem periodic_rhbandagree_bounce_zero_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S L : Nat) (ht : T ≤ t)
    (h : Rule30UOR.Interfaces.RhBandAgree t (m * P) (S + 1) (L + 1))
    (hstep : Rule30UOR.Interfaces.RhBandAgree (t + 1) (m * P) 2 S) :
    Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 ((L + 2) + S) :=
  Rule30Paper.Paper.periodic_rhbandagree_bounce_zero T P hP hper m t S L ht h hstep

/-- **Center-bounce inward extension of `RhBandAgree` at time `t + 1` from the verified paper**. -/
theorem periodic_rhbandagree_bounce_succ_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S L : Nat) (ht : T ≤ t)
    (h : Rule30UOR.Interfaces.RhBandAgree t (m * P) (S + 1) (L + 1))
    (hstep : Rule30UOR.Interfaces.RhBandAgree (t + 1) (m * P) 2 S) :
    Rule30UOR.Interfaces.RhBandAgree (t + 1) (m * P) 0 ((L + 1) + S) :=
  Rule30Paper.Paper.periodic_rhbandagree_bounce_succ T P hP hper m t S L ht h hstep

/-- **Direct right-half propagation of `SectorRhBandAgree` to every-time column `+1` periodicity from the verified paper**. -/
theorem rhcenter_one_periodic_of_sector_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hsec : Rule30UOR.Interfaces.SectorRhBandAgree k d U (m * P))
    (t : Nat) (ht_ge : (d + U * Rule30UOR.Core.twopow k) + 1 ≤ t) :
    Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1 :=
  Rule30Paper.Paper.rhcenter_one_periodic_of_sector_rhbandagree T P hP hper k d U m ht hsec t ht_ge

/-- **Direct right-half-to-`Φ`-fixed-point propagation of `SectorRhBandAgree` to every-time column `-1` periodicity from the verified paper**. -/
theorem lhcenter_one_periodic_of_sector_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hsec : Rule30UOR.Interfaces.SectorRhBandAgree k d U (m * P))
    (t : Nat) (ht_ge : (d + U * Rule30UOR.Core.twopow k) + 1 ≤ t) :
    Rule30UOR.Interfaces.lhCenter (t + m * P) 1 = Rule30UOR.Interfaces.lhCenter t 1 :=
  Rule30Paper.Paper.lhcenter_one_periodic_of_sector_rhbandagree T P hP hper k d U m ht hsec t ht_ge

/-- **Unconditional right-edge diagonal `2^k`-shift invariance of `rhCenter` from the verified paper**. -/
theorem rhcenter_diag_shift_twopow_eq_kit (k t p v : Nat)
    (hp : p ≤ t) (hj : t - p ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow k)
        (p + v * Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.rhCenter t p :=
  Rule30Paper.Paper.rhcenter_diag_shift_twopow_eq k t p v hp hj

/-- **Unconditional right-edge sector diagonal readout `rhCenter (j + u * 2^k) (u * 2^k) = center j` from the verified paper**. -/
theorem rhcenter_sector_diag_eq_center_kit (j k u : Nat) (hj : j ≤ k) :
    Rule30UOR.Interfaces.rhCenter (j + u * Rule30UOR.Core.twopow k)
        (u * Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center j :=
  Rule30Paper.Paper.rhcenter_sector_diag_eq_center j k u hj

/-- **Exact `2^k`-scale forward step law of the driven right half `rhCenter` from the verified paper**. -/
theorem rhcenter_scale_step_kit (t k p : Nat)
    (hp : p + Rule30UOR.Core.twopow (k + 1) ≤ t) :
    Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k)
        (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.rhCenter t p)
            (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t - p)) :=
  Rule30Paper.Paper.rhcenter_scale_step t k p hp

/-- **Exact `2^k`-scale inward step law of the driven right half `rhCenter` from the verified paper**. -/
theorem rhcenter_scale_inward_step_kit (t k p : Nat)
    (hp : p + Rule30UOR.Core.twopow (k + 1) ≤ t) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k)
              (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t - p)) :=
  Rule30Paper.Paper.rhcenter_scale_inward_step t k p hp

/-- **Sub-interval monotonicity of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_mono_kit (t Q p0 L p0p Lp : Nat)
    (hp : p0 ≤ p0p) (hL : p0p + Lp ≤ p0 + L)
    (h : Rule30UOR.Interfaces.RhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0p Lp :=
  Rule30Paper.Paper.rhbandagree_mono t Q p0 L p0p Lp hp hL h

/-- **Sub-interval monotonicity of `RhColAgree` from the verified paper**. -/
theorem rhcolagree_mono_kit (t Q p0 S s0 Sp : Nat)
    (hs : s0 + Sp ≤ S)
    (h : Rule30UOR.Interfaces.RhColAgree t Q p0 S) :
    Rule30UOR.Interfaces.RhColAgree (t + s0) Q p0 Sp :=
  Rule30Paper.Paper.rhcolagree_mono t Q p0 S s0 Sp hs h

/-- **Sub-interval monotonicity of `RhOrAgree` from the verified paper**. -/
theorem rhoragree_mono_kit (t Q p0 S s0 Sp : Nat)
    (hs : s0 + Sp ≤ S)
    (h : Rule30UOR.Interfaces.RhOrAgree t Q p0 S) :
    Rule30UOR.Interfaces.RhOrAgree (t + s0) Q p0 Sp :=
  Rule30Paper.Paper.rhoragree_mono t Q p0 S s0 Sp hs h

/-- **Right-half `RhOrAgree` from column-`p0` time-trace agreement from the verified paper**. -/
theorem rhoragree_of_col_agree_kit (t Q p0 S : Nat)
    (hcol : Rule30UOR.Interfaces.RhColAgree t Q p0 S)
    (hnext : ∀ s, s < S →
      Rule30UOR.Interfaces.rhCenter ((t + (s + 1)) + Q) (p0 + 1) =
        Rule30UOR.Interfaces.rhCenter (t + (s + 1)) (p0 + 1)) :
    Rule30UOR.Interfaces.RhOrAgree t Q (p0 + 1) S :=
  Rule30Paper.Paper.rhoragree_of_col_agree t Q p0 S hcol hnext

/-- **Center `RhOrAgree` from column-1 agreement under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_rhoragree_one_of_col_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h1 : ∀ s, s < S →
      Rule30UOR.Interfaces.rhCenter ((t + (s + 1)) + m * P) 1 =
        Rule30UOR.Interfaces.rhCenter (t + (s + 1)) 1) :
    Rule30UOR.Interfaces.RhOrAgree t (m * P) 1 S :=
  Rule30Paper.Paper.periodic_rhoragree_one_of_col_one T P hP hper m t S ht h1

/-- **Column-1 agreement from center `RhOrAgree` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_col_one_of_rhoragree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hor : Rule30UOR.Interfaces.RhOrAgree t (m * P) 1 S) :
    ∀ s, s < S →
      Rule30UOR.Interfaces.rhCenter ((t + (s + 1)) + m * P) 1 =
        Rule30UOR.Interfaces.rhCenter (t + (s + 1)) 1 :=
  Rule30Paper.Paper.periodic_col_one_of_rhoragree_one T P hP hper m t S ht hor

/-- **1-column inward step of right-half window determination from the verified paper**. -/
theorem rhcenter_inward_determine_step_kit (t Q p0 S : Nat)
    (hcol : Rule30UOR.Interfaces.RhColAgree t Q (p0 + 1) (S + 1))
    (hor : Rule30UOR.Interfaces.RhOrAgree t Q (p0 + 1) (S + 1)) :
    Rule30UOR.Interfaces.RhColAgree t Q p0 S ∧
      Rule30UOR.Interfaces.RhOrAgree t Q p0 S :=
  Rule30Paper.Paper.rhcenter_inward_determine_step t Q p0 S hcol hor

/-- **Multi-column inward right-half window determination from the verified paper**. -/
theorem rhcenter_inward_determine_kit (t Q p0 S K : Nat)
    (hcol : Rule30UOR.Interfaces.RhColAgree t Q (p0 + K) (S + K))
    (hor : Rule30UOR.Interfaces.RhOrAgree t Q (p0 + K) (S + K)) :
    Rule30UOR.Interfaces.RhColAgree t Q p0 S ∧
      Rule30UOR.Interfaces.RhOrAgree t Q p0 S :=
  Rule30Paper.Paper.rhcenter_inward_determine t Q p0 S K hcol hor

/-- **Right-half spatial band agreement from right-boundary column trace from the verified paper**. -/
theorem rhbandagree_of_inward_determine_kit (t Q p0 L : Nat)
    (hcol : Rule30UOR.Interfaces.RhColAgree t Q (p0 + L) L)
    (hor : Rule30UOR.Interfaces.RhOrAgree t Q (p0 + L) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_of_inward_determine t Q p0 L hcol hor

/-- **Unconditional right-edge `RhBandAgree` outside the light cone from the verified paper**. -/
theorem rhbandagree_outside_cone_kit (t Q p0 L : Nat) (h : t + Q < p0) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_outside_cone t Q p0 L h

/-- **`2^k`-scale forward band transport of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_step_kit (t k Q p0 L : Nat)
    (hp : (p0 + L) + Rule30UOR.Core.twopow (k + 1) ≤ t)
    (h0 : Rule30UOR.Interfaces.RhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.rhbandagree_scale_step t k Q p0 L hp h0 h1 h2 hw

/-- **`2^k`-scale inward band transport of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_inward_step_kit (t k Q p0 L : Nat)
    (hp : (p0 + L) + Rule30UOR.Core.twopow (k + 1) ≤ t)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_inward_step t k Q p0 L hp hlate h1 h2 hw

/-- **`WinWittAgree` from `RhBandAgree` on three `2^k`-bands and the late band from the verified paper**. -/
theorem winwittagree_of_rhbandagree_scale_kit (t k Q p0 L : Nat)
    (hp : (p0 + L) + Rule30UOR.Core.twopow (k + 1) ≤ t)
    (h0 : Rule30UOR.Interfaces.RhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L :=
  Rule30Paper.Paper.winwittagree_of_rhbandagree_scale t k Q p0 L hp h0 h1 h2 hlate

/-- **Establishing `SectorRhBandAgree` from right-half window determination at sector times from the verified paper**. -/
theorem sectorrhbandagree_of_inward_determine_kit (k d U Q : Nat)
    (hcol : ∀ u, U ≤ u →
      Rule30UOR.Interfaces.RhColAgree ((d + u * Rule30UOR.Core.twopow k) + 1) Q
        (Rule30UOR.Core.twopow k + 1) (Rule30UOR.Core.twopow k + 1))
    (hor : ∀ u, U ≤ u →
      Rule30UOR.Interfaces.RhOrAgree ((d + u * Rule30UOR.Core.twopow k) + 1) Q
        (Rule30UOR.Core.twopow k + 1) (Rule30UOR.Core.twopow k + 1)) :
    Rule30UOR.Interfaces.SectorRhBandAgree k d U Q :=
  Rule30Paper.Paper.sectorrhbandagree_of_inward_determine k d U Q hcol hor

/-- **Refutation of right-half window agreement at column `2^k + 1` for `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem not_sector_inward_determine_lcmperiod_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hcol : ∀ u, U ≤ u →
      Rule30UOR.Interfaces.RhColAgree ((d + u * Rule30UOR.Core.twopow k) + 1)
        (Rule30UOR.Interfaces.lcmPeriod P k)
        (Rule30UOR.Core.twopow k + 1) (Rule30UOR.Core.twopow k + 1)) :
    ¬ (∀ u, U ≤ u →
      Rule30UOR.Interfaces.RhOrAgree ((d + u * Rule30UOR.Core.twopow k) + 1)
        (Rule30UOR.Interfaces.lcmPeriod P k)
        (Rule30UOR.Core.twopow k + 1) (Rule30UOR.Core.twopow k + 1)) :=
  Rule30Paper.Paper.not_sector_inward_determine_lcmperiod T P hP hper k d U hU hd ht hcol

/-- **Unrestricted `2^k`-scale forward step of `rhCenter` (`p ≤ t`) from the verified paper**. -/
theorem rhcenter_scale_step_le_kit (t k p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t p)
            (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (t - p)) :=
  Rule30Paper.Paper.rhcenter_scale_step_le t k p hp

/-- **Unrestricted `2^k`-scale inward step of `rhCenter` (`p ≤ t`) from the verified paper**. -/
theorem rhcenter_scale_inward_step_le_kit (t k p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k)
              (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (t - p)) :=
  Rule30Paper.Paper.rhcenter_scale_inward_step_le t k p hp

/-- **Unrestricted `2^k`-scale forward band transport of `RhBandAgree` (`p0 + L ≤ t`) from the verified paper**. -/
theorem rhbandagree_scale_step_le_kit (t k Q p0 L : Nat)
    (hp : p0 + L ≤ t)
    (h0 : Rule30UOR.Interfaces.RhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.rhbandagree_scale_step_le t k Q p0 L hp h0 h1 h2 hw

/-- **Unrestricted `2^k`-scale inward band transport of `RhBandAgree` (`p0 + L ≤ t`) from the verified paper**. -/
theorem rhbandagree_scale_inward_step_le_kit (t k Q p0 L : Nat)
    (hp : p0 + L ≤ t)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_inward_step_le t k Q p0 L hp hlate h1 h2 hw

/-- **Unrestricted `WinWittAgree` from `RhBandAgree` on three `2^k`-bands and the late band (`p0 + L ≤ t`) from the verified paper**. -/
theorem winwittagree_of_rhbandagree_scale_le_kit (t k Q p0 L : Nat)
    (hp : p0 + L ≤ t)
    (h0 : Rule30UOR.Interfaces.RhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L :=
  Rule30Paper.Paper.winwittagree_of_rhbandagree_scale_le t k Q p0 L hp h0 h1 h2 hlate

/-- **Multi-step `2^k`-scale inward iteration of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_inward_steps_kit (t k Q p0 L M : Nat)
    (hp : (p0 + M * Rule30UOR.Core.twopow k) + L ≤ t)
    (hM : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + M * Rule30UOR.Core.twopow k) L)
    (hM1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + (M + 1) * Rule30UOR.Core.twopow k) L)
    (hlate : ∀ m, m < M →
      Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
        (p0 + (m + 1) * Rule30UOR.Core.twopow k) L)
    (hw : ∀ m, m < M →
      Rule30UOR.Interfaces.WinWittAgree t k Q
        (t - ((p0 + m * Rule30UOR.Core.twopow k) + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_inward_steps t k Q p0 L M hp hM hM1 hlate hw

/-- **Black-left masking in `rhCenter` inward step from the verified paper**. -/
theorem rhcenter_inward_of_black_left_kit (t p : Nat)
    (hb : Rule30UOR.Interfaces.rhCenter t (p + 1) = true) :
    Rule30UOR.Interfaces.rhCenter t p = !Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1) :=
  Rule30Paper.Paper.rhcenter_inward_of_black_left t p hb

/-- **Black-right masking in `rhCenter` inward step from the verified paper**. -/
theorem rhcenter_inward_of_black_right_kit (t p : Nat)
    (hb : Rule30UOR.Interfaces.rhCenter t (p + 2) = true) :
    Rule30UOR.Interfaces.rhCenter t p = !Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1) :=
  Rule30Paper.Paper.rhcenter_inward_of_black_right t p hb

/-- **Inward `Q`-agreement across a black column from the verified paper**. -/
theorem rhcenter_agree_of_black_left_kit (t Q p : Nat)
    (hbQ : Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) = true)
    (hb0 : Rule30UOR.Interfaces.rhCenter t (p + 1) = true)
    (hnext : Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1)) :
    Rule30UOR.Interfaces.rhCenter (t + Q) p = Rule30UOR.Interfaces.rhCenter t p :=
  Rule30Paper.Paper.rhcenter_agree_of_black_left t Q p hbQ hb0 hnext

/-- **White-pair splitting from constant diagonal step (`Z_down` in `rhCenter`) from the verified paper**. -/
theorem rhcenter_white_pair_of_diag_eq_kit (t p : Nat)
    (heq : Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1) = Rule30UOR.Interfaces.rhCenter t p) :
    Rule30UOR.Interfaces.rhCenter t (p + 1) = false ∧
      Rule30UOR.Interfaces.rhCenter t (p + 2) = false :=
  Rule30Paper.Paper.rhcenter_white_pair_of_diag_eq t p heq

/-- **Constant diagonal step from white pair in `rhCenter` from the verified paper**. -/
theorem rhcenter_diag_eq_of_white_pair_kit (t p : Nat)
    (hw1 : Rule30UOR.Interfaces.rhCenter t (p + 1) = false)
    (hw2 : Rule30UOR.Interfaces.rhCenter t (p + 2) = false) :
    Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1) = Rule30UOR.Interfaces.rhCenter t p :=
  Rule30Paper.Paper.rhcenter_diag_eq_of_white_pair t p hw1 hw2

/-- **Right-threshold diagonal shift law in `rhCenter` from the verified paper**. -/
theorem rhcenter_diag_shift_twopow_eq_of_threshold_kit (k J p s u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (hs : s ≤ J) :
    Rule30UOR.Interfaces.rhCenter ((p + s) + u * Rule30UOR.Core.twopow k)
      (p + u * Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.rhCenter (p + s) p :=
  Rule30Paper.Paper.rhcenter_diag_shift_twopow_eq_of_threshold k J p s u hJ hs

/-- **Right-threshold sector-column center law in `rhCenter` from the verified paper**. -/
theorem rhcenter_sector_diag_eq_center_of_threshold_kit (k J s u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (hs : s ≤ J) :
    Rule30UOR.Interfaces.rhCenter (s + u * Rule30UOR.Core.twopow k)
      (u * Rule30UOR.Core.twopow k) = Rule30UOR.Core.center s :=
  Rule30Paper.Paper.rhcenter_sector_diag_eq_center_of_threshold k J s u hJ hs

/-- **Right-edge white zero-gap of width `J` at multiples of `2^k` in `rhCenter` from the verified paper**. -/
theorem rhcenter_zero_gap_of_threshold_kit (k J u j : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hj1 : 1 ≤ j) (hjJ : j ≤ J) (hju : j ≤ u * Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.rhCenter (u * Rule30UOR.Core.twopow k)
      (u * Rule30UOR.Core.twopow k - j) = false :=
  Rule30Paper.Paper.rhcenter_zero_gap_of_threshold k J u j hJ hj1 hjJ hju

/-- **Right-edge black run of width `J + 1` at `(u + 1) * 2^k - 1` in `rhCenter` from the verified paper**. -/
theorem rhcenter_last_one_of_threshold_kit (k J u j : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J)
    (hjJ : j ≤ J) (hju : j ≤ (u + 1) * Rule30UOR.Core.twopow k - 1) :
    Rule30UOR.Interfaces.rhCenter ((u + 1) * Rule30UOR.Core.twopow k - 1)
      (((u + 1) * Rule30UOR.Core.twopow k - 1) - j) = true :=
  Rule30Paper.Paper.rhcenter_last_one_of_threshold k J u j hJ hjJ hju

/-- **Unconditional `2^k`-scale forward step of `rhCenter` from the verified paper**. -/
theorem rhcenter_scale_step_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t p)
            (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (t - p)) :=
  Rule30Paper.Paper.rhcenter_scale_step_uncond t k p

/-- **Unconditional `2^k`-scale inward step of `rhCenter` from the verified paper**. -/
theorem rhcenter_scale_inward_step_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.rhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (t - p)) :=
  Rule30Paper.Paper.rhcenter_scale_inward_step_uncond t k p

/-- **`RhWinWittAgree` from `WinWittAgree` inside the light cone from the verified paper**. -/
theorem rhwinwittagree_of_winwittagree_kit (t k Q p0 L : Nat)
    (hpt : p0 + L ≤ t)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhWinWittAgree t k Q p0 L :=
  Rule30Paper.Paper.rhwinwittagree_of_winwittagree t k Q p0 L hpt hw

/-- **`RhWinWittAgree` outside the light cone from the verified paper**. -/
theorem rhwinwittagree_outside_cone_kit (t k Q p0 L : Nat)
    (hout : t + Q ≤ p0) :
    Rule30UOR.Interfaces.RhWinWittAgree t k Q p0 L :=
  Rule30Paper.Paper.rhwinwittagree_outside_cone t k Q p0 L hout

/-- **Unconditional `2^k`-scale inward step of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_inward_step_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L)
    (h1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.RhWinWittAgree t k Q p0 L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_inward_step_uncond t k Q p0 L hlate h1 h2 hw

/-- **Multi-step unconditional `2^k`-scale inward propagation of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_inward_steps_uncond_kit (t k Q p0 L M : Nat)
    (hM : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + M * Rule30UOR.Core.twopow k) L)
    (hM1 : Rule30UOR.Interfaces.RhBandAgree t Q (p0 + (M + 1) * Rule30UOR.Core.twopow k) L)
    (hlate : ∀ m, m < M → Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + (m + 1) * Rule30UOR.Core.twopow k) L)
    (hw : ∀ m, m < M → Rule30UOR.Interfaces.RhWinWittAgree t k Q
      (p0 + m * Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_inward_steps_uncond t k Q p0 L M hM hM1 hlate hw

/-- **Inward `2^k`-scale cone reduction of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_of_scale_inward_cone_kit (t k Q p0 L M : Nat)
    (hcone : t + Q < p0 + M * Rule30UOR.Core.twopow k)
    (hlate : ∀ m, m < M → Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + (m + 1) * Rule30UOR.Core.twopow k) L)
    (hw : ∀ m, m < M → Rule30UOR.Interfaces.RhWinWittAgree t k Q
      (p0 + m * Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_of_scale_inward_cone t k Q p0 L M hcone hlate hw

/-- **Diagonal difference of `rhCenter` equals OR of right pair from the verified paper**. -/
theorem rhcenter_diag_diff_eq_or_kit (t p : Nat) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1))
      (Rule30UOR.Interfaces.rhCenter t p) =
      (Rule30UOR.Interfaces.rhCenter t (p + 1) || Rule30UOR.Interfaces.rhCenter t (p + 2)) :=
  Rule30Paper.Paper.rhcenter_diag_diff_eq_or t p

/-- **Right-half `Q`-defect diagonal conservation law from the verified paper**. -/
theorem rhcenter_defect_diag_step_kit (t Q p : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1))
        (Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1)))
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) p)
        (Rule30UOR.Interfaces.rhCenter t p)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) ||
          Rule30UOR.Interfaces.rhCenter (t + Q) (p + 2))
        (Rule30UOR.Interfaces.rhCenter t (p + 1) ||
          Rule30UOR.Interfaces.rhCenter t (p + 2)) :=
  Rule30Paper.Paper.rhcenter_defect_diag_step t Q p

/-- **Generalized Masked-Jen gate for `rhCenter` defect under column `p + 1` agreement from the verified paper**. -/
theorem rhcenter_defect_diag_step_of_col_eq_kit (t Q p : Nat)
    (hp1 : Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter t (p + 1)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1))
        (Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1)))
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) p)
        (Rule30UOR.Interfaces.rhCenter t p)) =
      ((!Rule30UOR.Interfaces.rhCenter t (p + 1)) &&
        Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) (p + 2))
          (Rule30UOR.Interfaces.rhCenter t (p + 2))) :=
  Rule30Paper.Paper.rhcenter_defect_diag_step_of_col_eq t Q p hp1

/-- **Inward `Q`-defect gate under two-time agreement at column `p + 1` from the verified paper**. -/
theorem rhcenter_defect_inward_of_col_eq_two_kit (t Q p : Nat)
    (hp1 : Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter t (p + 1))
    (hnext : Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1)) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) p)
      (Rule30UOR.Interfaces.rhCenter t p) =
      ((!Rule30UOR.Interfaces.rhCenter t (p + 1)) &&
        Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) (p + 2))
          (Rule30UOR.Interfaces.rhCenter t (p + 2))) :=
  Rule30Paper.Paper.rhcenter_defect_inward_of_col_eq_two t Q p hp1 hnext

/-- **Local right-permutive step across a white cell in `rhCenter` from the verified paper**. -/
theorem rhcenter_outward_of_white_mid_kit (t p : Nat)
    (hw : Rule30UOR.Interfaces.rhCenter t (p + 1) = false) :
    Rule30UOR.Interfaces.rhCenter t (p + 2) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1))
        (Rule30UOR.Interfaces.rhCenter t p) :=
  Rule30Paper.Paper.rhcenter_outward_of_white_mid t p hw

/-- **Outward `Q`-agreement across a white cell in `rhCenter` from the verified paper**. -/
theorem rhcenter_agree_outward_of_white_mid_kit (t Q p : Nat)
    (hw : Rule30UOR.Interfaces.rhCenter t (p + 1) = false)
    (hp : Rule30UOR.Interfaces.rhCenter (t + Q) p = Rule30UOR.Interfaces.rhCenter t p)
    (hp1 : Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) = Rule30UOR.Interfaces.rhCenter t (p + 1))
    (hnext : Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1)) :
    Rule30UOR.Interfaces.rhCenter (t + Q) (p + 2) =
      Rule30UOR.Interfaces.rhCenter t (p + 2) :=
  Rule30Paper.Paper.rhcenter_agree_outward_of_white_mid t Q p hw hp hp1 hnext

/-- **Inward-outward `Q`-defect equality across a white cell in `rhCenter` from the verified paper**. -/
theorem rhcenter_defect_inward_of_white_mid_kit (t Q p : Nat)
    (hw : Rule30UOR.Interfaces.rhCenter t (p + 1) = false)
    (hp1 : Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) = Rule30UOR.Interfaces.rhCenter t (p + 1))
    (hnext : Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1)) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) p)
      (Rule30UOR.Interfaces.rhCenter t p) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) (p + 2))
        (Rule30UOR.Interfaces.rhCenter t (p + 2)) :=
  Rule30Paper.Paper.rhcenter_defect_inward_of_white_mid t Q p hw hp1 hnext

/-- **Inward `Q`-agreement from vanishing masked defect under two-time agreement at column `p + 1` from the verified paper**. -/
theorem rhcenter_agree_inward_of_col_eq_two_kit (t Q p : Nat)
    (hp1 : Rule30UOR.Interfaces.rhCenter (t + Q) (p + 1) = Rule30UOR.Interfaces.rhCenter t (p + 1))
    (hnext : Rule30UOR.Interfaces.rhCenter ((t + 1) + Q) (p + 1) =
      Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1))
    (hmask : ((!Rule30UOR.Interfaces.rhCenter t (p + 1)) &&
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + Q) (p + 2))
        (Rule30UOR.Interfaces.rhCenter t (p + 2))) = false) :
    Rule30UOR.Interfaces.rhCenter (t + Q) p = Rule30UOR.Interfaces.rhCenter t p :=
  Rule30Paper.Paper.rhcenter_agree_inward_of_col_eq_two t Q p hp1 hnext hmask

/-- **Unconditional left-light-cone obstruction to `LhBandAgree` from the verified paper**. -/
theorem not_lhbandagree_of_lt_add_kit (t Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree t Q 0 L :=
  Rule30Paper.Paper.not_lhbandagree_of_lt_add t Q L hQ hL

/-- **1-column outward step of left-half time-trace determination from the verified paper**. -/
theorem lhcenter_outward_determine_step_kit (t Q p0 S : Nat)
    (h0 : Rule30UOR.Interfaces.LhColAgree t Q p0 (S + 1))
    (h1 : Rule30UOR.Interfaces.LhColAgree t Q (p0 + 1) (S + 1)) :
    Rule30UOR.Interfaces.LhColAgree t Q (p0 + 2) S :=
  Rule30Paper.Paper.lhcenter_outward_determine_step t Q p0 S h0 h1

/-- **Multi-column outward left-half time-trace determination from the verified paper**. -/
theorem lhcenter_outward_determine_kit (t Q p0 S K : Nat)
    (h0 : Rule30UOR.Interfaces.LhColAgree t Q p0 (S + K))
    (h1 : Rule30UOR.Interfaces.LhColAgree t Q (p0 + 1) (S + K)) :
    Rule30UOR.Interfaces.LhColAgree t Q (p0 + K) S ∧
      Rule30UOR.Interfaces.LhColAgree t Q ((p0 + K) + 1) S :=
  Rule30Paper.Paper.lhcenter_outward_determine t Q p0 S K h0 h1

/-- **Spatial left-half band agreement from center time-trace from the verified paper**. -/
theorem lhbandagree_of_outward_determine_kit (t Q p0 L : Nat)
    (h0 : Rule30UOR.Interfaces.LhColAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.LhColAgree t Q (p0 + 1) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1) :=
  Rule30Paper.Paper.lhbandagree_of_outward_determine t Q p0 L h0 h1

/-- **Finite-horizon incompatibility of `LhColAgree` at columns `0` and `1` from the verified paper**. -/
theorem not_lhcolagree_zero_one_of_pos_kit (t Q S : Nat)
    (hQ : 0 < Q) (hS : t + Q ≤ S + 1)
    (h0 : Rule30UOR.Interfaces.LhColAgree t Q 0 S) :
    ¬ Rule30UOR.Interfaces.LhColAgree t Q 1 S :=
  Rule30Paper.Paper.not_lhcolagree_zero_one_of_pos t Q S hQ hS h0

/-- **Periodic center supplies `LhColAgree` at column `0` from the verified paper**. -/
theorem periodic_lhcolagree_zero_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t) :
    Rule30UOR.Interfaces.LhColAgree t (m * P) 0 S :=
  Rule30Paper.Paper.periodic_lhcolagree_zero T P hP hper m t S ht

/-- **Finite-horizon death clock for column `-1` under periodic center from the verified paper**. -/
theorem not_periodic_lhcolagree_one_horizon_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (hm : 0 < m) (ht : T ≤ t) (hS : t + m * P ≤ S + 1) :
    ¬ Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.not_periodic_lhcolagree_one_horizon T P hP hper m t S hm ht hS

/-- **Transfer of time-trace agreement from `rhCenter · 1` to `lhCenter · 1` via the §6 `Φ` fixed-point law from the verified paper**. -/
theorem periodic_lhcolagree_one_of_rhcolagree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hrh : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S) :
    Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.periodic_lhcolagree_one_of_rhcolagree_one T P hP hper m t S ht hrh

/-- **Finite-horizon death clock for right-half column `+1` under periodic center from the verified paper**. -/
theorem not_periodic_rhcolagree_one_horizon_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (hm : 0 < m) (ht : T ≤ t) (hS : t + m * P ≤ S + 1) :
    ¬ Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.not_periodic_rhcolagree_one_horizon T P hP hper m t S hm ht hS

/-- **Time-trace agreement `RhColAgree` at column `+1` from spatial `RhBandAgree` from the verified paper**. -/
theorem periodic_rhcolagree_one_of_rhbandagree_zero_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (S + 1)) :
    Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.periodic_rhcolagree_one_of_rhbandagree_zero T P hP hper m t S ht hband

/-- **Gluing `M` finite sector bands into `RhColAgree` across `M * 2^k` steps from the verified paper**. -/
theorem periodic_rhcolagree_one_of_finite_sectors_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U M m : Nat) (hM : 1 ≤ M) (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hsec : ∀ j, j < M →
      Rule30UOR.Interfaces.RhBandAgree
        ((d + (U + j) * Rule30UOR.Core.twopow k) + 1) (m * P) 0
        (Rule30UOR.Core.twopow k + 1)) :
    Rule30UOR.Interfaces.RhColAgree
      ((d + U * Rule30UOR.Core.twopow k) + 1) (m * P) 1
      (M * Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_rhcolagree_one_of_finite_sectors T P hP hper k d U M m hM ht hsec

/-- **Finite-sector refutation of `RhBandAgree` at any multiple `Q = m * P` from the verified paper**. -/
theorem not_periodic_finite_sector_rhbandagree_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U M m : Nat) (hM : 1 ≤ M) (hm : 0 < m)
    (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hS : (d + U * Rule30UOR.Core.twopow k) + m * P ≤ M * Rule30UOR.Core.twopow k) :
    ¬ (∀ j, j < M →
      Rule30UOR.Interfaces.RhBandAgree
        ((d + (U + j) * Rule30UOR.Core.twopow k) + 1) (m * P) 0
        (Rule30UOR.Core.twopow k + 1)) :=
  Rule30Paper.Paper.not_periodic_finite_sector_rhbandagree_mul T P hP hper k d U M m hM hm ht hS

/-- **Finite-sector refutation of `RhBandAgree` at `Q = lcm(P, 2^k)` from the verified paper**. -/
theorem not_periodic_finite_sector_rhbandagree_lcmperiod_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U M : Nat) (hM : 1 ≤ M)
    (ht : T ≤ d + U * Rule30UOR.Core.twopow k)
    (hS : (d + U * Rule30UOR.Core.twopow k) + Rule30UOR.Interfaces.lcmPeriod P k ≤
      M * Rule30UOR.Core.twopow k) :
    ¬ (∀ j, j < M →
      Rule30UOR.Interfaces.RhBandAgree
        ((d + (U + j) * Rule30UOR.Core.twopow k) + 1) (Rule30UOR.Interfaces.lcmPeriod P k) 0
        (Rule30UOR.Core.twopow k + 1)) :=
  Rule30Paper.Paper.not_periodic_finite_sector_rhbandagree_lcmperiod T P hP hper k d U M hM ht hS

/-- **Exact linearization of the center-adjacent OR defect in `lhCenter` via the §6 `Φ` fixed-point law from the verified paper**. -/
theorem periodic_lhcenter_or_zero_defect_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.lhCenter (t + m * P) 1 || Rule30UOR.Interfaces.lhCenter (t + m * P) 0)
      (Rule30UOR.Interfaces.lhCenter t 1 || Rule30UOR.Interfaces.lhCenter t 0) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter t 1) :=
  Rule30Paper.Paper.periodic_lhcenter_or_zero_defect_eq T P hP hper m t ht

/-- **Exact linear time-derivative law for the column `-2` defect in `lhCenter` from the verified paper**. -/
theorem periodic_lhcenter_two_defect_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + m * P) 2)
      (Rule30UOR.Interfaces.lhCenter t 2) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter ((t + 1) + m * P) 1)
          (Rule30UOR.Interfaces.lhCenter (t + 1) 1))
        (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
          (Rule30UOR.Interfaces.lhCenter t 1)) :=
  Rule30Paper.Paper.periodic_lhcenter_two_defect_eq T P hP hper m t ht

/-- **Unconditional identity between `lhCenter` and `row` bit readout from the verified paper**. -/
theorem lhcenter_eq_row_testbit_uncond_kit (t p : Nat) :
    Rule30UOR.Interfaces.lhCenter t p =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) (t + p) :=
  Rule30Paper.Paper.lhcenter_eq_row_testbit_uncond t p

/-- **Fully unconditional `2^k`-scale forward step of `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_step_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter t p)
            (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.lhcenter_scale_step_uncond t k p

/-- **Fully unconditional `2^k`-scale outward step of `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_outward_step_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.lhCenter t p))
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.lhcenter_scale_outward_step_uncond t k p

/-- **Unconditional cross-center `2^k`-scale step between `lhCenter` and `rhCenter` from the verified paper**. -/
theorem lhcenter_scale_cross_step_kit (t k r : Nat) (hr : r ≤ Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t r)
            (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k - r)))
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow (k + 1) - r)))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.lhcenter_scale_cross_step t k r hr

/-- **Unconditional cross-center `2^k`-scale formula for `rhCenter` in terms of `lhCenter` and `winWitt` from the verified paper**. -/
theorem rhcenter_eq_lhcenter_scale_cross_kit (t k r : Nat) (hr : r ≤ Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.rhCenter t r =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r))
            (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k - r)))
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow (k + 1) - r)))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.rhcenter_eq_lhcenter_scale_cross t k r hr

/-- **Cross-center `2^k`-scale transport from `LhBandAgree` and `WinWittAgree` to `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_of_lhbandagree_scale_cross_kit (t k Q L : Nat)
    (hL : L ≤ Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (Rule30UOR.Core.twopow k - L) L)
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (Rule30UOR.Core.twopow (k + 1) - L) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q 0 L :=
  Rule30Paper.Paper.rhbandagree_of_lhbandagree_scale_cross t k Q L hL hlate h1 h2 hw

/-- **Converse cross-center `2^k`-scale transport to `WinWittAgree` from the verified paper**. -/
theorem winwittagree_of_rhbandagree_lhbandagree_scale_cross_kit (t k Q L : Nat)
    (hL : L ≤ Rule30UOR.Core.twopow k)
    (hrh : Rule30UOR.Interfaces.RhBandAgree t Q 0 L)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (Rule30UOR.Core.twopow k - L) L)
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (Rule30UOR.Core.twopow (k + 1) - L) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L :=
  Rule30Paper.Paper.winwittagree_of_rhbandagree_lhbandagree_scale_cross t k Q L hL hrh hlate h1 h2

/-- **Deriving `RhBandAgree` on `[0, 2^k]` from `LhColAgree · 1` and `WinWittAgree` from the verified paper**. -/
theorem periodic_rhbandagree_of_lhcolagree_one_and_winwittagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 (Rule30UOR.Core.twopow (k + 1)))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_rhbandagree_of_lhcolagree_one_and_winwittagree T P hP hper m t k ht hcol1 hw

/-- **Converse derivation of `WinWittAgree` from `LhColAgree · 1` and `RhBandAgree` from the verified paper**. -/
theorem periodic_winwittagree_of_lhcolagree_one_and_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 (Rule30UOR.Core.twopow (k + 1)))
    (hrh : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_winwittagree_of_lhcolagree_one_and_rhbandagree T P hP hper m t k ht hcol1 hrh

/-- **Unconditional `2^k`-scale forward band transport of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_step_uncond_kit (t k Q p0 L : Nat)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.lhbandagree_scale_step_uncond t k Q p0 L h0 h1 h2 hw

/-- **Unconditional `2^k`-scale outward band transport of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_outward_step_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.lhbandagree_scale_outward_step_uncond t k Q p0 L hlate h0 h1 hw

/-- **Exact diagonal difference law of the driven left half `lhCenter` from the verified paper**. -/
theorem lhcenter_diag_diff_eq_or_kit (t p : Nat) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1))
      (Rule30UOR.Interfaces.lhCenter t (p + 2)) =
      (Rule30UOR.Interfaces.lhCenter t (p + 1) || Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_diag_diff_eq_or t p

/-- **Exact outward step law for the left-half `Q`-defect from the verified paper**. -/
theorem lhcenter_defect_outward_step_kit (t Q p : Nat) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + Q) (p + 2))
      (Rule30UOR.Interfaces.lhCenter t (p + 2)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter ((t + 1) + Q) (p + 1))
          (Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter (t + Q) (p + 1) || Rule30UOR.Interfaces.lhCenter (t + Q) p)
          (Rule30UOR.Interfaces.lhCenter t (p + 1) || Rule30UOR.Interfaces.lhCenter t p)) :=
  Rule30Paper.Paper.lhcenter_defect_outward_step t Q p

/-- **Linearized outward defect step in `lhCenter` when column `p` agrees from the verified paper**. -/
theorem lhcenter_defect_outward_of_col_eq_kit (t Q p : Nat)
    (heq : Rule30UOR.Interfaces.lhCenter (t + Q) p = Rule30UOR.Interfaces.lhCenter t p) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + Q) (p + 2))
      (Rule30UOR.Interfaces.lhCenter t (p + 2)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter ((t + 1) + Q) (p + 1))
          (Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1)))
        (!Rule30UOR.Interfaces.lhCenter t p &&
          Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + Q) (p + 1))
            (Rule30UOR.Interfaces.lhCenter t (p + 1))) :=
  Rule30Paper.Paper.lhcenter_defect_outward_of_col_eq t Q p heq

/-- **Black-cell shielding in outward left-half defect propagation from the verified paper**. -/
theorem lhcenter_defect_outward_of_black_kit (t Q p : Nat)
    (hbQ : Rule30UOR.Interfaces.lhCenter (t + Q) p = true)
    (hb0 : Rule30UOR.Interfaces.lhCenter t p = true) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + Q) (p + 2))
      (Rule30UOR.Interfaces.lhCenter t (p + 2)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter ((t + 1) + Q) (p + 1))
        (Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1)) :=
  Rule30Paper.Paper.lhcenter_defect_outward_of_black t Q p hbQ hb0

/-- **Exact left-edge vanishing of `winWitt` from the verified paper**. -/
theorem winwitt_testbit_left_edge_kit (t k : Nat) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + t + Rule30UOR.Core.twopow (k + 1)) = false :=
  Rule30Paper.Paper.winwitt_testbit_left_edge t k

/-- **Vanishing of `winWitt` strictly outside the left light cone from the verified paper**. -/
theorem winwitt_testbit_gt_left_edge_kit (t k p : Nat) (hp : t < p) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow (k + 1)) = false :=
  Rule30Paper.Paper.winwitt_testbit_gt_left_edge t k p hp

/-- **Vanishing of `winWitt` at and outside the left light cone from the verified paper**. -/
theorem winwitt_testbit_ge_left_edge_kit (t k p : Nat) (hp : t ≤ p) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow (k + 1)) = false :=
  Rule30Paper.Paper.winwitt_testbit_ge_left_edge t k p hp

/-- **Settled left-edge vanishing of `winWitt` inside the light cone from the verified paper**. -/
theorem winwitt_testbit_settled_left_kit (t k j : Nat)
    (hj : j ≤ k) (hjt : j ≤ t) (hset : Rule30UOR.Interfaces.SettledBy j t) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + (t - j) + Rule30UOR.Core.twopow (k + 1)) = false :=
  Rule30Paper.Paper.winwitt_testbit_settled_left t k j hj hjt hset

/-- **Unconditional left-edge `LhBandAgree` outside the light cone from the verified paper**. -/
theorem lhbandagree_outside_cone_kit (t Q p0 L : Nat) (h : t + Q < p0) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.lhbandagree_outside_cone t Q p0 L h

/-- **Sub-interval monotonicity of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_mono_kit (t Q p0 L p0p Lp : Nat)
    (hp : p0 ≤ p0p) (hL : p0p + Lp ≤ p0 + L)
    (h : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0p Lp :=
  Rule30Paper.Paper.lhbandagree_mono t Q p0 L p0p Lp hp hL h

/-- **Sub-interval monotonicity of `LhColAgree` from the verified paper**. -/
theorem lhcolagree_mono_kit (t Q p0 S s0 Sp : Nat)
    (hs : s0 + Sp ≤ S) (h : Rule30UOR.Interfaces.LhColAgree t Q p0 S) :
    Rule30UOR.Interfaces.LhColAgree (t + s0) Q p0 Sp :=
  Rule30Paper.Paper.lhcolagree_mono t Q p0 S s0 Sp hs h

/-- **One-step forward propagation of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_step_kit (t Q p0 L : Nat)
    (h : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 2)) :
    Rule30UOR.Interfaces.LhBandAgree (t + 1) Q (p0 + 1) L :=
  Rule30Paper.Paper.lhbandagree_step t Q p0 L h

/-- **Multi-step forward propagation of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_steps_kit (t Q p0 L s : Nat)
    (h : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 2 * s)) :
    Rule30UOR.Interfaces.LhBandAgree (t + s) Q (p0 + s) L :=
  Rule30Paper.Paper.lhbandagree_steps t Q p0 L s h

/-- **Free inward extension of `LhBandAgree` from column `-1` to column `0` under `CenterPeriodic` from the verified paper**. -/
theorem periodic_lhbandagree_zero_of_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : Rule30UOR.Interfaces.LhBandAgree t (m * P) 1 L) :
    Rule30UOR.Interfaces.LhBandAgree t (m * P) 0 (L + 1) :=
  Rule30Paper.Paper.periodic_lhbandagree_zero_of_one T P hP hper m t L ht h

/-- **Deriving `RhBandAgree` on `[0, 2^k]` from `RhColAgree · 1` and `WinWittAgree` from the verified paper**. -/
theorem periodic_rhbandagree_of_rhcolagree_one_and_winwittagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 (Rule30UOR.Core.twopow (k + 1)))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_rhbandagree_of_rhcolagree_one_and_winwittagree T P hP hper m t k ht hcol1 hw

/-- **Converse derivation of `WinWittAgree` from `RhColAgree · 1` and `RhBandAgree` from the verified paper**. -/
theorem periodic_winwittagree_of_rhcolagree_one_and_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 (Rule30UOR.Core.twopow (k + 1)))
    (hrh : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_winwittagree_of_rhcolagree_one_and_rhbandagree T P hP hper m t k ht hcol1 hrh

/-- **Fully unconditional `2^k`-scale inward step of `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_inward_step_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.lhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.lhcenter_scale_inward_step_uncond t k p

/-- **Unconditional `2^k`-scale inward band transport of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_inward_step_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.lhbandagree_scale_inward_step_uncond t k Q p0 L hlate h1 h2 hw

/-- **Unconditional `WinWittAgree` at and outside the left light cone from the verified paper**. -/
theorem winwittagree_outside_left_cone_kit (t k Q p0 L : Nat) (hp : t + Q ≤ p0) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_outside_left_cone t k Q p0 L hp

/-- **Unconditional identity between `rdiag (t + p) t` and `lhCenter t p` from the verified paper**. -/
theorem rdiag_add_eq_lhcenter_uncond_kit (t p : Nat) :
    Rule30UOR.Core.rdiag (t + p) t = Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.rdiag_add_eq_lhcenter_uncond t p

/-- **Unconditional `2^k`-scale readout of `winWitt` in `lhCenter` coordinates from the verified paper**. -/
theorem winwitt_testbit_eq_lhcenter_scale_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.lhCenter t p))
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.winwitt_testbit_eq_lhcenter_scale_uncond t k p

/-- **Unconditional `2^k`-scale band derivation of `WinWittAgree` from four `LhBandAgree` bands from the verified paper**. -/
theorem winwittagree_of_lhbandagree_scale_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L)
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_of_lhbandagree_scale_uncond t k Q p0 L hlate h0 h1 h2

/-- **Fully unconditional `2^k`-scale middle-column step of `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_mid_step_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.lhCenter t p))
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.lhcenter_scale_mid_step_uncond t k p

/-- **Unconditional `2^k`-scale middle-band transport of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_mid_step_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L)
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.lhbandagree_scale_mid_step_uncond t k Q p0 L hlate h0 h2 hw

/-- **Outer `2^k`-strip 3-term forward scale step of `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_step_outer_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter t p)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.lhcenter_scale_step_outer_strip t k p hp

/-- **Outer `2^k`-strip 3-term inward scale step of `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_inward_outer_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.lhcenter_scale_inward_outer_strip t k p hp

/-- **Outer `2^k`-strip 3-term readout of `winWitt` from the verified paper**. -/
theorem winwitt_testbit_outer_left_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.winwitt_testbit_outer_left_strip t k p hp

/-- **Outer `2^k`-strip left-diagonal difference law for `winWitt` from the verified paper**. -/
theorem winwitt_testbit_outer_left_strip_eq_ldiag_xor_kit (t k p : Nat)
    (hpt : p ≤ t) (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.ldiag (t - p) (t + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.ldiag (t - p) t) :=
  Rule30Paper.Paper.winwitt_testbit_outer_left_strip_eq_ldiag_xor t k p hpt hp

/-- **Outer `2^k`-strip inward band transport of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_inward_outer_strip_kit (t k Q p0 L : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.lhbandagree_scale_inward_outer_strip t k Q p0 L hp hlate hw

/-- **Outer `2^k`-strip forward band transport of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_step_outer_strip_kit (t k Q p0 L : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.lhbandagree_scale_step_outer_strip t k Q p0 L hp h0 hw

/-- **Outer `2^k`-strip band derivation of `WinWittAgree` from the verified paper**. -/
theorem winwittagree_outer_left_strip_kit (t k Q p0 L : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_outer_left_strip t k Q p0 L hp hlate h0

/-- **Mutual incompatibility of `LhBandAgree (t + 2^k) Q (2^k) L` and `WinWittAgree t k Q (t + 2^(k+1)) L` inside scale `2^k` from the verified paper**. -/
theorem not_lhbandagree_and_winwittagree_of_lt_twopow_kit (t k Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) (hk : t + Q < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k) L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q (t + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.not_lhbandagree_and_winwittagree_of_lt_twopow t k Q L hQ hL hk hlate

/-- **Unconditional bit readout of `frobDefect k (row t)` in `lhCenter` coordinates from the verified paper**. -/
theorem frobdefect_row_testbit_lhcenter_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t))
      (t + p + 1 + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter t (p + 1 + Rule30UOR.Core.twopow (k + 1)) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k))
              (Rule30UOR.Interfaces.lhCenter t p))
          (Rule30UOR.Interfaces.lhCenter t (p + 1 + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Core.bxor
              (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1)))
              (Rule30UOR.Interfaces.lhCenter t p)))
        (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1)))
            (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.frobdefect_row_testbit_lhcenter_uncond t k p

/-- **Vanishing of `frobDefect k (row t)` across the outer `2^k`-strip of the left cone from the verified paper**. -/
theorem frobdefect_row_testbit_lhcenter_outer_strip_eq_false_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t))
      (t + p + 1 + Rule30UOR.Core.twopow (k + 1)) = false :=
  Rule30Paper.Paper.frobdefect_row_testbit_lhcenter_outer_strip_eq_false t k p hp

/-- **Unconditional bit readout of `phiScale k (row t)` in `lhCenter` coordinates from the verified paper**. -/
theorem phiscale_row_testbit_lhcenter_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
      (t + p + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.phiscale_row_testbit_lhcenter_uncond t k p

/-- **Single-cell collapse of `phiScale k (row t)` across the outer `2^k`-strip of the left cone from the verified paper**. -/
theorem phiscale_row_testbit_lhcenter_outer_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
      (t + p + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.phiscale_row_testbit_lhcenter_outer_strip t k p hp

/-- **Single-sector collapse of `crossCarry (phiScale k (row t)) (winWitt t (2^k))` across the outer `2^k`-strip from the verified paper**. -/
theorem crosscarry_row_scale_lhcenter_outer_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.crossCarry
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
      (t + p + 1 + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
          Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + p + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + (p + 1) + Rule30UOR.Core.twopow (k + 1)) &&
          Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.crosscarry_row_scale_lhcenter_outer_strip t k p hp

/-- **Single-sector window step law across the outer `2^k`-strip of the left cone from the verified paper**. -/
theorem winwitt_step_outer_left_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + 1) + (p + 1) + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
          ((t + 1) + (p + 1) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
            Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + p + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + (p + 1) + Rule30UOR.Core.twopow (k + 1)) &&
            Rule30UOR.Interfaces.lhCenter t p)) :=
  Rule30Paper.Paper.winwitt_step_outer_left_strip t k p hp

/-- **Single-sector 1-step forward propagation of `WinWittAgree` in the outer `2^k`-strip from the verified paper**. -/
theorem winwittagree_step_outer_left_strip_kit (t k Q p0 L : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) (L + 2)) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_step_outer_left_strip t k Q p0 L hp h0 hw

/-- **Multi-step single-sector forward propagation of `WinWittAgree` in the outer `2^k`-strip from the verified paper**. -/
theorem winwittagree_steps_outer_left_strip_kit (t k Q p0 L s : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 2 * s))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) (L + 2 * s)) :
    Rule30UOR.Interfaces.WinWittAgree (t + s) k Q ((t + s) + (p0 + s) + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_steps_outer_left_strip t k Q p0 L s hp h0 hw

/-- **Outward spatial step of `winWitt` across the outer `2^k`-strip of the left cone from the verified paper**. -/
theorem winwitt_outward_step_outer_left_strip_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + (p + 2) + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
            ((t + 1) + (p + 1) + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + (p + 1) + Rule30UOR.Core.twopow (k + 1)) ||
            Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + p + Rule30UOR.Core.twopow (k + 1))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
            Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + p + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + (p + 1) + Rule30UOR.Core.twopow (k + 1)) &&
            Rule30UOR.Interfaces.lhCenter t p)) :=
  Rule30Paper.Paper.winwitt_outward_step_outer_left_strip t k p hp

/-- **Single-sector 1-cell outward spatial extension of `WinWittAgree` in the outer `2^k`-strip from the verified paper**. -/
theorem winwittagree_extend_outer_left_strip_kit (t k Q p0 L : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (hstep :
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
        ((t + 1) + (p0 + L + 1) + Rule30UOR.Core.twopow (k + 1) + Q) =
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + 1) + (p0 + L + 1) + Rule30UOR.Core.twopow (k + 1))) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) (L + 2) :=
  Rule30Paper.Paper.winwittagree_extend_outer_left_strip t k Q p0 L hp h0 hw hstep

/-- **Single-sector outward band step of `WinWittAgree` in the outer `2^k`-strip from the verified paper**. -/
theorem winwittagree_outward_step_outer_left_strip_kit (t k Q p0 L : Nat)
    (hp : t + Q < p0 + Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (hnext : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + (p0 + 2) + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_outward_step_outer_left_strip t k Q p0 L hp h0 hw hnext

/-- **3-term cross-center `2^k`-scale duality in the outer `2^(k+1)`-regime from the verified paper**. -/
theorem rhcenter_eq_lhcenter_scale_cross_outer_kit (t k r : Nat)
    (hr : r ≤ Rule30UOR.Core.twopow k) (htr : t + r < Rule30UOR.Core.twopow (k + 1)) :
    Rule30UOR.Interfaces.rhCenter t r =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r))
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k - r)))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.rhcenter_eq_lhcenter_scale_cross_outer t k r hr htr

/-- **Outer cross-center `2^k`-scale band transport to `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_of_lhbandagree_scale_cross_outer_kit (t k Q L : Nat)
    (hL : L ≤ Rule30UOR.Core.twopow k) (ht : t + Q + L < Rule30UOR.Core.twopow (k + 1))
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (Rule30UOR.Core.twopow k - L) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q 0 L :=
  Rule30Paper.Paper.rhbandagree_of_lhbandagree_scale_cross_outer t k Q L hL ht hlate h1 hw

/-- **Outer cross-center `2^k`-scale band transport to `WinWittAgree` from the verified paper**. -/
theorem winwittagree_of_rhbandagree_lhbandagree_scale_cross_outer_kit (t k Q L : Nat)
    (hL : L ≤ Rule30UOR.Core.twopow k) (ht : t + Q + L < Rule30UOR.Core.twopow (k + 1))
    (hrh : Rule30UOR.Interfaces.RhBandAgree t Q 0 L)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L)
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (Rule30UOR.Core.twopow k - L) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L :=
  Rule30Paper.Paper.winwittagree_of_rhbandagree_lhbandagree_scale_cross_outer t k Q L hL ht hrh hlate h1

/-- **Half-horizon derivation of `RhBandAgree` on `[0, 2^k]` when `t + m * P < 2^k` from the verified paper**. -/
theorem periodic_rhbandagree_of_lhcolagree_one_and_winwittagree_outer_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < Rule30UOR.Core.twopow k)
    (hcol_early : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 (Rule30UOR.Core.twopow k))
    (hcol_late : Rule30UOR.Interfaces.LhColAgree (t + Rule30UOR.Core.twopow k) (m * P) 1 (Rule30UOR.Core.twopow k))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_rhbandagree_of_lhcolagree_one_and_winwittagree_outer
    T P hP hper m t k ht htk hcol_early hcol_late hw

/-- **Half-horizon converse derivation of `WinWittAgree` when `t + m * P < 2^k` from the verified paper**. -/
theorem periodic_winwittagree_of_lhcolagree_one_and_rhbandagree_outer_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < Rule30UOR.Core.twopow k)
    (hcol_early : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 (Rule30UOR.Core.twopow k))
    (hcol_late : Rule30UOR.Interfaces.LhColAgree (t + Rule30UOR.Core.twopow k) (m * P) 1 (Rule30UOR.Core.twopow k))
    (hrh : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_winwittagree_of_lhcolagree_one_and_rhbandagree_outer
    T P hP hper m t k ht htk hcol_early hcol_late hrh

/-- **2-term in-cone cross-center `2^k`-scale duality from the verified paper**. -/
theorem rhcenter_eq_lhcenter_scale_cross_cone_kit (t k r : Nat)
    (htr : t + r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.rhCenter t r =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.rhcenter_eq_lhcenter_scale_cross_cone t k r htr

/-- **2-term in-cone cross-center readout of late `lhCenter` from the verified paper**. -/
theorem lhcenter_scale_cross_cone_kit (t k r : Nat)
    (htr : t + r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter t r)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.lhcenter_scale_cross_cone t k r htr

/-- **2-term in-cone cross-center readout of `winWitt` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_cone_kit (t k r : Nat)
    (htr : t + r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r))
        (Rule30UOR.Interfaces.rhCenter t r) :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_cone t k r htr

/-- **Direct window readout in the inter-cone zero gap from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_kit (t k r : Nat)
    (ht : t < r) (htr : t + r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap t k r ht htr

/-- **Direct readout of late `lhCenter (t + 2^k) p` from `winWitt t (2^k)` in the inter-cone zero gap from the verified paper**. -/
theorem winwitt_testbit_zero_gap_eq_lhcenter_late_kit (t k p : Nat)
    (htp : t < p) (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) p :=
  Rule30Paper.Paper.winwitt_testbit_zero_gap_eq_lhcenter_late t k p htp hp

/-- **Deriving late `LhBandAgree (t + 2^k)` directly from `WinWittAgree t` in the inter-cone zero gap from the verified paper**. -/
theorem lhbandagree_of_winwittagree_zero_gap_kit (t k Q p0 L : Nat)
    (hp0 : t + Q < p0) (hL : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L :=
  Rule30Paper.Paper.lhbandagree_of_winwittagree_zero_gap t k Q p0 L hp0 hL hw

/-- **Deriving `WinWittAgree t` directly from late `LhBandAgree (t + 2^k)` in the inter-cone zero gap from the verified paper**. -/
theorem winwittagree_of_lhbandagree_zero_gap_kit (t k Q p0 L : Nat)
    (hp0 : t + Q < p0) (hL : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.winwittagree_of_lhbandagree_zero_gap t k Q p0 L hp0 hL hlate

/-- **In-cone cross-center derivation of `RhBandAgree` without early `LhBandAgree` from the verified paper**. -/
theorem rhbandagree_of_lhbandagree_and_winwittagree_cross_cone_kit (t k Q L : Nat)
    (ht : t + Q + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q 0 L :=
  Rule30Paper.Paper.rhbandagree_of_lhbandagree_and_winwittagree_cross_cone t k Q L ht hlate hw

/-- **In-cone cross-center derivation of `WinWittAgree` without early `LhBandAgree` from the verified paper**. -/
theorem winwittagree_of_rhbandagree_and_lhbandagree_cross_cone_kit (t k Q L : Nat)
    (ht : t + Q + L < Rule30UOR.Core.twopow k)
    (hrh : Rule30UOR.Interfaces.RhBandAgree t Q 0 L)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L :=
  Rule30Paper.Paper.winwittagree_of_rhbandagree_and_lhbandagree_cross_cone t k Q L ht hrh hlate

/-- **In-cone cross-center derivation of late `LhBandAgree` from `RhBandAgree` and `WinWittAgree` from the verified paper**. -/
theorem lhbandagree_of_rhbandagree_and_winwittagree_cross_cone_kit (t k Q L : Nat)
    (ht : t + Q + L < Rule30UOR.Core.twopow k)
    (hrh : Rule30UOR.Interfaces.RhBandAgree t Q 0 L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L :=
  Rule30Paper.Paper.lhbandagree_of_rhbandagree_and_winwittagree_cross_cone t k Q L ht hrh hw

/-- **Deriving `RhBandAgree` from late `LhColAgree (t + 2^k)` alone when `t + m * P + L < 2^k` from the verified paper**. -/
theorem periodic_rhbandagree_of_lhcolagree_late_and_winwittagree_cone_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k L : Nat) (ht : T ≤ t) (htk : t + m * P + L < Rule30UOR.Core.twopow k)
    (hcol_late : Rule30UOR.Interfaces.LhColAgree (t + Rule30UOR.Core.twopow k) (m * P) 1 (Rule30UOR.Core.twopow k))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k (m * P) ((t + Rule30UOR.Core.twopow (k + 1)) - L) L) :
    Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 L :=
  Rule30Paper.Paper.periodic_rhbandagree_of_lhcolagree_late_and_winwittagree_cone
    T P hP hper m t k L ht htk hcol_late hw

/-- **Converse derivation of `WinWittAgree` from late `LhColAgree (t + 2^k)` and `RhBandAgree` when `t + m * P + L < 2^k` from the verified paper**. -/
theorem periodic_winwittagree_of_lhcolagree_late_and_rhbandagree_cone_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k L : Nat) (ht : T ≤ t) (htk : t + m * P + L < Rule30UOR.Core.twopow k)
    (hcol_late : Rule30UOR.Interfaces.LhColAgree (t + Rule30UOR.Core.twopow k) (m * P) 1 (Rule30UOR.Core.twopow k))
    (hrh : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 L) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) ((t + Rule30UOR.Core.twopow (k + 1)) - L) L :=
  Rule30Paper.Paper.periodic_winwittagree_of_lhcolagree_late_and_rhbandagree_cone
    T P hP hper m t k L ht htk hcol_late hrh

/-- **1-step evolution of late `lhCenter` in the outer `2^k`-strip via `winWitt` from the verified paper**. -/
theorem lhcenter_step_outer_strip_from_winwitt_kit (t k p : Nat)
    (hp : t < p + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) ((p + 1) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter t (p + 2))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + (p + 2) + Rule30UOR.Core.twopow (k + 1))))
        ((Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter t (p + 1))
            (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + (p + 1) + Rule30UOR.Core.twopow (k + 1)))) ||
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter t p)
            (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + p + Rule30UOR.Core.twopow (k + 1))))) :=
  Rule30Paper.Paper.lhcenter_step_outer_strip_from_winwitt t k p hp

/-- **Unconditional 1-step spatiotemporal difference law of `winWitt` in `lhCenter` coordinates from the verified paper**. -/
theorem winwitt_step_lhcenter_defect_uncond_kit (t k p : Nat) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + 1) + (p + 1) + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + (p + 2) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.bxor
              (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) ((p + 1) + Rule30UOR.Core.twopow k) ||
                Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k))
              (Rule30UOR.Interfaces.lhCenter t (p + 1) || Rule30UOR.Interfaces.lhCenter t p))
            (Rule30UOR.Interfaces.lhCenter t ((p + 1) + Rule30UOR.Core.twopow k) ||
              Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow k)))
          (Rule30UOR.Interfaces.lhCenter t ((p + 1) + Rule30UOR.Core.twopow (k + 1)) ||
            Rule30UOR.Interfaces.lhCenter t (p + Rule30UOR.Core.twopow (k + 1)))) :=
  Rule30Paper.Paper.winwitt_step_lhcenter_defect_uncond t k p

/-- **Unconditional 1-step forward transport of `WinWittAgree` via four `LhBandAgree` bands from the verified paper**. -/
theorem winwittagree_step_of_lhbandagree_scale_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) (L + 1))
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) (L + 1))
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + (p0 + 2) + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_step_of_lhbandagree_scale_uncond t k Q p0 L hlate h0 h1 h2 hw

/-- **Unconditional 1-step outward transport of `WinWittAgree` via four `LhBandAgree` bands from the verified paper**. -/
theorem winwittagree_outward_of_lhbandagree_scale_uncond_kit (t k Q p0 L : Nat)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) (L + 1))
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (h1 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow k) (L + 1))
    (h2 : Rule30UOR.Interfaces.LhBandAgree t Q (p0 + Rule30UOR.Core.twopow (k + 1)) (L + 1))
    (hnext : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + (p0 + 2) + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_outward_of_lhbandagree_scale_uncond t k Q p0 L hlate h0 h1 h2 hnext

/-- **Single-term collapse of `phiScale k (row t)` in Sector 1 from the verified paper**. -/
theorem phiscale_row_testbit_lhcenter_sector_one_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
      (t + p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.phiscale_row_testbit_lhcenter_sector_one t k p hp

/-- **Same-column `2^k`-scale step of `lhCenter` inside the `2^k`-horizon from the verified paper**. -/
theorem lhcenter_scale_same_col_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter t p)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.lhcenter_scale_same_col_cone t k p hp

/-- **Same-column `2^k`-scale pullback of `lhCenter` inside the `2^k`-horizon from the verified paper**. -/
theorem lhcenter_scale_inward_same_col_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) p)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + p + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.lhcenter_scale_inward_same_col_cone t k p hp

/-- **Exact readout of Sector-1 `winWitt` as the same-column `2^k`-time jump of `lhCenter` from the verified paper**. -/
theorem winwitt_testbit_sector_one_lhcenter_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) p)
        (Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.winwitt_testbit_sector_one_lhcenter t k p hp

/-- **Same-column `2^k`-scale forward step of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_same_col_cone_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L :=
  Rule30Paper.Paper.lhbandagree_scale_same_col_cone t k Q p0 L hp h0 hw

/-- **Same-column `2^k`-scale pullback of `LhBandAgree` from the verified paper**. -/
theorem lhbandagree_scale_inward_same_col_cone_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.lhbandagree_scale_inward_same_col_cone t k Q p0 L hp hlate hw

/-- **Deriving Sector-1 `WinWittAgree` from same-column `LhBandAgree` at `t + 2^k` and `t` from the verified paper**. -/
theorem winwittagree_sector_one_lhcenter_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.winwittagree_sector_one_lhcenter t k Q p0 L hp hlate h0

/-- **Refutation of simultaneous late same-column `LhBandAgree` and Sector-1 `WinWittAgree` from the verified paper**. -/
theorem not_lhbandagree_late_and_winwittagree_sector_one_kit (t k Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) (htk : t + Q + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q 0 L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q (t + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.not_lhbandagree_late_and_winwittagree_sector_one t k Q L hQ hL htk hlate

/-- **Identical vanishing of Sector-1 `frobDefect k (row t)` across the left half from the verified paper**. -/
theorem frobdefect_row_testbit_lhcenter_sector_one_eq_false_kit (t k p : Nat)
    (hp : t + p + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t))
      ((t + p + 1) + Rule30UOR.Core.twopow k) = false :=
  Rule30Paper.Paper.frobdefect_row_testbit_lhcenter_sector_one_eq_false t k p hp

/-- **Single-sector collapse of Sector-1 `crossCarry` across the left half from the verified paper**. -/
theorem crosscarry_row_scale_lhcenter_sector_one_kit (t k p : Nat)
    (hp : t + p + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.crossCarry
        (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
      ((t + p + 1) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
          Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + p + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + (p + 1) + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.crosscarry_row_scale_lhcenter_sector_one t k p hp

/-- **Single-sector window step of Sector-1 `winWitt` across the left half from the verified paper**. -/
theorem winwitt_step_sector_one_lhcenter_kit (t k p : Nat)
    (hp : t + p + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + 1) + (p + 1) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
          ((t + 1) + (p + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
            Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + p + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + (p + 1) + Rule30UOR.Core.twopow k) &&
            Rule30UOR.Interfaces.lhCenter t p)) :=
  Rule30Paper.Paper.winwitt_step_sector_one_lhcenter t k p hp

/-- **Single-sector forward step of Sector-1 `WinWittAgree` from the verified paper**. -/
theorem winwittagree_step_sector_one_lhcenter_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L + 1 < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) (L + 2)) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.winwittagree_step_sector_one_lhcenter t k Q p0 L hp hb hw

/-- **Single-sector outward step of Sector-1 `WinWittAgree` from the verified paper**. -/
theorem winwittagree_outward_step_sector_one_lhcenter_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L + 1 < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) (L + 1))
    (hnext : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q (t + p0 + Rule30UOR.Core.twopow k) (L + 2) :=
  Rule30Paper.Paper.winwittagree_outward_step_sector_one_lhcenter t k Q p0 L hp hb hw hnext

/-- **Automatic `m * P`-invariance of the Sector-1 center-slot window bit inside the `2^k`-horizon from the verified paper**. -/
theorem periodic_winwitt_sector_one_zero_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
      ((t + m * P) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        (t + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_winwitt_sector_one_zero_eq T P hP hper m t k ht htk

/-- **Exact linear discrete time-derivative law for the Sector-1 column-`-2` window defect from the verified paper**. -/
theorem periodic_winwitt_sector_one_two_defect_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        ((t + m * P) + 2 + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        (t + 2 + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt ((t + 1) + m * P) (Rule30UOR.Core.twopow k))
            (((t + 1) + m * P) + 1 + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
            ((t + 1) + 1 + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
            ((t + m * P) + 1 + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + 1 + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.periodic_winwitt_sector_one_two_defect_eq T P hP hper m t k ht htk

/-- **Finite-horizon right-light-cone refutation of `RhBandAgree` from the verified paper**. -/
theorem not_rhbandagree_of_lt_add_kit (t Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) :
    ¬ Rule30UOR.Interfaces.RhBandAgree t Q 0 L :=
  Rule30Paper.Paper.not_rhbandagree_of_lt_add t Q L hQ hL

/-- **Single-term collapse of `phiScale k (row t)` at `(t + 2^k) - p` inside the `2^k`-horizon from the verified paper**. -/
theorem phiscale_row_testbit_rhcenter_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
      ((t + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Interfaces.rhCenter t p :=
  Rule30Paper.Paper.phiscale_row_testbit_rhcenter_cone t k p hp

/-- **Same-column `2^k`-scale step of `rhCenter` inside the `2^k`-horizon from the verified paper**. -/
theorem rhcenter_scale_same_col_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter t p)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - p)) :=
  Rule30Paper.Paper.rhcenter_scale_same_col_cone t k p hp

/-- **Same-column `2^k`-scale pullback of `rhCenter` inside the `2^k`-horizon from the verified paper**. -/
theorem rhcenter_scale_inward_same_col_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) p)
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - p)) :=
  Rule30Paper.Paper.rhcenter_scale_inward_same_col_cone t k p hp

/-- **Exact readout of `winWitt` at `(t + 2^k) - p` as the same-column `2^k`-time jump of `rhCenter` from the verified paper**. -/
theorem winwitt_testbit_rhcenter_same_col_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) p)
        (Rule30UOR.Interfaces.rhCenter t p) :=
  Rule30Paper.Paper.winwitt_testbit_rhcenter_same_col_cone t k p hp

/-- **Direct readout of late `rhCenter (t + 2^k) p` in the inter-cone zero gap from the verified paper**. -/
theorem winwitt_testbit_zero_gap_eq_rhcenter_late_kit (t k p : Nat)
    (htp : t < p) (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) p :=
  Rule30Paper.Paper.winwitt_testbit_zero_gap_eq_rhcenter_late t k p htp hp

/-- **Same-column `2^k`-scale forward step of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_same_col_cone_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (h0 : Rule30UOR.Interfaces.RhBandAgree t Q p0 L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow k) - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_same_col_cone t k Q p0 L hp h0 hw

/-- **Same-column `2^k`-scale pullback of `RhBandAgree` from the verified paper**. -/
theorem rhbandagree_scale_inward_same_col_cone_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow k) - (p0 + L)) L) :
    Rule30UOR.Interfaces.RhBandAgree t Q p0 L :=
  Rule30Paper.Paper.rhbandagree_scale_inward_same_col_cone t k Q p0 L hp hlate hw

/-- **Deriving `WinWittAgree` at `(t + 2^k) - (p0 + L)` from same-column `RhBandAgree` at `t + 2^k` and `t` from the verified paper**. -/
theorem winwittagree_rhcenter_same_col_cone_kit (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L)
    (h0 : Rule30UOR.Interfaces.RhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow k) - (p0 + L)) L :=
  Rule30Paper.Paper.winwittagree_rhcenter_same_col_cone t k Q p0 L hp hlate h0

/-- **Refutation of simultaneous late same-column `RhBandAgree` and right-wing `WinWittAgree` from the verified paper**. -/
theorem not_rhbandagree_late_and_winwittagree_cone_kit (t k Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) (htk : t + Q + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q 0 L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow k) - L) L :=
  Rule30Paper.Paper.not_rhbandagree_late_and_winwittagree_cone t k Q L hQ hL htk hlate

/-- **Extracting `LhBandAgree t Q 0 R` from two-sided symmetric `RowAgree t Q (t - R) (2 * R)` from the verified paper**. -/
theorem lhbandagree_of_rowagree_symm_kit (t Q R : Nat)
    (hR : R ≤ t)
    (hrow : Rule30UOR.Interfaces.RowAgree t Q (t - R) (2 * R)) :
    Rule30UOR.Interfaces.LhBandAgree t Q 0 R :=
  Rule30Paper.Paper.lhbandagree_of_rowagree_symm t Q R hR hrow

/-- **Symmetric doubling from `RhBandAgree` to `LhBandAgree` across the periodic center from the verified paper**. -/
theorem periodic_lhbandagree_zero_of_rhbandagree_zero_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t R : Nat) (ht : T ≤ t) (hR : R ≤ t)
    (hrh : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 R) :
    Rule30UOR.Interfaces.LhBandAgree t (m * P) 0 R :=
  Rule30Paper.Paper.periodic_lhbandagree_zero_of_rhbandagree_zero T P hP hper m t R ht hR hrh

/-- **Late-time symmetric doubling from `RhBandAgree (t + 2^k)` to `LhBandAgree (t + 2^k)` without `R ≤ t` from the verified paper**. -/
theorem periodic_lhbandagree_late_of_rhbandagree_late_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k R : Nat) (ht : T ≤ t) (hR : R ≤ Rule30UOR.Core.twopow k)
    (hrh : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) (m * P) 0 R) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) (m * P) 0 R :=
  Rule30Paper.Paper.periodic_lhbandagree_late_of_rhbandagree_late T P hP hper m t k R ht hR hrh

/-- **Cross-wing refutation of late `RhBandAgree (t + 2^k)` and left Sector-1 `WinWittAgree` from the verified paper**. -/
theorem not_periodic_rhbandagree_late_and_winwittagree_sector_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k L : Nat) (hm : 0 < m) (ht : T ≤ t) (hL : t + m * P ≤ L)
    (htk : t + m * P + L < Rule30UOR.Core.twopow k)
    (hrh_late : Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) (m * P) 0 L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.not_periodic_rhbandagree_late_and_winwittagree_sector_one
    T P hP hper m t k L hm ht hL htk hrh_late

/-- **Symmetric doubling of Sector-1 `WinWittAgree` across the periodic center from the verified paper**. -/
theorem periodic_winwittagree_sector_one_left_of_right_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k R : Nat) (ht : T ≤ t) (hR : R ≤ t) (htk : t + m * P + R < Rule30UOR.Core.twopow k)
    (hrh0 : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 R)
    (hw_right : Rule30UOR.Interfaces.WinWittAgree t k (m * P) ((t + Rule30UOR.Core.twopow k) - R) R) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) R :=
  Rule30Paper.Paper.periodic_winwittagree_sector_one_left_of_right
    T P hP hper m t k R ht hR htk hrh0 hw_right

/-- **Universal vanishing of `frobDefect k (row t)` above the Sector-0 light cone and below Sector 2 from the verified paper**. -/
theorem frobdefect_row_testbit_gt_two_mul_eq_false_kit (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t)) b = false :=
  Rule30Paper.Paper.frobdefect_row_testbit_gt_two_mul_eq_false t k b hb0 hb1

/-- **Vanishing of `frobDefect k (row t)` across the right half and center of Sector 1 from the verified paper**. -/
theorem frobdefect_row_testbit_rhcenter_cone_eq_false_kit (t k p : Nat)
    (hp : (t + p) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t))
      ((t + Rule30UOR.Core.twopow k) - p) = false :=
  Rule30Paper.Paper.frobdefect_row_testbit_rhcenter_cone_eq_false t k p hp

/-- **Single-sector collapse of Sector-1 `crossCarry` across the right half and center from the verified paper**. -/
theorem crosscarry_row_scale_rhcenter_cone_kit (t k p : Nat)
    (hp : (t + p) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Interfaces.crossCarry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
          (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
        ((t + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter t p &&
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow k) - (p + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow k) - p) &&
          Rule30UOR.Interfaces.rhCenter t (p + 1)) :=
  Rule30Paper.Paper.crosscarry_row_scale_rhcenter_cone t k p hp

/-- **Single-sector window step of `winWitt` across the right half and center from the verified paper**. -/
theorem winwitt_step_rhcenter_cone_kit (t k p : Nat)
    (hp : (t + p) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        (((t + 1) + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
          (((t + 1) + Rule30UOR.Core.twopow k) - p))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.rhCenter t p &&
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - (p + 1)))
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - p) &&
            Rule30UOR.Interfaces.rhCenter t (p + 1))) :=
  Rule30Paper.Paper.winwitt_step_rhcenter_cone t k p hp

/-- **Pure `Φ`-evolution of `winWitt` in the right inter-cone zero gap from the verified paper**. -/
theorem winwitt_step_zero_gap_eq_phi_kit (t k p : Nat)
    (htp : t < p) (hp : (t + p) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        (((t + 1) + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
        (((t + 1) + Rule30UOR.Core.twopow k) - p) :=
  Rule30Paper.Paper.winwitt_step_zero_gap_eq_phi t k p htp hp

/-- **Pure `Φ`-evolution of `winWitt` in the left outer cone gap from the verified paper**. -/
theorem winwitt_step_lhcenter_zero_gap_eq_phi_kit (t k p : Nat)
    (htp : t < p) (hp : (t + p) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        (((t + 1) + (p + 1)) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
        (((t + 1) + (p + 1)) + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.winwitt_step_lhcenter_zero_gap_eq_phi t k p htp hp

/-- **Single-sector forward step of right-wing `WinWittAgree` from the verified paper**. -/
theorem winwittagree_step_rhcenter_cone_kit (t k Q p0 L : Nat)
    (hp : (((t + Q) + p0) + L) + 1 < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 1)) (L + 2)) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q
      (((t + 1) + Rule30UOR.Core.twopow k) - (p0 + L)) L :=
  Rule30Paper.Paper.winwittagree_step_rhcenter_cone t k Q p0 L hp hb hw

/-- **Single-sector inward extension of right-wing `WinWittAgree` toward the center from the verified paper**. -/
theorem winwittagree_inward_step_rhcenter_cone_kit (t k Q p0 L : Nat)
    (hp : (((t + Q) + p0) + L) + 1 < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 1))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 1)) (L + 1))
    (hnext : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q
      (((t + 1) + Rule30UOR.Core.twopow k) - (p0 + L)) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 1)) (L + 2) :=
  Rule30Paper.Paper.winwittagree_inward_step_rhcenter_cone t k Q p0 L hp hb hw hnext

/-- **Exact center-slot step law of Sector-1 `winWitt` from the verified paper**. -/
theorem winwitt_step_sector_one_center_slot_kit (t k : Nat)
    (htk : t + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + 1) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + Rule30UOR.Core.twopow k) ||
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - 1))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center t &&
              Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                ((t + Rule30UOR.Core.twopow k) - 1))
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                (t + Rule30UOR.Core.twopow k) &&
              Rule30UOR.Interfaces.rhCenter t 1))) :=
  Rule30Paper.Paper.winwitt_step_sector_one_center_slot t k htk

/-- **`Φ`-coupled Sector-1 column-`-1` window defect law (late-center form) from the verified paper**. -/
theorem periodic_winwitt_sector_one_one_defect_eq_late_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : (t + m * P) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + 1) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + m * P) 1)
            (Rule30UOR.Interfaces.rhCenter t 1))
        (!Rule30UOR.Core.center (t + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
              (((t + m * P) + Rule30UOR.Core.twopow k) - 1))
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - 1))) :=
  Rule30Paper.Paper.periodic_winwitt_sector_one_one_defect_eq_late T P hP hper m t k ht htk

/-- **`Φ`-coupled Sector-1 column-`-1` window defect law (early-center form) from the verified paper**. -/
theorem periodic_winwitt_sector_one_one_defect_eq_early_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : (t + m * P) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + 1) + Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + Rule30UOR.Core.twopow k) &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.rhCenter ((t + Rule30UOR.Core.twopow k) + m * P) 1)
            (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) 1))
        (!Rule30UOR.Core.center t &&
          Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
              (((t + m * P) + Rule30UOR.Core.twopow k) - 1))
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - 1))) :=
  Rule30Paper.Paper.periodic_winwitt_sector_one_one_defect_eq_early T P hP hper m t k ht htk

/-- **Direct gated transfer between right and left column-`1` window slots when the center window slot vanishes from the verified paper**. -/
theorem periodic_winwitt_sector_one_one_defect_of_witt_zero_false_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : (t + m * P) + 1 < Rule30UOR.Core.twopow k)
    (hw0 : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      (t + Rule30UOR.Core.twopow k) = false) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + 1) + Rule30UOR.Core.twopow k)) =
      (!Rule30UOR.Core.center t &&
        Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
            (((t + m * P) + Rule30UOR.Core.twopow k) - 1))
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow k) - 1))) :=
  Rule30Paper.Paper.periodic_winwitt_sector_one_one_defect_of_witt_zero_false
    T P hP hper m t k ht htk hw0

/-- **Exact identification of left column-`-1` window defect with gated `rhCenter · 1` defect under right-slot agreement from the verified paper**. -/
theorem periodic_winwitt_sector_one_one_defect_of_witt_right_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : (t + m * P) + 1 < Rule30UOR.Core.twopow k)
    (hwr : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + Rule30UOR.Core.twopow k) - 1) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - 1)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + 1) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + 1) + Rule30UOR.Core.twopow k)) =
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + Rule30UOR.Core.twopow k) &&
        Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + m * P) 1)
          (Rule30UOR.Interfaces.rhCenter t 1)) :=
  Rule30Paper.Paper.periodic_winwitt_sector_one_one_defect_of_witt_right_eq
    T P hP hper m t k ht htk hwr

/-- **Symmetric doubling of Sector-1 `WinWittAgree` at width `1` without `1 ≤ t` from the verified paper**. -/
theorem periodic_winwittagree_sector_one_two_of_right_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : (t + m * P) + 1 < Rule30UOR.Core.twopow k)
    (hr1 : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hwr : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + Rule30UOR.Core.twopow k) - 1) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - 1)) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) 1 :=
  Rule30Paper.Paper.periodic_winwittagree_sector_one_two_of_right_one
    T P hP hper m t k ht htk hr1 hwr

/-- **Extending Sector-1 `WinWittAgree` to width `2` from two steps of right column-`+1` agreement from the verified paper**. -/
theorem periodic_winwittagree_sector_one_three_of_right_one_step_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : (t + m * P) + 2 < Rule30UOR.Core.twopow k)
    (hr1 : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hr1_next : Rule30UOR.Interfaces.rhCenter ((t + 1) + m * P) 1 =
      Rule30UOR.Interfaces.rhCenter (t + 1) 1)
    (hwr : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + m * P) (Rule30UOR.Core.twopow k))
        (((t + m * P) + Rule30UOR.Core.twopow k) - 1) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - 1))
    (hwr_next : Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.winWitt ((t + 1) + m * P) (Rule30UOR.Core.twopow k))
        ((((t + 1) + m * P) + Rule30UOR.Core.twopow k) - 1) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        (((t + 1) + Rule30UOR.Core.twopow k) - 1)) :
    Rule30UOR.Interfaces.WinWittAgree t k (m * P) (t + Rule30UOR.Core.twopow k) 2 :=
  Rule30Paper.Paper.periodic_winwittagree_sector_one_three_of_right_one_step
    T P hP hper m t k ht htk hr1 hr1_next hwr hwr_next

/-- **Universal sideways inversion of `winWitt` from the verified paper**. -/
theorem winwitt_inward_step_frobdefect_testbit_succ_kit (t k b : Nat)
    (hb : 1 ≤ b) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (b + 1) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k)) (b + 1))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) b ||
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (b - 1))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.wittBitBool
              (Rule30UOR.Interfaces.crossCarry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
                (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))) b)
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Interfaces.frobDefect k (Rule30UOR.Core.row t)) b))) :=
  Rule30Paper.Paper.winwitt_inward_step_frobdefect_testbit_succ t k b hb

/-- **Sideways inversion of `winWitt` above the Sector-0 light cone from the verified paper**. -/
theorem winwitt_inward_step_gt_two_mul_kit (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (b + 1) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k)) (b + 1))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) b ||
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (b - 1))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Interfaces.crossCarry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
              (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))) b)) :=
  Rule30Paper.Paper.winwitt_inward_step_gt_two_mul t k b hb0 hb1

/-- **Sideways readout of the left column-`-1` window bit from center and right-half data from the verified paper**. -/
theorem winwitt_sector_one_one_from_center_and_right_kit (t k : Nat)
    (htk : t + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + 1) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              (t + Rule30UOR.Core.twopow k) ||
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - 1))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Core.center t &&
              Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                ((t + Rule30UOR.Core.twopow k) - 1))
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                (t + Rule30UOR.Core.twopow k) &&
              Rule30UOR.Interfaces.rhCenter t 1))) :=
  Rule30Paper.Paper.winwitt_sector_one_one_from_center_and_right t k htk

/-- **Sideways outward inversion of `winWitt` across the left half of Sector 1 from the verified paper**. -/
theorem winwitt_inward_step_sector_one_lhcenter_kit (t k p : Nat)
    (hp : (t + p) + 1 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + (p + 2)) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          (((t + 1) + (p + 1)) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + (p + 1)) + Rule30UOR.Core.twopow k) ||
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + p) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter t (p + 1) &&
              Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                ((t + p) + Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                ((t + (p + 1)) + Rule30UOR.Core.twopow k) &&
              Rule30UOR.Interfaces.lhCenter t p))) :=
  Rule30Paper.Paper.winwitt_inward_step_sector_one_lhcenter t k p hp

/-- **Sideways inward inversion of `winWitt` across the right half of Sector 1 from the verified paper**. -/
theorem winwitt_inward_step_rhcenter_cone_kit (t k p : Nat)
    (hp : (t + p) + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          (((t + 1) + Rule30UOR.Core.twopow k) - (p + 1)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - (p + 1)) ||
            Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
              ((t + Rule30UOR.Core.twopow k) - (p + 2)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.rhCenter t (p + 1) &&
              Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                ((t + Rule30UOR.Core.twopow k) - (p + 2)))
            (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
                ((t + Rule30UOR.Core.twopow k) - (p + 1)) &&
              Rule30UOR.Interfaces.rhCenter t (p + 2)))) :=
  Rule30Paper.Paper.winwitt_inward_step_rhcenter_cone t k p hp

/-- **Pure-`Φ` sideways inward inversion of `winWitt` in the right inter-cone zero gap from the verified paper**. -/
theorem winwitt_inward_step_zero_gap_kit (t k p : Nat)
    (htp : t ≤ p) (hp : (t + p) + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - p) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          (((t + 1) + Rule30UOR.Core.twopow k) - (p + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow k) - (p + 1)) ||
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow k) - (p + 2))) :=
  Rule30Paper.Paper.winwitt_inward_step_zero_gap t k p htp hp

/-- **Unconditional forward step of `WinWittAgree` in the right inter-cone zero gap from the verified paper**. -/
theorem winwittagree_step_zero_gap_kit (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : (((t + Q) + p0) + L) + 1 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 1)) (L + 2)) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q
      (((t + 1) + Rule30UOR.Core.twopow k) - (p0 + L)) L :=
  Rule30Paper.Paper.winwittagree_step_zero_gap t k Q p0 L hp0 hp hw

/-- **Unconditional inward extension of `WinWittAgree` in the right inter-cone zero gap from the verified paper**. -/
theorem winwittagree_inward_step_zero_gap_kit (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : (((t + Q) + p0) + L) + 1 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 1)) (L + 1))
    (hnext : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q
      (((t + 1) + Rule30UOR.Core.twopow k) - (p0 + L)) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 1)) (L + 2) :=
  Rule30Paper.Paper.winwittagree_inward_step_zero_gap t k Q p0 L hp0 hp hw hnext

/-- **Unconditional forward step of `WinWittAgree` in the left outer cone gap from the verified paper**. -/
theorem winwittagree_step_lhcenter_zero_gap_kit (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : (((t + Q) + p0) + L) + 1 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + p0) + Rule30UOR.Core.twopow k) (L + 2)) :
    Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q
      (((t + 1) + (p0 + 1)) + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.winwittagree_step_lhcenter_zero_gap t k Q p0 L hp0 hp hw

/-- **Unconditional outward extension of `WinWittAgree` in the left outer cone gap from the verified paper**. -/
theorem winwittagree_outward_step_lhcenter_zero_gap_kit (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : (((t + Q) + p0) + L) + 1 < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + p0) + Rule30UOR.Core.twopow k) (L + 1))
    (hnext : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q
      (((t + 1) + (p0 + 1)) + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + p0) + Rule30UOR.Core.twopow k) (L + 2) :=
  Rule30Paper.Paper.winwittagree_outward_step_lhcenter_zero_gap t k Q p0 L hp0 hp hw hnext

/-- **Multi-step forward propagation of right-wing `WinWittAgree` across the right half from the verified paper**. -/
theorem winwittagree_steps_rhcenter_cone_kit (t k Q p0 L s : Nat)
    (hp : (((t + Q) + p0) + L) + 2 * s < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 2 * s))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 2 * s)) (L + 2 * s)) :
    Rule30UOR.Interfaces.WinWittAgree (t + s) k Q
      (((t + s) + Rule30UOR.Core.twopow k) - ((p0 + s) + L)) L :=
  Rule30Paper.Paper.winwittagree_steps_rhcenter_cone t k Q p0 L s hp hb hw

/-- **Multi-step propagation of late `RhBandAgree ((t + s) + 2^k)` from early `RhBandAgree` and `WinWittAgree` from the verified paper**. -/
theorem rhbandagree_late_steps_cone_kit (t k Q p0 L s : Nat)
    (hp : (((t + Q) + p0) + L) + 2 * s < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.RhBandAgree t Q p0 (L + 2 * s))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 2 * s)) (L + 2 * s)) :
    Rule30UOR.Interfaces.RhBandAgree ((t + s) + Rule30UOR.Core.twopow k) Q (p0 + s) L :=
  Rule30Paper.Paper.rhbandagree_late_steps_cone t k Q p0 L s hp hb hw

/-- **Multi-step unconditional forward propagation of `WinWittAgree` in the right inter-cone zero gap from the verified paper**. -/
theorem winwittagree_steps_zero_gap_kit (t k Q p0 L s : Nat)
    (hp0 : t + Q < p0)
    (hp : (((t + Q) + p0) + L) + 2 * s < Rule30UOR.Core.twopow k)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + Rule30UOR.Core.twopow k) - ((p0 + L) + 2 * s)) (L + 2 * s)) :
    Rule30UOR.Interfaces.WinWittAgree (t + s) k Q
      (((t + s) + Rule30UOR.Core.twopow k) - ((p0 + s) + L)) L :=
  Rule30Paper.Paper.winwittagree_steps_zero_gap t k Q p0 L s hp0 hp hw

/-- **Multi-step forward propagation of Sector-1 `WinWittAgree` across the left half from the verified paper**. -/
theorem winwittagree_steps_sector_one_lhcenter_kit (t k Q p0 L s : Nat)
    (hp : (((t + Q) + p0) + L) + 2 * s < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 2 * s))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + p0) + Rule30UOR.Core.twopow k) (L + 2 * s)) :
    Rule30UOR.Interfaces.WinWittAgree (t + s) k Q
      (((t + s) + (p0 + s)) + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.winwittagree_steps_sector_one_lhcenter t k Q p0 L s hp hb hw

/-- **Multi-step propagation of late `LhBandAgree ((t + s) + 2^k)` from early `LhBandAgree` and `WinWittAgree` from the verified paper**. -/
theorem lhbandagree_late_steps_sector_one_kit (t k Q p0 L s : Nat)
    (hp : (((t + Q) + p0) + L) + 2 * s < Rule30UOR.Core.twopow k)
    (hb : Rule30UOR.Interfaces.LhBandAgree t Q p0 (L + 2 * s))
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q
      ((t + p0) + Rule30UOR.Core.twopow k) (L + 2 * s)) :
    Rule30UOR.Interfaces.LhBandAgree ((t + s) + Rule30UOR.Core.twopow k) Q (p0 + s) L :=
  Rule30Paper.Paper.lhbandagree_late_steps_sector_one t k Q p0 L s hp hb hw

/-! ### Batch 16: Raw Inter-Cone Pure-`Φ` Window Evolution, Non-Overlapping 3-Sector Copy Laws of `phiScale`, and Early-Free Cross-Sector Window Duality -/

/-- **Vanishing of `phiScale k (row t)` across the raw inter-cone gap from the verified paper**. -/
theorem phiscale_row_testbit_inter_cone_gap_eq_false_kit (t k b : Nat)
    (hb0 : 2 * t < b) (hb1 : b < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t)) b = false :=
  Rule30Paper.Paper.phiscale_row_testbit_inter_cone_gap_eq_false t k b hb0 hb1

/-- **Direct readout of late `row (t + 2^k)` across the raw inter-cone gap from the verified paper**. -/
theorem winwitt_testbit_inter_cone_gap_eq_row_late_kit (t k b : Nat)
    (hb0 : 2 * t < b) (hb1 : b < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) b =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row (t + Rule30UOR.Core.twopow k)) b :=
  Rule30Paper.Paper.winwitt_testbit_inter_cone_gap_eq_row_late t k b hb0 hb1

/-- **Vanishing of `crossCarry` across the raw inter-cone gap from the verified paper**. -/
theorem crosscarry_row_scale_inter_cone_gap_eq_false_kit (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.crossCarry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))) b = false :=
  Rule30Paper.Paper.crosscarry_row_scale_inter_cone_gap_eq_false t k b hb0 hb1

/-- **Pure-`Φ` forward step of `winWitt` across the raw inter-cone gap from the verified paper**. -/
theorem winwitt_step_inter_cone_gap_eq_phi_kit (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k)) (b + 1) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))) (b + 1) :=
  Rule30Paper.Paper.winwitt_step_inter_cone_gap_eq_phi t k b hb0 hb1

/-- **Pure-`Φ` sideways inversion of `winWitt` across the raw inter-cone gap from the verified paper**. -/
theorem winwitt_inward_step_inter_cone_gap_kit (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (b + 1) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k)) (b + 1))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) b ||
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) (b - 1)) :=
  Rule30Paper.Paper.winwitt_inward_step_inter_cone_gap t k b hb0 hb1

/-- **Non-overlapping Sector-1 copy law of `phiScale k (row t)` from the verified paper**. -/
theorem phiscale_row_testbit_sector_one_eq_row_kit (t k d : Nat)
    (htk : 2 * t < Rule30UOR.Core.twopow k) (hd : d < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        (d + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) d :=
  Rule30Paper.Paper.phiscale_row_testbit_sector_one_eq_row t k d htk hd

/-- **Non-overlapping Sector-2 copy law of `phiScale k (row t)` from the verified paper**. -/
theorem phiscale_row_testbit_sector_two_eq_row_kit (t k d : Nat)
    (htk : 2 * t < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        (d + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) d :=
  Rule30Paper.Paper.phiscale_row_testbit_sector_two_eq_row t k d htk

/-- **Non-overlapping Sector-1 bit readout of `winWitt t (2^k)` from the verified paper**. -/
theorem winwitt_testbit_sector_one_eq_row_xor_kit (t k d : Nat)
    (htk : 2 * t < Rule30UOR.Core.twopow k) (hd : d < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        (d + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row (t + Rule30UOR.Core.twopow k))
          (d + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) d) :=
  Rule30Paper.Paper.winwitt_testbit_sector_one_eq_row_xor t k d htk hd

/-- **Non-overlapping Sector-2 bit readout of `winWitt t (2^k)` from the verified paper**. -/
theorem winwitt_testbit_sector_two_eq_row_xor_kit (t k d : Nat)
    (htk : 2 * t < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        (d + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row (t + Rule30UOR.Core.twopow k))
          (d + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.row t) d) :=
  Rule30Paper.Paper.winwitt_testbit_sector_two_eq_row_xor t k d htk

/-- **Early-free right-to-left cross-sector window duality from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_rhcenter_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - p))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - p)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) p)
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k)
          (Rule30UOR.Core.twopow k - p)) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_rhcenter_cone t k p hp

/-- **Early-free left-to-left cross-sector window duality from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_lhcenter_cone_kit (t k p : Nat)
    (hp : t + p < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + p) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + p) + Rule30UOR.Core.twopow (k + 1))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) p)
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k)
          (p + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_lhcenter_cone t k p hp

/-- **Early-free `2^k`-spatial shift of late `LhBandAgree (t + 2^k)` via cross-sector `WinWittAgree` from the verified paper**. -/
theorem lhbandagree_late_shift_of_winwittagree_sectors_kit (t k Q p0 L : Nat)
    (hp : ((t + Q) + p0) + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q p0 L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + p0) + Rule30UOR.Core.twopow k) L)
    (hw2 : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + p0) + Rule30UOR.Core.twopow (k + 1)) L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.lhbandagree_late_shift_of_winwittagree_sectors t k Q p0 L hp hlate hw1 hw2

/-- **Early-free cross-center transfer from late `LhBandAgree (t + 2^k)` to late `RhBandAgree (t + 2^k)` via cross-sector `WinWittAgree` from the verified paper**. -/
theorem rhbandagree_late_of_lhbandagree_late_and_winwittagree_sectors_kit (t k Q L : Nat)
    (hp : (t + Q) + L < Rule30UOR.Core.twopow k)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q (Rule30UOR.Core.twopow k - L) L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow k) - L) L)
    (hw2 : Rule30UOR.Interfaces.WinWittAgree t k Q ((t + Rule30UOR.Core.twopow (k + 1)) - L) L) :
    Rule30UOR.Interfaces.RhBandAgree (t + Rule30UOR.Core.twopow k) Q 0 L :=
  Rule30Paper.Paper.rhbandagree_late_of_lhbandagree_late_and_winwittagree_sectors t k Q L hp hlate hw1 hw2

/-- **Exact Sector-1 boundary bit readout `(winWitt t (2^k)).testBit (2^k) = !rhCenter (t + 2^k) t` from the verified paper**. -/
theorem winwitt_testbit_twopow_eq_not_rhcenter_late_kit (t k : Nat)
    (htk : 2 * t < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.twopow k) =
      !Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) t :=
  Rule30Paper.Paper.winwitt_testbit_twopow_eq_not_rhcenter_late t k htk

/-- **Pure-`Φ` recurrence of late `rhCenter (t + 2^k) t` along the Sector-1 boundary from the verified paper**. -/
theorem rhcenter_late_self_from_zero_gap_step_kit (t k : Nat)
    (htk : 2 * t + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) t =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter ((t + 1) + Rule30UOR.Core.twopow k) (t + 1))
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (t + 1) ||
          Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (t + 2)) :=
  Rule30Paper.Paper.rhcenter_late_self_from_zero_gap_step t k htk

/-- **Scale-independent left-diagonal coordinate of `lhCenter (t + 2^k) (p + 2^k)` from the verified paper**. -/
theorem lhcenter_late_shift_eq_ldiag_kit (t k p : Nat) (hp : p ≤ t) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.ldiag (t - p) (t + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_shift_eq_ldiag t k p hp

/-- **Scale-independent left-diagonal coordinate of `lhCenter (t + 2^k) (2^k - r)` from the verified paper**. -/
theorem lhcenter_late_cross_eq_ldiag_kit (t k r : Nat)
    (hr : r ≤ Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Core.ldiag (t + r) (t + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_cross_eq_ldiag t k r hr

/-- **Direct settled readout of `zcenter t` at `lhCenter (t + 2^k) (2^k)` from the verified paper**. -/
theorem lhcenter_late_twopow_eq_zcenter_kit (t k : Nat)
    (hk : t ≤ k) (hset : Rule30UOR.Interfaces.SettledAt t k) :
    Rule30UOR.Interfaces.ZCenterEq t
      (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.lhcenter_late_twopow_eq_zcenter t k hk hset

/-- **Settled Sector-2 center-slot window readout of `zcenter t` from the verified paper**. -/
theorem winwitt_testbit_sector_two_center_slot_zcenter_kit (t k : Nat)
    (hk : t ≤ k) (hset : Rule30UOR.Interfaces.SettledAt t k) :
    Rule30UOR.Interfaces.ZCenterEq t
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          (t + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.center t)) :=
  Rule30Paper.Paper.winwitt_testbit_sector_two_center_slot_zcenter t k hk hset

/-- **Early-free cross-sector window readout of `zcenter t` from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_center_slot_zcenter_kit (t k : Nat)
    (hk : t ≤ k) (hset : Rule30UOR.Interfaces.SettledAt t k) :
    Rule30UOR.Interfaces.ZCenterEq t
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (t + Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            (t + Rule30UOR.Core.twopow (k + 1))))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_center_slot_zcenter t k hk hset

/-- **Exact late left-half vanishing along any zero diagonal from the verified paper**. -/
theorem lhcenter_late_shift_of_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (hk : t - p ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) = false :=
  Rule30Paper.Paper.lhcenter_late_shift_of_zero_diag t k p hp hk hz hset

/-- **Exact late cross-center vanishing along any zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_of_zero_diag_kit (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_of_zero_diag t k r hk hz hset

/-- **Direct readout of early `lhCenter t p` from Sector-2 `winWitt` along a zero diagonal from the verified paper**. -/
theorem winwitt_testbit_outer_left_strip_of_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (hk : t - p ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + p) + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.winwitt_testbit_outer_left_strip_of_zero_diag t k p hp hk hz hset

/-- **Direct readout of early `rhCenter t r` from Sector-2 `winWitt` along a zero diagonal from the verified paper**. -/
theorem winwitt_testbit_scale_cross_of_zero_diag_kit (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.rhCenter t r :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_of_zero_diag t k r hk hz hset

/-- **Exact vanishing of Sector-2 cross-center `winWitt` in the inter-cone zero gap along a zero diagonal from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_of_zero_diag_kit (t k r : Nat)
    (htr : t < r) (hk : t + r ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap_of_zero_diag t k r htr hk hz hset

/-- **Direct cross-sector window readout of late `lhCenter (t + 2^k) p` along a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_lhcenter_of_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (htp : t + p < Rule30UOR.Core.twopow k) (hk : t - p ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + p) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + p) + Rule30UOR.Core.twopow (k + 1))) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) p :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_lhcenter_of_zero_diag t k p hp htp hk hz hset

/-- **Direct cross-sector window readout of late `rhCenter (t + 2^k) r` along a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_rhcenter_of_zero_diag_kit (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - r))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r)) =
      Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) r :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_rhcenter_of_zero_diag t k r hk hz hset

/-- **Exact vanishing of `lhCenter (z + 2^k) (2^k)` at any zero diagonal `z` from the verified paper**. -/
theorem lhcenter_late_twopow_of_zero_diag_kit (z k : Nat)
    (hk : z ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledAt z k) :
    Rule30UOR.Interfaces.lhCenter (z + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) = false :=
  Rule30Paper.Paper.lhcenter_late_twopow_of_zero_diag z k hk hz hset

/-- **Direct Sector-2 window readout of `center z` at any zero diagonal `z` from the verified paper**. -/
theorem winwitt_testbit_sector_two_center_slot_of_zero_diag_kit (z k : Nat)
    (hk : z ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledAt z k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt z (Rule30UOR.Core.twopow k))
        (z + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.center z :=
  Rule30Paper.Paper.winwitt_testbit_sector_two_center_slot_of_zero_diag z k hk hz hset

/-- **Direct cross-sector window readout of late `center (z + 2^k)` at any zero diagonal `z` from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_center_slot_of_zero_diag_kit (z k : Nat)
    (hk : z ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledAt z k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt z (Rule30UOR.Core.twopow k))
        (z + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt z (Rule30UOR.Core.twopow k))
        (z + Rule30UOR.Core.twopow (k + 1))) =
      Rule30UOR.Core.center (z + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_center_slot_of_zero_diag z k hk hz hset

/-- **Exact late left-half pinning along the post-zero black diagonal from the verified paper**. -/
theorem lhcenter_late_shift_after_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) ((t + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) = true :=
  Rule30Paper.Paper.lhcenter_late_shift_after_zero_diag t k p hp hk hz hset

/-- **Exact late cross-center pinning along the post-zero black diagonal from the verified paper**. -/
theorem lhcenter_late_cross_after_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_after_zero_diag t k r hk hz hset

/-- **Negated Sector-2 outer-strip window mirror along the post-zero black diagonal from the verified paper**. -/
theorem winwitt_testbit_outer_left_strip_after_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) ((t + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
        (((t + 2) + p) + Rule30UOR.Core.twopow (k + 1)) =
      !Rule30UOR.Interfaces.lhCenter (t + 2) p :=
  Rule30Paper.Paper.winwitt_testbit_outer_left_strip_after_zero_diag t k p hp hk hz hset

/-- **Negated Sector-2 cross-center window mirror along the post-zero black diagonal from the verified paper**. -/
theorem winwitt_testbit_scale_cross_after_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) =
      !Rule30UOR.Interfaces.rhCenter t (r + 2) :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_after_zero_diag t k r hk hz hset

/-- **Exact constant-`true` pinning of Sector-2 cross-center `winWitt` in the inter-cone zero gap along the post-zero black diagonal from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_after_zero_diag_kit (t k r : Nat)
    (htr : t < r + 2) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap_after_zero_diag t k r htr hk hz hset

/-- **Negated cross-sector window readout of late `lhCenter ((t + 2) + 2^k) p` along the post-zero black diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_lhcenter_after_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (htp : (t + 2) + p < Rule30UOR.Core.twopow k) (hk : (t - p) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) ((t + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
        (((t + 2) + p) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
        (((t + 2) + p) + Rule30UOR.Core.twopow (k + 1))) =
      !Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) p :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_lhcenter_after_zero_diag t k p hp htp hk hz hset

/-- **Negated cross-sector window readout of late `rhCenter (t + 2^k) (r + 2)` along the post-zero black diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_rhcenter_after_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - (r + 2)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))) =
      !Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (r + 2) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_rhcenter_after_zero_diag t k r hk hz hset

/-- **Exact pinning of `lhCenter ((z + 2) + 2^k) (2^k) = true` two steps past any zero diagonal `z` from the verified paper**. -/
theorem lhcenter_late_twopow_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledAt (z + 2) k) :
    Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) = true :=
  Rule30Paper.Paper.lhcenter_late_twopow_after_zero_diag z k hk hz hset

/-- **Negated Sector-2 window readout of `!center (z + 2)` two steps past any zero diagonal `z` from the verified paper**. -/
theorem winwitt_testbit_sector_two_center_slot_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledAt (z + 2) k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
        ((z + 2) + Rule30UOR.Core.twopow (k + 1)) =
      !Rule30UOR.Core.center (z + 2) :=
  Rule30Paper.Paper.winwitt_testbit_sector_two_center_slot_after_zero_diag z k hk hz hset

/-- **Negated cross-sector window readout of late `!center ((z + 2) + 2^k)` two steps past any zero diagonal `z` from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_center_slot_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledAt (z + 2) k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
        ((z + 2) + Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
        ((z + 2) + Rule30UOR.Core.twopow (k + 1))) =
      !Rule30UOR.Core.center ((z + 2) + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_center_slot_after_zero_diag z k hk hz hset

/-- **Real-orbit cross-center reset law across the post-zero black diagonal from the verified paper**. -/
theorem lhcenter_late_cross_reset_after_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_reset_after_zero_diag t k r hk hz hset

/-- **Real-orbit outer-strip reset law across the post-zero black diagonal from the verified paper**. -/
theorem lhcenter_late_shift_reset_after_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) ((t + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 3) + Rule30UOR.Core.twopow k) ((p + 1) + Rule30UOR.Core.twopow k) =
      !Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) ((p + 2) + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_shift_reset_after_zero_diag t k p hp hk hz hset

/-- **Sector-2 1-step window complementation across the post-zero black diagonal from the verified paper**. -/
theorem winwitt_sector_two_step_complement_after_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) =
      !(Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t (r + 1))
          (Rule30UOR.Interfaces.rhCenter (t + 1) (r + 2))) :=
  Rule30Paper.Paper.winwitt_sector_two_step_complement_after_zero_diag t k r hk hz hset

/-- **Unconditional 1-step bit flip of Sector-2 `winWitt` in the inter-cone zero gap across a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_step_flip_zero_gap_after_zero_diag_kit (t k r : Nat)
    (htr : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_sector_two_step_flip_zero_gap_after_zero_diag t k r htr hk hz hset

/-- **Early-free cross-sector 1-step window complementation of late `rhCenter` across the post-zero black diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_step_complement_after_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - (r + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - (r + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (r + 1))
        (Rule30UOR.Interfaces.rhCenter ((t + 1) + Rule30UOR.Core.twopow k) (r + 2))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_step_complement_after_zero_diag t k r hk hz hset

/-- **1-step fixed-bit jump from zero diagonal `t + r` to post-zero black diagonal `(t + r) + 2` in `lhCenter` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_of_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_of_zero_diag t k r hk hz hset

/-- **Negated Sector-2 window readout at fixed bit `(t + 2^(k+1)) - r` one step after zero diagonal `t + r` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_step_one_of_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      !Rule30UOR.Interfaces.rhCenter (t + 1) (r + 1) :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_step_one_of_zero_diag t k r hk hz hset

/-- **Exact `false → true` jump at fixed Sector-2 bit `(t + 2^(k+1)) - r` in the inter-cone zero gap from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_step_one_of_zero_diag_kit (t k r : Nat)
    (htr : t < r) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap_step_one_of_zero_diag t k r htr hk hz hset

/-- **Sector-2 fixed-bit 1-step zero-to-black transition across zero diagonal `t + r` from the verified paper**. -/
theorem winwitt_sector_two_zero_to_black_step_of_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r)) =
      !(Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t r)
          (Rule30UOR.Interfaces.rhCenter (t + 1) (r + 1))) :=
  Rule30Paper.Paper.winwitt_sector_two_zero_to_black_step_of_zero_diag t k r hk hz hset0 hset2

/-- **Negated cross-sector window readout at fixed bits `(t + 2^k) - r` and `(t + 2^(k+1)) - r` one step after zero diagonal `t + r` from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_rhcenter_step_one_of_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow k) - r))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r)) =
      !Rule30UOR.Interfaces.rhCenter ((t + 1) + Rule30UOR.Core.twopow k) (r + 1) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_rhcenter_step_one_of_zero_diag t k r hk hz hset

/-- **Early-free cross-sector fixed-bit 1-step zero-to-black transition of late `rhCenter` from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - r))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - r))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) r)
        (Rule30UOR.Interfaces.rhCenter ((t + 1) + Rule30UOR.Core.twopow k) (r + 1))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag t k r hk hz hset0 hset2

/-- **Exact Sector-2 right-half readout of `phiScale k (row t)` from the verified paper**. -/
theorem phiscale_row_testbit_scale_cross_cone_kit (t k r : Nat)
    (htr : t + r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.rhCenter t r :=
  Rule30Paper.Paper.phiscale_row_testbit_scale_cross_cone t k r htr

/-- **Exact vanishing of `phiScale k (row t)` in the Sector-2 cross-center zero gap from the verified paper**. -/
theorem phiscale_row_testbit_scale_cross_zero_gap_eq_false_kit (t k r : Nat)
    (ht : t < r) (htr : t + r < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.phiscale_row_testbit_scale_cross_zero_gap_eq_false t k r ht htr

/-- **Exact vanishing of `crossCarry` in the Sector-2 cross-center zero gap from the verified paper**. -/
theorem crosscarry_row_scale_cross_zero_gap_eq_false_kit (t k r : Nat)
    (ht : t ≤ r) (htr : (t + r) + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool
      (Rule30UOR.Interfaces.crossCarry (Rule30UOR.Core.phiScale k (Rule30UOR.Core.row t))
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.crosscarry_row_scale_cross_zero_gap_eq_false t k r ht htr

/-- **Pure-`Φ` evolution of `winWitt` in the Sector-2 cross-center zero gap from the verified paper**. -/
theorem winwitt_step_scale_cross_zero_gap_eq_phi_kit (t k r : Nat)
    (ht : t ≤ r) (htr : (t + r) + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool
        (Rule30UOR.Core.phi (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) :=
  Rule30Paper.Paper.winwitt_step_scale_cross_zero_gap_eq_phi t k r ht htr

/-- **Sideways pure-`Φ` inversion of `winWitt` in the Sector-2 cross-center zero gap from the verified paper**. -/
theorem winwitt_inward_step_scale_cross_zero_gap_kit (t k r : Nat)
    (ht : t ≤ r) (htr : (t + r) + 2 < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) ||
          Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))) :=
  Rule30Paper.Paper.winwitt_inward_step_scale_cross_zero_gap t k r ht htr

/-- **Linearized real-orbit step one diagonal before a zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_linear_step_one_before_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 1))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r))
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2))) :=
  Rule30Paper.Paper.lhcenter_late_cross_linear_step_one_before_zero_diag t k r hk hz hset

/-- **Linearized real-orbit step two diagonals before a zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_linear_step_two_before_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r))
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1))) :=
  Rule30Paper.Paper.lhcenter_late_cross_linear_step_two_before_zero_diag t k r hk hz hset

/-- **Linearized `Φ` window step in Sector 2 one diagonal before a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_linear_step_one_before_zero_diag_kit (t k r : Nat)
    (ht : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 1))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))) :=
  Rule30Paper.Paper.winwitt_sector_two_linear_step_one_before_zero_diag t k r ht hk hz hset

/-- **Linearized `Φ` window step in Sector 2 two diagonals before a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_linear_step_two_before_zero_diag_kit (t k r : Nat)
    (ht : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_sector_two_linear_step_two_before_zero_diag t k r ht hk hz hset

/-- **Real-orbit cross-center twin identity before a zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_twin_before_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_twin_before_zero_diag t k r hk hz hset

/-- **Real-orbit shifted left-half twin identity before a zero diagonal from the verified paper**. -/
theorem lhcenter_late_shift_twin_before_zero_diag_kit (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t - p) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) ((t + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) ((p + 2) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) ((p + 1) + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_shift_twin_before_zero_diag t k p hp hk hz hset

/-- **Sector-2 adjacent-bit twin identity before a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_twin_before_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t r) (Rule30UOR.Interfaces.rhCenter t (r + 1)) :=
  Rule30Paper.Paper.winwitt_sector_two_twin_before_zero_diag t k r hk hz hset

/-- **Inter-cone zero-gap adjacent-bit equality in Sector 2 before a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_twin_zero_gap_before_zero_diag_kit (t k r : Nat)
    (ht : t < r) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_sector_two_twin_zero_gap_before_zero_diag t k r ht hk hz hset

/-- **Early-free cross-sector adjacent-bit twin readout before a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_twin_before_zero_diag_kit (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - r))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - r)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - (r + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) r)
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) (r + 1)) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_twin_before_zero_diag t k r hk hz hset

/-- **Antiperiodicity of shifted late `lhCenter` at a doubling zero diagonal from the verified paper**. -/
theorem lhcenter_late_shift_antiperiodic_of_doubles_kit (P t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hd : Rule30UOR.CompilePoints.DoublesAt P (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 1) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + P) + Rule30UOR.Core.twopow k) ((p + P) + Rule30UOR.Core.twopow k) =
      !Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_shift_antiperiodic_of_doubles P t k p hp hk hz hd hset

/-- **Antiperiodicity of cross-center late `lhCenter` at a doubling zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_antiperiodic_of_doubles_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + P) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + P) + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_antiperiodic_of_doubles P t k r hk hz hd hset

/-- **Outer left-strip `winWitt` antiperiodicity at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_outer_left_strip_antiperiodic_of_doubles_kit (P t k p : Nat)
    (hp : p ≤ t) (htp : t + 1 < p + Rule30UOR.Core.twopow k) (hk : (t - p) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hd : Rule30UOR.CompilePoints.DoublesAt P (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 1) ((t + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        (((t + 1) + p) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + P) (Rule30UOR.Core.twopow k))
        ((((t + 1) + P) + (p + P)) + Rule30UOR.Core.twopow (k + 1))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + 1) p)
        (Rule30UOR.Interfaces.lhCenter ((t + 1) + P) (p + P))) :=
  Rule30Paper.Paper.winwitt_outer_left_strip_antiperiodic_of_doubles P t k p hp htp hk hz hd hset

/-- **Sector-2 cross-center `winWitt` antiperiodicity at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_scale_cross_antiperiodic_of_doubles_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter t ((r + P) + 1))
        (Rule30UOR.Interfaces.rhCenter (t + P) (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_antiperiodic_of_doubles P t k r hk hz hd hset

/-- **Inter-cone zero-gap Sector-2 bit flip under period shift `P` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_antiperiodic_of_doubles_kit (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_antiperiodic_of_doubles P t k r ht hk hz hd hset

/-- **Early-free cross-sector antiperiodicity at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_antiperiodic_of_doubles_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - ((r + P) + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
          (((t + P) + Rule30UOR.Core.twopow k) - (r + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
          (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) ((r + P) + 1))
        (Rule30UOR.Interfaces.rhCenter ((t + P) + Rule30UOR.Core.twopow k) (r + 1))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_antiperiodic_of_doubles P t k r hk hz hd hset

/-- **Real-orbit `P`-periodicity on all diagonals `d ≤ z` below a doubling point from the verified paper**. -/
theorem ldiag_periodic_of_doubles_le_kit (P z d s k : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z) (hdz : d ≤ z) (hk : d ≤ k)
    (hset : Rule30UOR.Interfaces.SettledBy d (s + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.ldiag d ((s + P) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.ldiag d (s + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.ldiag_periodic_of_doubles_le P z d s k hd hdz hk hset

/-- **Cross-center late `lhCenter` `P`-periodicity on all diagonals `(t + P) + r ≤ z` below a doubling point from the verified paper**. -/
theorem lhcenter_late_cross_periodic_of_doubles_le_kit (P z t k r : Nat)
    (hdz : (t + P) + r ≤ z) (hk : z ≤ k)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + P) + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + P) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + P)) :=
  Rule30Paper.Paper.lhcenter_late_cross_periodic_of_doubles_le P z t k r hdz hk hd hset

/-- **Sector-2 cross-center `winWitt` `P`-periodicity on all diagonals `(t + P) + r ≤ z` below a doubling point from the verified paper**. -/
theorem winwitt_scale_cross_periodic_of_doubles_le_kit (P z t k r : Nat)
    (hdz : (t + P) + r ≤ z) (hk : z ≤ k)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + P) + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + P)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - r)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter t (r + P))
        (Rule30UOR.Interfaces.rhCenter (t + P) r) :=
  Rule30Paper.Paper.winwitt_scale_cross_periodic_of_doubles_le P z t k r hdz hk hd hset

/-- **Inter-cone zero-gap Sector-2 bit invariance under period shift `P` below a doubling point from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_periodic_of_doubles_le_kit (P z t k r : Nat)
    (ht : t + P < r) (hdz : (t + P) + r ≤ z) (hk : z ≤ k)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + P) + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + P)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_periodic_of_doubles_le P z t k r ht hdz hk hd hset

/-- **Real-orbit space-time equivalence of `(t + P, z + 1)` and `(t + 1, z + 3)` at a doubling zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_doubles_eq_reset_step_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + P) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + P) + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2

/-- **Real-orbit `P`-antiperiodicity on the post-black reset diagonal `z + 3` at a doubling zero diagonal from the verified paper**. -/
theorem lhcenter_late_cross_reset_antiperiodic_of_doubles_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + P) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + P) + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2

/-- **Sector-2 window space-time equivalence of `(t + P, r + 1)` and `(t + 1, (r + P) + 2)` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_scale_cross_doubles_eq_reset_step_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + P) (r + 1))
        (Rule30UOR.Interfaces.rhCenter (t + 1) ((r + P) + 2)) :=
  Rule30Paper.Paper.winwitt_scale_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2

/-- **Inter-cone zero-gap Sector-2 bit identity between `(t + P, r + 1)` and `(t + 1, (r + P) + 1)` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_doubles_eq_reset_step_kit (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_doubles_eq_reset_step P t k r ht hk hz hd hset1 hset2

/-- **Sector-2 cross-center `winWitt` antiperiodicity on the post-black reset diagonal `z + 3` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_scale_cross_reset_antiperiodic_of_doubles_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + 1) ((r + P) + 2))
        (Rule30UOR.Interfaces.rhCenter ((t + 1) + P) (r + 2))) :=
  Rule30Paper.Paper.winwitt_scale_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2

/-- **Inter-cone zero-gap Sector-2 bit flip on the post-black reset diagonal `z + 3` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles_kit (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + P) (Rule30UOR.Core.twopow k))
        (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles P t k r ht hk hz hd hset1 hset2

/-- **Early-free cross-sector space-time equivalence between `(t + P, r + 1)` and `(t + 1, (r + P) + 2)` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_doubles_eq_reset_step_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
          (((t + P) + Rule30UOR.Core.twopow k) - (r + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + P) (Rule30UOR.Core.twopow k))
          (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - ((r + P) + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1)))) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter ((t + P) + Rule30UOR.Core.twopow k) (r + 1))
        (Rule30UOR.Interfaces.rhCenter ((t + 1) + Rule30UOR.Core.twopow k) ((r + P) + 2)) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_doubles_eq_reset_step P t k r hk hz hd hset1 hset2

/-- **Early-free cross-sector antiperiodicity on the post-black reset diagonal `z + 3` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_reset_antiperiodic_of_doubles_kit (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + P) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt P ((t + P) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + P) + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow k) - ((r + P) + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + P) + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + P) (Rule30UOR.Core.twopow k))
          (((t + P) + Rule30UOR.Core.twopow k) - (r + 1)))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + P) (Rule30UOR.Core.twopow k))
          (((t + P) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter ((t + 1) + Rule30UOR.Core.twopow k) ((r + P) + 2))
        (Rule30UOR.Interfaces.rhCenter (((t + 1) + P) + Rule30UOR.Core.twopow k) (r + 2))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2

/-- **Real-orbit `2^k - 1` twin readout of `zcenter t` two steps before a zero diagonal from the verified paper**. -/
theorem lhcenter_late_twopow_sub_one_eq_zcenter_before_zero_diag_kit (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + 2))
    (hset0 : Rule30UOR.Interfaces.SettledBy t (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (t + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq t
      (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - 1)) :=
  Rule30Paper.Paper.lhcenter_late_twopow_sub_one_eq_zcenter_before_zero_diag t k hk hz hset0 hset2

/-- **Sector-2 `(t + 2^(k+1)) - 1` window readout of `zcenter t` two steps before a zero diagonal from the verified paper**. -/
theorem winwitt_testbit_sector_two_sub_one_zcenter_before_zero_diag_kit (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + 2))
    (hset0 : Rule30UOR.Interfaces.SettledBy t (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (t + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq t
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
          ((t + Rule30UOR.Core.twopow (k + 1)) - 1))
        (Rule30UOR.Interfaces.rhCenter t 1)) :=
  Rule30Paper.Paper.winwitt_testbit_sector_two_sub_one_zcenter_before_zero_diag t k hk hz hset0 hset2

/-- **Early-free cross-sector `(t + 2^k) - 1` window readout of `zcenter t` two steps before a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_sub_one_zcenter_before_zero_diag_kit (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + 2))
    (hset0 : Rule30UOR.Interfaces.SettledBy t (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (t + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq t
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter (t + Rule30UOR.Core.twopow k) 1)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow k) - 1))
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
            ((t + Rule30UOR.Core.twopow (k + 1)) - 1)))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_sub_one_zcenter_before_zero_diag t k hk hz hset0 hset2

/-- **Shifted late `lhCenter` antiperiodic readout of `!zcenter (z + 1)` at a doubling zero diagonal from the verified paper**. -/
theorem lhcenter_late_shift_twopow_antiperiodic_zcenter_of_doubles_kit (P z k : Nat)
    (hk : z + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq (z + 1)
      (!Rule30UOR.Interfaces.lhCenter (((z + 1) + P) + Rule30UOR.Core.twopow k) (P + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.lhcenter_late_shift_twopow_antiperiodic_zcenter_of_doubles P z k hk hz hd hset

/-- **Outer left-strip `winWitt` readout of `!zcenter (z + 1)` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_outer_left_strip_zcenter_antiperiodic_of_doubles_kit (P z k : Nat)
    (hk : z + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq (z + 1)
      (!(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool
          (Rule30UOR.Core.winWitt ((z + 1) + P) (Rule30UOR.Core.twopow k))
          ((((z + 1) + P) + P) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Interfaces.lhCenter ((z + 1) + P) P))) :=
  Rule30Paper.Paper.winwitt_outer_left_strip_zcenter_antiperiodic_of_doubles P z k hk hz hd hset

/-- **Early-free cross-sector readout of `!zcenter (z + 1)` at a doubling zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_zcenter_antiperiodic_of_doubles_kit (P z k : Nat)
    (hcone : ((z + 1) + P) + P < Rule30UOR.Core.twopow k) (hk : z + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq (z + 1)
      (!(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (((z + 1) + P) + Rule30UOR.Core.twopow k) P)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt ((z + 1) + P) (Rule30UOR.Core.twopow k))
            ((((z + 1) + P) + P) + Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.wittBitBool
            (Rule30UOR.Core.winWitt ((z + 1) + P) (Rule30UOR.Core.twopow k))
            ((((z + 1) + P) + P) + Rule30UOR.Core.twopow (k + 1)))))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_zcenter_antiperiodic_of_doubles P z k hcone hk hz hd hset

/-- **Shifted late `lhCenter` `P`-invariant readout of `zcenter d` on all diagonals `d ≤ z` below a doubling point from the verified paper**. -/
theorem lhcenter_late_shift_twopow_periodic_zcenter_of_doubles_le_kit (P z d k : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z) (hdz : d ≤ z) (hk : d ≤ k)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq d
      (Rule30UOR.Interfaces.lhCenter ((d + P) + Rule30UOR.Core.twopow k) (P + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.lhcenter_late_shift_twopow_periodic_zcenter_of_doubles_le P z d k hd hdz hk hset

/-- **1-step real-orbit reset from `2^k` at `z + 1` to `2^k - 1` at `z + 2` after a zero diagonal from the verified paper**. -/
theorem lhcenter_late_twopow_sub_one_reset_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - 1) =
      !Rule30UOR.Interfaces.lhCenter ((z + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_twopow_sub_one_reset_after_zero_diag z k hk hz hset

/-- **Sector-2 fixed-bit step complementation from `z + 1` to `z + 2` after a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_center_to_sub_one_step_complement_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 1) (Rule30UOR.Core.twopow k))
        ((z + 1) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
        (((z + 2) + Rule30UOR.Core.twopow (k + 1)) - 1)) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (z + 1))
        (Rule30UOR.Interfaces.rhCenter (z + 2) 1)) :=
  Rule30Paper.Paper.winwitt_sector_two_center_to_sub_one_step_complement_after_zero_diag z k hk hz hset

/-- **Early-free cross-sector fixed-bit step complementation from `z + 1` to `z + 2` after a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_center_to_sub_one_step_complement_after_zero_diag_kit
    (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 1) (Rule30UOR.Core.twopow k))
          ((z + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 1) (Rule30UOR.Core.twopow k))
          ((z + 1) + Rule30UOR.Core.twopow (k + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
          (((z + 2) + Rule30UOR.Core.twopow k) - 1))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
          (((z + 2) + Rule30UOR.Core.twopow (k + 1)) - 1))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.rhCenter ((z + 2) + Rule30UOR.Core.twopow k) 1)) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_center_to_sub_one_step_complement_after_zero_diag z k hk hz hset

/-- **Real-orbit `2^k - 1` readout of `!zcenter (z + 1)` at `z + 2` after a zero diagonal from the verified paper**. -/
theorem lhcenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq (z + 1)
      (!Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - 1)) :=
  Rule30Paper.Paper.lhcenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag z k hk hz hset1 hset2

/-- **Sector-2 `((z + 2) + 2^(k+1)) - 1` window readout of `!zcenter (z + 1)` at `z + 2` after a zero diagonal from the verified paper**. -/
theorem winwitt_testbit_sector_two_sub_one_not_zcenter_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq (z + 1)
      (!(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
          (((z + 2) + Rule30UOR.Core.twopow (k + 1)) - 1))
        (Rule30UOR.Interfaces.rhCenter (z + 2) 1))) :=
  Rule30Paper.Paper.winwitt_testbit_sector_two_sub_one_not_zcenter_after_zero_diag z k hk hz hset1 hset2

/-- **Early-free cross-sector `((z + 2) + 2^k) - 1` window readout of `!zcenter (z + 1)` at `z + 2` after a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_sub_one_not_zcenter_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq (z + 1)
      (!(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rhCenter ((z + 2) + Rule30UOR.Core.twopow k) 1)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
            (((z + 2) + Rule30UOR.Core.twopow k) - 1))
          (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
            (((z + 2) + Rule30UOR.Core.twopow (k + 1)) - 1))))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_sub_one_not_zcenter_after_zero_diag z k hk hz hset1 hset2

/-- **Space-time identity between `((z + 1) + P, P + 2^k)` and `(z + 2, 2^k - 1)` at a doubling zero diagonal from the verified paper**. -/
theorem lhcenter_late_shift_twopow_doubles_eq_after_zero_diag_sub_one_kit (P z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt P z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (((z + 1) + P) + Rule30UOR.Core.twopow k) (P + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - 1) :=
  Rule30Paper.Paper.lhcenter_late_shift_twopow_doubles_eq_after_zero_diag_sub_one P z k hk hz hd hset1 hset2

/-- **1-step real-orbit reset from `1 + 2^k` at `z + 2` to `2^k` at `z + 3` after a zero diagonal from the verified paper**. -/
theorem lhcenter_late_twopow_reset_three_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((z + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      !Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) (1 + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_twopow_reset_three_after_zero_diag z k hk hz hset

/-- **Sector-2 fixed-bit step complementation from `z + 2` to `z + 3` after a zero diagonal from the verified paper**. -/
theorem winwitt_sector_two_one_to_center_step_complement_after_zero_diag_kit (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
        (((z + 2) + 1) + Rule30UOR.Core.twopow (k + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 3) (Rule30UOR.Core.twopow k))
        ((z + 3) + Rule30UOR.Core.twopow (k + 1))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (z + 2) 1)
        (Rule30UOR.Core.center (z + 3))) :=
  Rule30Paper.Paper.winwitt_sector_two_one_to_center_step_complement_after_zero_diag z k hk hz hset

/-- **Early-free cross-sector fixed-bit step complementation from `z + 2` to `z + 3` after a zero diagonal from the verified paper**. -/
theorem winwitt_sector_one_xor_sector_two_one_to_center_step_complement_after_zero_diag_kit
    (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
          (((z + 2) + 1) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 2) (Rule30UOR.Core.twopow k))
          (((z + 2) + 1) + Rule30UOR.Core.twopow (k + 1))))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 3) (Rule30UOR.Core.twopow k))
          ((z + 3) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (z + 3) (Rule30UOR.Core.twopow k))
          ((z + 3) + Rule30UOR.Core.twopow (k + 1)))) =
      !(Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) 1)
        (Rule30UOR.Core.center ((z + 3) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.winwitt_sector_one_xor_sector_two_one_to_center_step_complement_after_zero_diag z k hk hz hset

/-- **Same-column late `lhCenter` invariance under Sector-2 zero-gap `WinWittAgree` from the verified paper**. -/
theorem lhcenter_late_cross_eq_of_winwittagree_zero_gap_kit (t k Q r a L : Nat)
    (hr : t + Q < r) (hcone : (t + Q) + r < Rule30UOR.Core.twopow k)
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) :=
  Rule30Paper.Paper.lhcenter_late_cross_eq_of_winwittagree_zero_gap t k Q r a L hr hcone ha hL hw

/-- **Refutation of `WinWittAgree t k 2 a L` in the Sector-2 zero gap across any settled zero diagonal from the verified paper**. -/
theorem not_winwittagree_two_scale_cross_zero_gap_of_zero_diag_kit (t k r a L : Nat)
    (hr : t + 2 < r) (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) ((t + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 2 a L :=
  Rule30Paper.Paper.not_winwittagree_two_scale_cross_zero_gap_of_zero_diag t k r a L hr hk hz hset0 hset2 ha hL

/-- **Refutation of `WinWittAgree t k Q a L` in the Sector-2 zero gap whenever `t + r` is a zero diagonal and `(t + Q) + r = z + 2` is a post-zero black diagonal from the verified paper**. -/
theorem not_winwittagree_scale_cross_zero_gap_of_zero_and_after_zero_diag_kit
    (t k Q r z a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hrel : (t + Q) + r = z + 2)
    (hset0 : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q a L :=
  Rule30Paper.Paper.not_winwittagree_scale_cross_zero_gap_of_zero_and_after_zero_diag
    t k Q r z a L hr hk hz0 hz hrel hset0 hset2 ha hL

/-- **Single-window spatial `Q`-flip in Sector 2 at a doubling zero diagonal under `WinWittAgree` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Single-row spatial `Q`-flip in `lhCenter (t + 2^k)` at a doubling zero diagonal under Sector-2 zero-gap `WinWittAgree` from the verified paper**. -/
theorem lhcenter_late_cross_shift_flip_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_shift_flip_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset ha hL hw

/-! ### Batch 23: Outer Left-Strip & Sector-2 Center-Slot `WinWittAgree` Invariance, `zcenter` Shift Laws & Refutations, and Post-Black Reset Spatial `Q`-Flips at Doubling Diagonals -/

/-- **Same-column late `lhCenter (· + 2^k) (p + 2^k)` invariance under outer left-strip `WinWittAgree` from the verified paper**. -/
theorem lhcenter_late_shift_eq_of_winwittagree_outer_left_strip_kit (t k Q p a L : Nat)
    (hcone : (t + Q) + p < Rule30UOR.Core.twopow k)
    (ha : a ≤ (t + p) + Rule30UOR.Core.twopow (k + 1))
    (hL : (t + p) + Rule30UOR.Core.twopow (k + 1) ≤ a + L)
    (hp : Rule30UOR.Interfaces.lhCenter (t + Q) p = Rule30UOR.Interfaces.lhCenter t p)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_late_shift_eq_of_winwittagree_outer_left_strip t k Q p a L hcone ha hL hp hw

/-- **Refutation of `WinWittAgree t k 2 a L` in the outer left strip across any settled zero diagonal `t - p` from the verified paper**. -/
theorem not_winwittagree_two_outer_left_strip_of_zero_diag_kit (t k p a L : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - p) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) ((t + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + p) + Rule30UOR.Core.twopow (k + 1))
    (hL : (t + p) + Rule30UOR.Core.twopow (k + 1) ≤ a + L)
    (hcol : Rule30UOR.Interfaces.lhCenter (t + 2) p = Rule30UOR.Interfaces.lhCenter t p) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 2 a L :=
  Rule30Paper.Paper.not_winwittagree_two_outer_left_strip_of_zero_diag t k p a L hp hk hz hset0 hset2 ha hL hcol

/-- **Exact `zcenter` shift XOR from Sector-2 center-slot `WinWittAgree` from the verified paper**. -/
theorem zcenter_shift_xor_eq_center_xor_of_winwittagree_sector_two_center_slot_kit
    (t k Q a L : Nat)
    (hk : t + Q ≤ k)
    (hset0 : Rule30UOR.Interfaces.SettledBy t (t + Rule30UOR.Core.twopow k))
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t + Q) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ t + Rule30UOR.Core.twopow (k + 1))
    (hL : t + Rule30UOR.Core.twopow (k + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.ZCenterXorEq (t + Q) t
      (Rule30UOR.Core.bxor (Rule30UOR.Core.center (t + Q)) (Rule30UOR.Core.center t)) :=
  Rule30Paper.Paper.zcenter_shift_xor_eq_center_xor_of_winwittagree_sector_two_center_slot
    t k Q a L hk hset0 hsetQ ha hL hw

/-- **Exact `zcenter` shift equality from Sector-2 center-slot `WinWittAgree` at equal centers from the verified paper**. -/
theorem zcenter_shift_eq_of_winwittagree_sector_two_center_slot_kit
    (t k Q a L : Nat)
    (hk : t + Q ≤ k)
    (hset0 : Rule30UOR.Interfaces.SettledBy t (t + Rule30UOR.Core.twopow k))
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t + Q) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ t + Rule30UOR.Core.twopow (k + 1))
    (hL : t + Rule30UOR.Core.twopow (k + 1) ≤ a + L)
    (hc : Rule30UOR.Core.center (t + Q) = Rule30UOR.Core.center t)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.ZCenterXorEq (t + Q) t false :=
  Rule30Paper.Paper.zcenter_shift_eq_of_winwittagree_sector_two_center_slot
    t k Q a L hk hset0 hsetQ ha hL hc hw

/-- **Periodic `zcenter (t + m * P) = zcenter t` from Sector-2 center-slot `WinWittAgree` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_zcenter_shift_eq_of_winwittagree_sector_two_center_slot_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k a L : Nat)
    (ht : T ≤ t) (hk : t + m * P ≤ k)
    (hset0 : Rule30UOR.Interfaces.SettledBy t (t + Rule30UOR.Core.twopow k))
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t + m * P) ((t + m * P) + Rule30UOR.Core.twopow k))
    (ha : a ≤ t + Rule30UOR.Core.twopow (k + 1))
    (hL : t + Rule30UOR.Core.twopow (k + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k (m * P) a L) :
    Rule30UOR.Interfaces.ZCenterXorEq (t + m * P) t false :=
  Rule30Paper.Paper.periodic_zcenter_shift_eq_of_winwittagree_sector_two_center_slot
    T P hP h m t k a L ht hk hset0 hsetQ ha hL hw

/-- **Refutation of `WinWittAgree z k 2 a L` at the Sector-2 center slot of any settled zero diagonal from the verified paper**. -/
theorem not_winwittagree_two_sector_two_center_slot_of_zero_diag_kit
    (z k a L : Nat)
    (hk : z + 2 ≤ k) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ z + Rule30UOR.Core.twopow (k + 1))
    (hL : z + Rule30UOR.Core.twopow (k + 1) ≤ a + L)
    (hc : Rule30UOR.Core.center (z + 2) = Rule30UOR.Core.center z) :
    ¬ Rule30UOR.Interfaces.WinWittAgree z k 2 a L :=
  Rule30Paper.Paper.not_winwittagree_two_sector_two_center_slot_of_zero_diag
    z k a L hk hz hset0 hset2 ha hL hc

/-- **Periodic refutation of `WinWittAgree z1 k (m * P) a L` at the Sector-2 center slot when `z1` is a zero diagonal and `z1 + m * P = z2 + 2` from the verified paper**. -/
theorem not_periodic_winwittagree_sector_two_center_slot_of_zero_and_after_zero_diag_kit
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k a L : Nat)
    (ht : T ≤ z1) (hk : z1 + m * P ≤ k)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag z1)
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag z2)
    (hrel : z1 + m * P = z2 + 2)
    (hset1 : Rule30UOR.Interfaces.SettledBy z1 (z1 + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z2 + 2) ((z2 + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ z1 + Rule30UOR.Core.twopow (k + 1))
    (hL : z1 + Rule30UOR.Core.twopow (k + 1) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree z1 k (m * P) a L :=
  Rule30Paper.Paper.not_periodic_winwittagree_sector_two_center_slot_of_zero_and_after_zero_diag
    T P hP h m z1 z2 k a L ht hk hz1 hz2 hrel hset1 hset2 ha hL

/-- **Late-window spatial `Q`-flip in `winWitt (t + Q) (2^k)` at a doubling zero diagonal under `WinWittAgree` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Late-row spatial `Q`-flip in `lhCenter ((t + Q) + 2^k)` at a doubling zero diagonal under Sector-2 zero-gap `WinWittAgree` from the verified paper**. -/
theorem lhcenter_late_cross_late_shift_flip_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      !Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_late_shift_flip_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Same-bit temporal `Q`-flip of `winWitt` at `(t + 2^(k+1)) - (r + 1)` at a doubling zero diagonal under `WinWittAgree` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Post-black reset single-window spatial `Q`-flip in `winWitt (t + 1) (2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset single-row spatial `Q`-flip in `lhCenter ((t + 1) + 2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` from the verified paper**. -/
theorem lhcenter_late_cross_reset_shift_flip_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_reset_shift_flip_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Space-time equality between `(t, (t + 2^(k+1)) - (r + 1))` and `(t + 1, (t + 2^(k+1)) - ((r + Q) + 1))` at a doubling zero diagonal under `WinWittAgree` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **1-step temporal Sector-2 bit flip at `(t + 2^(k+1)) - (r + 1)` (`Q` diagonals below `z + 1`) under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_flip_at_shift_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_flip_at_shift_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **1-step temporal `lhCenter` complementation `Q` diagonals below `z + 1` under Sector-2 zero-gap `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_step_flip_at_shift_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_step_flip_at_shift_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-! ### Batch 24: Cross-Center `lhCenter` Step Law, Forced Two-Cell OR Gates & Twin Pinning Under `WinWittAgree` at Doubling Zero Diagonals, and Upward `Q`-Transported Reset Flips -/

/-- **Exact 1-step local Rule 30 law for `lhCenter` in cross-center coordinates `2^k - (r + 2)` from the verified paper**. -/
theorem lhcenter_late_cross_step_kit (t k r : Nat)
    (hr : r + 3 ≤ Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)))
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) ||
          Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3))) :=
  Rule30Paper.Paper.lhcenter_late_cross_step t k r hr

/-- **Forced two-cell OR gate `(lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3))) = true` from 1-step cross-center complementation from the verified paper**. -/
theorem lhcenter_late_cross_or_eq_true_of_step_flip_kit (t k r : Nat)
    (hr : r + 3 ≤ Rule30UOR.Core.twopow k)
    (hflip : Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1))) :
    (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) ||
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3))) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_or_eq_true_of_step_flip t k r hr hflip

/-- **Forced two-cell `lhCenter` OR gate `Q` diagonals below `z + 2` at a doubling zero diagonal under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_or_eq_true_at_shift_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) ||
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3))) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_or_eq_true_at_shift_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Forced two-bit Sector-2 `winWitt t (2^k)` OR gate at `(t + 2^(k+1)) - (r + 2)` and `(t + 2^(k+1)) - (r + 3)` under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_or_eq_true_at_shift_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) ||
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_or_eq_true_at_shift_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Exact pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` when `(t + r) + 2` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_three_of_doubles_and_winwittagree_and_zero_diag_two_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_three_of_doubles_and_winwittagree_and_zero_diag_two
    Q t k r a L hr hk hz hd hz2 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Exact pinning `lhCenter (t + 2^k) (2^k - (r + 2)) = true` when `(t + r) + 3` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_two_of_doubles_and_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_two_of_doubles_and_winwittagree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Twin-propagated pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` when `(t + r) + 3` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_one_of_doubles_and_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_one_of_doubles_and_winwittagree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Doubling-diagonal pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` when `(t + r) + 3` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_false_of_doubles_and_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_false_of_doubles_and_winwittagree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Period-3 doubling pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` from `DoublesAt 3 ((t + 3) + r)` and `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_before_zero_diag_of_doubles_three_and_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k 3 a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k 3 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_before_zero_diag_of_doubles_three_and_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Refutation of the 2-step pair `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` when `lhCenter (t + 2^k) (2^k - (r + 2))` and `lhCenter (t + 2^k) (2^k - (r + 3))` are both `false` from the verified paper**. -/
theorem not_winwittagree_step_pair_at_shift_of_doubles_and_both_false_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hf2 : Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false)
    (hf3 : Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = false)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L :=
  Rule30Paper.Paper.not_winwittagree_step_pair_at_shift_of_doubles_and_both_false
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hf2 hf3 hw0

/-- **Post-black reset late-window spatial `Q`-flip in `winWitt ((t + 1) + Q) (2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
        (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset late-row spatial `Q`-flip in `lhCenter (((t + 1) + Q) + 2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` from the verified paper**. -/
theorem lhcenter_late_cross_reset_late_shift_flip_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter (((t + 1) + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_reset_late_shift_flip_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset same-bit temporal `Q`-flip of `winWitt` at `t + 1` and `(t + 2^(k+1)) - (r + 1)` without settling `z + 3` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_reset_same_bit_flip_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_reset_same_bit_flip_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Upward `Q`-transported 1-step Sector-2 bit flip at `t + Q` and `(t + 2^(k+1)) - (r + 1)` (`Q` diagonals beyond `z + 1`) under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_step_flip_at_shift_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_step_flip_at_shift_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Upward `Q`-transported 1-step `lhCenter` complementation `Q` diagonals beyond `z + 1` under Sector-2 zero-gap `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_late_step_flip_at_shift_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) =
      !Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_late_step_flip_at_shift_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Upward `Q`-transported two-cell `lhCenter` OR gate at `(t + Q) + 2^k` and `Q` diagonals beyond `z + 2` under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    (Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) ||
      Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 3))) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Upward `Q`-transported two-bit Sector-2 OR gate in `winWitt (t + Q) (2^k)` at `(t + 2^(k+1)) - (r + 2)` and `(t + 2^(k+1)) - (r + 3)` under `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_or_eq_true_at_shift_of_doubles_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k Q a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k Q a L) :
    (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) ||
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_or_eq_true_at_shift_of_doubles_and_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Period-2 doubling pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on the doubling diagonal `z + 1` from `DoublesAt 2 ((t + 2) + r)` and `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_three_of_doubles_two_and_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 2) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 2 ((t + 2) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 2) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k 2 a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k 2 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_three_of_doubles_two_and_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Period-2 doubling pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on diagonal `z - 1` from `DoublesAt 2 ((t + 2) + r)` and `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 2) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 2 ((t + 2) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 2) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k 2 a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k 2 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Twin-propagated Period-2 doubling pinning `lhCenter (t + 2^k) (2^k - r) = false` on diagonal `z - 2` from `DoublesAt 2 ((t + 2) + r)` and `WinWittAgree` at `t` and `t + 1` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_false_of_doubles_two_and_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 2) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 2 ((t + 2) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 2) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : Rule30UOR.Interfaces.WinWittAgree t k 2 a L)
    (hw1 : Rule30UOR.Interfaces.WinWittAgree (t + 1) k 2 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_false_of_doubles_two_and_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Single-window below-threshold spatial `Q`-periodicity in `winWitt t (2^k)` from `DoublesAt Q z` and `WinWittAgree` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winwittagree_kit
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + Q)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winwittagree
    Q z t k r a L hr hle hk hd hset ha hL hw

/-- **Single-row below-threshold spatial `Q`-periodicity in `lhCenter (t + 2^k)` from `DoublesAt Q z` and Sector-2 zero-gap `WinWittAgree` from the verified paper**. -/
theorem lhcenter_late_cross_shift_eq_of_doubles_le_and_winwittagree_zero_gap_kit
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + Q)) :=
  Rule30Paper.Paper.lhcenter_late_cross_shift_eq_of_doubles_le_and_winwittagree_zero_gap
    Q z t k r a L hr hle hk hd hset ha hL hw

/-- **Same-bit temporal `Q`-invariance of `winWitt` at `(t + 2^(k+1)) - r` below a doubling threshold under `WinWittAgree` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_same_bit_eq_of_doubles_le_and_winwittagree_kit
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_same_bit_eq_of_doubles_le_and_winwittagree
    Q z t k r a L hr hle hk hd hset ha hL hw

/-- **Exact zero-diagonal transport `lhCenter (t + 2^k) (2^k - r) = false` (`Q` diagonals below `z`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap from the verified paper**. -/
theorem lhcenter_late_cross_eq_false_at_shift_of_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_eq_false_at_shift_of_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact post-zero black-diagonal transport `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`Q` diagonals below `z + 2`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap from the verified paper**. -/
theorem lhcenter_late_cross_eq_true_at_shift_after_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_eq_true_at_shift_after_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **1-step `lhCenter` complementation `Q` diagonals below `z + 1` from a SINGLE `WinWittAgree t k Q a L` at time `t` and bit `(t + 2^(k+1)) - (r + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **1-step Sector-2 `winWitt` bit flip at `(t + 2^(k+1)) - (r + 1)` from a SINGLE `WinWittAgree t k Q a L` at time `t` and bit `(t + 2^(k+1)) - (r + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winwittagree_kit
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winwittagree
    Q t k r a L ht hr hk hz hset2 ha hL hw

/-- **Exact pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true` (`Q` diagonals below `z + 2` at `t + 1`) from a SINGLE `WinWittAgree t k Q a L` across `(t + 2^(k+1)) - (r + 2)` and `(t + 2^(k+1)) - r` without `DoublesAt` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Post-black reset spatial `Q`-flip in `winWitt (t + 1) (2^k)` at a doubling zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_single_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset spatial `Q`-flip in `lhCenter ((t + 1) + 2^k)` at a doubling zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_reset_shift_flip_of_doubles_and_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_reset_shift_flip_of_doubles_and_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Exact Sector-2 bit transport `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false` (`Q` diagonals below `z`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - r)
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winwittagree
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact Sector-2 post-zero black-diagonal transport `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` (`Q` diagonals below `z + 2`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winwittagree_kit
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winwittagree
    Q t k r a L ht hr hk hz hset2 ha hL hw

/-- **Exact Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = true` at `t + 1` from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **1-step Sector-2 zero-to-one bit flip at `(t + 2^(k+1)) - r` (`Q` diagonals below `z`) from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_flip_at_shift_of_zero_diag_and_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_flip_at_shift_of_zero_diag_and_single_winwittagree
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Refutation of `WinWittAgree t k Q a L` at `(t + 2^(k+1)) - (r + 2)` when both `(t + Q) + r` and `(t + r) + 2` are zero diagonals from the verified paper**. -/
theorem not_winwittagree_at_shift_after_zero_diag_of_zero_diag_two_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset_z2 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q a L :=
  Rule30Paper.Paper.not_winwittagree_at_shift_after_zero_diag_of_zero_diag_two
    Q t k r a L hr hk hz hz2 hset_z2 hset2 ha hL

/-- **Twin-propagated exact pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` (`Q` diagonals below `z + 1`) from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_one_of_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset_z3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_one_of_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact 1-step pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`Q` diagonals below `z + 3` at `t + 1`) from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_two_false_of_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset_z3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_two_false_of_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset_z3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **Exact post-black reset pinning `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = true` on diagonal `z + 3` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset_z3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` two diagonals before ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` 1-step pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` on ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 4)) = false` on the doubling diagonal `z + 1` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` post-black reset pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 5)) = true` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_reset_diag_true_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 5)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_reset_diag_true_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Refutation of `WinWittAgree t k 2 a L` at `(t + 2^(k+1)) - (r + 2)` across ANY zero diagonal `z = (t + 2) + r` without `DoublesAt` from the verified paper**. -/
theorem not_winwittagree_two_at_shift_after_zero_diag_kit
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 2) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 2) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 2) + r) + 2) ((t + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 2 a L :=
  Rule30Paper.Paper.not_winwittagree_two_at_shift_after_zero_diag
    t k r a L hr hk hz hset0 hset2 ha hL

/-- **Refutation of `WinWittAgree t k Q a L` across a `Q`-span at a doubling zero diagonal when `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` from the verified paper**. -/
theorem not_winwittagree_of_doubles_and_same_bit_eq_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (heq : Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q a L :=
  Rule30Paper.Paper.not_winwittagree_of_doubles_and_same_bit_eq
    Q t k r a L hr hk hz hd hset1 ha hL heq

/-- **Twin-propagated Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` (`Q` diagonals below `z + 1`) from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_one_of_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hsetz3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_one_of_single_winwittagree_and_zero_diag_three
    Q t k r a L ht hr hk hz hz3 hsetz3 hset2 ha hL hw

/-- **Exact 1-step Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_r_plus_one_false_of_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hsetz3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_r_plus_one_false_of_single_winwittagree_and_zero_diag_three
    Q t k r a L ht hr hk hz hz3 hsetz3 hset2 ha hL hw

/-- **Exact Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hsetz3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hsetz3 hset1 hset2 ha hL hw

/-- **Late-row pinning `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = true` on `z + 1` from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_late_pin_doubling_diag_true_of_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hsetz3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_late_pin_doubling_diag_true_of_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hsetz3 hset2 ha hL hw

/-- **Exact post-black reset Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = true` on diagonal `z + 3` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hsetz3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hsetz3 hset1 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` two diagonals before ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_before_zero_diag_of_zero_diag_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_before_zero_diag_of_zero_diag_three_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` 1-step Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` across ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_before_zero_diag_false_of_zero_diag_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_before_zero_diag_false_of_zero_diag_three_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = false` on the doubling diagonal `z + 1` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 4)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` post-black reset Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = true` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 4)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 2)) = true` on the doubling diagonal `z + 1` from `WinWittAgree t k 1 a L` at the SINGLE bit `(t + 2^(k+1)) - (r + 1)` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 1) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 ((t + 1) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 1) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 1 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on `z + 1` from `WinWittAgree t k 1 a L` at `(t + 2^(k+1)) - (r + 1)` without `WinWittAgree (t + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_one_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 1) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 ((t + 1) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 1) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 1 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_one_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` post-black reset pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 1) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 ((t + 1) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 1 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winwittagree
    t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` post-black reset Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_one_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 1) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 ((t + 1) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 1 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_one_and_single_winwittagree
    t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 1 a L` across the 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at ANY period-1 doubling zero diagonal `z = (t + 1) + r` without `WinWittAgree (t + 1)` or `settle (z + 3)` from the verified paper**. -/
theorem not_winwittagree_one_of_doubles_kit
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 1) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 ((t + 1) + r))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 1) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 1 a L :=
  Rule30Paper.Paper.not_winwittagree_one_of_doubles
    t k r a L hr hk hz hd hset1 hset2 ha hL

/-- **Single-time refutation `¬ WinWittAgree t k Q a L` at a doubling zero diagonal `z = (t + Q) + r` when both `(t + r) + 3` and `((t + Q) + r) + 3` are zero diagonals from the verified paper**. -/
theorem not_winwittagree_of_doubles_and_zero_diag_three_and_after_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hza3 : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 3))
    (hsetz3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hseta3 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q a L :=
  Rule30Paper.Paper.not_winwittagree_of_doubles_and_zero_diag_three_and_after_three
    Q t k r a L hr hk hz hd hz3 hza3 hsetz3 hset1 hset2 hseta3 ha hL

/-- **`Q`-transported Twin Identity `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_twin_at_shift_of_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_twin_at_shift_of_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **`Q`-transported Sector-2 window Twin Identity `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_twin_at_shift_of_zero_diag_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_twin_at_shift_of_zero_diag_and_winwittagree
    Q t k r a L hr hk hz hset ha hL hw

/-- **`Q`-transported Linearization 1 (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 2))`) from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 2) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 3))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)))
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2))) :=
  Rule30Paper.Paper.lhcenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **`Q`-transported Linearization 2 (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 3))`) from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)))
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3))) :=
  Rule30Paper.Paper.lhcenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact 1-step `false` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`Q` diagonals below `z = ((t + Q) + r) + 3`) from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 3))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact 1-step Sector-2 bit `false` pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`Q` diagonals below `z = ((t + Q) + r) + 3`) from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_eq_false_at_shift_of_zero_diag_and_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 3))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_eq_false_at_shift_of_zero_diag_and_single_winwittagree
    Q t k r a L hr hk hz hset ha hL hw

/-- **Unconditional 1-step forward propagation of `WinWittAgree t k Q a L` from a 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at time `t` to row `(t + 1) + 2^k` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_eq_of_winwittagree_three_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hrk : ((t + Q) + r) + 3 < Rule30UOR.Core.twopow k)
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_eq_of_winwittagree_three_zero_gap
    Q t k r a L hr hrk ha hL hw

/-- **Unconditional 1-step forward propagation of `WinWittAgree t k Q a L` from a 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at time `t` to `winWitt (t + 1) (2^k)` at bit `(t + 2^(k+1)) - (r + 1)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_eq_of_winwittagree_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hrk : ((t + Q) + r) + 3 < Rule30UOR.Core.twopow k)
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
      (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_eq_of_winwittagree_three
    Q t k r a L hr hrk ha hL hw

/-- **Single-time `WinWittAgree` 1-step spatial `Q`-flip on the doubling diagonal `z + 1` in row `(t + 1) + 2^k` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 2))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (((t + Q) + r) + 2))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) =
      !Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 hset3 ha hL hw

/-- **Single-time `WinWittAgree` 1-step Sector-2 spatial `Q`-flip on `z + 1` in `winWitt (t + 1) (2^k)` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 2))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (((t + Q) + r) + 2))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) =
      !Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winwittagree
    Q t k r a L hr hk hz hd hset1 hset2 hset3 ha hL hw

/-- **Upward `Q`-transport of a zero diagonal `z = (t + Q) + r`: `lhCenter ((t + Q) + 2^k) (2^k - (r + Q)) = false` on diagonal `z + Q` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + Q)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Upward `Q`-transport of the post-zero black diagonal `z + 2`: `lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 2)) = true` on diagonal `z + Q + 2` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winwittagree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Upward `Q`-transported 1-step complementation `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 2)) = !lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 1))` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) =
      !Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Upward `Q`-transported 1-step Sector-2 window bit flip `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_step_flip_at_shift_after_zero_diag_of_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_step_flip_at_shift_after_zero_diag_of_single_winwittagree
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Single-time refutation `¬ WinWittAgree t k Q a L` across `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` whenever `(t + r) + 1` and `((t + Q) + r) + 3` are settled zero diagonals from the verified paper**. -/
theorem not_winwittagree_of_zero_diag_one_and_shift_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 1))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag (((t + Q) + r) + 3))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + r) + 1) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 3) ((t + Q) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k Q a L :=
  Rule30Paper.Paper.not_winwittagree_of_zero_diag_one_and_shift_three
    Q t k r a L hr hk hz1 hz3 hset1 hset3 ha hL

/-- **Minimum depth of a zero diagonal (`2 ≤ z`) from the verified paper**. -/
theorem zero_diag_ge_two_kit
    (z : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    2 ≤ z :=
  Rule30Paper.Paper.zero_diag_ge_two z hz

/-- **No two zero diagonals are separated by 2 (`IsZeroDiag z → ¬ IsZeroDiag (z + 2)`) from the verified paper**. -/
theorem not_iszerodiag_add_two_kit
    (z : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 2) :=
  Rule30Paper.Paper.not_iszerodiag_add_two z hz

/-- **Diagonal `z + 1` after a zero diagonal `z` is never all-black (`IsZeroDiag z → ¬ IsBlackDiag (z + 1)`) from the verified paper**. -/
theorem not_isblackdiag_add_one_of_zero_diag_kit
    (z : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 1) :=
  Rule30Paper.Paper.not_isblackdiag_add_one_of_zero_diag z hz

/-- **No two zero diagonals are separated by 3 (`IsZeroDiag z → ¬ IsZeroDiag (z + 3)`) from the verified paper**. -/
theorem not_iszerodiag_add_three_kit
    (z : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 3) :=
  Rule30Paper.Paper.not_iszerodiag_add_three z hz

/-- **Diagonal `z + 3` after a zero diagonal `z` is never all-black (`IsZeroDiag z → ¬ IsBlackDiag (z + 3)`) from the verified paper**. -/
theorem not_isblackdiag_add_three_of_zero_diag_kit
    (z : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 3) :=
  Rule30Paper.Paper.not_isblackdiag_add_three_of_zero_diag z hz

/-- **No two zero diagonals are separated by 4 (`IsZeroDiag z → ¬ IsZeroDiag (z + 4)`) from the verified paper**. -/
theorem not_iszerodiag_add_four_kit
    (z : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 4) :=
  Rule30Paper.Paper.not_iszerodiag_add_four z hz

/-- **Sharp Zero-Diagonal Minimum Gap Theorem (`z₁ + 5 ≤ z₂` for all zero diagonals `z₁ < z₂`) from the verified paper**. -/
theorem zero_diag_gap_ge_five_kit
    (z1 z2 : Nat)
    (h1 : Rule30UOR.ZeroDiagonals.IsZeroDiag z1)
    (h2 : Rule30UOR.ZeroDiagonals.IsZeroDiag z2)
    (hlt : z1 < z2) :
    z1 + 5 ≤ z2 :=
  Rule30Paper.Paper.zero_diag_gap_ge_five z1 z2 h1 h2 hlt

/-- **Upward `Q`-transported Sector-2 bit evaluation `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = false` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_eq_false_at_shift_of_zero_diag_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_eq_false_at_shift_of_zero_diag_and_winwittagree
    Q t k r a L hr hk hz hset ha hL hw

/-- **Upward `Q`-transported Sector-2 bit evaluation `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_eq_true_at_shift_after_zero_diag_and_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_eq_true_at_shift_after_zero_diag_and_winwittagree
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Upward `Q`-transported 1-step `true` pinning `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 1)) = true` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree_zero_gap_kit
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (((t + 1) + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Upward `Q`-transported 1-step Sector-2 bit `true` pinning `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = true` from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree_kit
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt ((t + 1) + Q) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winwittagree
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 doubling 1-step pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = true` on diagonal `z + 1` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 2-step pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false` on diagonal `z + 1` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 3-step pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = true` on diagonal `z + 3` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 3 a L` across the 4-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - r]` at ANY period-3 doubling zero diagonal `z = (t + 3) + r` from the verified paper**. -/
theorem not_winwittagree_three_of_doubles_kit
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 3 a L :=
  Rule30Paper.Paper.not_winwittagree_three_of_doubles
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL

/-- **Period-3 doubling 1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on diagonal `z + 1` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_r_plus_two_true_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_r_plus_two_true_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 2-step Sector-2 window bit pinning `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - r) = false` on diagonal `z + 1` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_two_pin_r_false_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_two_pin_r_false_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 3-step Sector-2 window bit pinning `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on diagonal `z + 3` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 3) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Exact 3-step same-bit negation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` at fixed bit index `(t + 2^(k+1)) - r` from a single `WinWittAgree t k 3 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_same_bit_r_flip_three_of_doubles_three_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 3) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 ((t + 3) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 3) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 3) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 3 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 3) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_same_bit_r_flip_three_of_doubles_three_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **1-step `true` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_two_true_of_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_two_true_of_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Exact `false` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = false` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_one_false_of_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_one_false_of_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Doubling-diagonal `true` pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = true` on `z + 1` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **Period-4 single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` 1-step `true` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_two_true_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_two_true_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` `false` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on diagonal `z - 3` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_one_false_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_one_false_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 doubling single-time `WinWittAgree` `true` pinning `lhCenter (t + 2^k) (2^k - ((r + 4) + 1)) = true` on diagonal `z + 1` at ANY period-4 doubling zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + 4) + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 1-step `false` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 4)) = false` on diagonal `z + 1` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 3)) = true` on diagonal `z + 1` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 4)) = false` on diagonal `z + 3` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 2)) = false` on diagonal `z + 1` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem lhcenter_late_cross_step_three_pin_r_plus_two_false_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 3))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_three_pin_r_plus_two_false_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **1-step post-zero OR-absorption law on diagonal `z + 4` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false`) when `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on `z + 3` from the verified paper**. -/
theorem lhcenter_late_cross_step_absorb_false_after_zero_diag_kit
    (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k))
    (h3 : Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_absorb_false_after_zero_diag
    t k r hk hz hset2 h3

/-- **2-step post-zero reset-and-absorption law from `z + 1` to `z + 4` (`lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false`) when `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on `z + 1` from the verified paper**. -/
theorem lhcenter_late_cross_two_step_absorb_false_after_zero_diag_kit
    (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k))
    (h1 : Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = false) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_two_step_absorb_false_after_zero_diag
    t k r hk hz hset2 h1

/-- **Period-4 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 5)) = true` on diagonal `z + 3` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 5)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 5)) = false` on diagonal `z + 4` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 5)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 4-step `true` pinning `lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true` on diagonal `z + 4` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 4) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 4 a L` across the 5-bit interval `[(t + 2^(k+1)) - (r + 4), (t + 2^(k+1)) - r]` at ANY period-4 doubling zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem not_winwittagree_four_of_doubles_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 4))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 4 a L :=
  Rule30Paper.Paper.not_winwittagree_four_of_doubles
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL

/-- **1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Doubling-diagonal Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = true` on `z + 1` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **Period-4 single-time `WinWittAgree` Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_three_true_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 3)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_three_true_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` 1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` on diagonal `z - 3` across ANY zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_one_false_of_zero_diag_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_one_false_of_zero_diag_four_and_single_winwittagree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 doubling single-time `WinWittAgree` Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + 4) + 1)) = true` on diagonal `z + 1` at ANY period-4 doubling zero diagonal `z = (t + 4) + r` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) ((t + 1) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + 4) + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 4-step Sector-2 window bit pinning `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on diagonal `z + 4` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 4) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Exact 4-step same-bit negation `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` at fixed bit index `(t + 2^(k+1)) - r` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_same_bit_r_flip_four_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 4) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - r)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_same_bit_r_flip_four_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Four diagonals past any zero diagonal is never all-black (`¬ IsBlackDiag (z + 4)`) from the verified paper**. -/
theorem not_isblackdiag_add_four_of_zero_diag_kit (z : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 4) :=
  Rule30Paper.Paper.not_isblackdiag_add_four_of_zero_diag z hz

/-- **Five diagonals past any zero diagonal is never all-black (`¬ IsBlackDiag (z + 5)`) from the verified paper**. -/
theorem not_isblackdiag_add_five_of_zero_diag_kit (z : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 5) :=
  Rule30Paper.Paper.not_isblackdiag_add_five_of_zero_diag z hz

/-- **Six diagonals past any zero diagonal is never all-black (`¬ IsBlackDiag (z + 6)`) from the verified paper**. -/
theorem not_isblackdiag_add_six_of_zero_diag_kit (z : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 6) :=
  Rule30Paper.Paper.not_isblackdiag_add_six_of_zero_diag z hz

/-- **Exact characterization of gap-5 zero-diagonal pairs (`IsZeroDiag z ∧ IsZeroDiag (z + 5) → IsBlackDiag (z - 1)`) from the verified paper**. -/
theorem isblackdiag_sub_one_of_zero_diag_and_add_five_kit (z : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 5)) :
    Rule30UOR.CompilePoints.IsBlackDiag (z - 1) :=
  Rule30Paper.Paper.isblackdiag_sub_one_of_zero_diag_and_add_five z hz hz5

/-- **Uniqueness of the gap-5 zero-diagonal pair `(2, 7)` (`IsZeroDiag z ∧ IsZeroDiag (z + 5) → z ≤ 2`) from the verified paper**. -/
theorem zero_diag_le_two_of_add_five_kit (z : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 5)) :
    z ≤ 2 :=
  Rule30Paper.Paper.zero_diag_le_two_of_add_five z hz hz5

/-- **Five diagonals past any zero diagonal `z > 2` is never a zero diagonal (`2 < z → IsZeroDiag z → ¬ IsZeroDiag (z + 5)`) from the verified paper**. -/
theorem not_iszerodiag_add_five_of_gt_two_kit (z : Nat)
    (hgt : 2 < z) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.ZeroDiagonals.IsZeroDiag (z + 5) :=
  Rule30Paper.Paper.not_iszerodiag_add_five_of_gt_two z hgt hz

/-- **Sharp zero-diagonal gap theorem above `z = 2` (`2 < z₁ → z₁ < z₂ → z₁ + 6 ≤ z₂`) from the verified paper**. -/
theorem zero_diag_gap_ge_six_of_gt_two_kit (z1 z2 : Nat)
    (hgt : 2 < z1)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag z1)
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag z2)
    (hlt : z1 < z2) :
    z1 + 6 ≤ z2 :=
  Rule30Paper.Paper.zero_diag_gap_ge_six_of_gt_two z1 z2 hgt hz1 hz2 hlt

/-- **Seven diagonals past any zero diagonal `z > 2` is never all-black (`2 < z → IsZeroDiag z → ¬ IsBlackDiag (z + 7)`) from the verified paper**. -/
theorem not_isblackdiag_add_seven_of_gt_two_and_zero_diag_kit (z : Nat)
    (hgt : 2 < z) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 7) :=
  Rule30Paper.Paper.not_isblackdiag_add_seven_of_gt_two_and_zero_diag z hgt hz

/-- **Period-4 doubling 1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = false` on diagonal `z + 1` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_r_plus_three_false_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 3)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_r_plus_three_false_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 2-step Sector-2 window bit pinning `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` on diagonal `z + 1` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_two_pin_r_plus_one_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 4) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_two_pin_r_plus_one_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step Sector-2 window bit pinning `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` on diagonal `z + 3` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_three_pin_r_plus_one_false_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 2) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 3) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_three_pin_r_plus_one_false_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 2-step Sector-2 window bit pinning `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` on diagonal `z + 3` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 3)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step Sector-2 window bit pinning `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false` on diagonal `z + 4` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 3) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Exact 3-step same-bit negation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2))` at fixed bit index `(t + 2^(k+1)) - (r + 2)` from a single `WinWittAgree t k 4 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_same_bit_r_plus_two_flip_three_of_doubles_four_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 4) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 4 ((t + 4) + r))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 4) + r) + 2) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 4 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 3) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_same_bit_r_plus_two_flip_three_of_doubles_four_and_single_winwittagree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Post-black reset diagonal `false` pinning `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = false` on `z + 3` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 2)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **Sector-2 window bit evaluation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = false` on `z + 3` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **1-step same-bit negation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winwittagree_and_zero_diag_four_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz4 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 4))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (hset4 : Rule30UOR.Interfaces.SettledBy ((t + r) + 4) ((t + 1) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winwittagree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **1-step same-bit negation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 3` is a settled zero diagonal from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winwittagree_and_zero_diag_three_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hz3 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 3))
    (hset_z3 : Rule30UOR.Interfaces.SettledBy ((t + r) + 3) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winwittagree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **1-step complementation `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = !lhCenter (t + 2^k) (2^k - (r + 3))` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winwittagree_and_zero_diag_five_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 5))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset5 : Rule30UOR.Interfaces.SettledBy ((t + r) + 5) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) =
      !Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winwittagree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset2 hset5 ha hL hw

/-- **Spatial stride-2 equality `lhCenter (t + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 3))` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winwittagree_and_zero_diag_five_kit
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 5))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset5 : Rule30UOR.Interfaces.SettledBy ((t + r) + 5) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) :=
  Rule30Paper.Paper.lhcenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winwittagree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset2 hset5 ha hL hw

/-- **2-step same-cell return `lhCenter ((t + 2) + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 1))` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_two_eq_r_plus_one_of_single_winwittagree_and_zero_diag_five_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 5))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset5 : Rule30UOR.Interfaces.SettledBy ((t + r) + 5) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_step_two_eq_r_plus_one_of_single_winwittagree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

/-- **Self-canceling parity pinning `lhCenter (t + 2^k) (2^k - (r - 1)) = true` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_sub_one_true_of_single_winwittagree_and_zero_diag_five_kit
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 5))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset5 : Rule30UOR.Interfaces.SettledBy ((t + r) + 5) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r - 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_sub_one_true_of_single_winwittagree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

/-- **Period-5 doubling `true` pinning `lhCenter (t + 2^k) (2^k - (r + 4)) = true` on `z - 1` across any period-5 doubling zero diagonal `z = (t + 5) + r` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling `true` pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on `z - 2` across any period-5 doubling zero diagonal `z = (t + 5) + r` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling `true` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` on `z - 4` across any period-5 doubling zero diagonal `z = (t + 5) + r` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling diagonal `false` pinning `lhCenter (t + 2^k) (2^k - (r + 6)) = false` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 6)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 1-step `true` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 5)) = true` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 5)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 4)) = true` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = false` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 3)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 5 a L` across any period-5 doubling zero diagonal `z = (t + 5) + r` without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)` from the verified paper**. -/
theorem not_winwittagree_five_of_doubles_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 4))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L) :
    ¬ Rule30UOR.Interfaces.WinWittAgree t k 5 a L :=
  Rule30Paper.Paper.not_winwittagree_five_of_doubles
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL

/-- **Period-5 doubling 4-step `true` pinning `lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true` on `z + 3` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 4) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 5-step `false` pinning `lhCenter ((t + 5) + 2^k) (2^k - (r + 4)) = false` on `z + 4` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 5) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 4)) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = true` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a single `WinWittAgree t k Q a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_sub_one_true_of_single_winwittagree_and_zero_diag_five_kit
    (Q t k r a L : Nat)
    (hr : (t + Q) + 1 < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hz5 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 5))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 2) ((t + Q) + Rule30UOR.Core.twopow k))
    (hset5 : Rule30UOR.Interfaces.SettledBy ((t + r) + 5) (t + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - r ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k Q a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r - 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_sub_one_true_of_single_winwittagree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

/-- **Period-5 doubling Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = true` on `z - 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 4)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` on `z - 2` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_three_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 3)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_three_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` on `z - 4` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_r_plus_one_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_r_plus_one_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling diagonal Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 6)) = false` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 6)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 1-step Sector-2 window bit evaluation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = true` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_one_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 4)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_one_pin_r_plus_four_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 2-step Sector-2 window bit evaluation `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 3-step Sector-2 window bit evaluation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = false` on `z + 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_three_pin_r_false_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 3) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_three_pin_r_false_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 4-step Sector-2 window bit evaluation `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on `z + 3` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 4) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 5-step Sector-2 window bit evaluation `(winWitt (t + 5) (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = false` on `z + 4` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_five_pin_r_sub_one_false_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 5) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r - 1)) = false :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_five_pin_r_sub_one_false_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = true` on `z - 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem lhcenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.lhCenter ((t + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling 2-step Sector-2 window bit evaluation `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on `z - 1` from a single `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_step_two_pin_r_true_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 5) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 2) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = true :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_step_two_pin_r_true_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Exact 5-step same-bit negation `(winWitt (t + 5) (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r - 1))` from a single 4-bit `WinWittAgree t k 5 a L` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_same_bit_r_sub_one_flip_five_of_doubles_five_and_single_winwittagree_kit
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + 5) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt 5 ((t + 5) + r))
    (hset_m1 : Rule30UOR.Interfaces.SettledBy ((t + 4) + r) (t + Rule30UOR.Core.twopow k))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + 5) + r) (t + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 1) (t + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + 5) + r) + 2) ((t + 3) + Rule30UOR.Core.twopow k))
    (ha : a ≤ (t + Rule30UOR.Core.twopow (k + 1)) - (r + 2))
    (hL : (t + Rule30UOR.Core.twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : Rule30UOR.Interfaces.WinWittAgree t k 5 a L) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 5) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r - 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r - 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_same_bit_r_sub_one_flip_five_of_doubles_five_and_single_winwittagree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Exact Finite Target refutation `¬ CenterPeriodic T P` from `RhColAgree t (m * P) 1 S` (`t + m * P ≤ S + 1`) from the verified paper**. -/
theorem not_centerperiodic_of_rhcolagree_one_horizon_kit
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hrh : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhcolagree_one_horizon T P m t S hP hm ht hS hrh

/-- **Exact Finite Target refutation `¬ CenterPeriodic T P` from `LhColAgree t (m * P) 1 S` (`t + m * P ≤ S + 1`) from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_horizon_kit
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_horizon T P m t S hP hm ht hS hlh

/-- **Exact Finite Target refutation `¬ CenterPeriodic T P` from `RhBandAgree t (m * P) 0 (S + 1)` (`t + m * P ≤ S + 1`) from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_zero_horizon_kit
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (S + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_zero_horizon T P m t S hP hm ht hS hband

/-- **Exact Finite Target refutation `¬ CenterPeriodic T P` via `K`-column inward determination from column `1 + K` from the verified paper**. -/
theorem not_centerperiodic_of_rhcenter_inward_determine_horizon_kit
    (T P m t S K : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (hcol : Rule30UOR.Interfaces.RhColAgree t (m * P) (1 + K) (S + K))
    (hor : Rule30UOR.Interfaces.RhOrAgree t (m * P) (1 + K) (S + K)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhcenter_inward_determine_horizon T P m t S K hP hm ht hS hcol hor

/-- **Producing `RhColAgree t (m * P) 1 S` from `RhOrAgree t (m * P) 1 S` and initial agreement at `(t, 1)` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_rhcolagree_one_of_rhoragree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h0 : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hor : Rule30UOR.Interfaces.RhOrAgree t (m * P) 1 S) :
    Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.periodic_rhcolagree_one_of_rhoragree_one T P hP hper m t S ht h0 hor

/-- **Exact Finite Target refutation `¬ CenterPeriodic T P` from `RhOrAgree t (m * P) 1 S` and initial agreement at `(t, 1)` (`t + m * P ≤ S + 1`) from the verified paper**. -/
theorem not_centerperiodic_of_rhoragree_one_horizon_kit
    (T P m t S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hS : t + m * P ≤ S + 1)
    (h0 : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hor : Rule30UOR.Interfaces.RhOrAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhoragree_one_horizon T P m t S hP hm ht hS h0 hor

/-- **Scale-free universal-in-`Q` settled `ldiag` periodicity below any doubling point from the verified paper**. -/
theorem ldiag_settled_periodic_of_doubles_le_kit (Q z d t : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z) (hdz : d ≤ z)
    (hset : Rule30UOR.Interfaces.SettledBy d t) :
    Rule30UOR.Core.ldiag d (t + Q) = Rule30UOR.Core.ldiag d t :=
  Rule30Paper.Paper.ldiag_settled_periodic_of_doubles_le Q z d t hd hdz hset

/-- **Scale-free universal-in-`Q` settled `ldiag` antiperiodicity on the doubling diagonal `z + 1` from the verified paper**. -/
theorem ldiag_settled_antiperiodic_of_doubles_kit (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) t) :
    Rule30UOR.Core.ldiag (z + 1) (t + Q) = !(Rule30UOR.Core.ldiag (z + 1) t) :=
  Rule30Paper.Paper.ldiag_settled_antiperiodic_of_doubles Q z t hz hd hset

/-- **Scale-free universal-in-`Q` diagonal-shift `lhCenter` agreement below any doubling point from the verified paper**. -/
theorem lhcenter_diag_shift_periodic_of_doubles_le_kit (Q z t p : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) t) :
    Rule30UOR.Interfaces.lhCenter (t + Q) (p + Q) = Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.lhcenter_diag_shift_periodic_of_doubles_le Q z t p hd hdz hset

/-- **Scale-free universal-in-`Q` diagonal-shift `lhCenter` antiperiodicity on the doubling diagonal `z + 1` from the verified paper**. -/
theorem lhcenter_diag_shift_antiperiodic_of_doubles_kit (Q t p : Nat)
    (hp : p ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 1) (t + 1)) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Q) (p + Q) = !(Rule30UOR.Interfaces.lhCenter (t + 1) p) :=
  Rule30Paper.Paper.lhcenter_diag_shift_antiperiodic_of_doubles Q t p hp hz hd hset

/-- **Scale-free universal-in-`Q` single-row spatial `Q`-periodicity on the real orbit under `LhBandAgree` from the verified paper**. -/
theorem lhcenter_spatial_periodic_of_doubles_le_and_lhbandagree_kit (Q z t p p0 L : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t (p + Q) = Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.lhcenter_spatial_periodic_of_doubles_le_and_lhbandagree Q z t p p0 L hd hdz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-row spatial `Q`-flip on `z + 1` under `LhBandAgree` from the verified paper**. -/
theorem lhcenter_spatial_antiperiodic_of_doubles_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hp : p ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 1) (t + 1))
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree (t + 1) Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + Q) = !(Rule30UOR.Interfaces.lhCenter (t + 1) p) :=
  Rule30Paper.Paper.lhcenter_spatial_antiperiodic_of_doubles_and_lhbandagree Q t p p0 L hp hz hd hset hp0 hL hband

/-- **Unconditional vanishing of `winWitt t (2^k)` across the settled left wing and outside the cone from the verified paper**. -/
theorem winwitt_testbit_settled_left_ge_kit (t k p : Nat)
    (hk : t - p ≤ k) (hset : Rule30UOR.Interfaces.SettledBy (t - p) t) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + p) + Rule30UOR.Core.twopow (k + 1)) = false :=
  Rule30Paper.Paper.winwitt_testbit_settled_left_ge t k p hk hset

/-- **Universal-in-`Q` production of `WinWittAgree` across the settled left strip from the verified paper**. -/
theorem winwittagree_settled_left_strip_kit (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → Rule30UOR.Interfaces.SettledBy d t) :
    Rule30UOR.Interfaces.WinWittAgree t k Q ((t + p0) + Rule30UOR.Core.twopow (k + 1)) L :=
  Rule30Paper.Paper.winwittagree_settled_left_strip t k Q p0 L hk hset

/-- **Universal-in-`Q` inward `2^k`-scale transport of `LhBandAgree` across the settled left strip without `WinWittAgree` premise from the verified paper**. -/
theorem lhbandagree_inward_of_settled_left_strip_kit (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → Rule30UOR.Interfaces.SettledBy d t)
    (hlate : Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L) :
    Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.lhbandagree_inward_of_settled_left_strip t k Q p0 L hk hset hlate

/-- **Universal-in-`Q` forward `2^k`-scale transport of `LhBandAgree` across the settled left strip without `WinWittAgree` premise from the verified paper**. -/
theorem lhbandagree_step_of_settled_left_strip_kit (t k Q p0 L : Nat)
    (hk : (t + Q) - p0 ≤ k)
    (hset : ∀ d : Nat, d ≤ (t + Q) - p0 → Rule30UOR.Interfaces.SettledBy d t)
    (h0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.LhBandAgree (t + Rule30UOR.Core.twopow k) Q
      (p0 + Rule30UOR.Core.twopow k) L :=
  Rule30Paper.Paper.lhbandagree_step_of_settled_left_strip t k Q p0 L hk hset h0

/-- **Unconditional `2^k`-scale diagonal-shift identity of `lhCenter` across the settled left wing and outside the cone from the verified paper**. -/
theorem lhcenter_scale_step_settled_left_ge_kit (t k p : Nat)
    (hk : t - p ≤ k) (hset : Rule30UOR.Interfaces.SettledBy (t - p) t) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (p + Rule30UOR.Core.twopow k) =
      Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.lhcenter_scale_step_settled_left_ge t k p hk hset

/-- **Scale-free settled `ldiag` vanishing on any zero diagonal from the verified paper**. -/
theorem ldiag_of_zero_diag_kit (z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z t) :
    Rule30UOR.Core.ldiag z t = false :=
  Rule30Paper.Paper.ldiag_of_zero_diag z t hz hset

/-- **Scale-free settled `ldiag` blackness two diagonals after any zero diagonal from the verified paper**. -/
theorem ldiag_after_zero_diag_kit (z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) t) :
    Rule30UOR.Core.ldiag (z + 2) t = true :=
  Rule30Paper.Paper.ldiag_after_zero_diag z t hz hset

/-- **Scale-free real-orbit `lhCenter` vanishing on any zero diagonal from the verified paper**. -/
theorem lhcenter_of_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) t) :
    Rule30UOR.Interfaces.lhCenter t p = false :=
  Rule30Paper.Paper.lhcenter_of_zero_diag t p hz hset

/-- **Scale-free real-orbit `lhCenter` blackness two diagonals after any zero diagonal from the verified paper**. -/
theorem lhcenter_after_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) (t + 2)) :
    Rule30UOR.Interfaces.lhCenter (t + 2) p = true :=
  Rule30Paper.Paper.lhcenter_after_zero_diag t p hz hset

/-- **Scale-free real-orbit Twin Identity before any zero diagonal from the verified paper**. -/
theorem lhcenter_twin_before_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset : Rule30UOR.Interfaces.SettledBy (t - p) t) :
    Rule30UOR.Interfaces.lhCenter t (p + 2) = Rule30UOR.Interfaces.lhCenter t (p + 1) :=
  Rule30Paper.Paper.lhcenter_twin_before_zero_diag t p hz hset

/-- **Scale-free real-orbit post-black reset complementation from the verified paper**. -/
theorem lhcenter_reset_after_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 2) (t + 2)) :
    Rule30UOR.Interfaces.lhCenter (t + 3) (p + 1) =
      !(Rule30UOR.Interfaces.lhCenter (t + 2) (p + 2)) :=
  Rule30Paper.Paper.lhcenter_reset_after_zero_diag t p hz hset

/-- **Scale-free real-orbit 2-step same-column flip across any zero diagonal from the verified paper**. -/
theorem lhcenter_two_step_same_col_flip_of_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) (t + 2)) :
    Rule30UOR.Interfaces.lhCenter (t + 2) p = !(Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_two_step_same_col_flip_of_zero_diag t p hz hset0 hset2

/-- **Scale-free refutation of `LhBandAgree t 2 p0 L` across any settled zero diagonal from the verified paper**. -/
theorem not_lhbandagree_two_of_zero_diag_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) (t + 2))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree t 2 p0 L :=
  Rule30Paper.Paper.not_lhbandagree_two_of_zero_diag t p p0 L hz hset0 hset2 hp0 hL

/-- **Scale-free general-`Q` refutation of `LhBandAgree t Q p0 L` when `(t + Q) - p = z + 2` from the verified paper**. -/
theorem not_lhbandagree_of_zero_and_after_zero_diag_kit (Q t p z p0 L : Nat)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hrel : (t + Q) - p = z + 2)
    (hset1 : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.not_lhbandagree_of_zero_and_after_zero_diag Q t p z p0 L hz1 hz2 hrel hset1 hset2 hp0 hL

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` transport of zero-diagonal vanishing down to row `t` from the verified paper**. -/
theorem lhcenter_eq_false_at_shift_of_zero_diag_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t p = false :=
  Rule30Paper.Paper.lhcenter_eq_false_at_shift_of_zero_diag_and_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` transport of post-zero blackness down to row `t` from the verified paper**. -/
theorem lhcenter_eq_true_at_shift_after_zero_diag_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - (p + 2)))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) - (p + 2)) + 2) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t p = true :=
  Rule30Paper.Paper.lhcenter_eq_true_at_shift_after_zero_diag_and_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` 1-step post-black reset complementation from the verified paper**. -/
theorem lhcenter_step_flip_at_shift_after_zero_diag_of_single_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - (p + 3)))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) - (p + 3)) + 2) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = !(Rule30UOR.Interfaces.lhCenter t (p + 2)) :=
  Rule30Paper.Paper.lhcenter_step_flip_at_shift_after_zero_diag_of_single_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` 1-step fixed-column jump to `true` from the verified paper**. -/
theorem lhcenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - (p + 2)))
    (hset0 : Rule30UOR.Interfaces.SettledBy ((t + Q) - (p + 2)) (t + Q))
    (hset2 : Rule30UOR.Interfaces.SettledBy (((t + Q) - (p + 2)) + 2) (t + Q))
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = true :=
  Rule30Paper.Paper.lhcenter_step_one_eq_true_at_shift_of_zero_diag_and_single_lhbandagree
    Q t p p0 L hz hset0 hset2 hp0 hL hband

/-- **Producing `LhBandAgree t (m * P) 0 (S + 1)` directly from `RhColAgree t (m * P) 1 S` under `CenterPeriodic` from the verified paper**. -/
theorem periodic_lhbandagree_zero_of_rhcolagree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hrh : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S) :
    Rule30UOR.Interfaces.LhBandAgree t (m * P) 0 (S + 1) :=
  Rule30Paper.Paper.periodic_lhbandagree_zero_of_rhcolagree_one T P hP hper m t S ht hrh

/-- **Producing center-anchored `LhBandAgree (t + s) (m * P) 0 (L + 1)` at every intermediate step `t + s` from `RhColAgree t (m * P) 1 (L + s)` under `CenterPeriodic` from the verified paper**. -/
theorem periodic_lhbandagree_steps_of_rhcolagree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L s : Nat) (ht : T ≤ t)
    (hrh : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 (L + s)) :
    Rule30UOR.Interfaces.LhBandAgree (t + s) (m * P) 0 (L + 1) :=
  Rule30Paper.Paper.periodic_lhbandagree_steps_of_rhcolagree_one T P hP hper m t L s ht hrh

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` transport of the twin identity down by `Q` steps from the verified paper**. -/
theorem lhcenter_twin_at_shift_of_zero_diag_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 2 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t (p + 2) = Rule30UOR.Interfaces.lhCenter t (p + 1) :=
  Rule30Paper.Paper.lhcenter_twin_at_shift_of_zero_diag_and_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` linearization 1 below any zero diagonal from the verified paper**. -/
theorem lhcenter_linear_step_one_at_shift_of_zero_diag_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter t (p + 2)) (Rule30UOR.Interfaces.lhCenter t (p + 1)) :=
  Rule30Paper.Paper.lhcenter_linear_step_one_at_shift_of_zero_diag_and_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` linearization 2 below any zero diagonal from the verified paper**. -/
theorem lhcenter_linear_step_two_at_shift_of_zero_diag_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - (p + 1)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) - (p + 1)) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.lhCenter t (p + 2)) (Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_linear_step_two_at_shift_of_zero_diag_and_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` twin cancellation pinning `lhCenter (t + 1) (p + 1) = false` from the verified paper**. -/
theorem lhcenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - p))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = false :=
  Rule30Paper.Paper.lhcenter_step_one_eq_false_at_shift_of_zero_diag_and_single_lhbandagree Q t p p0 L hz hset hp0 hL hband

/-- **Scale-free general-`Q` single-time refutation of `LhBandAgree t Q p0 L` when both `t - (p + 2)` and `(t + Q) - p` are zero diagonals from the verified paper**. -/
theorem not_lhbandagree_of_zero_diag_two_and_shift_zero_diag_kit (Q t p p0 L : Nat)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 2)))
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - p))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 2)) + 2) (t + 1))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t + Q) - p) (t + Q))
    (hp0 : p0 ≤ p) (hL : p + 2 ≤ p0 + L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree t Q p0 L :=
  Rule30Paper.Paper.not_lhbandagree_of_zero_diag_two_and_shift_zero_diag Q t p p0 L hz1 hz2 hset1 hset2 hp0 hL

/-- **Scale-free real-orbit 1-step post-zero OR-absorption law on `z + 4` from the verified paper**. -/
theorem lhcenter_step_absorb_false_after_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 2)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 2)) + 2) (t + 2))
    (h3 : Rule30UOR.Interfaces.lhCenter (t + 2) (p + 1) = true) :
    Rule30UOR.Interfaces.lhCenter (t + 3) (p + 1) = false :=
  Rule30Paper.Paper.lhcenter_step_absorb_false_after_zero_diag t p hz hset h3

/-- **Scale-free real-orbit 2-step post-zero reset-and-absorption law from `z + 1` to `z + 4` from the verified paper**. -/
theorem lhcenter_two_step_absorb_false_after_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 2)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 2)) + 2) (t + 2))
    (h1 : Rule30UOR.Interfaces.lhCenter (t + 2) (p + 3) = false) :
    Rule30UOR.Interfaces.lhCenter (t + 4) (p + 2) = false :=
  Rule30Paper.Paper.lhcenter_two_step_absorb_false_after_zero_diag t p hz hset h1

/-- **Unconditional cross-center zero-diagonal vanishing without `t + r ≤ k` from the verified paper**. -/
theorem lhcenter_late_cross_of_zero_diag_uncond_kit (t k r : Nat)
    (hr : r ≤ Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) = false :=
  Rule30Paper.Paper.lhcenter_late_cross_of_zero_diag_uncond t k r hr hz hset

/-- **Unconditional cross-center post-zero blackness without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem lhcenter_late_cross_after_zero_diag_uncond_kit (t k r : Nat)
    (hr : r + 2 ≤ Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) = true :=
  Rule30Paper.Paper.lhcenter_late_cross_after_zero_diag_uncond t k r hr hz hset

/-- **Unconditional cross-center post-black reset complementation without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem lhcenter_late_cross_reset_after_zero_diag_uncond_kit (t k r : Nat)
    (hr : r + 3 ≤ Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 2)) =
      !(Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1))) :=
  Rule30Paper.Paper.lhcenter_late_cross_reset_after_zero_diag_uncond t k r hr hz hset

/-- **Unconditional cross-center twin identity before any zero diagonal without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem lhcenter_late_cross_twin_before_zero_diag_uncond_kit (t k r : Nat)
    (hr : r + 2 ≤ Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) :=
  Rule30Paper.Paper.lhcenter_late_cross_twin_before_zero_diag_uncond t k r hr hz hset

/-- **Unconditional cross-center `Q`-periodicity below any doubling point without `z ≤ k` from the verified paper**. -/
theorem lhcenter_late_cross_periodic_of_doubles_le_uncond_kit (Q z t k r : Nat)
    (hr : r + Q ≤ Rule30UOR.Core.twopow k)
    (hdz : (t + Q) + r ≤ z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - r) =
      Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + Q)) :=
  Rule30Paper.Paper.lhcenter_late_cross_periodic_of_doubles_le_uncond Q z t k r hr hdz hd hset

/-- **Unconditional cross-center `Q`-antiperiodicity on the doubling diagonal `z + 1` without `z + 1 ≤ k` from the verified paper**. -/
theorem lhcenter_late_cross_antiperiodic_of_doubles_uncond_kit (Q t k r : Nat)
    (hr : (r + Q) + 1 ≤ Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - (r + 1)) =
      !(Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k - ((r + Q) + 1))) :=
  Rule30Paper.Paper.lhcenter_late_cross_antiperiodic_of_doubles_uncond Q t k r hr hz hd hset

/-- **Unconditional Sector-2 cross-center window mirror along any zero diagonal without `t + r ≤ k` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_of_zero_diag_uncond_kit (t k r : Nat)
    (hlt : t + r < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = Rule30UOR.Interfaces.rhCenter t r :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_of_zero_diag_uncond t k r hlt hz hset

/-- **Unconditional Sector-2 inter-cone zero-gap `false` pinning along any zero diagonal without `t + r ≤ k` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_of_zero_diag_uncond_kit (t k r : Nat)
    (htr : t < r) (hlt : t + r < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy (t + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) = false :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap_of_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional Sector-2 cross-center negated window mirror along the post-zero black diagonal without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_after_zero_diag_uncond_kit (t k r : Nat)
    (hlt : (t + r) + 2 < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = !(Rule30UOR.Interfaces.rhCenter t (r + 2)) :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_after_zero_diag_uncond t k r hlt hz hset

/-- **Unconditional Sector-2 inter-cone zero-gap `true` pinning along the post-zero black diagonal without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_after_zero_diag_uncond_kit (t k r : Nat)
    (htr : t < r + 2) (hlt : (t + r) + 2 < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 2)) = true :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap_after_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional Sector-2 inter-cone zero-gap adjacent twin equality before any zero diagonal without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem winwitt_testbit_scale_cross_zero_gap_twin_before_zero_diag_uncond_kit (t k r : Nat)
    (htr : t < r) (hlt : (t + r) + 2 ≤ Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + r) + 2))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) :=
  Rule30Paper.Paper.winwitt_testbit_scale_cross_zero_gap_twin_before_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional 1-step Sector-2 bit flip in the inter-cone zero gap across the post-zero black diagonal without `(t + r) + 2 ≤ k` from the verified paper**. -/
theorem winwitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond_kit (t k r : Nat)
    (htr : t ≤ r) (hlt : (t + r) + 3 < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t + r))
    (hset : Rule30UOR.Interfaces.SettledBy ((t + r) + 2) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + 1) (Rule30UOR.Core.twopow k))
      ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) :=
  Rule30Paper.Paper.winwitt_sector_two_step_flip_zero_gap_after_zero_diag_uncond t k r htr hlt hz hset

/-- **Unconditional Sector-2 cross-center `winWitt` `Q`-periodicity below any doubling point without `z ≤ k` from the verified paper**. -/
theorem winwitt_scale_cross_periodic_of_doubles_le_uncond_kit (Q z t k r : Nat)
    (hlt : (t + Q) + r < Rule30UOR.Core.twopow k)
    (hdz : (t + Q) + r ≤ z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + Q)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - r)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t (r + Q)) (Rule30UOR.Interfaces.rhCenter (t + Q) r) :=
  Rule30Paper.Paper.winwitt_scale_cross_periodic_of_doubles_le_uncond Q z t k r hlt hdz hd hset

/-- **Unconditional Sector-2 inter-cone zero-gap `Q`-periodicity below any doubling point without `z ≤ k` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond_kit (Q z t k r : Nat)
    (ht : t + Q < r) (hlt : (t + Q) + r < Rule30UOR.Core.twopow k)
    (hdz : (t + Q) + r ≤ z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy ((t + Q) + r) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
      (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - r) =
      Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - (r + Q)) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_periodic_of_doubles_le_uncond Q z t k r ht hlt hdz hd hset

/-- **Unconditional Sector-2 cross-center `winWitt` `Q`-antiperiodicity on the doubling diagonal `z + 1` without `z + 1 ≤ k` from the verified paper**. -/
theorem winwitt_scale_cross_antiperiodic_of_doubles_uncond_kit (Q t k r : Nat)
    (hlt : ((t + Q) + r) + 1 < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1)))
      (Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
        (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - (r + 1))) =
      !(Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter t ((r + Q) + 1)) (Rule30UOR.Interfaces.rhCenter (t + Q) (r + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_antiperiodic_of_doubles_uncond Q t k r hlt hz hd hset

/-- **Unconditional Sector-2 inter-cone zero-gap `Q`-antiperiodicity on the doubling diagonal `z + 1` without `z + 1 ≤ k` from the verified paper**. -/
theorem winwitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond_kit (Q t k r : Nat)
    (ht : t + Q ≤ r) (hlt : ((t + Q) + r) + 1 < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) + r))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q ((t + Q) + r))
    (hset : Rule30UOR.Interfaces.SettledBy (((t + Q) + r) + 1) (t + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt (t + Q) (Rule30UOR.Core.twopow k))
      (((t + Q) + Rule30UOR.Core.twopow (k + 1)) - (r + 1)) =
      !(Rule30UOR.Interfaces.wittBitBool (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k))
        ((t + Rule30UOR.Core.twopow (k + 1)) - ((r + Q) + 1))) :=
  Rule30Paper.Paper.winwitt_scale_cross_zero_gap_antiperiodic_of_doubles_uncond Q t k r ht hlt hz hd hset

/-- **Scale-free real-orbit post-zero blackness directly at row `t` from the verified paper**. -/
theorem lhcenter_at_t_after_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 2)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 2)) + 2) t) :
    Rule30UOR.Interfaces.lhCenter t p = true :=
  Rule30Paper.Paper.lhcenter_at_t_after_zero_diag t p hz hset

/-- **Scale-free real-orbit 1-step post-black reset complementation directly from row `t` from the verified paper**. -/
theorem lhcenter_step_one_reset_after_zero_diag_kit (t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = !(Rule30UOR.Interfaces.lhCenter t (p + 2)) :=
  Rule30Paper.Paper.lhcenter_step_one_reset_after_zero_diag t p hz hset

/-- **Scale-free universal-in-`Q` diagonal-shift antiperiodicity directly at row `t` without `p ≤ t` from the verified paper**. -/
theorem lhcenter_diag_shift_antiperiodic_at_t_of_doubles_kit (Q t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 1)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t) :
    Rule30UOR.Interfaces.lhCenter (t + Q) (p + Q) = !(Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_diag_shift_antiperiodic_at_t_of_doubles Q t p hz hd hset

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` spatial `Q`-flip on `z + 1` directly at row `t` from the verified paper**. -/
theorem lhcenter_spatial_antiperiodic_at_t_of_doubles_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 1)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t (p + Q) = !(Rule30UOR.Interfaces.lhCenter t p) :=
  Rule30Paper.Paper.lhcenter_spatial_antiperiodic_at_t_of_doubles_and_lhbandagree Q t p p0 L hz hd hset hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` space-time equivalence of `(t, (p + 2) + Q)` and `(t + 1, p + 1)` from the verified paper**. -/
theorem lhcenter_spatial_doubles_eq_step_one_reset_of_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 3)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ (p + 2) + Q) (hL : (p + 2) + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t ((p + 2) + Q) = Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) :=
  Rule30Paper.Paper.lhcenter_spatial_doubles_eq_step_one_reset_of_lhbandagree Q t p p0 L hz hd hset1 hset2 hp0 hL hband

/-- **Scale-free universal-in-`Q` real-orbit space-time equivalence of `(t + Q, (p + 2) + Q)` and `(t + 1, p + 1)` from the verified paper**. -/
theorem lhcenter_doubles_eq_step_one_reset_kit (Q t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 3)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t) :
    Rule30UOR.Interfaces.lhCenter (t + Q) ((p + 2) + Q) = Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) :=
  Rule30Paper.Paper.lhcenter_doubles_eq_step_one_reset Q t p hz hd hset1 hset2

/-- **Scale-free universal-in-`Q` diagonal-shift antiperiodicity on the post-black reset diagonal `z + 3` from the verified paper**. -/
theorem lhcenter_step_one_reset_antiperiodic_of_doubles_kit (Q t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 3)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + 1) ((p + Q) + 1) = !(Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1)) :=
  Rule30Paper.Paper.lhcenter_step_one_reset_antiperiodic_of_doubles Q t p hz hd hset1 hset2

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` spatial `Q`-flip at row `t + 1` on `z + 3` from the verified paper**. -/
theorem lhcenter_step_one_reset_shift_flip_of_doubles_and_single_lhbandagree_kit (Q t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 3)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ (p + 1) + Q) (hL : (p + 2) + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) ((p + 1) + Q) = !(Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1)) :=
  Rule30Paper.Paper.lhcenter_step_one_reset_shift_flip_of_doubles_and_single_lhbandagree Q t p p0 L hz hd hset1 hset2 hp0 hL hband

/-- **Scale-free `Q = 1` real-orbit pinning of `lhCenter t (p + 1) = true` under `LhBandAgree t 1 p0 L` from the verified paper**. -/
theorem lhcenter_pin_doubling_diag_true_of_doubles_one_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 2)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 (t - (p + 2)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 2)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 2)) + 1) t)
    (hp0 : p0 ≤ p + 2) (hL : p + 2 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 1 p0 L) :
    Rule30UOR.Interfaces.lhCenter t (p + 1) = true :=
  Rule30Paper.Paper.lhcenter_pin_doubling_diag_true_of_doubles_one_and_lhbandagree t p p0 L hz hd hset0 hset1 hp0 hL hband

/-- **Scale-free `Q = 1` real-orbit pinning of `lhCenter (t + 1) (p + 1) = false` under `LhBandAgree t 1 p0 L` from the verified paper**. -/
theorem lhcenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 (t - (p + 3)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 3)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ p + 3) (hL : p + 3 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 1 p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = false :=
  Rule30Paper.Paper.lhcenter_step_one_pin_reset_diag_false_of_doubles_one_and_lhbandagree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-free single-time refutation of `LhBandAgree t 1 p0 L` from `DoublesAt 1 (t - (p + 3))` from the verified paper**. -/
theorem not_lhbandagree_one_of_doubles_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 (t - (p + 3)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 3)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t)
    (hp0 : p0 ≤ p + 1) (hL : p + 3 ≤ p0 + L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree t 1 p0 L :=
  Rule30Paper.Paper.not_lhbandagree_one_of_doubles t p p0 L hz hd hset0 hset1 hset2 hp0 hL

/-- **Scale-free refutation of `RhColAgree t 1 1 S` under `CenterPeriodic T 1` from `DoublesAt 1 (t - (p + 3))` from the verified paper**. -/
theorem not_periodic_rhcolagree_one_of_doubles_one_kit (T : Nat)
    (hper : Rule30UOR.Scale.CenterPeriodic T 1)
    (t p S : Nat) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 3)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 1 (t - (p + 3)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 3)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 3)) + 2) t)
    (hS : p + 2 ≤ S) :
    ¬ Rule30UOR.Interfaces.RhColAgree t 1 1 S :=
  Rule30Paper.Paper.not_periodic_rhcolagree_one_of_doubles_one T hper t p S ht hz hd hset0 hset1 hset2 hS

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` pinning of `lhCenter t (p + 2) = true` from `IsZeroDiag (t - p)` and `IsZeroDiag ((t + Q) - (p + 3))` from the verified paper**. -/
theorem lhcenter_pin_plus_two_true_of_lhbandagree_and_zero_diag_three_kit (Q t p p0 L : Nat)
    (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hzQ : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - (p + 3)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (((t + Q) - (p + 3)) + 2) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter t (p + 2) = true :=
  Rule30Paper.Paper.lhcenter_pin_plus_two_true_of_lhbandagree_and_zero_diag_three Q t p p0 L hz0 hzQ hset0 hsetQ hp0 hL hband

/-- **Scale-free universal-in-`Q` single-time `LhBandAgree` pinning of `lhCenter (t + 1) (p + 1) = false` from `IsZeroDiag (t - p)` and `IsZeroDiag ((t + Q) - (p + 3))` from the verified paper**. -/
theorem lhcenter_step_one_pin_plus_one_false_of_lhbandagree_and_zero_diag_three_kit (Q t p p0 L : Nat)
    (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hzQ : Rule30UOR.ZeroDiagonals.IsZeroDiag ((t + Q) - (p + 3)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (((t + Q) - (p + 3)) + 2) (t + Q))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = false :=
  Rule30Paper.Paper.lhcenter_step_one_pin_plus_one_false_of_lhbandagree_and_zero_diag_three Q t p p0 L hz0 hzQ hset0 hsetQ hp0 hL hband

/-- **Scale-free `Q = 3` single-time `LhBandAgree` pinning of `lhCenter t (p + 2) = true` from a single zero diagonal `t - p` from the verified paper**. -/
theorem lhcenter_pin_before_zero_diag_of_zero_diag_three_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - p))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - p) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - p) + 2) (t + 3))
    (hp0 : p0 ≤ p + 1) (hL : p + 1 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 3 p0 L) :
    Rule30UOR.Interfaces.lhCenter t (p + 2) = true :=
  Rule30Paper.Paper.lhcenter_pin_before_zero_diag_of_zero_diag_three_and_lhbandagree t p p0 L hz hset0 hset2 hp0 hL hband

/-- **Scale-free `Q = 3` single-time `LhBandAgree` pinning of `lhCenter t p = false` on the doubling diagonal `z + 1` from the verified paper**. -/
theorem lhcenter_pin_doubling_diag_false_of_doubles_three_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 (t - (p + 1)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 1)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 2) (t + 3))
    (hp0 : p0 ≤ p + 2) (hL : p + 3 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 3 p0 L) :
    Rule30UOR.Interfaces.lhCenter t p = false :=
  Rule30Paper.Paper.lhcenter_pin_doubling_diag_false_of_doubles_three_and_lhbandagree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-free `Q = 3` single-time `LhBandAgree` pinning of `lhCenter (t + 1) (p + 1) = true` from the verified paper**. -/
theorem lhcenter_step_one_pin_plus_one_true_of_doubles_three_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 (t - (p + 1)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 1)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 2) (t + 3))
    (hp0 : p0 ≤ p + 2) (hL : p + 3 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 3 p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 1) (p + 1) = true :=
  Rule30Paper.Paper.lhcenter_step_one_pin_plus_one_true_of_doubles_three_and_lhbandagree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-free `Q = 3` single-time `LhBandAgree` pinning of `lhCenter (t + 2) (p + 2) = false` from the verified paper**. -/
theorem lhcenter_step_two_pin_plus_two_false_of_doubles_three_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 (t - (p + 1)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 1)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 2) (t + 3))
    (hp0 : p0 ≤ p + 2) (hL : p + 4 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 3 p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 2) (p + 2) = false :=
  Rule30Paper.Paper.lhcenter_step_two_pin_plus_two_false_of_doubles_three_and_lhbandagree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-free `Q = 3` single-time `LhBandAgree` pinning of `lhCenter (t + 3) (p + 1) = true` from the verified paper**. -/
theorem lhcenter_step_three_pin_plus_one_true_of_doubles_three_and_lhbandagree_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 (t - (p + 1)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 1)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 2) (t + 2))
    (hp0 : p0 ≤ p + 2) (hL : p + 4 ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t 3 p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + 3) (p + 1) = true :=
  Rule30Paper.Paper.lhcenter_step_three_pin_plus_one_true_of_doubles_three_and_lhbandagree t p p0 L hz hd hset0 hset1 hset2 hp0 hL hband

/-- **Scale-free single-time refutation of `LhBandAgree t 3 p0 L` from `DoublesAt 3 (t - (p + 1))` from the verified paper**. -/
theorem not_lhbandagree_three_of_doubles_kit (t p p0 L : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt 3 (t - (p + 1)))
    (hset0 : Rule30UOR.Interfaces.SettledBy (t - (p + 1)) t)
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hset2 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 2) (t + 2))
    (hp0 : p0 ≤ p + 1) (hL : p + 4 ≤ p0 + L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree t 3 p0 L :=
  Rule30Paper.Paper.not_lhbandagree_three_of_doubles t p p0 L hz hd hset0 hset1 hset2 hp0 hL

/-- **Scale-free dyadic `2^d`-periodicity of settled `ldiag` from the verified paper**. -/
theorem ldiag_settled_twopow_periodic_kit (d t : Nat)
    (hset : Rule30UOR.Interfaces.SettledBy d t) :
    Rule30UOR.Core.ldiag d (t + Rule30UOR.Core.twopow d) = Rule30UOR.Core.ldiag d t :=
  Rule30Paper.Paper.ldiag_settled_twopow_periodic d t hset

/-- **Scale-free common dyadic `2^e`-periodicity of settled `ldiag d` (`d ≤ e`) from the verified paper**. -/
theorem ldiag_settled_twopow_periodic_le_kit (e d t : Nat)
    (hde : d ≤ e) (hset : Rule30UOR.Interfaces.SettledBy d t) :
    Rule30UOR.Core.ldiag d (t + Rule30UOR.Core.twopow e) = Rule30UOR.Core.ldiag d t :=
  Rule30Paper.Paper.ldiag_settled_twopow_periodic_le e d t hde hset

/-- **Scale-free period-doubling `Q + Q`-periodicity on `z + 1` from the verified paper**. -/
theorem ldiag_settled_two_mul_periodic_of_doubles_kit (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) t) :
    Rule30UOR.Core.ldiag (z + 1) (t + (Q + Q)) = Rule30UOR.Core.ldiag (z + 1) t :=
  Rule30Paper.Paper.ldiag_settled_two_mul_periodic_of_doubles Q z t hz hd hset

/-- **Scale-free `Q`-antiperiodicity on the post-black reset diagonal `z + 3` from the verified paper**. -/
theorem ldiag_settled_reset_antiperiodic_of_doubles_kit (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 3) t) :
    Rule30UOR.Core.ldiag (z + 3) (t + Q) = !Rule30UOR.Core.ldiag (z + 3) t :=
  Rule30Paper.Paper.ldiag_settled_reset_antiperiodic_of_doubles Q z t hz hd hset

/-- **Scale-free common doubled period `Q + Q` through `z + 3` from the verified paper**. -/
theorem ldiag_settled_two_mul_periodic_le_add_three_of_doubles_kit (Q z d t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hdz : d ≤ z + 3) (hset : Rule30UOR.Interfaces.SettledBy d t) :
    Rule30UOR.Core.ldiag d (t + (Q + Q)) = Rule30UOR.Core.ldiag d t :=
  Rule30Paper.Paper.ldiag_settled_two_mul_periodic_le_add_three_of_doubles Q z d t hz hd hdz hset

/-- **Existence of a zero-diagonal doubling point for `twopow e` from the verified paper**. -/
theorem exists_zero_diag_doublesat_twopow_kit (e : Nat) :
    ∃ z : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow e) z :=
  Rule30Paper.Paper.exists_zero_diag_doublesat_twopow e

/-- **Existence of a zero-diagonal doubling point for `m * P` from the verified paper**. -/
theorem exists_zero_diag_doublesat_mul_kit (m P : Nat) (hm : 0 < m) (hP : 0 < P) :
    ∃ z : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z :=
  Rule30Paper.Paper.exists_zero_diag_doublesat_mul m P hm hP

/-- **Dyadic doubling depth lower bound `e ≤ z` from the verified paper**. -/
theorem doublesat_twopow_le_kit (e z : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow e) z) :
    e ≤ z :=
  Rule30Paper.Paper.doublesat_twopow_le e z hd

/-- **Unbounded depth of dyadic doubling zero diagonals from the verified paper**. -/
theorem exists_zero_diag_doublesat_twopow_ge_kit (e : Nat) :
    ∃ z : Nat, e ≤ z ∧ Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow e) z :=
  Rule30Paper.Paper.exists_zero_diag_doublesat_twopow_ge e

/-- **Scale-free universal-in-`Q` 2-shift diagonal periodicity on `z + 1` from the verified paper**. -/
theorem lhcenter_two_shift_diag_periodic_of_doubles_kit (Q t p : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 1)))
    (hset : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Q) ((p + Q) + Q) = Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.lhcenter_two_shift_diag_periodic_of_doubles Q t p hz hd hset

/-- **Scale-free universal-in-`Q` (`1 ≤ Q`) single-time `LhBandAgree` flip at `(t + Q, (p + Q) + Q)` from the verified paper**. -/
theorem lhcenter_shift_two_q_flip_of_doubles_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter (t + Q) ((p + Q) + Q) = !Rule30UOR.Interfaces.lhCenter t p :=
  Rule30Paper.Paper.lhcenter_shift_two_q_flip_of_doubles_and_lhbandagree Q t p p0 L hQ hz hd hset1 hsetQ hp0 hL hband

/-- **Scale-free universal-in-`Q` (`1 ≤ Q`) single-time `LhBandAgree` same-column `Q`-flip at `(p + Q) + Q` from the verified paper**. -/
theorem lhcenter_same_col_two_q_flip_of_doubles_and_lhbandagree_kit (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    Rule30UOR.Interfaces.lhCenter ((t + Q) + Q) ((p + Q) + Q) =
      !Rule30UOR.Interfaces.lhCenter (t + Q) ((p + Q) + Q) :=
  Rule30Paper.Paper.lhcenter_same_col_two_q_flip_of_doubles_and_lhbandagree Q t p p0 L hQ hz hd hset1 hsetQ hp0 hL hband

/-- **Scale-free universal-in-`Q` (`1 ≤ Q`) refutation of `LhBandAgree (t + Q) Q` under `LhBandAgree t Q` from the verified paper**. -/
theorem not_lhbandagree_step_q_of_doubles_kit (Q t p p0 L p1 L1 : Nat)
    (hQ : 1 ≤ Q)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt Q (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : p + Q ≤ p0 + L)
    (hp1 : p1 ≤ (p + Q) + Q) (hL1 : (p + Q) + Q ≤ p1 + L1)
    (hband0 : Rule30UOR.Interfaces.LhBandAgree t Q p0 L) :
    ¬ Rule30UOR.Interfaces.LhBandAgree (t + Q) Q p1 L1 :=
  Rule30Paper.Paper.not_lhbandagree_step_q_of_doubles Q t p p0 L p1 L1 hQ hz hd hset1 hsetQ hp0 hL hp1 hL1 hband0

/-- **Scale-free universal-in-`m, P` refutation of `RhColAgree t (m * P) 1 S` under `CenterPeriodic T P` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_periodic_rhcolagree_one_of_doubles_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t p S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.not_periodic_rhcolagree_one_of_doubles T P hP hper m t p S hm ht hz hd hset1 hsetQ hS

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from `RhColAgree t (m * P) 1 S` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_rhcolagree_one_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hrh : Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhcolagree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hrh


/-- **Scale-free universal-in-`m, P` refutation of `LhColAgree t (m * P) 1 S` under `CenterPeriodic T P` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_periodic_lhcolagree_one_of_doubles_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t p S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.not_periodic_lhcolagree_one_of_doubles T P hP hper m t p S hm ht hz hd hset1 hsetQ hS

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from `LhColAgree t (m * P) 1 S` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hlh

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from `RhBandAgree t (m * P) 0 (S + 1)` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_zero_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 0 (S + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_zero_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hband

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` via `K`-column inward determination at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_rhcenter_inward_determine_doubles_kit
    (T P m t p S K : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hcol : Rule30UOR.Interfaces.RhColAgree t (m * P) (1 + K) (S + K))
    (hor : Rule30UOR.Interfaces.RhOrAgree t (m * P) (1 + K) (S + K)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhcenter_inward_determine_doubles T P m t p S K hP hm ht hz hd hset1 hsetQ hS hcol hor

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from `RhOrAgree t (m * P) 1 S` and initial agreement at `(t, 1)` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_rhoragree_one_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h0 : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hor : Rule30UOR.Interfaces.RhOrAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhoragree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS h0 hor

/-- **Direct `z + (p + 1)` coordinate refutation of `RhColAgree (z + (p + 1)) (m * P) 1 S` at any doubling zero diagonal `z` from the verified paper**. -/
theorem not_periodic_rhcolagree_one_at_zero_diag_doubles_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z p S : Nat) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1) :
    ¬ Rule30UOR.Interfaces.RhColAgree (z + (p + 1)) (m * P) 1 S :=
  Rule30Paper.Paper.not_periodic_rhcolagree_one_at_zero_diag_doubles T P hP hper m z p S hm ht hz hd hset1 hsetQ hS

/-- **Unconditional existence of a doubling zero diagonal `z` and settled column `p` refuting `RhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))` under `CenterPeriodic T P` alone from the verified paper**. -/
theorem exists_zero_diag_not_periodic_rhcolagree_one_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      ¬ Rule30UOR.Interfaces.RhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P)) :=
  Rule30Paper.Paper.exists_zero_diag_not_periodic_rhcolagree_one T P hP hper m hm

/-- **Unconditional existence of a doubling zero diagonal `z` and settled column `p` refuting `LhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P))` under `CenterPeriodic T P` alone from the verified paper**. -/
theorem exists_zero_diag_not_periodic_lhcolagree_one_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      ¬ Rule30UOR.Interfaces.LhColAgree (z + (p + 1)) (m * P) 1 (p + 3 * (m * P)) :=
  Rule30Paper.Paper.exists_zero_diag_not_periodic_lhcolagree_one T P hP hper m hm

/-- **Scale-`0` masked parity `maskparity t 0` as the exact white-center column-`1` readout from the verified paper**. -/
theorem maskparity_zero_eq_not_center_and_rhcenter_one_kit (t : Nat) :
    Rule30UOR.Scale.maskparity t 0 =
      (!Rule30UOR.Core.center t && Rule30UOR.Interfaces.rhCenter t 1) :=
  Rule30Paper.Paper.maskparity_zero_eq_not_center_and_rhcenter_one t

/-- **Unconditional left-half column-`-1` agreement at every black center `center t = true` from the verified paper**. -/
theorem periodic_lhcenter_one_eq_of_black_center_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hb : Rule30UOR.Core.center t = true) :
    Rule30UOR.Interfaces.lhCenter (t + m * P) 1 = Rule30UOR.Interfaces.lhCenter t 1 :=
  Rule30Paper.Paper.periodic_lhcenter_one_eq_of_black_center T P hP hper m t ht hb

/-- **Producing left-half column-`-1` agreement from white-center column-`1` agreement alone from the verified paper**. -/
theorem periodic_lhcenter_one_eq_of_white_center_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hw : Rule30UOR.Core.center t = false →
      Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1) :
    Rule30UOR.Interfaces.lhCenter (t + m * P) 1 = Rule30UOR.Interfaces.lhCenter t 1 :=
  Rule30Paper.Paper.periodic_lhcenter_one_eq_of_white_center T P hP hper m t ht hw

/-- **Producing left-half column-`-1` agreement from first-bit `maskparity · 0` agreement from the verified paper**. -/
theorem periodic_lhcenter_one_eq_of_maskparity_zero_eq_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hm0 : Rule30UOR.Scale.maskparity (t + m * P) 0 = Rule30UOR.Scale.maskparity t 0) :
    Rule30UOR.Interfaces.lhCenter (t + m * P) 1 = Rule30UOR.Interfaces.lhCenter t 1 :=
  Rule30Paper.Paper.periodic_lhcenter_one_eq_of_maskparity_zero_eq T P hP hper m t ht hm0

/-- **Producing full left-band agreement `LhBandAgree t (m * P) 0 (S + 1)` from white-center column-`1` agreement alone from the verified paper**. -/
theorem periodic_lhbandagree_zero_of_white_center_rhcenter_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 = Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    Rule30UOR.Interfaces.LhBandAgree t (m * P) 0 (S + 1) :=
  Rule30Paper.Paper.periodic_lhbandagree_zero_of_white_center_rhcenter_one T P hP hper m t S ht hw

/-- **Producing full left-band agreement `LhBandAgree t (m * P) 0 (S + 1)` from window agreement of `maskparity · 0` from the verified paper**. -/
theorem periodic_lhbandagree_zero_of_maskparity_zero_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Interfaces.LhBandAgree t (m * P) 0 (S + 1) :=
  Rule30Paper.Paper.periodic_lhbandagree_zero_of_maskparity_zero_agree T P hP hper m t S ht hm0

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from white-center column-`1` agreement at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 = Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hw

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from window agreement of `maskparity · 0` at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS hm0

/-- **Direct `z + (p + 1)` coordinate refutation of `CenterPeriodic T P` from white-center column-`1` agreement at any doubling zero diagonal `z` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_at_zero_diag_doubles_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_at_zero_diag_doubles T P m z p S hP hm ht hz hd hset1 hsetQ hS hw

/-- **Direct `z + (p + 1)` coordinate refutation of `CenterPeriodic T P` from `maskparity · 0` agreement at any doubling zero diagonal `z` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_at_zero_diag_doubles_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hm0 : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_at_zero_diag_doubles T P m z p S hP hm ht hz hd hset1 hsetQ hS hm0

/-- **Unconditional existence of a white center `s ≤ p + 3 * (m * P)` where `rhCenter · 1` flips under `CenterPeriodic T P` alone from the verified paper**. -/
theorem exists_zero_diag_white_center_rhcenter_one_flip_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p s : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      s ≤ p + 3 * (m * P) ∧
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false ∧
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + s) 1 :=
  Rule30Paper.Paper.exists_zero_diag_white_center_rhcenter_one_flip_of_periodic T P hP hper m hm

/-- **Unconditional existence of a step `s ≤ p + 3 * (m * P)` where `maskparity · 0` flips under `CenterPeriodic T P` alone from the verified paper**. -/
theorem exists_zero_diag_maskparity_zero_flip_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p s : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      s ≤ p + 3 * (m * P) ∧
      Rule30UOR.Scale.maskparity (((z + (p + 1)) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + (p + 1)) + s) 0 :=
  Rule30Paper.Paper.exists_zero_diag_maskparity_zero_flip_of_periodic T P hP hper m hm

/-- **Unconditional existence of a step `s ≤ p + 3 * (m * P)` where `lhCenter · 1` flips under `CenterPeriodic T P` alone from the verified paper**. -/
theorem exists_zero_diag_lhcenter_one_flip_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m : Nat) (hm : 0 < m) :
    ∃ z p s : Nat, Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      s ≤ p + 3 * (m * P) ∧
      Rule30UOR.Interfaces.lhCenter (((z + (p + 1)) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.lhCenter ((z + (p + 1)) + s) 1 :=
  Rule30Paper.Paper.exists_zero_diag_lhcenter_one_flip_of_periodic T P hP hper m hm

/-- **1-step evolution of right-half column `1` driven by the center from the verified paper**. -/
theorem rhcenter_step_one_eq_center_xor_or_kit (t : Nat) :
    Rule30UOR.Interfaces.rhCenter (t + 1) 1 =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center t)
        (Rule30UOR.Interfaces.rhCenter t 1 || Rule30UOR.Interfaces.rhCenter t 2) :=
  Rule30Paper.Paper.rhcenter_step_one_eq_center_xor_or t

/-- **Black column-`1` OR-absorption law from the verified paper**. -/
theorem rhcenter_step_one_eq_not_center_of_black_one_kit (t : Nat)
    (hb : Rule30UOR.Interfaces.rhCenter t 1 = true) :
    Rule30UOR.Interfaces.rhCenter (t + 1) 1 = !Rule30UOR.Core.center t :=
  Rule30Paper.Paper.rhcenter_step_one_eq_not_center_of_black_one t hb

/-- **White-center + black-column-`1` persistence law from the verified paper**. -/
theorem rhcenter_step_one_eq_true_of_white_center_and_black_one_kit (t : Nat)
    (hc : Rule30UOR.Core.center t = false)
    (hb : Rule30UOR.Interfaces.rhCenter t 1 = true) :
    Rule30UOR.Interfaces.rhCenter (t + 1) 1 = true :=
  Rule30Paper.Paper.rhcenter_step_one_eq_true_of_white_center_and_black_one t hc hb

/-- **1-step column-`1` black pinning from `maskparity t 0 = true` from the verified paper**. -/
theorem rhcenter_step_one_eq_true_of_maskparity_zero_true_kit (t : Nat)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    Rule30UOR.Interfaces.rhCenter (t + 1) 1 = true :=
  Rule30Paper.Paper.rhcenter_step_one_eq_true_of_maskparity_zero_true t hm0

/-- **2-step column-`1` determination from `maskparity t 0 = true` from the verified paper**. -/
theorem rhcenter_step_two_eq_not_center_of_maskparity_zero_true_kit (t : Nat)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    Rule30UOR.Interfaces.rhCenter (t + 2) 1 = !Rule30UOR.Core.center (t + 1) :=
  Rule30Paper.Paper.rhcenter_step_two_eq_not_center_of_maskparity_zero_true t hm0

/-- **Unconditional 1-step forward propagation of right-half column-`1` agreement across a black column-`1` cell from the verified paper**. -/
theorem periodic_rhcenter_step_one_eq_of_black_one_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hbQ : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = true)
    (hb0 : Rule30UOR.Interfaces.rhCenter t 1 = true) :
    Rule30UOR.Interfaces.rhCenter ((t + 1) + m * P) 1 =
      Rule30UOR.Interfaces.rhCenter (t + 1) 1 :=
  Rule30Paper.Paper.periodic_rhcenter_step_one_eq_of_black_one T P hP hper m t ht hbQ hb0

/-- **Unconditional 1-step forward propagation of left-half column-`-1` agreement across a black column-`1` cell from the verified paper**. -/
theorem periodic_lhcenter_step_one_eq_of_black_one_kit (T P : Nat) (hP : 0 < P)
    (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hbQ : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = true)
    (hb0 : Rule30UOR.Interfaces.rhCenter t 1 = true) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + m * P) 1 =
      Rule30UOR.Interfaces.lhCenter (t + 1) 1 :=
  Rule30Paper.Paper.periodic_lhcenter_step_one_eq_of_black_one T P hP hper m t ht hbQ hb0

/-- **2-step forward propagation of left-half column-`-1` agreement from `maskparity · 0 = true` at time `t` alone from the verified paper**. -/
theorem periodic_lhcenter_step_one_and_two_eq_of_maskparity_zero_true_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hmQ : Rule30UOR.Scale.maskparity (t + m * P) 0 = true)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + m * P) 1 =
        Rule30UOR.Interfaces.lhCenter (t + 1) 1 ∧
      Rule30UOR.Interfaces.lhCenter ((t + 2) + m * P) 1 =
        Rule30UOR.Interfaces.lhCenter (t + 2) 1 :=
  Rule30Paper.Paper.periodic_lhcenter_step_one_and_two_eq_of_maskparity_zero_true T P hP hper m t ht hmQ hm0

/-- **Producing full left-band agreement `LhBandAgree t (m * P) 0 (S + 1)` from OR-agreement conditioned solely on white next centers from the verified paper**. -/
theorem periodic_lhbandagree_zero_of_white_center_rhoragree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h0 : Rule30UOR.Core.center t = false →
      Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hor : ∀ s : Nat, s < S →
      Rule30UOR.Core.center (t + (s + 1)) = false →
        (Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 ||
          Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 2) =
          (Rule30UOR.Interfaces.rhCenter (t + s) 1 ||
            Rule30UOR.Interfaces.rhCenter (t + s) 2)) :
    Rule30UOR.Interfaces.LhBandAgree t (m * P) 0 (S + 1) :=
  Rule30Paper.Paper.periodic_lhbandagree_zero_of_white_center_rhoragree_one T P hP hper m t S ht h0 hor

/-- **Scale-free universal-in-`m, P` refutation of `CenterPeriodic T P` from white-center-conditioned OR-agreement at any doubling zero diagonal `z = t - (p + 1)` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhoragree_one_doubles_kit
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag (t - (p + 1)))
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) (t - (p + 1)))
    (hset1 : Rule30UOR.Interfaces.SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : Rule30UOR.Interfaces.SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h0 : Rule30UOR.Core.center t = false →
      Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (hor : ∀ s : Nat, s < S →
      Rule30UOR.Core.center (t + (s + 1)) = false →
        (Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 ||
          Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 2) =
          (Rule30UOR.Interfaces.rhCenter (t + s) 1 ||
            Rule30UOR.Interfaces.rhCenter (t + s) 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhoragree_one_doubles T P m t p S hP hm ht hz hd hset1 hsetQ hS h0 hor

/-- **White column-`1` linearization law from the verified paper**. -/
theorem rhcenter_step_one_eq_center_xor_two_of_white_one_kit (t : Nat)
    (hw : Rule30UOR.Interfaces.rhCenter t 1 = false) :
    Rule30UOR.Interfaces.rhCenter (t + 1) 1 =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center t) (Rule30UOR.Interfaces.rhCenter t 2) :=
  Rule30Paper.Paper.rhcenter_step_one_eq_center_xor_two_of_white_one t hw

/-- **1-step forward propagation of right-half column-`1` agreement across a white column-`1` cell from column-`2` agreement from the verified paper**. -/
theorem periodic_rhcenter_step_one_eq_of_white_one_and_two_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hwQ : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = false)
    (hw0 : Rule30UOR.Interfaces.rhCenter t 1 = false)
    (h2 : Rule30UOR.Interfaces.rhCenter (t + m * P) 2 = Rule30UOR.Interfaces.rhCenter t 2) :
    Rule30UOR.Interfaces.rhCenter ((t + 1) + m * P) 1 = Rule30UOR.Interfaces.rhCenter (t + 1) 1 :=
  Rule30Paper.Paper.periodic_rhcenter_step_one_eq_of_white_one_and_two_eq T P hP hper m t ht hwQ hw0 h2

/-- **Unified 1-step forward propagation of left-half column-`-1` agreement requiring column `2` only when `center (t + 1) = false` and `rhCenter t 1 = false` from the verified paper**. -/
theorem periodic_lhcenter_step_one_eq_of_white_or_black_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (h1 : Rule30UOR.Interfaces.rhCenter (t + m * P) 1 = Rule30UOR.Interfaces.rhCenter t 1)
    (h2 : Rule30UOR.Core.center (t + 1) = false →
      Rule30UOR.Interfaces.rhCenter t 1 = false →
        Rule30UOR.Interfaces.rhCenter (t + m * P) 2 = Rule30UOR.Interfaces.rhCenter t 2) :
    Rule30UOR.Interfaces.lhCenter ((t + 1) + m * P) 1 = Rule30UOR.Interfaces.lhCenter (t + 1) 1 :=
  Rule30Paper.Paper.periodic_lhcenter_step_one_eq_of_white_or_black_one T P hP hper m t ht h1 h2

/-- **Unconditional identification of the dyadic left wing `cell t (negpow k)` with `lhCenter t (twopow k)` from the verified paper**. -/
theorem cell_negpow_eq_lhcenter_twopow_kit (t k : Nat) :
    Rule30UOR.Core.cell t (Rule30UOR.Scale.negpow k) =
      Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.cell_negpow_eq_lhcenter_twopow t k

/-- **Unconditional dyadic scale identity at the center in terms of `lhCenter` from the verified paper**. -/
theorem scale_center_lhcenter_kit (t k : Nat) :
    Rule30UOR.Core.center (t + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor (Rule30UOR.Core.center t)
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k)))
        (Rule30UOR.Scale.response t k) :=
  Rule30Paper.Paper.scale_center_lhcenter t k

/-- **Unconditional `m * P`-defect lock between `lhCenter · (2^k)` and `response · k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_lhcenter_twopow_defect_eq_response_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.lhCenter (t + m * P) (Rule30UOR.Core.twopow k))
      (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.response (t + m * P) k)
        (Rule30UOR.Scale.response t k) :=
  Rule30Paper.Paper.periodic_lhcenter_twopow_defect_eq_response_defect T P hP hper m t k ht

/-- **Unconditional `m * P`-defect decomposition of `maskparity · k` into `lhCenter · (2^k)` and `leftresponse · k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_maskparity_defect_eq_lhcenter_twopow_xor_leftresponse_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (t + m * P) k)
      (Rule30UOR.Scale.maskparity t k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter (t + m * P) (Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (t + m * P) k)
          (Rule30UOR.Scale.leftresponse t k)) :=
  Rule30Paper.Paper.periodic_maskparity_defect_eq_lhcenter_twopow_xor_leftresponse_defect T P hP hper m t k ht

/-- **Inside-the-cone `m * P`-invariance of `response · k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_response_eq_cone_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hcone : t + m * P < Rule30UOR.Core.twopow k) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k :=
  Rule30Paper.Paper.periodic_response_eq_cone_mul T P hP hper m t k ht hcone

/-- **Inside-the-cone `m * P`-defect lock between `maskparity · k` and `leftresponse · k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_maskparity_defect_eq_leftresponse_defect_cone_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hcone : t + m * P < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (t + m * P) k)
      (Rule30UOR.Scale.maskparity t k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) :=
  Rule30Paper.Paper.periodic_maskparity_defect_eq_leftresponse_defect_cone_mul T P hP hper m t k ht hcone

/-- **Unconditional `m * P`-antiperiodicity of `response · k` at the left light-cone boundary `t + m * P = 2^k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_response_flip_at_twopow_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (hm : 0 < m) (ht : T ≤ t) (heq : t + m * P = Rule30UOR.Core.twopow k) :
    Rule30UOR.Scale.response (t + m * P) k = !Rule30UOR.Scale.response t k :=
  Rule30Paper.Paper.periodic_response_flip_at_twopow_mul T P hP hper m t k hm ht heq

/-- **Unconditional `m * P`-defect inversion between `maskparity · k` and `leftresponse · k` at the left light-cone boundary `t + m * P = 2^k` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_maskparity_defect_eq_not_leftresponse_defect_at_twopow_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (hm : 0 < m) (ht : T ≤ t) (heq : t + m * P = Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (t + m * P) k)
      (Rule30UOR.Scale.maskparity t k) =
      !Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) :=
  Rule30Paper.Paper.periodic_maskparity_defect_eq_not_leftresponse_defect_at_twopow_mul T P hP hper m t k hm ht heq

/-- **Exact pointwise equality of `m * P`-defects between `lhCenter · 1` and `maskparity · 0` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_lhcenter_one_defect_eq_maskparity_zero_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
      (Rule30UOR.Interfaces.lhCenter t 1) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity (t + m * P) 0)
        (Rule30UOR.Scale.maskparity t 0) :=
  Rule30Paper.Paper.periodic_lhcenter_one_defect_eq_maskparity_zero_defect T P hP hper m t ht

/-- **Converse pointwise equivalence: `lhCenter (t + m * P) 1 = lhCenter t 1 → maskparity (t + m * P) 0 = maskparity t 0` under `CenterPeriodic T P` from the verified paper**. -/
theorem periodic_maskparity_zero_eq_of_lhcenter_one_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hlh : Rule30UOR.Interfaces.lhCenter (t + m * P) 1 = Rule30UOR.Interfaces.lhCenter t 1) :
    Rule30UOR.Scale.maskparity (t + m * P) 0 = Rule30UOR.Scale.maskparity t 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_eq_of_lhcenter_one_eq T P hP hper m t ht hlh

/-- **Unconditional dyadic jump of the `lhCenter · 1` period-shift defect equals the 1-step difference of the scale-`k` `maskparity · k` period-shift defect from the verified paper**. -/
theorem periodic_lhcenter_one_dyadic_jump_defect_eq_maskparity_step_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter ((t + Rule30UOR.Core.twopow k) + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter t 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity ((t + 1) + m * P) k)
          (Rule30UOR.Scale.maskparity (t + 1) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.maskparity (t + m * P) k)
          (Rule30UOR.Scale.maskparity t k)) :=
  Rule30Paper.Paper.periodic_lhcenter_one_dyadic_jump_defect_eq_maskparity_step_defect T P hP hper m t k ht

/-- **Inside-the-cone dyadic jump of the `lhCenter · 1` period-shift defect equals the 1-step difference of the `leftresponse · k` period-shift defect from the verified paper**. -/
theorem periodic_lhcenter_one_dyadic_jump_defect_eq_leftresponse_step_defect_cone_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hcone : (t + 1) + m * P < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter ((t + Rule30UOR.Core.twopow k) + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter t 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k)
          (Rule30UOR.Scale.leftresponse (t + 1) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (t + m * P) k)
          (Rule30UOR.Scale.leftresponse t k)) :=
  Rule30Paper.Paper.periodic_lhcenter_one_dyadic_jump_defect_eq_leftresponse_step_defect_cone_mul T P hP hper m t k ht hcone

/-- **Unconditional inversion of the `lhCenter · 1` dyadic jump defect at the left light-cone boundary `(t + 1) + m * P = 2^k` from the verified paper**. -/
theorem periodic_lhcenter_one_dyadic_jump_defect_eq_not_leftresponse_step_defect_at_twopow_mul_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (hm : 0 < m) (ht : T ≤ t) (heq : (t + 1) + m * P = Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter ((t + Rule30UOR.Core.twopow k) + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter t 1)) =
      !Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k)
          (Rule30UOR.Scale.leftresponse (t + 1) k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (t + m * P) k)
          (Rule30UOR.Scale.leftresponse t k)) :=
  Rule30Paper.Paper.periodic_lhcenter_one_dyadic_jump_defect_eq_not_leftresponse_step_defect_at_twopow_mul T P hP hper m t k hm ht heq

/-- **General unconditional decomposition of the `lhCenter · 1` dyadic jump defect into the 1-step difference of `lhCenter · (2^k)` and the 1-step difference of `leftresponse · k` from the verified paper**. -/
theorem periodic_lhcenter_one_dyadic_jump_defect_eq_lhcenter_twopow_step_xor_leftresponse_step_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter ((t + Rule30UOR.Core.twopow k) + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) 1))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (t + m * P) 1)
        (Rule30UOR.Interfaces.lhCenter t 1)) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter ((t + 1) + m * P) (Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.lhCenter (t + 1) (Rule30UOR.Core.twopow k)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Interfaces.lhCenter (t + m * P) (Rule30UOR.Core.twopow k))
            (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k))))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k)
            (Rule30UOR.Scale.leftresponse (t + 1) k))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (t + m * P) k)
            (Rule30UOR.Scale.leftresponse t k))) :=
  Rule30Paper.Paper.periodic_lhcenter_one_dyadic_jump_defect_eq_lhcenter_twopow_step_xor_leftresponse_step_defect T P hP hper m t k ht

/-- **Unconditional dyadic left-wing vanishing along any settled zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_of_zero_diag_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (z + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) = false :=
  Rule30Paper.Paper.lhcenter_twopow_of_zero_diag z k hz hset

/-- **Unconditional dyadic left-wing blackness two diagonals after any settled zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_after_zero_diag_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((z + 2) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) = true :=
  Rule30Paper.Paper.lhcenter_twopow_after_zero_diag z k hz hset

/-- **Unconditional outside-the-cone collapse of the dyadic scale identity along any settled zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem scale_center_at_zero_diag_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (z + Rule30UOR.Core.twopow k))
        (Rule30UOR.Scale.response (z + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.scale_center_at_zero_diag z k hz hset

/-- **Unconditional outside-the-cone inversion of the dyadic scale identity two diagonals after any settled zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem scale_center_after_zero_diag_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.center (((z + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Core.twopow k) =
      !Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + 2) + Rule30UOR.Core.twopow k))
        (Rule30UOR.Scale.response ((z + 2) + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.scale_center_after_zero_diag z k hz hset

/-- **Unconditional outside-the-cone center-lag formula for `response (z + 2^k) k` along any settled zero diagonal `z` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_response_at_zero_diag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.response (z + Rule30UOR.Core.twopow k) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center (z + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.periodic_response_at_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional outside-the-cone inverted center-lag formula for `response ((z + 2) + 2^k) k` two diagonals after any settled zero diagonal `z` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_response_after_zero_diag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ (z + 2) + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.response ((z + 2) + Rule30UOR.Core.twopow k) k =
      !Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (((z + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center ((z + 2) + Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.periodic_response_after_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional `m * P`-defect readout of `response` at `z + 2^k` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_response_defect_at_zero_diag_eq_lhcenter_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((z + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.response (z + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Interfaces.lhCenter ((z + Rule30UOR.Core.twopow k) + m * P) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_response_defect_at_zero_diag_eq_lhcenter_twopow T P hP hper m z k ht hz hset

/-- **Unconditional `m * P`-defect readout of `response` at `(z + 2) + 2^k` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_response_defect_after_zero_diag_eq_not_lhcenter_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ (z + 2) + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response (((z + 2) + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.response ((z + 2) + Rule30UOR.Core.twopow k) k) =
      !Rule30UOR.Interfaces.lhCenter (((z + 2) + Rule30UOR.Core.twopow k) + m * P) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.periodic_response_defect_after_zero_diag_eq_not_lhcenter_twopow T P hP hper m z k ht hz hset

/-- **Outside-the-cone `m * P`-invariance of `response · k` under `LhBandAgree` covering `2^k` from the verified paper**. -/
theorem periodic_response_eq_of_lhbandagree_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k p0 L : Nat) (ht : T ≤ t)
    (hp0 : p0 ≤ Rule30UOR.Core.twopow k) (hL : Rule30UOR.Core.twopow k ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t (m * P) p0 L) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k :=
  Rule30Paper.Paper.periodic_response_eq_of_lhbandagree_twopow T P hP hper m t k p0 L ht hp0 hL hband

/-- **Outside-the-cone `m * P`-defect lock between `maskparity · k` and `leftresponse · k` under `LhBandAgree` covering `2^k` from the verified paper**. -/
theorem periodic_maskparity_defect_eq_leftresponse_defect_of_lhbandagree_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k p0 L : Nat) (ht : T ≤ t)
    (hp0 : p0 ≤ Rule30UOR.Core.twopow k) (hL : Rule30UOR.Core.twopow k ≤ p0 + L)
    (hband : Rule30UOR.Interfaces.LhBandAgree t (m * P) p0 L) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (t + m * P) k)
      (Rule30UOR.Scale.maskparity t k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) :=
  Rule30Paper.Paper.periodic_maskparity_defect_eq_leftresponse_defect_of_lhbandagree_twopow T P hP hper m t k p0 L ht hp0 hL hband

/-- **Producing outside-the-cone `response (t + m * P) k = response t k` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_response_eq_of_white_center_rhcenter_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k :=
  Rule30Paper.Paper.periodic_response_eq_of_white_center_rhcenter_one_twopow T P hP hper m t k S ht hS hw

/-- **Producing outside-the-cone `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhcenter_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (t + m * P) k)
      (Rule30UOR.Scale.maskparity t k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) :=
  Rule30Paper.Paper.periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhcenter_one_twopow T P hP hper m t k S ht hS hw

/-- **Universal unconditional dyadic coboundary of `response` for every `t, k ∈ ℕ` from the verified paper**. -/
theorem response_coboundary_eq_lhcenter_twopow_kit (t k : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Scale.response t (k + 1)) (Rule30UOR.Scale.response t k))
      (Rule30UOR.Scale.response (t + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.response_coboundary_eq_lhcenter_twopow t k

/-- **Universal unconditional dyadic coboundary of `leftresponse` for every `t, k ∈ ℕ` from the verified paper**. -/
theorem leftresponse_coboundary_eq_lhcenter_twopow_kit (t k : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Scale.leftresponse t (k + 1)) (Rule30UOR.Scale.leftresponse t k))
      (Rule30UOR.Scale.leftresponse (t + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow k)))
        (Rule30UOR.Interfaces.lhCenter t (Rule30UOR.Core.twopow (k + 1))) :=
  Rule30Paper.Paper.leftresponse_coboundary_eq_lhcenter_twopow t k

/-- **Inside-the-cone readout of `lhCenter (t + 2^k) (2^k)` as the `response` dyadic coboundary dropping `t ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_eq_response_coboundary_cone_kit (t k : Nat)
    (ht : t < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor (Rule30UOR.Scale.response t (k + 1)) (Rule30UOR.Scale.response t k))
        (Rule30UOR.Scale.response (t + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.lhcenter_twopow_eq_response_coboundary_cone t k ht

/-- **Inside-the-cone readout of `lhCenter (t + 2^k) (2^k)` as the pure left-half `leftresponse` dyadic coboundary dropping `t ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_eq_leftresponse_coboundary_cone_kit (t k : Nat)
    (ht : t < Rule30UOR.Core.twopow k) :
    Rule30UOR.Interfaces.lhCenter (t + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor (Rule30UOR.Scale.leftresponse t (k + 1)) (Rule30UOR.Scale.leftresponse t k))
        (Rule30UOR.Scale.leftresponse (t + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.lhcenter_twopow_eq_leftresponse_coboundary_cone t k ht

/-- **Inside-the-cone vanishing of the `leftresponse` dyadic coboundary along any settled zero diagonal `z` dropping `z ≤ k` from the verified paper**. -/
theorem leftresponse_coboundary_at_zero_diag_cone_kit (z k : Nat)
    (hcone : z < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Scale.leftresponse z (k + 1)) (Rule30UOR.Scale.leftresponse z k))
      (Rule30UOR.Scale.leftresponse (z + Rule30UOR.Core.twopow k) k) = false :=
  Rule30Paper.Paper.leftresponse_coboundary_at_zero_diag_cone z k hcone hz hset

/-- **Inside-the-cone non-vanishing (`= true`) of the `leftresponse` dyadic coboundary two diagonals after any settled zero diagonal `z` dropping `z + 2 ≤ k` from the verified paper**. -/
theorem leftresponse_coboundary_after_zero_diag_cone_kit (z k : Nat)
    (hcone : z + 2 < Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Scale.leftresponse (z + 2) (k + 1)) (Rule30UOR.Scale.leftresponse (z + 2) k))
      (Rule30UOR.Scale.leftresponse ((z + 2) + Rule30UOR.Core.twopow k) k) = true :=
  Rule30Paper.Paper.leftresponse_coboundary_after_zero_diag_cone z k hcone hz hset

/-- **Unconditional dyadic left-wing scale-step flip along any settled doubling diagonal `z + 1` without `z ≤ k` or `z < 2^k` from the verified paper**. -/
theorem lhcenter_twopow_succ_antiperiodic_of_doubles_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((z + 1) + Rule30UOR.Core.twopow (k + 1)) (Rule30UOR.Core.twopow (k + 1)) =
      !Rule30UOR.Interfaces.lhCenter ((z + 1) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_twopow_succ_antiperiodic_of_doubles z k hz hd hset

/-- **Unconditional outside-the-cone formula for `maskparity (z + 2^k) k` along any settled zero diagonal `z` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_maskparity_at_zero_diag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.maskparity (z + Rule30UOR.Core.twopow k) k =
      Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse (z + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (z + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.periodic_maskparity_at_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional outside-the-cone inverted formula for `maskparity ((z + 2) + 2^k) k` two diagonals after any settled zero diagonal `z` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_maskparity_after_zero_diag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ (z + 2) + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.maskparity ((z + 2) + Rule30UOR.Core.twopow k) k =
      !Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse ((z + 2) + Rule30UOR.Core.twopow k) k)
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (((z + 2) + Rule30UOR.Core.twopow k) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center ((z + 2) + Rule30UOR.Core.twopow k))) :=
  Rule30Paper.Paper.periodic_maskparity_after_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional `m * P`-defect law for `maskparity` at `z + 2^k` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_maskparity_defect_at_zero_diag_eq_lhcenter_twopow_xor_leftresponse_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity ((z + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.maskparity (z + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter ((z + Rule30UOR.Core.twopow k) + m * P) (Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse ((z + Rule30UOR.Core.twopow k) + m * P) k)
          (Rule30UOR.Scale.leftresponse (z + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_maskparity_defect_at_zero_diag_eq_lhcenter_twopow_xor_leftresponse_defect T P hP hper m z k ht hz hset

/-- **Unconditional `m * P`-defect law for `maskparity` at `(z + 2) + 2^k` under `CenterPeriodic T P` without `z ≤ k` from the verified paper**. -/
theorem periodic_maskparity_defect_after_zero_diag_eq_not_lhcenter_twopow_xor_leftresponse_defect_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ (z + 2) + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.maskparity (((z + 2) + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.maskparity ((z + 2) + Rule30UOR.Core.twopow k) k) =
      !Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.lhCenter (((z + 2) + Rule30UOR.Core.twopow k) + m * P) (Rule30UOR.Core.twopow k))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Scale.leftresponse (((z + 2) + Rule30UOR.Core.twopow k) + m * P) k)
          (Rule30UOR.Scale.leftresponse ((z + 2) + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_maskparity_defect_after_zero_diag_eq_not_lhcenter_twopow_xor_leftresponse_defect T P hP hper m z k ht hz hset

/-- **Unconditional shift-`2` (`m * P = 2`) antiperiodicity of `response · k` at `z + 2^k` for every zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem periodic_response_flip_at_zero_diag_step_two_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (hmP : m * P = 2) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.response ((z + Rule30UOR.Core.twopow k) + m * P) k =
      !Rule30UOR.Scale.response (z + Rule30UOR.Core.twopow k) k :=
  Rule30Paper.Paper.periodic_response_flip_at_zero_diag_step_two T P hP hper m z k hmP ht hz hset0 hset2

/-- **Unconditional `m * P`-antiperiodicity of `response · k` between any two settled zero diagonals separated by `z1 + m * P = z2 + 2` from the verified paper**. -/
theorem periodic_response_flip_of_two_zero_diags_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k : Nat) (ht : T ≤ z1 + Rule30UOR.Core.twopow k)
    (hshift : z1 + m * P = z2 + 2)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag z1)
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag z2)
    (hset1 : Rule30UOR.Interfaces.SettledBy z1 (z1 + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z2 + 2) ((z2 + 2) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.response ((z1 + Rule30UOR.Core.twopow k) + m * P) k =
      !Rule30UOR.Scale.response (z1 + Rule30UOR.Core.twopow k) k :=
  Rule30Paper.Paper.periodic_response_flip_of_two_zero_diags T P hP hper m z1 z2 k ht hshift hz1 hz2 hset1 hset2

/-- **Unconditional `m * P`-equality of `response · k` between any two settled zero diagonals separated by `z1 + m * P = z2` from the verified paper**. -/
theorem periodic_response_eq_of_two_zero_diags_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k : Nat) (ht : T ≤ z1 + Rule30UOR.Core.twopow k)
    (hshift : z1 + m * P = z2)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag z1)
    (hz2 : Rule30UOR.ZeroDiagonals.IsZeroDiag z2)
    (hset1 : Rule30UOR.Interfaces.SettledBy z1 (z1 + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy z2 (z2 + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Scale.response ((z1 + Rule30UOR.Core.twopow k) + m * P) k =
      Rule30UOR.Scale.response (z1 + Rule30UOR.Core.twopow k) k :=
  Rule30Paper.Paper.periodic_response_eq_of_two_zero_diags T P hP hper m z1 z2 k ht hshift hz1 hz2 hset1 hset2

/-- **Universal-in-`Q` inside-the-cone late `leftresponse` shift-defect law dropping `d + Q ≤ k` from the verified paper**. -/
theorem late_leftresponse_defect_eq_lhcenter_twopow_defect_cone_kit
    (Q d k : Nat) (hcone : d + Q < Rule30UOR.Core.twopow k) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.leftresponse ((d + Rule30UOR.Core.twopow k) + Q) k)
      (Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow k) k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Interfaces.lhCenter ((d + Rule30UOR.Core.twopow k) + Q) (Rule30UOR.Core.twopow k))
          (Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)))
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (d + Q) (k + 1))
            (Rule30UOR.Scale.leftresponse d (k + 1)))
          (Rule30UOR.Core.bxor
            (Rule30UOR.Scale.leftresponse (d + Q) k)
            (Rule30UOR.Scale.leftresponse d k))) :=
  Rule30Paper.Paper.late_leftresponse_defect_eq_lhcenter_twopow_defect_cone Q d k hcone

/-- **Exact recurrence of `maskcount t (n + 1)` via `maskparity (t + n) 0` from the verified paper**. -/
theorem maskcount_succ_eq_xor_maskparity_zero_kit (t n : Nat) :
    Rule30UOR.Scale.maskcount t (n + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Scale.maskcount t n) (Rule30UOR.Scale.maskparity (t + n) 0) :=
  Rule30Paper.Paper.maskcount_succ_eq_xor_maskparity_zero t n

/-- **Universal-in-`Q` determination of `maskcount · n` from first-bit `maskparity · 0` agreement from the verified paper**. -/
theorem maskcount_eq_of_maskparity_zero_agree_kit (t Q n : Nat)
    (hm : ∀ s : Nat, s < n →
      Rule30UOR.Scale.maskparity ((t + s) + Q) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.maskcount (t + Q) n = Rule30UOR.Scale.maskcount t n :=
  Rule30Paper.Paper.maskcount_eq_of_maskparity_zero_agree t Q n hm

/-- **Universal-in-`Q` determination of `maskparity · k` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem maskparity_eq_of_maskparity_zero_agree_kit (t Q k S : Nat)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hm : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + Q) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.maskparity (t + Q) k = Rule30UOR.Scale.maskparity t k :=
  Rule30Paper.Paper.maskparity_eq_of_maskparity_zero_agree t Q k S hS hm

/-- **Producing `maskparity (t + m * P) k = maskparity t k` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_maskparity_eq_of_white_center_rhcenter_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    Rule30UOR.Scale.maskparity (t + m * P) k = Rule30UOR.Scale.maskparity t k :=
  Rule30Paper.Paper.periodic_maskparity_eq_of_white_center_rhcenter_one_twopow T P hP hper m t k S ht hS hw

/-- **Producing `leftresponse (t + m * P) k = leftresponse t k` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_leftresponse_eq_of_white_center_rhcenter_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    Rule30UOR.Scale.leftresponse (t + m * P) k = Rule30UOR.Scale.leftresponse t k :=
  Rule30Paper.Paper.periodic_leftresponse_eq_of_white_center_rhcenter_one_twopow T P hP hper m t k S ht hS hw

/-- **Producing `leftresponse (t + m * P) k = leftresponse t k` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_leftresponse_eq_of_maskparity_zero_agree_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hm : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.leftresponse (t + m * P) k = Rule30UOR.Scale.leftresponse t k :=
  Rule30Paper.Paper.periodic_leftresponse_eq_of_maskparity_zero_agree_twopow T P hP hper m t k S ht hS hm

/-- **Producing `response (t + m * P) k = response t k` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_response_eq_of_maskparity_zero_agree_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hm : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k :=
  Rule30Paper.Paper.periodic_response_eq_of_maskparity_zero_agree_twopow T P hP hper m t k S ht hS hm

/-- **Producing `leftresponse (t + m * P) k = leftresponse t k` from `LhColAgree t (m * P) 1 S` over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_leftresponse_eq_of_lhcolagree_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S) :
    Rule30UOR.Scale.leftresponse (t + m * P) k = Rule30UOR.Scale.leftresponse t k :=
  Rule30Paper.Paper.periodic_leftresponse_eq_of_lhcolagree_one_twopow T P hP hper m t k S ht hS hlh

/-- **Producing `maskparity (t + m * P) k = maskparity t k` from `LhColAgree t (m * P) 1 S` over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_maskparity_eq_of_lhcolagree_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S) :
    Rule30UOR.Scale.maskparity (t + m * P) k = Rule30UOR.Scale.maskparity t k :=
  Rule30Paper.Paper.periodic_maskparity_eq_of_lhcolagree_one_twopow T P hP hper m t k S ht hS hlh

/-- **Producing `response (t + m * P) k = response t k` from `LhColAgree t (m * P) 1 S` over `2^k ≤ S + 1` from the verified paper**. -/
theorem periodic_response_eq_of_lhcolagree_one_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k :=
  Rule30Paper.Paper.periodic_response_eq_of_lhcolagree_one_twopow T P hP hper m t k S ht hS hlh

/-- **Unconditional identification of `lhCenter (d + 2^k) (2^k)` with `ldiag d (d + 2^k)` without `d ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_eq_ldiag_kit (d k : Nat) :
    Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.ldiag d (d + Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_twopow_eq_ldiag d k

/-- **Settled dyadic left wing equals the zero-state center `zcenter d` from the verified paper**. -/
theorem lhcenter_twopow_settled_eq_zcenter_kit (d k : Nat)
    (hk : d ≤ k) (hset : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.ZCenterEq d
      (Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k)) :=
  Rule30Paper.Paper.lhcenter_twopow_settled_eq_zcenter d k hk hset

/-- **Scale-step invariance of the settled dyadic left wing `lhCenter (d + 2^k) (2^k)` from the verified paper**. -/
theorem lhcenter_twopow_settled_scale_invariant_kit (d k : Nat)
    (hk : d ≤ k) (hset : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow (k + 1)) (Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_twopow_settled_scale_invariant d k hk hset

/-- **Unconditional scale-step invariance of `lhCenter (d + 2^k) (2^k)` below any dyadic doubling threshold `z` without `d ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_succ_periodic_of_doubles_le_kit (z d k : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow (k + 1)) (Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_twopow_succ_periodic_of_doubles_le z d k hd hdz hset

/-- **Unconditional dyadic left-wing scale-step flip along the reset diagonal `z + 3` without `z ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_reset_succ_antiperiodic_of_doubles_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Interfaces.lhCenter ((z + 3) + Rule30UOR.Core.twopow (k + 1)) (Rule30UOR.Core.twopow (k + 1)) =
      !Rule30UOR.Interfaces.lhCenter ((z + 3) + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.lhcenter_twopow_reset_succ_antiperiodic_of_doubles z k hz hd hset

/-- **Unconditional identification of `lhCenter (d + 2^k) (2^k)` with the late Rule-60 scale increment without `d ≤ k` from the verified paper**. -/
theorem lhcenter_twopow_eq_late_scale_center_kit (d k : Nat) :
    Rule30UOR.Interfaces.lhCenter (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.bxor
          (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow k)))
        (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.lhcenter_twopow_eq_late_scale_center d k

/-- **Unconditional scale-step invariance of the late Rule-60 scale increment below `z` (`DoublesAt (twopow k) z`) without `d ≤ k` from the verified paper**. -/
theorem late_scale_center_periodic_of_doubles_le_kit (z d k : Nat)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z)
    (hset : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow (k + 2)))
        (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow (k + 1))))
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow (k + 1)) (k + 1)) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Core.twopow k)))
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.late_scale_center_periodic_of_doubles_le z d k hd hdz hset

/-- **Unconditional scale-step flip of the late Rule-60 scale increment along `z + 1` at a dyadic doubling zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem late_scale_center_antiperiodic_of_doubles_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + 1) + Rule30UOR.Core.twopow (k + 2)))
        (Rule30UOR.Core.center ((z + 1) + Rule30UOR.Core.twopow (k + 1))))
      (Rule30UOR.Scale.response ((z + 1) + Rule30UOR.Core.twopow (k + 1)) (k + 1)) =
    !Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + 1) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.center ((z + 1) + Rule30UOR.Core.twopow k)))
      (Rule30UOR.Scale.response ((z + 1) + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.late_scale_center_antiperiodic_of_doubles z k hz hd hset

/-- **Unconditional scale-step flip of the late Rule-60 scale increment along `z + 3` at a dyadic doubling zero diagonal `z` without `z ≤ k` from the verified paper**. -/
theorem late_scale_center_reset_antiperiodic_of_doubles_kit (z k : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hset : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + 3) + Rule30UOR.Core.twopow (k + 2)))
        (Rule30UOR.Core.center ((z + 3) + Rule30UOR.Core.twopow (k + 1))))
      (Rule30UOR.Scale.response ((z + 3) + Rule30UOR.Core.twopow (k + 1)) (k + 1)) =
    !Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Core.center ((z + 3) + Rule30UOR.Core.twopow (k + 1)))
        (Rule30UOR.Core.center ((z + 3) + Rule30UOR.Core.twopow k)))
      (Rule30UOR.Scale.response ((z + 3) + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.late_scale_center_reset_antiperiodic_of_doubles z k hz hd hset

/-- **Scale-step invariance of the late `response` shift defect below `z` (`DoublesAt (twopow k) z`) without `z ≤ k` from the verified paper**. -/
theorem periodic_late_response_defect_eq_of_doubles_le_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d + m * P ≤ z) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (d + m * P) ((d + m * P) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow (k + 1)) (k + 1)) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_late_response_defect_eq_of_doubles_le T P hP hper m d z k hd hdz ht hset0 hset1

/-- **Scale-step flip of the late `response` shift defect across a dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`) without `z ≤ k` or `DoublesAt (m * P) z` from the verified paper**. -/
theorem periodic_late_response_defect_flip_of_doubles_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow (k + 1)) (k + 1)) =
    !Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_late_response_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset1

/-- **Scale-step `response` inversion at `k + 1` from scale-`k` agreement across a dyadic doubling zero diagonal `z` from the verified paper**. -/
theorem periodic_late_response_flip_of_doubles_and_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hreq : Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow k) + m * P) k =
      Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :
    Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1) =
      !Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow (k + 1)) (k + 1) :=
  Rule30Paper.Paper.periodic_late_response_flip_of_doubles_and_eq T P hP hper m d z k hz hd hdz hdm ht hset0 hset1 hreq

/-- **Refuting `CenterPeriodic` at `t + m * P = 2^k` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_at_twopow_kit
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hcone : t + m * P = Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter (t + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_at_twopow T P m t k S hP hm ht hcone hS hw

/-- **Refuting `CenterPeriodic` at `t + m * P = 2^k` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_at_twopow_kit
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hcone : t + m * P = Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity (t + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_at_twopow T P m t k S hP hm ht hcone hS hmp

/-- **Refuting `CenterPeriodic` at `z + 2^k` for `m * P = 2` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_at_zero_diag_step_two_kit
    (T P m z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((z + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((z + Rule30UOR.Core.twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_at_zero_diag_step_two T P m z k S hP hz hm ht hset0 hset2 hS hw

/-- **Refuting `CenterPeriodic` at `z + 2^k` for `m * P = 2` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_at_zero_diag_step_two_kit
    (T P m z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + Rule30UOR.Core.twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_at_zero_diag_step_two T P m z k S hP hz hm ht hset0 hset2 hS hmp

/-- **Refuting `CenterPeriodic` at `z + 2^k` from two zero diagonals and white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_of_two_zero_diags_kit
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((z + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((z + Rule30UOR.Core.twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_of_two_zero_diags T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hw

/-- **Refuting `CenterPeriodic` at `z + 2^k` from two zero diagonals and first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_of_two_zero_diags_kit
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + Rule30UOR.Core.twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_of_two_zero_diags T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hmp

/-- **Two-scale refutation of `CenterPeriodic` across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`) from white-center column-`1` agreement without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_scale_step_doubles_kit
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hS0 : Rule30UOR.Core.twopow k ≤ S0 + 1) (hS1 : Rule30UOR.Core.twopow (k + 1) ≤ S1 + 1)
    (hw0 : ∀ s : Nat, s ≤ S0 →
      Rule30UOR.Core.center ((d + Rule30UOR.Core.twopow k) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((d + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((d + Rule30UOR.Core.twopow k) + s) 1)
    (hw1 : ∀ s : Nat, s ≤ S1 →
      Rule30UOR.Core.center ((d + Rule30UOR.Core.twopow (k + 1)) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((d + Rule30UOR.Core.twopow (k + 1)) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((d + Rule30UOR.Core.twopow (k + 1)) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_scale_step_doubles T P m d z k S0 S1 hP hz hd hdz hdm ht hset0 hset1 hS0 hS1 hw0 hw1

/-- **Two-scale refutation of `CenterPeriodic` across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`) from first-bit `maskparity · 0` agreement without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_scale_step_doubles_kit
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hS0 : Rule30UOR.Core.twopow k ≤ S0 + 1) (hS1 : Rule30UOR.Core.twopow (k + 1) ≤ S1 + 1)
    (hm0 : ∀ s : Nat, s ≤ S0 →
      Rule30UOR.Scale.maskparity (((d + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow k) + s) 0)
    (hm1 : ∀ s : Nat, s ≤ S1 →
      Rule30UOR.Scale.maskparity (((d + Rule30UOR.Core.twopow (k + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow (k + 1)) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_scale_step_doubles T P m d z k S0 S1 hP hz hd hdz hdm ht hset0 hset1 hS0 hS1 hm0 hm1

/-- **Strict exponential dominance `n < 2^n` from the verified paper**. -/
theorem lt_twopow_self_kit (n : Nat) : n < Rule30UOR.Core.twopow n :=
  Rule30Paper.Paper.lt_twopow_self n

/-- **Refuting `CenterPeriodic` at `t + m * P = 2^k` from `LhColAgree t (m * P) 1 S` over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_at_twopow_kit
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hcone : t + m * P = Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_at_twopow T P m t k S hP hm ht hcone hS hlh

/-- **Refuting `CenterPeriodic` at `z + 2^k` for `m * P = 2` from `LhColAgree (z + 2^k) (m * P) 1 S` over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_at_zero_diag_step_two_kit
    (T P m z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree (z + Rule30UOR.Core.twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_at_zero_diag_step_two T P m z k S hP hz hm ht hset0 hset2 hS hlh

/-- **Refuting `CenterPeriodic` at `z + 2^k` from two zero diagonals and `LhColAgree (z + 2^k) (m * P) 1 S` over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_of_two_zero_diags_kit
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree (z + Rule30UOR.Core.twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_of_two_zero_diags T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hlh

/-- **Two-scale refutation of `CenterPeriodic` across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`) from `LhColAgree` without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_scale_step_doubles_kit
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hS0 : Rule30UOR.Core.twopow k ≤ S0 + 1) (hS1 : Rule30UOR.Core.twopow (k + 1) ≤ S1 + 1)
    (hlh0 : Rule30UOR.Interfaces.LhColAgree (d + Rule30UOR.Core.twopow k) (m * P) 1 S0)
    (hlh1 : Rule30UOR.Interfaces.LhColAgree (d + Rule30UOR.Core.twopow (k + 1)) (m * P) 1 S1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_scale_step_doubles T P m d z k S0 S1 hP hz hd hdz hdm ht hset0 hset1 hS0 hS1 hlh0 hlh1

/-- **Direct `twopow k - m * P` cone-boundary refutation of `CenterPeriodic` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_sub_twopow_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ Rule30UOR.Core.twopow k) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((Rule30UOR.Core.twopow k - m * P) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_sub_twopow T P m k S hP hm hk hS hw

/-- **Direct `twopow k - m * P` cone-boundary refutation of `CenterPeriodic` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_sub_twopow_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ Rule30UOR.Core.twopow k) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((Rule30UOR.Core.twopow k - m * P) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_sub_twopow T P m k S hP hm hk hS hmp

/-- **Unconditional existence of a white-center `rhCenter · 1` flip within `2^k` steps of `t + m * P = 2^k` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_white_center_rhcenter_one_flip_at_twopow_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hcone : t + m * P = Rule30UOR.Core.twopow k) (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center (t + s) = false ∧
      Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 =
        !Rule30UOR.Interfaces.rhCenter (t + s) 1 :=
  Rule30Paper.Paper.exists_white_center_rhcenter_one_flip_at_twopow_of_periodic T P hP hper m t k S hm ht hcone hS

/-- **Unconditional existence of a first-bit `maskparity · 0` flip within `2^k` steps of `t + m * P = 2^k` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_maskparity_zero_flip_at_twopow_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hcone : t + m * P = Rule30UOR.Core.twopow k) (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.exists_maskparity_zero_flip_at_twopow_of_periodic T P hP hper m t k S hm ht hcone hS

/-- **Unconditional existence of a left-column-`-1` `lhCenter · 1` flip within `2^k` steps of `t + m * P = 2^k` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_lhcenter_one_flip_at_twopow_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hcone : t + m * P = Rule30UOR.Core.twopow k) (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Interfaces.lhCenter ((t + s) + m * P) 1 =
        !Rule30UOR.Interfaces.lhCenter (t + s) 1 :=
  Rule30Paper.Paper.exists_lhcenter_one_flip_at_twopow_of_periodic T P hP hper m t k S hm ht hcone hS

/-- **Unconditional existence of a white-center `rhCenter · 1` flip in `[2^k - m * P, 2^(k+1) - m * P)` for every `k` with `T + m * P ≤ 2^k` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_white_center_rhcenter_one_flip_sub_twopow_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ Rule30UOR.Core.twopow k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Core.center ((Rule30UOR.Core.twopow k - m * P) + s) = false ∧
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + s) 1 :=
  Rule30Paper.Paper.exists_white_center_rhcenter_one_flip_sub_twopow_of_periodic T P hP hper m k hm hk

/-- **Unconditional existence of a first-bit `maskparity · 0` flip in `[2^k - m * P, 2^(k+1) - m * P)` for every `k` with `T + m * P ≤ 2^k` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_maskparity_zero_flip_sub_twopow_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ Rule30UOR.Core.twopow k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Scale.maskparity (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((Rule30UOR.Core.twopow k - m * P) + s) 0 :=
  Rule30Paper.Paper.exists_maskparity_zero_flip_sub_twopow_of_periodic T P hP hper m k hm hk

/-- **Unconditional existence of a left-column-`-1` `lhCenter · 1` flip in `[2^k - m * P, 2^(k+1) - m * P)` for every `k` with `T + m * P ≤ 2^k` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_lhcenter_one_flip_sub_twopow_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ Rule30UOR.Core.twopow k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Interfaces.lhCenter (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.lhCenter ((Rule30UOR.Core.twopow k - m * P) + s) 1 :=
  Rule30Paper.Paper.exists_lhcenter_one_flip_sub_twopow_of_periodic T P hP hper m k hm hk

/-- **Unconditional existence of a white-center `rhCenter · 1` flip within `2^k` steps of `z + 2^k` when `m * P = 2` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_white_center_rhcenter_one_flip_at_zero_diag_step_two_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + s) = false ∧
      Rule30UOR.Interfaces.rhCenter (((z + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.rhCenter ((z + Rule30UOR.Core.twopow k) + s) 1 :=
  Rule30Paper.Paper.exists_white_center_rhcenter_one_flip_at_zero_diag_step_two_of_periodic T P hP hper m z k S hz hm ht hset0 hset2 hS

/-- **Unconditional existence of a first-bit `maskparity · 0` flip within `2^k` steps of `z + 2^k` when `m * P = 2` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity (((z + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + Rule30UOR.Core.twopow k) + s) 0 :=
  Rule30Paper.Paper.exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic T P hP hper m z k S hz hm ht hset0 hset2 hS

/-- **Monotonicity of `twopow` (`a ≤ b → 2^a ≤ 2^b`) from the verified paper**. -/
theorem twopow_mono_kit (a b : Nat) (h : a ≤ b) :
    Rule30UOR.Core.twopow a ≤ Rule30UOR.Core.twopow b :=
  Rule30Paper.Paper.twopow_mono a b h

/-- **Strict exponential bound `n < 2^k` from `n ≤ k` from the verified paper**. -/
theorem lt_twopow_of_le_kit (n k : Nat) (h : n ≤ k) :
    n < Rule30UOR.Core.twopow k :=
  Rule30Paper.Paper.lt_twopow_of_le n k h

/-- **Refuting `CenterPeriodic` at every scale `k ≥ T + m * P` from white-center column-`1` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_sub_twopow_ge_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ k) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((Rule30UOR.Core.twopow k - m * P) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_sub_twopow_ge T P m k S hP hm hk hS hw

/-- **Refuting `CenterPeriodic` at every scale `k ≥ T + m * P` from first-bit `maskparity · 0` agreement over `2^k ≤ S + 1` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_sub_twopow_ge_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ k) (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((Rule30UOR.Core.twopow k - m * P) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_sub_twopow_ge T P m k S hP hm hk hS hmp

/-- **Unconditional existence of a white-center `rhCenter · 1` flip in `[2^k - m * P, 2^(k+1) - m * P)` for every `k ≥ T + m * P` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_white_center_rhcenter_one_flip_sub_twopow_ge_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Core.center ((Rule30UOR.Core.twopow k - m * P) + s) = false ∧
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + s) 1 :=
  Rule30Paper.Paper.exists_white_center_rhcenter_one_flip_sub_twopow_ge_of_periodic T P hP hper m k hm hk

/-- **Unconditional existence of a first-bit `maskparity · 0` flip in `[2^k - m * P, 2^(k+1) - m * P)` for every `k ≥ T + m * P` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_maskparity_zero_flip_sub_twopow_ge_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Scale.maskparity (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((Rule30UOR.Core.twopow k - m * P) + s) 0 :=
  Rule30Paper.Paper.exists_maskparity_zero_flip_sub_twopow_ge_of_periodic T P hP hper m k hm hk

/-- **Unconditional existence of a left-column-`-1` `lhCenter · 1` flip in `[2^k - m * P, 2^(k+1) - m * P)` for every `k ≥ T + m * P` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_lhcenter_one_flip_sub_twopow_ge_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Interfaces.lhCenter (((Rule30UOR.Core.twopow k - m * P) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.lhCenter ((Rule30UOR.Core.twopow k - m * P) + s) 1 :=
  Rule30Paper.Paper.exists_lhcenter_one_flip_sub_twopow_ge_of_periodic T P hP hper m k hm hk

/-- **Unconditional fundamental-period (`P` itself, no multiplier `m`!) white-center `rhCenter · 1` flip in `[2^k - P, 2^(k+1) - P)` for every `k ≥ T + P` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_white_center_rhcenter_one_flip_sub_twopow_p_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k : Nat) (hk : T + P ≤ k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Core.center ((Rule30UOR.Core.twopow k - P) + s) = false ∧
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - P) + s) + P) 1 =
        !Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - P) + s) 1 :=
  Rule30Paper.Paper.exists_white_center_rhcenter_one_flip_sub_twopow_p_of_periodic T P hP hper k hk

/-- **Unconditional fundamental-period (`P` itself, no multiplier `m`!) first-bit `maskparity · 0` flip in `[2^k - P, 2^(k+1) - P)` for every `k ≥ T + P` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_maskparity_zero_flip_sub_twopow_p_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k : Nat) (hk : T + P ≤ k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Scale.maskparity (((Rule30UOR.Core.twopow k - P) + s) + P) 0 =
        !Rule30UOR.Scale.maskparity ((Rule30UOR.Core.twopow k - P) + s) 0 :=
  Rule30Paper.Paper.exists_maskparity_zero_flip_sub_twopow_p_of_periodic T P hP hper k hk

/-- **Unconditional fundamental-period (`P` itself, no multiplier `m`!) left-column-`-1` `lhCenter · 1` flip in `[2^k - P, 2^(k+1) - P)` for every `k ≥ T + P` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_lhcenter_one_flip_sub_twopow_p_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k : Nat) (hk : T + P ≤ k) :
    ∃ s : Nat, s < Rule30UOR.Core.twopow k ∧
      Rule30UOR.Interfaces.lhCenter (((Rule30UOR.Core.twopow k - P) + s) + P) 1 =
        !Rule30UOR.Interfaces.lhCenter ((Rule30UOR.Core.twopow k - P) + s) 1 :=
  Rule30Paper.Paper.exists_lhcenter_one_flip_sub_twopow_p_of_periodic T P hP hper k hk

/-- **Unconditional existence of a left-column-`-1` `lhCenter · 1` flip within `2^k` steps of `z + 2^k` when `m * P = 2` under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_lhcenter_one_flip_at_zero_diag_step_two_of_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset2 : Rule30UOR.Interfaces.SettledBy (z + 2) ((z + 2) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Interfaces.lhCenter (((z + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.lhCenter ((z + Rule30UOR.Core.twopow k) + s) 1 :=
  Rule30Paper.Paper.exists_lhcenter_one_flip_at_zero_diag_step_two_of_periodic T P hP hper m z k S hz hm ht hset0 hset2 hS

/-- **Unconditional existence of a white-center `rhCenter · 1` flip within `2^k` steps of `z + 2^k` for any two zero diagonals under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_white_center_rhcenter_one_flip_of_two_zero_diags_and_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center ((z + Rule30UOR.Core.twopow k) + s) = false ∧
      Rule30UOR.Interfaces.rhCenter (((z + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.rhCenter ((z + Rule30UOR.Core.twopow k) + s) 1 :=
  Rule30Paper.Paper.exists_white_center_rhcenter_one_flip_of_two_zero_diags_and_periodic T P hP hper m z k S hz0 h2 hz1 ht hset0 hset1 hS

/-- **Unconditional existence of a first-bit `maskparity · 0` flip within `2^k` steps of `z + 2^k` for any two zero diagonals under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_maskparity_zero_flip_of_two_zero_diags_and_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity (((z + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + Rule30UOR.Core.twopow k) + s) 0 :=
  Rule30Paper.Paper.exists_maskparity_zero_flip_of_two_zero_diags_and_periodic T P hP hper m z k S hz0 h2 hz1 ht hset0 hset1 hS

/-- **Unconditional existence of a left-column-`-1` `lhCenter · 1` flip within `2^k` steps of `z + 2^k` for any two zero diagonals under `CenterPeriodic` alone from the verified paper**. -/
theorem exists_lhcenter_one_flip_of_two_zero_diags_and_periodic_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Interfaces.lhCenter (((z + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
        !Rule30UOR.Interfaces.lhCenter ((z + Rule30UOR.Core.twopow k) + s) 1 :=
  Rule30Paper.Paper.exists_lhcenter_one_flip_of_two_zero_diags_and_periodic T P hP hper m z k S hz0 h2 hz1 ht hset0 hset1 hS

/-- **Scale-step flip of the combined `maskparity ⊕ leftresponse` shift defect across a dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`) without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow (k + 1)) (k + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow (k + 1)) (k + 1))) =
    !Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow k) + m * P) k)
        (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) k))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse ((d + Rule30UOR.Core.twopow k) + m * P) k)
        (Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset1

/-- **Scale-step flip of the late `response` shift defect across the reset diagonal `z + 3` (`DoublesAt (twopow k) z`) without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem periodic_late_response_reset_defect_flip_of_doubles_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow (k + 1)) (k + 1)) =
    !Rule30UOR.Core.bxor
      (Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :=
  Rule30Paper.Paper.periodic_late_response_reset_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset3

/-- **Scale-step `response` inversion at `k + 1` from scale-`k` agreement across the reset diagonal `z + 3` (`DoublesAt (twopow k) z`) from the verified paper**. -/
theorem periodic_late_response_reset_flip_of_doubles_and_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k))
    (hreq : Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow k) + m * P) k =
      Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow k) k) :
    Rule30UOR.Scale.response ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1) =
      !Rule30UOR.Scale.response (d + Rule30UOR.Core.twopow (k + 1)) (k + 1) :=
  Rule30Paper.Paper.periodic_late_response_reset_flip_of_doubles_and_eq T P hP hper m d z k hz hd hdz hdm ht hset0 hset3 hreq

/-- **Scale-step flip of the combined `maskparity ⊕ leftresponse` shift defect across the reset diagonal `z + 3` (`DoublesAt (twopow k) z`) without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem periodic_late_maskparity_xor_leftresponse_reset_defect_flip_of_doubles_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k)) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow (k + 1)) (k + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse ((d + Rule30UOR.Core.twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow (k + 1)) (k + 1))) =
    !Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow k) + m * P) k)
        (Rule30UOR.Scale.maskparity (d + Rule30UOR.Core.twopow k) k))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Scale.leftresponse ((d + Rule30UOR.Core.twopow k) + m * P) k)
        (Rule30UOR.Scale.leftresponse (d + Rule30UOR.Core.twopow k) k)) :=
  Rule30Paper.Paper.periodic_late_maskparity_xor_leftresponse_reset_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset3

/-- **Single-window (`2^k + 2^(k+1) ≤ S + 1`) refutation of `CenterPeriodic` across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`, `d + m * P = z + 1`) from white-center column-`1` agreement without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_three_twopow_doubles_kit
    (T P m d z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow (k + 1) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((d + Rule30UOR.Core.twopow k) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((d + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((d + Rule30UOR.Core.twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_three_twopow_doubles T P m d z k S hP hz hd hdz hdm ht hset0 hset1 hS hw

/-- **Single-window (`2^k + 2^(k+1) ≤ S + 1`) refutation of `CenterPeriodic` across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`, `d + m * P = z + 1`) from first-bit `maskparity · 0` agreement without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_three_twopow_doubles_kit
    (T P m d z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow (k + 1) ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((d + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_three_twopow_doubles T P m d z k S hP hz hd hdz hdm ht hset0 hset1 hS hmp

/-- **Single-window (`2^k + 2^(k+1) ≤ S + 1`) refutation of `CenterPeriodic` across any dyadic doubling zero diagonal `z` (`DoublesAt (twopow k) z`, `d + m * P = z + 1`) from `LhColAgree` without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_three_twopow_doubles_kit
    (T P m d z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) ((z + 1) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow (k + 1) ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree (d + Rule30UOR.Core.twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_three_twopow_doubles T P m d z k S hP hz hd hdz hdm ht hset0 hset1 hS hlh

/-- **Single-window (`2^k + 2^(k+1) ≤ S + 1`) refutation of `CenterPeriodic` across the reset diagonal `d + m * P = z + 3` (`DoublesAt (twopow k) z`) from white-center column-`1` agreement without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_white_center_rhcenter_one_three_twopow_reset_doubles_kit
    (T P m d z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow (k + 1) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((d + Rule30UOR.Core.twopow k) + s) = false →
        Rule30UOR.Interfaces.rhCenter (((d + Rule30UOR.Core.twopow k) + s) + m * P) 1 =
          Rule30UOR.Interfaces.rhCenter ((d + Rule30UOR.Core.twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_white_center_rhcenter_one_three_twopow_reset_doubles T P m d z k S hP hz hd hdz hdm ht hset0 hset3 hS hw

/-- **Single-window (`2^k + 2^(k+1) ≤ S + 1`) refutation of `CenterPeriodic` across the reset diagonal `d + m * P = z + 3` (`DoublesAt (twopow k) z`) from first-bit `maskparity · 0` agreement without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_maskparity_zero_agree_three_twopow_reset_doubles_kit
    (T P m d z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow (k + 1) ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((d + Rule30UOR.Core.twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + Rule30UOR.Core.twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_maskparity_zero_agree_three_twopow_reset_doubles T P m d z k S hP hz hd hdz hdm ht hset0 hset3 hS hmp

/-- **Single-window (`2^k + 2^(k+1) ≤ S + 1`) refutation of `CenterPeriodic` across the reset diagonal `d + m * P = z + 3` (`DoublesAt (twopow k) z`) from `LhColAgree` without `DoublesAt (m * P) z` or `z ≤ k` from the verified paper**. -/
theorem not_centerperiodic_of_lhcolagree_one_three_twopow_reset_doubles_kit
    (T P m d z k S : Nat) (hP : 0 < P) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (Rule30UOR.Core.twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy d (d + Rule30UOR.Core.twopow k))
    (hset3 : Rule30UOR.Interfaces.SettledBy (z + 3) ((z + 3) + Rule30UOR.Core.twopow k))
    (hS : Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow (k + 1) ≤ S + 1)
    (hlh : Rule30UOR.Interfaces.LhColAgree (d + Rule30UOR.Core.twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_lhcolagree_one_three_twopow_reset_doubles T P m d z k S hP hz hd hdz hdm ht hset0 hset3 hS hlh

/-- **Exact diagonal readout of the driven right half `rdrv` (`rdrv t t k p = rhCenter (t + k) p`, `kit [33]`) from the verified paper**. -/
theorem rdrv_diag_eq_rhcenter_kit (t k p : Nat) :
    Rule30UOR.Interfaces.rdrv t t k p = Rule30UOR.Interfaces.rhCenter (t + k) p :=
  Rule30Paper.Paper.rdrv_diag_eq_rhcenter t k p

/-- **All-white seed readout of the driven right half `rdrv` (`rdrv 0 0 t p = rhCenter t p`, `kit [33]`) from the verified paper**. -/
theorem rdrv_zero_eq_rhcenter_kit (t p : Nat) :
    Rule30UOR.Interfaces.rdrv 0 0 t p = Rule30UOR.Interfaces.rhCenter t p :=
  Rule30Paper.Paper.rdrv_zero_eq_rhcenter t p

/-- **Interior Rule-30 evolution law of the driven right half `rdrv` from the verified paper**. -/
theorem rdrv_step_succ_kit (td tx k p : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx k p)
        (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2)) :=
  Rule30Paper.Paper.rdrv_step_succ td tx k p

/-- **Complete independence of the center drive outside the drive cone (`k < p`) in the driven right half `rdrv` from the verified paper**. -/
theorem rdrv_drive_indep_of_lt_kit (td td' tx k p : Nat) (hkp : k < p) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td' tx k p :=
  Rule30Paper.Paper.rdrv_drive_indep_of_lt td td' tx k p hkp

/-- **Drive-shift invariance of the driven right half `rdrv` under `CenterPeriodic` (`rdrv (td + m * P) tx k p = rdrv td tx k p`) from the verified paper**. -/
theorem periodic_rdrv_drive_shift_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m td tx k p : Nat) (htd : T ≤ td) :
    Rule30UOR.Interfaces.rdrv (td + m * P) tx k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.periodic_rdrv_drive_shift_eq T P hP hper m td tx k p htd

/-- **Same-drive representation of the `m * P`-shifted right half under `CenterPeriodic` (`rhCenter ((t + m * P) + k) p = rdrv t (t + m * P) k p`) from the verified paper**. -/
theorem periodic_rhcenter_shift_eq_rdrv_same_drive_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k p : Nat) (ht : T ≤ t) :
    Rule30UOR.Interfaces.rhCenter ((t + m * P) + k) p =
      Rule30UOR.Interfaces.rdrv t (t + m * P) k p :=
  Rule30Paper.Paper.periodic_rhcenter_shift_eq_rdrv_same_drive T P hP hper m t k p ht

/-- **Outside-the-drive-cone exact readout of `rdrv` (`k < p`) from the verified paper**. -/
theorem rdrv_outside_cone_eq_rhcenter_kit
    (td tx k p : Nat) (hkp : k < p) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rhCenter (tx + k) p :=
  Rule30Paper.Paper.rdrv_outside_cone_eq_rhcenter td tx k p hkp

/-- **Semigroup restart law of the driven right half `rdrv` (`rdrv t t (a + k) p = rdrv (t + a) (t + a) k p`) from the verified paper**. -/
theorem rdrv_semigroup_add_kit
    (t a k p : Nat) :
    Rule30UOR.Interfaces.rdrv t t (a + k) p = Rule30UOR.Interfaces.rdrv (t + a) (t + a) k p :=
  Rule30Paper.Paper.rdrv_semigroup_add t a k p

/-- **Sharp drive-cone causality of the driven right half `rdrv` (`s + p ≤ k`, `kit [33]`) from the verified paper**. -/
theorem rdrv_drive_causal_cone_kit
    (td td' tx k p : Nat)
    (hc : ∀ s : Nat, s + p ≤ k →
      Rule30UOR.Core.center (td + s) = Rule30UOR.Core.center (td' + s)) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td' tx k p :=
  Rule30Paper.Paper.rdrv_drive_causal_cone td td' tx k p hc

/-- **Initial-slice causality of the driven right half `rdrv` under a shared drive (`p + k ≤ L + 1`, `kit [33]`) from the verified paper**. -/
theorem rdrv_init_causal_cone_kit
    (td tx Q L k p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 L) (hpk : p + k ≤ L + 1) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_init_causal_cone td tx Q L k p hband hpk

/-- **Same-drive column-`1` agreement of `rdrv` over `[0, S]` from initial slice `RhBandAgree` from the verified paper**. -/
theorem rdrv_col_one_agree_of_rhbandagree_one_kit
    (td tx Q S s : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 S) (hs : s ≤ S) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) s 1 = Rule30UOR.Interfaces.rdrv td tx s 1 :=
  Rule30Paper.Paper.rdrv_col_one_agree_of_rhbandagree_one td tx Q S s hband hs

/-- **Derivation of `RhColAgree t (m * P) 1 S` from `RhBandAgree t (m * P) 1 S` via the driven right half `rdrv` from the verified paper**. -/
theorem periodic_rhcolagree_one_of_rhbandagree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t) (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 S) :
    Rule30UOR.Interfaces.RhColAgree t (m * P) 1 S :=
  Rule30Paper.Paper.periodic_rhcolagree_one_of_rhbandagree_one T P hP hper m t S ht hband

/-- **Derivation of `maskparity · 0` agreement over `[t, t + S]` from `RhBandAgree t (m * P) 1 S` under `CenterPeriodic` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rhbandagree_one_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t) (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 S) (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rhbandagree_one T P hP hper m t S s ht hband hs

/-- **Derivation of `maskparity · 0` agreement from same-drive `rdrv` column-`1` agreement at white centers from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rdrv_one_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hw : Rule30UOR.Core.center (t + s) = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) s 1 = Rule30UOR.Interfaces.rdrv t t s 1) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht hw

/-- **Bounded-width strip determination law of the driven right half `rdrv` from the verified paper**. -/
theorem rdrv_strip_agree_of_rhbandagree_and_col_agree_kit
    (td tx Q B S s p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hcol : ∀ u : Nat, u < S →
      Rule30UOR.Interfaces.rdrv td (tx + Q) u (B + 2) = Rule30UOR.Interfaces.rdrv td tx u (B + 2))
    (hs : s ≤ S) (hp : p ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) s p = Rule30UOR.Interfaces.rdrv td tx s p :=
  Rule30Paper.Paper.rdrv_strip_agree_of_rhbandagree_and_col_agree td tx Q B S s p hband hcol hs hp

/-- **Derivation of `maskparity · 0` agreement over `[t, t + S]` from fixed-width strip agreement from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rhbandagree_and_rhcolagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B S s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hcol : Rule30UOR.Interfaces.RhColAgree t (m * P) (B + 2) S) (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rhbandagree_and_rhcolagree T P hP hper m t B S s ht hband hcol hs

/-- **Refutation of `CenterPeriodic` from same-drive `rdrv` column-`1` agreement over `p + 3 * (m * P)` steps after a zero diagonal from the verified paper**. -/
theorem not_centerperiodic_of_rdrv_one_agree_at_zero_diag_step_two_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 =
          Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rdrv_one_agree_at_zero_diag_step_two T P m z p S hP hm ht hz hd hset1 hsetQ hS hw

/-- **Refutation of `CenterPeriodic` from spatial right-half slice agreement `RhBandAgree (z + (p + 1)) (m * P) 1 S` at a zero diagonal from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_one_at_zero_diag_step_two_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_one_at_zero_diag_step_two T P m z p S hP hm ht hz hd hset1 hsetQ hS hband

/-- **Refutation of `CenterPeriodic` from fixed-width right-half strip agreement at a zero diagonal from the verified paper**. -/
theorem not_centerperiodic_of_strip_agree_at_zero_diag_step_two_kit
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hcol : Rule30UOR.Interfaces.RhColAgree (z + (p + 1)) (m * P) (B + 2) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_strip_agree_at_zero_diag_step_two T P m z p B S hP hm ht hz hd hset1 hsetQ hS hband hcol

/-- **Dyadic (`2^k - m * P`) refutation of `CenterPeriodic` from same-drive `rdrv` column-`1` agreement from the verified paper**. -/
theorem not_centerperiodic_of_rdrv_one_agree_sub_twopow_ge_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ Rule30UOR.Core.twopow k) (ht : T + m * P ≤ Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((Rule30UOR.Core.twopow k - m * P) + s) = false →
        Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k) s 1 =
          Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k - m * P) s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rdrv_one_agree_sub_twopow_ge T P m k S hP hm hmP ht hS hw

/-- **Dyadic (`2^k - m * P`) refutation of `CenterPeriodic` from spatial right-half slice agreement `RhBandAgree (2^k - m * P) (m * P) 1 S` from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_one_sub_twopow_ge_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ Rule30UOR.Core.twopow k) (ht : T + m * P ≤ Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (Rule30UOR.Core.twopow k - m * P) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_one_sub_twopow_ge T P m k S hP hm hmP ht hS hband

/-- **Exact inward Rule-30 inversion in the driven right half `rdrv` (`kit [33]` + `kit [23]`) from the verified paper**. -/
theorem rdrv_inward_bxor_kit
    (td tx k p : Nat) :
    Rule30UOR.Interfaces.rdrv td tx k p =
      Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1))
        (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2)) :=
  Rule30Paper.Paper.rdrv_inward_bxor td tx k p

/-- **Black-left OR-masking in the inward step of `rdrv` from the verified paper**. -/
theorem rdrv_inward_of_black_left_kit
    (td tx k p : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx k (p + 1) = true) :
    Rule30UOR.Interfaces.rdrv td tx k p =
      !Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1) :=
  Rule30Paper.Paper.rdrv_inward_of_black_left td tx k p hb

/-- **Black-right OR-masking in the inward step of `rdrv` from the verified paper**. -/
theorem rdrv_inward_of_black_right_kit
    (td tx k p : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx k (p + 2) = true) :
    Rule30UOR.Interfaces.rdrv td tx k p =
      !Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1) :=
  Rule30Paper.Paper.rdrv_inward_of_black_right td tx k p hb

/-- **Direct center-drive evolution of column `1` of `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_step_one_eq_center_xor_or_kit
    (td tx k : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) 1 =
      Rule30UOR.Core.bxor
        (Rule30UOR.Core.center (td + k))
        (Rule30UOR.Interfaces.rdrv td tx k 1 || Rule30UOR.Interfaces.rdrv td tx k 2) :=
  Rule30Paper.Paper.rdrv_step_one_eq_center_xor_or td tx k

/-- **Black column-`1` OR-absorption in `rdrv` (`rdrv td tx (k + 1) 1 = !center (td + k)`) from the verified paper**. -/
theorem rdrv_step_one_eq_not_center_of_black_one_kit
    (td tx k : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx k 1 = true) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) 1 = !Rule30UOR.Core.center (td + k) :=
  Rule30Paper.Paper.rdrv_step_one_eq_not_center_of_black_one td tx k hb

/-- **Unconditional drive-cancellation law for column-`1` defects in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_step_one_defect_eq_or_defect_kit
    (td tx2 tx k : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.rdrv td tx2 (k + 1) 1)
      (Rule30UOR.Interfaces.rdrv td tx (k + 1) 1) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.rdrv td tx2 k 1 || Rule30UOR.Interfaces.rdrv td tx2 k 2)
      (Rule30UOR.Interfaces.rdrv td tx k 1 || Rule30UOR.Interfaces.rdrv td tx k 2) :=
  Rule30Paper.Paper.rdrv_step_one_defect_eq_or_defect td tx2 tx k

/-- **Unconditional 1-step forward pinning of column `1` in `rdrv` across a black cell from the verified paper**. -/
theorem rdrv_step_one_eq_of_black_one_kit
    (td tx2 tx k : Nat)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 k 1 = true)
    (hb0 : Rule30UOR.Interfaces.rdrv td tx k 1 = true) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + 1) 1 = Rule30UOR.Interfaces.rdrv td tx (k + 1) 1 :=
  Rule30Paper.Paper.rdrv_step_one_eq_of_black_one td tx2 tx k hb2 hb0

/-- **Vanishing of the driven right half `rdrv` outside the light cone `p > tx + k` from the verified paper**. -/
theorem rdrv_gt_eq_false_kit
    (td tx k p : Nat) (hgt : tx + k < p) :
    Rule30UOR.Interfaces.rdrv td tx k p = false :=
  Rule30Paper.Paper.rdrv_gt_eq_false td tx k p hgt

/-- **Black right-edge diagonal of the driven right half `rdrv` (`0 < tx`) from the verified paper**. -/
theorem rdrv_self_eq_true_kit
    (td tx k : Nat) (htx : 0 < tx) :
    Rule30UOR.Interfaces.rdrv td tx k (tx + k) = true :=
  Rule30Paper.Paper.rdrv_self_eq_true td tx k htx

/-- **Unconditional right-edge `2^e`-shift invariance of `rdrv` outside the drive cone (`k < p`) from the verified paper**. -/
theorem rdrv_diag_shift_twopow_eq_kit
    (td tx e k p v : Nat)
    (hkp : k < p) (hpt : p ≤ tx + k) (he : (tx + k) - p ≤ e) :
    Rule30UOR.Interfaces.rdrv td (tx + v * Rule30UOR.Core.twopow e) k (p + v * Rule30UOR.Core.twopow e) =
      Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_diag_shift_twopow_eq td tx e k p v hkp hpt he

/-- **Single-cell inward agreement step in `rdrv` from the verified paper**. -/
theorem rdrv_inward_step_agree_kit
    (td tx2 tx k p : Nat)
    (hnext : Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (p + 1) =
      Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1))
    (hor : (Rule30UOR.Interfaces.rdrv td tx2 k (p + 1) || Rule30UOR.Interfaces.rdrv td tx2 k (p + 2)) =
      (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2))) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_inward_step_agree td tx2 tx k p hnext hor

/-- **1-column inward propagation of temporal agreement in `rdrv` from the verified paper**. -/
theorem rdrv_inward_two_col_step_agree_kit
    (td tx2 tx S p s : Nat)
    (hc1 : ∀ u : Nat, u ≤ S + 1 →
      Rule30UOR.Interfaces.rdrv td tx2 u (p + 1) = Rule30UOR.Interfaces.rdrv td tx u (p + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rdrv td tx2 u (p + 2) = Rule30UOR.Interfaces.rdrv td tx u (p + 2))
    (hs : s ≤ S) :
    Rule30UOR.Interfaces.rdrv td tx2 s p = Rule30UOR.Interfaces.rdrv td tx s p :=
  Rule30Paper.Paper.rdrv_inward_two_col_step_agree td tx2 tx S p s hc1 hc2 hs

/-- **Multi-column (`K`-step) inward propagation of temporal agreement in `rdrv` from the verified paper**. -/
theorem rdrv_inward_two_col_propagate_kit
    (td tx2 tx K p0 S s : Nat)
    (hc1 : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv td tx2 u (p0 + K) = Rule30UOR.Interfaces.rdrv td tx u (p0 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv td tx2 u ((p0 + K) + 1) = Rule30UOR.Interfaces.rdrv td tx u ((p0 + K) + 1))
    (hs : s ≤ S) :
    Rule30UOR.Interfaces.rdrv td tx2 s p0 = Rule30UOR.Interfaces.rdrv td tx s p0 :=
  Rule30Paper.Paper.rdrv_inward_two_col_propagate td tx2 tx K p0 S s hc1 hc2 hs

/-- **Derivation of `maskparity · 0` agreement over `[t, t + S]` from two-column `rdrv` agreement at depth `1 + K` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rdrv_two_col_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K S s : Nat) (ht : T ≤ t)
    (hc1 : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv t (t + m * P) u (1 + K) = Rule30UOR.Interfaces.rdrv t t u (1 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv t (t + m * P) u ((1 + K) + 1) = Rule30UOR.Interfaces.rdrv t t u ((1 + K) + 1))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rdrv_two_col_agree T P hP hper m t K S s ht hc1 hc2 hs

/-- **Refutation of `CenterPeriodic` from two-column `rdrv` agreement at depth `1 + K` after a zero diagonal from the verified paper**. -/
theorem not_centerperiodic_of_rdrv_two_col_agree_at_zero_diag_kit
    (T P m z p K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) =
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u ((1 + K) + 1) =
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) u ((1 + K) + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rdrv_two_col_agree_at_zero_diag T P m z p K S hP hm ht hz hd hset1 hsetQ hS hc1 hc2

/-- **Right-threshold diagonal `2^e`-shift law in `rdrv` (`k < p`) from the verified paper**. -/
theorem rdrv_diag_shift_twopow_eq_of_threshold_kit
    (td tx e J k p v : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold e J) (hkp : k < p) (hpt : p ≤ tx + k)
    (hJle : (tx + k) - p ≤ J) :
    Rule30UOR.Interfaces.rdrv td (tx + v * Rule30UOR.Core.twopow e) k (p + v * Rule30UOR.Core.twopow e) =
      Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_diag_shift_twopow_eq_of_threshold td tx e J k p v hJ hkp hpt hJle

/-- **Right-edge white zero-gap of width `J` at multiples of `2^e` in `rdrv` from the verified paper**. -/
theorem rdrv_zero_gap_of_threshold_kit
    (td e J u k j : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold e J) (hj1 : 1 ≤ j) (hjJ : j ≤ J)
    (hkju : k + j < u * Rule30UOR.Core.twopow e) :
    Rule30UOR.Interfaces.rdrv td (u * Rule30UOR.Core.twopow e - k) k (u * Rule30UOR.Core.twopow e - j) = false :=
  Rule30Paper.Paper.rdrv_zero_gap_of_threshold td e J u k j hJ hj1 hjJ hkju

/-- **Right-edge black run of width `J + 1` at `(u + 1) * 2^e - 1` in `rdrv` from the verified paper**. -/
theorem rdrv_last_one_of_threshold_kit
    (td e J u k j : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold e J) (hjJ : j ≤ J)
    (hkju : k + j < (u + 1) * Rule30UOR.Core.twopow e - 1) :
    Rule30UOR.Interfaces.rdrv td (((u + 1) * Rule30UOR.Core.twopow e - 1) - k) k
      (((u + 1) * Rule30UOR.Core.twopow e - 1) - j) = true :=
  Rule30Paper.Paper.rdrv_last_one_of_threshold td e J u k j hJ hjJ hkju

/-- **Interior defect evolution law in `rdrv` from the verified paper**. -/
theorem rdrv_defect_step_succ_kit
    (td tx2 tx k p : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (p + 1))
      (Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1)) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx2 k p) (Rule30UOR.Interfaces.rdrv td tx k p))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rdrv td tx2 k (p + 1) || Rule30UOR.Interfaces.rdrv td tx2 k (p + 2))
        (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2))) :=
  Rule30Paper.Paper.rdrv_defect_step_succ td tx2 tx k p

/-- **Inward defect evolution law in `rdrv` from the verified paper**. -/
theorem rdrv_defect_inward_step_kit
    (td tx2 tx k p : Nat) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.rdrv td tx2 k p)
      (Rule30UOR.Interfaces.rdrv td tx k p) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (p + 1)) (Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1)))
      (Rule30UOR.Core.bxor
        (Rule30UOR.Interfaces.rdrv td tx2 k (p + 1) || Rule30UOR.Interfaces.rdrv td tx2 k (p + 2))
        (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2))) :=
  Rule30Paper.Paper.rdrv_defect_inward_step td tx2 tx k p

/-- **Unconditional column-`1` step agreement from OR-agreement in `rdrv` from the verified paper**. -/
theorem rdrv_step_one_eq_of_or_eq_kit
    (td tx2 tx k : Nat)
    (hor : (Rule30UOR.Interfaces.rdrv td tx2 k 1 || Rule30UOR.Interfaces.rdrv td tx2 k 2) =
      (Rule30UOR.Interfaces.rdrv td tx k 1 || Rule30UOR.Interfaces.rdrv td tx k 2)) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + 1) 1 = Rule30UOR.Interfaces.rdrv td tx (k + 1) 1 :=
  Rule30Paper.Paper.rdrv_step_one_eq_of_or_eq td tx2 tx k hor

/-- **Unconditional OR-agreement from column-`1` step agreement in `rdrv` from the verified paper**. -/
theorem rdrv_or_one_eq_of_step_one_eq_kit
    (td tx2 tx k : Nat)
    (hstep : Rule30UOR.Interfaces.rdrv td tx2 (k + 1) 1 = Rule30UOR.Interfaces.rdrv td tx (k + 1) 1) :
    (Rule30UOR.Interfaces.rdrv td tx2 k 1 || Rule30UOR.Interfaces.rdrv td tx2 k 2) =
      (Rule30UOR.Interfaces.rdrv td tx k 1 || Rule30UOR.Interfaces.rdrv td tx k 2) :=
  Rule30Paper.Paper.rdrv_or_one_eq_of_step_one_eq td tx2 tx k hstep

/-- **Constant diagonal step across a white pair in `rdrv` from the verified paper**. -/
theorem rdrv_diag_eq_of_white_pair_kit
    (td tx k p : Nat)
    (hw1 : Rule30UOR.Interfaces.rdrv td tx k (p + 1) = false)
    (hw2 : Rule30UOR.Interfaces.rdrv td tx k (p + 2) = false) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1) = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_diag_eq_of_white_pair td tx k p hw1 hw2

/-- **Linear diagonal defect step under OR-agreement in `rdrv` from the verified paper**. -/
theorem rdrv_defect_diag_eq_of_or_eq_kit
    (td tx2 tx k p : Nat)
    (hor : (Rule30UOR.Interfaces.rdrv td tx2 k (p + 1) || Rule30UOR.Interfaces.rdrv td tx2 k (p + 2)) =
      (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2))) :
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (p + 1))
      (Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1)) =
    Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.rdrv td tx2 k p)
      (Rule30UOR.Interfaces.rdrv td tx k p) :=
  Rule30Paper.Paper.rdrv_defect_diag_eq_of_or_eq td tx2 tx k p hor

/-- **Inward agreement across a black left column in `rdrv` from the verified paper**. -/
theorem rdrv_agree_inward_of_black_left_kit
    (td tx2 tx k p : Nat)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 k (p + 1) = true)
    (hb0 : Rule30UOR.Interfaces.rdrv td tx k (p + 1) = true)
    (hnext : Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (p + 1) =
      Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1)) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_agree_inward_of_black_left td tx2 tx k p hb2 hb0 hnext

/-- **Derivation of `maskparity · 0` agreement from white-center-conditioned `rdrv` OR-agreement from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rdrv_or_one_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t)
    (h0 : Rule30UOR.Core.center t = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) 0 1 = Rule30UOR.Interfaces.rdrv t t 0 1)
    (hor : ∀ u : Nat, u < S →
      Rule30UOR.Core.center (t + (u + 1)) = false →
        (Rule30UOR.Interfaces.rdrv t (t + m * P) u 1 || Rule30UOR.Interfaces.rdrv t (t + m * P) u 2) =
          (Rule30UOR.Interfaces.rdrv t t u 1 || Rule30UOR.Interfaces.rdrv t t u 2))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rdrv_or_one_agree T P hP hper m t S s ht h0 hor hs

/-- **Multi-column (`K`-step) inward propagation of column-plus-OR agreement in `rdrv` from the verified paper**. -/
theorem rdrv_inward_col_or_propagate_kit
    (td tx2 tx K p0 S s : Nat)
    (hc : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv td tx2 u (p0 + K) = Rule30UOR.Interfaces.rdrv td tx u (p0 + K))
    (ho : ∀ u : Nat, u < S + K →
      (Rule30UOR.Interfaces.rdrv td tx2 u (p0 + K) || Rule30UOR.Interfaces.rdrv td tx2 u ((p0 + K) + 1)) =
        (Rule30UOR.Interfaces.rdrv td tx u (p0 + K) || Rule30UOR.Interfaces.rdrv td tx u ((p0 + K) + 1)))
    (hs : s ≤ S) :
    Rule30UOR.Interfaces.rdrv td tx2 s p0 = Rule30UOR.Interfaces.rdrv td tx s p0 :=
  Rule30Paper.Paper.rdrv_inward_col_or_propagate td tx2 tx K p0 S s hc ho hs

/-- **Derivation of `maskparity · 0` agreement over `[t, t + S]` from `rdrv` column-plus-OR agreement at depth `1 + K` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rdrv_col_or_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K S s : Nat) (ht : T ≤ t)
    (hc : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv t (t + m * P) u (1 + K) = Rule30UOR.Interfaces.rdrv t t u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (Rule30UOR.Interfaces.rdrv t (t + m * P) u (1 + K) || Rule30UOR.Interfaces.rdrv t (t + m * P) u ((1 + K) + 1)) =
        (Rule30UOR.Interfaces.rdrv t t u (1 + K) || Rule30UOR.Interfaces.rdrv t t u ((1 + K) + 1)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rdrv_col_or_agree T P hP hper m t K S s ht hc ho hs

/-- **Refutation of `CenterPeriodic` from `rdrv` column-plus-OR agreement at depth `1 + K` after a zero diagonal from the verified paper**. -/
theorem not_centerperiodic_of_rdrv_col_or_agree_at_zero_diag_kit
    (T P m z p K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) =
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) ||
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u ((1 + K) + 1)) =
      (Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K) ||
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) u ((1 + K) + 1))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rdrv_col_or_agree_at_zero_diag T P m z p K S hP hm ht hz hd hset1 hsetQ hS hc ho

/-- **Dyadic (`2^k - m * P`) refutation of `CenterPeriodic` from `rdrv` column-plus-OR agreement at depth `1 + K` from the verified paper**. -/
theorem not_centerperiodic_of_rdrv_col_or_agree_sub_twopow_ge_kit
    (T P m k K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ Rule30UOR.Core.twopow k) (ht : T + m * P ≤ Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hc : ∀ u : Nat, u ≤ S + K →
      Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k) u (1 + K) =
        Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k - m * P) u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k) u (1 + K) ||
        Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k) u ((1 + K) + 1)) =
      (Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k - m * P) u (1 + K) ||
        Rule30UOR.Interfaces.rdrv (Rule30UOR.Core.twopow k - m * P) (Rule30UOR.Core.twopow k - m * P) u ((1 + K) + 1))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rdrv_col_or_agree_sub_twopow_ge T P m k K S hP hm hmP ht hS hc ho

/-- **All-white initial slice of the pure-drive right half `rdrv td 0 0 p` (`0 < p`, `kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_init_eq_false_kit
    (td p : Nat) (hp : 0 < p) :
    Rule30UOR.Interfaces.rdrv td 0 0 p = false :=
  Rule30Paper.Paper.rdrv_white_seed_init_eq_false td p hp

/-- **Vanishing of the pure-drive right half `rdrv td 0 k p` outside the drive cone `k < p` from the verified paper**. -/
theorem rdrv_white_seed_gt_eq_false_kit
    (td k p : Nat) (hkp : k < p) :
    Rule30UOR.Interfaces.rdrv td 0 k p = false :=
  Rule30Paper.Paper.rdrv_white_seed_gt_eq_false td k p hkp

/-- **Exact drive-cone edge readout of the pure-drive right half (`rdrv td 0 k k = center td`) from the verified paper**. -/
theorem rdrv_white_seed_diag_eq_center_kit
    (td k : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 k k = Rule30UOR.Core.center td :=
  Rule30Paper.Paper.rdrv_white_seed_diag_eq_center td k

/-- **Exact `m * P`-periodicity of the pure-drive right half `rdrv td 0 k p` under `CenterPeriodic` (`kit [33]`) from the verified paper**. -/
theorem periodic_rdrv_white_seed_shift_eq_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m td k p : Nat) (htd : T ≤ td) :
    Rule30UOR.Interfaces.rdrv (td + m * P) 0 k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.periodic_rdrv_white_seed_shift_eq T P hP hper m td k p htd

/-- **Reduction of `rdrv td tx k p` to the pure-drive right half `rdrv td 0 k p` over an initial white band (`kit [33]`) from the verified paper**. -/
theorem rdrv_eq_white_seed_of_initial_white_band_kit
    (td tx L k p : Nat)
    (hw : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hpk : p + k ≤ L + 1) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_eq_white_seed_of_initial_white_band td tx L k p hw hpk

/-- **Column-`1` agreement with the pure-drive right half `rdrv td 0 s 1` over an initial white band from the verified paper**. -/
theorem rdrv_col_one_eq_white_seed_of_initial_white_band_kit
    (td tx S s : Nat)
    (hw : ∀ i : Nat, i ≤ S → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hs : s ≤ S) :
    Rule30UOR.Interfaces.rdrv td tx s 1 = Rule30UOR.Interfaces.rdrv td 0 s 1 :=
  Rule30Paper.Paper.rdrv_col_one_eq_white_seed_of_initial_white_band td tx S s hw hs

/-- **1-step black persistence of column `1` in `rdrv` at a white drive bit from the verified paper**. -/
theorem rdrv_step_one_eq_true_of_white_center_and_black_one_kit
    (td tx k : Nat)
    (hc : Rule30UOR.Core.center (td + k) = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx k 1 = true) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) 1 = true :=
  Rule30Paper.Paper.rdrv_step_one_eq_true_of_white_center_and_black_one td tx k hc hb

/-- **Multi-step black persistence of column `1` in `rdrv` across a white center run (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_center_run_black_one_persist_kit
    (td tx k W j : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx k 1 = true)
    (hrun : ∀ u : Nat, u < W → Rule30UOR.Core.center (td + (k + u)) = false)
    (hj : j ≤ W) :
    Rule30UOR.Interfaces.rdrv td tx (k + j) 1 = true :=
  Rule30Paper.Paper.rdrv_white_center_run_black_one_persist td tx k W j hb hrun hj

/-- **Multi-step column-`1` agreement in `rdrv` across a white center run plus one step from the verified paper**. -/
theorem rdrv_white_center_run_black_one_agree_kit
    (td tx2 tx k W j : Nat)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 k 1 = true)
    (hb0 : Rule30UOR.Interfaces.rdrv td tx k 1 = true)
    (hrun : ∀ u : Nat, u < W → Rule30UOR.Core.center (td + (k + u)) = false)
    (hj : j ≤ W + 1) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + j) 1 = Rule30UOR.Interfaces.rdrv td tx (k + j) 1 :=
  Rule30Paper.Paper.rdrv_white_center_run_black_one_agree td tx2 tx k W j hb2 hb0 hrun hj

/-- **1-step black pinning `rdrv t t 1 1 = true` from `maskparity t 0 = true` from the verified paper**. -/
theorem rdrv_step_one_eq_true_of_maskparity_zero_true_kit
    (t : Nat)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    Rule30UOR.Interfaces.rdrv t t 1 1 = true :=
  Rule30Paper.Paper.rdrv_step_one_eq_true_of_maskparity_zero_true t hm0

/-- **1-step black pinning `rdrv t (t + m * P) 1 1 = true` from `maskparity (t + m * P) 0 = true` under `CenterPeriodic` from the verified paper**. -/
theorem periodic_rdrv_step_one_eq_true_of_maskparity_zero_true_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hmQ : Rule30UOR.Scale.maskparity (t + m * P) 0 = true) :
    Rule30UOR.Interfaces.rdrv t (t + m * P) 1 1 = true :=
  Rule30Paper.Paper.periodic_rdrv_step_one_eq_true_of_maskparity_zero_true T P hP hper m t ht hmQ

/-- **Multi-step propagation of `maskparity · 0` agreement across a white center run from a single `maskparity · 0 = true` match from the verified paper**. -/
theorem periodic_maskparity_zero_agree_on_white_run_of_maskparity_zero_true_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t W s : Nat) (ht : T ≤ t)
    (hmQ : Rule30UOR.Scale.maskparity (t + m * P) 0 = true)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true)
    (hrun : ∀ u : Nat, u < W → Rule30UOR.Core.center (t + (1 + u)) = false)
    (hs : s ≤ W + 2) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_on_white_run_of_maskparity_zero_true T P hP hper m t W s ht hmQ hm0 hrun hs

/-- **Two-column agreement of `rdrv` with the pure-drive right half `rdrv td 0 k ·` inside the right-threshold white zero-gap from the verified paper**. -/
theorem rdrv_two_col_eq_white_seed_of_zero_gap_kit
    (td e J u k j : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold e J) (hj1 : 1 ≤ j) (hjJ : j + 1 ≤ J)
    (hkju : k + (j + 1) < u * Rule30UOR.Core.twopow e) :
    Rule30UOR.Interfaces.rdrv td (u * Rule30UOR.Core.twopow e - k) k (u * Rule30UOR.Core.twopow e - (j + 1)) =
      Rule30UOR.Interfaces.rdrv td 0 k (u * Rule30UOR.Core.twopow e - (j + 1)) ∧
    Rule30UOR.Interfaces.rdrv td (u * Rule30UOR.Core.twopow e - k) k (u * Rule30UOR.Core.twopow e - j) =
      Rule30UOR.Interfaces.rdrv td 0 k (u * Rule30UOR.Core.twopow e - j) :=
  Rule30Paper.Paper.rdrv_two_col_eq_white_seed_of_zero_gap td e J u k j hJ hj1 hjJ hkju

/-- **Derivation of `maskparity · 0` agreement when both `t + m * P` and `t` agree with the pure-drive evolution `rdrv t 0 s 1` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_both_eq_white_seed_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hw : Rule30UOR.Core.center (t + s) = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) s 1 = Rule30UOR.Interfaces.rdrv t 0 s 1 ∧
      Rule30UOR.Interfaces.rdrv t t s 1 = Rule30UOR.Interfaces.rdrv t 0 s 1) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_both_eq_white_seed T P hP hper m t s ht hw

/-- **Refutation of `CenterPeriodic` when both `t + m * P` and `t` agree with the pure-drive evolution `rdrv · 0 s 1` over `p + 3 * (m * P)` steps after a zero diagonal from the verified paper**. -/
theorem not_centerperiodic_of_both_eq_white_seed_at_zero_diag_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 =
          Rule30UOR.Interfaces.rdrv (z + (p + 1)) 0 s 1 ∧
        Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) s 1 =
          Rule30UOR.Interfaces.rdrv (z + (p + 1)) 0 s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_both_eq_white_seed_at_zero_diag T P m z p S hP hm ht hz hd hset1 hsetQ hS hw

/-- **First sub-diagonal step identity of the pure-drive right half (`rdrv td 0 (k + 2) (k + 1) = bxor (rdrv td 0 (k + 1) k) (center td)`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_one_step_kit
    (td k : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (k + 2) (k + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td 0 (k + 1) k) (Rule30UOR.Core.center td) :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_one_step td k

/-- **Period-`2` invariance of the first sub-diagonal of the pure-drive right half (`rdrv td 0 (k + 3) (k + 2) = rdrv td 0 (k + 1) k`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_one_period_two_kit
    (td k : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (k + 3) (k + 2) = Rule30UOR.Interfaces.rdrv td 0 (k + 1) k :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_one_period_two td k

/-- **Closed form of the first sub-diagonal of the pure-drive right half at even indices (`rdrv td 0 (2 * u + 1) (2 * u) = center (td + 1)`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_one_even_kit
    (td u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (2 * u + 1) (2 * u) = Rule30UOR.Core.center (td + 1) :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_one_even td u

/-- **Closed form of the first sub-diagonal of the pure-drive right half at odd indices (`rdrv td 0 (2 * u + 2) (2 * u + 1) = bxor (center (td + 1)) (center td)`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_one_odd_kit
    (td u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (2 * u + 2) (2 * u + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center (td + 1)) (Rule30UOR.Core.center td) :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_one_odd td u

/-- **Universal `2^d`-diagonal periodicity of the pure-drive right half (`rdrv td 0 ((k + d) + u * 2^d) (k + u * 2^d) = rdrv td 0 (k + d) k`, `kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_period_twopow_kit
    (td d k u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 ((k + d) + u * Rule30UOR.Core.twopow d) (k + u * Rule30UOR.Core.twopow d) =
      Rule30UOR.Interfaces.rdrv td 0 (k + d) k :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_period_twopow td d k u

/-- **Uniform `2^d`-diagonal periodicity across the first `d + 1` sub-diagonals of `rdrv td 0` (`p ≤ k → k - p ≤ d`) from the verified paper**. -/
theorem rdrv_white_seed_diag_shift_twopow_eq_kit
    (td d k p u : Nat) (hpk : p ≤ k) (hkd : k - p ≤ d) :
    Rule30UOR.Interfaces.rdrv td 0 (k + u * Rule30UOR.Core.twopow d) (p + u * Rule30UOR.Core.twopow d) =
      Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_white_seed_diag_shift_twopow_eq td d k p u hpk hkd

/-- **Universal dyadic-multiple scale identity of the pure-drive right half (`rdrv td 0 (d + u * 2^d) (u * 2^d) = center (td + d)`, `kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_scale_mult_eq_center_kit
    (td d u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (d + u * Rule30UOR.Core.twopow d) (u * Rule30UOR.Core.twopow d) =
      Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_white_seed_scale_mult_eq_center td d u

/-- **Universal dyadic scale identity of the pure-drive right half (`rdrv td 0 (d + 2^d) (2^d) = center (td + d)`, `kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_scale_eq_center_kit
    (td d : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (d + Rule30UOR.Core.twopow d) (Rule30UOR.Core.twopow d) =
      Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_white_seed_scale_eq_center td d

/-- **Universal high-scale identity of the pure-drive right half (`d ≤ k → rdrv td 0 (d + 2^k) (2^k) = center (td + d)`) from the verified paper**. -/
theorem rdrv_white_seed_scale_ge_eq_center_kit
    (td d k : Nat) (hdk : d ≤ k) :
    Rule30UOR.Interfaces.rdrv td 0 (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_white_seed_scale_ge_eq_center td d k hdk

/-- **Scale-doubling stabilization law of the pure-drive right half (`d ≤ k → rdrv td 0 (d + 2^(k+1)) (2^(k+1)) = rdrv td 0 (d + 2^k) (2^k)`) from the verified paper**. -/
theorem rdrv_white_seed_scale_double_eq_scale_kit
    (td d k : Nat) (hdk : d ≤ k) :
    Rule30UOR.Interfaces.rdrv td 0 (d + Rule30UOR.Core.twopow (k + 1)) (Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.rdrv td 0 (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) :=
  Rule30Paper.Paper.rdrv_white_seed_scale_double_eq_scale td d k hdk

/-- **Dyadic scale readout of `rdrv td tx` inside an initial right-half white band from the verified paper**. -/
theorem rdrv_scale_eq_center_of_initial_white_band_kit
    (td tx L d k : Nat)
    (hw : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hdk : d ≤ k) (hL : d + 2 * Rule30UOR.Core.twopow k ≤ L + 1) :
    Rule30UOR.Interfaces.rdrv td tx (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_scale_eq_center_of_initial_white_band td tx L d k hw hdk hL

/-- **Right-half dyadic scale identity inside an initial white band (`rhCenter (t + (d + 2^k)) (2^k) = center (t + d)`) from the verified paper**. -/
theorem rhcenter_scale_eq_center_of_initial_white_band_kit
    (t L d k : Nat)
    (hw : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter t (1 + i) = false)
    (hdk : d ≤ k) (hL : d + 2 * Rule30UOR.Core.twopow k ≤ L + 1) :
    Rule30UOR.Interfaces.rhCenter (t + (d + Rule30UOR.Core.twopow k)) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (t + d) :=
  Rule30Paper.Paper.rhcenter_scale_eq_center_of_initial_white_band t L d k hw hdk hL

/-- **Transfer of `2^d`-diagonal periodicity to `rdrv td tx` inside an initial white band from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_of_initial_white_band_kit
    (td tx L d k u : Nat)
    (hw : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hL : (k + u * Rule30UOR.Core.twopow d) + ((k + d) + u * Rule30UOR.Core.twopow d) ≤ L + 1) :
    Rule30UOR.Interfaces.rdrv td tx ((k + d) + u * Rule30UOR.Core.twopow d) (k + u * Rule30UOR.Core.twopow d) =
      Rule30UOR.Interfaces.rdrv td tx (k + d) k :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_of_initial_white_band td tx L d k u hw hL

/-- **Triangle-cone agreement of two same-drive right halves over shared initial white bands from the verified paper**. -/
theorem rdrv_eq_of_both_initial_white_band_kit
    (td tx2 tx L k p : Nat)
    (hw2 : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter tx2 (1 + i) = false)
    (hw1 : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hpk : p + k ≤ L + 1) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_eq_of_both_initial_white_band td tx2 tx L k p hw2 hw1 hpk

/-- **Periodic right-half triangle agreement over shared initial white bands from the verified paper**. -/
theorem periodic_rhcenter_shift_eq_of_both_initial_white_band_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L k p : Nat) (ht : T ≤ t)
    (hw2 : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter (t + m * P) (1 + i) = false)
    (hw1 : ∀ i : Nat, i ≤ L → Rule30UOR.Interfaces.rhCenter t (1 + i) = false)
    (hpk : p + k ≤ L + 1) :
    Rule30UOR.Interfaces.rhCenter ((t + m * P) + k) p = Rule30UOR.Interfaces.rhCenter (t + k) p :=
  Rule30Paper.Paper.periodic_rhcenter_shift_eq_of_both_initial_white_band T P hP hper m t L k p ht hw2 hw1 hpk

/-- **Main-diagonal step law of the driven right half `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_step_rhcenter_kit
    (td tx k : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) (k + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx k k)
        (Rule30UOR.Interfaces.rhCenter (tx + k) (k + 1) || Rule30UOR.Interfaces.rhCenter (tx + k) (k + 2)) :=
  Rule30Paper.Paper.rdrv_main_diag_step_rhcenter td tx k

/-- **Main-diagonal drive-defect constancy law of `rdrv` (`bxor (rdrv td2 tx k k) (rdrv td tx k k) = bxor (center td2) (center td)`) from the verified paper**. -/
theorem rdrv_main_diag_drive_defect_const_kit
    (td2 td tx k : Nat) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td2 tx k k) (Rule30UOR.Interfaces.rdrv td tx k k) =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center td2) (Rule30UOR.Core.center td) :=
  Rule30Paper.Paper.rdrv_main_diag_drive_defect_const td2 td tx k

/-- **Exact drive/state separation formula on the main diagonal of `rdrv` (`rdrv td tx k k = bxor (rhCenter (tx + k) k) (bxor (center td) (center tx))`, `kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_eq_rhcenter_xor_centers_kit
    (td tx k : Nat) :
    Rule30UOR.Interfaces.rdrv td tx k k =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (tx + k) k)
        (Rule30UOR.Core.bxor (Rule30UOR.Core.center td) (Rule30UOR.Core.center tx)) :=
  Rule30Paper.Paper.rdrv_main_diag_eq_rhcenter_xor_centers td tx k

/-- **Main-diagonal agreement of `rdrv td tx k k` with `rhCenter (tx + k) k` when `center td = center tx` from the verified paper**. -/
theorem rdrv_main_diag_eq_rhcenter_of_center_eq_kit
    (td tx k : Nat)
    (hc : Rule30UOR.Core.center td = Rule30UOR.Core.center tx) :
    Rule30UOR.Interfaces.rdrv td tx k k = Rule30UOR.Interfaces.rhCenter (tx + k) k :=
  Rule30Paper.Paper.rdrv_main_diag_eq_rhcenter_of_center_eq td tx k hc

/-- **Unattenuated drive-wavefront defect law along sub-diagonal `d` (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_wavefront_defect_const_kit
    (td2 td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td2 + j) = Rule30UOR.Core.center (td + j)) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td2 tx (p + d) p) (Rule30UOR.Interfaces.rdrv td tx (p + d) p) =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center (td2 + d)) (Rule30UOR.Core.center (td + d)) :=
  Rule30Paper.Paper.rdrv_drive_wavefront_defect_const td2 td tx d p hc

/-- **Exact drive-wavefront readout formula relative to `rhCenter` from the verified paper**. -/
theorem rdrv_drive_wavefront_eq_rhcenter_xor_kit
    (td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = Rule30UOR.Core.center (tx + j)) :
    Rule30UOR.Interfaces.rdrv td tx (p + d) p =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (tx + (p + d)) p)
        (Rule30UOR.Core.bxor (Rule30UOR.Core.center (td + d)) (Rule30UOR.Core.center (tx + d))) :=
  Rule30Paper.Paper.rdrv_drive_wavefront_eq_rhcenter_xor td tx d p hc

/-- **Exact drive-wavefront flip law at the first drive disagreement from the verified paper**. -/
theorem rdrv_drive_wavefront_flip_of_first_center_diff_kit
    (td2 td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td2 + j) = Rule30UOR.Core.center (td + j))
    (hdiff : Rule30UOR.Core.center (td2 + d) = !(Rule30UOR.Core.center (td + d))) :
    Rule30UOR.Interfaces.rdrv td2 tx (p + d) p = !(Rule30UOR.Interfaces.rdrv td tx (p + d) p) :=
  Rule30Paper.Paper.rdrv_drive_wavefront_flip_of_first_center_diff td2 td tx d p hc hdiff

/-- **1-step inward wavefront shielding by a black cell (`kit [33]`) from the verified paper**. -/
theorem rdrv_inward_agree_step_of_black_shield_kit
    (td tx2 tx k d : Nat)
    (hd0 : Rule30UOR.Interfaces.rdrv td tx2 k d = Rule30UOR.Interfaces.rdrv td tx k d)
    (hd1 : Rule30UOR.Interfaces.rdrv td tx2 k (d + 1) = Rule30UOR.Interfaces.rdrv td tx k (d + 1))
    (hb : Rule30UOR.Interfaces.rdrv td tx k (d + 1) = true) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (d + 1) = Rule30UOR.Interfaces.rdrv td tx (k + 1) (d + 1) :=
  Rule30Paper.Paper.rdrv_inward_agree_step_of_black_shield td tx2 tx k d hd0 hd1 hb

/-- **1-step inward wavefront defect transmission across a white cell from the verified paper**. -/
theorem rdrv_inward_defect_step_of_white_shield_kit
    (td tx2 tx k d : Nat)
    (hd0 : Rule30UOR.Interfaces.rdrv td tx2 k d = Rule30UOR.Interfaces.rdrv td tx k d)
    (hd1 : Rule30UOR.Interfaces.rdrv td tx2 k (d + 1) = Rule30UOR.Interfaces.rdrv td tx k (d + 1))
    (hw : Rule30UOR.Interfaces.rdrv td tx k (d + 1) = false) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (d + 1)) (Rule30UOR.Interfaces.rdrv td tx (k + 1) (d + 1)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx2 k (d + 2)) (Rule30UOR.Interfaces.rdrv td tx k (d + 2)) :=
  Rule30Paper.Paper.rdrv_inward_defect_step_of_white_shield td tx2 tx k d hd0 hd1 hw

/-- **1-step inward agreement from three-column agreement from the verified paper**. -/
theorem rdrv_inward_agree_step_of_three_agree_kit
    (td tx2 tx k d : Nat)
    (hd0 : Rule30UOR.Interfaces.rdrv td tx2 k d = Rule30UOR.Interfaces.rdrv td tx k d)
    (hd1 : Rule30UOR.Interfaces.rdrv td tx2 k (d + 1) = Rule30UOR.Interfaces.rdrv td tx k (d + 1))
    (hd2 : Rule30UOR.Interfaces.rdrv td tx2 k (d + 2) = Rule30UOR.Interfaces.rdrv td tx k (d + 2)) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + 1) (d + 1) = Rule30UOR.Interfaces.rdrv td tx (k + 1) (d + 1) :=
  Rule30Paper.Paper.rdrv_inward_agree_step_of_three_agree td tx2 tx k d hd0 hd1 hd2

/-- **Inward wavefront defect transmission outside `RhBandAgree` across a white boundary cell from the verified paper**. -/
theorem rdrv_init_wavefront_defect_of_white_kit
    (td tx Q L d k : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 L) (hdk : d + k ≤ L)
    (hw : Rule30UOR.Interfaces.rdrv td tx k (d + 1) = false) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td (tx + Q) (k + 1) (d + 1)) (Rule30UOR.Interfaces.rdrv td tx (k + 1) (d + 1)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td (tx + Q) k (d + 2)) (Rule30UOR.Interfaces.rdrv td tx k (d + 2)) :=
  Rule30Paper.Paper.rdrv_init_wavefront_defect_of_white td tx Q L d k hband hdk hw

/-- **Inward wavefront absorption outside `RhBandAgree` by a black boundary cell (`kit [33]`) from the verified paper**. -/
theorem rdrv_init_wavefront_absorb_of_black_kit
    (td tx Q L d k : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 L) (hdk : d + k ≤ L)
    (hb : Rule30UOR.Interfaces.rdrv td tx k (d + 1) = true) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) (k + 1) (d + 1) = Rule30UOR.Interfaces.rdrv td tx (k + 1) (d + 1) :=
  Rule30Paper.Paper.rdrv_init_wavefront_absorb_of_black td tx Q L d k hband hdk hb

/-- **Inward wavefront agreement propagation along `p + k = L + 2` from the verified paper**. -/
theorem rdrv_init_wavefront_agree_propagate_kit
    (td tx Q L d k j : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 L)
    (hd : d + (k + j) ≤ L + 1)
    (h0 : Rule30UOR.Interfaces.rdrv td (tx + Q) k ((d + 1) + j) = Rule30UOR.Interfaces.rdrv td tx k ((d + 1) + j)) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) (k + j) (d + 1) = Rule30UOR.Interfaces.rdrv td tx (k + j) (d + 1) :=
  Rule30Paper.Paper.rdrv_init_wavefront_agree_propagate td tx Q L d k j hband hd h0

/-- **Extension of column-`1` agreement from `L` to `L + 1` by a single black shield cell (`kit [33]`) from the verified paper**. -/
theorem rdrv_init_wavefront_col_one_agree_of_black_shield_kit
    (td tx Q L k : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 L) (hk : k ≤ L)
    (hb : Rule30UOR.Interfaces.rdrv td tx k ((L + 1) - k) = true) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) (L + 1) 1 = Rule30UOR.Interfaces.rdrv td tx (L + 1) 1 :=
  Rule30Paper.Paper.rdrv_init_wavefront_col_one_agree_of_black_shield td tx Q L k hband hk hb

/-- **Extension of `maskparity · 0` agreement from `L` to `L + 1` by a single black shield cell from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rhbandagree_and_black_shield_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L k s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 L) (hk : k ≤ L)
    (hb : Rule30UOR.Interfaces.rdrv t t k ((L + 1) - k) = true) (hs : s ≤ L + 1) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rhbandagree_and_black_shield T P hP hper m t L k s ht hband hk hb hs

/-- **Bounded-width strip determination of `rdrv` requiring boundary column `B + 2` agreement only when column `B + 1` is white (`kit [33]`) from the verified paper**. -/
theorem rdrv_strip_agree_of_white_boundary_col_agree_kit
    (td tx Q B S s p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hcol : ∀ u : Nat, u < S →
      Rule30UOR.Interfaces.rdrv td tx u (B + 1) = false →
      Rule30UOR.Interfaces.rdrv td (tx + Q) u (B + 2) = Rule30UOR.Interfaces.rdrv td tx u (B + 2))
    (hs : s ≤ S) (hp : p ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) s p = Rule30UOR.Interfaces.rdrv td tx s p :=
  Rule30Paper.Paper.rdrv_strip_agree_of_white_boundary_col_agree td tx Q B S s p hband hcol hs hp

/-- **Bounded-width strip shielding by a black boundary column `B + 1` (`kit [33]`) from the verified paper**. -/
theorem rdrv_strip_agree_of_black_boundary_col_kit
    (td tx Q B S s p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hb : ∀ u : Nat, u < S → Rule30UOR.Interfaces.rdrv td tx u (B + 1) = true)
    (hs : s ≤ S) (hp : p ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) s p = Rule30UOR.Interfaces.rdrv td tx s p :=
  Rule30Paper.Paper.rdrv_strip_agree_of_black_boundary_col td tx Q B S s p hband hb hs hp

/-- **Derivation of `maskparity · 0` agreement over `[t, t + S]` from a black boundary column `B + 1` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_black_boundary_col_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B S s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hb : ∀ u : Nat, u < S → Rule30UOR.Interfaces.rdrv t t u (B + 1) = true) (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_black_boundary_col T P hP hper m t B S s ht hband hb hs

/-- **First sub-diagonal step flip law at a black main-diagonal gate (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_step_of_black_main_diag_kit
    (td tx k : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx (k + 1) (k + 1) = true) :
    Rule30UOR.Interfaces.rdrv td tx (k + 2) (k + 1) = !(Rule30UOR.Interfaces.rdrv td tx (k + 1) k) :=
  Rule30Paper.Paper.rdrv_subdiag_one_step_of_black_main_diag td tx k hb

/-- **First sub-diagonal step law at a white main-diagonal gate from the verified paper**. -/
theorem rdrv_subdiag_one_step_of_white_main_diag_kit
    (td tx k : Nat)
    (hw : Rule30UOR.Interfaces.rdrv td tx (k + 1) (k + 1) = false) :
    Rule30UOR.Interfaces.rdrv td tx (k + 2) (k + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (k + 1) k)
        (Rule30UOR.Interfaces.rhCenter (tx + (k + 1)) (k + 2)) :=
  Rule30Paper.Paper.rdrv_subdiag_one_step_of_white_main_diag td tx k hw

/-- **Main-diagonal gate determination theorem for the entire drive cone `p ≤ k` (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_cone_agree_of_main_diag_gate_kit
    (td tx2 tx k p : Nat)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ k → Rule30UOR.Interfaces.rdrv td tx2 u u = Rule30UOR.Interfaces.rdrv td tx u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ k →
      Rule30UOR.Interfaces.rdrv td tx u u = false →
      Rule30UOR.Interfaces.rdrv td tx2 u (u + 1) = Rule30UOR.Interfaces.rdrv td tx u (u + 1))
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_drive_cone_agree_of_main_diag_gate td tx2 tx k p hdiag hgate hpk

/-- **Total drive-cone shielding by a black main diagonal (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_cone_agree_of_black_main_diag_kit
    (td tx2 tx k p : Nat)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ k → Rule30UOR.Interfaces.rdrv td tx2 u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ k → Rule30UOR.Interfaces.rdrv td tx u u = true)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_drive_cone_agree_of_black_main_diag td tx2 tx k p hb2 hb1 hpk

/-- **Exact collapse of the drive cone `p ≤ k` to the pure-drive right half `rdrv td 0` under a black main diagonal (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_cone_eq_white_seed_of_black_main_diag_kit
    (td tx k p : Nat)
    (hc : Rule30UOR.Core.center td = true)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ k → Rule30UOR.Interfaces.rdrv td tx u u = true)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_drive_cone_eq_white_seed_of_black_main_diag td tx k p hc hb hpk

/-- **Exact collapse of `rdrv td tx` to `rdrv td 0` inside `p ≤ k` when `rhCenter (tx + u) u = true` from the verified paper**. -/
theorem rdrv_drive_cone_eq_white_seed_of_black_center_and_rhcenter_diag_kit
    (td tx k p : Nat)
    (hcd : Rule30UOR.Core.center td = true)
    (hcx : Rule30UOR.Core.center tx = true)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ k → Rule30UOR.Interfaces.rhCenter (tx + u) u = true)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_drive_cone_eq_white_seed_of_black_center_and_rhcenter_diag td tx k p hcd hcx hb hpk

/-- **Exact collapse of `rhCenter (t + k) p` to the pure-drive right half `rdrv t 0 k p` inside `p ≤ k` from the verified paper**. -/
theorem rhcenter_drive_cone_eq_white_seed_of_black_diag_kit
    (t k p : Nat)
    (hc : Rule30UOR.Core.center t = true)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ k → Rule30UOR.Interfaces.rhCenter (t + u) u = true)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + k) p = Rule30UOR.Interfaces.rdrv t 0 k p :=
  Rule30Paper.Paper.rhcenter_drive_cone_eq_white_seed_of_black_diag t k p hc hb hpk

/-- **Derivation of `maskparity · 0` agreement from main-diagonal gate agreement (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_main_diag_gate_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ s →
      Rule30UOR.Interfaces.rdrv t (t + m * P) u u = Rule30UOR.Interfaces.rdrv t t u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ s →
      Rule30UOR.Interfaces.rdrv t t u u = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) u (u + 1) = Rule30UOR.Interfaces.rdrv t t u (u + 1)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_main_diag_gate T P hP hper m t s ht hs hdiag hgate

/-- **Derivation of `maskparity · 0` agreement from a black main-diagonal gate from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_black_main_diag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ s → Rule30UOR.Interfaces.rdrv t (t + m * P) u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ s → Rule30UOR.Interfaces.rdrv t t u u = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_black_main_diag T P hP hper m t s ht hs hb2 hb1

/-- **Zero-diagonal refutation of `CenterPeriodic` from main-diagonal gate agreement from the verified paper**. -/
theorem not_centerperiodic_of_main_diag_gate_at_zero_diag_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 →
      Rule30UOR.Interfaces.rdrv (z + p) ((z + p) + m * P) u u = Rule30UOR.Interfaces.rdrv (z + p) (z + p) u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 →
      Rule30UOR.Interfaces.rdrv (z + p) (z + p) u u = false →
      Rule30UOR.Interfaces.rdrv (z + p) ((z + p) + m * P) u (u + 1) = Rule30UOR.Interfaces.rdrv (z + p) (z + p) u (u + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_main_diag_gate_at_zero_diag T P m z p S hP hm ht hz hd hset1 hset2 hS hdiag hgate

/-- **Zero-diagonal refutation of `CenterPeriodic` from a black main-diagonal gate from the verified paper**. -/
theorem not_centerperiodic_of_black_main_diag_at_zero_diag_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 → Rule30UOR.Interfaces.rdrv (z + p) ((z + p) + m * P) u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 → Rule30UOR.Interfaces.rdrv (z + p) (z + p) u u = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_main_diag_at_zero_diag T P m z p S hP hm ht hz hd hset1 hset2 hS hb2 hb1

/-- **Zero-diagonal refutation of `CenterPeriodic` from a black boundary column `B + 1` from the verified paper**. -/
theorem not_centerperiodic_of_black_boundary_col_at_zero_diag_kit
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hb : ∀ u : Nat, u < S → Rule30UOR.Interfaces.rdrv (z + (p + 1)) (z + (p + 1)) u (B + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_boundary_col_at_zero_diag T P m z p B S hP hm ht hz hd hset1 hset2 hS hband hb

/-- **Main-diagonal agreement of `rdrv` from 2-cell super-diagonal corridor OR agreement (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_agree_of_corridor_or_agree_kit
    (td tx2 tx k : Nat)
    (hor : ∀ u : Nat, u < k →
      (Rule30UOR.Interfaces.rhCenter (tx2 + u) (u + 1) || Rule30UOR.Interfaces.rhCenter (tx2 + u) (u + 2)) =
      (Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) || Rule30UOR.Interfaces.rhCenter (tx + u) (u + 2))) :
    Rule30UOR.Interfaces.rdrv td tx2 k k = Rule30UOR.Interfaces.rdrv td tx k k :=
  Rule30Paper.Paper.rdrv_main_diag_agree_of_corridor_or_agree td tx2 tx k hor

/-- **Main-diagonal constancy `rdrv td tx k k = center td` under a 2-cell white super-diagonal corridor (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_eq_center_of_white_corridor_kit
    (td tx k : Nat)
    (hw : ∀ u : Nat, u < k →
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) = false ∧
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 2) = false) :
    Rule30UOR.Interfaces.rdrv td tx k k = Rule30UOR.Core.center td :=
  Rule30Paper.Paper.rdrv_main_diag_eq_center_of_white_corridor td tx k hw

/-- **2-cell super-diagonal corridor determination of the entire drive cone `p ≤ k` (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_cone_agree_of_corridor_gate_kit
    (td tx2 tx k p : Nat)
    (hc1 : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (tx2 + u) (u + 1) = Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) = false →
      Rule30UOR.Interfaces.rhCenter (tx2 + u) (u + 2) = Rule30UOR.Interfaces.rhCenter (tx + u) (u + 2))
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_drive_cone_agree_of_corridor_gate td tx2 tx k p hc1 hc2 hpk

/-- **Single black first-super-diagonal shielding of the entire drive cone `p ≤ k` (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_cone_agree_of_black_first_superdiag_kit
    (td tx2 tx k p : Nat)
    (hb2 : ∀ u : Nat, u ≤ k → Rule30UOR.Interfaces.rhCenter (tx2 + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ k → Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) = true)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_drive_cone_agree_of_black_first_superdiag td tx2 tx k p hb2 hb1 hpk

/-- **Exact collapse of the drive cone `p ≤ k` to the pure-drive right half `rdrv td 0` under a 2-cell white super-diagonal corridor (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_cone_eq_white_seed_of_white_corridor_kit
    (td tx k p : Nat)
    (hw : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) = false ∧
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 2) = false)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_drive_cone_eq_white_seed_of_white_corridor td tx k p hw hpk

/-- **Exact collapse of `rhCenter (t + k) p` to `rdrv t 0 k p` inside `p ≤ k` under a 2-cell white super-diagonal corridor from the verified paper**. -/
theorem rhcenter_drive_cone_eq_white_seed_of_white_corridor_kit
    (t k p : Nat)
    (hw : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (t + u) (u + 1) = false ∧
      Rule30UOR.Interfaces.rhCenter (t + u) (u + 2) = false)
    (hpk : p ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + k) p = Rule30UOR.Interfaces.rdrv t 0 k p :=
  Rule30Paper.Paper.rhcenter_drive_cone_eq_white_seed_of_white_corridor t k p hw hpk

/-- **Dyadic scale readout of `rdrv td tx` under a black main diagonal (`kit [33]`) from the verified paper**. -/
theorem rdrv_scale_eq_center_of_black_main_diag_kit
    (td tx d k : Nat)
    (hc : Rule30UOR.Core.center td = true) (hdk : d ≤ k)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ d + Rule30UOR.Core.twopow k → Rule30UOR.Interfaces.rdrv td tx u u = true) :
    Rule30UOR.Interfaces.rdrv td tx (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_scale_eq_center_of_black_main_diag td tx d k hc hdk hb

/-- **Right-half dyadic scale identity under a black main diagonal from the verified paper**. -/
theorem rhcenter_scale_eq_center_of_black_diag_kit
    (t d k : Nat)
    (hc : Rule30UOR.Core.center t = true) (hdk : d ≤ k)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ d + Rule30UOR.Core.twopow k → Rule30UOR.Interfaces.rhCenter (t + u) u = true) :
    Rule30UOR.Interfaces.rhCenter (t + (d + Rule30UOR.Core.twopow k)) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (t + d) :=
  Rule30Paper.Paper.rhcenter_scale_eq_center_of_black_diag t d k hc hdk hb

/-- **Dyadic scale readout of `rdrv td tx` under a 2-cell white super-diagonal corridor (`kit [33]`) from the verified paper**. -/
theorem rdrv_scale_eq_center_of_white_corridor_kit
    (td tx d k : Nat)
    (hdk : d ≤ k)
    (hw : ∀ u : Nat, u ≤ d + Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) = false ∧
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + 2) = false) :
    Rule30UOR.Interfaces.rdrv td tx (d + Rule30UOR.Core.twopow k) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_scale_eq_center_of_white_corridor td tx d k hdk hw

/-- **Right-half dyadic scale identity under a 2-cell white super-diagonal corridor from the verified paper**. -/
theorem rhcenter_scale_eq_center_of_white_corridor_kit
    (t d k : Nat)
    (hdk : d ≤ k)
    (hw : ∀ u : Nat, u ≤ d + Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (t + u) (u + 1) = false ∧
      Rule30UOR.Interfaces.rhCenter (t + u) (u + 2) = false) :
    Rule30UOR.Interfaces.rhCenter (t + (d + Rule30UOR.Core.twopow k)) (Rule30UOR.Core.twopow k) =
      Rule30UOR.Core.center (t + d) :=
  Rule30Paper.Paper.rhcenter_scale_eq_center_of_white_corridor t d k hdk hw

/-- **Transfer of `2^d`-diagonal periodicity to `rdrv td tx` under a black main diagonal from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_of_black_main_diag_kit
    (td tx d k u : Nat)
    (hc : Rule30UOR.Core.center td = true)
    (hb : ∀ j : Nat, 1 ≤ j → j ≤ (k + d) + u * Rule30UOR.Core.twopow d → Rule30UOR.Interfaces.rdrv td tx j j = true) :
    Rule30UOR.Interfaces.rdrv td tx ((k + d) + u * Rule30UOR.Core.twopow d) (k + u * Rule30UOR.Core.twopow d) =
      Rule30UOR.Interfaces.rdrv td tx (k + d) k :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_of_black_main_diag td tx d k u hc hb

/-- **Derivation of `maskparity · 0` agreement from 2-cell super-diagonal corridor agreement (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_corridor_gate_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hc1 : ∀ u : Nat, u ≤ s →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + 1) = Rule30UOR.Interfaces.rhCenter (t + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ s →
      Rule30UOR.Interfaces.rhCenter (t + u) (u + 1) = false →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + 2) = Rule30UOR.Interfaces.rhCenter (t + u) (u + 2)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_corridor_gate T P hP hper m t s ht hs hc1 hc2

/-- **Derivation of `maskparity · 0` agreement from a single black first super-diagonal from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_black_first_superdiag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hb2 : ∀ u : Nat, u ≤ s → Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ s → Rule30UOR.Interfaces.rhCenter (t + u) (u + 1) = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_black_first_superdiag T P hP hper m t s ht hs hb2 hb1

/-- **Zero-diagonal refutation of `CenterPeriodic` from 2-cell super-diagonal corridor agreement from the verified paper**. -/
theorem not_centerperiodic_of_corridor_gate_at_zero_diag_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S + 1 →
      Rule30UOR.Interfaces.rhCenter (((z + p) + m * P) + u) (u + 1) = Rule30UOR.Interfaces.rhCenter ((z + p) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S + 1 →
      Rule30UOR.Interfaces.rhCenter ((z + p) + u) (u + 1) = false →
      Rule30UOR.Interfaces.rhCenter (((z + p) + m * P) + u) (u + 2) = Rule30UOR.Interfaces.rhCenter ((z + p) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_corridor_gate_at_zero_diag T P m z p S hP hm ht hz hd hset1 hset2 hS hc1 hc2

/-- **Zero-diagonal refutation of `CenterPeriodic` from a single black first super-diagonal from the verified paper**. -/
theorem not_centerperiodic_of_black_first_superdiag_at_zero_diag_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p) (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S + 1 → Rule30UOR.Interfaces.rhCenter (((z + p) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S + 1 → Rule30UOR.Interfaces.rhCenter ((z + p) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_first_superdiag_at_zero_diag T P m z p S hP hm ht hz hd hset1 hset2 hS hb2 hb1

/-- **All-black first sub-diagonal of `rdrv td 0` when `(center td, center (td + 1)) = (false, true)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_eq_true_of_false_true_kit
    (td u : Nat)
    (hc0 : Rule30UOR.Core.center td = false)
    (hc1 : Rule30UOR.Core.center (td + 1) = true) :
    Rule30UOR.Interfaces.rdrv td 0 (u + 1) u = true :=
  Rule30Paper.Paper.rdrv_subdiag_one_eq_true_of_false_true td u hc0 hc1

/-- **Vanishing of `rdrv td 0 k p` above sub-diagonal `d` under a length-`d` white drive prefix from the verified paper**. -/
theorem rdrv_white_seed_eq_false_of_white_drive_prefix_kit
    (td d k p : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false)
    (hkp : k < p + d) :
    Rule30UOR.Interfaces.rdrv td 0 k p = false :=
  Rule30Paper.Paper.rdrv_white_seed_eq_false_of_white_drive_prefix td d k p hw hkp

/-- **Exact time-shift law of `rdrv td 0` under a length-`d` white drive prefix (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_shift_of_white_drive_prefix_kit
    (td d k p : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false) :
    Rule30UOR.Interfaces.rdrv td 0 (d + k) p = Rule30UOR.Interfaces.rdrv (td + d) 0 k p :=
  Rule30Paper.Paper.rdrv_white_seed_shift_of_white_drive_prefix td d k p hw

/-- **Sub-diagonal `d` constancy of `rdrv td 0` under a length-`d` white drive prefix from the verified paper**. -/
theorem rdrv_white_seed_subdiag_eq_center_of_white_drive_prefix_kit
    (td d u : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false) :
    Rule30UOR.Interfaces.rdrv td 0 (u + d) u = Rule30UOR.Core.center (td + d) :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_eq_center_of_white_drive_prefix td d u hw

/-- **Sub-diagonal `d` gate determination of the entire sub-cone `p + d ≤ k` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subcone_agree_of_subdiag_gate_kit
    (td tx2 tx d k p : Nat)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ k →
      Rule30UOR.Interfaces.rdrv td tx2 (u + d) u = Rule30UOR.Interfaces.rdrv td tx (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ k →
      Rule30UOR.Interfaces.rdrv td tx (u + d) u = false →
      Rule30UOR.Interfaces.rdrv td tx2 (u + d) (u + 1) = Rule30UOR.Interfaces.rdrv td tx (u + d) (u + 1))
    (hpk : p + d ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_subcone_agree_of_subdiag_gate td tx2 tx d k p hdiag hgate hpk

/-- **Total sub-cone shielding `p + d ≤ k` by a black sub-diagonal `d` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subcone_agree_of_black_subdiag_kit
    (td tx2 tx d k p : Nat)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ k → Rule30UOR.Interfaces.rdrv td tx2 (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ k → Rule30UOR.Interfaces.rdrv td tx (u + d) u = true)
    (hpk : p + d ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_subcone_agree_of_black_subdiag td tx2 tx d k p hb2 hb1 hpk

/-- **Collapse of the sub-cone `p + d ≤ k` to `rdrv td 0` under a white prefix and black sub-diagonal `d` from the verified paper**. -/
theorem rdrv_subcone_eq_white_seed_of_white_prefix_and_black_subdiag_kit
    (td tx d k p : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false)
    (hcd : Rule30UOR.Core.center (td + d) = true)
    (hb : ∀ u : Nat, 1 ≤ u → u + d ≤ k → Rule30UOR.Interfaces.rdrv td tx (u + d) u = true)
    (hpk : p + d ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_subcone_eq_white_seed_of_white_prefix_and_black_subdiag td tx d k p hw hcd hb hpk

/-- **Collapse of the sub-cone `p + 1 ≤ k` to `rdrv td 0` under `(center td, center (td + 1)) = (false, true)` and a black sub-diagonal `1` from the verified paper**. -/
theorem rdrv_subcone_one_eq_white_seed_of_false_true_and_black_subdiag_one_kit
    (td tx k p : Nat)
    (hc0 : Rule30UOR.Core.center td = false)
    (hc1 : Rule30UOR.Core.center (td + 1) = true)
    (hb : ∀ u : Nat, 1 ≤ u → u + 1 ≤ k → Rule30UOR.Interfaces.rdrv td tx (u + 1) u = true)
    (hpk : p + 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_subcone_one_eq_white_seed_of_false_true_and_black_subdiag_one td tx k p hc0 hc1 hb hpk

/-- **Derivation of `maskparity · 0` agreement from sub-diagonal `d` gate agreement (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_subdiag_gate_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t d s : Nat) (ht : T ≤ t) (hs : 1 + d ≤ s)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ s →
      Rule30UOR.Interfaces.rdrv t (t + m * P) (u + d) u = Rule30UOR.Interfaces.rdrv t t (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ s →
      Rule30UOR.Interfaces.rdrv t t (u + d) u = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) (u + d) (u + 1) = Rule30UOR.Interfaces.rdrv t t (u + d) (u + 1)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_subdiag_gate T P hP hper m t d s ht hs hdiag hgate

/-- **Derivation of `maskparity · 0` agreement from a black sub-diagonal `d` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_black_subdiag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t d s : Nat) (ht : T ≤ t) (hs : 1 + d ≤ s)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ s → Rule30UOR.Interfaces.rdrv t (t + m * P) (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ s → Rule30UOR.Interfaces.rdrv t t (u + d) u = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_black_subdiag T P hP hper m t d s ht hs hb2 hb1

/-- **Zero-diagonal refutation of `CenterPeriodic` from sub-diagonal `d` gate agreement from the verified paper**. -/
theorem not_centerperiodic_of_subdiag_gate_at_zero_diag_kit
    (T P m z p t d S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htd : t + (d + 1) = z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) →
      Rule30UOR.Interfaces.rdrv t (t + m * P) (u + d) u = Rule30UOR.Interfaces.rdrv t t (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) →
      Rule30UOR.Interfaces.rdrv t t (u + d) u = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) (u + d) (u + 1) = Rule30UOR.Interfaces.rdrv t t (u + d) (u + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_subdiag_gate_at_zero_diag T P m z p t d S hP hm ht htd hz hd hset1 hset2 hS hdiag hgate

/-- **Zero-diagonal refutation of `CenterPeriodic` from a black sub-diagonal `d` from the verified paper**. -/
theorem not_centerperiodic_of_black_subdiag_at_zero_diag_kit
    (T P m z p t d S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htd : t + (d + 1) = z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) → Rule30UOR.Interfaces.rdrv t (t + m * P) (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) → Rule30UOR.Interfaces.rdrv t t (u + d) u = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_subdiag_at_zero_diag T P m z p t d S hP hm ht htd hz hd hset1 hset2 hS hb2 hb1

/-- **Black wavefront generation at a white `rhCenter` cell when the drive flips at `d` (`kit [33]`) from the verified paper**. -/
theorem rdrv_drive_wavefront_eq_true_of_first_diff_and_white_rhcenter_kit
    (td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = Rule30UOR.Core.center (tx + j))
    (hdiff : Rule30UOR.Core.center (td + d) = !(Rule30UOR.Core.center (tx + d)))
    (hw : Rule30UOR.Interfaces.rhCenter (tx + (p + d)) p = false) :
    Rule30UOR.Interfaces.rdrv td tx (p + d) p = true :=
  Rule30Paper.Paper.rdrv_drive_wavefront_eq_true_of_first_diff_and_white_rhcenter td tx d p hc hdiff hw

/-- **Exact readout `rdrv td tx (p + d) p = rhCenter (tx + (p + d)) p` under center prefix agreement up to `d` from the verified paper**. -/
theorem rdrv_drive_wavefront_eq_rhcenter_of_center_prefix_eq_kit
    (td tx d p : Nat)
    (hc : ∀ j : Nat, j ≤ d → Rule30UOR.Core.center (td + j) = Rule30UOR.Core.center (tx + j)) :
    Rule30UOR.Interfaces.rdrv td tx (p + d) p = Rule30UOR.Interfaces.rhCenter (tx + (p + d)) p :=
  Rule30Paper.Paper.rdrv_drive_wavefront_eq_rhcenter_of_center_prefix_eq td tx d p hc

/-- **Exact sub-diagonal readout of `rdrv t (t + m * P)` under `CenterPeriodic` from the verified paper**. -/
theorem periodic_rdrv_subdiag_eq_rhcenter_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t d p : Nat) (ht : T ≤ t) :
    Rule30UOR.Interfaces.rdrv t (t + m * P) (p + d) p =
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + (p + d)) p :=
  Rule30Paper.Paper.periodic_rdrv_subdiag_eq_rhcenter T P hP hper m t d p ht

/-- **Expanding trapezoid determination `p ≤ k + (B + 1)` from `RhBandAgree tx Q 1 B` and a super-diagonal gate on `(u, u + (B + 1))` (`kit [33]`) from the verified paper**. -/
theorem rdrv_trapezoid_agree_of_superdiag_gate_kit
    (td tx Q B k p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hc1 : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter ((tx + Q) + u) (u + (B + 1)) =
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter ((tx + Q) + u) (u + (B + 2)) =
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + (B + 2)))
    (hpk : p ≤ k + (B + 1)) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_trapezoid_agree_of_superdiag_gate td tx Q B k p hband hc1 hc2 hpk

/-- **Expanding trapezoid shielding `p ≤ k + (B + 1)` by a black super-diagonal `(u, u + (B + 1))` (`kit [33]`) from the verified paper**. -/
theorem rdrv_trapezoid_agree_of_black_superdiag_kit
    (td tx Q B k p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hb2 : ∀ u : Nat, u ≤ k → Rule30UOR.Interfaces.rhCenter ((tx + Q) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ k → Rule30UOR.Interfaces.rhCenter (tx + u) (u + (B + 1)) = true)
    (hpk : p ≤ k + (B + 1)) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_trapezoid_agree_of_black_superdiag td tx Q B k p hband hb2 hb1 hpk

/-- **Exact collapse of the expanding trapezoid `p ≤ k + (B + 1)` to `rdrv td 0` under an initial white band and 2-cell white super-diagonal corridor (`kit [33]`) from the verified paper**. -/
theorem rdrv_trapezoid_eq_white_seed_of_white_band_and_corridor_kit
    (td tx B k p : Nat)
    (hwb : ∀ i : Nat, i ≤ B → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hwc : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + (B + 1)) = false ∧
      Rule30UOR.Interfaces.rhCenter (tx + u) (u + (B + 2)) = false)
    (hpk : p ≤ k + (B + 1)) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_trapezoid_eq_white_seed_of_white_band_and_corridor td tx B k p hwb hwc hpk

/-- **Exact collapse of `rhCenter (t + k) p` to `rdrv t 0 k p` inside the expanding trapezoid `p ≤ k + (B + 1)` from the verified paper**. -/
theorem rhcenter_trapezoid_eq_white_seed_of_white_band_and_corridor_kit
    (t B k p : Nat)
    (hwb : ∀ i : Nat, i ≤ B → Rule30UOR.Interfaces.rhCenter t (1 + i) = false)
    (hwc : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 1)) = false ∧
      Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 2)) = false)
    (hpk : p ≤ k + (B + 1)) :
    Rule30UOR.Interfaces.rhCenter (t + k) p = Rule30UOR.Interfaces.rdrv t 0 k p :=
  Rule30Paper.Paper.rhcenter_trapezoid_eq_white_seed_of_white_band_and_corridor t B k p hwb hwc hpk

/-- **Derivation of `maskparity · 0` agreement from `RhBandAgree t (m * P) 1 B` and a super-diagonal `(u, u + (B + 1))` gate (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_superdiag_gate_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ s →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + (B + 1)) =
      Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ s →
      Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + (B + 2)) =
      Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 2))) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_superdiag_gate T P hP hper m t B s ht hband hc1 hc2

/-- **Derivation of `maskparity · 0` agreement from `RhBandAgree t (m * P) 1 B` and a black super-diagonal `(u, u + (B + 1))` from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_black_superdiag_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hb2 : ∀ u : Nat, u ≤ s → Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ s → Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 1)) = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_black_superdiag T P hP hper m t B s ht hband hb2 hb1

/-- **Zero-diagonal refutation of `CenterPeriodic` from `RhBandAgree` and a super-diagonal `(u, u + (B + 1))` gate from the verified paper**. -/
theorem not_centerperiodic_of_superdiag_gate_at_zero_diag_kit
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 1)) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 2)) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_superdiag_gate_at_zero_diag T P m z p B S hP hm ht hz hd hset1 hset2 hS hband hc1 hc2

/-- **Zero-diagonal refutation of `CenterPeriodic` from `RhBandAgree` and a black super-diagonal `(u, u + (B + 1))` from the verified paper**. -/
theorem not_centerperiodic_of_black_superdiag_at_zero_diag_kit
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hb2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + (B + 1)) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_superdiag_at_zero_diag T P m z p B S hP hm ht hz hd hset1 hset2 hS hband hb2 hb1

/-- **Full-horizon (`s ≥ 0`) derivation of `maskparity · 0` agreement from 2-cell super-diagonal corridor agreement (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_corridor_gate_all_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hc1 : ∀ u : Nat, u ≤ s →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + 1) = Rule30UOR.Interfaces.rhCenter (t + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ s →
      Rule30UOR.Interfaces.rhCenter (t + u) (u + 1) = false →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + 2) = Rule30UOR.Interfaces.rhCenter (t + u) (u + 2)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_corridor_gate_all T P hP hper m t s ht hc1 hc2

/-- **Full-horizon (`s ≥ 0`) derivation of `maskparity · 0` agreement from a single black first super-diagonal from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_black_first_superdiag_all_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hb2 : ∀ u : Nat, u ≤ s → Rule30UOR.Interfaces.rhCenter ((t + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ s → Rule30UOR.Interfaces.rhCenter (t + u) (u + 1) = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_black_first_superdiag_all T P hP hper m t s ht hb2 hb1

/-- **Direct zero-diagonal refutation of `CenterPeriodic` at `z + (p + 1)` from the 2-cell super-diagonal corridor gate from the verified paper**. -/
theorem not_centerperiodic_of_corridor_gate_at_zero_diag_direct_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + u) (u + 1) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + 1) = false →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + u) (u + 2) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_corridor_gate_at_zero_diag_direct T P m z p S hP hm ht hz hd hset1 hset2 hS hc1 hc2

/-- **Direct zero-diagonal refutation of `CenterPeriodic` at `z + (p + 1)` from a single black first super-diagonal from the verified paper**. -/
theorem not_centerperiodic_of_black_first_superdiag_at_zero_diag_direct_kit
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_first_superdiag_at_zero_diag_direct T P m z p S hP hm ht hz hd hset1 hset2 hS hb2 hb1

/-- **Dyadic-window refutation of `CenterPeriodic` from the 2-cell super-diagonal corridor gate from the verified paper**. -/
theorem not_centerperiodic_of_corridor_gate_sub_twopow_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ Rule30UOR.Core.twopow k) (ht : T + m * P ≤ Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + m * P) + u) (u + 1) =
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + 1) = false →
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + m * P) + u) (u + 2) =
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_corridor_gate_sub_twopow T P m k S hP hm hmP ht hS hc1 hc2

/-- **Dyadic-window refutation of `CenterPeriodic` from a single black first super-diagonal from the verified paper**. -/
theorem not_centerperiodic_of_black_first_superdiag_sub_twopow_kit
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ Rule30UOR.Core.twopow k) (ht : T + m * P ≤ Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_black_first_superdiag_sub_twopow T P m k S hP hm hmP ht hS hb2 hb1

/-- **Dyadic-window refutation of `CenterPeriodic` from `RhBandAgree` and a super-diagonal `(u, u + (B + 1))` gate from the verified paper**. -/
theorem not_centerperiodic_of_superdiag_gate_sub_twopow_kit
    (T P m k B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ Rule30UOR.Core.twopow k) (ht : T + m * P ≤ Rule30UOR.Core.twopow k)
    (hS : Rule30UOR.Core.twopow k ≤ S + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (Rule30UOR.Core.twopow k - m * P) (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + m * P) + u) (u + (B + 1)) =
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ S →
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter (((Rule30UOR.Core.twopow k - m * P) + m * P) + u) (u + (B + 2)) =
      Rule30UOR.Interfaces.rhCenter ((Rule30UOR.Core.twopow k - m * P) + u) (u + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_superdiag_gate_sub_twopow T P m k B S hP hm hmP ht hS hband hc1 hc2

/-- **1-Step Black Persistence Behind a Left White Cell in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_black_stays_step_kit
    (td tx k p : Nat)
    (hw : Rule30UOR.Interfaces.rdrv td tx k p = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx k (p + 1) = true) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1) = true :=
  Rule30Paper.Paper.rdrv_black_stays_step td tx k p hw hb

/-- **Multi-Step Black Persistence Behind a White Left Boundary Run in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_black_stays_kit
    (td tx a p n k : Nat)
    (hw : ∀ s : Nat, s < n → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx a (p + 1) = true)
    (hk : k ≤ n) :
    Rule30UOR.Interfaces.rdrv td tx (a + k) (p + 1) = true :=
  Rule30Paper.Paper.rdrv_black_stays td tx a p n k hw hb hk

/-- **Column-`1` Black Persistence Across a White Drive Run in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_black_stays_of_white_drive_kit
    (td tx a r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx a 1 = true)
    (hk : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx (a + k) 1 = true :=
  Rule30Paper.Paper.rdrv_col_one_black_stays_of_white_drive td tx a r k hw hb hk

/-- **Column-`1` Reset to `false` at the Black Drive End of a White Drive Run in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_flip_after_white_drive_kit
    (td tx a r : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hbend : Rule30UOR.Core.center (td + (a + r)) = true)
    (hb : Rule30UOR.Interfaces.rdrv td tx a 1 = true) :
    Rule30UOR.Interfaces.rdrv td tx (a + (r + 1)) 1 = false :=
  Rule30Paper.Paper.rdrv_col_one_flip_after_white_drive td tx a r hw hbend hb

/-- **Unconditional Inward Arrival of a Black Cell Across `n` White Boundary Steps in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_black_reaches_boundary_kit
    (td tx a p n : Nat)
    (hw : ∀ s : Nat, s < n → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx a (p + (n + 1)) = true) :
    Rule30UOR.Interfaces.rdrv td tx (a + n) (p + 1) = true :=
  Rule30Paper.Paper.rdrv_black_reaches_boundary td tx a p n hw hb

/-- **Inward Arrival and Persistence of a Black Cell at Column `1` During a White Drive Run (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_black_of_white_drive_and_black_cell_kit
    (td tx a n r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx a (n + 1) = true)
    (hnk : n ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx (a + k) 1 = true :=
  Rule30Paper.Paper.rdrv_col_one_black_of_white_drive_and_black_cell td tx a n r k hw hb hnk hkr

/-- **Inward Arrival and Persistence at Column `1` from an Initial Black Cell `rhCenter tx (n + 1) = true` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_black_from_init_of_white_drive_kit
    (td tx n r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + s) = false)
    (hb : Rule30UOR.Interfaces.rhCenter tx (n + 1) = true)
    (hnk : n ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx k 1 = true :=
  Rule30Paper.Paper.rdrv_col_one_black_from_init_of_white_drive td tx n r k hw hb hnk hkr

/-- **Unconditional Column-`1` Black Arrival from the Right-Edge Diagonal `rhCenter tx tx = true` During a White Drive Run (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_black_from_right_edge_of_white_drive_kit
    (td tx r k : Nat)
    (htx : 1 ≤ tx)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + s) = false)
    (htk : tx ≤ k + 1) (hkr : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx k 1 = true :=
  Rule30Paper.Paper.rdrv_col_one_black_from_right_edge_of_white_drive td tx r k htx hw htk hkr

/-- **Synchronization of Column `1` Across Two Initial States During a White Drive Run (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_agree_of_white_drive_and_black_cells_kit
    (td tx2 tx a n2 n1 r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 a (n2 + 1) = true)
    (hb1 : Rule30UOR.Interfaces.rdrv td tx a (n1 + 1) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx2 (a + k) 1 = Rule30UOR.Interfaces.rdrv td tx (a + k) 1 :=
  Rule30Paper.Paper.rdrv_col_one_agree_of_white_drive_and_black_cells td tx2 tx a n2 n1 r k hw hb2 hb1 hn2 hn1 hkr

/-- **Synchronization of Column `1` One Step After a White Drive Run (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_agree_after_white_drive_and_black_cells_kit
    (td tx2 tx a n2 n1 r : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 a (n2 + 1) = true)
    (hb1 : Rule30UOR.Interfaces.rdrv td tx a (n1 + 1) = true)
    (hn2 : n2 ≤ r) (hn1 : n1 ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx2 (a + (r + 1)) 1 = Rule30UOR.Interfaces.rdrv td tx (a + (r + 1)) 1 :=
  Rule30Paper.Paper.rdrv_col_one_agree_after_white_drive_and_black_cells td tx2 tx a n2 n1 r hw hb2 hb1 hn2 hn1

/-- **Derivation of `maskparity · 0` Agreement from a White Center Run and Black Right-Half Cells (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_white_drive_and_black_cells_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t a n2 n1 r k : Nat) (ht : T ≤ t)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + (a + s)) = false)
    (hb2 : Rule30UOR.Interfaces.rdrv t (t + m * P) a (n2 + 1) = true)
    (hb1 : Rule30UOR.Interfaces.rdrv t t a (n1 + 1) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Scale.maskparity ((t + (a + k)) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + (a + k)) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_white_drive_and_black_cells T P hP hper m t a n2 n1 r k ht hw hb2 hb1 hn2 hn1 hkr

/-- **Derivation of `maskparity · 0` Agreement from an Initial White Center Run and Initial Black Right-Half Cells (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_from_init_of_white_drive_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t n2 n1 r k : Nat) (ht : T ≤ t)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (hb2 : Rule30UOR.Interfaces.rhCenter (t + m * P) (n2 + 1) = true)
    (hb1 : Rule30UOR.Interfaces.rhCenter t (n1 + 1) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Scale.maskparity ((t + k) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + k) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_from_init_of_white_drive T P hP hper m t n2 n1 r k ht hw hb2 hb1 hn2 hn1 hkr

/-- **White Prefix Forced by a White Column-`1` Cell During a White Drive Run (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_prefix_forced_of_col_one_white_kit
    (td tx a r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (h1 : Rule30UOR.Interfaces.rdrv td tx (a + (q - 1)) 1 = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    Rule30UOR.Interfaces.rdrv td tx a q = false :=
  Rule30Paper.Paper.rdrv_white_prefix_forced_of_col_one_white td tx a r q hw h1 hq1 hqr

/-- **White Right-Half Cell `rhCenter t q = false` Forced by a White Column-`1` Cell During a White Center Run (`kit [33]`) from the verified paper**. -/
theorem rhcenter_white_prefix_forced_of_col_one_white_kit
    (t r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (h1 : Rule30UOR.Interfaces.rhCenter (t + (q - 1)) 1 = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    Rule30UOR.Interfaces.rhCenter t q = false :=
  Rule30Paper.Paper.rhcenter_white_prefix_forced_of_col_one_white t r q hw h1 hq1 hqr

/-- **White Right-Half Band `[1, r + 1]` Forced by a White Center Run and White Column-`1` Run (`kit [33]`) from the verified paper**. -/
theorem rhcenter_white_band_forced_of_col_one_white_run_kit
    (t r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (h1 : ∀ s : Nat, s ≤ r → Rule30UOR.Interfaces.rhCenter (t + s) 1 = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    Rule30UOR.Interfaces.rhCenter t q = false :=
  Rule30Paper.Paper.rhcenter_white_band_forced_of_col_one_white_run t r q hw h1 hq1 hqr

/-- **Autonomous 1-Step Sub-Diagonal Recurrence in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_succ_two_step_kit
    (td tx c u : Nat) :
    Rule30UOR.Interfaces.rdrv td tx ((u + 1) + (c + 2)) (u + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (u + (c + 2)) u)
        (Rule30UOR.Interfaces.rdrv td tx ((u + 1) + (c + 1)) (u + 1) ||
          Rule30UOR.Interfaces.rdrv td tx ((u + 2) + c) (u + 2)) :=
  Rule30Paper.Paper.rdrv_subdiag_succ_two_step td tx c u

/-- **Autonomous Determination of Sub-Diagonal `c + 2` from OR-Agreement of Sub-Diagonals `c + 1` and `c` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_agree_of_prev_or_agree_kit
    (td tx2 tx c k : Nat)
    (hor : ∀ u : Nat, u < k →
      (Rule30UOR.Interfaces.rdrv td tx2 ((u + 1) + (c + 1)) (u + 1) ||
        Rule30UOR.Interfaces.rdrv td tx2 ((u + 2) + c) (u + 2)) =
      (Rule30UOR.Interfaces.rdrv td tx ((u + 1) + (c + 1)) (u + 1) ||
        Rule30UOR.Interfaces.rdrv td tx ((u + 2) + c) (u + 2))) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + (c + 2)) k = Rule30UOR.Interfaces.rdrv td tx (k + (c + 2)) k :=
  Rule30Paper.Paper.rdrv_subdiag_agree_of_prev_or_agree td tx2 tx c k hor

/-- **Determination of Sub-Diagonal `c + 2` from Agreement of Sub-Diagonals `c + 1` and `c` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_agree_of_two_prev_subdiags_kit
    (td tx2 tx c k : Nat)
    (hd1 : ∀ u : Nat, u ≤ k → Rule30UOR.Interfaces.rdrv td tx2 (u + (c + 1)) u = Rule30UOR.Interfaces.rdrv td tx (u + (c + 1)) u)
    (hd0 : ∀ u : Nat, u ≤ k + 1 → Rule30UOR.Interfaces.rdrv td tx2 (u + c) u = Rule30UOR.Interfaces.rdrv td tx (u + c) u) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + (c + 2)) k = Rule30UOR.Interfaces.rdrv td tx (k + (c + 2)) k :=
  Rule30Paper.Paper.rdrv_subdiag_agree_of_two_prev_subdiags td tx2 tx c k hd1 hd0

/-- **Sub-Cone Determination `p + (c + 1) ≤ k` from Agreement of Two Consecutive Sub-Diagonals `c + 1` and `c` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subcone_agree_of_two_subdiags_kit
    (td tx2 tx c k p : Nat)
    (hd1 : ∀ u : Nat, u ≤ k → Rule30UOR.Interfaces.rdrv td tx2 (u + (c + 1)) u = Rule30UOR.Interfaces.rdrv td tx (u + (c + 1)) u)
    (hd0 : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rdrv td tx2 ((u + 1) + c) (u + 1) = Rule30UOR.Interfaces.rdrv td tx ((u + 1) + c) (u + 1))
    (hpk : p + (c + 1) ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_subcone_agree_of_two_subdiags td tx2 tx c k p hd1 hd0 hpk

/-- **Exact Collapse of Sub-Diagonal `c + 2` to the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_eq_white_seed_of_prev_or_eq_kit
    (td tx c k : Nat)
    (hor : ∀ u : Nat, u < k →
      (Rule30UOR.Interfaces.rdrv td tx ((u + 1) + (c + 1)) (u + 1) ||
        Rule30UOR.Interfaces.rdrv td tx ((u + 2) + c) (u + 2)) =
      (Rule30UOR.Interfaces.rdrv td 0 ((u + 1) + (c + 1)) (u + 1) ||
        Rule30UOR.Interfaces.rdrv td 0 ((u + 2) + c) (u + 2))) :
    Rule30UOR.Interfaces.rdrv td tx (k + (c + 2)) k = Rule30UOR.Interfaces.rdrv td 0 (k + (c + 2)) k :=
  Rule30Paper.Paper.rdrv_subdiag_eq_white_seed_of_prev_or_eq td tx c k hor

/-- **Sub-Diagonal `H`-Shift Defect Invariance (`accum_shift`) in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_accum_shift_xor_kit
    (td tx c a H k : Nat)
    (hor : ∀ u : Nat, u < k →
      (Rule30UOR.Interfaces.rdrv td tx (((a + H) + (u + 1)) + (c + 1)) ((a + H) + (u + 1)) ||
        Rule30UOR.Interfaces.rdrv td tx (((a + H) + (u + 2)) + c) ((a + H) + (u + 2))) =
      (Rule30UOR.Interfaces.rdrv td tx ((a + (u + 1)) + (c + 1)) (a + (u + 1)) ||
        Rule30UOR.Interfaces.rdrv td tx ((a + (u + 2)) + c) (a + (u + 2)))) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (((a + H) + k) + (c + 2)) ((a + H) + k))
         (Rule30UOR.Interfaces.rdrv td tx ((a + k) + (c + 2)) (a + k)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx ((a + H) + (c + 2)) (a + H))
           (Rule30UOR.Interfaces.rdrv td tx (a + (c + 2)) a) :=
  Rule30Paper.Paper.rdrv_subdiag_accum_shift_xor td tx c a H k hor

/-- **Sub-Diagonal `2 * H` Period-Doubling from `H`-Periodicity of the Preceding OR Gate (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_double_of_prev_or_period_kit
    (td tx c a H k : Nat)
    (hor : ∀ u : Nat, u < H + k →
      (Rule30UOR.Interfaces.rdrv td tx (((a + H) + (u + 1)) + (c + 1)) ((a + H) + (u + 1)) ||
        Rule30UOR.Interfaces.rdrv td tx (((a + H) + (u + 2)) + c) ((a + H) + (u + 2))) =
      (Rule30UOR.Interfaces.rdrv td tx ((a + (u + 1)) + (c + 1)) (a + (u + 1)) ||
        Rule30UOR.Interfaces.rdrv td tx ((a + (u + 2)) + c) (a + (u + 2)))) :
    Rule30UOR.Interfaces.rdrv td tx (((a + 2 * H) + k) + (c + 2)) ((a + 2 * H) + k) =
      Rule30UOR.Interfaces.rdrv td tx ((a + k) + (c + 2)) (a + k) :=
  Rule30Paper.Paper.rdrv_subdiag_period_double_of_prev_or_period td tx c a H k hor

/-- **Sub-Diagonal `2 * H` Period-Doubling from `H`-Periodicity of Sub-Diagonals `c + 1` and `c` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_double_of_two_prev_periods_kit
    (td tx c a H k : Nat)
    (hp1 : ∀ u : Nat, u ≤ H + k →
      Rule30UOR.Interfaces.rdrv td tx (((a + H) + u) + (c + 1)) ((a + H) + u) =
      Rule30UOR.Interfaces.rdrv td tx ((a + u) + (c + 1)) (a + u))
    (hp0 : ∀ u : Nat, u ≤ (H + k) + 1 →
      Rule30UOR.Interfaces.rdrv td tx (((a + H) + u) + c) ((a + H) + u) =
      Rule30UOR.Interfaces.rdrv td tx ((a + u) + c) (a + u)) :
    Rule30UOR.Interfaces.rdrv td tx (((a + 2 * H) + k) + (c + 2)) ((a + 2 * H) + k) =
      Rule30UOR.Interfaces.rdrv td tx ((a + k) + (c + 2)) (a + k) :=
  Rule30Paper.Paper.rdrv_subdiag_period_double_of_two_prev_periods td tx c a H k hp1 hp0

/-- **Sub-Diagonal `c + 2` Complementation Step Under a Black Preceding Sub-Diagonal `c + 1` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_succ_two_step_of_black_prev_kit
    (td tx c u : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx ((u + 1) + (c + 1)) (u + 1) = true) :
    Rule30UOR.Interfaces.rdrv td tx ((u + 1) + (c + 2)) (u + 1) = !Rule30UOR.Interfaces.rdrv td tx (u + (c + 2)) u :=
  Rule30Paper.Paper.rdrv_subdiag_succ_two_step_of_black_prev td tx c u hb

/-- **Sub-Diagonal `1` Period-`2` Invariance Under Two Consecutive Black Main-Diagonal Cells (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_period_two_of_black_main_diag_kit
    (td tx u : Nat)
    (hb1 : Rule30UOR.Interfaces.rdrv td tx (u + 1) (u + 1) = true)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx (u + 2) (u + 2) = true) :
    Rule30UOR.Interfaces.rdrv td tx ((u + 2) + 1) (u + 2) = Rule30UOR.Interfaces.rdrv td tx (u + 1) u :=
  Rule30Paper.Paper.rdrv_subdiag_one_period_two_of_black_main_diag td tx u hb1 hb2

/-- **Sub-Diagonal `1` Agreement Under a Black Main Diagonal (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_agree_of_black_main_diag_kit
    (td tx2 tx k : Nat)
    (hb : ∀ u : Nat, u < k →
      Rule30UOR.Interfaces.rdrv td tx2 (u + 1) (u + 1) = true ∧ Rule30UOR.Interfaces.rdrv td tx (u + 1) (u + 1) = true) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + 1) k = Rule30UOR.Interfaces.rdrv td tx (k + 1) k :=
  Rule30Paper.Paper.rdrv_subdiag_one_agree_of_black_main_diag td tx2 tx k hb

/-- **Sub-Diagonal `2` Complementation Step Under a Black Main Diagonal (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_two_step_of_black_main_diag_kit
    (td tx u : Nat)
    (hb : Rule30UOR.Interfaces.rdrv td tx (u + 2) (u + 2) = true) :
    Rule30UOR.Interfaces.rdrv td tx ((u + 1) + 2) (u + 1) = !Rule30UOR.Interfaces.rdrv td tx (u + 2) u :=
  Rule30Paper.Paper.rdrv_subdiag_two_step_of_black_main_diag td tx u hb

/-- **Sub-Diagonal `2` Period-`2` Invariance Under Two Consecutive Black Main-Diagonal Cells (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_two_period_two_of_black_main_diag_kit
    (td tx u : Nat)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx (u + 2) (u + 2) = true)
    (hb3 : Rule30UOR.Interfaces.rdrv td tx (u + 3) (u + 3) = true) :
    Rule30UOR.Interfaces.rdrv td tx ((u + 2) + 2) (u + 2) = Rule30UOR.Interfaces.rdrv td tx (u + 2) u :=
  Rule30Paper.Paper.rdrv_subdiag_two_period_two_of_black_main_diag td tx u hb2 hb3

/-- **Sub-Diagonal `2` Agreement Under a Black Main Diagonal (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_two_agree_of_black_main_diag_kit
    (td tx2 tx k : Nat)
    (hb : ∀ u : Nat, u < k →
      Rule30UOR.Interfaces.rdrv td tx2 (u + 2) (u + 2) = true ∧ Rule30UOR.Interfaces.rdrv td tx (u + 2) (u + 2) = true) :
    Rule30UOR.Interfaces.rdrv td tx2 (k + 2) k = Rule30UOR.Interfaces.rdrv td tx (k + 2) k :=
  Rule30Paper.Paper.rdrv_subdiag_two_agree_of_black_main_diag td tx2 tx k hb

/-- **Sub-Cone `p + 2 ≤ k` Determination from Main-Diagonal Blackness at `u ≥ 1` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subcone_two_agree_of_black_main_diag_kit
    (td tx2 tx k p : Nat)
    (hb : ∀ u : Nat, u ≤ k →
      Rule30UOR.Interfaces.rdrv td tx2 (u + 1) (u + 1) = true ∧ Rule30UOR.Interfaces.rdrv td tx (u + 1) (u + 1) = true)
    (hpk : p + 2 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_subcone_two_agree_of_black_main_diag td tx2 tx k p hb hpk

/-- **Exact Right-Diagonal Identification of Super-Diagonals in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_eq_rdiag_kit
    (t c u : Nat) (hct : c ≤ t) :
    Rule30UOR.Interfaces.rhCenter (t + u) (u + c) = Rule30UOR.Core.rdiag (t - c) (t + u) :=
  Rule30Paper.Paper.rhcenter_superdiag_eq_rdiag t c u hct

/-- **Exact Right-Diagonal Identification of Super-Diagonals in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_superdiag_eq_rdiag_kit
    (td tx c u : Nat) (hc1 : 1 ≤ c) (hct : c ≤ tx) :
    Rule30UOR.Interfaces.rdrv td tx u (u + c) = Rule30UOR.Core.rdiag (tx - c) (tx + u) :=
  Rule30Paper.Paper.rdrv_superdiag_eq_rdiag td tx c u hc1 hct

/-- **Unconditional `2^k`-Periodicity in `u` of Super-Diagonals `rhCenter (t + u) (u + c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_period_twopow_kit
    (t c k u v : Nat) (htc : t - c ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + (u + v * Rule30UOR.Core.twopow k)) ((u + v * Rule30UOR.Core.twopow k) + c) =
      Rule30UOR.Interfaces.rhCenter (t + u) (u + c) :=
  Rule30Paper.Paper.rhcenter_superdiag_period_twopow t c k u v htc

/-- **Right-Threshold `2^k`-Periodicity in `u` of Super-Diagonals `rhCenter (t + u) (u + c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_period_twopow_of_threshold_kit
    (t c k J u v : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : t - c ≤ J) :
    Rule30UOR.Interfaces.rhCenter (t + (u + v * Rule30UOR.Core.twopow k)) ((u + v * Rule30UOR.Core.twopow k) + c) =
      Rule30UOR.Interfaces.rhCenter (t + u) (u + c) :=
  Rule30Paper.Paper.rhcenter_superdiag_period_twopow_of_threshold t c k J u v hJ htc

/-- **Unconditional `2^k`-Periodicity in `u` of Super-Diagonals in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_superdiag_period_twopow_kit
    (td tx c k u v : Nat)
    (hc1 : 1 ≤ c) (htc : tx - c ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx (u + v * Rule30UOR.Core.twopow k) ((u + v * Rule30UOR.Core.twopow k) + c) =
      Rule30UOR.Interfaces.rdrv td tx u (u + c) :=
  Rule30Paper.Paper.rdrv_superdiag_period_twopow td tx c k u v hc1 htc

/-- **Right-Threshold `2^k`-Periodicity in `u` of Super-Diagonals in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_superdiag_period_twopow_of_threshold_kit
    (td tx c k J u v : Nat)
    (hc1 : 1 ≤ c) (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - c ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx (u + v * Rule30UOR.Core.twopow k) ((u + v * Rule30UOR.Core.twopow k) + c) =
      Rule30UOR.Interfaces.rdrv td tx u (u + c) :=
  Rule30Paper.Paper.rdrv_superdiag_period_twopow_of_threshold td tx c k J u v hc1 hJ htc

/-- **All-Time Super-Diagonal Agreement from a Single `2^k` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_agree_all_of_lt_twopow_kit
    (t Q c k u : Nat)
    (htc : (t + Q) - c ≤ k)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((t + Q) + r) (r + c) = Rule30UOR.Interfaces.rhCenter (t + r) (r + c)) :
    Rule30UOR.Interfaces.rhCenter ((t + Q) + u) (u + c) = Rule30UOR.Interfaces.rhCenter (t + u) (u + c) :=
  Rule30Paper.Paper.rhcenter_superdiag_agree_all_of_lt_twopow t Q c k u htc h

/-- **All-Time Super-Diagonal Agreement Under `IsRightThreshold k J` from a Single `2^k` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_agree_all_of_threshold_kit
    (t Q c k J u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : (t + Q) - c ≤ J)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((t + Q) + r) (r + c) = Rule30UOR.Interfaces.rhCenter (t + r) (r + c)) :
    Rule30UOR.Interfaces.rhCenter ((t + Q) + u) (u + c) = Rule30UOR.Interfaces.rhCenter (t + u) (u + c) :=
  Rule30Paper.Paper.rhcenter_superdiag_agree_all_of_threshold t Q c k J u hJ htc h

/-- **All-Time Conditional Super-Diagonal Gate from a Single `2^k` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_gate_all_of_lt_twopow_kit
    (t Q c k u : Nat)
    (htc : (t + Q) - c ≤ k)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (t + r) (r + c) = false →
      Rule30UOR.Interfaces.rhCenter ((t + Q) + r) (r + (c + 1)) = Rule30UOR.Interfaces.rhCenter (t + r) (r + (c + 1)))
    (hw : Rule30UOR.Interfaces.rhCenter (t + u) (u + c) = false) :
    Rule30UOR.Interfaces.rhCenter ((t + Q) + u) (u + (c + 1)) = Rule30UOR.Interfaces.rhCenter (t + u) (u + (c + 1)) :=
  Rule30Paper.Paper.rhcenter_superdiag_gate_all_of_lt_twopow t Q c k u htc h hw

/-- **All-Time Conditional Super-Diagonal Gate Under `IsRightThreshold k J` from a Single `2^k` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_gate_all_of_threshold_kit
    (t Q c k J u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : (t + Q) - c ≤ J)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (t + r) (r + c) = false →
      Rule30UOR.Interfaces.rhCenter ((t + Q) + r) (r + (c + 1)) = Rule30UOR.Interfaces.rhCenter (t + r) (r + (c + 1)))
    (hw : Rule30UOR.Interfaces.rhCenter (t + u) (u + c) = false) :
    Rule30UOR.Interfaces.rhCenter ((t + Q) + u) (u + (c + 1)) = Rule30UOR.Interfaces.rhCenter (t + u) (u + (c + 1)) :=
  Rule30Paper.Paper.rhcenter_superdiag_gate_all_of_threshold t Q c k J u hJ htc h hw

/-- **Infinite-Horizon Trapezoid Determination `p ≤ s + (B + 1)` from `RhBandAgree` and a `2^k`-Bounded Super-Diagonal Gate (`kit [33]`) from the verified paper**. -/
theorem rdrv_trapezoid_agree_of_superdiag_gate_twopow_kit
    (td tx Q B k s p : Nat)
    (htc : (tx + Q) - (B + 1) ≤ k)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hc1 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((tx + Q) + r) (r + (B + 1)) = Rule30UOR.Interfaces.rhCenter (tx + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (tx + r) (r + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter ((tx + Q) + r) (r + (B + 2)) = Rule30UOR.Interfaces.rhCenter (tx + r) (r + (B + 2)))
    (hps : p ≤ s + (B + 1)) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) s p = Rule30UOR.Interfaces.rdrv td tx s p :=
  Rule30Paper.Paper.rdrv_trapezoid_agree_of_superdiag_gate_twopow td tx Q B k s p htc hband hc1 hc2 hps

/-- **Infinite-Horizon Trapezoid Determination `p ≤ s + (B + 1)` Under `IsRightThreshold k J` from a `2^k`-Bounded Super-Diagonal Gate (`kit [33]`) from the verified paper**. -/
theorem rdrv_trapezoid_agree_of_superdiag_gate_threshold_kit
    (td tx Q B k J s p : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : (tx + Q) - (B + 1) ≤ J)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hc1 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((tx + Q) + r) (r + (B + 1)) = Rule30UOR.Interfaces.rhCenter (tx + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (tx + r) (r + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter ((tx + Q) + r) (r + (B + 2)) = Rule30UOR.Interfaces.rhCenter (tx + r) (r + (B + 2)))
    (hps : p ≤ s + (B + 1)) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) s p = Rule30UOR.Interfaces.rdrv td tx s p :=
  Rule30Paper.Paper.rdrv_trapezoid_agree_of_superdiag_gate_threshold td tx Q B k J s p hJ htc hband hc1 hc2 hps

/-- **All-Time `maskparity · 0` Agreement from `RhBandAgree` and a `2^k`-Bounded Super-Diagonal Gate (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_superdiag_gate_twopow_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B k s : Nat) (ht : T ≤ t) (htc : (t + m * P) - (B + 1) ≤ k)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + r) (r + (B + 1)) = Rule30UOR.Interfaces.rhCenter (t + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (t + r) (r + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter ((t + m * P) + r) (r + (B + 2)) = Rule30UOR.Interfaces.rhCenter (t + r) (r + (B + 2))) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_superdiag_gate_twopow T P hP hper m t B k s ht htc hband hc1 hc2

/-- **Horizon-Free (`r < 2^k`) Zero-Diagonal Refutation of `CenterPeriodic` from `RhBandAgree` and a Super-Diagonal Gate (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_superdiag_gate_twopow_at_zero_diag_kit
    (T P m z p B k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (htc : ((z + (p + 1)) + m * P) - (B + 1) ≤ k)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 1)) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + r) (r + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 2)) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + r) (r + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_superdiag_gate_twopow_at_zero_diag T P m z p B k hP hm ht hz hd hset1 hset2 htc hband hc1 hc2

/-- **Horizon-Free (`r < 2^k`) Zero-Diagonal Refutation of `CenterPeriodic` Under `IsRightThreshold k J` (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_superdiag_gate_threshold_at_zero_diag_kit
    (T P m z p B k J : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : ((z + (p + 1)) + m * P) - (B + 1) ≤ J)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 1)) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < Rule30UOR.Core.twopow k →
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + r) (r + (B + 1)) = false →
      Rule30UOR.Interfaces.rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 2)) =
      Rule30UOR.Interfaces.rhCenter ((z + (p + 1)) + r) (r + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_superdiag_gate_threshold_at_zero_diag T P m z p B k J hP hm ht hz hd hset1 hset2 hJ htc hband hc1 hc2

/-- **Gate-Free Inward Light-Cone Determination from Step `a` (`kit [33]`) from the verified paper**. -/
theorem rdrv_inward_cone_agree_from_step_kit
    (td tx2 tx a B k p : Nat)
    (hinit : ∀ q : Nat, q ≤ B + 1 → Rule30UOR.Interfaces.rdrv td tx2 a q = Rule30UOR.Interfaces.rdrv td tx a q)
    (hpk : p + k ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td tx2 (a + k) p = Rule30UOR.Interfaces.rdrv td tx (a + k) p :=
  Rule30Paper.Paper.rdrv_inward_cone_agree_from_step td tx2 tx a B k p hinit hpk

/-- **Gate-Free Inward Light-Cone Determination from `k = 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_inward_cone_agree_of_init_agree_kit
    (td tx2 tx B k p : Nat)
    (hinit : ∀ q : Nat, q ≤ B + 1 → Rule30UOR.Interfaces.rdrv td tx2 0 q = Rule30UOR.Interfaces.rdrv td tx 0 q)
    (hpk : p + k ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_inward_cone_agree_of_init_agree td tx2 tx B k p hinit hpk

/-- **Gate-Free Inward Light-Cone Determination from `RhBandAgree tx Q 1 B` (`kit [33]`) from the verified paper**. -/
theorem rdrv_inward_cone_agree_of_rhbandagree_kit
    (td tx Q B k p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hpk : p + k ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_inward_cone_agree_of_rhbandagree td tx Q B k p hband hpk

/-- **Gate-Free Column-`1` Determination from `RhBandAgree tx Q 1 B` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_agree_of_rhbandagree_kit
    (td tx Q B k : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hk : k ≤ B) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) k 1 = Rule30UOR.Interfaces.rdrv td tx k 1 :=
  Rule30Paper.Paper.rdrv_col_one_agree_of_rhbandagree td tx Q B k hband hk

/-- **Gate-Free Collapse to the Pure-Drive White Seed `rdrv td 0` Inside the Inward Light Cone (`kit [33]`) from the verified paper**. -/
theorem rdrv_inward_cone_eq_white_seed_of_initial_white_band_kit
    (td tx B k p : Nat)
    (hw : ∀ i : Nat, i ≤ B → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hpk : p + k ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_inward_cone_eq_white_seed_of_initial_white_band td tx B k p hw hpk

/-- **Gate-Free Collapse of `rhCenter (t + k) p` to `rdrv t 0 k p` Inside the Inward Light Cone (`kit [33]`) from the verified paper**. -/
theorem rhcenter_inward_cone_eq_white_seed_of_initial_white_band_kit
    (t B k p : Nat)
    (hw : ∀ i : Nat, i ≤ B → Rule30UOR.Interfaces.rhCenter t (1 + i) = false)
    (hpk : p + k ≤ B + 1) :
    Rule30UOR.Interfaces.rhCenter (t + k) p = Rule30UOR.Interfaces.rdrv t 0 k p :=
  Rule30Paper.Paper.rhcenter_inward_cone_eq_white_seed_of_initial_white_band t B k p hw hpk

/-- **Gate-Free Right-Half Inward Light-Cone Agreement Under `CenterPeriodic` (`kit [33]`) from the verified paper**. -/
theorem periodic_rhcenter_inward_cone_agree_of_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s p : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hps : p + s ≤ B + 1) :
    Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) p = Rule30UOR.Interfaces.rhCenter (t + s) p :=
  Rule30Paper.Paper.periodic_rhcenter_inward_cone_agree_of_rhbandagree T P hP hper m t B s p ht hband hps

/-- **Stepwise Contraction of `RhBandAgree` Under `CenterPeriodic` (`kit [33]`) from the verified paper**. -/
theorem periodic_rhbandagree_step_of_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hs : s ≤ B) :
    Rule30UOR.Interfaces.RhBandAgree (t + s) (m * P) 1 (B - s) :=
  Rule30Paper.Paper.periodic_rhbandagree_step_of_rhbandagree T P hP hper m t B s ht hband hs

/-- **Gate-Free Column-`1` Agreement `rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1` from `RhBandAgree t (m * P) 1 B` (`kit [33]`) from the verified paper**. -/
theorem periodic_rhcenter_one_agree_of_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hs : s ≤ B) :
    Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) 1 = Rule30UOR.Interfaces.rhCenter (t + s) 1 :=
  Rule30Paper.Paper.periodic_rhcenter_one_agree_of_rhbandagree T P hP hper m t B s ht hband hs

/-- **Gate-Free `maskparity · 0` Agreement from Single-Slice `RhBandAgree t (m * P) 1 B` (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hs : s ≤ B) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_rhbandagree T P hP hper m t B s ht hband hs

/-- **Single-Slice Refutation of `CenterPeriodic` from `RhBandAgree` at a Doubling Zero Diagonal (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_at_zero_diag_doubles_kit
    (T P m z p B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hB : p + 3 * (m * P) ≤ B + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_at_zero_diag_doubles T P m z p B hP hm ht hz hd hset1 hset2 hB hband

/-- **Single-Slice Dyadic Refutation of `CenterPeriodic` from `RhBandAgree` (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_twopow_kit
    (T P m t k B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = Rule30UOR.Core.twopow k)
    (hB : Rule30UOR.Core.twopow k ≤ B + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_twopow T P m t k B hP hm ht htm hB hband

/-- **Single-Slice Zero-Diagonal Pair Refutation of `CenterPeriodic` from `RhBandAgree` (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_rhbandagree_at_zero_diag_pair_kit
    (T P m z k B : Nat) (hP : 0 < P) (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hB : Rule30UOR.Core.twopow k ≤ B + 1)
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + Rule30UOR.Core.twopow k) (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_rhbandagree_at_zero_diag_pair T P m z k B hP hz0 h2 hz1 ht hset0 hset1 hB hband

/-- **Shortened-Horizon Strip + Inward Light-Cone Determination (`kit [33]`) from the verified paper**. -/
theorem rdrv_inward_cone_agree_of_short_boundary_gate_kit
    (td tx Q B a k p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 B)
    (hc2 : ∀ u : Nat, u < a →
      Rule30UOR.Interfaces.rdrv td tx u (B + 1) = false →
      Rule30UOR.Interfaces.rdrv td (tx + Q) u (B + 2) = Rule30UOR.Interfaces.rdrv td tx u (B + 2))
    (hpk : p + k ≤ B + 1) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) (a + k) p = Rule30UOR.Interfaces.rdrv td tx (a + k) p :=
  Rule30Paper.Paper.rdrv_inward_cone_agree_of_short_boundary_gate td tx Q B a k p hband hc2 hpk

/-- **Shortened-Horizon `maskparity · 0` Agreement from a Conditional Boundary Gate of Length `a = S - B` (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_short_boundary_gate_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B a k : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 B)
    (hc2 : ∀ u : Nat, u < a →
      Rule30UOR.Interfaces.rdrv t t u (B + 1) = false →
      Rule30UOR.Interfaces.rdrv t (t + m * P) u (B + 2) = Rule30UOR.Interfaces.rdrv t t u (B + 2))
    (hk : k ≤ B) :
    Rule30UOR.Scale.maskparity ((t + (a + k)) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + (a + k)) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_short_boundary_gate T P hP hper m t B a k ht hband hc2 hk

/-- **General Column-`p` Inward Arrival and Persistence in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_black_reaches_and_stays_boundary_kit
    (td tx a p n r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hb : Rule30UOR.Interfaces.rdrv td tx a (p + (n + 1)) = true)
    (hnk : n ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx (a + k) (p + 1) = true :=
  Rule30Paper.Paper.rdrv_black_reaches_and_stays_boundary td tx a p n r k hw hb hnk hkr

/-- **Column `p + 1` Reset to `false` at the Black End of a White Run on Column `p` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_succ_flip_after_white_col_and_black_cell_kit
    (td tx a p n r : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hbend : Rule30UOR.Interfaces.rdrv td tx (a + r) p = true)
    (hb : Rule30UOR.Interfaces.rdrv td tx a (p + (n + 1)) = true)
    (hnr : n ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx (a + (r + 1)) (p + 1) = false :=
  Rule30Paper.Paper.rdrv_col_succ_flip_after_white_col_and_black_cell td tx a p n r hw hbend hb hnr

/-- **Synchronization of Column `p + 1` Across Two States During a White Run on Column `p` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_succ_agree_of_white_col_and_black_cells_kit
    (td tx2 tx a p n2 n1 r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx2 (a + s) p = false ∧ Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 a (p + (n2 + 1)) = true)
    (hb1 : Rule30UOR.Interfaces.rdrv td tx a (p + (n1 + 1)) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx2 (a + k) (p + 1) = Rule30UOR.Interfaces.rdrv td tx (a + k) (p + 1) :=
  Rule30Paper.Paper.rdrv_col_succ_agree_of_white_col_and_black_cells td tx2 tx a p n2 n1 r k hw hb2 hb1 hn2 hn1 hkr

/-- **Synchronization of Column `p + 1` One Step After a White Run on Column `p` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_succ_agree_after_white_col_and_black_cells_kit
    (td tx2 tx a p n2 n1 r : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx2 (a + s) p = false ∧ Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hend : Rule30UOR.Interfaces.rdrv td tx2 (a + r) p = Rule30UOR.Interfaces.rdrv td tx (a + r) p)
    (hb2 : Rule30UOR.Interfaces.rdrv td tx2 a (p + (n2 + 1)) = true)
    (hb1 : Rule30UOR.Interfaces.rdrv td tx a (p + (n1 + 1)) = true)
    (hn2 : n2 ≤ r) (hn1 : n1 ≤ r) :
    Rule30UOR.Interfaces.rdrv td tx2 (a + (r + 1)) (p + 1) = Rule30UOR.Interfaces.rdrv td tx (a + (r + 1)) (p + 1) :=
  Rule30Paper.Paper.rdrv_col_succ_agree_after_white_col_and_black_cells td tx2 tx a p n2 n1 r hw hend hb2 hb1 hn2 hn1

/-- **White Spatial Cell `p + q` Forced by a White Column `p + 1` Cell Behind a White Column `p` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_offset_forced_of_white_col_kit
    (td tx a p r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (h1 : Rule30UOR.Interfaces.rdrv td tx (a + (q - 1)) (p + 1) = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    Rule30UOR.Interfaces.rdrv td tx a (p + q) = false :=
  Rule30Paper.Paper.rdrv_white_offset_forced_of_white_col td tx a p r q hw h1 hq1 hqr

/-- **Outward Right-Going White Triangle Forced by a 2-Column White Run `(p, p + 1)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_triangle_forced_of_two_white_cols_kit
    (td tx a p r u q : Nat)
    (hw0 : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hw1 : ∀ s : Nat, s ≤ r → Rule30UOR.Interfaces.rdrv td tx (a + s) (p + 1) = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    Rule30UOR.Interfaces.rdrv td tx (a + u) (p + q) = false :=
  Rule30Paper.Paper.rdrv_white_triangle_forced_of_two_white_cols td tx a p r u q hw0 hw1 hq1 huq

/-- **Outward Right-Going White Triangle Forced by a White Center Run and White Column-`1` Run in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_triangle_forced_of_white_drive_and_col_one_kit
    (td tx a r u q : Nat)
    (hw0 : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hw1 : ∀ s : Nat, s ≤ r → Rule30UOR.Interfaces.rdrv td tx (a + s) 1 = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    Rule30UOR.Interfaces.rdrv td tx (a + u) q = false :=
  Rule30Paper.Paper.rdrv_white_triangle_forced_of_white_drive_and_col_one td tx a r u q hw0 hw1 hq1 huq

/-- **Outward Right-Going White Triangle in `rhCenter` Forced by a White Center Run and White Column-`1` Run (`kit [33]`) from the verified paper**. -/
theorem rhcenter_white_triangle_forced_of_white_drive_and_col_one_kit
    (t r u q : Nat)
    (hw0 : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (hw1 : ∀ s : Nat, s ≤ r → Rule30UOR.Interfaces.rhCenter (t + s) 1 = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    Rule30UOR.Interfaces.rhCenter (t + u) q = false :=
  Rule30Paper.Paper.rhcenter_white_triangle_forced_of_white_drive_and_col_one t r u q hw0 hw1 hq1 huq

/-- **1-Step White Propagation from Three Consecutive White Cells in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_step_of_three_white_kit
    (td tx k p : Nat)
    (hw0 : Rule30UOR.Interfaces.rdrv td tx k p = false)
    (hw1 : Rule30UOR.Interfaces.rdrv td tx k (p + 1) = false)
    (hw2 : Rule30UOR.Interfaces.rdrv td tx k (p + 2) = false) :
    Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1) = false :=
  Rule30Paper.Paper.rdrv_white_step_of_three_white td tx k p hw0 hw1 hw2

/-- **Outward Right-Going White Triangle from a White Boundary Column `p` and Spatial White Interval (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_triangle_of_white_col_and_spatial_interval_kit
    (td tx a p r u q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Interfaces.rdrv td tx (a + s) p = false)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ r + 1 → Rule30UOR.Interfaces.rdrv td tx a (p + j) = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    Rule30UOR.Interfaces.rdrv td tx (a + u) (p + q) = false :=
  Rule30Paper.Paper.rdrv_white_triangle_of_white_col_and_spatial_interval td tx a p r u q hw hsp hq1 huq

/-- **Pure Spatial White-Diamond Propagation in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_diamond_of_spatial_white_interval_kit
    (td tx a p L u q : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → Rule30UOR.Interfaces.rdrv td tx a (p + j) = false)
    (hu1 : u + 1 ≤ q) (hu2 : u + q ≤ L) :
    Rule30UOR.Interfaces.rdrv td tx (a + u) (p + q) = false :=
  Rule30Paper.Paper.rdrv_white_diamond_of_spatial_white_interval td tx a p L u q hsp hu1 hu2

/-- **2-Cell White Super-Diagonal Corridor Generated by a Spatial White Interval in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_superdiag_white_corridor_of_spatial_white_interval_kit
    (td tx a p L u : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → Rule30UOR.Interfaces.rdrv td tx a (p + j) = false)
    (huL : 2 * u + 2 ≤ L) :
    Rule30UOR.Interfaces.rdrv td tx (a + u) (p + (u + 1)) = false ∧
      Rule30UOR.Interfaces.rdrv td tx (a + u) (p + (u + 2)) = false :=
  Rule30Paper.Paper.rdrv_superdiag_white_corridor_of_spatial_white_interval td tx a p L u hsp huL

/-- **Pure Spatial White-Diamond Propagation in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_white_diamond_of_spatial_white_interval_kit
    (t p L u q : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → Rule30UOR.Interfaces.rhCenter t (p + j) = false)
    (hu1 : u + 1 ≤ q) (hu2 : u + q ≤ L) :
    Rule30UOR.Interfaces.rhCenter (t + u) (p + q) = false :=
  Rule30Paper.Paper.rhcenter_white_diamond_of_spatial_white_interval t p L u q hsp hu1 hu2

/-- **2-Cell White Super-Diagonal Corridor in `rhCenter` Generated by a Spatial White Interval (`kit [33]`) from the verified paper**. -/
theorem rhcenter_superdiag_white_corridor_of_spatial_white_interval_kit
    (t B L u : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → Rule30UOR.Interfaces.rhCenter t (B + j) = false)
    (huL : 2 * u + 2 ≤ L) :
    Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 1)) = false ∧
      Rule30UOR.Interfaces.rhCenter (t + u) (u + (B + 2)) = false :=
  Rule30Paper.Paper.rhcenter_superdiag_white_corridor_of_spatial_white_interval t B L u hsp huL

/-- **Expanding Trapezoid Collapse to `rdrv td 0` from a Single-Slice Wide White Band (`kit [33]`) from the verified paper**. -/
theorem rdrv_trapezoid_eq_white_seed_of_wide_white_band_kit
    (td tx B k p : Nat)
    (hw : ∀ i : Nat, i ≤ B + (2 * k + 2) → Rule30UOR.Interfaces.rhCenter tx (1 + i) = false)
    (hpk : p ≤ k + (B + 1)) :
    Rule30UOR.Interfaces.rdrv td tx k p = Rule30UOR.Interfaces.rdrv td 0 k p :=
  Rule30Paper.Paper.rdrv_trapezoid_eq_white_seed_of_wide_white_band td tx B k p hw hpk

/-- **1-Step Main-Diagonal Recurrence of `rdrv` Driven by Super-Diagonals `1` and `2` of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_step_eq_rhcenter_kit
    (td tx u : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (u + 1) (u + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx u u)
        (Rule30UOR.Interfaces.rhCenter (tx + u) (u + 1) || Rule30UOR.Interfaces.rhCenter (tx + u) (u + 2)) :=
  Rule30Paper.Paper.rdrv_main_diag_step_eq_rhcenter td tx u

/-- **Main-Diagonal `H`-Shift Defect Invariance (`accum_shift`) in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_accum_shift_xor_kit
    (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < n →
      (Rule30UOR.Interfaces.rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 1) ||
        Rule30UOR.Interfaces.rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 2)) =
      (Rule30UOR.Interfaces.rhCenter (tx + (a + u)) ((a + u) + 1) ||
        Rule30UOR.Interfaces.rhCenter (tx + (a + u)) ((a + u) + 2))) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx ((a + H) + n) ((a + H) + n))
         (Rule30UOR.Interfaces.rdrv td tx (a + n) (a + n)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (a + H) (a + H))
           (Rule30UOR.Interfaces.rdrv td tx a a) :=
  Rule30Paper.Paper.rdrv_main_diag_accum_shift_xor td tx a H n hor

/-- **Main-Diagonal `2 * H` Period-Doubling from `H`-Periodicity of the Super-Diagonal OR Gate (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_period_double_of_superdiag_or_period_kit
    (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < H + n →
      (Rule30UOR.Interfaces.rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 1) ||
        Rule30UOR.Interfaces.rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 2)) =
      (Rule30UOR.Interfaces.rhCenter (tx + (a + u)) ((a + u) + 1) ||
        Rule30UOR.Interfaces.rhCenter (tx + (a + u)) ((a + u) + 2))) :
    Rule30UOR.Interfaces.rdrv td tx ((a + 2 * H) + n) ((a + 2 * H) + n) =
      Rule30UOR.Interfaces.rdrv td tx (a + n) (a + n) :=
  Rule30Paper.Paper.rdrv_main_diag_period_double_of_superdiag_or_period td tx a H n hor

/-- **Unconditional `2^(k + 1)`-Periodicity in `u` of the Main Diagonal `rdrv td tx u u` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_period_twopow_succ_kit
    (td tx k u : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx (u + Rule30UOR.Core.twopow (k + 1)) (u + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.rdrv td tx u u :=
  Rule30Paper.Paper.rdrv_main_diag_period_twopow_succ td tx k u htc

/-- **Right-Threshold `2^(k + 1)`-Periodicity in `u` of the Main Diagonal `rdrv td tx u u` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_period_twopow_succ_of_threshold_kit
    (td tx k J u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx (u + Rule30UOR.Core.twopow (k + 1)) (u + Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.rdrv td tx u u :=
  Rule30Paper.Paper.rdrv_main_diag_period_twopow_succ_of_threshold td tx k J u hJ htc

/-- **Multi-Period `v * 2^(k + 1)`-Invariance in `u` of the Main Diagonal `rdrv td tx u u` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_period_twopow_succ_mul_kit
    (td tx k u v : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx (u + v * Rule30UOR.Core.twopow (k + 1)) (u + v * Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Interfaces.rdrv td tx u u :=
  Rule30Paper.Paper.rdrv_main_diag_period_twopow_succ_mul td tx k u v htc

/-- **All-Time Main-Diagonal Agreement from a Single `2^(k + 1)` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_agree_all_of_lt_twopow_succ_kit
    (td tx Q k u : Nat)
    (htc : (tx + Q) - 1 ≤ k)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow (k + 1) →
      Rule30UOR.Interfaces.rdrv td (tx + Q) r r = Rule30UOR.Interfaces.rdrv td tx r r) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) u u = Rule30UOR.Interfaces.rdrv td tx u u :=
  Rule30Paper.Paper.rdrv_main_diag_agree_all_of_lt_twopow_succ td tx Q k u htc h

/-- **1-Step Sub-Diagonal `1` Recurrence Driven by the Main Diagonal and Super-Diagonal `1` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_step_eq_rhcenter_kit
    (td tx u : Nat) :
    Rule30UOR.Interfaces.rdrv td tx ((u + 1) + 1) (u + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (u + 1) u)
        (Rule30UOR.Interfaces.rdrv td tx (u + 1) (u + 1) || Rule30UOR.Interfaces.rhCenter (tx + (u + 1)) ((u + 1) + 1)) :=
  Rule30Paper.Paper.rdrv_subdiag_one_step_eq_rhcenter td tx u

/-- **Sub-Diagonal `1` `H`-Shift Defect Invariance (`accum_shift`) in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_accum_shift_xor_kit
    (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < n →
      (Rule30UOR.Interfaces.rdrv td tx ((a + H) + (u + 1)) ((a + H) + (u + 1)) ||
        Rule30UOR.Interfaces.rhCenter (tx + ((a + H) + (u + 1))) (((a + H) + (u + 1)) + 1)) =
      (Rule30UOR.Interfaces.rdrv td tx (a + (u + 1)) (a + (u + 1)) ||
        Rule30UOR.Interfaces.rhCenter (tx + (a + (u + 1))) ((a + (u + 1)) + 1))) :
    Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (((a + H) + n) + 1) ((a + H) + n))
         (Rule30UOR.Interfaces.rdrv td tx ((a + n) + 1) (a + n)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx ((a + H) + 1) (a + H))
           (Rule30UOR.Interfaces.rdrv td tx (a + 1) a) :=
  Rule30Paper.Paper.rdrv_subdiag_one_accum_shift_xor td tx a H n hor

/-- **Sub-Diagonal `1` `2 * H` Period-Doubling from `H`-Periodicity of the Main/Super-Diagonal OR Gate (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_period_double_of_or_period_kit
    (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < H + n →
      (Rule30UOR.Interfaces.rdrv td tx ((a + H) + (u + 1)) ((a + H) + (u + 1)) ||
        Rule30UOR.Interfaces.rhCenter (tx + ((a + H) + (u + 1))) (((a + H) + (u + 1)) + 1)) =
      (Rule30UOR.Interfaces.rdrv td tx (a + (u + 1)) (a + (u + 1)) ||
        Rule30UOR.Interfaces.rhCenter (tx + (a + (u + 1))) ((a + (u + 1)) + 1))) :
    Rule30UOR.Interfaces.rdrv td tx (((a + 2 * H) + n) + 1) ((a + 2 * H) + n) =
      Rule30UOR.Interfaces.rdrv td tx ((a + n) + 1) (a + n) :=
  Rule30Paper.Paper.rdrv_subdiag_one_period_double_of_or_period td tx a H n hor

/-- **Unconditional `2^(k + 2)`-Periodicity in `u` of Sub-Diagonal `1` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_period_twopow_succ_two_kit
    (td tx k u : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx ((u + Rule30UOR.Core.twopow (k + 2)) + 1) (u + Rule30UOR.Core.twopow (k + 2)) =
      Rule30UOR.Interfaces.rdrv td tx (u + 1) u :=
  Rule30Paper.Paper.rdrv_subdiag_one_period_twopow_succ_two td tx k u htc

/-- **Right-Threshold `2^(k + 2)`-Periodicity in `u` of Sub-Diagonal `1` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_one_period_twopow_succ_two_of_threshold_kit
    (td tx k J u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx ((u + Rule30UOR.Core.twopow (k + 2)) + 1) (u + Rule30UOR.Core.twopow (k + 2)) =
      Rule30UOR.Interfaces.rdrv td tx (u + 1) u :=
  Rule30Paper.Paper.rdrv_subdiag_one_period_twopow_succ_two_of_threshold td tx k J u hJ htc

/-- **Universal Sub-Diagonal `2^(k + 1 + c)`-Periodicity Law in `u` for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_all_kit
    (td tx k c u : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx ((u + Rule30UOR.Core.twopow ((k + 1) + c)) + c) (u + Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_all td tx k c u htc

/-- **Multi-Period `v * 2^(k + 1 + c)`-Invariance in `u` of Sub-Diagonal `c` in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_all_mul_kit
    (td tx k c u v : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx ((u + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (u + v * Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_all_mul td tx k c u v htc

/-- **Right-Threshold Universal Sub-Diagonal `2^(k + 1 + c)`-Periodicity Law in `u` for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_all_of_threshold_kit
    (td tx k J c u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx ((u + Rule30UOR.Core.twopow ((k + 1) + c)) + c) (u + Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_all_of_threshold td tx k J c u hJ htc

/-- **Exact Center-Drive Replication on the Main Diagonal at Multiples of `2^(k + 1)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_at_twopow_succ_eq_center_kit
    (td tx k v : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow (k + 1)) (v * Rule30UOR.Core.twopow (k + 1)) =
      Rule30UOR.Core.center td :=
  Rule30Paper.Paper.rdrv_main_diag_at_twopow_succ_eq_center td tx k v htc

/-- **Exact Center-Drive Replication on Sub-Diagonal `c` at Multiples of `2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_at_twopow_all_eq_center_kit
    (td tx k c v : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (v * Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (td + c) :=
  Rule30Paper.Paper.rdrv_subdiag_at_twopow_all_eq_center td tx k c v htc

/-- **Right-Threshold Center-Drive Replication on Sub-Diagonal `c` at `2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_at_twopow_all_eq_center_of_threshold_kit
    (td tx k J c : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx (Rule30UOR.Core.twopow ((k + 1) + c) + c) (Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (td + c) :=
  Rule30Paper.Paper.rdrv_subdiag_at_twopow_all_eq_center_of_threshold td tx k J c hJ htc

/-- **Exact Center Replication Inside `rhCenter` at Dyadic Columns `v * 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_subdiag_at_twopow_all_eq_center_kit
    (t k c v : Nat) (htc : t - 1 ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow ((k + 1) + c)) + c)) (v * Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (t + c) :=
  Rule30Paper.Paper.rhcenter_subdiag_at_twopow_all_eq_center t k c v htc

/-- **Right-Threshold Center Replication Inside `rhCenter` at `2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_subdiag_at_twopow_all_eq_center_of_threshold_kit
    (t k J c : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : t - 1 ≤ J) :
    Rule30UOR.Interfaces.rhCenter (t + (Rule30UOR.Core.twopow ((k + 1) + c) + c)) (Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (t + c) :=
  Rule30Paper.Paper.rhcenter_subdiag_at_twopow_all_eq_center_of_threshold t k J c hJ htc

/-- **Unconditional Agreement of Two Driven Trajectories `tx2, tx` at Dyadic Sub-Diagonal Multiples `v * 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_at_twopow_all_agree_kit
    (td tx2 tx k c v : Nat)
    (htc2 : tx2 - 1 ≤ k) (htc1 : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx2 ((v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (v * Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (v * Rule30UOR.Core.twopow ((k + 1) + c)) :=
  Rule30Paper.Paper.rdrv_subdiag_at_twopow_all_agree td tx2 tx k c v htc2 htc1

/-- **Exact Dyadic Lift of Column `1` (`rdrv td tx (1 + c) 1`) to Column `1 + v * 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_eq_subdiag_at_twopow_all_kit
    (td tx k c v : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx (1 + c) 1 =
      Rule30UOR.Interfaces.rdrv td tx ((1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) :=
  Rule30Paper.Paper.rdrv_col_one_eq_subdiag_at_twopow_all td tx k c v htc

/-- **Right-Threshold Dyadic Lift of Column `1` to Column `1 + 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_eq_subdiag_at_twopow_all_of_threshold_kit
    (td tx k J c : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx (1 + c) 1 =
      Rule30UOR.Interfaces.rdrv td tx ((1 + Rule30UOR.Core.twopow ((k + 1) + c)) + c) (1 + Rule30UOR.Core.twopow ((k + 1) + c)) :=
  Rule30Paper.Paper.rdrv_col_one_eq_subdiag_at_twopow_all_of_threshold td tx k J c hJ htc

/-- **Exact Dyadic Lift of Column `1` in `rhCenter` (`rhCenter (t + (1 + c)) 1`) to Column `1 + v * 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_col_one_eq_subdiag_at_twopow_all_kit
    (t k c v : Nat) (htc : t - 1 ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + (1 + c)) 1 =
      Rule30UOR.Interfaces.rhCenter (t + ((1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c)) (1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) :=
  Rule30Paper.Paper.rhcenter_col_one_eq_subdiag_at_twopow_all t k c v htc

/-- **Right-Threshold Dyadic Lift of Column `1` in `rhCenter` to Column `1 + 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_col_one_eq_subdiag_at_twopow_all_of_threshold_kit
    (t k J c : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : t - 1 ≤ J) :
    Rule30UOR.Interfaces.rhCenter (t + (1 + c)) 1 =
      Rule30UOR.Interfaces.rhCenter (t + ((1 + Rule30UOR.Core.twopow ((k + 1) + c)) + c)) (1 + Rule30UOR.Core.twopow ((k + 1) + c)) :=
  Rule30Paper.Paper.rhcenter_col_one_eq_subdiag_at_twopow_all_of_threshold t k J c hJ htc

/-- **Column-`1` Agreement at Step `1 + c` from Agreement at Dyadic Column `1 + v * 2^((k + 1) + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_agree_of_subdiag_twopow_agree_kit
    (td tx2 tx k c v : Nat)
    (htc2 : tx2 - 1 ≤ k) (htc1 : tx - 1 ≤ k)
    (h : Rule30UOR.Interfaces.rdrv td tx2 ((1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) =
         Rule30UOR.Interfaces.rdrv td tx ((1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (1 + v * Rule30UOR.Core.twopow ((k + 1) + c))) :
    Rule30UOR.Interfaces.rdrv td tx2 (1 + c) 1 = Rule30UOR.Interfaces.rdrv td tx (1 + c) 1 :=
  Rule30Paper.Paper.rdrv_col_one_agree_of_subdiag_twopow_agree td tx2 tx k c v htc2 htc1 h

/-- **All-Column Agreement on Sub-Diagonal `c` from a Single `2^((k + 1) + c)` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_agree_all_of_lt_twopow_all_kit
    (td tx Q k c u : Nat)
    (htc : (tx + Q) - 1 ≤ k)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow ((k + 1) + c) →
      Rule30UOR.Interfaces.rdrv td (tx + Q) (r + c) r = Rule30UOR.Interfaces.rdrv td tx (r + c) r) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) (u + c) u = Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_agree_all_of_lt_twopow_all td tx Q k c u htc h

/-- **Right-Threshold Multi-Period `v * 2^((k + 1) + c)`-Invariance in `u` of Sub-Diagonal `c` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_all_mul_of_threshold_kit
    (td tx k J c u v : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    Rule30UOR.Interfaces.rdrv td tx ((u + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (u + v * Rule30UOR.Core.twopow ((k + 1) + c)) =
      Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_all_mul_of_threshold td tx k J c u v hJ htc

/-- **Right-Threshold All-Column Agreement on Sub-Diagonal `c` from a Single `2^((k + 1) + c)` Fundamental Period (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_agree_all_of_threshold_kit
    (td tx Q k J c u : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : (tx + Q) - 1 ≤ J)
    (h : ∀ r : Nat, r < Rule30UOR.Core.twopow ((k + 1) + c) →
      Rule30UOR.Interfaces.rdrv td (tx + Q) (r + c) r = Rule30UOR.Interfaces.rdrv td tx (r + c) r) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) (u + c) u = Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_agree_all_of_threshold td tx Q k J c u hJ htc h

/-- **Derivation of `maskparity · 0` Agreement at `t + (1 + c)` from Dyadic Sub-Diagonal Column `1 + v * 2^((k + 1) + c)` Agreement (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_subdiag_twopow_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k c v : Nat) (ht : T ≤ t) (htc : (t + m * P) - 1 ≤ k)
    (h : Rule30UOR.Interfaces.rdrv t (t + m * P) ((1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) =
         Rule30UOR.Interfaces.rdrv t t ((1 + v * Rule30UOR.Core.twopow ((k + 1) + c)) + c) (1 + v * Rule30UOR.Core.twopow ((k + 1) + c))) :
    Rule30UOR.Scale.maskparity ((t + (1 + c)) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + (1 + c)) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_subdiag_twopow_agree T P hP hper m t k c v ht htc h

/-- **Additive-to-Multiplicative Law for `twopow` from the verified paper**. -/
theorem twopow_add_eq_mul_kit (a b : Nat) :
    Rule30UOR.Core.twopow (a + b) = Rule30UOR.Core.twopow b * Rule30UOR.Core.twopow a :=
  Rule30Paper.Paper.twopow_add_eq_mul a b

/-- **Sub-Diagonal Scale Factorization for `v * 2^((k + 1) + C)` (`kit [33]`) from the verified paper**. -/
theorem twopow_subdiag_scale_split_kit (k c C v : Nat) (hc : c ≤ C) :
    v * Rule30UOR.Core.twopow ((k + 1) + C) =
      (v * Rule30UOR.Core.twopow (C - c)) * Rule30UOR.Core.twopow ((k + 1) + c) :=
  Rule30Paper.Paper.twopow_subdiag_scale_split k c C v hc

/-- **Dyadic Quadrant Replication Theorem for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_quadrant_eq_kit
    (td tx k C v j q : Nat) (htc : tx - 1 ≤ k) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow ((k + 1) + C) + j) (v * Rule30UOR.Core.twopow ((k + 1) + C) + q) =
      Rule30UOR.Interfaces.rdrv td tx j q :=
  Rule30Paper.Paper.rdrv_dyadic_quadrant_eq td tx k C v j q htc hjq

/-- **Right-Threshold Dyadic Quadrant Replication Theorem for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_quadrant_eq_of_threshold_kit
    (td tx k J C v j q : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : tx - 1 ≤ J) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow ((k + 1) + C) + j) (v * Rule30UOR.Core.twopow ((k + 1) + C) + q) =
      Rule30UOR.Interfaces.rdrv td tx j q :=
  Rule30Paper.Paper.rdrv_dyadic_quadrant_eq_of_threshold td tx k J C v j q hJ htc hjq

/-- **Dyadic `C`-Step Slab Replication for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_slab_eq_kit
    (td tx k C v j q : Nat) (htc : tx - 1 ≤ k) (hj : j ≤ C) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow ((k + 1) + C) + j) (v * Rule30UOR.Core.twopow ((k + 1) + C) + q) =
      Rule30UOR.Interfaces.rdrv td tx j q :=
  Rule30Paper.Paper.rdrv_dyadic_slab_eq td tx k C v j q htc hj

/-- **Dyadic Horizontal Row Replication at Step `v * 2^(k + 1)` in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_row_eq_init_kit
    (td tx k v q : Nat) (htc : tx - 1 ≤ k) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow (k + 1)) (v * Rule30UOR.Core.twopow (k + 1) + q) =
      Rule30UOR.Interfaces.rdrv td tx 0 q :=
  Rule30Paper.Paper.rdrv_dyadic_row_eq_init td tx k v q htc

/-- **Spatio-Temporal Dyadic Quadrant Self-Similarity of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_quadrant_eq_kit
    (t k C v j q : Nat) (htc : t - 1 ≤ k) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rhCenter (t + (v * Rule30UOR.Core.twopow ((k + 1) + C) + j)) (v * Rule30UOR.Core.twopow ((k + 1) + C) + q) =
      Rule30UOR.Interfaces.rhCenter (t + j) q :=
  Rule30Paper.Paper.rhcenter_dyadic_quadrant_eq t k C v j q htc hjq

/-- **Right-Threshold Dyadic Quadrant Self-Similarity of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_quadrant_eq_of_threshold_kit
    (t k J C v j q : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : t - 1 ≤ J) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rhCenter (t + (v * Rule30UOR.Core.twopow ((k + 1) + C) + j)) (v * Rule30UOR.Core.twopow ((k + 1) + C) + q) =
      Rule30UOR.Interfaces.rhCenter (t + j) q :=
  Rule30Paper.Paper.rhcenter_dyadic_quadrant_eq_of_threshold t k J C v j q hJ htc hjq

/-- **Spatio-Temporal `C`-Step Slab Self-Similarity of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_slab_eq_kit
    (t k C v j q : Nat) (htc : t - 1 ≤ k) (hj : j ≤ C) :
    Rule30UOR.Interfaces.rhCenter (t + (v * Rule30UOR.Core.twopow ((k + 1) + C) + j)) (v * Rule30UOR.Core.twopow ((k + 1) + C) + q) =
      Rule30UOR.Interfaces.rhCenter (t + j) q :=
  Rule30Paper.Paper.rhcenter_dyadic_slab_eq t k C v j q htc hj

/-- **Exact Horizontal Row Replication in `rhCenter` at Time `t + v * 2^(k + 1)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_eq_kit
    (t k v q : Nat) (htc : t - 1 ≤ k) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow (k + 1)) (v * Rule30UOR.Core.twopow (k + 1) + q) =
      Rule30UOR.Interfaces.rhCenter t q :=
  Rule30Paper.Paper.rhcenter_dyadic_row_eq t k v q htc

/-- **Right-Threshold Horizontal Row Replication in `rhCenter` at Time `t + v * 2^(k + 1)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_eq_of_threshold_kit
    (t k J v q : Nat)
    (hJ : Rule30UOR.Interfaces.IsRightThreshold k J) (htc : t - 1 ≤ J) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow (k + 1)) (v * Rule30UOR.Core.twopow (k + 1) + q) =
      Rule30UOR.Interfaces.rhCenter t q :=
  Rule30Paper.Paper.rhcenter_dyadic_row_eq_of_threshold t k J v q hJ htc

/-- **Pullback of `RhBandAgree t Q a B` from Shifted Dyadic Row `t + v * 2^(k + 1)` (`kit [33]`) from the verified paper**. -/
theorem rhbandagree_of_dyadic_row_shift_agree_kit
    (t Q k v a B : Nat) (htc : (t + Q) - 1 ≤ k)
    (hband : Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow (k + 1)) Q (v * Rule30UOR.Core.twopow (k + 1) + a) B) :
    Rule30UOR.Interfaces.RhBandAgree t Q a B :=
  Rule30Paper.Paper.rhbandagree_of_dyadic_row_shift_agree t Q k v a B htc hband

/-- **Pushforward of `RhBandAgree t Q a B` to Shifted Dyadic Row `t + v * 2^(k + 1)` (`kit [33]`) from the verified paper**. -/
theorem rhbandagree_dyadic_row_shift_of_rhbandagree_kit
    (t Q k v a B : Nat) (htc : (t + Q) - 1 ≤ k)
    (hband : Rule30UOR.Interfaces.RhBandAgree t Q a B) :
    Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow (k + 1)) Q (v * Rule30UOR.Core.twopow (k + 1) + a) B :=
  Rule30Paper.Paper.rhbandagree_dyadic_row_shift_of_rhbandagree t Q k v a B htc hband

/-- **Gate-Free `maskparity · 0` Agreement from Shifted Dyadic Row `RhBandAgree` (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_dyadic_row_shift_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k v B s : Nat) (ht : T ≤ t) (htc : (t + m * P) - 1 ≤ k)
    (hband : Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow (k + 1)) (m * P) (v * Rule30UOR.Core.twopow (k + 1) + 1) B)
    (hs : s ≤ B) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_dyadic_row_shift_agree T P hP hper m t k v B s ht htc hband hs

/-- **Refutation of `CenterPeriodic` from Shifted Dyadic Row `RhBandAgree` at a Doubling Zero Diagonal (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_dyadic_row_shift_agree_at_zero_diag_doubles_kit
    (T P m z p k v B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (htc : ((z + (p + 1)) + m * P) - 1 ≤ k)
    (hB : p + 3 * (m * P) ≤ B)
    (hband : Rule30UOR.Interfaces.RhBandAgree ((z + (p + 1)) + v * Rule30UOR.Core.twopow (k + 1)) (m * P) (v * Rule30UOR.Core.twopow (k + 1) + 1) B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_dyadic_row_shift_agree_at_zero_diag_doubles T P m z p k v B hP hm ht hz hd hset1 hset2 htc hB hband

/-- **1-Step Sub-Diagonal `1` Recurrence in the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_one_step_eq_center_kit (td u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 ((u + 1) + 1) (u + 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td 0 (u + 1) u) (Rule30UOR.Core.center td) :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_one_step_eq_center td u

/-- **Unconditional Period-`2` Law in `u` for Sub-Diagonal `1` of the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_one_period_two_all_kit (td u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 ((u + 2) + 1) (u + 2) =
      Rule30UOR.Interfaces.rdrv td 0 (u + 1) u :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_one_period_two_all td u

/-- **Universal `2^c`-Periodicity in `u` of All Sub-Diagonals `c` in the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_period_twopow_all_kit (td c u : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 ((u + Rule30UOR.Core.twopow c) + c) (u + Rule30UOR.Core.twopow c) =
      Rule30UOR.Interfaces.rdrv td 0 (u + c) u :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_period_twopow_all td c u

/-- **Multi-Period `v * 2^c`-Invariance in `u` of Sub-Diagonal `c` in `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_period_twopow_all_mul_kit (td c u v : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 ((u + v * Rule30UOR.Core.twopow c) + c) (u + v * Rule30UOR.Core.twopow c) =
      Rule30UOR.Interfaces.rdrv td 0 (u + c) u :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_period_twopow_all_mul td c u v

/-- **Exact Center-Drive Replication at `u = v * 2^c` in the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_subdiag_at_twopow_eq_center_kit (td c v : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 ((v * Rule30UOR.Core.twopow c) + c) (v * Rule30UOR.Core.twopow c) =
      Rule30UOR.Core.center (td + c) :=
  Rule30Paper.Paper.rdrv_white_seed_subdiag_at_twopow_eq_center td c v

/-- **Exact Dyadic Lift of Column `1` to `1 + v * 2^c` in the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_col_one_eq_subdiag_at_twopow_kit (td c v : Nat) :
    Rule30UOR.Interfaces.rdrv td 0 (1 + c) 1 =
      Rule30UOR.Interfaces.rdrv td 0 ((1 + v * Rule30UOR.Core.twopow c) + c) (1 + v * Rule30UOR.Core.twopow c) :=
  Rule30Paper.Paper.rdrv_white_seed_col_one_eq_subdiag_at_twopow td c v

/-- **Unconditional Dyadic Quadrant Self-Similarity of the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_dyadic_quadrant_eq_kit (td C v j q : Nat) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rdrv td 0 ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) + q) =
      Rule30UOR.Interfaces.rdrv td 0 j q :=
  Rule30Paper.Paper.rdrv_white_seed_dyadic_quadrant_eq td C v j q hjq

/-- **Unconditional `C`-Step Slab Self-Similarity of the Pure-Drive White Seed `rdrv td 0` (`kit [33]`) from the verified paper**. -/
theorem rdrv_white_seed_dyadic_slab_eq_kit (td C v j q : Nat) (hj : j ≤ C) :
    Rule30UOR.Interfaces.rdrv td 0 ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) + q) =
      Rule30UOR.Interfaces.rdrv td 0 j q :=
  Rule30Paper.Paper.rdrv_white_seed_dyadic_slab_eq td C v j q hj

/-- **Delay-Free `2^c`-Periodicity of Right Diagonals in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_subdiag_period_twopow_zero_delay_kit (c u : Nat) :
    Rule30UOR.Interfaces.rhCenter ((u + Rule30UOR.Core.twopow c) + c) (u + Rule30UOR.Core.twopow c) =
      Rule30UOR.Interfaces.rhCenter (u + c) u :=
  Rule30Paper.Paper.rhcenter_subdiag_period_twopow_zero_delay c u

/-- **Delay-Free Multi-Period `v * 2^c`-Invariance of Right Diagonals in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_subdiag_period_twopow_zero_delay_mul_kit (c u v : Nat) :
    Rule30UOR.Interfaces.rhCenter ((u + v * Rule30UOR.Core.twopow c) + c) (u + v * Rule30UOR.Core.twopow c) =
      Rule30UOR.Interfaces.rhCenter (u + c) u :=
  Rule30Paper.Paper.rhcenter_subdiag_period_twopow_zero_delay_mul c u v

/-- **Delay-Free Center Replication in `rhCenter` at `(v * 2^c + c, v * 2^c)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_subdiag_at_twopow_zero_delay_eq_center_kit (c v : Nat) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow c) + c) (v * Rule30UOR.Core.twopow c) =
      Rule30UOR.Core.center c :=
  Rule30Paper.Paper.rhcenter_subdiag_at_twopow_zero_delay_eq_center c v

/-- **Delay-Free Dyadic Lift of Column `1` (`rhCenter (1 + c) 1`) to Column `1 + v * 2^c` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_col_one_eq_subdiag_at_twopow_zero_delay_kit (c v : Nat) :
    Rule30UOR.Interfaces.rhCenter (1 + c) 1 =
      Rule30UOR.Interfaces.rhCenter ((1 + v * Rule30UOR.Core.twopow c) + c) (1 + v * Rule30UOR.Core.twopow c) :=
  Rule30Paper.Paper.rhcenter_col_one_eq_subdiag_at_twopow_zero_delay c v

/-- **Delay-Free Global Dyadic Quadrant Self-Similarity of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_quadrant_zero_delay_eq_kit (C v j q : Nat) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) + q) =
      Rule30UOR.Interfaces.rhCenter j q :=
  Rule30Paper.Paper.rhcenter_dyadic_quadrant_zero_delay_eq C v j q hjq

/-- **Delay-Free Global `C`-Step Slab Self-Similarity of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_slab_zero_delay_eq_kit (C v j q : Nat) (hj : j ≤ C) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) + q) =
      Rule30UOR.Interfaces.rhCenter j q :=
  Rule30Paper.Paper.rhcenter_dyadic_slab_zero_delay_eq C v j q hj

/-- **Dyadic Exterior White Corridor of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_triangle_white_corridor_kit (C v j q : Nat) (hjq : j < q) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) + q) = false :=
  Rule30Paper.Paper.rhcenter_dyadic_triangle_white_corridor C v j q hjq

/-- **Hypothesis-Free `2^(tx + c)`-Periodicity in `u` of All Sub-Diagonals `c` in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_tx_add_kit (td tx c u : Nat) :
    Rule30UOR.Interfaces.rdrv td tx ((u + Rule30UOR.Core.twopow (tx + c)) + c) (u + Rule30UOR.Core.twopow (tx + c)) =
      Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_tx_add td tx c u

/-- **Hypothesis-Free Multi-Period `v * 2^(tx + c)`-Invariance in `u` of Sub-Diagonal `c` in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_period_twopow_tx_add_mul_kit (td tx c u v : Nat) :
    Rule30UOR.Interfaces.rdrv td tx ((u + v * Rule30UOR.Core.twopow (tx + c)) + c) (u + v * Rule30UOR.Core.twopow (tx + c)) =
      Rule30UOR.Interfaces.rdrv td tx (u + c) u :=
  Rule30Paper.Paper.rdrv_subdiag_period_twopow_tx_add_mul td tx c u v

/-- **Hypothesis-Free `v * 2^tx`-Invariance in `u` of the Main Diagonal in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_period_twopow_tx_kit (td tx u v : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (u + v * Rule30UOR.Core.twopow tx) (u + v * Rule30UOR.Core.twopow tx) =
      Rule30UOR.Interfaces.rdrv td tx u u :=
  Rule30Paper.Paper.rdrv_main_diag_period_twopow_tx td tx u v

/-- **Hypothesis-Free Center-Drive Replication on the Main Diagonal at `u = v * 2^tx` (`kit [33]`) from the verified paper**. -/
theorem rdrv_main_diag_at_twopow_tx_eq_center_kit (td tx v : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow tx) (v * Rule30UOR.Core.twopow tx) =
      Rule30UOR.Core.center td :=
  Rule30Paper.Paper.rdrv_main_diag_at_twopow_tx_eq_center td tx v

/-- **Hypothesis-Free Center-Drive Replication on Sub-Diagonal `c` at `u = v * 2^(tx + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_subdiag_at_twopow_tx_add_eq_center_kit (td tx c v : Nat) :
    Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow (tx + c)) + c) (v * Rule30UOR.Core.twopow (tx + c)) =
      Rule30UOR.Core.center (td + c) :=
  Rule30Paper.Paper.rdrv_subdiag_at_twopow_tx_add_eq_center td tx c v

/-- **Hypothesis-Free Dyadic Lift of Column `1` to `1 + v * 2^(tx + c)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_col_one_eq_subdiag_at_twopow_tx_add_kit (td tx c v : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (1 + c) 1 =
      Rule30UOR.Interfaces.rdrv td tx ((1 + v * Rule30UOR.Core.twopow (tx + c)) + c) (1 + v * Rule30UOR.Core.twopow (tx + c)) :=
  Rule30Paper.Paper.rdrv_col_one_eq_subdiag_at_twopow_tx_add td tx c v

/-- **Hypothesis-Free Dyadic Quadrant Replication (`U = v * 2^(tx + C)`) for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_quadrant_tx_add_eq_kit (td tx C v j q : Nat) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow (tx + C)) + j) ((v * Rule30UOR.Core.twopow (tx + C)) + q) =
      Rule30UOR.Interfaces.rdrv td tx j q :=
  Rule30Paper.Paper.rdrv_dyadic_quadrant_tx_add_eq td tx C v j q hjq

/-- **Hypothesis-Free `C`-Step Slab Replication (`U = v * 2^(tx + C)`) for `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_slab_tx_add_eq_kit (td tx C v j q : Nat) (hj : j ≤ C) :
    Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow (tx + C)) + j) ((v * Rule30UOR.Core.twopow (tx + C)) + q) =
      Rule30UOR.Interfaces.rdrv td tx j q :=
  Rule30Paper.Paper.rdrv_dyadic_slab_tx_add_eq td tx C v j q hj

/-- **Hypothesis-Free Horizontal Row Replication at Step `v * 2^tx` in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_row_tx_eq_init_kit (td tx v q : Nat) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow tx) ((v * Rule30UOR.Core.twopow tx) + q) =
      Rule30UOR.Interfaces.rdrv td tx 0 q :=
  Rule30Paper.Paper.rdrv_dyadic_row_tx_eq_init td tx v q

/-- **Hypothesis-Free Spatio-Temporal Quadrant Self-Similarity (`U = v * 2^(t + C)`) of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_quadrant_t_add_eq_kit (t C v j q : Nat) (hjq : j ≤ q + C) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow (t + C)) + j)) ((v * Rule30UOR.Core.twopow (t + C)) + q) =
      Rule30UOR.Interfaces.rhCenter (t + j) q :=
  Rule30Paper.Paper.rhcenter_dyadic_quadrant_t_add_eq t C v j q hjq

/-- **Hypothesis-Free Spatio-Temporal `C`-Step Slab Self-Similarity (`U = v * 2^(t + C)`) of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_slab_t_add_eq_kit (t C v j q : Nat) (hj : j ≤ C) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow (t + C)) + j)) ((v * Rule30UOR.Core.twopow (t + C)) + q) =
      Rule30UOR.Interfaces.rhCenter (t + j) q :=
  Rule30Paper.Paper.rhcenter_dyadic_slab_t_add_eq t C v j q hj

/-- **Hypothesis-Free Horizontal Row Self-Similarity (`U = v * 2^t`) of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_t_eq_kit (t v q : Nat) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow t) ((v * Rule30UOR.Core.twopow t) + q) =
      Rule30UOR.Interfaces.rhCenter t q :=
  Rule30Paper.Paper.rhcenter_dyadic_row_t_eq t v q

/-- **Common-Scale (`t ≤ K`) Horizontal Row Self-Similarity of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_scale_eq_kit (t K v q : Nat) (htK : t ≤ K) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow K) ((v * Rule30UOR.Core.twopow K) + q) =
      Rule30UOR.Interfaces.rhCenter t q :=
  Rule30Paper.Paper.rhcenter_dyadic_row_scale_eq t K v q htK

/-- **Common-Scale (`t + Q ≤ K`) Pullback of `RhBandAgree t Q a B` from Shifted Row `t + v * 2^K` (`kit [33]`) from the verified paper**. -/
theorem rhbandagree_of_dyadic_row_scale_agree_kit
    (t Q K v a B : Nat) (htK : t + Q ≤ K)
    (hband : Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow K) Q ((v * Rule30UOR.Core.twopow K) + a) B) :
    Rule30UOR.Interfaces.RhBandAgree t Q a B :=
  Rule30Paper.Paper.rhbandagree_of_dyadic_row_scale_agree t Q K v a B htK hband

/-- **Common-Scale (`t + m * P ≤ K`) Gate-Free `maskparity · 0` Agreement from Shifted Row `RhBandAgree` (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_of_dyadic_row_scale_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v B s : Nat) (ht : T ≤ t) (htK : t + m * P ≤ K)
    (hband : Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow K) (m * P) ((v * Rule30UOR.Core.twopow K) + 1) B)
    (hs : s ≤ B) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_of_dyadic_row_scale_agree T P hP hper m t K v B s ht htK hband hs

/-- **Initial Row Termination Outside the Light Cone (`kit [33]`) from the verified paper**. -/
theorem rdrv_init_gt_eq_false_kit (td tx q : Nat) (hq : tx < q) :
    Rule30UOR.Interfaces.rdrv td tx 0 q = false :=
  Rule30Paper.Paper.rdrv_init_gt_eq_false td tx q hq

/-- **Dyadic `C`-Step Slab Exterior White Cone of `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_slab_tx_gt_eq_false_kit (td tx C v j q : Nat) (hj : j ≤ C) (hq : tx + j < q) :
    Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow (tx + C)) + j) ((v * Rule30UOR.Core.twopow (tx + C)) + q) = false :=
  Rule30Paper.Paper.rdrv_dyadic_slab_tx_gt_eq_false td tx C v j q hj hq

/-- **Automatic Initial-Row Agreement Outside Both Light Cones (`kit [33]`) from the verified paper**. -/
theorem rdrv_init_agree_of_gt_kit (td tx2 tx q : Nat) (hq2 : tx2 < q) (hq1 : tx < q) :
    Rule30UOR.Interfaces.rdrv td tx2 0 q = Rule30UOR.Interfaces.rdrv td tx 0 q :=
  Rule30Paper.Paper.rdrv_init_agree_of_gt td tx2 tx q hq2 hq1

/-- **Automatic Agreement of `rdrv` Outside Both Light Cones (`kit [33]`) from the verified paper**. -/
theorem rdrv_agree_of_gt_kit (td tx2 tx k p : Nat) (hp2 : tx2 + k < p) (hp1 : tx + k < p) :
    Rule30UOR.Interfaces.rdrv td tx2 k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_agree_of_gt td tx2 tx k p hp2 hp1

/-- **All-Width Expansion of Support-Width `RhBandAgree tx Q 1 (tx + Q)` (`kit [33]`) from the verified paper**. -/
theorem rhbandagree_all_of_support_agree_kit (tx Q B : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 (tx + Q)) :
    Rule30UOR.Interfaces.RhBandAgree tx Q 1 B :=
  Rule30Paper.Paper.rhbandagree_all_of_support_agree tx Q B hband

/-- **All-Time All-Column Determination of `rdrv` from Support-Width `RhBandAgree tx Q 1 (tx + Q)` (`kit [33]`) from the verified paper**. -/
theorem rdrv_agree_all_of_support_rhbandagree_kit (td tx Q k p : Nat)
    (hband : Rule30UOR.Interfaces.RhBandAgree tx Q 1 (tx + Q)) :
    Rule30UOR.Interfaces.rdrv td (tx + Q) k p = Rule30UOR.Interfaces.rdrv td tx k p :=
  Rule30Paper.Paper.rdrv_agree_all_of_support_rhbandagree td tx Q k p hband

/-- **All-Time All-Column Agreement of `rhCenter` Under `CenterPeriodic` from Support-Width `RhBandAgree` (`kit [33]`) from the verified paper**. -/
theorem periodic_rhcenter_agree_all_of_support_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s p : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 (t + m * P)) :
    Rule30UOR.Interfaces.rhCenter ((t + s) + m * P) p = Rule30UOR.Interfaces.rhCenter (t + s) p :=
  Rule30Paper.Paper.periodic_rhcenter_agree_all_of_support_rhbandagree T P hP hper m t s p ht hband

/-- **All-Time `maskparity · 0` Agreement Under `CenterPeriodic` from Support-Width `RhBandAgree` (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_all_of_support_rhbandagree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 (t + m * P)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_all_of_support_rhbandagree T P hP hper m t s ht hband

/-- **Support-Width (`(z + (p + 1)) + m * P`) Single-Slice Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_support_rhbandagree_at_zero_diag_doubles_kit
    (T P m z p : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (hd : Rule30UOR.CompilePoints.DoublesAt (m * P) z)
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + 1) (z + (p + 1)))
    (hset2 : Rule30UOR.Interfaces.SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + (p + 1)) (m * P) 1 ((z + (p + 1)) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_support_rhbandagree_at_zero_diag_doubles T P m z p hP hm ht hz hd hset1 hset2 hband

/-- **Support-Width (`t + m * P = 2^k`) Single-Slice Dyadic Refutation of `CenterPeriodic` (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_support_rhbandagree_twopow_kit
    (T P m t k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = Rule30UOR.Core.twopow k)
    (hband : Rule30UOR.Interfaces.RhBandAgree t (m * P) 1 (t + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_support_rhbandagree_twopow T P m t k hP hm ht htm hband

/-- **Support-Width Single-Slice Zero-Diagonal Pair Refutation of `CenterPeriodic` (`kit [33]`) from the verified paper**. -/
theorem not_centerperiodic_of_support_rhbandagree_at_zero_diag_pair_kit
    (T P m z k : Nat) (hP : 0 < P)
    (hz0 : Rule30UOR.ZeroDiagonals.IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : Rule30UOR.ZeroDiagonals.IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + Rule30UOR.Core.twopow k)
    (hset0 : Rule30UOR.Interfaces.SettledBy z (z + Rule30UOR.Core.twopow k))
    (hset1 : Rule30UOR.Interfaces.SettledBy (z + m * P) ((z + m * P) + Rule30UOR.Core.twopow k))
    (hband : Rule30UOR.Interfaces.RhBandAgree (z + Rule30UOR.Core.twopow k) (m * P) 1 ((z + Rule30UOR.Core.twopow k) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  Rule30Paper.Paper.not_centerperiodic_of_support_rhbandagree_at_zero_diag_pair T P m z k hP hz0 h2 hz1 ht hset0 hset1 hband

/-- **Dyadic Row White Tail of `rdrv` at Step `v * 2^tx` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_row_tx_gt_eq_false_kit (td tx v q : Nat) (hq : tx < q) :
    Rule30UOR.Interfaces.rdrv td tx (v * Rule30UOR.Core.twopow tx) ((v * Rule30UOR.Core.twopow tx) + q) = false :=
  Rule30Paper.Paper.rdrv_dyadic_row_tx_gt_eq_false td tx v q hq

/-- **Dyadic Row White Tail of `rhCenter` at Time `t + v * 2^t` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_t_gt_eq_false_kit (t v q : Nat) (hq : t < q) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow t) ((v * Rule30UOR.Core.twopow t) + q) = false :=
  Rule30Paper.Paper.rhcenter_dyadic_row_t_gt_eq_false t v q hq

/-- **All-Width Pullback of `RhBandAgree t Q 1 B` from Support-Width Shifted Dyadic Row Agreement (`kit [33]`) from the verified paper**. -/
theorem rhbandagree_all_of_dyadic_row_support_agree_kit (t Q K v B : Nat) (htK : t + Q ≤ K)
    (hband : Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow K) Q ((v * Rule30UOR.Core.twopow K) + 1) (t + Q)) :
    Rule30UOR.Interfaces.RhBandAgree t Q 1 B :=
  Rule30Paper.Paper.rhbandagree_all_of_dyadic_row_support_agree t Q K v B htK hband

/-- **All-Time `maskparity · 0` Agreement from Support-Width Shifted Dyadic Row Agreement (`kit [33]`) from the verified paper**. -/
theorem periodic_maskparity_zero_agree_all_of_dyadic_row_support_agree_kit
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v s : Nat) (ht : T ≤ t) (htK : t + m * P ≤ K)
    (hband : Rule30UOR.Interfaces.RhBandAgree (t + v * Rule30UOR.Core.twopow K) (m * P) ((v * Rule30UOR.Core.twopow K) + 1) (t + m * P)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  Rule30Paper.Paper.periodic_maskparity_zero_agree_all_of_dyadic_row_support_agree T P hP hper m t K v s ht htK hband

/-- **Spatial Left-Inversion Law of `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_left_step_inv_kit (td tx k p : Nat) :
    Rule30UOR.Interfaces.rdrv td tx k p =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (k + 1) (p + 1))
        (Rule30UOR.Interfaces.rdrv td tx k (p + 1) || Rule30UOR.Interfaces.rdrv td tx k (p + 2)) :=
  Rule30Paper.Paper.rdrv_left_step_inv td tx k p

/-- **Subtracted-Column Left-Inversion Law of `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_left_step_inv_sub_kit (td tx k U d : Nat) (hdU : d + 1 ≤ U) :
    Rule30UOR.Interfaces.rdrv td tx k (U - (d + 1)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rdrv td tx (k + 1) (U - d))
        (Rule30UOR.Interfaces.rdrv td tx k (U - d) || Rule30UOR.Interfaces.rdrv td tx k ((U - d) + 1)) :=
  Rule30Paper.Paper.rdrv_left_step_inv_sub td tx k U d hdU

/-- **Spatial Left-Inversion Law of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_left_step_inv_kit (t p : Nat) :
    Rule30UOR.Interfaces.rhCenter t p =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + 1) (p + 1))
        (Rule30UOR.Interfaces.rhCenter t (p + 1) || Rule30UOR.Interfaces.rhCenter t (p + 2)) :=
  Rule30Paper.Paper.rhcenter_left_step_inv t p

/-- **Subtracted-Column Left-Inversion Law of `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_left_step_inv_sub_kit (t U d : Nat) (hdU : d + 1 ≤ U) :
    Rule30UOR.Interfaces.rhCenter t (U - (d + 1)) =
      Rule30UOR.Core.bxor (Rule30UOR.Interfaces.rhCenter (t + 1) (U - d))
        (Rule30UOR.Interfaces.rhCenter t (U - d) || Rule30UOR.Interfaces.rhCenter t ((U - d) + 1)) :=
  Rule30Paper.Paper.rhcenter_left_step_inv_sub t U d hdU

/-- **Exact Readout of Predecessor Column `v * 2^(tx + C) - 1` in `rdrv` (`kit [33]`) from the verified paper**. -/
theorem rdrv_dyadic_pred_col_eq_center_xor_kit (td tx C v j : Nat)
    (hv : 1 ≤ v) (hj : j + 1 ≤ C) :
    Rule30UOR.Interfaces.rdrv td tx ((v * Rule30UOR.Core.twopow (tx + C)) + j) ((v * Rule30UOR.Core.twopow (tx + C)) - 1) =
      Rule30UOR.Core.bxor (Rule30UOR.Core.center (td + (j + 1)))
        (Rule30UOR.Core.center (td + j) || Rule30UOR.Interfaces.rdrv td tx j 1) :=
  Rule30Paper.Paper.rdrv_dyadic_pred_col_eq_center_xor td tx C v j hv hj

/-- **Exact Embedding of Left-Half Column `-1` (`lhCenter (t + j) 1`) at Right-Half Column `v * 2^(t + C) - 1` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_pred_col_t_add_eq_lhcenter_one_kit (t C v j : Nat)
    (hv : 1 ≤ v) (hj : j + 1 ≤ C) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow (t + C)) + j)) ((v * Rule30UOR.Core.twopow (t + C)) - 1) =
      Rule30UOR.Interfaces.lhCenter (t + j) 1 :=
  Rule30Paper.Paper.rhcenter_dyadic_pred_col_t_add_eq_lhcenter_one t C v j hv hj

/-- **Delay-Free Embedding of Left-Half Column `-1` (`lhCenter j 1`) at Right-Half Column `v * 2^C - 1` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_pred_col_zero_delay_eq_lhcenter_one_kit (C v j : Nat)
    (hv : 1 ≤ v) (hj : j + 1 ≤ C) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) - 1) =
      Rule30UOR.Interfaces.lhCenter j 1 :=
  Rule30Paper.Paper.rhcenter_dyadic_pred_col_zero_delay_eq_lhcenter_one C v j hv hj

/-- **General Left-Inversion Propagation of `lhCenter` to the Left of Column `U` in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_sub_eq_lhcenter_of_col_eq_center_and_one_kit
    (t T0 U C d j : Nat)
    (hdU : d ≤ U) (hjd : j + d ≤ C)
    (h0 : ∀ s : Nat, s ≤ C → Rule30UOR.Interfaces.rhCenter (T0 + s) U = Rule30UOR.Core.center (t + s))
    (h1 : ∀ s : Nat, s + 1 ≤ C → Rule30UOR.Interfaces.rhCenter (T0 + s) (U - 1) = Rule30UOR.Interfaces.lhCenter (t + s) 1) :
    Rule30UOR.Interfaces.rhCenter (T0 + j) (U - d) = Rule30UOR.Interfaces.lhCenter (t + j) d :=
  Rule30Paper.Paper.rhcenter_sub_eq_lhcenter_of_col_eq_center_and_one t T0 U C d j hdU hjd h0 h1

/-- **Full Embedding of the Left Half `lhCenter (t + j) d` Inside the Right Half `rhCenter` to the Left of `U = v * 2^(t + C)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_sub_eq_lhcenter_t_add_kit (t C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * Rule30UOR.Core.twopow (t + C)) (hjd : j + d ≤ C) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow (t + C)) + j)) ((v * Rule30UOR.Core.twopow (t + C)) - d) =
      Rule30UOR.Interfaces.lhCenter (t + j) d :=
  Rule30Paper.Paper.rhcenter_dyadic_sub_eq_lhcenter_t_add t C v d j hv hdU hjd

/-- **Delay-Free Full Embedding of the Left Half `lhCenter j d` Inside the Right Half `rhCenter` to the Left of `U = v * 2^C` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_sub_eq_lhcenter_zero_delay_kit (C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * Rule30UOR.Core.twopow C) (hjd : j + d ≤ C) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) - d) =
      Rule30UOR.Interfaces.lhCenter j d :=
  Rule30Paper.Paper.rhcenter_dyadic_sub_eq_lhcenter_zero_delay C v d j hv hdU hjd

/-- **Left-Side White Isolation Corridor Around `U = v * 2^(t + C)` in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_left_white_corridor_t_add_kit (t C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * Rule30UOR.Core.twopow (t + C)) (hjd : j + d ≤ C) (htd : t + j < d) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow (t + C)) + j)) ((v * Rule30UOR.Core.twopow (t + C)) - d) = false :=
  Rule30Paper.Paper.rhcenter_dyadic_left_white_corridor_t_add t C v d j hv hdU hjd htd

/-- **Delay-Free Left-Side White Isolation Corridor Around `U = v * 2^C` in `rhCenter` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_left_white_corridor_zero_delay_kit (C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * Rule30UOR.Core.twopow C) (hjd : j + d ≤ C) (hjd2 : j < d) :
    Rule30UOR.Interfaces.rhCenter ((v * Rule30UOR.Core.twopow C) + j) ((v * Rule30UOR.Core.twopow C) - d) = false :=
  Rule30Paper.Paper.rhcenter_dyadic_left_white_corridor_zero_delay C v d j hv hdU hjd hjd2

/-- **Horizontal Row Left-Side White Isolation Corridor at `t + v * 2^(t + C)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_left_white_corridor_t_add_kit (t C v d : Nat)
    (hv : 1 ≤ v) (hdC : d ≤ C) (htd : t < d) :
    Rule30UOR.Interfaces.rhCenter (t + v * Rule30UOR.Core.twopow (t + C)) ((v * Rule30UOR.Core.twopow (t + C)) - d) = false :=
  Rule30Paper.Paper.rhcenter_dyadic_row_left_white_corridor_t_add t C v d hv hdC htd

/-- **Delay-Free Horizontal Row Left-Side White Isolation Corridor at `v * 2^C` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_row_left_white_corridor_zero_delay_kit (C v d : Nat)
    (hv : 1 ≤ v) (hd1 : 1 ≤ d) (hdC : d ≤ C) :
    Rule30UOR.Interfaces.rhCenter (v * Rule30UOR.Core.twopow C) ((v * Rule30UOR.Core.twopow C) - d) = false :=
  Rule30Paper.Paper.rhcenter_dyadic_row_left_white_corridor_zero_delay C v d hv hd1 hdC

/-- **Direct Embedding of Left Diagonals `ldiag` Inside the Right Half `rhCenter` to the Left of `U = v * 2^(t + C)` (`kit [33]`) from the verified paper**. -/
theorem rhcenter_dyadic_sub_eq_ldiag_t_add_kit (t C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * Rule30UOR.Core.twopow (t + C)) (hjd : j + d ≤ C) (hdt : d ≤ t + j) :
    Rule30UOR.Interfaces.rhCenter (t + ((v * Rule30UOR.Core.twopow (t + C)) + j)) ((v * Rule30UOR.Core.twopow (t + C)) - d) =
      Rule30UOR.Core.ldiag ((t + j) - d) (t + j) :=
  Rule30Paper.Paper.rhcenter_dyadic_sub_eq_ldiag_t_add t C v d j hv hdU hjd hdt

end Rule30Bridge
