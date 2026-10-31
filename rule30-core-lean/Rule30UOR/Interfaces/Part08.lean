module

public import Rule30UOR.Interfaces.Part07

/-!
# `Rule30UOR.Interfaces`, part 8

* Batch 18: Post-Zero Black-Diagonal Window Mirrors and 1-Step Reset Complementarity in `lhCenter` and `winWitt`
* Batch 19: Fixed-Bit Zero-to-Black Diagonal Jump Under 1 Time Step and Linearized `Φ` Evolution Before Zero Diagonals
* Batch 20: Real-Orbit Twin Identity Before a Zero Diagonal and Antiperiodic Sector-2 Window Flips at Doubling Zero Diagonals (9.592–9.606)
* Batch 21: Post-Black Reset Antiperiodicity on Diagonal `z + 3`, Space-Time Equivalence of `(t + P, z + 1)` and `(t + 1, z + 3)`, and `zcenter` Twin/Doubling Readouts (9.607–9.621)
* Batch 22: Center-Boundary Post-Black Reset Bridges (`2^k ↔ 2^k - 1` and `1 + 2^k ↔ 2^k`), `!zcenter (z + 1)` Readouts at `z + 2`, and Sector-2 Zero-Gap `WinWittAgree` Refutations (9.622–9.636)
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

/-! ### Batch 18: Post-Zero Black-Diagonal Window Mirrors and 1-Step Reset Complementarity in `lhCenter` and `winWitt` -/

theorem not_isZeroDiag_zero (hz : IsZeroDiag 0) : False := by
  have h0 := hz 0
  rw [Rule30UOR.ZeroDiagonals.E_zero'] at h0
  exact absurd h0 (by decide)

theorem add_five_le_twopow : ∀ k : Nat, 3 ≤ k → k + 5 ≤ twopow k
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by decide
  | k + 4, _ => by
    have ih := add_five_le_twopow (k + 3) (by omega)
    have hstep : twopow (k + 4) = twopow (k + 3) + twopow (k + 3) :=
      Rule30UOR.Core.twopow_succ (k + 3)
    omega

theorem gt_twopow_of_zero_diag_le (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z) :
    z + 7 ≤ twopow k := by
  have hz0 : z ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have hk3 : 3 ≤ k := by omega
  have h5 := add_five_le_twopow k hk3
  omega

/-- **Exact Late Left-Half Pinning Along the Post-Zero Black Diagonal (`lhCenter_late_shift_after_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `(t - p) + 2 ≤ k`, `IsZeroDiag (t - p)`, and `settle ((t - p) + 2) ≤ (t + 2) + 2^k` (`SettledBy ((t - p) + 2) ((t + 2) + 2^k)`), the late shifted cell `lhCenter ((t + 2) + 2^k) (p + 2^k)` lies on the post-zero black diagonal `(t - p) + 2` and equals `true`! -/
theorem lhCenter_late_shift_after_zero_diag (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle ((t - p) + 2) ≤ (t + 2) + twopow k) :
    lhCenter ((t + 2) + twopow k) (p + twopow k) = true := by
  rw [lhCenter_late_shift_eq_ldiag (t + 2) k p (by omega),
    show (t + 2) - p = (t - p) + 2 by omega,
    ldiag_settled_eq_E ((t - p) + 2) (t + 2) k hk hset]
  exact black_after_zero_diag (t - p) hz (t + 2)

theorem lhCenter_late_shift_after_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy ((t - p) + 2) ((t + 2) + twopow k)) :
    lhCenter ((t + 2) + twopow k) (p + twopow k) = true :=
  lhCenter_late_shift_after_zero_diag t k p hp hk hz hset

/-- **Exact Late Cross-Center Pinning Along the Post-Zero Black Diagonal (`lhCenter_late_cross_after_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (`SettledBy ((t + r) + 2) (t + 2^k)`), the late cross-center cell `lhCenter (t + 2^k) (2^k - (r + 2))` lies on the post-zero black diagonal `(t + r) + 2` and equals `true`! -/
theorem lhCenter_late_cross_after_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true := by
  have hrk : r + 2 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  rw [lhCenter_late_cross_eq_ldiag t k (r + 2) hrk,
    show t + (r + 2) = (t + r) + 2 by omega,
    ldiag_settled_eq_E ((t + r) + 2) t k hk hset]
  exact black_after_zero_diag (t + r) hz t

theorem lhCenter_late_cross_after_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_after_zero_diag t k r hk hz hset

/-- **Negated Sector-2 Outer-Strip Window Mirror Along the Post-Zero Black Diagonal (`winWitt_testBit_outer_left_strip_after_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `(t - p) + 2 ≤ k`, `IsZeroDiag (t - p)`, and `settle ((t - p) + 2) ≤ (t + 2) + 2^k`, because `lhCenter ((t + 2) + 2^k) (p + 2^k) = true`, the Sector-2 window bit `(winWitt (t + 2) (2^k)).testBit (((t + 2) + p) + 2^(k+1))` equals `!lhCenter (t + 2) p`! -/
theorem winWitt_testBit_outer_left_strip_after_zero_diag (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle ((t - p) + 2) ≤ (t + 2) + twopow k) :
    (winWitt (t + 2) (twopow k)).testBit (((t + 2) + p) + twopow (k + 1)) =
      !lhCenter (t + 2) p := by
  have hlt : t + 2 < p + twopow k := by
    have h7 := gt_twopow_of_zero_diag_le (t - p) k hk hz
    omega
  rw [winWitt_testBit_outer_left_strip (t + 2) k p hlt,
    lhCenter_late_shift_after_zero_diag t k p hp hk hz hset]
  cases lhCenter (t + 2) p <;> rfl

theorem winWitt_testBit_outer_left_strip_after_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy ((t - p) + 2) ((t + 2) + twopow k)) :
    wittBitBool (winWitt (t + 2) (twopow k)) (((t + 2) + p) + twopow (k + 1)) =
      !lhCenter (t + 2) p :=
  winWitt_testBit_outer_left_strip_after_zero_diag t k p hp hk hz hset

/-- **Negated Sector-2 Cross-Center Window Mirror Along the Post-Zero Black Diagonal (`winWitt_testBit_scale_cross_after_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k`, because `lhCenter (t + 2^k) (2^k - (r + 2)) = true`, the Sector-2 cross-center window bit `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2))` equals `!rhCenter t (r + 2)`! -/
theorem winWitt_testBit_scale_cross_after_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) =
      !rhCenter t (r + 2) := by
  have hlt : t + (r + 2) < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_cone t k (r + 2) hlt,
    lhCenter_late_cross_after_zero_diag t k r hk hz hset]
  cases rhCenter t (r + 2) <;> rfl

theorem winWitt_testBit_scale_cross_after_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) =
      !rhCenter t (r + 2) :=
  winWitt_testBit_scale_cross_after_zero_diag t k r hk hz hset

/-- **Exact Constant-`true` Pinning of Sector-2 Cross-Center `winWitt` in the Inter-Cone Zero Gap Along the Post-Zero Black Diagonal (`winWitt_testBit_scale_cross_zero_gap_after_zero_diag`)**:
    for all `t, k, r : Nat` with `t < r + 2`, `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k`, `lhCenter (t + 2^k) (2^k - (r + 2)) = true` while `rhCenter t (r + 2) = false`, so `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true`! -/
theorem winWitt_testBit_scale_cross_zero_gap_after_zero_diag (t k r : Nat)
    (htr : t < r + 2) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  rw [winWitt_testBit_scale_cross_after_zero_diag t k r hk hz hset,
    rhCenter_gt_eq_false t (r + 2) htr]
  rfl

theorem winWitt_testBit_scale_cross_zero_gap_after_zero_diag_prop (t k r : Nat)
    (htr : t < r + 2) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_testBit_scale_cross_zero_gap_after_zero_diag t k r htr hk hz hset

/-- **Negated Cross-Sector Window Readout of Late `lhCenter ((t + 2) + 2^k) p` Along the Post-Zero Black Diagonal (`winWitt_sector_one_xor_sector_two_lhCenter_after_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `(t + 2) + p < 2^k`, `(t - p) + 2 ≤ k`, `IsZeroDiag (t - p)`, and `settle ((t - p) + 2) ≤ (t + 2) + 2^k`, `(winWitt (t + 2) (2^k)).testBit (((t + 2) + p) + 2^k) ⊕ (winWitt (t + 2) (2^k)).testBit (((t + 2) + p) + 2^(k+1)) = !lhCenter ((t + 2) + 2^k) p`! -/
theorem winWitt_sector_one_xor_sector_two_lhCenter_after_zero_diag (t k p : Nat)
    (hp : p ≤ t) (htp : (t + 2) + p < twopow k) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle ((t - p) + 2) ≤ (t + 2) + twopow k) :
    bxor
      ((winWitt (t + 2) (twopow k)).testBit (((t + 2) + p) + twopow k))
      ((winWitt (t + 2) (twopow k)).testBit (((t + 2) + p) + twopow (k + 1))) =
      !lhCenter ((t + 2) + twopow k) p := by
  rw [winWitt_sector_one_xor_sector_two_lhCenter_cone (t + 2) k p htp,
    lhCenter_late_shift_after_zero_diag t k p hp hk hz hset]
  cases lhCenter ((t + 2) + twopow k) p <;> rfl

theorem winWitt_sector_one_xor_sector_two_lhCenter_after_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (htp : (t + 2) + p < twopow k) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy ((t - p) + 2) ((t + 2) + twopow k)) :
    bxor
      (wittBitBool (winWitt (t + 2) (twopow k)) (((t + 2) + p) + twopow k))
      (wittBitBool (winWitt (t + 2) (twopow k)) (((t + 2) + p) + twopow (k + 1))) =
      !lhCenter ((t + 2) + twopow k) p :=
  winWitt_sector_one_xor_sector_two_lhCenter_after_zero_diag t k p hp htp hk hz hset

/-- **Negated Cross-Sector Window Readout of Late `rhCenter (t + 2^k) (r + 2)` Along the Post-Zero Black Diagonal (`winWitt_sector_one_xor_sector_two_rhCenter_after_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k`, `(winWitt t (2^k)).testBit ((t + 2^k) - (r + 2)) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !rhCenter (t + 2^k) (r + 2)`! -/
theorem winWitt_sector_one_xor_sector_two_rhCenter_after_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow k) - (r + 2)))
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2))) =
      !rhCenter (t + twopow k) (r + 2) := by
  have hlt : t + (r + 2) < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_sector_one_xor_sector_two_rhCenter_cone t k (r + 2) hlt,
    lhCenter_late_cross_after_zero_diag t k r hk hz hset]
  cases rhCenter (t + twopow k) (r + 2) <;> rfl

theorem winWitt_sector_one_xor_sector_two_rhCenter_after_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (r + 2)))
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2))) =
      !rhCenter (t + twopow k) (r + 2) :=
  winWitt_sector_one_xor_sector_two_rhCenter_after_zero_diag t k r hk hz hset

/-- **Exact Pinning of `lhCenter ((z + 2) + 2^k) (2^k) = true` Two Steps Past Any Zero Diagonal `z` (`lhCenter_late_twopow_after_zero_diag`)**:
    for all `z, k : Nat` with `z + 2 ≤ k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + 2^k` (`SettledAt (z + 2) k`), `lhCenter ((z + 2) + 2^k) (2^k) = true`! -/
theorem lhCenter_late_twopow_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    lhCenter ((z + 2) + twopow k) (twopow k) = true := by
  rw [lhCenter_late_twopow_eq_zcenter (z + 2) k hk hset,
    zcenter_after_zero_diag z hz]

theorem lhCenter_late_twopow_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z) (hset : SettledAt (z + 2) k) :
    lhCenter ((z + 2) + twopow k) (twopow k) = true :=
  lhCenter_late_twopow_after_zero_diag z k hk hz hset

/-- **Negated Sector-2 Window Readout of `!center (z + 2)` Two Steps Past Any Zero Diagonal `z` (`winWitt_testBit_sector_two_center_slot_after_zero_diag`)**:
    for all `z, k : Nat` with `z + 2 ≤ k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + 2^k` (`SettledAt (z + 2) k`), `(winWitt (z + 2) (2^k)).testBit ((z + 2) + 2^(k+1)) = !center (z + 2)`! -/
theorem winWitt_testBit_sector_two_center_slot_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    (winWitt (z + 2) (twopow k)).testBit ((z + 2) + twopow (k + 1)) =
      !Rule30UOR.Core.center (z + 2) := by
  have h := winWitt_testBit_sector_two_center_slot_zcenter (z + 2) k hk hset
  rw [zcenter_after_zero_diag z hz] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt (z + 2) (twopow k)).testBit ((z + 2) + twopow (k + 1)) <;>
    cases Rule30UOR.Core.center (z + 2) <;> decide

theorem winWitt_testBit_sector_two_center_slot_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z) (hset : SettledAt (z + 2) k) :
    wittBitBool (winWitt (z + 2) (twopow k)) ((z + 2) + twopow (k + 1)) =
      !Rule30UOR.Core.center (z + 2) :=
  winWitt_testBit_sector_two_center_slot_after_zero_diag z k hk hz hset

/-- **Negated Cross-Sector Window Readout of Late `!center ((z + 2) + 2^k)` Two Steps Past Any Zero Diagonal `z` (`winWitt_sector_one_xor_sector_two_center_slot_after_zero_diag`)**:
    for all `z, k : Nat` with `z + 2 ≤ k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + 2^k` (`SettledAt (z + 2) k`), `(winWitt (z + 2) (2^k)).testBit ((z + 2) + 2^k) ⊕ (winWitt (z + 2) (2^k)).testBit ((z + 2) + 2^(k+1)) = !center ((z + 2) + 2^k)`! -/
theorem winWitt_sector_one_xor_sector_two_center_slot_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor
      ((winWitt (z + 2) (twopow k)).testBit ((z + 2) + twopow k))
      ((winWitt (z + 2) (twopow k)).testBit ((z + 2) + twopow (k + 1))) =
      !Rule30UOR.Core.center ((z + 2) + twopow k) := by
  have h := winWitt_sector_one_xor_sector_two_center_slot_zcenter (z + 2) k hk hset
  rw [zcenter_after_zero_diag z hz] at h
  revert h
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center ((z + 2) + twopow k) <;>
    cases ((winWitt (z + 2) (twopow k)).testBit ((z + 2) + twopow k) ^^
      (winWitt (z + 2) (twopow k)).testBit ((z + 2) + twopow (k + 1))) <;> decide

theorem winWitt_sector_one_xor_sector_two_center_slot_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z) (hset : SettledAt (z + 2) k) :
    bxor
      (wittBitBool (winWitt (z + 2) (twopow k)) ((z + 2) + twopow k))
      (wittBitBool (winWitt (z + 2) (twopow k)) ((z + 2) + twopow (k + 1))) =
      !Rule30UOR.Core.center ((z + 2) + twopow k) :=
  winWitt_sector_one_xor_sector_two_center_slot_after_zero_diag z k hk hz hset

/-- **Real-Orbit Cross-Center Reset Law Across the Post-Zero Black Diagonal (`lhCenter_late_cross_reset_after_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k` (with NO settlement hypothesis on `(t + r) + 1` or `(t + r) + 3`!), because `lhCenter (t + 2^k) (2^k - (r + 2)) = true` forces the OR gate in `lhCenter_step_succ` to `true`, `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`! -/
theorem lhCenter_late_cross_reset_after_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have hr3 : r + 3 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  have hs := lhCenter_step_succ (t + twopow k) (twopow k - (r + 3))
  rw [show (t + twopow k) + 1 = (t + 1) + twopow k by omega,
    show (twopow k - (r + 3)) + 1 = twopow k - (r + 2) by omega,
    show (twopow k - (r + 3)) + 2 = twopow k - (r + 1) by omega,
    lhCenter_late_cross_after_zero_diag t k r hk hz hset,
    Bool.true_or] at hs
  rw [hs]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> rfl

theorem lhCenter_late_cross_reset_after_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_reset_after_zero_diag t k r hk hz hset

/-- **Real-Orbit Outer-Strip Reset Law Across the Post-Zero Black Diagonal (`lhCenter_late_shift_reset_after_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `(t - p) + 2 ≤ k`, `IsZeroDiag (t - p)`, and `settle ((t - p) + 2) ≤ (t + 2) + 2^k`, because `lhCenter ((t + 2) + 2^k) (p + 2^k) = true` forces the OR gate in `lhCenter_step_succ ((t + 2) + 2^k) (p + 2^k)` to `true`, `lhCenter ((t + 3) + 2^k) ((p + 1) + 2^k) = !lhCenter ((t + 2) + 2^k) ((p + 2) + 2^k)`! -/
theorem lhCenter_late_shift_reset_after_zero_diag (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle ((t - p) + 2) ≤ (t + 2) + twopow k) :
    lhCenter ((t + 3) + twopow k) ((p + 1) + twopow k) =
      !lhCenter ((t + 2) + twopow k) ((p + 2) + twopow k) := by
  have hs := lhCenter_step_succ ((t + 2) + twopow k) (p + twopow k)
  rw [show ((t + 2) + twopow k) + 1 = (t + 3) + twopow k by omega,
    show (p + twopow k) + 1 = (p + 1) + twopow k by omega,
    show (p + twopow k) + 2 = (p + 2) + twopow k by omega,
    lhCenter_late_shift_after_zero_diag t k p hp hk hz hset,
    Bool.or_true] at hs
  rw [hs]
  cases lhCenter ((t + 2) + twopow k) ((p + 2) + twopow k) <;> rfl

theorem lhCenter_late_shift_reset_after_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy ((t - p) + 2) ((t + 2) + twopow k)) :
    lhCenter ((t + 3) + twopow k) ((p + 1) + twopow k) =
      !lhCenter ((t + 2) + twopow k) ((p + 2) + twopow k) :=
  lhCenter_late_shift_reset_after_zero_diag t k p hp hk hz hset

/-- **Sector-2 1-Step Window Complementation Across the Post-Zero Black Diagonal (`winWitt_sector_two_step_complement_after_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k`, combining `winWitt_testBit_scale_cross_cone` at `(t, r + 1)` and `(t + 1, r + 2)` with `lhCenter_late_cross_reset_after_zero_diag` cancels the intermediate cell `lhCenter (t + 2^k) (2^k - (r + 1))` at the fixed Sector-2 bit index `(t + 2^(k+1)) - (r + 1)`! -/
theorem winWitt_sector_two_step_complement_after_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)))
      ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter t (r + 1)) (rhCenter (t + 1) (r + 2))) := by
  have h7 := gt_twopow_of_zero_diag_le (t + r) k hk hz
  have h1 := winWitt_testBit_scale_cross_cone t k (r + 1) (by omega)
  have h2 := winWitt_testBit_scale_cross_cone (t + 1) k (r + 2) (by omega)
  rw [show ((t + 1) + twopow (k + 1)) - (r + 2) = (t + twopow (k + 1)) - (r + 1) by omega,
    lhCenter_late_cross_reset_after_zero_diag t k r hk hz hset] at h2
  rw [h1, h2]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases rhCenter t (r + 1) <;>
    cases rhCenter (t + 1) (r + 2) <;> rfl

theorem winWitt_sector_two_step_complement_after_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)))
      (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter t (r + 1)) (rhCenter (t + 1) (r + 2))) :=
  winWitt_sector_two_step_complement_after_zero_diag t k r hk hz hset

/-- **Unconditional 1-Step Bit Flip of Sector-2 `winWitt` in the Inter-Cone Zero Gap Across a Zero Diagonal (`winWitt_sector_two_step_flip_zero_gap_after_zero_diag`)**:
    for all `t, k, r : Nat` with `t ≤ r`, `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k`, both `rhCenter t (r + 1) = false` and `rhCenter (t + 1) (r + 2) = false`, so the fixed Sector-2 bit `(t + 2^(k+1)) - (r + 1)` of `winWitt` flips unconditionally between `t` and `t + 1`! -/
theorem winWitt_sector_two_step_flip_zero_gap_after_zero_diag (t k r : Nat)
    (htr : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have hc := winWitt_sector_two_step_complement_after_zero_diag t k r hk hz hset
  rw [rhCenter_gt_eq_false t (r + 1) (by omega),
    rhCenter_gt_eq_false (t + 1) (r + 2) (by omega)] at hc
  revert hc
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;>
    cases (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_sector_two_step_flip_zero_gap_after_zero_diag_prop (t k r : Nat)
    (htr : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) :=
  winWitt_sector_two_step_flip_zero_gap_after_zero_diag t k r htr hk hz hset

/-- **Early-Free Cross-Sector 1-Step Window Complementation of Late `rhCenter` Across the Post-Zero Black Diagonal (`winWitt_sector_one_xor_sector_two_step_complement_after_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ t + 2^k`, combining `winWitt_sector_one_xor_sector_two_rhCenter_cone` at `(t, r + 1)` and `(t + 1, r + 2)` with `lhCenter_late_cross_reset_after_zero_diag` cancels `lhCenter (t + 2^k) (2^k - (r + 1))` at the fixed bit indices `(t + 2^k) - (r + 1)` and `(t + 2^(k+1)) - (r + 1)`! -/
theorem winWitt_sector_one_xor_sector_two_step_complement_after_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    bxor
      (bxor
        ((winWitt t (twopow k)).testBit ((t + twopow k) - (r + 1)))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1))))
      (bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow k) - (r + 1)))
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)))) =
      !(bxor
        (rhCenter (t + twopow k) (r + 1))
        (rhCenter ((t + 1) + twopow k) (r + 2))) := by
  have h7 := gt_twopow_of_zero_diag_le (t + r) k hk hz
  have h1 := winWitt_sector_one_xor_sector_two_rhCenter_cone t k (r + 1) (by omega)
  have h2 := winWitt_sector_one_xor_sector_two_rhCenter_cone (t + 1) k (r + 2) (by omega)
  rw [show ((t + 1) + twopow k) - (r + 2) = (t + twopow k) - (r + 1) by omega,
    show ((t + 1) + twopow (k + 1)) - (r + 2) = (t + twopow (k + 1)) - (r + 1) by omega,
    lhCenter_late_cross_reset_after_zero_diag t k r hk hz hset] at h2
  rw [h1, h2]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases rhCenter (t + twopow k) (r + 1) <;>
    cases rhCenter ((t + 1) + twopow k) (r + 2) <;> rfl

theorem winWitt_sector_one_xor_sector_two_step_complement_after_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (r + 1)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))))
      (bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow k) - (r + 1)))
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)))) =
      !(bxor
        (rhCenter (t + twopow k) (r + 1))
        (rhCenter ((t + 1) + twopow k) (r + 2))) :=
  winWitt_sector_one_xor_sector_two_step_complement_after_zero_diag t k r hk hz hset

/-! ### Batch 19: Fixed-Bit Zero-to-Black Diagonal Jump Under 1 Time Step and Linearized `Φ` Evolution Before Zero Diagonals -/

/-- **1-Step Fixed-Bit Jump from Zero Diagonal `t + r` to Post-Zero Black Diagonal `(t + r) + 2` in `lhCenter` (`lhCenter_late_cross_step_one_of_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ (t + 1) + 2^k` (`SettledBy ((t + r) + 2) ((t + 1) + 2^k)`), at time `(t + 1) + 2^k` column `2^k - (r + 1)` sits on left diagonal `(t + 1) + (r + 1) = (t + r) + 2`, so `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true`! -/
theorem lhCenter_late_cross_step_one_of_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ (t + 1) + twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true := by
  have hr1 : r + 1 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  rw [lhCenter_late_cross_eq_ldiag (t + 1) k (r + 1) hr1,
    show (t + 1) + (r + 1) = (t + r) + 2 by omega,
    ldiag_settled_eq_E ((t + r) + 2) (t + 1) k hk hset]
  exact black_after_zero_diag (t + r) hz (t + 1)

theorem lhCenter_late_cross_step_one_of_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) ((t + 1) + twopow k)) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_step_one_of_zero_diag t k r hk hz hset

/-- **Negated Sector-2 Window Readout at Fixed Bit `(t + 2^(k+1)) - r` One Step After Zero Diagonal `t + r` (`winWitt_testBit_scale_cross_step_one_of_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ (t + 1) + 2^k`, at time `t + 1` the same Sector-2 bit index `(t + 2^(k+1)) - r = ((t + 1) + 2^(k+1)) - (r + 1)` reads `!rhCenter (t + 1) (r + 1)`! -/
theorem winWitt_testBit_scale_cross_step_one_of_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ (t + 1) + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      !rhCenter (t + 1) (r + 1) := by
  have hlt : (t + 1) + (r + 1) < twopow k := by
    have := twopow_gt_self k
    omega
  have hw := winWitt_testBit_scale_cross_cone (t + 1) k (r + 1) hlt
  rw [show ((t + 1) + twopow (k + 1)) - (r + 1) = (t + twopow (k + 1)) - r by omega,
    lhCenter_late_cross_step_one_of_zero_diag t k r hk hz hset] at hw
  rw [hw]
  cases rhCenter (t + 1) (r + 1) <;> rfl

theorem winWitt_testBit_scale_cross_step_one_of_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) ((t + 1) + twopow k)) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) =
      !rhCenter (t + 1) (r + 1) :=
  winWitt_testBit_scale_cross_step_one_of_zero_diag t k r hk hz hset

/-- **Exact `false → true` Jump at Fixed Sector-2 Bit `(t + 2^(k+1)) - r` in the Inter-Cone Zero Gap (`winWitt_testBit_scale_cross_zero_gap_step_one_of_zero_diag`)**:
    for all `t, k, r : Nat` with `t < r`, `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ (t + 1) + 2^k`, at time `t + 1` the exact same bit `(t + 2^(k+1)) - r` (which was `false` at time `t` by `winWitt_testBit_scale_cross_zero_gap_of_zero_diag`) equals `true`! -/
theorem winWitt_testBit_scale_cross_zero_gap_step_one_of_zero_diag (t k r : Nat)
    (htr : t < r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ (t + 1) + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  rw [winWitt_testBit_scale_cross_step_one_of_zero_diag t k r hk hz hset,
    rhCenter_gt_eq_false (t + 1) (r + 1) (by omega)]
  rfl

theorem winWitt_testBit_scale_cross_zero_gap_step_one_of_zero_diag_prop (t k r : Nat)
    (htr : t < r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) ((t + 1) + twopow k)) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_testBit_scale_cross_zero_gap_step_one_of_zero_diag t k r htr hk hz hset

/-- **Sector-2 Fixed-Bit 1-Step Zero-to-Black Transition Across Zero Diagonal `t + r` (`winWitt_sector_two_zero_to_black_step_of_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, `settle (t + r) ≤ t + 2^k`, and `settle ((t + r) + 2) ≤ (t + 1) + 2^k`, XORing bit `(t + 2^(k+1)) - r` of `winWitt` at times `t` and `t + 1` gives `!(rhCenter t r ⊕ rhCenter (t + 1) (r + 1))`! -/
theorem winWitt_sector_two_zero_to_black_step_of_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset0 : settle (t + r) ≤ t + twopow k)
    (hset2 : settle ((t + r) + 2) ≤ (t + 1) + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r))
      ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r)) =
      !(bxor (rhCenter t r) (rhCenter (t + 1) (r + 1))) := by
  rw [winWitt_testBit_scale_cross_of_zero_diag t k r (by omega) hz hset0,
    winWitt_testBit_scale_cross_step_one_of_zero_diag t k r hk hz hset2]
  simp only [bxor_eq_xor]
  cases rhCenter t r <;> cases rhCenter (t + 1) (r + 1) <;> rfl

theorem winWitt_sector_two_zero_to_black_step_of_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset0 : SettledBy (t + r) (t + twopow k))
    (hset2 : SettledBy ((t + r) + 2) ((t + 1) + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r))
      (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r)) =
      !(bxor (rhCenter t r) (rhCenter (t + 1) (r + 1))) :=
  winWitt_sector_two_zero_to_black_step_of_zero_diag t k r hk hz hset0 hset2

/-- **Negated Cross-Sector Window Readout at Fixed Bits `(t + 2^k) - r` and `(t + 2^(k+1)) - r` One Step After Zero Diagonal `t + r` (`winWitt_sector_one_xor_sector_two_rhCenter_step_one_of_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, and `settle ((t + r) + 2) ≤ (t + 1) + 2^k`, at time `t + 1` the cross-sector XOR at `(t + 2^k) - r` and `(t + 2^(k+1)) - r` equals `!rhCenter ((t + 1) + 2^k) (r + 1)`! -/
theorem winWitt_sector_one_xor_sector_two_rhCenter_step_one_of_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle ((t + r) + 2) ≤ (t + 1) + twopow k) :
    bxor
      ((winWitt (t + 1) (twopow k)).testBit ((t + twopow k) - r))
      ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r)) =
      !rhCenter ((t + 1) + twopow k) (r + 1) := by
  have hlt : (t + 1) + (r + 1) < twopow k := by
    have := twopow_gt_self k
    omega
  have hw := winWitt_sector_one_xor_sector_two_rhCenter_cone (t + 1) k (r + 1) hlt
  rw [show ((t + 1) + twopow k) - (r + 1) = (t + twopow k) - r by omega,
    show ((t + 1) + twopow (k + 1)) - (r + 1) = (t + twopow (k + 1)) - r by omega,
    lhCenter_late_cross_step_one_of_zero_diag t k r hk hz hset] at hw
  rw [hw]
  cases rhCenter ((t + 1) + twopow k) (r + 1) <;> rfl

theorem winWitt_sector_one_xor_sector_two_rhCenter_step_one_of_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy ((t + r) + 2) ((t + 1) + twopow k)) :
    bxor
      (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow k) - r))
      (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r)) =
      !rhCenter ((t + 1) + twopow k) (r + 1) :=
  winWitt_sector_one_xor_sector_two_rhCenter_step_one_of_zero_diag t k r hk hz hset

/-- **Early-Free Cross-Sector Fixed-Bit 1-Step Zero-to-Black Transition of Late `rhCenter` (`winWitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag (t + r)`, `settle (t + r) ≤ t + 2^k`, and `settle ((t + r) + 2) ≤ (t + 1) + 2^k`, XORing the cross-sector window bits at `(t + 2^k) - r` and `(t + 2^(k+1)) - r` across times `t` and `t + 1` gives `!(rhCenter (t + 2^k) r ⊕ rhCenter ((t + 1) + 2^k) (r + 1))`! -/
theorem winWitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset0 : settle (t + r) ≤ t + twopow k)
    (hset2 : settle ((t + r) + 2) ≤ (t + 1) + twopow k) :
    bxor
      (bxor
        ((winWitt t (twopow k)).testBit ((t + twopow k) - r))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)))
      (bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow k) - r))
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r))) =
      !(bxor
        (rhCenter (t + twopow k) r)
        (rhCenter ((t + 1) + twopow k) (r + 1))) := by
  rw [winWitt_sector_one_xor_sector_two_rhCenter_of_zero_diag t k r (by omega) hz hset0,
    winWitt_sector_one_xor_sector_two_rhCenter_step_one_of_zero_diag t k r hk hz hset2]
  simp only [bxor_eq_xor]
  cases rhCenter (t + twopow k) r <;>
    cases rhCenter ((t + 1) + twopow k) (r + 1) <;> rfl

theorem winWitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset0 : SettledBy (t + r) (t + twopow k))
    (hset2 : SettledBy ((t + r) + 2) ((t + 1) + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - r))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)))
      (bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow k) - r))
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r))) =
      !(bxor
        (rhCenter (t + twopow k) r)
        (rhCenter ((t + 1) + twopow k) (r + 1))) :=
  winWitt_sector_one_xor_sector_two_zero_to_black_step_of_zero_diag t k r hk hz hset0 hset2

/-- **Exact Sector-2 Right-Half Readout of `phiScale k (row t)` (`phiScale_row_testBit_scale_cross_cone`)**:
    for all `t, k, r : Nat` with `t + r < 2^k` (with NO bound `2 * t < 2^k` or `r ≤ t` required!), `(phiScale k (row t)).testBit ((t + 2^(k+1)) - r) = rhCenter t r`! -/
theorem phiScale_row_testBit_scale_cross_cone (t k r : Nat)
    (htr : t + r < twopow k) :
    (phiScale k (row t)).testBit ((t + twopow (k + 1)) - r) =
      rhCenter t r := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hw := winWitt_testBit_scale_cross_cone t k r htr
  have hdef := congrArg (fun n => n.testBit ((t + twopow (k + 1)) - r)) (row_scale t k)
  rw [Nat.testBit_xor] at hdef
  have hrow := lhCenter_eq_row_testBit_uncond (t + twopow k) (twopow k - r)
  rw [show (t + twopow k) + (twopow k - r) = (t + twopow (k + 1)) - r by omega] at hrow
  rw [← hrow, hw] at hdef
  revert hdef
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - r) <;>
    cases rhCenter t r <;>
    cases (phiScale k (row t)).testBit ((t + twopow (k + 1)) - r) <;> decide

theorem phiScale_row_testBit_scale_cross_cone_prop (t k r : Nat)
    (htr : t + r < twopow k) :
    wittBitBool (phiScale k (row t)) ((t + twopow (k + 1)) - r) =
      rhCenter t r :=
  phiScale_row_testBit_scale_cross_cone t k r htr

/-- **Exact Vanishing of `phiScale k (row t)` in the Sector-2 Cross-Center Zero Gap (`phiScale_row_testBit_scale_cross_zero_gap_eq_false`)**:
    for all `t, k, r : Nat` with `t < r` and `t + r < 2^k`, `(phiScale k (row t)).testBit ((t + 2^(k+1)) - r) = false`! -/
theorem phiScale_row_testBit_scale_cross_zero_gap_eq_false (t k r : Nat)
    (ht : t < r) (htr : t + r < twopow k) :
    (phiScale k (row t)).testBit ((t + twopow (k + 1)) - r) = false := by
  rw [phiScale_row_testBit_scale_cross_cone t k r htr,
    rhCenter_gt_eq_false t r ht]

theorem phiScale_row_testBit_scale_cross_zero_gap_eq_false_prop (t k r : Nat)
    (ht : t < r) (htr : t + r < twopow k) :
    wittBitBool (phiScale k (row t)) ((t + twopow (k + 1)) - r) = false :=
  phiScale_row_testBit_scale_cross_zero_gap_eq_false t k r ht htr

/-- **Exact Vanishing of `crossCarry` in the Sector-2 Cross-Center Zero Gap (`crossCarry_row_scale_cross_zero_gap_eq_false`)**:
    for all `t, k, r : Nat` with `t ≤ r` and `t + r + 2 < 2^k`, `(crossCarry (phiScale k (row t)) (winWitt t (2^k))).testBit ((t + 2^(k+1)) - (r + 1)) = false`! -/
theorem crossCarry_row_scale_cross_zero_gap_eq_false (t k r : Nat)
    (ht : t ≤ r) (htr : t + r + 2 < twopow k) :
    (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit
        ((t + twopow (k + 1)) - (r + 1)) = false := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hc := crossCarry_testBit_succ (phiScale k (row t)) (winWitt t (twopow k))
    ((t + twopow (k + 1)) - (r + 2))
  rw [show ((t + twopow (k + 1)) - (r + 2)) + 1 = (t + twopow (k + 1)) - (r + 1) by omega,
    phiScale_row_testBit_scale_cross_zero_gap_eq_false t k (r + 1) (by omega) (by omega),
    phiScale_row_testBit_scale_cross_zero_gap_eq_false t k (r + 2) (by omega) (by omega)] at hc
  rw [hc, Bool.false_and, Bool.and_false]
  rfl

theorem crossCarry_row_scale_cross_zero_gap_eq_false_prop (t k r : Nat)
    (ht : t ≤ r) (htr : t + r + 2 < twopow k) :
    wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k)))
        ((t + twopow (k + 1)) - (r + 1)) = false :=
  crossCarry_row_scale_cross_zero_gap_eq_false t k r ht htr

/-- **Pure-`Φ` Evolution of `winWitt` in the Sector-2 Cross-Center Zero Gap (`winWitt_step_scale_cross_zero_gap_eq_phi`)**:
    for all `t, k, r : Nat` with `t ≤ r` and `t + r + 2 < 2^k`, both `crossCarry` and `frobDefect` vanish at `(t + 2^(k+1)) - (r + 1)`, so `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = (phi (winWitt t (2^k))).testBit ((t + 2^(k+1)) - r)`! -/
theorem winWitt_step_scale_cross_zero_gap_eq_phi (t k r : Nat)
    (ht : t ≤ r) (htr : t + r + 2 < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      (phi (winWitt t (twopow k))).testBit ((t + twopow (k + 1)) - r) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hs := winWitt_step_frobDefect_testBit_succ t k ((t + twopow (k + 1)) - (r + 1))
  rw [show ((t + twopow (k + 1)) - (r + 1)) + 1 = (t + twopow (k + 1)) - r by omega,
    crossCarry_row_scale_cross_zero_gap_eq_false t k r ht htr,
    frobDefect_row_testBit_gt_two_mul_eq_false t k ((t + twopow (k + 1)) - (r + 1))
      (by omega) (by omega)] at hs
  rw [hs]
  cases (phi (winWitt t (twopow k))).testBit ((t + twopow (k + 1)) - r) <;> rfl

theorem winWitt_step_scale_cross_zero_gap_eq_phi_prop (t k r : Nat)
    (ht : t ≤ r) (htr : t + r + 2 < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) =
      wittBitBool (phi (winWitt t (twopow k))) ((t + twopow (k + 1)) - r) :=
  winWitt_step_scale_cross_zero_gap_eq_phi t k r ht htr

/-- **Sideways Pure-`Φ` Inversion of `winWitt` in the Sector-2 Cross-Center Zero Gap (`winWitt_inward_step_scale_cross_zero_gap`)**:
    for all `t, k, r : Nat` with `t ≤ r` and `t + r + 2 < 2^k`, `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) ⊕ ((winWitt t (twopow k)).testBit ((t + 2^(k+1)) - (r + 1)) || (winWitt t (twopow k)).testBit ((t + 2^(k+1)) - (r + 2)))`! -/
theorem winWitt_inward_step_scale_cross_zero_gap (t k r : Nat)
    (ht : t ≤ r) (htr : t + r + 2 < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) ||
          (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2))) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hs := winWitt_step_scale_cross_zero_gap_eq_phi t k r ht htr
  have hp := phi_testBit_add_two (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2))
  rw [show ((t + twopow (k + 1)) - (r + 2)) + 2 = (t + twopow (k + 1)) - r by omega,
    show ((t + twopow (k + 1)) - (r + 2)) + 1 = (t + twopow (k + 1)) - (r + 1) by omega] at hp
  rw [hp] at hs
  rw [hs]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;>
    cases ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) ||
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2))) <;> rfl

theorem winWitt_inward_step_scale_cross_zero_gap_prop (t k r : Nat)
    (ht : t ≤ r) (htr : t + r + 2 < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) ||
          wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2))) :=
  winWitt_inward_step_scale_cross_zero_gap t k r ht htr

/-- **Linearized Real-Orbit Step One Diagonal Before a Zero Diagonal (`lhCenter_late_cross_linear_step_one_before_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag ((t + r) + 1)`, and `settle ((t + r) + 1) ≤ t + 2^k`, because `lhCenter (t + 2^k) (2^k - (r + 1)) = false` (`lhCenter_late_cross_of_zero_diag` at `r + 1`), the OR gate in `lhCenter_step_succ` collapses to its second input: `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - r) ⊕ lhCenter (t + 2^k) (2^k - (r + 2))`! -/
theorem lhCenter_late_cross_linear_step_one_before_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 1))
    (hset : settle ((t + r) + 1) ≤ t + twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) =
      bxor
        (lhCenter (t + twopow k) (twopow k - r))
        (lhCenter (t + twopow k) (twopow k - (r + 2))) := by
  have hr2 : r + 2 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  have hs := lhCenter_step_succ (t + twopow k) (twopow k - (r + 2))
  have hz' : IsZeroDiag (t + (r + 1)) := by
    rwa [show t + (r + 1) = (t + r) + 1 by omega]
  have hset' : settle (t + (r + 1)) ≤ t + twopow k := by
    rwa [show t + (r + 1) = (t + r) + 1 by omega]
  rw [show (t + twopow k) + 1 = (t + 1) + twopow k by omega,
    show (twopow k - (r + 2)) + 1 = twopow k - (r + 1) by omega,
    show (twopow k - (r + 2)) + 2 = twopow k - r by omega,
    lhCenter_late_cross_of_zero_diag t k (r + 1) (by omega) hz' hset',
    Bool.false_or] at hs
  exact hs

theorem lhCenter_late_cross_linear_step_one_before_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 1))
    (hset : SettledBy ((t + r) + 1) (t + twopow k)) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) =
      bxor
        (lhCenter (t + twopow k) (twopow k - r))
        (lhCenter (t + twopow k) (twopow k - (r + 2))) :=
  lhCenter_late_cross_linear_step_one_before_zero_diag t k r hk hz hset

/-- **Linearized Real-Orbit Step Two Diagonals Before a Zero Diagonal (`lhCenter_late_cross_linear_step_two_before_zero_diag`)**:
    for all `t, k, r : Nat` with `(t + r) + 2 ≤ k`, `IsZeroDiag ((t + r) + 2)`, and `settle ((t + r) + 2) ≤ t + 2^k`, because `lhCenter (t + 2^k) (2^k - (r + 2)) = false` (`lhCenter_late_cross_of_zero_diag` at `r + 2`), the OR gate in `lhCenter_step_succ` collapses to its first input: `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - r) ⊕ lhCenter (t + 2^k) (2^k - (r + 1))`! -/
theorem lhCenter_late_cross_linear_step_two_before_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) =
      bxor
        (lhCenter (t + twopow k) (twopow k - r))
        (lhCenter (t + twopow k) (twopow k - (r + 1))) := by
  have hr2 : r + 2 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  have hs := lhCenter_step_succ (t + twopow k) (twopow k - (r + 2))
  have hz' : IsZeroDiag (t + (r + 2)) := by
    rwa [show t + (r + 2) = (t + r) + 2 by omega]
  have hset' : settle (t + (r + 2)) ≤ t + twopow k := by
    rwa [show t + (r + 2) = (t + r) + 2 by omega]
  rw [show (t + twopow k) + 1 = (t + 1) + twopow k by omega,
    show (twopow k - (r + 2)) + 1 = twopow k - (r + 1) by omega,
    show (twopow k - (r + 2)) + 2 = twopow k - r by omega,
    lhCenter_late_cross_of_zero_diag t k (r + 2) (by omega) hz' hset',
    Bool.or_false] at hs
  exact hs

theorem lhCenter_late_cross_linear_step_two_before_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) =
      bxor
        (lhCenter (t + twopow k) (twopow k - r))
        (lhCenter (t + twopow k) (twopow k - (r + 1))) :=
  lhCenter_late_cross_linear_step_two_before_zero_diag t k r hk hz hset

/-- **Linearized `Φ` Window Step in Sector 2 One Diagonal Before a Zero Diagonal (`winWitt_sector_two_linear_step_one_before_zero_diag`)**:
    for all `t, k, r : Nat` with `t ≤ r`, `(t + r) + 2 ≤ k`, `IsZeroDiag ((t + r) + 1)`, and `settle ((t + r) + 1) ≤ t + 2^k`, because `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false`, the OR gate in `Φ` linearizes to `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2))`! -/
theorem winWitt_sector_two_linear_step_one_before_zero_diag (t k r : Nat)
    (ht : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 1))
    (hset : settle ((t + r) + 1) ≤ t + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      bxor
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2))) := by
  have htr : t + r + 2 < twopow k := by
    have := twopow_gt_self k
    omega
  have hi := winWitt_inward_step_scale_cross_zero_gap t k r ht htr
  have hz' : IsZeroDiag (t + (r + 1)) := by
    rwa [show t + (r + 1) = (t + r) + 1 by omega]
  have hset' : settle (t + (r + 1)) ≤ t + twopow k := by
    rwa [show t + (r + 1) = (t + r) + 1 by omega]
  rw [winWitt_testBit_scale_cross_zero_gap_of_zero_diag t k (r + 1) (by omega) (by omega) hz' hset',
    Bool.false_or] at hi
  revert hi
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;>
    cases (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) <;> decide

theorem winWitt_sector_two_linear_step_one_before_zero_diag_prop (t k r : Nat)
    (ht : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 1))
    (hset : SettledBy ((t + r) + 1) (t + twopow k)) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) =
      bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2))) :=
  winWitt_sector_two_linear_step_one_before_zero_diag t k r ht hk hz hset

/-- **Linearized `Φ` Window Step in Sector 2 Two Diagonals Before a Zero Diagonal (`winWitt_sector_two_linear_step_two_before_zero_diag`)**:
    for all `t, k, r : Nat` with `t ≤ r`, `(t + r) + 2 ≤ k`, `IsZeroDiag ((t + r) + 2)`, and `settle ((t + r) + 2) ≤ t + 2^k`, because `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false`, the OR gate in `Φ` linearizes to `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`! -/
theorem winWitt_sector_two_linear_step_two_before_zero_diag (t k r : Nat)
    (ht : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      bxor
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1))) := by
  have htr : t + r + 2 < twopow k := by
    have := twopow_gt_self k
    omega
  have hi := winWitt_inward_step_scale_cross_zero_gap t k r ht htr
  have hz' : IsZeroDiag (t + (r + 2)) := by
    rwa [show t + (r + 2) = (t + r) + 2 by omega]
  have hset' : settle (t + (r + 2)) ≤ t + twopow k := by
    rwa [show t + (r + 2) = (t + r) + 2 by omega]
  rw [winWitt_testBit_scale_cross_zero_gap_of_zero_diag t k (r + 2) (by omega) (by omega) hz' hset',
    Bool.or_false] at hi
  revert hi
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;>
    cases (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_sector_two_linear_step_two_before_zero_diag_prop (t k r : Nat)
    (ht : t ≤ r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) =
      bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_sector_two_linear_step_two_before_zero_diag t k r ht hk hz hset

/-! ### Batch 20: Real-Orbit Twin Identity Before a Zero Diagonal and Antiperiodic Sector-2 Window Flips at Doubling Zero Diagonals (9.592–9.606) -/

/-- **Real-orbit cross-center twin identity before a zero diagonal (9.592)**:
for all `t, k, r ∈ ℕ` with `(t + r) + 2 ≤ k`, if `(t + r) + 2` is a zero diagonal that has settled by `t + 2^k`, then the two adjacent late cells on diagonals `t + r` and `(t + r) + 1` at time `t + 2^k` are identically equal (`lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))`), without requiring settlement of diagonals `t + r` or `(t + r) + 1`. -/
theorem lhCenter_late_cross_twin_before_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have hlin := lhCenter_late_cross_linear_step_two_before_zero_diag t k r hk hz hset
  have hz1 : IsZeroDiag ((t + 1) + (r + 1)) := by
    rwa [show (t + 1) + (r + 1) = (t + r) + 2 by omega]
  have hk1 : (t + 1) + (r + 1) ≤ k := by omega
  have hset1 : settle ((t + 1) + (r + 1)) ≤ (t + 1) + twopow k := by
    rw [show (t + 1) + (r + 1) = (t + r) + 2 by omega]
    omega
  rw [lhCenter_late_cross_of_zero_diag (t + 1) k (r + 1) hk1 hz1 hset1] at hlin
  revert hlin
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - r) <;>
    cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> decide

theorem lhCenter_late_cross_twin_before_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_twin_before_zero_diag t k r hk hz hset

/-- **Real-orbit shifted left-half twin identity before a zero diagonal (9.593)**:
for all `t, k, p ∈ ℕ` with `p ≤ t` and `(t - p) + 2 ≤ k`, if `(t - p) + 2` is a zero diagonal that has settled by `(t + 2) + 2^k`, then `lhCenter ((t + 2) + 2^k) ((p + 2) + 2^k) = lhCenter ((t + 2) + 2^k) ((p + 1) + 2^k)` without requiring settlement of `t - p` or `(t - p) + 1`. -/
theorem lhCenter_late_shift_twin_before_zero_diag (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag ((t - p) + 2))
    (hset : settle ((t - p) + 2) ≤ (t + 2) + twopow k) :
    lhCenter ((t + 2) + twopow k) ((p + 2) + twopow k) =
      lhCenter ((t + 2) + twopow k) ((p + 1) + twopow k) := by
  have hstep := lhCenter_step_succ ((t + 2) + twopow k) (p + twopow k)
  rw [show ((t + 2) + twopow k) + 1 = (t + 3) + twopow k by omega,
    show (p + twopow k) + 1 = (p + 1) + twopow k by omega,
    show (p + twopow k) + 2 = (p + 2) + twopow k by omega] at hstep
  have hz2 : IsZeroDiag ((t + 2) - p) := by
    rwa [show (t + 2) - p = (t - p) + 2 by omega]
  have hk2 : (t + 2) - p ≤ k := by omega
  have hset2 : settle ((t + 2) - p) ≤ (t + 2) + twopow k := by
    rwa [show (t + 2) - p = (t - p) + 2 by omega]
  have hz3 : IsZeroDiag ((t + 3) - (p + 1)) := by
    rwa [show (t + 3) - (p + 1) = (t - p) + 2 by omega]
  have hk3 : (t + 3) - (p + 1) ≤ k := by omega
  have hset3 : settle ((t + 3) - (p + 1)) ≤ (t + 3) + twopow k := by
    rw [show (t + 3) - (p + 1) = (t - p) + 2 by omega]
    omega
  rw [lhCenter_late_shift_of_zero_diag (t + 2) k p (by omega) hk2 hz2 hset2,
    lhCenter_late_shift_of_zero_diag (t + 3) k (p + 1) (by omega) hk3 hz3 hset3,
    Bool.or_false] at hstep
  revert hstep
  simp only [bxor_eq_xor]
  cases lhCenter ((t + 2) + twopow k) ((p + 2) + twopow k) <;>
    cases lhCenter ((t + 2) + twopow k) ((p + 1) + twopow k) <;> decide

theorem lhCenter_late_shift_twin_before_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag ((t - p) + 2))
    (hset : SettledBy ((t - p) + 2) ((t + 2) + twopow k)) :
    lhCenter ((t + 2) + twopow k) ((p + 2) + twopow k) =
      lhCenter ((t + 2) + twopow k) ((p + 1) + twopow k) :=
  lhCenter_late_shift_twin_before_zero_diag t k p hp hk hz hset

/-- **Sector-2 adjacent-bit twin identity before a zero diagonal (9.594)**:
for all `t, k, r ∈ ℕ` with `(t + r) + 2 ≤ k`, if `(t + r) + 2` is a zero diagonal that has settled by `t + 2^k`, then the XOR of the two adjacent Sector-2 window bits `(t + 2^(k+1)) - r` and `(t + 2^(k+1)) - (r + 1)` at time `t` equals `rhCenter t r ⊕ rhCenter t (r + 1)`. -/
theorem winWitt_sector_two_twin_before_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r))
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1))) =
      bxor (rhCenter t r) (rhCenter t (r + 1)) := by
  have htr : t + r + 2 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_cone t k r (by omega),
    winWitt_testBit_scale_cross_cone t k (r + 1) (by omega),
    lhCenter_late_cross_twin_before_zero_diag t k r hk hz hset]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases rhCenter t r <;>
    cases rhCenter t (r + 1) <;> decide

theorem winWitt_sector_two_twin_before_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r))
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))) =
      bxor (rhCenter t r) (rhCenter t (r + 1)) :=
  winWitt_sector_two_twin_before_zero_diag t k r hk hz hset

/-- **Inter-cone zero-gap adjacent-bit equality in Sector 2 before a zero diagonal (9.595)**:
for all `t, k, r ∈ ℕ` with `t < r` and `(t + r) + 2 ≤ k`, if `(t + r) + 2` is a zero diagonal that has settled by `t + 2^k`, then the two adjacent Sector-2 window bits `(t + 2^(k+1)) - r` and `(t + 2^(k+1)) - (r + 1)` at time `t` are identically equal. -/
theorem winWitt_sector_two_twin_zero_gap_before_zero_diag (t k r : Nat)
    (ht : t < r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h := winWitt_sector_two_twin_before_zero_diag t k r hk hz hset
  rw [rhCenter_gt_eq_false t r ht, rhCenter_gt_eq_false t (r + 1) (by omega)] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_sector_two_twin_zero_gap_before_zero_diag_prop (t k r : Nat)
    (ht : t < r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) :=
  winWitt_sector_two_twin_zero_gap_before_zero_diag t k r ht hk hz hset

/-- **Early-free cross-sector adjacent-bit twin readout before a zero diagonal (9.596)**:
for all `t, k, r ∈ ℕ` with `(t + r) + 2 ≤ k`, if `(t + r) + 2` is a zero diagonal that has settled by `t + 2^k`, then the XOR of the Sector-1 `⊕` Sector-2 window pairs at `r` and `r + 1` equals the late right-half adjacent difference `rhCenter (t + 2^k) r ⊕ rhCenter (t + 2^k) (r + 1)`. -/
theorem winWitt_sector_one_xor_sector_two_twin_before_zero_diag (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : settle ((t + r) + 2) ≤ t + twopow k) :
    bxor
      (bxor
        ((winWitt t (twopow k)).testBit ((t + twopow k) - r))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)))
      (bxor
        ((winWitt t (twopow k)).testBit ((t + twopow k) - (r + 1)))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)))) =
      bxor (rhCenter (t + twopow k) r) (rhCenter (t + twopow k) (r + 1)) := by
  have htr : t + r + 2 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_sector_one_xor_sector_two_rhCenter_cone t k r (by omega),
    winWitt_sector_one_xor_sector_two_rhCenter_cone t k (r + 1) (by omega),
    lhCenter_late_cross_twin_before_zero_diag t k r hk hz hset]
  simp only [bxor_eq_xor]
  cases rhCenter (t + twopow k) r <;>
    cases rhCenter (t + twopow k) (r + 1) <;>
    cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> decide

theorem winWitt_sector_one_xor_sector_two_twin_before_zero_diag_prop (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + r) + 2))
    (hset : SettledBy ((t + r) + 2) (t + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - r))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)))
      (bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (r + 1)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)))) =
      bxor (rhCenter (t + twopow k) r) (rhCenter (t + twopow k) (r + 1)) :=
  winWitt_sector_one_xor_sector_two_twin_before_zero_diag t k r hk hz hset

/-- **Antiperiodicity of shifted late `lhCenter` at a doubling zero diagonal (9.597)**:
for all `P, t, k, p ∈ ℕ` with `p ≤ t` and `(t - p) + 1 ≤ k`, if `t - p` is a zero diagonal where period `P` doubles (`DoublesAt P (t - p)`) and `(t - p) + 1` has settled by `(t + 1) + 2^k`, then shifting both time and column by `P` flips `lhCenter ((t + 1) + 2^k) (p + 2^k)`. -/
theorem lhCenter_late_shift_antiperiodic_of_doubles (P t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 1 ≤ k)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt P (t - p))
    (hset : settle ((t - p) + 1) ≤ (t + 1) + twopow k) :
    lhCenter (((t + 1) + P) + twopow k) ((p + P) + twopow k) =
      !lhCenter ((t + 1) + twopow k) (p + twopow k) := by
  rw [lhCenter_late_shift_eq_ldiag ((t + 1) + P) k (p + P) (by omega),
    lhCenter_late_shift_eq_ldiag (t + 1) k p (by omega),
    show ((t + 1) + P) - (p + P) = (t - p) + 1 by omega,
    show (t + 1) - p = (t - p) + 1 by omega]
  exact ldiag_antiperiodic_of_doubles P (t - p) (t + 1) k hz hd hk hset

theorem lhCenter_late_shift_antiperiodic_of_doubles_prop (P t k p : Nat)
    (hp : p ≤ t) (hk : (t - p) + 1 ≤ k)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt P (t - p))
    (hset : SettledBy ((t - p) + 1) ((t + 1) + twopow k)) :
    lhCenter (((t + 1) + P) + twopow k) ((p + P) + twopow k) =
      !lhCenter ((t + 1) + twopow k) (p + twopow k) :=
  lhCenter_late_shift_antiperiodic_of_doubles P t k p hp hk hz hd hset

/-- **Antiperiodicity of cross-center late `lhCenter` at a doubling zero diagonal (9.598)**:
for all `P, t, k, r ∈ ℕ` with `(t + P + r) + 1 ≤ k`, if `t + P + r` is a zero diagonal where period `P` doubles (`DoublesAt P (t + P + r)`) and `(t + P + r) + 1` has settled by `t + 2^k`, then `lhCenter ((t + P) + 2^k) (2^k - (r + 1)) = !lhCenter (t + 2^k) (2^k - (r + P + 1))`. -/
theorem lhCenter_late_cross_antiperiodic_of_doubles (P t k r : Nat)
    (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : settle ((t + P + r) + 1) ≤ t + twopow k) :
    lhCenter ((t + P) + twopow k) (twopow k - (r + 1)) =
      !lhCenter (t + twopow k) (twopow k - (r + P + 1)) := by
  have hr : r + P + 1 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  rw [lhCenter_late_cross_eq_ldiag (t + P) k (r + 1) (by omega),
    lhCenter_late_cross_eq_ldiag t k (r + P + 1) hr,
    show (t + P) + (r + 1) = (t + P + r) + 1 by omega,
    show t + (r + P + 1) = (t + P + r) + 1 by omega]
  exact ldiag_antiperiodic_of_doubles P (t + P + r) t k hz hd hk hset

theorem lhCenter_late_cross_antiperiodic_of_doubles_prop (P t k r : Nat)
    (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : SettledBy ((t + P + r) + 1) (t + twopow k)) :
    lhCenter ((t + P) + twopow k) (twopow k - (r + 1)) =
      !lhCenter (t + twopow k) (twopow k - (r + P + 1)) :=
  lhCenter_late_cross_antiperiodic_of_doubles P t k r hk hz hd hset

/-- **Outer left-strip `winWitt` antiperiodicity at a doubling zero diagonal (9.599)**:
for all `P, t, k, p ∈ ℕ` with `p ≤ t`, `t + 1 < p + 2^k`, and `(t - p) + 1 ≤ k`, if `t - p` is a zero diagonal where period `P` doubles and `(t - p) + 1` has settled by `(t + 1) + 2^k`, then the XOR of the outer left-strip Sector-2 window bits at `(t + 1, p)` and `((t + 1) + P, p + P)` equals `!(lhCenter (t + 1) p ⊕ lhCenter ((t + 1) + P) (p + P))`. -/
theorem winWitt_outer_left_strip_antiperiodic_of_doubles (P t k p : Nat)
    (hp : p ≤ t) (htp : t + 1 < p + twopow k) (hk : (t - p) + 1 ≤ k)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt P (t - p))
    (hset : settle ((t - p) + 1) ≤ (t + 1) + twopow k) :
    bxor
      ((winWitt (t + 1) (twopow k)).testBit (((t + 1) + p) + twopow (k + 1)))
      ((winWitt ((t + 1) + P) (twopow k)).testBit ((((t + 1) + P) + (p + P)) + twopow (k + 1))) =
      !(bxor (lhCenter (t + 1) p) (lhCenter ((t + 1) + P) (p + P))) := by
  rw [winWitt_testBit_outer_left_strip (t + 1) k p htp,
    winWitt_testBit_outer_left_strip ((t + 1) + P) k (p + P) (by omega),
    lhCenter_late_shift_antiperiodic_of_doubles P t k p hp hk hz hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (t + 1) p <;>
    cases lhCenter ((t + 1) + P) (p + P) <;>
    cases lhCenter ((t + 1) + twopow k) (p + twopow k) <;> decide

theorem winWitt_outer_left_strip_antiperiodic_of_doubles_prop (P t k p : Nat)
    (hp : p ≤ t) (htp : t + 1 < p + twopow k) (hk : (t - p) + 1 ≤ k)
    (hz : IsZeroDiag (t - p)) (hd : DoublesAt P (t - p))
    (hset : SettledBy ((t - p) + 1) ((t + 1) + twopow k)) :
    bxor
      (wittBitBool (winWitt (t + 1) (twopow k)) (((t + 1) + p) + twopow (k + 1)))
      (wittBitBool (winWitt ((t + 1) + P) (twopow k)) ((((t + 1) + P) + (p + P)) + twopow (k + 1))) =
      !(bxor (lhCenter (t + 1) p) (lhCenter ((t + 1) + P) (p + P))) :=
  winWitt_outer_left_strip_antiperiodic_of_doubles P t k p hp htp hk hz hd hset

/-- **Sector-2 cross-center `winWitt` antiperiodicity at a doubling zero diagonal (9.600)**:
for all `P, t, k, r ∈ ℕ` with `(t + P + r) + 1 ≤ k`, if `t + P + r` is a zero diagonal where period `P` doubles and `(t + P + r) + 1` has settled by `t + 2^k`, then the XOR of the Sector-2 cross-center window bits at `(t, r + P + 1)` and `(t + P, r + 1)` equals `!(rhCenter t (r + P + 1) ⊕ rhCenter (t + P) (r + 1))`. -/
theorem winWitt_scale_cross_antiperiodic_of_doubles (P t k r : Nat)
    (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : settle ((t + P + r) + 1) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P + 1)))
      ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter t (r + P + 1)) (rhCenter (t + P) (r + 1))) := by
  have htr : t + P + r + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_cone t k (r + P + 1) (by omega),
    winWitt_testBit_scale_cross_cone (t + P) k (r + 1) (by omega),
    lhCenter_late_cross_antiperiodic_of_doubles P t k r hk hz hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + P + 1)) <;>
    cases rhCenter t (r + P + 1) <;>
    cases rhCenter (t + P) (r + 1) <;> decide

theorem winWitt_scale_cross_antiperiodic_of_doubles_prop (P t k r : Nat)
    (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : SettledBy ((t + P + r) + 1) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + P + 1)))
      (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter t (r + P + 1)) (rhCenter (t + P) (r + 1))) :=
  winWitt_scale_cross_antiperiodic_of_doubles P t k r hk hz hd hset

/-- **Inter-cone zero-gap Sector-2 bit flip under period shift `P` at a doubling zero diagonal (9.601)**:
for all `P, t, k, r ∈ ℕ` with `t + P ≤ r` and `(t + P + r) + 1 ≤ k`, if `t + P + r` is a zero diagonal where period `P` doubles and `(t + P + r) + 1` has settled by `t + 2^k`, then `(winWitt (t + P) (2^k)).testBit (((t + P) + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + P + 1))`. -/
theorem winWitt_scale_cross_zero_gap_antiperiodic_of_doubles (P t k r : Nat)
    (ht : t + P ≤ r) (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : settle ((t + P + r) + 1) ≤ t + twopow k) :
    (winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P + 1)) := by
  have h := winWitt_scale_cross_antiperiodic_of_doubles P t k r hk hz hd hset
  rw [rhCenter_gt_eq_false t (r + P + 1) (by omega),
    rhCenter_gt_eq_false (t + P) (r + 1) (by omega)] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P + 1)) <;>
    cases (winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_scale_cross_zero_gap_antiperiodic_of_doubles_prop (P t k r : Nat)
    (ht : t + P ≤ r) (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : SettledBy ((t + P + r) + 1) (t + twopow k)) :
    wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1)) =
      !wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + P + 1)) :=
  winWitt_scale_cross_zero_gap_antiperiodic_of_doubles P t k r ht hk hz hd hset

/-- **Early-free cross-sector antiperiodicity at a doubling zero diagonal (9.602)**:
for all `P, t, k, r ∈ ℕ` with `(t + P + r) + 1 ≤ k`, if `t + P + r` is a zero diagonal where period `P` doubles and `(t + P + r) + 1` has settled by `t + 2^k`, then the XOR of the Sector-1 `⊕` Sector-2 window pairs at `(t, r + P + 1)` and `(t + P, r + 1)` equals `!(rhCenter (t + 2^k) (r + P + 1) ⊕ rhCenter ((t + P) + 2^k) (r + 1))`. -/
theorem winWitt_sector_one_xor_sector_two_antiperiodic_of_doubles (P t k r : Nat)
    (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : settle ((t + P + r) + 1) ≤ t + twopow k) :
    bxor
      (bxor
        ((winWitt t (twopow k)).testBit ((t + twopow k) - (r + P + 1)))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P + 1))))
      (bxor
        ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow k) - (r + 1)))
        ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)))) =
      !(bxor (rhCenter (t + twopow k) (r + P + 1)) (rhCenter ((t + P) + twopow k) (r + 1))) := by
  have htr : t + P + r + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_sector_one_xor_sector_two_rhCenter_cone t k (r + P + 1) (by omega),
    winWitt_sector_one_xor_sector_two_rhCenter_cone (t + P) k (r + 1) (by omega),
    lhCenter_late_cross_antiperiodic_of_doubles P t k r hk hz hd hset]
  simp only [bxor_eq_xor]
  cases rhCenter (t + twopow k) (r + P + 1) <;>
    cases rhCenter ((t + P) + twopow k) (r + 1) <;>
    cases lhCenter (t + twopow k) (twopow k - (r + P + 1)) <;> decide

theorem winWitt_sector_one_xor_sector_two_antiperiodic_of_doubles_prop (P t k r : Nat)
    (hk : (t + P + r) + 1 ≤ k)
    (hz : IsZeroDiag (t + P + r)) (hd : DoublesAt P (t + P + r))
    (hset : SettledBy ((t + P + r) + 1) (t + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (r + P + 1)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + P + 1))))
      (bxor
        (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow k) - (r + 1)))
        (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1)))) =
      !(bxor (rhCenter (t + twopow k) (r + P + 1)) (rhCenter ((t + P) + twopow k) (r + 1))) :=
  winWitt_sector_one_xor_sector_two_antiperiodic_of_doubles P t k r hk hz hd hset

/-- **Real-orbit `P`-periodicity on all diagonals `d ≤ z` below a doubling point (9.603)**:
if `DoublesAt P z`, then for every depth `d ≤ z`, scale `k ≥ d`, and time `s` with `settle d ≤ s + 2^k`, `ldiag d ((s + P) + 2^k) = ldiag d (s + 2^k)`. -/
theorem ldiag_periodic_of_doubles_le (P z d s k : Nat)
    (hd : DoublesAt P z) (hdz : d ≤ z) (hk : d ≤ k)
    (hset : settle d ≤ s + twopow k) :
    ldiag d ((s + P) + twopow k) = ldiag d (s + twopow k) := by
  have hsetP : settle d ≤ (s + P) + twopow k := by omega
  rw [ldiag_settled_eq_E d (s + P) k hk hsetP,
    ldiag_settled_eq_E d s k hk hset]
  exact hd.1 d hdz s

theorem ldiag_periodic_of_doubles_le_prop (P z d s k : Nat)
    (hd : DoublesAt P z) (hdz : d ≤ z) (hk : d ≤ k)
    (hset : SettledBy d (s + twopow k)) :
    ldiag d ((s + P) + twopow k) = ldiag d (s + twopow k) :=
  ldiag_periodic_of_doubles_le P z d s k hd hdz hk hset

/-- **Cross-center late `lhCenter` `P`-periodicity on all diagonals `t + P + r ≤ z` below a doubling point (9.604)**:
for all `P, z, t, k, r ∈ ℕ` with `t + P + r ≤ z` and `z ≤ k`, if `DoublesAt P z` and `settle (t + P + r) ≤ t + 2^k`, then `lhCenter ((t + P) + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + P))`. -/
theorem lhCenter_late_cross_periodic_of_doubles_le (P z t k r : Nat)
    (hdz : t + P + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt P z)
    (hset : settle (t + P + r) ≤ t + twopow k) :
    lhCenter ((t + P) + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + P)) := by
  have hr : r + P ≤ twopow k := by
    have := twopow_gt_self k
    omega
  rw [lhCenter_late_cross_eq_ldiag (t + P) k r (by omega),
    lhCenter_late_cross_eq_ldiag t k (r + P) hr,
    show t + (r + P) = t + P + r by omega]
  exact ldiag_periodic_of_doubles_le P z (t + P + r) t k hd hdz (by omega) hset

theorem lhCenter_late_cross_periodic_of_doubles_le_prop (P z t k r : Nat)
    (hdz : t + P + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt P z)
    (hset : SettledBy (t + P + r) (t + twopow k)) :
    lhCenter ((t + P) + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + P)) :=
  lhCenter_late_cross_periodic_of_doubles_le P z t k r hdz hk hd hset

/-- **Sector-2 cross-center `winWitt` `P`-periodicity on all diagonals `t + P + r ≤ z` below a doubling point (9.605)**:
for all `P, z, t, k, r ∈ ℕ` with `t + P + r ≤ z` and `z ≤ k`, if `DoublesAt P z` and `settle (t + P + r) ≤ t + 2^k`, then the XOR of the Sector-2 cross-center window bits at `(t, r + P)` and `(t + P, r)` equals `rhCenter t (r + P) ⊕ rhCenter (t + P) r`. -/
theorem winWitt_scale_cross_periodic_of_doubles_le (P z t k r : Nat)
    (hdz : t + P + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt P z)
    (hset : settle (t + P + r) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P)))
      ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - r)) =
      bxor (rhCenter t (r + P)) (rhCenter (t + P) r) := by
  have htr : t + P + r < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_cone t k (r + P) (by omega),
    winWitt_testBit_scale_cross_cone (t + P) k r (by omega),
    lhCenter_late_cross_periodic_of_doubles_le P z t k r hdz hk hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + P)) <;>
    cases rhCenter t (r + P) <;>
    cases rhCenter (t + P) r <;> decide

theorem winWitt_scale_cross_periodic_of_doubles_le_prop (P z t k r : Nat)
    (hdz : t + P + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt P z)
    (hset : SettledBy (t + P + r) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + P)))
      (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - r)) =
      bxor (rhCenter t (r + P)) (rhCenter (t + P) r) :=
  winWitt_scale_cross_periodic_of_doubles_le P z t k r hdz hk hd hset

/-- **Inter-cone zero-gap Sector-2 bit invariance under period shift `P` below a doubling point (9.606)**:
for all `P, z, t, k, r ∈ ℕ` with `t + P < r`, `t + P + r ≤ z`, and `z ≤ k`, if `DoublesAt P z` and `settle (t + P + r) ≤ t + 2^k`, then `(winWitt (t + P) (2^k)).testBit (((t + P) + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + P))` (contrasting with the exact negation at diagonal `z + 1` in `9.601`). -/
theorem winWitt_scale_cross_zero_gap_periodic_of_doubles_le (P z t k r : Nat)
    (ht : t + P < r) (hdz : t + P + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt P z)
    (hset : SettledBy (t + P + r) (t + twopow k)) :
    (winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P)) := by
  have h := winWitt_scale_cross_periodic_of_doubles_le P z t k r hdz hk hd hset
  rw [rhCenter_gt_eq_false t (r + P) (by omega),
    rhCenter_gt_eq_false (t + P) r ht] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + P)) <;>
    cases (winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - r) <;> decide

theorem winWitt_scale_cross_zero_gap_periodic_of_doubles_le_prop (P z t k r : Nat)
    (ht : t + P < r) (hdz : t + P + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt P z)
    (hset : SettledBy (t + P + r) (t + twopow k)) :
    wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + P)) :=
  winWitt_scale_cross_zero_gap_periodic_of_doubles_le P z t k r ht hdz hk hd hset

/-! ### Batch 21: Post-Black Reset Antiperiodicity on Diagonal `z + 3`, Space-Time Equivalence of `(t + P, z + 1)` and `(t + 1, z + 3)`, and `zcenter` Twin/Doubling Readouts (9.607–9.621) -/

/-- **Real-orbit space-time equivalence of `(t + P, z + 1)` and `(t + 1, z + 3)` at a doubling zero diagonal (9.607)**:
for all `P, t, k, r ∈ ℕ` with `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles (`DoublesAt P ((t + P) + r)`) and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k` (with NO settlement hypothesis on `((t + P) + r) + 3`!), then `lhCenter ((t + P) + 2^k) (2^k - (r + 1)) = lhCenter ((t + 1) + 2^k) (2^k - ((r + P) + 2))`. -/
theorem lhCenter_late_cross_doubles_eq_reset_step (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    lhCenter ((t + P) + twopow k) (twopow k - (r + 1)) =
      lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) := by
  have ha := lhCenter_late_cross_antiperiodic_of_doubles P t k r (by omega) hz hd hset1
  have hz' : IsZeroDiag (t + (r + P)) := by
    rwa [show t + (r + P) = (t + P) + r by omega]
  have hset2' : settle ((t + (r + P)) + 2) ≤ t + twopow k := by
    rwa [show (t + (r + P)) + 2 = ((t + P) + r) + 2 by omega]
  have hrst := lhCenter_late_cross_reset_after_zero_diag t k (r + P) (by omega) hz' hset2'
  rw [ha, hrst]

theorem lhCenter_late_cross_doubles_eq_reset_step_prop (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    lhCenter ((t + P) + twopow k) (twopow k - (r + 1)) =
      lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) :=
  lhCenter_late_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2

/-- **Real-orbit `P`-antiperiodicity on the post-black reset diagonal `z + 3` at a doubling zero diagonal (9.608)**:
for all `P, t, k, r ∈ ℕ` with `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k` (with NO settlement hypothesis on `((t + P) + r) + 3`!), then `lhCenter (((t + 1) + P) + 2^k) (2^k - (r + 2)) = !lhCenter ((t + 1) + 2^k) (2^k - ((r + P) + 2))`. -/
theorem lhCenter_late_cross_reset_antiperiodic_of_doubles (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    lhCenter (((t + 1) + P) + twopow k) (twopow k - (r + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) := by
  have hsetP : settle (((t + P) + r) + 2) ≤ (t + P) + twopow k := by omega
  have hrstP := lhCenter_late_cross_reset_after_zero_diag (t + P) k r hk hz hsetP
  rw [show (t + P) + 1 = (t + 1) + P by omega] at hrstP
  rw [hrstP, lhCenter_late_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2]

theorem lhCenter_late_cross_reset_antiperiodic_of_doubles_prop (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    lhCenter (((t + 1) + P) + twopow k) (twopow k - (r + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) :=
  lhCenter_late_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2

/-- **Sector-2 window space-time equivalence of `(t + P, r + 1)` and `(t + 1, (r + P) + 2)` at a doubling zero diagonal (9.609)**:
for all `P, t, k, r ∈ ℕ` with `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k`, then `(winWitt (t + P) (2^k)).testBit (((t + P) + 2^(k+1)) - (r + 1)) ⊕ (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + P) + 1)) = rhCenter (t + P) (r + 1) ⊕ rhCenter (t + 1) ((r + P) + 2)`. -/
theorem winWitt_scale_cross_doubles_eq_reset_step (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    bxor
      ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)))
      ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1))) =
      bxor (rhCenter (t + P) (r + 1)) (rhCenter (t + 1) ((r + P) + 2)) := by
  have htr := gt_twopow_of_zero_diag_le ((t + P) + r) k hk hz
  have h2k1 : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h1 := winWitt_testBit_scale_cross_cone (t + P) k (r + 1) (by omega)
  have h2 := winWitt_testBit_scale_cross_cone (t + 1) k ((r + P) + 2) (by omega)
  rw [show ((t + 1) + twopow (k + 1)) - ((r + P) + 2) =
    (t + twopow (k + 1)) - ((r + P) + 1) by omega] at h2
  rw [h1, h2, lhCenter_late_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2]
  simp only [bxor_eq_xor]
  cases lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) <;>
    cases rhCenter (t + P) (r + 1) <;>
    cases rhCenter (t + 1) ((r + P) + 2) <;> decide

theorem winWitt_scale_cross_doubles_eq_reset_step_prop (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1)))
      (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + P) + 1))) =
      bxor (rhCenter (t + P) (r + 1)) (rhCenter (t + 1) ((r + P) + 2)) :=
  winWitt_scale_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2

/-- **Inter-cone zero-gap Sector-2 bit identity between `(t + P, r + 1)` and `(t + 1, (r + P) + 1)` at a doubling zero diagonal (9.610)**:
for all `P, t, k, r ∈ ℕ` with `t + P ≤ r` and `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k`, then `(winWitt (t + P) (2^k)).testBit (((t + P) + 2^(k+1)) - (r + 1)) = (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + P) + 1))`. -/
theorem winWitt_scale_cross_zero_gap_doubles_eq_reset_step (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    (winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)) =
      (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1)) := by
  have h := winWitt_scale_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2
  rw [rhCenter_gt_eq_false (t + P) (r + 1) (by omega),
    rhCenter_gt_eq_false (t + 1) ((r + P) + 2) (by omega)] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)) <;>
    cases (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1)) <;> decide

theorem winWitt_scale_cross_zero_gap_doubles_eq_reset_step_prop (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1)) =
      wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + P) + 1)) :=
  winWitt_scale_cross_zero_gap_doubles_eq_reset_step P t k r ht hk hz hd hset1 hset2

/-- **Sector-2 cross-center `winWitt` antiperiodicity on the post-black reset diagonal `z + 3` at a doubling zero diagonal (9.611)**:
for all `P, t, k, r ∈ ℕ` with `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k`, then `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + P) + 1)) ⊕ (winWitt ((t + 1) + P) (2^k)).testBit (((t + P) + 2^(k+1)) - (r + 1)) = !(rhCenter (t + 1) ((r + P) + 2) ⊕ rhCenter ((t + 1) + P) (r + 2))`. -/
theorem winWitt_scale_cross_reset_antiperiodic_of_doubles (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    bxor
      ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1)))
      ((winWitt ((t + 1) + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter (t + 1) ((r + P) + 2)) (rhCenter ((t + 1) + P) (r + 2))) := by
  have htr := gt_twopow_of_zero_diag_le ((t + P) + r) k hk hz
  have h2k1 : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h1 := winWitt_testBit_scale_cross_cone (t + 1) k ((r + P) + 2) (by omega)
  have h2 := winWitt_testBit_scale_cross_cone ((t + 1) + P) k (r + 2) (by omega)
  rw [show ((t + 1) + twopow (k + 1)) - ((r + P) + 2) =
    (t + twopow (k + 1)) - ((r + P) + 1) by omega] at h1
  rw [show (((t + 1) + P) + twopow (k + 1)) - (r + 2) =
    ((t + P) + twopow (k + 1)) - (r + 1) by omega] at h2
  rw [h1, h2, lhCenter_late_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2]
  simp only [bxor_eq_xor]
  cases lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) <;>
    cases rhCenter (t + 1) ((r + P) + 2) <;>
    cases rhCenter ((t + 1) + P) (r + 2) <;> decide

theorem winWitt_scale_cross_reset_antiperiodic_of_doubles_prop (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + P) + 1)))
      (wittBitBool (winWitt ((t + 1) + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1))) =
      !(bxor (rhCenter (t + 1) ((r + P) + 2)) (rhCenter ((t + 1) + P) (r + 2))) :=
  winWitt_scale_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2

/-- **Inter-cone zero-gap Sector-2 bit flip on the post-black reset diagonal `z + 3` at a doubling zero diagonal (9.612)**:
for all `P, t, k, r ∈ ℕ` with `t + P ≤ r` and `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k`, then `(winWitt ((t + 1) + P) (2^k)).testBit (((t + P) + 2^(k+1)) - (r + 1)) = !(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + P) + 1))`. -/
theorem winWitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    (winWitt ((t + 1) + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1)) := by
  have h := winWitt_scale_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2
  rw [rhCenter_gt_eq_false (t + 1) ((r + P) + 2) (by omega),
    rhCenter_gt_eq_false ((t + 1) + P) (r + 2) (by omega)] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1)) <;>
    cases (winWitt ((t + 1) + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles_prop (P t k r : Nat)
    (ht : t + P ≤ r) (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    wittBitBool (winWitt ((t + 1) + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1)) =
      !wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + P) + 1)) :=
  winWitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles P t k r ht hk hz hd hset1 hset2

/-- **Early-free cross-sector space-time equivalence between `(t + P, r + 1)` and `(t + 1, (r + P) + 2)` at a doubling zero diagonal (9.613)**:
for all `P, t, k, r ∈ ℕ` with `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k`, then the XOR of the Sector-1 `⊕` Sector-2 window pairs at `(t + P, r + 1)` and `(t + 1, (r + P) + 1)` equals `rhCenter ((t + P) + 2^k) (r + 1) ⊕ rhCenter ((t + 1) + 2^k) ((r + P) + 2)`. -/
theorem winWitt_sector_one_xor_sector_two_doubles_eq_reset_step (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    bxor
      (bxor
        ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow k) - (r + 1)))
        ((winWitt (t + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1))))
      (bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow k) - ((r + P) + 1)))
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1)))) =
      bxor
        (rhCenter ((t + P) + twopow k) (r + 1))
        (rhCenter ((t + 1) + twopow k) ((r + P) + 2)) := by
  have htr := gt_twopow_of_zero_diag_le ((t + P) + r) k hk hz
  have h2k1 : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h1 := winWitt_sector_one_xor_sector_two_rhCenter_cone (t + P) k (r + 1) (by omega)
  have h2 := winWitt_sector_one_xor_sector_two_rhCenter_cone (t + 1) k ((r + P) + 2) (by omega)
  rw [show ((t + 1) + twopow k) - ((r + P) + 2) =
    (t + twopow k) - ((r + P) + 1) by omega,
    show ((t + 1) + twopow (k + 1)) - ((r + P) + 2) =
    (t + twopow (k + 1)) - ((r + P) + 1) by omega] at h2
  rw [h1, h2, lhCenter_late_cross_doubles_eq_reset_step P t k r hk hz hd hset1 hset2]
  simp only [bxor_eq_xor]
  cases rhCenter ((t + P) + twopow k) (r + 1) <;>
    cases rhCenter ((t + 1) + twopow k) ((r + P) + 2) <;>
    cases lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) <;> decide

theorem winWitt_sector_one_xor_sector_two_doubles_eq_reset_step_prop (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow k) - (r + 1)))
        (wittBitBool (winWitt (t + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1))))
      (bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow k) - ((r + P) + 1)))
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + P) + 1)))) =
      bxor
        (rhCenter ((t + P) + twopow k) (r + 1))
        (rhCenter ((t + 1) + twopow k) ((r + P) + 2)) :=
  winWitt_sector_one_xor_sector_two_doubles_eq_reset_step P t k r hk hz hd hset1 hset2

/-- **Early-free cross-sector antiperiodicity on the post-black reset diagonal `z + 3` at a doubling zero diagonal (9.614)**:
for all `P, t, k, r ∈ ℕ` with `((t + P) + r) + 2 ≤ k`, if `(t + P) + r` is a zero diagonal where period `P` doubles and both `((t + P) + r) + 1` and `((t + P) + r) + 2` have settled by `t + 2^k`, then the XOR of the Sector-1 `⊕` Sector-2 window pairs at `(t + 1, (r + P) + 1)` and `((t + 1) + P, r + 1)` equals `!(rhCenter ((t + 1) + 2^k) ((r + P) + 2) ⊕ rhCenter (((t + 1) + P) + 2^k) (r + 2))`. -/
theorem winWitt_sector_one_xor_sector_two_reset_antiperiodic_of_doubles (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : settle (((t + P) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + P) + r) + 2) ≤ t + twopow k) :
    bxor
      (bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow k) - ((r + P) + 1)))
        ((winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + P) + 1))))
      (bxor
        ((winWitt ((t + 1) + P) (twopow k)).testBit (((t + P) + twopow k) - (r + 1)))
        ((winWitt ((t + 1) + P) (twopow k)).testBit (((t + P) + twopow (k + 1)) - (r + 1)))) =
      !(bxor
        (rhCenter ((t + 1) + twopow k) ((r + P) + 2))
        (rhCenter (((t + 1) + P) + twopow k) (r + 2))) := by
  have htr := gt_twopow_of_zero_diag_le ((t + P) + r) k hk hz
  have h2k1 : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h1 := winWitt_sector_one_xor_sector_two_rhCenter_cone (t + 1) k ((r + P) + 2) (by omega)
  have h2 := winWitt_sector_one_xor_sector_two_rhCenter_cone ((t + 1) + P) k (r + 2) (by omega)
  rw [show ((t + 1) + twopow k) - ((r + P) + 2) =
    (t + twopow k) - ((r + P) + 1) by omega,
    show ((t + 1) + twopow (k + 1)) - ((r + P) + 2) =
    (t + twopow (k + 1)) - ((r + P) + 1) by omega] at h1
  rw [show (((t + 1) + P) + twopow k) - (r + 2) =
    ((t + P) + twopow k) - (r + 1) by omega,
    show (((t + 1) + P) + twopow (k + 1)) - (r + 2) =
    ((t + P) + twopow (k + 1)) - (r + 1) by omega] at h2
  rw [h1, h2, lhCenter_late_cross_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2]
  simp only [bxor_eq_xor]
  cases rhCenter ((t + 1) + twopow k) ((r + P) + 2) <;>
    cases rhCenter (((t + 1) + P) + twopow k) (r + 2) <;>
    cases lhCenter ((t + 1) + twopow k) (twopow k - ((r + P) + 2)) <;> decide

theorem winWitt_sector_one_xor_sector_two_reset_antiperiodic_of_doubles_prop (P t k r : Nat)
    (hk : ((t + P) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + P) + r)) (hd : DoublesAt P ((t + P) + r))
    (hset1 : SettledBy (((t + P) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + P) + r) + 2) (t + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow k) - ((r + P) + 1)))
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + P) + 1))))
      (bxor
        (wittBitBool (winWitt ((t + 1) + P) (twopow k)) (((t + P) + twopow k) - (r + 1)))
        (wittBitBool (winWitt ((t + 1) + P) (twopow k)) (((t + P) + twopow (k + 1)) - (r + 1)))) =
      !(bxor
        (rhCenter ((t + 1) + twopow k) ((r + P) + 2))
        (rhCenter (((t + 1) + P) + twopow k) (r + 2))) :=
  winWitt_sector_one_xor_sector_two_reset_antiperiodic_of_doubles P t k r hk hz hd hset1 hset2

/-- **Real-orbit `2^k - 1` twin readout of `zcenter t` two steps before a zero diagonal (9.615)**:
for all `t, k ∈ ℕ` with `t + 2 ≤ k`, if `t + 2` is a zero diagonal and both `t` and `t + 2` have settled by `t + 2^k` (with NO settlement hypothesis on `t + 1`!), then `lhCenter (t + 2^k) (2^k - 1) = zcenter t`. -/
theorem lhCenter_late_twopow_sub_one_eq_zcenter_before_zero_diag (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : IsZeroDiag (t + 2))
    (hset0 : settle t ≤ t + twopow k)
    (hset2 : settle (t + 2) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - 1) = zcenter t := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k 0 (by omega)
    (by simpa using hz) (by simpa using hset2)
  simp only [Nat.sub_zero, Nat.zero_add] at htwin
  rw [← htwin, lhCenter_late_twopow_eq_zcenter t k (by omega) hset0]

theorem lhCenter_late_twopow_sub_one_eq_zcenter_before_zero_diag_prop (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : IsZeroDiag (t + 2))
    (hset0 : SettledBy t (t + twopow k))
    (hset2 : SettledBy (t + 2) (t + twopow k)) :
    ZCenterEq t (lhCenter (t + twopow k) (twopow k - 1)) :=
  (lhCenter_late_twopow_sub_one_eq_zcenter_before_zero_diag t k hk hz hset0 hset2).symm

/-- **Sector-2 `(t + 2^(k+1)) - 1` window readout of `zcenter t` two steps before a zero diagonal (9.616)**:
for all `t, k ∈ ℕ` with `t + 2 ≤ k`, if `t + 2` is a zero diagonal and both `t` and `t + 2` have settled by `t + 2^k`, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - 1) = zcenter t ⊕ rhCenter t 1`. -/
theorem winWitt_testBit_sector_two_sub_one_zcenter_before_zero_diag (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : IsZeroDiag (t + 2))
    (hset0 : settle t ≤ t + twopow k)
    (hset2 : settle (t + 2) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - 1) =
      bxor (zcenter t) (rhCenter t 1) := by
  have htr : t + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_cone t k 1 htr,
    lhCenter_late_twopow_sub_one_eq_zcenter_before_zero_diag t k hk hz hset0 hset2]

theorem winWitt_testBit_sector_two_sub_one_zcenter_before_zero_diag_prop (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : IsZeroDiag (t + 2))
    (hset0 : SettledBy t (t + twopow k))
    (hset2 : SettledBy (t + 2) (t + twopow k)) :
    ZCenterEq t
      (bxor
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - 1))
        (rhCenter t 1)) := by
  unfold ZCenterEq wittBitBool
  rw [winWitt_testBit_sector_two_sub_one_zcenter_before_zero_diag t k hk hz hset0 hset2]
  simp only [bxor_eq_xor]
  cases zcenter t <;> cases rhCenter t 1 <;> decide

/-- **Early-free cross-sector `(t + 2^k) - 1` window readout of `zcenter t` two steps before a zero diagonal (9.617)**:
for all `t, k ∈ ℕ` with `t + 2 ≤ k`, if `t + 2` is a zero diagonal and both `t` and `t + 2` have settled by `t + 2^k`, then `(winWitt t (2^k)).testBit ((t + 2^k) - 1) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - 1) = rhCenter (t + 2^k) 1 ⊕ zcenter t`. -/
theorem winWitt_sector_one_xor_sector_two_sub_one_zcenter_before_zero_diag (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : IsZeroDiag (t + 2))
    (hset0 : settle t ≤ t + twopow k)
    (hset2 : settle (t + 2) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow k) - 1))
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - 1)) =
      bxor (rhCenter (t + twopow k) 1) (zcenter t) := by
  have htr : t + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_sector_one_xor_sector_two_rhCenter_cone t k 1 htr,
    lhCenter_late_twopow_sub_one_eq_zcenter_before_zero_diag t k hk hz hset0 hset2]

theorem winWitt_sector_one_xor_sector_two_sub_one_zcenter_before_zero_diag_prop (t k : Nat)
    (hk : t + 2 ≤ k)
    (hz : IsZeroDiag (t + 2))
    (hset0 : SettledBy t (t + twopow k))
    (hset2 : SettledBy (t + 2) (t + twopow k)) :
    ZCenterEq t
      (bxor
        (rhCenter (t + twopow k) 1)
        (bxor
          (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))
          (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - 1)))) := by
  unfold ZCenterEq wittBitBool
  rw [winWitt_sector_one_xor_sector_two_sub_one_zcenter_before_zero_diag t k hk hz hset0 hset2]
  simp only [bxor_eq_xor]
  cases rhCenter (t + twopow k) 1 <;> cases zcenter t <;> decide

/-- **Shifted late `lhCenter` antiperiodic readout of `!zcenter (z + 1)` at a doubling zero diagonal (9.618)**:
for all `P, z, k ∈ ℕ` with `z + 1 ≤ k`, if `z` is a zero diagonal where period `P` doubles (`DoublesAt P z`) and `z + 1` has settled by `(z + 1) + 2^k`, then `lhCenter (((z + 1) + P) + 2^k) (P + 2^k) = !zcenter (z + 1)`. -/
theorem lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles (P z k : Nat)
    (hk : z + 1 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset : settle (z + 1) ≤ (z + 1) + twopow k) :
    lhCenter (((z + 1) + P) + twopow k) (P + twopow k) = !zcenter (z + 1) := by
  have h := lhCenter_late_shift_antiperiodic_of_doubles P z k 0 (Nat.zero_le z)
    (by simpa using hk) (by simpa using hz) (by simpa using hd) (by simpa using hset)
  simp only [Nat.zero_add] at h
  rw [h, lhCenter_late_twopow_eq_zcenter (z + 1) k hk hset]

theorem lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles_prop (P z k : Nat)
    (hk : z + 1 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset : SettledBy (z + 1) ((z + 1) + twopow k)) :
    ZCenterEq (z + 1) (!lhCenter (((z + 1) + P) + twopow k) (P + twopow k)) := by
  unfold ZCenterEq
  rw [lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles P z k hk hz hd hset]
  cases zcenter (z + 1) <;> decide

/-- **Outer left-strip `winWitt` readout of `!zcenter (z + 1)` at a doubling zero diagonal (9.619)**:
for all `P, z, k ∈ ℕ` with `z + 1 ≤ k`, if `z` is a zero diagonal where period `P` doubles and `z + 1` has settled by `(z + 1) + 2^k`, then `(winWitt ((z + 1) + P) (2^k)).testBit ((((z + 1) + P) + P) + 2^(k+1)) = !(zcenter (z + 1) ⊕ lhCenter ((z + 1) + P) P)`. -/
theorem winWitt_outer_left_strip_zcenter_antiperiodic_of_doubles (P z k : Nat)
    (hk : z + 1 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset : settle (z + 1) ≤ (z + 1) + twopow k) :
    (winWitt ((z + 1) + P) (twopow k)).testBit ((((z + 1) + P) + P) + twopow (k + 1)) =
      !(bxor (zcenter (z + 1)) (lhCenter ((z + 1) + P) P)) := by
  have hlt : (z + 1) + P < P + twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_outer_left_strip ((z + 1) + P) k P hlt,
    lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles P z k hk hz hd hset]
  simp only [bxor_eq_xor]
  cases zcenter (z + 1) <;>
    cases lhCenter ((z + 1) + P) P <;> decide

theorem winWitt_outer_left_strip_zcenter_antiperiodic_of_doubles_prop (P z k : Nat)
    (hk : z + 1 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset : SettledBy (z + 1) ((z + 1) + twopow k)) :
    ZCenterEq (z + 1)
      (!(bxor
        (wittBitBool (winWitt ((z + 1) + P) (twopow k)) ((((z + 1) + P) + P) + twopow (k + 1)))
        (lhCenter ((z + 1) + P) P))) := by
  unfold ZCenterEq wittBitBool
  rw [winWitt_outer_left_strip_zcenter_antiperiodic_of_doubles P z k hk hz hd hset]
  simp only [bxor_eq_xor]
  cases zcenter (z + 1) <;>
    cases lhCenter ((z + 1) + P) P <;> decide

/-- **Early-free cross-sector readout of `!zcenter (z + 1)` at a doubling zero diagonal (9.620)**:
for all `P, z, k ∈ ℕ` with `((z + 1) + P) + P < 2^k` and `z + 1 ≤ k`, if `z` is a zero diagonal where period `P` doubles and `z + 1` has settled by `(z + 1) + 2^k`, then `(winWitt ((z + 1) + P) (2^k)).testBit ((((z + 1) + P) + P) + 2^k) ⊕ (winWitt ((z + 1) + P) (2^k)).testBit ((((z + 1) + P) + P) + 2^(k+1)) = !(lhCenter (((z + 1) + P) + 2^k) P ⊕ zcenter (z + 1))`. -/
theorem winWitt_sector_one_xor_sector_two_zcenter_antiperiodic_of_doubles (P z k : Nat)
    (hcone : ((z + 1) + P) + P < twopow k) (hk : z + 1 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset : settle (z + 1) ≤ (z + 1) + twopow k) :
    bxor
      ((winWitt ((z + 1) + P) (twopow k)).testBit ((((z + 1) + P) + P) + twopow k))
      ((winWitt ((z + 1) + P) (twopow k)).testBit ((((z + 1) + P) + P) + twopow (k + 1))) =
      !(bxor (lhCenter (((z + 1) + P) + twopow k) P) (zcenter (z + 1))) := by
  rw [winWitt_sector_one_xor_sector_two_lhCenter_cone ((z + 1) + P) k P hcone,
    lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles P z k hk hz hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (((z + 1) + P) + twopow k) P <;>
    cases zcenter (z + 1) <;> decide

theorem winWitt_sector_one_xor_sector_two_zcenter_antiperiodic_of_doubles_prop (P z k : Nat)
    (hcone : ((z + 1) + P) + P < twopow k) (hk : z + 1 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset : SettledBy (z + 1) ((z + 1) + twopow k)) :
    ZCenterEq (z + 1)
      (!(bxor
        (lhCenter (((z + 1) + P) + twopow k) P)
        (bxor
          (wittBitBool (winWitt ((z + 1) + P) (twopow k)) ((((z + 1) + P) + P) + twopow k))
          (wittBitBool (winWitt ((z + 1) + P) (twopow k)) ((((z + 1) + P) + P) + twopow (k + 1)))))) := by
  unfold ZCenterEq wittBitBool
  rw [winWitt_sector_one_xor_sector_two_zcenter_antiperiodic_of_doubles P z k hcone hk hz hd hset]
  simp only [bxor_eq_xor]
  cases lhCenter (((z + 1) + P) + twopow k) P <;>
    cases zcenter (z + 1) <;> decide

/-- **Shifted late `lhCenter` `P`-invariant readout of `zcenter d` on all diagonals `d ≤ z` below a doubling point (9.621)**:
for all `P, z, d, k ∈ ℕ` with `d ≤ z` and `d ≤ k`, if `DoublesAt P z` and `settle d ≤ d + 2^k`, then `lhCenter ((d + P) + 2^k) (P + 2^k) = zcenter d` (contrasting with `!zcenter (z + 1)` at `d = z + 1` in `9.618`). -/
theorem lhCenter_late_shift_twopow_periodic_zcenter_of_doubles_le (P z d k : Nat)
    (hd : DoublesAt P z) (hdz : d ≤ z) (hk : d ≤ k)
    (hset : settle d ≤ d + twopow k) :
    lhCenter ((d + P) + twopow k) (P + twopow k) = zcenter d := by
  have h0 := lhCenter_late_shift_eq_ldiag d k 0 (Nat.zero_le d)
  simp only [Nat.sub_zero, Nat.zero_add] at h0
  rw [lhCenter_late_shift_eq_ldiag (d + P) k P (by omega),
    show (d + P) - P = d by omega,
    ldiag_periodic_of_doubles_le P z d d k hd hdz hk hset,
    ← h0,
    lhCenter_late_twopow_eq_zcenter d k hk hset]

theorem lhCenter_late_shift_twopow_periodic_zcenter_of_doubles_le_prop (P z d k : Nat)
    (hd : DoublesAt P z) (hdz : d ≤ z) (hk : d ≤ k)
    (hset : SettledBy d (d + twopow k)) :
    ZCenterEq d (lhCenter ((d + P) + twopow k) (P + twopow k)) :=
  (lhCenter_late_shift_twopow_periodic_zcenter_of_doubles_le P z d k hd hdz hk hset).symm

/-! ### Batch 22: Center-Boundary Post-Black Reset Bridges (`2^k ↔ 2^k - 1` and `1 + 2^k ↔ 2^k`), `!zcenter (z + 1)` Readouts at `z + 2`, and Sector-2 Zero-Gap `WinWittAgree` Refutations (9.622–9.636) -/

/-- **1-step real-orbit reset from `2^k` at `z + 1` to `2^k - 1` at `z + 2` after a zero diagonal (9.622)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and `z + 2` has settled by `(z + 1) + 2^k` (with NO settlement hypothesis on `z + 1` or `z + 3`!), then `lhCenter ((z + 2) + 2^k) (2^k - 1) = !lhCenter ((z + 1) + 2^k) (2^k)`. -/
theorem lhCenter_late_twopow_sub_one_reset_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 1) + twopow k) :
    lhCenter ((z + 2) + twopow k) (twopow k - 1) =
      !lhCenter ((z + 1) + twopow k) (twopow k) := by
  have hk2 : 2 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  have hblk := lhCenter_late_cross_step_one_of_zero_diag z k 0
    (by simpa using hk) (by simpa using hz) (by simpa using hset)
  have hstep := lhCenter_step_succ ((z + 1) + twopow k) (twopow k - 2)
  rw [show ((z + 1) + twopow k) + 1 = (z + 2) + twopow k by omega,
    show (twopow k - 2) + 1 = twopow k - 1 by omega,
    show (twopow k - 2) + 2 = twopow k by omega,
    hblk, Bool.true_or] at hstep
  rw [hstep]
  cases lhCenter ((z + 1) + twopow k) (twopow k) <;> rfl

theorem lhCenter_late_twopow_sub_one_reset_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 1) + twopow k)) :
    lhCenter ((z + 2) + twopow k) (twopow k - 1) =
      !lhCenter ((z + 1) + twopow k) (twopow k) :=
  lhCenter_late_twopow_sub_one_reset_after_zero_diag z k hk hz hset

/-- **Sector-2 fixed-bit step complementation from `z + 1` to `z + 2` after a zero diagonal (9.623)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and `z + 2` has settled by `(z + 1) + 2^k`, then `(winWitt (z + 1) (2^k)).testBit ((z + 1) + 2^(k+1)) ⊕ (winWitt (z + 2) (2^k)).testBit (((z + 2) + 2^(k+1)) - 1) = !(center (z + 1) ⊕ rhCenter (z + 2) 1)`. -/
theorem winWitt_sector_two_center_to_sub_one_step_complement_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 1) + twopow k) :
    bxor
      ((winWitt (z + 1) (twopow k)).testBit ((z + 1) + twopow (k + 1)))
      ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + twopow (k + 1)) - 1)) =
      !(bxor (Rule30UOR.Core.center (z + 1)) (rhCenter (z + 2) 1)) := by
  have h7 := gt_twopow_of_zero_diag_le z k (by omega) hz
  have hw1 := winWitt_testBit_outer_left_strip (z + 1) k 0 (by omega)
  simp only [Nat.add_zero, Nat.zero_add, lhCenter_zero_eq_center] at hw1
  have hw2 := winWitt_testBit_scale_cross_cone (z + 2) k 1 (by omega)
  rw [hw1, hw2, lhCenter_late_twopow_sub_one_reset_after_zero_diag z k hk hz hset]
  simp only [bxor_eq_xor]
  cases lhCenter ((z + 1) + twopow k) (twopow k) <;>
    cases Rule30UOR.Core.center (z + 1) <;>
    cases rhCenter (z + 2) 1 <;> decide

theorem winWitt_sector_two_center_to_sub_one_step_complement_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 1) + twopow k)) :
    bxor
      (wittBitBool (winWitt (z + 1) (twopow k)) ((z + 1) + twopow (k + 1)))
      (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + twopow (k + 1)) - 1)) =
      !(bxor (Rule30UOR.Core.center (z + 1)) (rhCenter (z + 2) 1)) :=
  winWitt_sector_two_center_to_sub_one_step_complement_after_zero_diag z k hk hz hset

/-- **Early-free cross-sector fixed-bit step complementation from `z + 1` to `z + 2` after a zero diagonal (9.624)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and `z + 2` has settled by `(z + 1) + 2^k`, then `((winWitt (z + 1) (2^k)).testBit ((z + 1) + 2^k) ⊕ (winWitt (z + 1) (2^k)).testBit ((z + 1) + 2^(k+1))) ⊕ ((winWitt (z + 2) (2^k)).testBit (((z + 2) + 2^k) - 1) ⊕ (winWitt (z + 2) (2^k)).testBit (((z + 2) + 2^(k+1)) - 1)) = !(center ((z + 1) + 2^k) ⊕ rhCenter ((z + 2) + 2^k) 1)`. -/
theorem winWitt_sector_one_xor_sector_two_center_to_sub_one_step_complement_after_zero_diag
    (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 1) + twopow k) :
    bxor
      (bxor
        ((winWitt (z + 1) (twopow k)).testBit ((z + 1) + twopow k))
        ((winWitt (z + 1) (twopow k)).testBit ((z + 1) + twopow (k + 1))))
      (bxor
        ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + twopow k) - 1))
        ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + twopow (k + 1)) - 1))) =
      !(bxor (Rule30UOR.Core.center ((z + 1) + twopow k)) (rhCenter ((z + 2) + twopow k) 1)) := by
  have h7 := gt_twopow_of_zero_diag_le z k (by omega) hz
  have hd1 := winWitt_sector_one_xor_sector_two_lhCenter_cone (z + 1) k 0 (by omega)
  simp only [Nat.add_zero, Nat.zero_add, lhCenter_zero_eq_center] at hd1
  have hd2 := winWitt_sector_one_xor_sector_two_rhCenter_cone (z + 2) k 1 (by omega)
  rw [hd1, hd2, lhCenter_late_twopow_sub_one_reset_after_zero_diag z k hk hz hset]
  simp only [bxor_eq_xor]
  cases lhCenter ((z + 1) + twopow k) (twopow k) <;>
    cases Rule30UOR.Core.center ((z + 1) + twopow k) <;>
    cases rhCenter ((z + 2) + twopow k) 1 <;> decide

theorem winWitt_sector_one_xor_sector_two_center_to_sub_one_step_complement_after_zero_diag_prop
    (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 1) + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt (z + 1) (twopow k)) ((z + 1) + twopow k))
        (wittBitBool (winWitt (z + 1) (twopow k)) ((z + 1) + twopow (k + 1))))
      (bxor
        (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + twopow k) - 1))
        (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + twopow (k + 1)) - 1))) =
      !(bxor (Rule30UOR.Core.center ((z + 1) + twopow k)) (rhCenter ((z + 2) + twopow k) 1)) :=
  winWitt_sector_one_xor_sector_two_center_to_sub_one_step_complement_after_zero_diag z k hk hz hset

/-- **Real-orbit `2^k - 1` readout of `!zcenter (z + 1)` at `z + 2` after a zero diagonal without settling `z + 3` (9.625)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and both `z + 1` and `z + 2` have settled by `(z + 1) + 2^k` (with NO settlement hypothesis on `z + 3`!), then `lhCenter ((z + 2) + 2^k) (2^k - 1) = !zcenter (z + 1)`. -/
theorem lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 1) + twopow k) :
    lhCenter ((z + 2) + twopow k) (twopow k - 1) = !zcenter (z + 1) := by
  rw [lhCenter_late_twopow_sub_one_reset_after_zero_diag z k hk hz hset2,
    lhCenter_late_twopow_eq_zcenter (z + 1) k (by omega) hset1]

theorem lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 1) + twopow k)) :
    ZCenterEq (z + 1) (!lhCenter ((z + 2) + twopow k) (twopow k - 1)) := by
  unfold ZCenterEq
  rw [lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag z k hk hz hset1 hset2]
  cases zcenter (z + 1) <;> decide

/-- **Sector-2 `((z + 2) + 2^(k+1)) - 1` window readout of `!zcenter (z + 1)` at `z + 2` after a zero diagonal (9.626)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and both `z + 1` and `z + 2` have settled by `(z + 1) + 2^k`, then `(winWitt (z + 2) (2^k)).testBit (((z + 2) + 2^(k+1)) - 1) = !(zcenter (z + 1) ⊕ rhCenter (z + 2) 1)`. -/
theorem winWitt_testBit_sector_two_sub_one_not_zcenter_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 1) + twopow k) :
    (winWitt (z + 2) (twopow k)).testBit (((z + 2) + twopow (k + 1)) - 1) =
      !(bxor (zcenter (z + 1)) (rhCenter (z + 2) 1)) := by
  have h7 := gt_twopow_of_zero_diag_le z k (by omega) hz
  rw [winWitt_testBit_scale_cross_cone (z + 2) k 1 (by omega),
    lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag z k hk hz hset1 hset2]
  simp only [bxor_eq_xor]
  cases zcenter (z + 1) <;> cases rhCenter (z + 2) 1 <;> decide

theorem winWitt_testBit_sector_two_sub_one_not_zcenter_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 1) + twopow k)) :
    ZCenterEq (z + 1)
      (!(bxor
        (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + twopow (k + 1)) - 1))
        (rhCenter (z + 2) 1))) := by
  unfold ZCenterEq wittBitBool
  rw [winWitt_testBit_sector_two_sub_one_not_zcenter_after_zero_diag z k hk hz hset1 hset2]
  simp only [bxor_eq_xor]
  cases zcenter (z + 1) <;> cases rhCenter (z + 2) 1 <;> decide

/-- **Early-free cross-sector `((z + 2) + 2^k) - 1` window readout of `!zcenter (z + 1)` at `z + 2` after a zero diagonal (9.627)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and both `z + 1` and `z + 2` have settled by `(z + 1) + 2^k`, then `(winWitt (z + 2) (2^k)).testBit (((z + 2) + 2^k) - 1) ⊕ (winWitt (z + 2) (2^k)).testBit (((z + 2) + 2^(k+1)) - 1) = !(rhCenter ((z + 2) + 2^k) 1 ⊕ zcenter (z + 1))`. -/
theorem winWitt_sector_one_xor_sector_two_sub_one_not_zcenter_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 1) + twopow k) :
    bxor
      ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + twopow k) - 1))
      ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + twopow (k + 1)) - 1)) =
      !(bxor (rhCenter ((z + 2) + twopow k) 1) (zcenter (z + 1))) := by
  have h7 := gt_twopow_of_zero_diag_le z k (by omega) hz
  rw [winWitt_sector_one_xor_sector_two_rhCenter_cone (z + 2) k 1 (by omega),
    lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag z k hk hz hset1 hset2]
  simp only [bxor_eq_xor]
  cases rhCenter ((z + 2) + twopow k) 1 <;> cases zcenter (z + 1) <;> decide

theorem winWitt_sector_one_xor_sector_two_sub_one_not_zcenter_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 1) + twopow k)) :
    ZCenterEq (z + 1)
      (!(bxor
        (rhCenter ((z + 2) + twopow k) 1)
        (bxor
          (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + twopow k) - 1))
          (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + twopow (k + 1)) - 1))))) := by
  unfold ZCenterEq wittBitBool
  rw [winWitt_sector_one_xor_sector_two_sub_one_not_zcenter_after_zero_diag z k hk hz hset1 hset2]
  simp only [bxor_eq_xor]
  cases rhCenter ((z + 2) + twopow k) 1 <;> cases zcenter (z + 1) <;> decide

/-- **Space-time identity between `((z + 1) + P, P + 2^k)` and `(z + 2, 2^k - 1)` at a doubling zero diagonal (9.628)**:
for all `P, z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal where period `P` doubles (`DoublesAt P z`) and both `z + 1` and `z + 2` have settled by `(z + 1) + 2^k`, then `lhCenter (((z + 1) + P) + 2^k) (P + 2^k) = lhCenter ((z + 2) + 2^k) (2^k - 1)` (both equal `!zcenter (z + 1)`). -/
theorem lhCenter_late_shift_twopow_doubles_eq_after_zero_diag_sub_one (P z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 1) + twopow k) :
    lhCenter (((z + 1) + P) + twopow k) (P + twopow k) =
      lhCenter ((z + 2) + twopow k) (twopow k - 1) := by
  rw [lhCenter_late_shift_twopow_antiperiodic_zcenter_of_doubles P z k (by omega) hz hd hset1,
    lhCenter_late_twopow_sub_one_eq_not_zcenter_after_zero_diag z k hk hz hset1 hset2]

theorem lhCenter_late_shift_twopow_doubles_eq_after_zero_diag_sub_one_prop (P z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 1) + twopow k)) :
    lhCenter (((z + 1) + P) + twopow k) (P + twopow k) =
      lhCenter ((z + 2) + twopow k) (twopow k - 1) :=
  lhCenter_late_shift_twopow_doubles_eq_after_zero_diag_sub_one P z k hk hz hd hset1 hset2

/-- **1-step real-orbit reset from `1 + 2^k` at `z + 2` to `2^k` at `z + 3` after a zero diagonal (9.629)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and `z + 2` has settled by `(z + 2) + 2^k` (with NO settlement hypothesis on `z + 1` or `z + 3`!), then `lhCenter ((z + 3) + 2^k) (2^k) = !lhCenter ((z + 2) + 2^k) (1 + 2^k)`. -/
theorem lhCenter_late_twopow_reset_three_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    lhCenter ((z + 3) + twopow k) (twopow k) =
      !lhCenter ((z + 2) + twopow k) (1 + twopow k) := by
  have hk1 : 1 ≤ twopow k := by
    have := twopow_gt_self k
    omega
  have hblk := lhCenter_late_twopow_after_zero_diag z k hk hz hset
  have hstep := lhCenter_step_succ ((z + 2) + twopow k) (twopow k - 1)
  rw [show ((z + 2) + twopow k) + 1 = (z + 3) + twopow k by omega,
    show (twopow k - 1) + 1 = twopow k by omega,
    show (twopow k - 1) + 2 = 1 + twopow k by omega,
    hblk, Bool.true_or] at hstep
  rw [hstep]
  cases lhCenter ((z + 2) + twopow k) (1 + twopow k) <;> rfl

theorem lhCenter_late_twopow_reset_three_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    lhCenter ((z + 3) + twopow k) (twopow k) =
      !lhCenter ((z + 2) + twopow k) (1 + twopow k) :=
  lhCenter_late_twopow_reset_three_after_zero_diag z k hk hz hset

/-- **Sector-2 fixed-bit step complementation from `z + 2` to `z + 3` after a zero diagonal (9.630)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and `z + 2` has settled by `(z + 2) + 2^k`, then `(winWitt (z + 2) (2^k)).testBit (((z + 2) + 1) + 2^(k+1)) ⊕ (winWitt (z + 3) (2^k)).testBit ((z + 3) + 2^(k+1)) = !(lhCenter (z + 2) 1 ⊕ center (z + 3))`. -/
theorem winWitt_sector_two_one_to_center_step_complement_after_zero_diag (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor
      ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + 1) + twopow (k + 1)))
      ((winWitt (z + 3) (twopow k)).testBit ((z + 3) + twopow (k + 1))) =
      !(bxor (lhCenter (z + 2) 1) (Rule30UOR.Core.center (z + 3))) := by
  have h7 := gt_twopow_of_zero_diag_le z k (by omega) hz
  have hw2 := winWitt_testBit_outer_left_strip (z + 2) k 1 (by omega)
  have hw3 := winWitt_testBit_outer_left_strip (z + 3) k 0 (by omega)
  simp only [Nat.add_zero, Nat.zero_add, lhCenter_zero_eq_center] at hw3
  rw [hw2, hw3, lhCenter_late_twopow_reset_three_after_zero_diag z k hk hz hset]
  simp only [bxor_eq_xor]
  cases lhCenter ((z + 2) + twopow k) (1 + twopow k) <;>
    cases lhCenter (z + 2) 1 <;>
    cases Rule30UOR.Core.center (z + 3) <;> decide

theorem winWitt_sector_two_one_to_center_step_complement_after_zero_diag_prop (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    bxor
      (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + 1) + twopow (k + 1)))
      (wittBitBool (winWitt (z + 3) (twopow k)) ((z + 3) + twopow (k + 1))) =
      !(bxor (lhCenter (z + 2) 1) (Rule30UOR.Core.center (z + 3))) :=
  winWitt_sector_two_one_to_center_step_complement_after_zero_diag z k hk hz hset

/-- **Early-free cross-sector fixed-bit step complementation from `z + 2` to `z + 3` after a zero diagonal (9.631)**:
for all `z, k ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal and `z + 2` has settled by `(z + 2) + 2^k`, then `((winWitt (z + 2) (2^k)).testBit (((z + 2) + 1) + 2^k) ⊕ (winWitt (z + 2) (2^k)).testBit (((z + 2) + 1) + 2^(k+1))) ⊕ ((winWitt (z + 3) (2^k)).testBit ((z + 3) + 2^k) ⊕ (winWitt (z + 3) (2^k)).testBit ((z + 3) + 2^(k+1))) = !(lhCenter ((z + 2) + 2^k) 1 ⊕ center ((z + 3) + 2^k))`. -/
theorem winWitt_sector_one_xor_sector_two_one_to_center_step_complement_after_zero_diag
    (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor
      (bxor
        ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + 1) + twopow k))
        ((winWitt (z + 2) (twopow k)).testBit (((z + 2) + 1) + twopow (k + 1))))
      (bxor
        ((winWitt (z + 3) (twopow k)).testBit ((z + 3) + twopow k))
        ((winWitt (z + 3) (twopow k)).testBit ((z + 3) + twopow (k + 1)))) =
      !(bxor (lhCenter ((z + 2) + twopow k) 1) (Rule30UOR.Core.center ((z + 3) + twopow k))) := by
  have h7 := gt_twopow_of_zero_diag_le z k (by omega) hz
  have hd2 := winWitt_sector_one_xor_sector_two_lhCenter_cone (z + 2) k 1 (by omega)
  have hd3 := winWitt_sector_one_xor_sector_two_lhCenter_cone (z + 3) k 0 (by omega)
  simp only [Nat.add_zero, Nat.zero_add, lhCenter_zero_eq_center] at hd3
  rw [hd2, hd3, lhCenter_late_twopow_reset_three_after_zero_diag z k hk hz hset]
  simp only [bxor_eq_xor]
  cases lhCenter ((z + 2) + twopow k) (1 + twopow k) <;>
    cases lhCenter ((z + 2) + twopow k) 1 <;>
    cases Rule30UOR.Core.center ((z + 3) + twopow k) <;> decide

theorem winWitt_sector_one_xor_sector_two_one_to_center_step_complement_after_zero_diag_prop
    (z k : Nat)
    (hk : z + 2 ≤ k)
    (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    bxor
      (bxor
        (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + 1) + twopow k))
        (wittBitBool (winWitt (z + 2) (twopow k)) (((z + 2) + 1) + twopow (k + 1))))
      (bxor
        (wittBitBool (winWitt (z + 3) (twopow k)) ((z + 3) + twopow k))
        (wittBitBool (winWitt (z + 3) (twopow k)) ((z + 3) + twopow (k + 1)))) =
      !(bxor (lhCenter ((z + 2) + twopow k) 1) (Rule30UOR.Core.center ((z + 3) + twopow k))) :=
  winWitt_sector_one_xor_sector_two_one_to_center_step_complement_after_zero_diag z k hk hz hset

/-- **Same-column late `lhCenter` invariance under Sector-2 zero-gap `WinWittAgree` (9.632)**:
for all `t, k, Q, r, a, L ∈ ℕ` with `t + Q < r`, `(t + Q) + r < 2^k`, `a ≤ (t + 2^(k+1)) - r`, and `(t + 2^(k+1)) - r ≤ a + L`, if `WinWittAgree t k Q a L` holds, then `lhCenter ((t + Q) + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - r)`. -/
theorem lhCenter_late_cross_eq_of_winWittAgree_zero_gap (t k Q r a L : Nat)
    (hr : t + Q < r) (hcone : (t + Q) + r < twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - r) := by
  have hi := hw (((t + twopow (k + 1)) - r) - a) (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show a + (((t + twopow (k + 1)) - r) - a) = (t + twopow (k + 1)) - r by omega,
    show ((t + twopow (k + 1)) - r) + Q = ((t + Q) + twopow (k + 1)) - r by omega,
    winWitt_testBit_scale_cross_zero_gap (t + Q) k r hr hcone,
    winWitt_testBit_scale_cross_zero_gap t k r (by omega) (by omega)] at hi
  exact hi

theorem lhCenter_late_cross_eq_of_winWittAgree_zero_gap_prop (t k Q r a L : Nat)
    (hr : t + Q < r) (hcone : (t + Q) + r < twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - r) :=
  lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q r a L hr hcone ha hL hw

/-- **Refutation of `WinWittAgree t k 2 a L` in the Sector-2 zero gap across any settled zero diagonal (9.633)**:
for all `t, k, r, a, L ∈ ℕ` with `t + 2 < r` and `(t + r) + 2 ≤ k`, if `t + r` is a zero diagonal, `settle (t + r) ≤ t + 2^k`, `settle ((t + r) + 2) ≤ (t + 2) + 2^k`, and `a ≤ (t + 2^(k+1)) - r ≤ a + L`, then `¬ WinWittAgree t k 2 a L`. -/
theorem not_winWittAgree_two_scale_cross_zero_gap_of_zero_diag (t k r a L : Nat)
    (hr : t + 2 < r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset0 : settle (t + r) ≤ t + twopow k)
    (hset2 : settle ((t + r) + 2) ≤ (t + 2) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k 2 a L := by
  intro hw
  have hcone : (t + 2) + r < twopow k := by
    have := twopow_gt_self k
    omega
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k 2 r a L hr hcone ha hL hw
  have h0 := lhCenter_late_cross_of_zero_diag t k r (by omega) hz hset0
  have h2 : lhCenter ((t + 2) + twopow k) (twopow k - r) = true := by
    rw [lhCenter_late_cross_eq_ldiag (t + 2) k r (by omega),
      show (t + 2) + r = (t + r) + 2 by omega,
      ldiag_settled_eq_E ((t + r) + 2) (t + 2) k hk hset2]
    exact black_after_zero_diag (t + r) hz (t + 2)
  rw [h0, h2] at heq
  exact Bool.noConfusion heq

theorem not_winWittAgree_two_scale_cross_zero_gap_of_zero_diag_prop (t k r a L : Nat)
    (hr : t + 2 < r) (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset0 : SettledBy (t + r) (t + twopow k))
    (hset2 : SettledBy ((t + r) + 2) ((t + 2) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k 2 a L :=
  not_winWittAgree_two_scale_cross_zero_gap_of_zero_diag t k r a L hr hk hz hset0 hset2 ha hL

/-- **Refutation of `WinWittAgree t k Q a L` in the Sector-2 zero gap whenever `t + r` is a zero diagonal and `(t + Q) + r = z + 2` is a post-zero black diagonal (9.634)**:
for all `t, k, Q, r, z, a, L ∈ ℕ` with `t + Q < r`, `(t + Q) + r ≤ k`, `IsZeroDiag (t + r)`, `IsZeroDiag z`, `(t + Q) + r = z + 2`, `settle (t + r) ≤ t + 2^k`, `settle (z + 2) ≤ (t + Q) + 2^k`, and `a ≤ (t + 2^(k+1)) - r ≤ a + L`, `¬ WinWittAgree t k Q a L`. -/
theorem not_winWittAgree_scale_cross_zero_gap_of_zero_and_after_zero_diag
    (t k Q r z a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz0 : IsZeroDiag (t + r)) (hz : IsZeroDiag z)
    (hrel : (t + Q) + r = z + 2)
    (hset0 : settle (t + r) ≤ t + twopow k)
    (hset2 : settle (z + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k Q a L := by
  intro hw
  have hcone : (t + Q) + r < twopow k := by
    have := twopow_gt_self k
    omega
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q r a L hr hcone ha hL hw
  have h0 := lhCenter_late_cross_of_zero_diag t k r (by omega) hz0 hset0
  have hQ : lhCenter ((t + Q) + twopow k) (twopow k - r) = true := by
    rw [lhCenter_late_cross_eq_ldiag (t + Q) k r (by omega),
      hrel,
      ldiag_settled_eq_E (z + 2) (t + Q) k (by omega) hset2]
    exact black_after_zero_diag z hz (t + Q)
  rw [h0, hQ] at heq
  exact Bool.noConfusion heq

theorem not_winWittAgree_scale_cross_zero_gap_of_zero_and_after_zero_diag_prop
    (t k Q r z a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz0 : IsZeroDiag (t + r)) (hz : IsZeroDiag z)
    (hrel : (t + Q) + r = z + 2)
    (hset0 : SettledBy (t + r) (t + twopow k))
    (hset2 : SettledBy (z + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k Q a L :=
  not_winWittAgree_scale_cross_zero_gap_of_zero_and_after_zero_diag
    t k Q r z a L hr hk hz0 hz hrel hset0 hset2 ha hL

/-- **Single-window spatial `Q`-flip in Sector 2 at a doubling zero diagonal under `WinWittAgree` (9.635)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 1 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles (`DoublesAt Q ((t + Q) + r)`), `((t + Q) + r) + 1` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))`. -/
theorem winWitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  have hi := hw (((t + twopow (k + 1)) - (r + 1)) - a) (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hcone : ((t + Q) + r) + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [show a + (((t + twopow (k + 1)) - (r + 1)) - a) = (t + twopow (k + 1)) - (r + 1) by omega,
    show ((t + twopow (k + 1)) - (r + 1)) + Q = ((t + Q) + twopow (k + 1)) - (r + 1) by omega,
    winWitt_scale_cross_zero_gap_antiperiodic_of_doubles Q t k r hr hk hz hd hset] at hi
  exact hi.symm

theorem winWitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1))) :=
  winWitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Single-row spatial `Q`-flip in `lhCenter (t + 2^k)` at a doubling zero diagonal under Sector-2 zero-gap `WinWittAgree` (9.636)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 1 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `lhCenter (t + 2^k) (2^k - (r + 1)) = !lhCenter (t + 2^k) (2^k - ((r + Q) + 1))`. -/
theorem lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) =
      !lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) := by
  have hcone : ((t + Q) + r) + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 1) a L
    (by omega) (by omega) ha hL hw
  rw [lhCenter_late_cross_antiperiodic_of_doubles Q t k r hk hz hd hset] at heq
  exact heq.symm

theorem lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) =
      !lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) :=
  lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset ha hL hw

end Rule30UOR.Interfaces
