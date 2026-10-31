module

public import Rule30UOR.Interfaces.Part09

/-!
# `Rule30UOR.Interfaces`, part 10

* Batch 27: Single-Time `WinWittAgree` Sector-2 Window Bit Pinning, Period-1 Doubling Pinning & Unconditional Single-Time Refutation (`not_winWittAgree_one_of_doubles`) (9.697–9.711)
* Batch 28: Single-Time `WinWittAgree` `Q`-Transported Twin Identities, Linearized Steps, 1-Step Forward Propagation, Doubling-Diagonal 1-Step Flips, and Upward `Q`-Transport (9.712–9.726)
* Batch 29: Sharp Zero-Diagonal Gap Theorem (`z₁ + 5 ≤ z₂`), Upward `Q`-Transported Sector-2 Window Bit Laws, and Unconditional Single-Time Refutation `not_winWittAgree_three_of_doubles` for Period-3 Doubling (9.727–9.741)
* Batch 30: Period-3 Doubling Sector-2 Window Light-Cone Cascade, General-`Q` `(t + r) + 4` Zero-Diagonal Pinning, and Period-4 Doubling 3-Step Light-Cone Cascade (9.742–9.756)
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

/-! ### Batch 27: Single-Time `WinWittAgree` Sector-2 Window Bit Pinning, Period-1 Doubling Pinning & Unconditional Single-Time Refutation (`not_winWittAgree_one_of_doubles`) (9.697–9.711) -/

/-- **Twin-propagated Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` (`Q` diagonals below `z + 1`) from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.697)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t ≤ r`, `t + Q ≤ r + 1`, and `((t + Q) + r) + 3 ≤ k`, if `(t + Q) + r` and `(t + r) + 3` are zero diagonals, `(t + r) + 3` has settled by `t + 2^k`, `((t + Q) + r) + 2` has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k (by omega) hz
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 1) (by omega) (by omega)]
  exact lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L ht hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact 1-step Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.698)**:
under the same hypotheses as `9.697`, `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = false := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k (by omega) hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_pin_r_plus_two_false_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L ht hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` (9.699)**:
translates `9.689` into `winWitt t (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) = false := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k (by omega) hz
  rw [winWitt_testBit_scale_cross_zero_gap t k ((r + Q) + 1) (by omega) (by omega)]
  exact lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) = false :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **Late-row pinning `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = true` on `z + 1` from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.700)**:
combining `9.687` (`lhCenter (t + 2^k) (2^k - (r + 1)) = true`) with `lhCenter_late_cross_eq_of_winWittAgree_zero_gap` (`9.632`) at column `r + 1` pins `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = true`. -/
theorem lhCenter_late_cross_late_pin_doubling_diag_true_of_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + 1)) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k (by omega) hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 1) a L (by omega) (by omega) (by omega) hL hw]
  exact lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L (by omega) hk hz hz3 hset_z3 hset2 ha (by omega) hw

theorem lhCenter_late_cross_late_pin_doubling_diag_true_of_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_late_pin_doubling_diag_true_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact post-black reset Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = true` on diagonal `z + 3` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.701)**:
translates `9.690` into `winWitt (t + 1) (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k (by omega) hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - ((r + Q) + 1) = ((t + 1) + twopow (k + 1)) - ((r + Q) + 2) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k ((r + Q) + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` two diagonals before ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.702)**:
translates `9.691` into `winWitt t (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + 3) + r) k hk hz
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 1) (by omega) (by omega)]
  exact lhCenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` 1-step Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` across ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.703)**:
translates `9.692` into `winWitt (t + 1) (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_before_zero_diag_false_of_zero_diag_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = false := by
  have h7 := gt_twopow_of_zero_diag_le ((t + 3) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_before_zero_diag_false_of_zero_diag_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_step_one_pin_before_zero_diag_false_of_zero_diag_three_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = false` on the doubling diagonal `z + 1` without `WinWittAgree (t + 1)` (9.704)**:
translates `9.693` into `winWitt t (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 4)) = false := by
  have h7 := gt_twopow_of_zero_diag_le ((t + 3) + r) k hk hz
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 4) (by omega) (by omega)]
  exact lhCenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 4)) = false :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` post-black reset Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = true` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.705)**:
translates `9.694` into `winWitt (t + 1) (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 4)) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + 3) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 4) = ((t + 1) + twopow (k + 1)) - (r + 5) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 5) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 4)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 2)) = true` on the doubling diagonal `z + 1` from `WinWittAgree t k 1 a L` at the SINGLE bit `(t + 2^(k+1)) - (r + 1)` without `WinWittAgree (t + 1)` (9.706)**:
when `Q = 1`, `lhCenter (t + 2^k) (2^k - (r + 1))` lies on the zero diagonal `z = (t + 1) + r = t + (r + 1)` itself (`= false`), so the spatial 1-flip `9.636` pins `lhCenter (t + 2^k) (2^k - (r + 2)) = true`. -/
theorem lhCenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset0 : settle ((t + 1) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 1) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true := by
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    1 t k r a L hr hk hz hd hset1 ha hL hw
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 1)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 1) (by omega)
      (by rw [show t + (r + 1) = (t + 1) + r by omega]; exact hz)
      (by rw [show t + (r + 1) = (t + 1) + r by omega]; exact hset0)
  rw [hfalse, show (r + 1) + 1 = r + 2 by omega] at hflip
  cases h : lhCenter (t + twopow k) (twopow k - (r + 2))
  · rw [h] at hflip
    exact absurd hflip (by decide)
  · rfl

theorem lhCenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset0 : SettledBy ((t + 1) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 1) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` Sector-2 bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on `z + 1` from `WinWittAgree t k 1 a L` at `(t + 2^(k+1)) - (r + 1)` without `WinWittAgree (t + 1)` (9.707)**:
translates `9.706` into `winWitt t (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset0 : settle ((t + 1) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 1) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  have hz0 : (t + 1) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset0 : SettledBy ((t + 1) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 1) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` post-black reset pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.708)**:
when `Q = 1`, `lhCenter ((t + 1) + 2^k) (2^k - (r + 2))` lies on the post-zero black diagonal `z + 2 = ((t + 1) + r) + 2` itself (`= true`), so `9.681` (`Q = 1`) pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false`. -/
theorem lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset1 : settle (((t + 1) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 1) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = false := by
  have hflip := lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap
    1 t k r a L hr hk hz hd hset1 hset2 ha hL hw
  have htrue : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true :=
    lhCenter_late_cross_after_zero_diag (t + 1) k r hk hz (by omega)
  rw [htrue, show (r + 1) + 2 = r + 3 by omega] at hflip
  cases h : lhCenter ((t + 1) + twopow k) (twopow k - (r + 3))
  · rfl
  · rw [h] at hflip
    exact absurd hflip (by decide)

theorem lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset1 : SettledBy (((t + 1) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 1) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = false :=
  lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Period-1 doubling single-time `WinWittAgree` post-black reset Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.709)**:
translates `9.708` into `winWitt (t + 1) (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset1 : settle (((t + 1) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 1) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = false := by
  have h7 := gt_twopow_of_zero_diag_le ((t + 1) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 2) = ((t + 1) + twopow (k + 1)) - (r + 3) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 3) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset1 : SettledBy (((t + 1) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 1) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 1 a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = false :=
  winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 1 a L` across the 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at ANY period-1 doubling zero diagonal `z = (t + 1) + r` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.710)**:
for all `t, k, r, a, L ∈ ℕ` with `t + 1 ≤ r` and `((t + 1) + r) + 2 ≤ k`, if `(t + 1) + r` is a zero diagonal where period `1` doubles (`DoublesAt 1 ((t + 1) + r)`), `((t + 1) + r) + 1` and `((t + 1) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 3)`, and `(t + 2^(k+1)) - (r + 1) ≤ a + L`, then `¬ WinWittAgree t k 1 a L`. -/
theorem not_winWittAgree_one_of_doubles
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset1 : settle (((t + 1) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 1) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ WinWittAgree t k 1 a L := by
  intro hw
  have h7 := gt_twopow_of_zero_diag_le ((t + 1) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hfalse := lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_one_and_single_winWittAgree
    t k r a L hr hk hz hd hset1 hset2 (by omega) hL hw
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap
    t k 1 (r + 3) a L (by omega) (by omega) ha (by omega) hw
  have htrue : lhCenter (t + twopow k) (twopow k - (r + 3)) = true := by
    rw [show r + 3 = (r + 1) + 2 by omega]
    exact lhCenter_late_cross_after_zero_diag t k (r + 1)
      (by rw [show (t + (r + 1)) + 2 = ((t + 1) + r) + 2 by omega]; exact hk)
      (by rw [show t + (r + 1) = (t + 1) + r by omega]; exact hz)
      (by rw [show (t + (r + 1)) + 2 = ((t + 1) + r) + 2 by omega]; exact hset2)
  rw [hfalse, htrue] at heq
  exact Bool.false_ne_true heq

theorem not_winWittAgree_one_of_doubles_prop
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 1) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 1) + r)) (hd : DoublesAt 1 ((t + 1) + r))
    (hset1 : SettledBy (((t + 1) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 1) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ WinWittAgree t k 1 a L :=
  not_winWittAgree_one_of_doubles
    t k r a L hr hk hz hd hset1 hset2 ha hL

/-- **Single-time refutation `¬ WinWittAgree t k Q a L` at a doubling zero diagonal `z = (t + Q) + r` when both `(t + r) + 3` and `((t + Q) + r) + 3` are zero diagonals (9.711)**:
by `9.690`, `WinWittAgree t k Q a L` across `[(t + 2^(k+1)) - (r + 2), (t + 2^(k+1)) - (r + 1)]` pins `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = true` on diagonal `z + 3`, contradicting `IsZeroDiag (z + 3)`. -/
theorem not_winWittAgree_of_doubles_and_zero_diag_three_and_after_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hza3 : IsZeroDiag (((t + Q) + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (hset_a3 : settle (((t + Q) + r) + 3) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ WinWittAgree t k Q a L := by
  intro hw
  have htrue := lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw
  have hfalse : lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) = false :=
    lhCenter_late_cross_of_zero_diag (t + 1) k ((r + Q) + 2)
      (by rw [show (t + 1) + ((r + Q) + 2) = ((t + Q) + r) + 3 by omega]; exact hk)
      (by rw [show (t + 1) + ((r + Q) + 2) = ((t + Q) + r) + 3 by omega]; exact hza3)
      (by rw [show (t + 1) + ((r + Q) + 2) = ((t + Q) + r) + 3 by omega]; exact hset_a3)
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem not_winWittAgree_of_doubles_and_zero_diag_three_and_after_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hza3 : IsZeroDiag (((t + Q) + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (hset_a3 : SettledBy (((t + Q) + r) + 3) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ WinWittAgree t k Q a L :=
  not_winWittAgree_of_doubles_and_zero_diag_three_and_after_three
    Q t k r a L hr hk hz hd hz3 hza3 hset_z3 hset1 hset2 hset_a3 ha hL

/-! ### Batch 28: Single-Time `WinWittAgree` `Q`-Transported Twin Identities, Linearized Steps, 1-Step Forward Propagation, Doubling-Diagonal 1-Step Flips, and Upward `Q`-Transport (9.712–9.726) -/

/-- **`Q`-transported Twin Identity `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))` in row `t + 2^k` from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.712)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q < r` and `((t + Q) + r) + 2 ≤ k`, if `((t + Q) + r) + 2` is a zero diagonal that has settled by `(t + Q) + 2^k` (requiring no settling hypothesis on `(t + Q) + r` or `((t + Q) + r) + 1`), `a ≤ (t + 2^(k+1)) - (r + 1)`, `(t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + 1))`. -/
theorem lhCenter_late_cross_twin_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hset : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [← lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q r a L hr (by omega) (by omega) hL hw,
    ← lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 1) a L (by omega) (by omega) ha (by omega) hw]
  exact lhCenter_late_cross_twin_before_zero_diag (t + Q) k r hk hz hset

theorem lhCenter_late_cross_twin_at_shift_of_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hset : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_twin_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **`Q`-transported Sector-2 window Twin Identity `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.713)**:
under the same hypotheses as `9.712`, the two adjacent Sector-2 window bits `(t + 2^(k+1)) - r` and `(t + 2^(k+1)) - (r + 1)` of `winWitt t (2^k)` are identically equal. -/
theorem winWitt_scale_cross_zero_gap_twin_at_shift_of_zero_diag_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hset : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k r (by omega) (by omega),
    winWitt_testBit_scale_cross_zero_gap t k (r + 1) (by omega) (by omega)]
  exact lhCenter_late_cross_twin_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

theorem winWitt_scale_cross_zero_gap_twin_at_shift_of_zero_diag_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hset : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) :=
  winWitt_scale_cross_zero_gap_twin_at_shift_of_zero_diag_and_winWittAgree
    Q t k r a L hr hk hz hset ha hL hw

/-- **`Q`-transported Linearization 1 (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 2))`) from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - (r + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.714)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r + 2` and `((t + Q) + r) + 3 ≤ k`, if `((t + Q) + r) + 3` is a zero diagonal that has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 3) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 2))`. -/
theorem lhCenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 2) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 3))
    (hset : settle (((t + Q) + r) + 3) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 3) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      bxor (lhCenter (t + twopow k) (twopow k - (r + 1)))
        (lhCenter (t + twopow k) (twopow k - (r + 2))) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 3)) = false :=
    lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
      Q t k (r + 3) a L (by omega)
      (by rw [show (t + Q) + (r + 3) = ((t + Q) + r) + 3 by omega]; exact hk)
      (by rw [show (t + Q) + (r + 3) = ((t + Q) + r) + 3 by omega]; exact hz)
      (by rw [show (t + Q) + (r + 3) = ((t + Q) + r) + 3 by omega]; exact hset)
      ha hL hw
  rw [lhCenter_late_cross_step t k r (by omega), hfalse, Bool.or_false]

theorem lhCenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 2) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 3))
    (hset : SettledBy (((t + Q) + r) + 3) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 3) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      bxor (lhCenter (t + twopow k) (twopow k - (r + 1)))
        (lhCenter (t + twopow k) (twopow k - (r + 2))) :=
  lhCenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **`Q`-transported Linearization 2 (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 3))`) from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - (r + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.715)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r + 1` and `((t + Q) + r) + 3 ≤ k`, if `((t + Q) + r) + 2` is a zero diagonal that has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ lhCenter (t + 2^k) (2^k - (r + 3))`. -/
theorem lhCenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hset : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      bxor (lhCenter (t + twopow k) (twopow k - (r + 1)))
        (lhCenter (t + twopow k) (twopow k - (r + 3))) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 2)) = false :=
    lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
      Q t k (r + 2) a L (by omega)
      (by rw [show (t + Q) + (r + 2) = ((t + Q) + r) + 2 by omega]; omega)
      (by rw [show (t + Q) + (r + 2) = ((t + Q) + r) + 2 by omega]; exact hz)
      (by rw [show (t + Q) + (r + 2) = ((t + Q) + r) + 2 by omega]; exact hset)
      ha hL hw
  rw [lhCenter_late_cross_step t k r (by omega), hfalse, Bool.false_or]

theorem lhCenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hset : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      bxor (lhCenter (t + twopow k) (twopow k - (r + 1)))
        (lhCenter (t + twopow k) (twopow k - (r + 3))) :=
  lhCenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact 1-step `false` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`Q` diagonals below a zero diagonal `z = ((t + Q) + r) + 3`) from a SINGLE `WinWittAgree t k Q a L` at time `t` across `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` without `DoublesAt` or `WinWittAgree (t + 1)` (9.716)**:
combining Linearization 1 (`9.714`) with the `Q`-transported Twin Identity (`9.712`) at `r + 1` cancels the two equal XOR inputs (`x ⊕ x = false`). -/
theorem lhCenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 3))
    (hset : settle (((t + Q) + r) + 3) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [lhCenter_late_cross_linear_step_one_at_shift_of_zero_diag_and_winWittAgree_zero_gap
      Q t k r a L (by omega) hk hz hset ha (by omega) hw,
    lhCenter_late_cross_twin_at_shift_of_zero_diag_and_winWittAgree_zero_gap
      Q t k (r + 1) a L (by omega)
      (by rw [show ((t + Q) + (r + 1)) + 2 = ((t + Q) + r) + 3 by omega]; exact hk)
      (by rw [show ((t + Q) + (r + 1)) + 2 = ((t + Q) + r) + 3 by omega]; exact hz)
      (by rw [show ((t + Q) + (r + 1)) + 2 = ((t + Q) + r) + 3 by omega]; exact hset)
      (by rw [show (r + 1) + 1 = r + 2 by omega]; omega) hL hw]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - ((r + 1) + 1)) <;> rfl

theorem lhCenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 3))
    (hset : SettledBy (((t + Q) + r) + 3) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = false :=
  lhCenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact 1-step Sector-2 bit `false` pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` (`Q` diagonals below `z = ((t + Q) + r) + 3`) from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.717)**:
translates `9.716` into `winWitt (t + 1) (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 3))
    (hset : settle (((t + Q) + r) + 3) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 3))
    (hset : SettledBy (((t + Q) + r) + 3) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree
    Q t k r a L hr hk hz hset ha hL hw

/-- **Unconditional 1-step forward propagation of `WinWittAgree t k Q a L` from a 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at time `t` to row `(t + 1) + 2^k` without `IsZeroDiag`, `DoublesAt`, `settle`, or `WinWittAgree (t + 1)` (9.718)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 3 < 2^k`, if `a ≤ (t + 2^(k+1)) - (r + 3)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter (((t + 1) + Q) + 2^k) (2^k - (r + 2)) = lhCenter ((t + 1) + 2^k) (2^k - (r + 2))`. -/
theorem lhCenter_late_cross_step_one_eq_of_winWittAgree_three_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hrk : ((t + Q) + r) + 3 < twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - (r + 2)) =
      lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + 1) + Q = (t + Q) + 1 by clear ha hL; omega,
    lhCenter_late_cross_step (t + Q) k r (by clear ha hL; omega),
    lhCenter_late_cross_step t k r (by clear ha hL; omega),
    lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 1) a L (by clear ha hL; omega) (by clear ha hL; omega) (by omega) hL hw,
    lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 2) a L (by clear ha hL; omega) (by clear ha hL; omega) (by omega) (by omega) hw,
    lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 3) a L (by clear ha hL; omega) (by clear ha hL; omega) ha (by omega) hw]

theorem lhCenter_late_cross_step_one_eq_of_winWittAgree_three_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hrk : ((t + Q) + r) + 3 < twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - (r + 2)) =
      lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) :=
  lhCenter_late_cross_step_one_eq_of_winWittAgree_three_zero_gap
    Q t k r a L hr hrk ha hL hw

/-- **Unconditional 1-step forward propagation of `WinWittAgree t k Q a L` from a 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` at time `t` to `winWitt (t + 1) (2^k)` at bit `(t + 2^(k+1)) - (r + 1)` without `WinWittAgree (t + 1)` (9.719)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 3 < 2^k`, if `a ≤ (t + 2^(k+1)) - (r + 3)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `(winWitt ((t + 1) + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - (r + 1)) = (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_step_one_eq_of_winWittAgree_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hrk : ((t + Q) + r) + 3 < twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt ((t + 1) + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (r + 1)) =
      (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show ((t + Q) + twopow (k + 1)) - (r + 1) = (((t + 1) + Q) + twopow (k + 1)) - (r + 2) by clear ha hL; omega,
    show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap ((t + 1) + Q) k (r + 2) (by clear ha hL; omega) (by clear ha hL; omega),
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_one_eq_of_winWittAgree_three_zero_gap
    Q t k r a L hr (by clear ha hL; omega) ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_eq_of_winWittAgree_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hrk : ((t + Q) + r) + 3 < twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt ((t + 1) + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - (r + 1)) =
      wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) :=
  winWitt_scale_cross_zero_gap_step_one_eq_of_winWittAgree_three
    Q t k r a L hr hrk ha hL hw

/-- **Single-time `WinWittAgree` 1-step spatial `Q`-flip on the doubling diagonal `z + 1` in row `(t + 1) + 2^k` (`lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = !lhCenter ((t + 1) + 2^k) (2^k - (r + 2))`) without `WinWittAgree (t + 1)` (9.720)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 3 ≤ k`, if `((t + Q) + r) + 2` is a zero diagonal where period `Q` doubles (`IsZeroDiag (((t + Q) + r) + 2)` and `DoublesAt Q (((t + Q) + r) + 2)`), `((t + Q) + r) + 1`, `((t + Q) + r) + 2`, and `((t + Q) + r) + 3` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 3)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = !lhCenter ((t + 1) + 2^k) (2^k - (r + 2))`. -/
theorem lhCenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hd : DoublesAt Q (((t + Q) + r) + 2))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (hset3 : settle (((t + Q) + r) + 3) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hlin1 := lhCenter_late_cross_linear_step_two_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L (by omega) hk hz (by omega) (by omega) (by omega) hw
  have hfalse : lhCenter (t + twopow k) (twopow k - ((r + Q) + 2)) = false :=
    lhCenter_late_cross_of_zero_diag t k ((r + Q) + 2)
      (by rw [show t + ((r + Q) + 2) = ((t + Q) + r) + 2 by omega]; omega)
      (by rw [show t + ((r + Q) + 2) = ((t + Q) + r) + 2 by omega]; exact hz)
      (by rw [show t + ((r + Q) + 2) = ((t + Q) + r) + 2 by omega]; exact hset2)
  have heq1 : lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) := by
    rw [show (r + Q) + 1 = (r + 1) + Q by clear ha hL; omega]
    exact (lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap
      Q (((t + Q) + r) + 2) t k (r + 1) a L (by clear ha hL; omega) (by clear ha hL; omega) (by clear ha hL; omega) hd
      (by rw [show (t + Q) + (r + 1) = ((t + Q) + r) + 1 by clear ha hL; omega]; exact hset1)
      (by omega) hL hw).symm
  have hflip3 : lhCenter (t + twopow k) (twopow k - (r + 3)) =
      !lhCenter (t + twopow k) (twopow k - ((r + Q) + 3)) := by
    rw [show (r + Q) + 3 = ((r + 2) + Q) + 1 by omega,
      show r + 3 = (r + 2) + 1 by omega]
    exact lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
      Q t k (r + 2) a L (by omega)
      (by rw [show ((t + Q) + (r + 2)) + 1 = ((t + Q) + r) + 3 by omega]; exact hk)
      (by rw [show (t + Q) + (r + 2) = ((t + Q) + r) + 2 by omega]; exact hz)
      (by rw [show (t + Q) + (r + 2) = ((t + Q) + r) + 2 by omega]; exact hd)
      (by rw [show ((t + Q) + (r + 2)) + 1 = ((t + Q) + r) + 3 by omega]; exact hset3)
      (by rw [show (r + 2) + 1 = r + 3 by omega]; exact ha)
      (by rw [show (r + 2) + 1 = r + 3 by omega]; omega) hw
  rw [lhCenter_late_cross_step t k (r + Q) (by omega), hfalse, Bool.false_or,
    heq1, hlin1, hflip3]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases lhCenter (t + twopow k) (twopow k - ((r + Q) + 3)) <;> rfl

theorem lhCenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hd : DoublesAt Q (((t + Q) + r) + 2))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (hset3 : SettledBy (((t + Q) + r) + 3) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) :=
  lhCenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 hset3 ha hL hw

/-- **Single-time `WinWittAgree` 1-step Sector-2 spatial `Q`-flip on `z + 1` in `winWitt (t + 1) (2^k)` (`(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = !(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`) without `WinWittAgree (t + 1)` (9.721)**:
translates `9.720` into `winWitt (t + 1) (2^k)` in the Sector-2 zero gap. -/
theorem winWitt_scale_cross_zero_gap_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hd : DoublesAt Q (((t + Q) + r) + 2))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (hset3 : settle (((t + Q) + r) + 3) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) =
      !(winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - ((r + Q) + 1) = ((t + 1) + twopow (k + 1)) - ((r + Q) + 2) by omega,
    show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k ((r + Q) + 2) (by omega) (by omega),
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 hset3 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag (((t + Q) + r) + 2))
    (hd : DoublesAt Q (((t + Q) + r) + 2))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (hset3 : SettledBy (((t + Q) + r) + 3) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) =
      !(wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_step_one_shift_flip_on_doubling_diag_of_doubles_and_single_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 hset3 ha hL hw

/-- **Upward `Q`-transport of a zero diagonal `z = (t + Q) + r`: `lhCenter ((t + Q) + 2^k) (2^k - (r + Q)) = false` on diagonal `z + Q` from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - (r + Q)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.722)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t < r` and `((t + Q) + r) + 1 ≤ k`, if `(t + Q) + r` is a zero diagonal that has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + Q) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + Q) + 2^k) (2^k - (r + Q)) = false`. -/
theorem lhCenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : settle ((t + Q) + r) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + Q))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + Q)) = false := by
  have hz0 : (t + Q) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + Q) a L
    (by clear ha hL; omega) (by clear ha hL; omega) ha hL hw]
  exact lhCenter_late_cross_of_zero_diag t k (r + Q)
    (by clear ha hL; omega)
    (by rw [show t + (r + Q) = (t + Q) + r by clear ha hL; omega]; exact hz)
    (by rw [show t + (r + Q) = (t + Q) + r by clear ha hL; omega]; exact hset)

theorem lhCenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : SettledBy ((t + Q) + r) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + Q))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + Q)) = false :=
  lhCenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Upward `Q`-transport of the post-zero black diagonal `z + 2`: `lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 2)) = true` on diagonal `z + Q + 2` from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - ((r + Q) + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.723)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t ≤ r + 1` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal and `((t + Q) + r) + 2` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 2)) = true`. -/
theorem lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 2)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q ((r + Q) + 2) a L
    (by clear ha hL; omega) (by clear ha hL; omega) ha hL hw]
  exact lhCenter_late_cross_after_zero_diag t k (r + Q)
    (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show t + (r + Q) = (t + Q) + r by clear ha hL; omega]; exact hz)
    (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by clear ha hL; omega]; exact hset2)

theorem lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 2)) = true :=
  lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Upward `Q`-transported 1-step complementation `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 2)) = !lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 1))` from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - ((r + Q) + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.724)**:
upgrades `9.666` by dropping both `DoublesAt` and `WinWittAgree (t + 1)`. -/
theorem lhCenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) =
      !lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have htrue := lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw
  rw [show (t + 1) + Q = (t + Q) + 1 by clear ha hL; omega,
    lhCenter_late_cross_step (t + Q) k (r + Q) (by clear ha hL; omega), htrue, Bool.true_or]
  simp only [bxor_eq_xor]
  cases lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) <;> rfl

theorem lhCenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) =
      !lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) :=
  lhCenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Upward `Q`-transported 1-step Sector-2 window bit flip `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - ((r + Q) + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.725)**:
upgrades `9.665` by dropping both `DoublesAt` and `WinWittAgree (t + 1)`. -/
theorem winWitt_scale_cross_zero_gap_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt ((t + 1) + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h1 : (t + twopow (k + 1)) - (r + 1) = (((t + 1) + Q) + twopow (k + 1)) - ((r + Q) + 2) := by clear ha hL; omega
  have h2 : (t + twopow (k + 1)) - (r + 1) = ((t + Q) + twopow (k + 1)) - ((r + Q) + 1) := by clear ha hL; omega
  rw [h1, winWitt_testBit_scale_cross_zero_gap ((t + 1) + Q) k ((r + Q) + 2) (by clear ha hL h1 h2; omega) (by clear ha hL h1 h2; omega),
    ← h1, h2, winWitt_testBit_scale_cross_zero_gap (t + Q) k ((r + Q) + 1) (by clear ha hL h1 h2; omega) (by clear ha hL h1 h2; omega)]
  exact lhCenter_late_cross_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    Q t k r a L (by clear ha hL h1 h2; omega) hk hz hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt ((t + 1) + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_late_step_flip_at_shift_after_zero_diag_of_single_winWittAgree
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Single-time refutation `¬ WinWittAgree t k Q a L` across the 3-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - (r + 1)]` whenever `(t + r) + 1` and `((t + Q) + r) + 3` are settled zero diagonals — without `DoublesAt` or `WinWittAgree (t + 1)` (9.726)**:
`IsZeroDiag (((t + Q) + r) + 3)` pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`9.716`), contradicting `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` on `((t + r) + 1) + 2` (`lhCenter_late_cross_after_zero_diag`). -/
theorem not_winWittAgree_of_zero_diag_one_and_shift_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz1 : IsZeroDiag ((t + r) + 1))
    (hz3 : IsZeroDiag (((t + Q) + r) + 3))
    (hset1 : settle (((t + r) + 1) + 2) ≤ (t + 1) + twopow k)
    (hset3 : settle (((t + Q) + r) + 3) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ WinWittAgree t k Q a L := by
  intro hw
  have hfalse := lhCenter_late_cross_step_one_eq_false_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz3 hset3 ha hL hw
  have htrue : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true :=
    lhCenter_late_cross_after_zero_diag (t + 1) k r
      (by rw [show ((t + 1) + r) + 2 = (t + r) + 3 by omega]; omega)
      (by rw [show (t + 1) + r = (t + r) + 1 by omega]; exact hz1)
      (by rw [show ((t + 1) + r) + 2 = ((t + r) + 1) + 2 by omega]; exact hset1)
  rw [htrue] at hfalse
  exact Bool.false_ne_true hfalse.symm

theorem not_winWittAgree_of_zero_diag_one_and_shift_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz1 : IsZeroDiag ((t + r) + 1))
    (hz3 : IsZeroDiag (((t + Q) + r) + 3))
    (hset1 : SettledBy (((t + r) + 1) + 2) ((t + 1) + twopow k))
    (hset3 : SettledBy (((t + Q) + r) + 3) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L) :
    ¬ WinWittAgree t k Q a L :=
  not_winWittAgree_of_zero_diag_one_and_shift_three
    Q t k r a L hr hk hz1 hz3 hset1 hset3 ha hL

/-! ### Batch 29: Sharp Zero-Diagonal Gap Theorem (`z₁ + 5 ≤ z₂`), Upward `Q`-Transported Sector-2 Window Bit Laws, and Unconditional Single-Time Refutation `not_winWittAgree_three_of_doubles` for Period-3 Doubling (9.727–9.741) -/

/-- **Minimum depth of a zero diagonal (`2 ≤ z`, sharp at `z = 2`) (9.727)**:
for every `z ∈ ℕ`, if `IsZeroDiag z`, then `2 ≤ z` (since `E 0 0 = true` and `E 1 0 = true`). -/
theorem zero_diag_ge_two (z : Nat) (hz : IsZeroDiag z) : 2 ≤ z := by
  rcases z with _ | _ | z
  · exact False.elim (not_isZeroDiag_zero hz)
  · have h1 := hz 0
    rw [Rule30UOR.ZeroDiagonals.E_one'] at h1
    exact False.elim (absurd h1 (by decide))
  · omega

theorem zero_diag_ge_two_prop (z : Nat) (hz : IsZeroDiag z) : 2 ≤ z :=
  zero_diag_ge_two z hz

/-- **No two zero diagonals are separated by 2 (`IsZeroDiag z → ¬ IsZeroDiag (z + 2)`) (9.728)**:
for every `z ∈ ℕ`, if `IsZeroDiag z`, then `z + 2` is all-black (`black_after_zero_diag`), so `¬ IsZeroDiag (z + 2)`. -/
theorem not_isZeroDiag_add_two (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 2) := by
  intro hz2
  have hb := black_after_zero_diag z hz 0
  have hw := hz2 0
  rw [hb] at hw
  exact Bool.noConfusion hw

theorem not_isZeroDiag_add_two_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 2) :=
  not_isZeroDiag_add_two z hz

/-- **Diagonal `z + 1` after a zero diagonal `z` is never all-black (`IsZeroDiag z → ¬ IsBlackDiag (z + 1)`) (9.729)**:
if `IsBlackDiag (z + 1)` held, `accumulate_after_zero` would force `IsZeroDiag (z - 1)` adjacent to `IsZeroDiag z`, contradicting `zero_then_nonzero`. Combined with `zero_then_nonzero` (`¬ IsZeroDiag (z + 1)`), diagonal `z + 1` is neither all-white nor all-black. -/
theorem not_isBlackDiag_add_one_of_zero_diag (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsBlackDiag (z + 1) := by
  intro hb1
  rcases z with _ | j
  · exact not_isZeroDiag_zero hz
  · have hj : IsZeroDiag j := by
      intro t
      have hacc := Rule30UOR.CompilePoints.accumulate_after_zero hz t
      rw [hb1 (t + 1), hb1 t] at hacc
      revert hacc
      cases E j t <;> decide
    exact Rule30UOR.CompilePoints.zero_then_nonzero j hj hz

theorem not_isBlackDiag_add_one_of_zero_diag_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsBlackDiag (z + 1) :=
  not_isBlackDiag_add_one_of_zero_diag z hz

/-- **No two zero diagonals are separated by 3 (`IsZeroDiag z → ¬ IsZeroDiag (z + 3)`) (9.730)**:
if `IsZeroDiag (z + 3)` held, `twin_before_zero` and `black_after_zero_diag` would force `IsBlackDiag (z + 1)`, contradicting `not_isBlackDiag_add_one_of_zero_diag` (`9.729`). -/
theorem not_isZeroDiag_add_three (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 3) := by
  intro hz3
  apply not_isBlackDiag_add_one_of_zero_diag z hz
  intro t
  have htwin := Rule30UOR.CompilePoints.twin_before_zero (j := z + 1)
    (by rw [show (z + 1) + 2 = z + 3 by omega]; exact hz3) t
  rw [htwin]
  exact black_after_zero_diag z hz t

theorem not_isZeroDiag_add_three_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 3) :=
  not_isZeroDiag_add_three z hz

/-- **Diagonal `z + 3` after a zero diagonal `z` is never all-black (`IsZeroDiag z → ¬ IsBlackDiag (z + 3)`) (9.731)**:
if `IsBlackDiag (z + 3)` held, `reset_three_after_zero` (`E (z + 3) (t + 1) = !E (z + 1) t`) would force `IsZeroDiag (z + 1)`, contradicting `zero_then_nonzero`. Combined with `9.730` (`¬ IsZeroDiag (z + 3)`), diagonal `z + 3` is neither all-white nor all-black. -/
theorem not_isBlackDiag_add_three_of_zero_diag (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsBlackDiag (z + 3) := by
  intro hb3
  apply Rule30UOR.CompilePoints.zero_then_nonzero z hz
  intro t
  have hres := Rule30UOR.CompilePoints.reset_three_after_zero z hz t
  rw [hb3 (t + 1)] at hres
  revert hres
  cases E (z + 1) t <;> decide

theorem not_isBlackDiag_add_three_of_zero_diag_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsBlackDiag (z + 3) :=
  not_isBlackDiag_add_three_of_zero_diag z hz

/-- **No two zero diagonals are separated by 4 (`IsZeroDiag z → ¬ IsZeroDiag (z + 4)`) (9.732)**:
if `IsZeroDiag (z + 4)` held, `twin_before_zero` and `black_after_zero_diag` would force `IsBlackDiag (z + 3)`, contradicting `not_isBlackDiag_add_three_of_zero_diag` (`9.731`). -/
theorem not_isZeroDiag_add_four (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 4) := by
  intro hz4
  apply not_isBlackDiag_add_three_of_zero_diag z hz
  intro t
  have htwin := Rule30UOR.CompilePoints.twin_before_zero (j := z + 2)
    (by rw [show (z + 2) + 2 = z + 4 by omega]; exact hz4) t
  rw [← htwin]
  exact black_after_zero_diag z hz t

theorem not_isZeroDiag_add_four_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 4) :=
  not_isZeroDiag_add_four z hz

/-- **Sharp Zero-Diagonal Minimum Gap Theorem (`z₁ + 5 ≤ z₂` for all zero diagonals `z₁ < z₂`, sharp at `z₁ = 2, z₂ = 7`) (9.733)**:
for all `z₁, z₂ ∈ ℕ`, if `IsZeroDiag z₁`, `IsZeroDiag z₂`, and `z₁ < z₂`, then `z₁ + 5 ≤ z₂`. -/
theorem zero_diag_gap_ge_five (z1 z2 : Nat)
    (h1 : IsZeroDiag z1) (h2 : IsZeroDiag z2) (hlt : z1 < z2) :
    z1 + 5 ≤ z2 := by
  refine Decidable.byContradiction fun hlt5 => ?_
  have hd : z2 = z1 + 1 ∨ z2 = z1 + 2 ∨ z2 = z1 + 3 ∨ z2 = z1 + 4 := by omega
  rcases hd with rfl | rfl | rfl | rfl
  · exact Rule30UOR.CompilePoints.zero_then_nonzero z1 h1 h2
  · exact not_isZeroDiag_add_two z1 h1 h2
  · exact not_isZeroDiag_add_three z1 h1 h2
  · exact not_isZeroDiag_add_four z1 h1 h2

theorem zero_diag_gap_ge_five_prop (z1 z2 : Nat)
    (h1 : IsZeroDiag z1) (h2 : IsZeroDiag z2) (hlt : z1 < z2) :
    z1 + 5 ≤ z2 :=
  zero_diag_gap_ge_five z1 z2 h1 h2 hlt

/-- **Upward `Q`-transported Sector-2 bit evaluation `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = false` on diagonal `z + Q` from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - (r + Q)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.734)**:
translates `9.722` into `winWitt (t + Q) (2^k)`, where the `+ Q` time shift and `+ Q` spatial shift cancel to give bit index `(t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_late_eq_false_at_shift_of_zero_diag_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : settle ((t + Q) + r) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + Q))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - r) = false := by
  have hz0 : (t + Q) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + Q) + twopow (k + 1)) - (r + Q) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + Q) k (r + Q) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

theorem winWitt_scale_cross_zero_gap_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : SettledBy ((t + Q) + r) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + Q))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - r) = false :=
  winWitt_scale_cross_zero_gap_late_eq_false_at_shift_of_zero_diag_and_winWittAgree
    Q t k r a L hr hk hz hset ha hL hw

/-- **Upward `Q`-transported Sector-2 bit evaluation `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on diagonal `z + Q + 2` from a SINGLE `WinWittAgree t k Q a L` at bit `(t + 2^(k+1)) - ((r + Q) + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.735)**:
translates `9.723` into `winWitt (t + Q) (2^k)` at bit `(t + 2^(k+1)) - (r + 2)`. -/
theorem winWitt_scale_cross_zero_gap_late_eq_true_at_shift_after_zero_diag_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 2) = ((t + Q) + twopow (k + 1)) - ((r + Q) + 2) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + Q) k ((r + Q) + 2) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_scale_cross_zero_gap_late_eq_true_at_shift_after_zero_diag_and_winWittAgree
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **Upward `Q`-transported 1-step `true` pinning `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 1)) = true` on diagonal `z + Q + 2` from a SINGLE `WinWittAgree t k Q a L` across `[(t + 2^(k+1)) - ((r + Q) + 2), (t + 2^(k+1)) - (r + Q)]` without `DoublesAt` or `WinWittAgree (t + 1)` (9.736)**:
combines `9.722` (`= false`) and `9.723` (`= true`) with `lhCenter_step_succ` (`false ⊕ (_ || true) = true`). -/
theorem lhCenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : settle ((t + Q) + r) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hfalse := lhCenter_late_cross_late_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr (by clear ha hL; omega) hz hset0 (by omega) hL hw
  have htrue := lhCenter_late_cross_late_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L (by clear ha hL; omega) hk hz hset2 ha (by omega) hw
  have hstep := lhCenter_step_succ ((t + Q) + twopow k) (twopow k - ((r + Q) + 2))
  rw [show ((t + Q) + twopow k) + 1 = ((t + 1) + Q) + twopow k by clear ha hL; omega,
    show (twopow k - ((r + Q) + 2)) + 1 = twopow k - ((r + Q) + 1) by clear ha hL; omega,
    show (twopow k - ((r + Q) + 2)) + 2 = twopow k - (r + Q) by clear ha hL; omega,
    hfalse, htrue, Bool.or_true] at hstep
  exact hstep

theorem lhCenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : SettledBy ((t + Q) + r) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 1)) = true :=
  lhCenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Upward `Q`-transported 1-step Sector-2 bit `true` pinning `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = true` from a SINGLE `WinWittAgree t k Q a L` across `[(t + 2^(k+1)) - ((r + Q) + 2), (t + 2^(k+1)) - (r + Q)]` without `DoublesAt` or `WinWittAgree (t + 1)` (9.737)**:
translates `9.736` into `winWitt ((t + 1) + Q) (2^k)` at bit `(t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : settle ((t + Q) + r) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt ((t + 1) + Q) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = (((t + 1) + Q) + twopow (k + 1)) - ((r + Q) + 1) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap ((t + 1) + Q) k ((r + Q) + 1) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : SettledBy ((t + Q) + r) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 2))
    (hL : (t + twopow (k + 1)) - (r + Q) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt ((t + 1) + Q) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_scale_cross_zero_gap_late_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 doubling 1-step pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = true` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 3 a L` at time `t` across `[(t + 2^(k+1)) - (r + 2), (t + 2^(k+1)) - (r + 1)]` without `WinWittAgree (t + 1)` (9.738)**:
combines `x_2 = true` (`9.676`), `x_3 = false` (on `z`), and `x_4 = false` (`9.693`) in `lhCenter_late_cross_step t k (r + 1)` (`true ⊕ (false || false) = true`). -/
theorem lhCenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hx2 : lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
    lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
      3 t k r a L (by clear ha hL; omega) hk hz (by clear ha hL; omega) ha (by omega) hw
  have hx3 : lhCenter (t + twopow k) (twopow k - (r + 3)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 3)
      (by clear ha hL; omega)
      (by rw [show t + (r + 3) = (t + 3) + r by clear ha hL; omega]; exact hz)
      (by rw [show t + (r + 3) = (t + 3) + r by clear ha hL; omega]; exact hset0)
  have hx4 : lhCenter (t + twopow k) (twopow k - (r + 4)) = false := by
    rw [show r + 4 = (r + 3) + 1 by clear ha hL; omega]
    exact lhCenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree
      t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step t k (r + 1) (by clear ha hL; omega)
  rw [show (r + 1) + 2 = r + 3 by clear ha hL; omega,
    show (r + 1) + 1 = r + 2 by clear ha hL; omega,
    show (r + 1) + 3 = r + 4 by clear ha hL; omega,
    hx2, hx3, hx4] at hstep
  exact hstep

theorem lhCenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 2-step pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 3 a L` at time `t` across `[(t + 2^(k+1)) - (r + 2), (t + 2^(k+1)) - r]` without `WinWittAgree (t + 1)` or `WinWittAgree (t + 2)` (9.739)**:
combines `x'_1 = true` (`9.679`) and `x'_3 = true` (`9.738`) in `lhCenter_late_cross_step (t + 1) k r` (`true ⊕ (_ || true) = false`). -/
theorem lhCenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hx1' : lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true :=
    lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
      3 t k r a L hr hk hz (by clear ha hL; omega) (by clear ha hL; omega) ha hL hw
  have hx3' : lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = true :=
    lhCenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
      t k r a L (by clear ha hL; omega) hk hz hd hset0 hset1 hset2 ha (by omega) hw
  have hstep := lhCenter_late_cross_step (t + 1) k r (by clear ha hL; omega)
  rw [show (t + 1) + 1 = t + 2 by clear ha hL; omega,
    hx1', hx3', Bool.or_true] at hstep
  exact hstep

theorem lhCenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = false :=
  lhCenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 3-step pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = true` on diagonal `z + 3` from a SINGLE `WinWittAgree t k 3 a L` at time `t` across `[(t + 2^(k+1)) - (r + 2), (t + 2^(k+1)) - r]` without `WinWittAgree (t + 1)`, `WinWittAgree (t + 2)`, or `settle (z + 3)` (9.740)**:
combines `9.739` (`lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false`) with the Post-Black Reset Identity `lhCenter_late_cross_reset_after_zero_diag (t + 2) k (r + 1)` (`9.572`). -/
theorem lhCenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 3)) = true := by
  have hres := lhCenter_late_cross_reset_after_zero_diag (t + 2) k (r + 1)
    (by rw [show ((t + 2) + (r + 1)) + 2 = ((t + 3) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 2) + (r + 1) = (t + 3) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 2) + (r + 1)) + 2 = ((t + 3) + r) + 2 by clear ha hL; omega]; clear ha hL; omega)
  have hx2'' := lhCenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw
  rw [show (t + 2) + 1 = t + 3 by clear ha hL; omega,
    show (r + 1) + 2 = r + 3 by clear ha hL; omega,
    show (r + 1) + 1 = r + 2 by clear ha hL; omega,
    hx2''] at hres
  exact hres

theorem lhCenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 3 a L` across the 4-bit interval `[(t + 2^(k+1)) - (r + 3), (t + 2^(k+1)) - r]` at ANY period-3 doubling zero diagonal `z = (t + 3) + r` — without `WinWittAgree (t + 1)`, `WinWittAgree (t + 2)`, or `settle (z + 3)` (9.741)**:
`9.740` pins `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = true` on `z + 3`, whereas `lhCenter (t + 2^k) (2^k - (r + 3)) = false` on `z` (`lhCenter_late_cross_of_zero_diag`), contradicting `lhCenter_late_cross_eq_of_winWittAgree_zero_gap` (`9.632`) at `(t + 2^(k+1)) - (r + 3)`. -/
theorem not_winWittAgree_three_of_doubles
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k 3 a L := by
  intro hw
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have htrue := lhCenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 (by omega) hL hw
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k 3 (r + 3) a L
    (by clear ha hL; omega) (by clear ha hL; omega) ha (by omega) hw
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 3)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 3)
      (by clear ha hL; omega)
      (by rw [show t + (r + 3) = (t + 3) + r by clear ha hL; omega]; exact hz)
      (by rw [show t + (r + 3) = (t + 3) + r by clear ha hL; omega]; exact hset0)
  rw [htrue, hfalse] at heq
  exact Bool.noConfusion heq

theorem not_winWittAgree_three_of_doubles_prop
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k 3 a L :=
  not_winWittAgree_three_of_doubles
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL

/-! ### Batch 30: Period-3 Doubling Sector-2 Window Light-Cone Cascade, General-`Q` `(t + r) + 4` Zero-Diagonal Pinning, and Period-4 Doubling 3-Step Light-Cone Cascade (9.742–9.756) -/

/-- **Period-3 doubling 1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 3 a L` at time `t` without `WinWittAgree (t + 1)` (9.742)**:
translates `9.738` into `winWitt (t + 1) (2^k)` at bit `((t + 1) + 2^(k+1)) - (r + 3) = (t + 2^(k+1)) - (r + 2)`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_two_true_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 2) = ((t + 1) + twopow (k + 1)) - (r + 3) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 3) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_one_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_two_true_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_two_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 2-step Sector-2 window bit pinning `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - r) = false` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 3 a L` at time `t` without `WinWittAgree (t + 1)` or `WinWittAgree (t + 2)` (9.743)**:
translates `9.739` into `winWitt (t + 2) (2^k)` at bit `((t + 2) + 2^(k+1)) - (r + 2) = (t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_step_two_pin_r_false_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt (t + 2) (twopow k)).testBit ((t + twopow (k + 1)) - r) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 2) + twopow (k + 1)) - (r + 2) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 2) k (r + 2) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_two_pin_r_plus_two_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_two_pin_r_false_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt (t + 2) (twopow k)) ((t + twopow (k + 1)) - r) = false :=
  winWitt_scale_cross_zero_gap_step_two_pin_r_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling 3-step Sector-2 window bit pinning `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on diagonal `z + 3` from a SINGLE `WinWittAgree t k 3 a L` at time `t` without `WinWittAgree (t + 1)`, `WinWittAgree (t + 2)`, or `settle (z + 3)` (9.744)**:
translates `9.740` into `winWitt (t + 3) (2^k)` at bit `((t + 3) + 2^(k+1)) - (r + 3) = (t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt (t + 3) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 3) + twopow (k + 1)) - (r + 3) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 3) k (r + 3) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_three_pin_r_plus_three_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt (t + 3) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Exact 3-step same-bit negation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` at fixed bit index `(t + 2^(k+1)) - r` from a SINGLE 3-bit `WinWittAgree t k 3 a L` at time `t` (9.745)**:
at any period-3 doubling zero diagonal `z = (t + 3) + r`, bit `(t + 2^(k+1)) - r` alternates `(false, true, false, true)` across `t, t + 1, t + 2, t + 3` (`9.682`, `9.684`, `9.743`, `9.744`), so its value at `t + 3` is the exact negation of its value at `t`. -/
theorem winWitt_scale_cross_zero_gap_same_bit_r_flip_three_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    (winWitt (t + 3) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_three_pin_r_true_of_doubles_three_and_single_winWittAgree
      t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw,
    winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree
      3 t k r a L hr (by clear ha hL; omega) hz (by clear ha hL; omega) (by omega) hL hw]
  rfl

theorem winWitt_scale_cross_zero_gap_same_bit_r_flip_three_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 < r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    wittBitBool (winWitt (t + 3) (twopow k)) ((t + twopow (k + 1)) - r) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  winWitt_scale_cross_zero_gap_same_bit_r_flip_three_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **1-step `true` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.746)**:
in row `(t + 1) + 2^k`, cell `2^k - (r + 3)` lies on the zero diagonal `(t + 1) + (r + 3) = (t + r) + 4`, so the Twin Identity Before a Zero Diagonal (`9.592`) equates `lhCenter ((t + 1) + 2^k) (2^k - (r + 2))` with `lhCenter ((t + 1) + 2^k) (2^k - (r + 1))` (`= true` by `9.679`). -/
theorem lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset4 : settle ((t + r) + 4) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag (t + 1) k (r + 1)
    (by rw [show ((t + 1) + (r + 1)) + 2 = (t + r) + 4 by clear ha hL; omega]; exact hk4)
    (by rw [show ((t + 1) + (r + 1)) + 2 = (t + r) + 4 by clear ha hL; omega]; exact hz4)
    (by rw [show ((t + 1) + (r + 1)) + 2 = (t + r) + 4 by clear ha hL; omega]; exact hset4)
  rw [show (r + 1) + 1 = r + 2 by clear ha hL; omega] at htwin
  rw [← htwin]
  exact lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

theorem lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset4 : SettledBy ((t + r) + 4) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Exact `false` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = false` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.747)**:
combines `9.746` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true`) with `9.677` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`). -/
theorem lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset4 : settle ((t + r) + 4) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hstep := lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw
  have hflip := lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    Q t k r a L (by clear ha hL; omega) hk hz hset2 ha (by omega) hw
  rw [hstep] at hflip
  revert hflip
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> decide

theorem lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset4 : SettledBy ((t + r) + 4) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = false :=
  lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Doubling-diagonal `true` pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = true` on `z + 1` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` (9.748)**:
combines `9.747` (`lhCenter (t + 2^k) (2^k - (r + 1)) = false`) with the spatial `Q`-flip `9.636`. -/
theorem lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset4 : settle ((t + r) + 4) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hpin := lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L (by clear ha hL; omega) (by clear ha hL; omega) hz hd hset1 (by omega) (by omega) hw
  rw [hpin] at hflip
  revert hflip
  cases lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) <;> decide

theorem lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset4 : SettledBy ((t + r) + 4) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) = true :=
  lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **Period-4 single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.749)**:
when `Q = 4`, `(t + (r + 2)) + 2 = (t + 4) + r = z` is the zero diagonal itself, so the Twin Identity Before a Zero Diagonal (`9.592`) equates `lhCenter (t + 2^k) (2^k - (r + 3))` with `lhCenter (t + 2^k) (2^k - (r + 2))` (`= true` by `9.676`). -/
theorem lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k (r + 2)
    (by rw [show (t + (r + 2)) + 2 = (t + 4) + r by clear ha hL; omega]; clear ha hL; omega)
    (by rw [show (t + (r + 2)) + 2 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by rw [show (t + (r + 2)) + 2 = (t + 4) + r by clear ha hL; omega]; exact hset0)
  rw [show (r + 2) + 1 = r + 3 by clear ha hL; omega] at htwin
  rw [← htwin]
  exact lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    4 t k r a L hr hk hz hset2 ha hL hw

theorem lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` 1-step `true` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.750)**:
specializes `9.746` to `Q = 4`, where `(t + r) + 4 = (t + 4) + r = z` is the zero diagonal itself. -/
theorem lhCenter_late_cross_step_one_pin_r_plus_two_true_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ (t + 1) + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four
    4 t k r a L hr hk (by clear ha hL; omega) hz
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by clear ha hL; omega) hset2
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hset0)
    ha hL hw

theorem lhCenter_late_cross_step_one_pin_r_plus_two_true_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) ((t + 1) + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_step_one_pin_r_plus_two_true_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` `false` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on diagonal `z - 3` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.751)**:
specializes `9.747` to `Q = 4`, where `(t + r) + 4 = (t + 4) + r = z` is the zero diagonal itself. -/
theorem lhCenter_late_cross_pin_r_plus_one_false_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ (t + 1) + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = false :=
  lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    4 t k r a L hr hk (by clear ha hL; omega) hz
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by clear ha hL; omega) hset2
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hset0)
    ha hL hw

theorem lhCenter_late_cross_pin_r_plus_one_false_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) ((t + 1) + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = false :=
  lhCenter_late_cross_pin_r_plus_one_false_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 doubling single-time `WinWittAgree` `true` pinning `lhCenter (t + 2^k) (2^k - ((r + 4) + 1)) = true` on diagonal `z + 1` at ANY period-4 doubling zero diagonal `z = (t + 4) + r` without `WinWittAgree (t + 1)` (9.752)**:
specializes `9.748` to `Q = 4`, where `(t + r) + 4 = (t + 4) + r = z` is the doubling zero diagonal itself. -/
theorem lhCenter_late_cross_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ (t + 1) + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter (t + twopow k) (twopow k - ((r + 4) + 1)) = true :=
  lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    4 t k r a L hr hk (by clear ha hL; omega) hz hd
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by clear ha hL; omega) hset1 hset2
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hset0)
    ha hL hw

theorem lhCenter_late_cross_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) ((t + 1) + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter (t + twopow k) (twopow k - ((r + 4) + 1)) = true :=
  lhCenter_late_cross_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 1-step `false` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 4)) = false` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1)` (9.753)**:
combines `x_3 = true` (`9.749`), `x_4 = false` (on `z`), and `x_5 = true` (`9.752`) in `lhCenter_late_cross_step t k (r + 2)` (`true ⊕ (false || true) = false`). -/
theorem lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 4)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hx3 : lhCenter (t + twopow k) (twopow k - (r + 3)) = true :=
    lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
      t k r a L (by clear ha hL; omega) hk hz hset0 hset2 ha (by omega) hw
  have hx4 : lhCenter (t + twopow k) (twopow k - (r + 4)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 4)
      (by clear ha hL; omega)
      (by rw [show t + (r + 4) = (t + 4) + r by clear ha hL; omega]; exact hz)
      (by rw [show t + (r + 4) = (t + 4) + r by clear ha hL; omega]; exact hset0)
  have hx5 : lhCenter (t + twopow k) (twopow k - (r + 5)) = true := by
    rw [show r + 5 = (r + 4) + 1 by clear ha hL; omega]
    exact lhCenter_late_cross_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree
      t k r a L hr hk hz hd (by clear ha hL; omega) hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step t k (r + 2) (by clear ha hL; omega)
  rw [show (r + 2) + 2 = r + 4 by clear ha hL; omega,
    show (r + 2) + 1 = r + 3 by clear ha hL; omega,
    show (r + 2) + 3 = r + 5 by clear ha hL; omega,
    hx3, hx4, hx5] at hstep
  exact hstep

theorem lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 4)) = false :=
  lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 3)) = true` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1)` or `WinWittAgree (t + 2)` (9.754)**:
combines `x'_2 = true` (`9.750`), `x'_3 = false` (on `z`), and `x'_4 = false` (`9.753`) in `lhCenter_late_cross_step (t + 1) k (r + 1)` (`true ⊕ (false || false) = true`). -/
theorem lhCenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 3)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hx2' : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true :=
    lhCenter_late_cross_step_one_pin_r_plus_two_true_of_zero_diag_four_and_single_winWittAgree
      t k r a L hr hk hz (by clear ha hL; omega) hset2 ha hL hw
  have hx3' : lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = false :=
    lhCenter_late_cross_of_zero_diag (t + 1) k (r + 3)
      (by clear ha hL; omega)
      (by rw [show (t + 1) + (r + 3) = (t + 4) + r by clear ha hL; omega]; exact hz)
      (by rw [show (t + 1) + (r + 3) = (t + 4) + r by clear ha hL; omega]; clear ha hL; omega)
  have hx4' : lhCenter ((t + 1) + twopow k) (twopow k - (r + 4)) = false :=
    lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
      t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step (t + 1) k (r + 1) (by clear ha hL; omega)
  rw [show (t + 1) + 1 = t + 2 by clear ha hL; omega,
    show (r + 1) + 2 = r + 3 by clear ha hL; omega,
    show (r + 1) + 1 = r + 2 by clear ha hL; omega,
    show (r + 1) + 3 = r + 4 by clear ha hL; omega,
    hx2', hx3', hx4'] at hstep
  exact hstep

theorem lhCenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 4)) = false` on diagonal `z + 3` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1)`, `WinWittAgree (t + 2)`, or `settle (z + 3)` (9.755)**:
combines `9.754` (`lhCenter ((t + 2) + 2^k) (2^k - (r + 3)) = true`) with the Post-Black Reset Identity `lhCenter_late_cross_reset_after_zero_diag (t + 2) k (r + 2)` (`9.572`). -/
theorem lhCenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 2) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 4)) = false := by
  have hres := lhCenter_late_cross_reset_after_zero_diag (t + 2) k (r + 2)
    (by rw [show ((t + 2) + (r + 2)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 2) + (r + 2) = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 2) + (r + 2)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hset2)
  have hx3'' := lhCenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 (by clear ha hL; omega) ha hL hw
  rw [show (t + 2) + 1 = t + 3 by clear ha hL; omega,
    show (r + 2) + 2 = r + 4 by clear ha hL; omega,
    show (r + 2) + 1 = r + 3 by clear ha hL; omega,
    hx3''] at hres
  exact hres

theorem lhCenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 2) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 4)) = false :=
  lhCenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 2)) = false` on diagonal `z + 1` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt`, `WinWittAgree (t + 1..3)`, or `settle (z + 3)` (9.756)**:
`9.749` and `9.632` at `r + 3` pin `lhCenter ((t + 4) + 2^k) (2^k - (r + 3)) = true` on `z + 3`, which by the Post-Black Reset Identity `lhCenter_late_cross_reset_after_zero_diag (t + 3) k (r + 1)` (`9.572`) equals `!lhCenter ((t + 3) + 2^k) (2^k - (r + 2))`. -/
theorem lhCenter_late_cross_step_three_pin_r_plus_two_false_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 2)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hx3 := lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 (by clear ha hL; omega) (by omega) hL hw
  have hy3 := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k 4 (r + 3) a L
    (by clear ha hL; omega) (by clear ha hL; omega) ha (by omega) hw
  have hres := lhCenter_late_cross_reset_after_zero_diag (t + 3) k (r + 1)
    (by rw [show ((t + 3) + (r + 1)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 3) + (r + 1) = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 3) + (r + 1)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hset2)
  rw [show (t + 3) + 1 = t + 4 by clear ha hL; omega,
    show (r + 1) + 2 = r + 3 by clear ha hL; omega,
    show (r + 1) + 1 = r + 2 by clear ha hL; omega,
    hy3, hx3] at hres
  revert hres
  cases lhCenter ((t + 3) + twopow k) (twopow k - (r + 2)) <;> decide

theorem lhCenter_late_cross_step_three_pin_r_plus_two_false_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 3))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 2)) = false :=
  lhCenter_late_cross_step_three_pin_r_plus_two_false_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

end Rule30UOR.Interfaces
