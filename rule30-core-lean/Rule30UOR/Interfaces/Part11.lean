module

public import Rule30UOR.Interfaces.Part10

/-!
# `Rule30UOR.Interfaces`, part 11

* Batch 31: Post-Zero OR-Absorption on `z + 4`, Unconditional Single-Time Refutation `not_winWittAgree_four_of_doubles`, and Sector-2 Window Bit Evaluations (9.757–9.771)
* Batch 32: Non-Black Diagonals `z + 4 .. z + 7`, Uniqueness of the Gap-5 Zero-Diagonal Pair `(2, 7)` (`z₁ + 6 ≤ z₂` for `2 < z₁`), and Period-4 Doubling Sector-2 Window Light-Cone Cascade (9.772–9.786)
* Batch 33: General-`Q` Reset-Diagonal Same-Bit Negations, `(t + r) + 5` Zero-Diagonal Parity Cancellation, and Unconditional Single-Time Refutation `not_winWittAgree_five_of_doubles` (9.787–9.801)
* Batch 34: Period-5 Post-Zero Reset/Absorption Steps 4–5 and Sector-2 Window Bit Pinning Across `t .. t + 5` (9.802–9.816)
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

/-! ### Batch 31: Post-Zero OR-Absorption on `z + 4`, Unconditional Single-Time Refutation `not_winWittAgree_four_of_doubles`, and Sector-2 Window Bit Evaluations (9.757–9.771) -/

/-- **1-step post-zero OR-absorption law on diagonal `z + 4` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = false`) when `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on `z + 3`, without `settle (z + 3)` or `settle (z + 4)` (9.757)**:
for any zero diagonal `z = t + r` with `settle (z + 2) ≤ t + 2^k`, `lhCenter (t + 2^k) (2^k - (r + 2)) = true` on `z + 2`, so if `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on `z + 3`, the OR gate in `lhCenter_late_cross_step t k (r + 1)` absorbs `lhCenter (t + 2^k) (2^k - (r + 4))` (`true || _ = true`) and yields `true ⊕ true = false`. -/
theorem lhCenter_late_cross_step_absorb_false_after_zero_diag
    (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset2 : settle ((t + r) + 2) ≤ t + twopow k)
    (h3 : lhCenter (t + twopow k) (twopow k - (r + 3)) = true) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2 : lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
    lhCenter_late_cross_after_zero_diag t k r hk hz hset2
  have hstep := lhCenter_late_cross_step t k (r + 1) (by omega)
  rw [show (r + 1) + 2 = r + 3 by omega,
    show (r + 1) + 1 = r + 2 by omega,
    show (r + 1) + 3 = r + 4 by omega,
    h2, h3, Bool.true_or] at hstep
  exact hstep

theorem lhCenter_late_cross_step_absorb_false_after_zero_diag_prop
    (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset2 : SettledBy ((t + r) + 2) (t + twopow k))
    (h3 : lhCenter (t + twopow k) (twopow k - (r + 3)) = true) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = false :=
  lhCenter_late_cross_step_absorb_false_after_zero_diag t k r hk hz hset2 h3

/-- **2-step post-zero reset-and-absorption law from `z + 1` to `z + 4` (`lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false`) when `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on `z + 1`, without `settle (z + 1)`, `settle (z + 3)`, or `settle (z + 4)` (9.758)**:
for any zero diagonal `z = t + r` with `settle (z + 2) ≤ t + 2^k`, `lhCenter (t + 2^k) (2^k - (r + 1)) = false` forces `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = true` on `z + 3` by `9.572`, which combines with `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true` on `z + 2` in `lhCenter_late_cross_step (t + 1) k r` to force `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = false` on `z + 4`. -/
theorem lhCenter_late_cross_two_step_absorb_false_after_zero_diag
    (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset2 : settle ((t + r) + 2) ≤ t + twopow k)
    (h1 : lhCenter (t + twopow k) (twopow k - (r + 1)) = false) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h3 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = true := by
    have hres := lhCenter_late_cross_reset_after_zero_diag t k r hk hz hset2
    rw [h1] at hres
    exact hres
  have h2 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true := by
    rw [lhCenter_late_cross_eq_ldiag (t + 1) k (r + 1) (by omega),
      show (t + 1) + (r + 1) = (t + r) + 2 by omega,
      ldiag_settled_eq_E ((t + r) + 2) (t + 1) k hk (by omega)]
    exact black_after_zero_diag (t + r) hz (t + 1)
  have hstep := lhCenter_late_cross_step (t + 1) k r (by omega)
  rw [show (t + 1) + 1 = t + 2 by omega,
    h2, h3, Bool.true_or] at hstep
  exact hstep

theorem lhCenter_late_cross_two_step_absorb_false_after_zero_diag_prop
    (t k r : Nat)
    (hk : (t + r) + 2 ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset2 : SettledBy ((t + r) + 2) (t + twopow k))
    (h1 : lhCenter (t + twopow k) (twopow k - (r + 1)) = false) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = false :=
  lhCenter_late_cross_two_step_absorb_false_after_zero_diag t k r hk hz hset2 h1

/-- **Period-4 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 5)) = true` on diagonal `z + 3` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..2)` or `settle (z + 3)` (9.759)**:
combines `9.753` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 4)) = false` on `z + 1`) with the Post-Black Reset Identity `lhCenter_late_cross_reset_after_zero_diag (t + 1) k (r + 3)` (`9.572`). -/
theorem lhCenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 5)) = true := by
  have h1 := lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 (by clear ha hL; omega) ha hL hw
  have hres := lhCenter_late_cross_reset_after_zero_diag (t + 1) k (r + 3)
    (by rw [show ((t + 1) + (r + 3)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 1) + (r + 3) = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 1) + (r + 3)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hset2)
  rw [show (t + 1) + 1 = t + 2 by clear ha hL; omega,
    show (r + 3) + 2 = r + 5 by clear ha hL; omega,
    show (r + 3) + 1 = r + 4 by clear ha hL; omega,
    h1] at hres
  exact hres

theorem lhCenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 5)) = true :=
  lhCenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 5)) = false` on diagonal `z + 4` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)` (9.760)**:
applies the 2-step post-zero reset-and-absorption law `9.758` at `(t + 1, r + 3)` to `9.753` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 4)) = false`). -/
theorem lhCenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 5)) = false := by
  have h1 := lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 (by clear ha hL; omega) ha hL hw
  have habs := lhCenter_late_cross_two_step_absorb_false_after_zero_diag (t + 1) k (r + 3)
    (by rw [show ((t + 1) + (r + 3)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 1) + (r + 3) = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 1) + (r + 3)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hset2)
    (by rw [show (r + 3) + 1 = r + 4 by clear ha hL; omega]; exact h1)
  rw [show (t + 1) + 2 = t + 3 by clear ha hL; omega,
    show (r + 3) + 2 = r + 5 by clear ha hL; omega] at habs
  exact habs

theorem lhCenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 5)) = false :=
  lhCenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 4-step `true` pinning `lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true` on diagonal `z + 4` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)` (9.761)**:
combines `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = true` (on `z + 2`), `9.755` (`lhCenter ((t + 3) + 2^k) (2^k - (r + 4)) = false` on `z + 3`), and `9.760` (`lhCenter ((t + 3) + 2^k) (2^k - (r + 5)) = false` on `z + 4`) in `lhCenter_late_cross_step (t + 3) k (r + 2)` (`true ⊕ (false || false) = true`). -/
theorem lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 4) + twopow k) (twopow k - (r + 4)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have hx3 : lhCenter ((t + 3) + twopow k) (twopow k - (r + 3)) = true := by
    have hblk := lhCenter_late_cross_after_zero_diag (t + 3) k (r + 1)
      (by rw [show ((t + 3) + (r + 1)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; exact hk)
      (by rw [show (t + 3) + (r + 1) = (t + 4) + r by clear ha hL; omega]; exact hz)
      (by rw [show ((t + 3) + (r + 1)) + 2 = ((t + 4) + r) + 2 by clear ha hL; omega]; clear ha hL; omega)
    rw [show (r + 1) + 2 = r + 3 by clear ha hL; omega] at hblk
    exact hblk
  have hx4 := lhCenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 (by clear ha hL; omega) ha hL hw
  have hx5 := lhCenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step (t + 3) k (r + 2) (by clear ha hL; omega)
  rw [show (t + 3) + 1 = t + 4 by clear ha hL; omega,
    show (r + 2) + 2 = r + 4 by clear ha hL; omega,
    show (r + 2) + 1 = r + 3 by clear ha hL; omega,
    show (r + 2) + 3 = r + 5 by clear ha hL; omega,
    hx3, hx4, hx5] at hstep
  exact hstep

theorem lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    lhCenter ((t + 4) + twopow k) (twopow k - (r + 4)) = true :=
  lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 4 a L` across the 5-bit interval `[(t + 2^(k+1)) - (r + 4), (t + 2^(k+1)) - r]` at ANY period-4 doubling zero diagonal `z = (t + 4) + r` without `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)` (9.762)**:
by `9.761`, `WinWittAgree t k 4 a L` across `[r, r + 2]` forces `lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true`, whereas `lhCenter (t + 2^k) (2^k - (r + 4))` lies on the zero diagonal `z = (t + 4) + r` (`= false`), contradicting `WinWittAgree t k 4 a L` at `(t + 2^(k+1)) - (r + 4)` (`9.632`). -/
theorem not_winWittAgree_four_of_doubles
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 4))
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k 4 a L := by
  intro hw
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have htrue := lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 (by omega) hL hw
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 4)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 4)
      (by clear ha hL; omega)
      (by rw [show t + (r + 4) = (t + 4) + r by clear ha hL; omega]; exact hz)
      (by rw [show t + (r + 4) = (t + 4) + r by clear ha hL; omega]; exact hset0)
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k 4 (r + 4) a L
    (by clear ha hL; omega) (by clear ha hL; omega) ha (by omega) hw
  rw [htrue, hfalse] at heq
  exact Bool.noConfusion heq

theorem not_winWittAgree_four_of_doubles_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 4))
    (hL : (t + twopow (k + 1)) - r ≤ a + L) :
    ¬ WinWittAgree t k 4 a L :=
  not_winWittAgree_four_of_doubles
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL

/-- **1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.763)**:
translates `9.746` into `winWitt (t + 1) (2^k)` at bit `((t + 1) + 2^(k+1)) - (r + 2) = (t + 2^(k+1)) - (r + 1)`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winWittAgree_and_zero_diag_four
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
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_one_pin_r_plus_two_true_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winWittAgree_and_zero_diag_four_prop
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
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` when both `(t + Q) + r` and `(t + r) + 4` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.764)**:
translates `9.747` into `winWitt t (2^k)` at bit `(t + 2^(k+1)) - (r + 1)`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
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
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 1) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four_prop
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
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hz4 hset0 hset2 hset4 ha hL hw

/-- **Doubling-diagonal Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = true` on `z + 1` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` (9.765)**:
translates `9.748` into `winWitt t (2^k)` at bit `(t + 2^(k+1)) - ((r + Q) + 1)`. -/
theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
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
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k ((r + Q) + 1) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four_prop
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
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **Period-4 single-time `WinWittAgree` Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.766)**:
translates `9.749` into `winWitt t (2^k)` at bit `(t + 2^(k+1)) - (r + 3)`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 3)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 3) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 ≤ r + 1) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 3)) = true :=
  winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` 1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` on diagonal `z - 1` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.767)**:
specializes `9.763` to `Q = 4`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ (t + 1) + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_single_winWittAgree_and_zero_diag_four
    4 t k r a L hr hk (by clear ha hL; omega) hz
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by clear ha hL; omega) hset2
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hset0)
    ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) ((t + 1) + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_one_true_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 single-time `WinWittAgree` Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` on diagonal `z - 3` across ANY zero diagonal `z = (t + 4) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.768)**:
specializes `9.764` to `Q = 4`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_zero_diag_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ (t + 1) + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 4) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_single_winWittAgree_and_zero_diag_four
    4 t k r a L hr hk (by clear ha hL; omega) hz
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by clear ha hL; omega) hset2
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hset0)
    ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_zero_diag_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) ((t + 1) + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 4) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_pin_r_plus_one_false_of_zero_diag_four_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-4 doubling single-time `WinWittAgree` Sector-2 window bit pinning `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + 4) + 1)) = true` on diagonal `z + 1` at ANY period-4 doubling zero diagonal `z = (t + 4) + r` without `WinWittAgree (t + 1)` (9.769)**:
specializes `9.765` to `Q = 4`. -/
theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree
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
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + 4) + 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    4 t k r a L hr hk (by clear ha hL; omega) hz hd
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hz)
    (by clear ha hL; omega) hset1 hset2
    (by rw [show (t + r) + 4 = (t + 4) + r by clear ha hL; omega]; exact hset0)
    ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree_prop
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
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + 4) + 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 4-step Sector-2 window bit pinning `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on diagonal `z + 4` from a SINGLE 3-bit `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)` (9.770)**:
translates `9.761` into `winWitt (t + 4) (2^k)` at bit `((t + 4) + 2^(k+1)) - (r + 4) = (t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt (t + 4) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 4) + twopow (k + 1)) - (r + 4) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 4) k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt (t + 4) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Exact 4-step same-bit negation `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` at fixed bit index `(t + 2^(k+1)) - r` from a SINGLE 3-bit `WinWittAgree t k 4 a L` at time `t` (9.771)**:
combines `9.770` (`(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = true`) with `9.682` (`(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false`). -/
theorem winWitt_scale_cross_zero_gap_same_bit_r_flip_four_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt (t + 4) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_four_and_single_winWittAgree
      t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw,
    winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree
      4 t k r a L hr (by clear ha hL; omega) hz (by clear ha hL; omega) (by omega) hL hw]
  rfl

theorem winWitt_scale_cross_zero_gap_same_bit_r_flip_four_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt (t + 4) (twopow k)) ((t + twopow (k + 1)) - r) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  winWitt_scale_cross_zero_gap_same_bit_r_flip_four_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-! ### Batch 32: Non-Black Diagonals `z + 4 .. z + 7`, Uniqueness of the Gap-5 Zero-Diagonal Pair `(2, 7)` (`z₁ + 6 ≤ z₂` for `2 < z₁`), and Period-4 Doubling Sector-2 Window Light-Cone Cascade (9.772–9.786) -/

/-- **Four diagonals past any zero diagonal is never all-black (`¬ IsBlackDiag (z + 4)`) (9.772)**:
if `IsBlackDiag (z + 4)`, then `zero_before_black_diag` forces `IsZeroDiag (z + 2)`, contradicting `not_isZeroDiag_add_two` (`9.728`). -/
theorem not_isBlackDiag_add_four_of_zero_diag (z : Nat) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 4) := by
  intro hb4
  exact not_isZeroDiag_add_two z hz
    (Rule30UOR.CompilePoints.zero_before_black_diag (z + 2)
      (by rw [show (z + 2) + 2 = z + 4 by omega]; exact hb4))

theorem not_isBlackDiag_add_four_of_zero_diag_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 4) :=
  not_isBlackDiag_add_four_of_zero_diag z hz

/-- **Five diagonals past any zero diagonal is never all-black (`¬ IsBlackDiag (z + 5)`) (9.773)**:
if `IsBlackDiag (z + 5)`, then `zero_before_black_diag` forces `IsZeroDiag (z + 3)`, contradicting `not_isZeroDiag_add_three` (`9.730`). -/
theorem not_isBlackDiag_add_five_of_zero_diag (z : Nat) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 5) := by
  intro hb5
  exact not_isZeroDiag_add_three z hz
    (Rule30UOR.CompilePoints.zero_before_black_diag (z + 3)
      (by rw [show (z + 3) + 2 = z + 5 by omega]; exact hb5))

theorem not_isBlackDiag_add_five_of_zero_diag_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 5) :=
  not_isBlackDiag_add_five_of_zero_diag z hz

/-- **Six diagonals past any zero diagonal is never all-black (`¬ IsBlackDiag (z + 6)`) (9.774)**:
if `IsBlackDiag (z + 6)`, then `zero_before_black_diag` forces `IsZeroDiag (z + 4)`, contradicting `not_isZeroDiag_add_four` (`9.732`). -/
theorem not_isBlackDiag_add_six_of_zero_diag (z : Nat) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 6) := by
  intro hb6
  exact not_isZeroDiag_add_four z hz
    (Rule30UOR.CompilePoints.zero_before_black_diag (z + 4)
      (by rw [show (z + 4) + 2 = z + 6 by omega]; exact hb6))

theorem not_isBlackDiag_add_six_of_zero_diag_prop (z : Nat) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 6) :=
  not_isBlackDiag_add_six_of_zero_diag z hz

/-- **Exact characterization of gap-5 zero-diagonal pairs (`IsZeroDiag z ∧ IsZeroDiag (z + 5) → IsBlackDiag (z - 1)`) (9.775)**:
if both `z` and `z + 5` are zero diagonals, `twin_before_zero` equates `z + 3` and `z + 4`, so `E_step (z + 2)` behind the all-black diagonal `z + 2` forces `z + 3` (and hence `z + 1`, by `reset_three_after_zero`) to alternate at every time step, which by `accumulate_after_zero` forces `z - 1` to be all-black. -/
theorem isBlackDiag_sub_one_of_zero_diag_and_add_five
    (z : Nat) (hz : IsZeroDiag z) (hz5 : IsZeroDiag (z + 5)) :
    Rule30UOR.CompilePoints.IsBlackDiag (z - 1) := by
  have hge2 := zero_diag_ge_two z hz
  intro t
  have hz5' : Rule30UOR.CompilePoints.Zero ((z + 3) + 2) := by
    rw [show (z + 3) + 2 = z + 5 by omega]
    exact hz5
  have htwin1 : E (z + 3) (t + 1) = E (z + 4) (t + 1) :=
    Rule30UOR.CompilePoints.twin_before_zero hz5' (t + 1)
  have htwin2 : E (z + 3) (t + 2) = E (z + 4) (t + 2) :=
    Rule30UOR.CompilePoints.twin_before_zero hz5' (t + 2)
  have hstep3 := Rule30UOR.Intent.E_step (z + 2) (t + 1)
  have hblk2 : E (z + 2) (t + 1) = true := black_after_zero_diag z hz (t + 1)
  rw [show (z + 2) + 2 = z + 4 by omega,
    show (z + 2) + 1 = z + 3 by omega,
    show (t + 1) + 1 = t + 2 by omega,
    hblk2, ← htwin2, ← htwin1] at hstep3
  have hres0 := Rule30UOR.CompilePoints.reset_three_after_zero z hz t
  have hres1 := Rule30UOR.CompilePoints.reset_three_after_zero z hz (t + 1)
  rw [show (t + 1) + 1 = t + 2 by omega] at hres1
  rw [hres0] at hstep3
  have hz' : Rule30UOR.CompilePoints.Zero ((z - 1) + 1) := by
    rw [show (z - 1) + 1 = z by omega]
    exact hz
  have hacc := Rule30UOR.CompilePoints.accumulate_after_zero hz' t
  rw [show (z - 1) + 2 = z + 1 by omega] at hacc
  rw [hacc] at hres1
  revert hstep3 hres1
  cases E (z - 1) t <;> cases E (z + 1) t <;> cases E (z + 3) (t + 2) <;> decide

theorem isBlackDiag_sub_one_of_zero_diag_and_add_five_prop
    (z : Nat) (hz : IsZeroDiag z) (hz5 : IsZeroDiag (z + 5)) :
    Rule30UOR.CompilePoints.IsBlackDiag (z - 1) :=
  isBlackDiag_sub_one_of_zero_diag_and_add_five z hz hz5

/-- **Uniqueness of the gap-5 zero-diagonal pair `(2, 7)` (`IsZeroDiag z ∧ IsZeroDiag (z + 5) → z ≤ 2`) (9.776)**:
for `z ≥ 3`, `IsBlackDiag (z - 1)` (`9.775`) forces `IsZeroDiag (z - 3)` (`zero_before_black_diag`), contradicting `zero_diag_gap_ge_five (z - 3) z` (`9.733`). -/
theorem zero_diag_le_two_of_add_five
    (z : Nat) (hz : IsZeroDiag z) (hz5 : IsZeroDiag (z + 5)) :
    z ≤ 2 := by
  refine Decidable.byContradiction fun h => ?_
  have hb1 := isBlackDiag_sub_one_of_zero_diag_and_add_five z hz hz5
  have hz3 : IsZeroDiag (z - 3) :=
    Rule30UOR.CompilePoints.zero_before_black_diag (z - 3)
      (by rw [show (z - 3) + 2 = z - 1 by omega]; exact hb1)
  have hgap := zero_diag_gap_ge_five (z - 3) z hz3 hz (by omega)
  omega

theorem zero_diag_le_two_of_add_five_prop
    (z : Nat) (hz : IsZeroDiag z) (hz5 : IsZeroDiag (z + 5)) :
    z ≤ 2 :=
  zero_diag_le_two_of_add_five z hz hz5

/-- **Five diagonals past any zero diagonal `z > 2` is never a zero diagonal (`2 < z → IsZeroDiag z → ¬ IsZeroDiag (z + 5)`) (9.777)**:
immediate from `zero_diag_le_two_of_add_five` (`9.776`). -/
theorem not_isZeroDiag_add_five_of_gt_two
    (z : Nat) (hgt : 2 < z) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 5) := by
  intro hz5
  have hle := zero_diag_le_two_of_add_five z hz hz5
  omega

theorem not_isZeroDiag_add_five_of_gt_two_prop
    (z : Nat) (hgt : 2 < z) (hz : IsZeroDiag z) :
    ¬ IsZeroDiag (z + 5) :=
  not_isZeroDiag_add_five_of_gt_two z hgt hz

/-- **Sharp zero-diagonal gap theorem above `z = 2` (`2 < z₁ → z₁ < z₂ → z₁ + 6 ≤ z₂`) (9.778)**:
combines `zero_diag_gap_ge_five` (`9.733`) with `not_isZeroDiag_add_five_of_gt_two` (`9.777`). -/
theorem zero_diag_gap_ge_six_of_gt_two
    (z1 z2 : Nat) (hgt : 2 < z1) (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2) (hlt : z1 < z2) :
    z1 + 6 ≤ z2 := by
  have h5 := zero_diag_gap_ge_five z1 z2 hz1 hz2 hlt
  have hn5 := not_isZeroDiag_add_five_of_gt_two z1 hgt hz1
  refine Decidable.byContradiction fun h => ?_
  have heq5 : z2 = z1 + 5 := by omega
  exact hn5 (heq5 ▸ hz2)

theorem zero_diag_gap_ge_six_of_gt_two_prop
    (z1 z2 : Nat) (hgt : 2 < z1) (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2) (hlt : z1 < z2) :
    z1 + 6 ≤ z2 :=
  zero_diag_gap_ge_six_of_gt_two z1 z2 hgt hz1 hz2 hlt

/-- **Seven diagonals past any zero diagonal `z > 2` is never all-black (`2 < z → IsZeroDiag z → ¬ IsBlackDiag (z + 7)`) (9.779)**:
if `IsBlackDiag (z + 7)`, then `zero_before_black_diag` forces `IsZeroDiag (z + 5)`, contradicting `not_isZeroDiag_add_five_of_gt_two` (`9.777`). -/
theorem not_isBlackDiag_add_seven_of_gt_two_and_zero_diag
    (z : Nat) (hgt : 2 < z) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 7) := by
  intro hb7
  exact not_isZeroDiag_add_five_of_gt_two z hgt hz
    (Rule30UOR.CompilePoints.zero_before_black_diag (z + 5)
      (by rw [show (z + 5) + 2 = z + 7 by omega]; exact hb7))

theorem not_isBlackDiag_add_seven_of_gt_two_and_zero_diag_prop
    (z : Nat) (hgt : 2 < z) (hz : IsZeroDiag z) :
    ¬ Rule30UOR.CompilePoints.IsBlackDiag (z + 7) :=
  not_isBlackDiag_add_seven_of_gt_two_and_zero_diag z hgt hz

/-- **Period-4 doubling 1-step Sector-2 window bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = false` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1)` (9.780)**:
translates `9.753` into `winWitt (t + 1) (2^k)` at bit `((t + 1) + 2^(k+1)) - (r + 4) = (t + 2^(k+1)) - (r + 3)`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_three_false_of_doubles_four_and_single_winWittAgree
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
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 3)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 3) = ((t + 1) + twopow (k + 1)) - (r + 4) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_one_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_three_false_of_doubles_four_and_single_winWittAgree_prop
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
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 3)) = false :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_three_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 2-step Sector-2 window bit pinning `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` on diagonal `z + 1` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..2)` (9.781)**:
translates `9.754` into `winWitt (t + 2) (2^k)` at bit `((t + 2) + 2^(k+1)) - (r + 3) = (t + 2^(k+1)) - (r + 1)`. -/
theorem winWitt_scale_cross_zero_gap_step_two_pin_r_plus_one_true_of_doubles_four_and_single_winWittAgree
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
    (winWitt (t + 2) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 1) = ((t + 2) + twopow (k + 1)) - (r + 3) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 2) k (r + 3) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_two_pin_r_plus_one_true_of_doubles_four_and_single_winWittAgree_prop
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
    wittBitBool (winWitt (t + 2) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_step_two_pin_r_plus_one_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step Sector-2 window bit pinning `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = false` on diagonal `z + 3` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..3)` or `settle (z + 3)` (9.782)**:
translates `9.755` into `winWitt (t + 3) (2^k)` at bit `((t + 3) + 2^(k+1)) - (r + 4) = (t + 2^(k+1)) - (r + 1)`. -/
theorem winWitt_scale_cross_zero_gap_step_three_pin_r_plus_one_false_of_doubles_four_and_single_winWittAgree
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
    (winWitt (t + 3) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 1) = ((t + 3) + twopow (k + 1)) - (r + 4) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 3) k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_three_pin_r_plus_four_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_three_pin_r_plus_one_false_of_doubles_four_and_single_winWittAgree_prop
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
    wittBitBool (winWitt (t + 3) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = false :=
  winWitt_scale_cross_zero_gap_step_three_pin_r_plus_one_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 2-step Sector-2 window bit pinning `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` on diagonal `z + 3` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..2)` or `settle (z + 3)` (9.783)**:
translates `9.759` into `winWitt (t + 2) (2^k)` at bit `((t + 2) + 2^(k+1)) - (r + 5) = (t + 2^(k+1)) - (r + 3)`. -/
theorem winWitt_scale_cross_zero_gap_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt (t + 2) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 3)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 3) = ((t + 2) + twopow (k + 1)) - (r + 5) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 2) k (r + 5) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_two_pin_r_plus_five_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt (t + 2) (twopow k)) ((t + twopow (k + 1)) - (r + 3)) = true :=
  winWitt_scale_cross_zero_gap_step_two_pin_r_plus_three_true_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-4 doubling 3-step Sector-2 window bit pinning `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false` on diagonal `z + 4` from a SINGLE `WinWittAgree t k 4 a L` at time `t` without `WinWittAgree (t + 1..3)`, `settle (z + 3)`, or `settle (z + 4)` (9.784)**:
translates `9.760` into `winWitt (t + 3) (2^k)` at bit `((t + 3) + 2^(k+1)) - (r + 5) = (t + 2^(k+1)) - (r + 2)`. -/
theorem winWitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt (t + 3) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 2) = ((t + 3) + twopow (k + 1)) - (r + 5) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 3) k (r + 5) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_three_pin_r_plus_five_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt (t + 3) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = false :=
  winWitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Exact 3-step same-bit negation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2))` at fixed bit index `(t + 2^(k+1)) - (r + 2)` from a SINGLE 3-bit `WinWittAgree t k 4 a L` at time `t` (9.785)**:
combines `9.784` (`(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = false`) with `9.683` (`(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true`). -/
theorem winWitt_scale_cross_zero_gap_same_bit_r_plus_two_flip_three_of_doubles_four_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 4) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 4) + r) + 2) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    (winWitt (t + 3) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_three_pin_r_plus_two_false_of_doubles_four_and_single_winWittAgree
      t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw,
    winWitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winWittAgree
      4 t k r a L (by clear ha hL; omega) (by clear ha hL; omega) hk hz (by clear ha hL; omega) ha (by omega) hw]
  rfl

theorem winWitt_scale_cross_zero_gap_same_bit_r_plus_two_flip_three_of_doubles_four_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 4 < r) (hk : ((t + 4) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 4) + r))
    (hd : DoublesAt 4 ((t + 4) + r))
    (hset0 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 4) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 4) + r) + 2) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k 4 a L) :
    wittBitBool (winWitt (t + 3) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2))) :=
  winWitt_scale_cross_zero_gap_same_bit_r_plus_two_flip_three_of_doubles_four_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Post-black reset diagonal `false` pinning `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = false` on `z + 3` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `settle (z + 3)` (9.786)**:
combines `9.748` (`lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = true` on `z + 1`) with the Post-Black Reset Identity `lhCenter_late_cross_reset_after_zero_diag t k (r + Q)` (`9.572`). -/
theorem lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (hset4 : settle ((t + r) + 4) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) = false := by
  have h1 := lhCenter_late_cross_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 (by clear ha hL; omega) hset4 ha hL hw
  have hres := lhCenter_late_cross_reset_after_zero_diag t k (r + Q)
    (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show t + (r + Q) = (t + Q) + r by clear ha hL; omega]; exact hz)
    (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by clear ha hL; omega]; exact hset2)
  rw [h1] at hres
  exact hres

theorem lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (hset4 : SettledBy ((t + r) + 4) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) = false :=
  lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-! ### Batch 33: General-`Q` Reset-Diagonal Same-Bit Negations, `(t + r) + 5` Zero-Diagonal Parity Cancellation, and Unconditional Single-Time Refutation `not_winWittAgree_five_of_doubles` (9.787–9.801) -/

/-- **Sector-2 window bit evaluation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = false` on the reset diagonal `z + 3` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `settle (z + 3)` (9.787)**:
translates `9.786` into `winWitt (t + 1) (2^k)` via `winWitt_testBit_scale_cross_zero_gap (t + 1) k ((r + Q) + 2)`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (hset4 : settle ((t + r) + 4) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) = false := by
  have hge := zero_diag_ge_two ((t + Q) + r) hz
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - ((r + Q) + 1) = ((t + 1) + twopow (k + 1)) - ((r + Q) + 2) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k ((r + Q) + 2) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (hset4 : SettledBy ((t + r) + 4) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) = false :=
  winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **1-step same-bit negation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 4` is a settled zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `settle (z + 3)` (9.788)**:
combines `9.787` (`= false` at `t + 1`) with `9.765` (`= true` at `t`). -/
theorem winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_four
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (hset4 : settle ((t + r) + 4) ≤ (t + 1) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_four
      Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw,
    winWitt_scale_cross_zero_gap_pin_doubling_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_four
      Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 (by clear ha hL; omega) hset4 ha hL hw]
  rfl

theorem winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_four_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk4 : (t + r) + 4 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz4 : IsZeroDiag ((t + r) + 4))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (hset4 : SettledBy ((t + r) + 4) ((t + 1) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1))) :=
  winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_four
    Q t k r a L hr hk hk4 hz hd hz4 hset0 hset1 hset2 hset4 ha hL hw

/-- **1-step same-bit negation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))` when `(t + Q) + r` is a doubling zero diagonal and `(t + r) + 3` is a settled zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `settle (z + 3)` (9.789)**:
combines `9.701` (`= true` at `t + 1`) with `9.699` (`= false` at `t`). -/
theorem winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  rw [winWitt_scale_cross_zero_gap_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
      Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw,
    winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three
      Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw]
  rfl

theorem winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1))) :=
  winWitt_scale_cross_zero_gap_step_one_same_bit_doubling_flip_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **1-step complementation `lhCenter ((t + 1) + 2^k) (2^k - (r + 3)) = !lhCenter (t + 2^k) (2^k - (r + 3))` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.790)**:
combines `9.676` (`lhCenter (t + 2^k) (2^k - (r + 2)) = true`) with the Twin Identity Before a Zero Diagonal (`9.592`, equating `r + 3` and `r + 4` before `(t + r) + 5`) in `lhCenter_late_cross_step t k (r + 1)`. -/
theorem lhCenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winWittAgree_and_zero_diag_five
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset5 : settle ((t + r) + 5) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) =
      !lhCenter (t + twopow k) (twopow k - (r + 3)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2 : lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
    lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
      Q t k r a L hr hk hz hset2 ha hL hw
  have htwin : lhCenter (t + twopow k) (twopow k - (r + 3)) =
      lhCenter (t + twopow k) (twopow k - (r + 4)) := by
    have ht := lhCenter_late_cross_twin_before_zero_diag t k (r + 3)
      (by clear ha hL; omega)
      (by rw [show (t + (r + 3)) + 2 = (t + r) + 5 by clear ha hL; omega]; exact hz5)
      (by rw [show (t + (r + 3)) + 2 = (t + r) + 5 by clear ha hL; omega]; exact hset5)
    rwa [show (r + 3) + 1 = r + 4 by clear ha hL; omega] at ht
  have hstep := lhCenter_late_cross_step t k (r + 1) (by clear ha hL; omega)
  rw [show (r + 1) + 2 = r + 3 by clear ha hL; omega,
    show (r + 1) + 1 = r + 2 by clear ha hL; omega,
    show (r + 1) + 3 = r + 4 by clear ha hL; omega,
    h2, ← htwin, Bool.or_self, bxor_eq_xor] at hstep
  rw [hstep]
  cases lhCenter (t + twopow k) (twopow k - (r + 3)) <;> rfl

theorem lhCenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winWittAgree_and_zero_diag_five_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset5 : SettledBy ((t + r) + 5) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) =
      !lhCenter (t + twopow k) (twopow k - (r + 3)) :=
  lhCenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset2 hset5 ha hL hw

/-- **Spatial stride-2 equality `lhCenter (t + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 3))` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.791)**:
at time `(t + 1) + 2^k`, the Twin Identity Before a Zero Diagonal (`9.592`) equates `2^k - (r + 2)` (`= !lhCenter (t + 2^k) (2^k - (r + 1))` by `9.677`) with `2^k - (r + 3)` (`= !lhCenter (t + 2^k) (2^k - (r + 3))` by `9.790`), canceling the two negations. -/
theorem lhCenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winWittAgree_and_zero_diag_five
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset5 : settle ((t + r) + 5) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) =
      lhCenter (t + twopow k) (twopow k - (r + 3)) := by
  have h12 := lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw
  have h13 := lhCenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset2 hset5 ha hL hw
  have htwin1 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) := by
    have ht := lhCenter_late_cross_twin_before_zero_diag (t + 1) k (r + 2)
      (by clear ha hL; omega)
      (by rw [show ((t + 1) + (r + 2)) + 2 = (t + r) + 5 by clear ha hL; omega]; exact hz5)
      (by rw [show ((t + 1) + (r + 2)) + 2 = (t + r) + 5 by clear ha hL; omega]; clear ha hL; omega)
    rwa [show (r + 2) + 1 = r + 3 by clear ha hL; omega] at ht
  rw [h12, h13] at htwin1
  revert htwin1
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases lhCenter (t + twopow k) (twopow k - (r + 3)) <;> decide

theorem lhCenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winWittAgree_and_zero_diag_five_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset5 : SettledBy ((t + r) + 5) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) =
      lhCenter (t + twopow k) (twopow k - (r + 3)) :=
  lhCenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset2 hset5 ha hL hw

/-- **2-step same-cell return `lhCenter ((t + 2) + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 1))` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1..2)` (9.792)**:
combining `9.679` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true`), the Twin Identity `9.592` at `t + 1` and `t + 2`, and `9.677` in `lhCenter_late_cross_step (t + 1) k r` cancels two consecutive negations (`!!x = x`). -/
theorem lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset5 : settle ((t + r) + 5) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 1)) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h1_1 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true :=
    lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
      Q t k r a L hr hk hz hset0 hset2 ha hL hw
  have h1_2 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) :=
    lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
      Q t k r a L (by clear ha hL; omega) hk hz hset2 ha (by omega) hw
  have htwin1 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) := by
    have ht := lhCenter_late_cross_twin_before_zero_diag (t + 1) k (r + 2)
      (by clear ha hL; omega)
      (by rw [show ((t + 1) + (r + 2)) + 2 = (t + r) + 5 by clear ha hL; omega]; exact hz5)
      (by rw [show ((t + 1) + (r + 2)) + 2 = (t + r) + 5 by clear ha hL; omega]; clear ha hL; omega)
    rwa [show (r + 2) + 1 = r + 3 by clear ha hL; omega] at ht
  have htwin2 : lhCenter ((t + 2) + twopow k) (twopow k - (r + 1)) =
      lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) := by
    have ht := lhCenter_late_cross_twin_before_zero_diag (t + 2) k (r + 1)
      (by clear ha hL; omega)
      (by rw [show ((t + 2) + (r + 1)) + 2 = (t + r) + 5 by clear ha hL; omega]; exact hz5)
      (by rw [show ((t + 2) + (r + 1)) + 2 = (t + r) + 5 by clear ha hL; omega]; clear ha hL; omega)
    rwa [show (r + 1) + 1 = r + 2 by clear ha hL; omega] at ht
  have hstep := lhCenter_late_cross_step (t + 1) k r (by clear ha hL; omega)
  rw [show (t + 1) + 1 = t + 2 by clear ha hL; omega,
    h1_1, ← htwin1, Bool.or_self, h1_2, bxor_eq_xor] at hstep
  rw [htwin2, hstep]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> rfl

theorem lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset5 : SettledBy ((t + r) + 5) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 1)) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

/-- **Self-canceling parity pinning `lhCenter (t + 2^k) (2^k - (r - 1)) = true` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1..2)` (9.793)**:
combining `9.792` (`lhCenter ((t + 2) + 2^k) (2^k - (r + 1)) = B`), `9.679` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true`, which forces `lhCenter ((t + 2) + 2^k) (2^k - (r + 1)) = !lhCenter ((t + 1) + 2^k) (2^k - r)`), and `9.675` (`lhCenter (t + 2^k) (2^k - r) = false`, which forces `lhCenter ((t + 1) + 2^k) (2^k - r) = A ⊕ B` for `A = lhCenter (t + 2^k) (2^k - (r - 1))`) yields the self-canceling parity equation `B = !(A ⊕ B)`, pinning `A = true` unconditionally! -/
theorem lhCenter_late_cross_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset5 : settle ((t + r) + 5) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r - 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h0 : lhCenter (t + twopow k) (twopow k - r) = false :=
    lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
      Q t k r a L hr (by clear ha hL; omega) hz hset0 (by omega) hL hw
  have h1_1 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true :=
    lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
      Q t k r a L hr hk hz hset0 hset2 ha hL hw
  have h2_1 : lhCenter ((t + 2) + twopow k) (twopow k - (r + 1)) =
      lhCenter (t + twopow k) (twopow k - (r + 1)) :=
    lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five
      Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw
  have hstep1 := lhCenter_step_succ ((t + 1) + twopow k) (twopow k - (r + 2))
  rw [show ((t + 1) + twopow k) + 1 = (t + 2) + twopow k by clear ha hL; omega,
    show (twopow k - (r + 2)) + 1 = twopow k - (r + 1) by clear ha hL; omega,
    show (twopow k - (r + 2)) + 2 = twopow k - r by clear ha hL; omega,
    h1_1, Bool.true_or, h2_1] at hstep1
  have hstep0 := lhCenter_step_succ (t + twopow k) (twopow k - (r + 1))
  rw [show (t + twopow k) + 1 = (t + 1) + twopow k by clear ha hL; omega,
    show (twopow k - (r + 1)) + 1 = twopow k - r by clear ha hL; omega,
    show (twopow k - (r + 1)) + 2 = twopow k - (r - 1) by clear ha hL; omega,
    h0, Bool.false_or] at hstep0
  rw [hstep0] at hstep1
  revert hstep1
  cases lhCenter (t + twopow k) (twopow k - (r - 1)) <;>
    cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> decide

theorem lhCenter_late_cross_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset5 : SettledBy ((t + r) + 5) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r - 1)) = true :=
  lhCenter_late_cross_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

/-- **Period-5 doubling `true` pinning `lhCenter (t + 2^k) (2^k - (r + 4)) = true` on `z - 1` across ANY period-5 doubling zero diagonal `z = (t + 5) + r` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.794)**:
for `Q = 5`, `(t + 5) + r = (t + r) + 5`, so `9.793` pins `lhCenter (t + 2^k) (2^k - (r - 1)) = true`, which below-threshold spatial 5-periodicity `lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap 5 ((t + 5) + r) t k (r - 1) a L` (`9.673`) transports by `+ 5` to `(r - 1) + 5 = r + 4` on `z - 1 = (t + 4) + r`. -/
theorem lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 4)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hsub1 : lhCenter (t + twopow k) (twopow k - (r - 1)) = true :=
    lhCenter_late_cross_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
      5 t k r a L (by clear ha hL; omega) hk (by clear ha hL; omega) hz
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by clear ha hL; omega) hset2
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hset0)
      ha (by omega) hw
  have hsh := lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap
    5 ((t + 5) + r) t k (r - 1) a L
    (by clear ha hL; omega) (by clear ha hL; omega) (by clear ha hL; omega) hd
    (by rw [show (t + 5) + (r - 1) = (t + 4) + r by clear ha hL; omega]; exact hset_m1)
    (by omega) hL hw
  rw [show (r - 1) + 5 = r + 4 by clear ha hL; omega, hsub1] at hsh
  exact hsh.symm

theorem lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 4)) = true :=
  lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling `true` pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on `z - 2` across ANY period-5 doubling zero diagonal `z = (t + 5) + r` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.795)**:
combines `9.794` (`lhCenter (t + 2^k) (2^k - (r + 4)) = true`) with the Twin Identity Before a Zero Diagonal (`9.592`) at time `t`. -/
theorem lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k (r + 3)
    (by clear ha hL; omega)
    (by rw [show (t + (r + 3)) + 2 = (t + 5) + r by clear ha hL; omega]; exact hz)
    (by rw [show (t + (r + 3)) + 2 = (t + 5) + r by clear ha hL; omega]; exact hset0)
  rw [show (r + 3) + 1 = r + 4 by clear ha hL; omega] at htwin
  rw [htwin]
  exact lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

theorem lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling `true` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` on `z - 4` across ANY period-5 doubling zero diagonal `z = (t + 5) + r` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.796)**:
combines `9.795` (`lhCenter (t + 2^k) (2^k - (r + 3)) = true`) with the stride-2 equality `9.791` (`Q = 5`). -/
theorem lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [lhCenter_late_cross_eq_r_plus_one_r_plus_three_of_single_winWittAgree_and_zero_diag_five
    5 t k r a L (by clear ha hL; omega) hk (by clear ha hL; omega) hz
    (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hz)
    hset2
    (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hset0)
    ha (by omega) hw]
  exact lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

theorem lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling diagonal `false` pinning `lhCenter (t + 2^k) (2^k - (r + 6)) = false` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.797)**:
combines `9.796` (`lhCenter (t + 2^k) (2^k - (r + 1)) = true`) with the single-time doubling spatial 5-flip `lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap 5 t k r a L` (`9.636`). -/
theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 6)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h1 := lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    5 t k r a L (by clear ha hL; omega) (by clear ha hL; omega) hz hd hset1 (by omega) (by omega) hw
  rw [show (r + 5) + 1 = r + 6 by clear ha hL; omega, h1] at hflip
  revert hflip
  cases lhCenter (t + twopow k) (twopow k - (r + 6)) <;> decide

theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 6)) = false :=
  lhCenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 1-step `true` pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 5)) = true` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.798)**:
in `lhCenter_late_cross_step t k (r + 3)`, left `2^k - (r + 4) = true` (`9.794`, on `z - 1`), center `2^k - (r + 5) = false` (on `z`), and right `2^k - (r + 6) = false` (`9.797`, on `z + 1`), yielding `true ⊕ (false || false) = true`. -/
theorem lhCenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 5)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h4 := lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw
  have h5 : lhCenter (t + twopow k) (twopow k - (r + 5)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 5) (by clear ha hL; omega)
      (by rw [show t + (r + 5) = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by rw [show t + (r + 5) = (t + 5) + r by clear ha hL; omega]; exact hset0)
  have h6 := lhCenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step t k (r + 3) (by clear ha hL; omega)
  rw [show (r + 3) + 2 = r + 5 by clear ha hL; omega,
    show (r + 3) + 1 = r + 4 by clear ha hL; omega,
    show (r + 3) + 3 = r + 6 by clear ha hL; omega,
    h4, h5, h6] at hstep
  exact hstep

theorem lhCenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 5)) = true :=
  lhCenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 4)) = true` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.799)**:
in `lhCenter_late_cross_step (t + 1) k (r + 2)`, left `2^k - (r + 3) = false` (`9.790` + `9.795`, on `z - 1`), center `2^k - (r + 4) = false` (on `z`), and right `2^k - (r + 5) = true` (`9.798`, on `z + 1`), yielding `false ⊕ (false || true) = true`. -/
theorem lhCenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 4)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h3_0 := lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw
  have h3_1 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 3)) = false := by
    have hnot := lhCenter_late_cross_step_one_at_shift_plus_three_eq_not_of_single_winWittAgree_and_zero_diag_five
      5 t k r a L (by clear ha hL; omega) hk (by clear ha hL; omega) hz
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hz)
      hset2
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hset0)
      ha (by omega) hw
    rw [h3_0] at hnot
    exact hnot
  have h4_1 : lhCenter ((t + 1) + twopow k) (twopow k - (r + 4)) = false :=
    lhCenter_late_cross_of_zero_diag (t + 1) k (r + 4) (by clear ha hL; omega)
      (by rw [show (t + 1) + (r + 4) = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by rw [show (t + 1) + (r + 4) = (t + 5) + r by clear ha hL; omega]; clear ha hL; omega)
  have h5_1 := lhCenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step (t + 1) k (r + 2) (by clear ha hL; omega)
  rw [show (t + 1) + 1 = t + 2 by clear ha hL; omega,
    show (r + 2) + 2 = r + 4 by clear ha hL; omega,
    show (r + 2) + 1 = r + 3 by clear ha hL; omega,
    show (r + 2) + 3 = r + 5 by clear ha hL; omega,
    h3_1, h4_1, h5_1] at hstep
  exact hstep

theorem lhCenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 4)) = true :=
  lhCenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 3-step `false` pinning `lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = false` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.800)**:
in `lhCenter_late_cross_step (t + 2) k (r + 1)`, left `2^k - (r + 2) = true` (`9.792` + `9.796` + `9.592`, on `z - 1`), center `2^k - (r + 3) = false` (on `z`), and right `2^k - (r + 4) = true` (`9.799`, on `z + 1`), yielding `true ⊕ (false || true) = false`. -/
theorem lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 3)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h1_0 := lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw
  have h1_2 : lhCenter ((t + 2) + twopow k) (twopow k - (r + 1)) = true := by
    rw [lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five
      5 t k r a L (by clear ha hL; omega) hk (by clear ha hL; omega) hz
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by clear ha hL; omega) hset2
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hset0)
      ha (by omega) hw]
    exact h1_0
  have h2_2 : lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = true := by
    have htwin := lhCenter_late_cross_twin_before_zero_diag (t + 2) k (r + 1)
      (by clear ha hL; omega)
      (by rw [show ((t + 2) + (r + 1)) + 2 = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by rw [show ((t + 2) + (r + 1)) + 2 = (t + 5) + r by clear ha hL; omega]; clear ha hL; omega)
    rw [show (r + 1) + 1 = r + 2 by clear ha hL; omega] at htwin
    rw [← htwin]
    exact h1_2
  have h3_2 : lhCenter ((t + 2) + twopow k) (twopow k - (r + 3)) = false :=
    lhCenter_late_cross_of_zero_diag (t + 2) k (r + 3) (by clear ha hL; omega)
      (by rw [show (t + 2) + (r + 3) = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by rw [show (t + 2) + (r + 3) = (t + 5) + r by clear ha hL; omega]; clear ha hL; omega)
  have h4_2 := lhCenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw
  have hstep := lhCenter_late_cross_step (t + 2) k (r + 1) (by clear ha hL; omega)
  rw [show (t + 2) + 1 = t + 3 by clear ha hL; omega,
    show (r + 1) + 2 = r + 3 by clear ha hL; omega,
    show (r + 1) + 1 = r + 2 by clear ha hL; omega,
    show (r + 1) + 3 = r + 4 by clear ha hL; omega,
    h2_2, h3_2, h4_2] at hstep
  exact hstep

theorem lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 3) + twopow k) (twopow k - (r + 3)) = false :=
  lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Unconditional single-time refutation `¬ WinWittAgree t k 5 a L` across ANY period-5 doubling zero diagonal `z = (t + 5) + r` without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)` (9.801)**:
applying the 2-step post-zero reset-and-absorption law `lhCenter_late_cross_two_step_absorb_false_after_zero_diag (t + 3) k (r + 2)` (`9.758`) to `9.800` (`lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = false` on `z + 1`) pins `lhCenter ((t + 5) + 2^k) (2^k - (r + 4)) = false` on `z + 4`, whereas `9.794` pins `lhCenter (t + 2^k) (2^k - (r + 4)) = true` on `z - 1`, contradicting `lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k 5 (r + 4) a L` (`9.632`). -/
theorem not_winWittAgree_five_of_doubles
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 4))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L) :
    ¬ WinWittAgree t k 5 a L := by
  intro hw
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h3 := lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 (by clear ha hL; omega) (by omega) hL hw
  have h5_false : lhCenter ((t + 5) + twopow k) (twopow k - (r + 4)) = false := by
    have habs := lhCenter_late_cross_two_step_absorb_false_after_zero_diag (t + 3) k (r + 2)
      (by rw [show ((t + 3) + (r + 2)) + 2 = ((t + 5) + r) + 2 by clear ha hL; omega]; exact hk)
      (by rw [show (t + 3) + (r + 2) = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by rw [show ((t + 3) + (r + 2)) + 2 = ((t + 5) + r) + 2 by clear ha hL; omega]; exact hset2)
      (by rw [show (r + 2) + 1 = r + 3 by clear ha hL; omega]; exact h3)
    rwa [show (t + 3) + 2 = t + 5 by clear ha hL; omega,
      show (r + 2) + 2 = r + 4 by clear ha hL; omega] at habs
  have h0_true := lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 (by clear ha hL; omega) (by omega) hL hw
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k 5 (r + 4) a L
    (by clear ha hL; omega) (by clear ha hL; omega) ha (by omega) hw
  rw [h5_false, h0_true] at heq
  exact Bool.noConfusion heq

theorem not_winWittAgree_five_of_doubles_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 4))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L) :
    ¬ WinWittAgree t k 5 a L :=
  not_winWittAgree_five_of_doubles
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL

/-! ### Batch 34: Period-5 Post-Zero Reset/Absorption Steps 4–5 and Sector-2 Window Bit Pinning Across `t .. t + 5` (9.802–9.816) -/

/-- **Period-5 doubling 4-step `true` pinning `lhCenter ((t + 4) + 2^k) (2^k - (r + 4)) = true` on `z + 3` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` or `settle (z + 3)` (9.802)**:
combines `9.800` (`lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = false` on `z + 1`) with the Post-Black Reset Identity `lhCenter_late_cross_reset_after_zero_diag (t + 3) k (r + 2)` (`9.572`). -/
theorem lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 4) + twopow k) (twopow k - (r + 4)) = true := by
  have h3 := lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 (by clear ha hL; omega) ha hL hw
  have hres := lhCenter_late_cross_reset_after_zero_diag (t + 3) k (r + 2)
    (by rw [show ((t + 3) + (r + 2)) + 2 = ((t + 5) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 3) + (r + 2) = (t + 5) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 3) + (r + 2)) + 2 = ((t + 5) + r) + 2 by clear ha hL; omega]; exact hset2)
  rw [show (t + 3) + 1 = t + 4 by clear ha hL; omega,
    show (r + 2) + 2 = r + 4 by clear ha hL; omega,
    show (r + 2) + 1 = r + 3 by clear ha hL; omega,
    h3] at hres
  exact hres

theorem lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 4) + twopow k) (twopow k - (r + 4)) = true :=
  lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 5-step `false` pinning `lhCenter ((t + 5) + 2^k) (2^k - (r + 4)) = false` on `z + 4` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)` (9.803)**:
applies the 2-step post-zero reset-and-absorption law `lhCenter_late_cross_two_step_absorb_false_after_zero_diag (t + 3) k (r + 2)` (`9.758`) to `9.800` (`lhCenter ((t + 3) + 2^k) (2^k - (r + 3)) = false` on `z + 1`). -/
theorem lhCenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 5) + twopow k) (twopow k - (r + 4)) = false := by
  have h3 := lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 (by clear ha hL; omega) ha hL hw
  have habs := lhCenter_late_cross_two_step_absorb_false_after_zero_diag (t + 3) k (r + 2)
    (by rw [show ((t + 3) + (r + 2)) + 2 = ((t + 5) + r) + 2 by clear ha hL; omega]; exact hk)
    (by rw [show (t + 3) + (r + 2) = (t + 5) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 3) + (r + 2)) + 2 = ((t + 5) + r) + 2 by clear ha hL; omega]; exact hset2)
    (by rw [show (r + 2) + 1 = r + 3 by clear ha hL; omega]; exact h3)
  rwa [show (t + 3) + 2 = t + 5 by clear ha hL; omega,
    show (r + 2) + 2 = r + 4 by clear ha hL; omega] at habs

theorem lhCenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 5) + twopow k) (twopow k - (r + 4)) = false :=
  lhCenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = true` when `(t + Q) + r` and `(t + r) + 5` are settled zero diagonals from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1..2)` (9.804)**:
translates `9.793` into `winWitt t (2^k)` via `winWitt_testBit_scale_cross_zero_gap t k (r - 1)`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
    (Q t k r a L : Nat)
    (hr : (t + Q) + 1 < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (hset5 : settle ((t + r) + 5) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r - 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r - 1) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L (by clear ha hL; omega) hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five_prop
    (Q t k r a L : Nat)
    (hr : (t + Q) + 1 < r) (hk : ((t + Q) + r) + 2 ≤ k) (hk5 : (t + r) + 5 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz5 : IsZeroDiag ((t + r) + 5))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (hset5 : SettledBy ((t + r) + 5) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r - 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
    Q t k r a L hr hk hk5 hz hz5 hset0 hset2 hset5 ha hL hw

/-- **Period-5 doubling Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = true` on `z - 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.805)**:
translates `9.794` into `winWitt t (2^k)` via `winWitt_testBit_scale_cross_zero_gap t k (r + 4)`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 4)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_r_plus_four_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 4)) = true :=
  winWitt_scale_cross_zero_gap_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3)) = true` on `z - 2` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.806)**:
translates `9.795` into `winWitt t (2^k)` via `winWitt_testBit_scale_cross_zero_gap t k (r + 3)`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 3)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 3) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_r_plus_three_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 3)) = true :=
  winWitt_scale_cross_zero_gap_pin_r_plus_three_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = true` on `z - 4` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.807)**:
translates `9.796` into `winWitt t (2^k)` via `winWitt_testBit_scale_cross_zero_gap t k (r + 1)`. -/
theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 1) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_r_plus_one_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) = true :=
  winWitt_scale_cross_zero_gap_pin_r_plus_one_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling diagonal Sector-2 window bit evaluation `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 6)) = false` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.808)**:
translates `9.797` into `winWitt t (2^k)` via `winWitt_testBit_scale_cross_zero_gap t k (r + 6)`. -/
theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 6)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 6) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 6)) = false :=
  winWitt_scale_cross_zero_gap_pin_doubling_diag_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 1-step Sector-2 window bit evaluation `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 4)) = true` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.809)**:
translates `9.798` into `winWitt (t + 1) (2^k)` at bit `((t + 1) + 2^(k+1)) - (r + 5) = (t + 2^(k+1)) - (r + 4)`. -/
theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 4)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 4) = ((t + 1) + twopow (k + 1)) - (r + 5) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 5) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_one_pin_r_plus_five_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 4)) = true :=
  winWitt_scale_cross_zero_gap_step_one_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 2-step Sector-2 window bit evaluation `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.810)**:
translates `9.799` into `winWitt (t + 2) (2^k)` at bit `((t + 2) + 2^(k+1)) - (r + 4) = (t + 2^(k+1)) - (r + 2)`. -/
theorem winWitt_scale_cross_zero_gap_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 2) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 2) = ((t + 2) + twopow (k + 1)) - (r + 4) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 2) k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_two_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 2) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_scale_cross_zero_gap_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 3-step Sector-2 window bit evaluation `(winWitt (t + 3) (2^k)).testBit ((t + 2^(k+1)) - r) = false` on `z + 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.811)**:
translates `9.800` into `winWitt (t + 3) (2^k)` at bit `((t + 3) + 2^(k+1)) - (r + 3) = (t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_step_three_pin_r_false_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 3) (twopow k)).testBit ((t + twopow (k + 1)) - r) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 3) + twopow (k + 1)) - (r + 3) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 3) k (r + 3) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_three_pin_r_plus_three_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_three_pin_r_false_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 3) (twopow k)) ((t + twopow (k + 1)) - r) = false :=
  winWitt_scale_cross_zero_gap_step_three_pin_r_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 4-step Sector-2 window bit evaluation `(winWitt (t + 4) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on `z + 3` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` or `settle (z + 3)` (9.812)**:
translates `9.802` into `winWitt (t + 4) (2^k)` at bit `((t + 4) + 2^(k+1)) - (r + 4) = (t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 4) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 4) + twopow (k + 1)) - (r + 4) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 4) k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_four_pin_r_plus_four_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 4) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_scale_cross_zero_gap_step_four_pin_r_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 5-step Sector-2 window bit evaluation `(winWitt (t + 5) (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = false` on `z + 4` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)` (9.813)**:
translates `9.803` into `winWitt (t + 5) (2^k)` at bit `((t + 5) + 2^(k+1)) - (r + 4) = (t + 2^(k+1)) - (r - 1)`. -/
theorem winWitt_scale_cross_zero_gap_step_five_pin_r_sub_one_false_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 5) (twopow k)).testBit ((t + twopow (k + 1)) - (r - 1)) = false := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r - 1) = ((t + 5) + twopow (k + 1)) - (r + 4) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 5) k (r + 4) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_five_pin_r_plus_four_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_five_pin_r_sub_one_false_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 5) (twopow k)) ((t + twopow (k + 1)) - (r - 1)) = false :=
  winWitt_scale_cross_zero_gap_step_five_pin_r_sub_one_false_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

/-- **Period-5 doubling 2-step `true` pinning `lhCenter ((t + 2) + 2^k) (2^k - (r + 2)) = true` on `z - 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.814)**:
combines the 2-step return `9.792` (`lhCenter ((t + 2) + 2^k) (2^k - (r + 1)) = lhCenter (t + 2^k) (2^k - (r + 1))`), `9.796` (`lhCenter (t + 2^k) (2^k - (r + 1)) = true`), and the Twin Identity Before a Zero Diagonal (`9.592`) at time `t + 2`. -/
theorem lhCenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h1_0 := lhCenter_late_cross_pin_r_plus_one_true_of_zero_diag_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw
  have h1_2 : lhCenter ((t + 2) + twopow k) (twopow k - (r + 1)) = true := by
    rw [lhCenter_late_cross_step_two_eq_r_plus_one_of_single_winWittAgree_and_zero_diag_five
      5 t k r a L (by clear ha hL; omega) hk (by clear ha hL; omega) hz
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by clear ha hL; omega) hset2
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hset0)
      ha (by omega) hw]
    exact h1_0
  have htwin := lhCenter_late_cross_twin_before_zero_diag (t + 2) k (r + 1)
    (by clear ha hL; omega)
    (by rw [show ((t + 2) + (r + 1)) + 2 = (t + 5) + r by clear ha hL; omega]; exact hz)
    (by rw [show ((t + 2) + (r + 1)) + 2 = (t + 5) + r by clear ha hL; omega]; clear ha hL; omega)
  rw [show (r + 1) + 1 = r + 2 by clear ha hL; omega] at htwin
  rw [← htwin]
  exact h1_2

theorem lhCenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    lhCenter ((t + 2) + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Period-5 doubling 2-step Sector-2 window bit evaluation `(winWitt (t + 2) (2^k)).testBit ((t + 2^(k+1)) - r) = true` on `z - 1` from a SINGLE `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)` (9.815)**:
translates `9.814` into `winWitt (t + 2) (2^k)` at bit `((t + 2) + 2^(k+1)) - (r + 2) = (t + 2^(k+1)) - r`. -/
theorem winWitt_scale_cross_zero_gap_step_two_pin_r_true_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 5) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 2) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 2) + twopow (k + 1)) - (r + 2) by clear ha hL; omega,
    winWitt_testBit_scale_cross_zero_gap (t + 2) k (r + 2) (by clear ha hL; omega) (by clear ha hL; omega)]
  exact lhCenter_late_cross_step_two_pin_r_plus_two_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_two_pin_r_true_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 5) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 2) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_scale_cross_zero_gap_step_two_pin_r_true_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset2 ha hL hw

/-- **Exact 5-step same-bit negation `(winWitt (t + 5) (2^k)).testBit ((t + 2^(k+1)) - (r - 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r - 1))` at fixed bit index `(t + 2^(k+1)) - (r - 1)` from a SINGLE 4-bit `WinWittAgree t k 5 a L` at time `t` without `WinWittAgree (t + 1..4)`, `settle (z + 3)`, or `settle (z + 4)` (9.816)**:
combines `9.813` (`= false` at `t + 5`) with `9.804` (`= true` at `t`). -/
theorem winWitt_scale_cross_zero_gap_same_bit_r_sub_one_flip_five_of_doubles_five_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : settle ((t + 4) + r) ≤ t + twopow k)
    (hset0 : settle ((t + 5) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 5) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 5) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    (winWitt (t + 5) (twopow k)).testBit ((t + twopow (k + 1)) - (r - 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r - 1)) := by
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by clear ha hL; omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_five_pin_r_sub_one_false_of_doubles_five_and_single_winWittAgree
      t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw,
    winWitt_scale_cross_zero_gap_pin_r_sub_one_true_of_single_winWittAgree_and_zero_diag_five
      5 t k r a L (by clear ha hL; omega) hk (by clear ha hL; omega) hz
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hz)
      (by clear ha hL; omega) (by clear ha hL; omega)
      (by rw [show (t + r) + 5 = (t + 5) + r by clear ha hL; omega]; exact hset0)
      ha (by omega) hw]
  rfl

theorem winWitt_scale_cross_zero_gap_same_bit_r_sub_one_flip_five_of_doubles_five_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 6 < r) (hk : ((t + 5) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 5) + r))
    (hd : DoublesAt 5 ((t + 5) + r))
    (hset_m1 : SettledBy ((t + 4) + r) (t + twopow k))
    (hset0 : SettledBy ((t + 5) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 5) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 5) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r - 1) ≤ a + L)
    (hw : WinWittAgree t k 5 a L) :
    wittBitBool (winWitt (t + 5) (twopow k)) ((t + twopow (k + 1)) - (r - 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r - 1))) :=
  winWitt_scale_cross_zero_gap_same_bit_r_sub_one_flip_five_of_doubles_five_and_single_winWittAgree
    t k r a L hr hk hz hd hset_m1 hset0 hset1 hset2 ha hL hw

end Rule30UOR.Interfaces
