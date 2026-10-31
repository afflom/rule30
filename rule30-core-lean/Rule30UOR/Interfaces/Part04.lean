module

public import Rule30UOR.Interfaces.Part03

/-!
# `Rule30UOR.Interfaces`, part 4

* The Frobenius Defect `δ_k` and the Window Step Outside the Cone
* Tying the Single-Cell Seed In-Cone Laws (`R_periodic` and `δ_k = 0`) to the Three Targets
* In-Cone Seed Laws (`restart`, `R_periodic`, `frobDefect = 0`), Sector-2 Wronskian of `winWitt`, and Target Refutations
* Paper-facing wrappers for Theorems 9.225–9.242
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

/-! ### The Frobenius Defect `δ_k` and the Window Step Outside the Cone -/

/-- **The Frobenius Defect `δ_k(y)` (`frobDefect k y`)**:
    `δ_k(y) = carry(scale_k y) ⊕ scale_k(carry y)` measures the failure of the nonlinear carry map `carry` to commute with the Frobenius scale operator `phiScale k`. Inside the light cone (`2 * t0 + 1 < 2^k`) on `row t0`, `frobDefect k (row t0) = 0` because the three shifted copies of `row t0` do not overlap; outside the cone (`2^k ≤ t0`), `frobDefect k (row t0)` is a sum of pairwise products of cells of `row t0` that are `2^k` or `2^(k+1)` apart. -/
def frobDefect (k y : Nat) : Nat :=
  carry (phiScale k y) ^^^ phiScale k (carry y)

/-- Paper-facing predicate asserting that bit `j` of `frobDefect k y` equals `bton b`. -/
def BitFrobDefectEq (k y j : Nat) (b : Bool) : Prop :=
  bit (frobDefect k y) j = bton b

/-- **In-Cone Vanishing of the Frobenius Defect (`frobDefect_row_cone_eq_zero`)**: inside the light cone (`2 * t0 + 1 < 2^k`), the scaled copies of `row t0` do not overlap, so `frobDefect k (row t0) = 0`. -/
theorem frobDefect_row_cone_eq_zero (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    frobDefect k (row t0) = 0 := by
  unfold frobDefect
  rw [carry_phiScale_row_cone t0 k hcone, Nat.xor_self]

/-- **Universal Window Step Equation with the Frobenius Defect (`winWitt_step_frobDefect`)**:
    at EVERY base time `t0` and scale `k` (inside OR outside the light cone!),
    `win(t0 + 1, 2^k) = Φ(w) ⊕ ↑crosscarry(S r, w) ⊕ ↑δ_k(r)`,
    where `w = win(t0, 2^k)`, `r = row(t0)`, `S = phiScale k`, and `δ_k = frobDefect k`. -/
theorem winWitt_step_frobDefect (t0 k : Nat) :
    winWitt (t0 + 1) (twopow k) =
      (phi (winWitt t0 (twopow k)) ^^^
        (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) <<< 1)) ^^^
        (frobDefect k (row t0) <<< 1) := by
  have hb := winWitt_base_step t0 k
  have hc : carry (row (t0 + twopow k)) =
      (carry (phiScale k (row t0)) ^^^ carry (winWitt t0 (twopow k))) ^^^
        crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) := by
    rw [row_scale t0 k, carry_xor]
  have hp : phi (winWitt t0 (twopow k)) =
      phiLinear (winWitt t0 (twopow k)) ^^^ (carry (winWitt t0 (twopow k)) <<< 1) :=
    Rule30UOR.Core.phi_split (winWitt t0 (twopow k))
  unfold frobDefect
  rw [hb, hc, hp]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases (phiLinear (winWitt t0 (twopow k))).testBit i <;>
    cases decide (i ≥ 1) <;>
    cases (carry (phiScale k (row t0))).testBit (i - 1) <;>
    cases (phiScale k (carry (row t0))).testBit (i - 1) <;>
    cases (carry (winWitt t0 (twopow k))).testBit (i - 1) <;>
    cases (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (i - 1) <;> rfl

/-- **Bitwise Universal Window Step at Bit `j + 1` (`winWitt_step_frobDefect_testBit_succ`)**:
    for all `t0, k, j : Nat`, bit `j + 1` of `winWitt (t0 + 1) (2^k)` equals bit `j + 1` of `phi (winWitt t0 (2^k))` XORed with bit `j` of `crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))` and bit `j` of `frobDefect k (row t0)`. -/
theorem winWitt_step_frobDefect_testBit_succ (t0 k j : Nat) :
    (winWitt (t0 + 1) (twopow k)).testBit (j + 1) =
      bxor (bxor ((phi (winWitt t0 (twopow k))).testBit (j + 1))
        ((crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit j))
        ((frobDefect k (row t0)).testBit j) := by
  have hs := congrArg (fun n => n.testBit (j + 1)) (winWitt_step_frobDefect t0 k)
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft,
    show decide (j + 1 ≥ 1) = true from decide_eq_true (by omega),
    Bool.true_and, Nat.add_sub_cancel] at hs
  rw [hs, bxor_eq_xor, bxor_eq_xor]

/-- **General Outside-the-Cone Bit Readout of `frobDefect k (row t0)` at `(r + 1) + 2^k` (`frobDefect_row_testBit_outside_cone`)**:
    for fixed `k` and all `r ≥ 2^k` (outside the light cone), the three diagonal self-carry terms cancel between `carry (phiScale k (row t0))` and `phiScale k (carry (row t0))`, leaving the exact sum of products of cells of `row t0` at distance `2^k` and `2^(k+1)` apart! -/
theorem frobDefect_row_testBit_outside_cone (t0 k r : Nat) (hr : twopow k ≤ r) :
    (frobDefect k (row t0)).testBit ((r + 1) + twopow k) =
      bxor (bxor
        (rdiag ((r + 1) + twopow k) t0 &&
          bxor (rdiag r t0) (rdiag (r - twopow k) t0))
        (rdiag (r + 1) t0 &&
          bxor (rdiag (r + twopow k) t0) (rdiag (r - twopow k) t0)))
        (rdiag ((r + 1) - twopow k) t0 &&
          bxor (rdiag (r + twopow k) t0) (rdiag r t0)) := by
  have hc1 : (carry (phiScale k (row t0))).testBit ((r + 1) + twopow k) =
      ((phiScale k (row t0)).testBit ((r + 1) + twopow k) &&
        (phiScale k (row t0)).testBit (r + twopow k)) := by
    have h0 := carry_testBit_succ (phiScale k (row t0)) (r + twopow k)
    rw [show (r + twopow k) + 1 = (r + 1) + twopow k by omega] at h0
    exact h0
  rw [phiScale_row_testBit_outside_cone t0 k (r + 1) (by omega),
    phiScale_row_testBit_outside_cone t0 k r hr] at hc1
  have hc2 : (phiScale k (carry (row t0))).testBit ((r + 1) + twopow k) =
      bxor (bxor
        (rdiag ((r + 1) + twopow k) t0 && rdiag (r + twopow k) t0)
        (rdiag (r + 1) t0 && rdiag r t0))
        (rdiag ((r + 1) - twopow k) t0 && rdiag (r - twopow k) t0) := by
    change (((carry (row t0)) ^^^ ((carry (row t0)) <<< twopow k)) ^^^
        ((carry (row t0)) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, bxor_eq_xor]
    have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    have hb1 : (carry (row t0)).testBit ((r + 1) + twopow k) =
        (rdiag ((r + 1) + twopow k) t0 && rdiag (r + twopow k) t0) := by
      have h0 := carry_testBit_succ (row t0) (r + twopow k)
      rw [show (r + twopow k) + 1 = (r + 1) + twopow k by omega,
        row_testBit t0 ((r + 1) + twopow k), row_testBit t0 (r + twopow k)] at h0
      exact h0
    have hb2 : (carry (row t0)).testBit (r + 1) =
        (rdiag (r + 1) t0 && rdiag r t0) := by
      rw [carry_testBit_succ (row t0) r, row_testBit t0 (r + 1), row_testBit t0 r]
    have hb3 : (carry (row t0)).testBit ((r + 1) - twopow k) =
        (rdiag ((r + 1) - twopow k) t0 && rdiag (r - twopow k) t0) := by
      have h0 := carry_testBit_succ (row t0) (r - twopow k)
      rw [show (r - twopow k) + 1 = (r + 1) - twopow k by omega,
        row_testBit t0 ((r + 1) - twopow k), row_testBit t0 (r - twopow k)] at h0
      exact h0
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow k - twopow k = r + 1 by omega,
      show (r + 1) + twopow k - (twopow k + twopow k) = (r + 1) - twopow k by omega,
      hb1, hb2, hb3]
  unfold frobDefect
  rw [Nat.testBit_xor, hc1, hc2]
  simp only [bxor_eq_xor]
  cases rdiag ((r + 1) + twopow k) t0 <;>
    cases rdiag (r + 1) t0 <;>
    cases rdiag ((r + 1) - twopow k) t0 <;>
    cases rdiag (r + twopow k) t0 <;>
    cases rdiag r t0 <;>
    cases rdiag (r - twopow k) t0 <;> rfl

/-- **Frobenius Defect `δ_k` at the Center Slot `(s + 1) + 2^k` Outside the Cone (`frobDefect_row_center_slot_outside_cone`)**:
    for fixed `k` and all `s ≥ 2^k` (with NO upper bound on `s`), at time `t0 = s + 1`, the center slot `(s + 1) + 2^k` of `frobDefect k (row (s + 1))` (which shifts under `↑` to the center bit `(s + 2) + 2^k` of `winWitt (s + 2) (2^k)`) is the 3-term sum of products of cells of `row (s + 1)` at distance `2^k` and `2^(k+1)` apart! -/
theorem frobDefect_row_center_slot_outside_cone (s k : Nat) (hs : twopow k ≤ s) :
    (frobDefect k (row (s + 1))).testBit ((s + 1) + twopow k) =
      bxor (bxor
        (ldiag ((s + 1) - twopow k) (s + 1) &&
          bxor (rdiag s (s + 1)) (rdiag (s - twopow k) (s + 1)))
        (Rule30UOR.Core.center (s + 1) &&
          bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag (s - twopow k) (s + 1))))
        (rdiag ((s + 1) - twopow k) (s + 1) &&
          bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1))) := by
  rw [frobDefect_row_testBit_outside_cone (s + 1) k s hs,
    ← core_center_eq_rdiag (s + 1)]
  have hl1 : rdiag ((s + 1) + twopow k) (s + 1) = ldiag ((s + 1) - twopow k) (s + 1) := by
    have h0 := ldiag_eq_rdiag ((s + 1) - twopow k) (twopow k)
    rw [show (s + 1) - twopow k + twopow k = s + 1 by omega,
      show (s + 1) - twopow k + 2 * twopow k = (s + 1) + twopow k by omega] at h0
    exact h0.symm
  have hl0 : rdiag (s + twopow k) (s + 1) = ldiag ((s + 2) - twopow k) (s + 1) := by
    have h0 := ldiag_eq_rdiag ((s + 2) - twopow k) (twopow k - 1)
    have hpos : ∀ m, 1 ≤ twopow m := by
      intro m
      induction m with
      | zero => decide
      | succ j ih => rw [Rule30UOR.Core.twopow_succ]; omega
    have hk := hpos k
    rw [show (s + 2) - twopow k + (twopow k - 1) = s + 1 by omega,
      show (s + 2) - twopow k + 2 * (twopow k - 1) = s + twopow k by omega] at h0
    exact h0.symm
  rw [hl1, hl0]

/-- **Frobenius Defect `δ_k` at the Center Slot `(s + 1) + 2^k` on White Center Steps (`frobDefect_row_center_slot_at_white_center_outside_cone`)**:
    for fixed `k` and all `s ≥ 2^k`, whenever `center (s + 1) = false`, the middle term vanishes and `rdiag s (s + 1) = maskparity (s + 1) 0`, so `(frobDefect k (row (s + 1))).testBit ((s + 1) + 2^k)` pairs `ldiag ((s + 1) - 2^k) (s + 1)` and `rdiag ((s + 1) - 2^k) (s + 1)` directly with `maskparity (s + 1) 0`! -/
theorem frobDefect_row_center_slot_at_white_center_outside_cone (s k : Nat) (hs : twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    (frobDefect k (row (s + 1))).testBit ((s + 1) + twopow k) =
      bxor
        (ldiag ((s + 1) - twopow k) (s + 1) &&
          bxor (Rule30UOR.Scale.maskparity (s + 1) 0) (rdiag (s - twopow k) (s + 1)))
        (rdiag ((s + 1) - twopow k) (s + 1) &&
          bxor (ldiag ((s + 2) - twopow k) (s + 1)) (Rule30UOR.Scale.maskparity (s + 1) 0)) := by
  have hm : rdiag s (s + 1) = Rule30UOR.Scale.maskparity (s + 1) 0 := by
    have hm0 := maskparity_succ_zero_eq_rdiag s
    rw [← core_center_eq_rdiag (s + 1), hw, Bool.not_false, Bool.true_and] at hm0
    exact hm0.symm
  rw [frobDefect_row_center_slot_outside_cone s k hs, hw, hm]
  simp only [bxor_eq_xor, Bool.false_and, Bool.xor_false]

/-- **Frobenius Defect `δ_k` at the Column-`-1` Slot `(d + 2) + 2^k` Outside the Cone (`frobDefect_row_colm1_slot_outside_cone`)**:
    for fixed `k` and all `d ≥ 2^k` (with NO upper bound on `d`), at time `t0 = d + 1`, the column-`-1` slot `(d + 2) + 2^k` of `frobDefect k (row (d + 1))` (which shifts under `↑` to the column-`-1` bit `(d + 3) + 2^k` of `winWitt (d + 2) (2^k)`) is the 3-term sum of products of cells of `row (d + 1)` at distance `2^k` and `2^(k+1)` apart! -/
theorem frobDefect_row_colm1_slot_outside_cone (d k : Nat) (hd : twopow k ≤ d) :
    (frobDefect k (row (d + 1))).testBit ((d + 2) + twopow k) =
      bxor (bxor
        (ldiag (d - twopow k) (d + 1) &&
          bxor (Rule30UOR.Core.center (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1)))
        (ldiag d (d + 1) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
        (rdiag ((d + 2) - twopow k) (d + 1) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1))) := by
  have hf := frobDefect_row_testBit_outside_cone (d + 1) k (d + 1) (by omega)
  rw [show (d + 1 + 1) + twopow k = (d + 2) + twopow k by omega,
    show d + 1 + 1 = d + 2 by omega,
    ← core_center_eq_rdiag (d + 1)] at hf
  have hl1 : rdiag ((d + 2) + twopow k) (d + 1) = ldiag (d - twopow k) (d + 1) := by
    have h0 := ldiag_eq_rdiag (d - twopow k) (twopow k + 1)
    rw [show d - twopow k + (twopow k + 1) = d + 1 by omega,
      show d - twopow k + 2 * (twopow k + 1) = (d + 2) + twopow k by omega] at h0
    exact h0.symm
  have hl2 : rdiag (d + 2) (d + 1) = ldiag d (d + 1) := by
    rw [show d + 2 = d + 2 * 1 by omega, ← ldiag_eq_rdiag d 1]
  have hl0 : rdiag ((d + 1) + twopow k) (d + 1) = ldiag ((d + 1) - twopow k) (d + 1) := by
    have h0 := ldiag_eq_rdiag ((d + 1) - twopow k) (twopow k)
    rw [show (d + 1) - twopow k + twopow k = d + 1 by omega,
      show (d + 1) - twopow k + 2 * twopow k = (d + 1) + twopow k by omega] at h0
    exact h0.symm
  rw [hl1, hl2, hl0] at hf
  exact hf

/-- **Frobenius Defect `δ_k` at the Column-`-1` Slot `(d + 2) + 2^k` on White Center Steps (`frobDefect_row_colm1_slot_at_white_center_outside_cone`)**:
    for fixed `k` and all `d ≥ 2^k`, whenever `center (d + 1) = false`, `center (d + 1)` drops out of `(frobDefect k (row (d + 1))).testBit ((d + 2) + 2^k)`, leaving a pure sum of products of non-center cells of `row (d + 1)` at distance `2^k` and `2^(k+1)` apart! -/
theorem frobDefect_row_colm1_slot_at_white_center_outside_cone (d k : Nat) (hd : twopow k ≤ d)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    (frobDefect k (row (d + 1))).testBit ((d + 2) + twopow k) =
      bxor (bxor
        (ldiag (d - twopow k) (d + 1) && rdiag ((d + 1) - twopow k) (d + 1))
        (ldiag d (d + 1) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
        (rdiag ((d + 2) - twopow k) (d + 1) && ldiag ((d + 1) - twopow k) (d + 1)) := by
  rw [frobDefect_row_colm1_slot_outside_cone d k hd, hw]
  simp only [bxor_eq_xor, Bool.false_xor, Bool.xor_false]

/-- **Frobenius Defect `δ_k` at the Column-`+1` Slot `(s + 1) + 2^k` of `row (s + 2)` Outside the Cone (`frobDefect_row_col1_slot_outside_cone`)**:
    for fixed `k` and all `s ≥ 2^k` (with NO upper bound on `s`), at time `t0 = s + 2`, the column-`+1` slot `(s + 1) + 2^k` of `frobDefect k (row (s + 2))` (which shifts under `↑` to the column-`+1` bit `(s + 2) + 2^k` of `winWitt (s + 3) (2^k)`) is the 3-term sum of products of cells of `row (s + 2)` at distance `2^k` and `2^(k+1)` apart! -/
theorem frobDefect_row_col1_slot_outside_cone (s k : Nat) (hs : twopow k ≤ s) :
    (frobDefect k (row (s + 2))).testBit ((s + 1) + twopow k) =
      bxor (bxor
        (ldiag ((s + 3) - twopow k) (s + 2) &&
          bxor (rdiag s (s + 2)) (rdiag (s - twopow k) (s + 2)))
        (rdiag (s + 1) (s + 2) &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag (s - twopow k) (s + 2))))
        (rdiag ((s + 1) - twopow k) (s + 2) &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag s (s + 2))) := by
  rw [frobDefect_row_testBit_outside_cone (s + 2) k s hs]
  have hl1 : rdiag ((s + 1) + twopow k) (s + 2) = ldiag ((s + 3) - twopow k) (s + 2) := by
    have h0 := ldiag_eq_rdiag ((s + 3) - twopow k) (twopow k - 1)
    have hpos : ∀ m, 1 ≤ twopow m := by
      intro m
      induction m with
      | zero => decide
      | succ j ih => rw [Rule30UOR.Core.twopow_succ]; omega
    have hk := hpos k
    rw [show (s + 3) - twopow k + (twopow k - 1) = s + 2 by omega,
      show (s + 3) - twopow k + 2 * (twopow k - 1) = (s + 1) + twopow k by omega] at h0
    exact h0.symm
  rw [hl1]

/-- **Frobenius Defect `δ_k` at the Column-`+1` Slot `(s + 1) + 2^k` of `row (s + 2)` on White Center Steps (`frobDefect_row_col1_slot_at_white_center_outside_cone`)**:
    for fixed `k` and all `s ≥ 2^k`, whenever `center (s + 2) = false`, `rdiag (s + 1) (s + 2) = maskparity (s + 2) 0`, tying `maskparity (s + 2) 0` directly to `bxor (rdiag (s + 2^k) (s + 2)) (rdiag (s - 2^k) (s + 2))`! -/
theorem frobDefect_row_col1_slot_at_white_center_outside_cone (s k : Nat) (hs : twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 2) = false) :
    (frobDefect k (row (s + 2))).testBit ((s + 1) + twopow k) =
      bxor (bxor
        (ldiag ((s + 3) - twopow k) (s + 2) &&
          bxor (rdiag s (s + 2)) (rdiag (s - twopow k) (s + 2)))
        (Rule30UOR.Scale.maskparity (s + 2) 0 &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag (s - twopow k) (s + 2))))
        (rdiag ((s + 1) - twopow k) (s + 2) &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag s (s + 2))) := by
  have hm : rdiag (s + 1) (s + 2) = Rule30UOR.Scale.maskparity (s + 2) 0 := by
    have hm0 := maskparity_succ_zero_eq_rdiag (s + 1)
    rw [← core_center_eq_rdiag (s + 2), hw, Bool.not_false, Bool.true_and] at hm0
    exact hm0.symm
  rw [frobDefect_row_col1_slot_outside_cone s k hs, hm]

/-- **The Periodic Window Step Outside the Cone at the Center Slot (`periodic_winWitt_step_center_slot_outside_cone`)**:
    for fixed `k` and all `s ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), advancing `winWitt (s + 1) (2^k) ↦ winWitt (s + 2) (2^k)` at the center slot `(s + 2) + 2^k` ties the Rule 30 evolution `wittRespBool (s + 2) k ⊕ (Φ(winWitt (s + 1) (2^k)))_((s + 2) + 2^k)` directly to the outside-the-cone cross-carry and the center-slot Frobenius defect `δ_k(row (s + 1))`! -/
theorem periodic_winWitt_step_center_slot_outside_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : twopow k ≤ s) :
    wittRespBool (s + 2) k =
      bxor (bxor
        ((phi (winWitt (s + 1) (twopow k))).testBit ((s + 2) + twopow k))
        (bxor (bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (Rule30UOR.Core.center (s + 1)))
            (rdiag ((s + 1) - twopow k) (s + 1)) &&
          rdiag (s + twopow k) ((s + 1) + twopow k))
          (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) &&
            bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
              (rdiag (s - twopow k) (s + 1)))))
        (bxor (bxor
          (ldiag ((s + 1) - twopow k) (s + 1) &&
            bxor (rdiag s (s + 1)) (rdiag (s - twopow k) (s + 1)))
          (Rule30UOR.Core.center (s + 1) &&
            bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag (s - twopow k) (s + 1))))
          (rdiag ((s + 1) - twopow k) (s + 1) &&
            bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))) := by
  have hstep := winWitt_step_frobDefect_testBit_succ (s + 1) k ((s + 1) + twopow k)
  rw [show ((s + 1) + twopow k) + 1 = (s + 2) + twopow k by omega] at hstep
  change wittRespBool (s + 2) k = _ at hstep
  have hcc := crossCarry_at_center_bit_outside_cone_wronskian s k hs
  rw [Rule30UOR.Scale.center_mod hP h (s + 1) (twopow k) ht,
    show twopow k % P = Rule30UOR.Scale.lag P k from rfl] at hcc
  rw [hstep, hcc, frobDefect_row_center_slot_outside_cone s k hs]

/-- **The Periodic Window Step Outside the Cone at the Center Slot on White Late Center Steps (`periodic_winWitt_step_center_slot_at_white_late_center_outside_cone`)**:
    for fixed `k` and all `s ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), whenever `center ((s + 1) + lag P k) = false`, the cross-carry collapses to `wittRespBool (s + 1) k && maskparity ((s + 1) + 2^k) 0`, tying `wittRespBool (s + 2) k` across time to `wittRespBool (s + 1) k && maskparity ((s + 1) + 2^k) 0` and the Frobenius defect `δ_k(row (s + 1))`! -/
theorem periodic_winWitt_step_center_slot_at_white_late_center_outside_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : twopow k ≤ s)
    (hw_late : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    wittRespBool (s + 2) k =
      bxor (bxor
        ((phi (winWitt (s + 1) (twopow k))).testBit ((s + 2) + twopow k))
        (wittRespBool (s + 1) k && Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0))
        (bxor (bxor
          (ldiag ((s + 1) - twopow k) (s + 1) &&
            bxor (rdiag s (s + 1)) (rdiag (s - twopow k) (s + 1)))
          (Rule30UOR.Core.center (s + 1) &&
            bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag (s - twopow k) (s + 1))))
          (rdiag ((s + 1) - twopow k) (s + 1) &&
            bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))) := by
  have hstep := winWitt_step_frobDefect_testBit_succ (s + 1) k ((s + 1) + twopow k)
  rw [show ((s + 1) + twopow k) + 1 = (s + 2) + twopow k by omega] at hstep
  change wittRespBool (s + 2) k = _ at hstep
  have hw1 : Rule30UOR.Core.center ((s + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (s + 1) (twopow k) ht]
    exact hw_late
  rw [hstep, crossCarry_at_white_late_center_eq_witt_and_maskparity s k hw1,
    frobDefect_row_center_slot_outside_cone s k hs]

/-- **The Periodic Window Step Outside the Cone at the Center Slot on White Early and Late Centers (`periodic_winWitt_step_center_slot_at_both_white_centers_outside_cone`)**:
    for fixed `k` and all `s ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), whenever `center (s + 1) = false` and `center ((s + 1) + lag P k) = false`, `wittRespBool (s + 2) k` is determined by `(phi (winWitt (s + 1) (2^k))).testBit ((s + 2) + 2^k)`, the cross-carry `((ldiag ((s + 1) - 2^k) (s + 1) ⊕ rdiag ((s + 1) - 2^k) (s + 1)) && maskparity ((s + 1) + 2^k) 0)`, and the 2-term Frobenius defect pairing `ldiag ((s + 1) - 2^k) (s + 1)` and `rdiag ((s + 1) - 2^k) (s + 1)` with `maskparity (s + 1) 0`! -/
theorem periodic_winWitt_step_center_slot_at_both_white_centers_outside_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : twopow k ≤ s)
    (hw1 : Rule30UOR.Core.center (s + 1) = false)
    (hw2 : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    wittRespBool (s + 2) k =
      bxor (bxor
        ((phi (winWitt (s + 1) (twopow k))).testBit ((s + 2) + twopow k))
        (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (rdiag ((s + 1) - twopow k) (s + 1)) &&
          Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0))
        (bxor
          (ldiag ((s + 1) - twopow k) (s + 1) &&
            bxor (Rule30UOR.Scale.maskparity (s + 1) 0) (rdiag (s - twopow k) (s + 1)))
          (rdiag ((s + 1) - twopow k) (s + 1) &&
            bxor (ldiag ((s + 2) - twopow k) (s + 1)) (Rule30UOR.Scale.maskparity (s + 1) 0))) := by
  have hstep := winWitt_step_frobDefect_testBit_succ (s + 1) k ((s + 1) + twopow k)
  rw [show ((s + 1) + twopow k) + 1 = (s + 2) + twopow k by omega] at hstep
  change wittRespBool (s + 2) k = _ at hstep
  rw [hstep,
    periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity T P hP h s k ht hs hw1 hw2,
    frobDefect_row_center_slot_at_white_center_outside_cone s k hs hw1]

/-- **The Periodic Window Step Outside the Cone at the Column-`-1` Slot `(d + 3) + 2^k` (`periodic_winWitt_step_colm1_slot_outside_cone`)**:
    for fixed `k` and all `d ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), advancing `winWitt (d + 1) (2^k) ↦ winWitt (d + 2) (2^k)` at the column-`-1` slot `(d + 3) + 2^k` combines `(phi (winWitt (d + 1) (2^k))).testBit ((d + 3) + 2^k)` with the column-`-1` cross-carry (Theorem 9.177) and the column-`-1` Frobenius defect `δ_k(row (d + 1))` at `(d + 2) + 2^k`! -/
theorem periodic_winWitt_step_colm1_slot_outside_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d) :
    (winWitt (d + 2) (twopow k)).testBit ((d + 3) + twopow k) =
      bxor (bxor
        ((phi (winWitt (d + 1) (twopow k))).testBit ((d + 3) + twopow k))
        (bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
            (rdiag ((d + 2) - twopow k) (d + 1)) &&
          Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
          (ldiag (d + twopow k) ((d + 1) + twopow k) &&
            bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
              (rdiag ((d + 1) - twopow k) (d + 1)))))
        (bxor (bxor
          (ldiag (d - twopow k) (d + 1) &&
            bxor (Rule30UOR.Core.center (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1)))
          (ldiag d (d + 1) &&
            bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
          (rdiag ((d + 2) - twopow k) (d + 1) &&
            bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))) := by
  have hstep := winWitt_step_frobDefect_testBit_succ (d + 1) k ((d + 2) + twopow k)
  rw [show ((d + 2) + twopow k) + 1 = (d + 3) + twopow k by omega] at hstep
  rw [hstep,
    periodic_crossCarry_colm1_outside_cone_wronskian T P hP h d k ht hd,
    frobDefect_row_colm1_slot_outside_cone d k hd]

/-- **The Periodic Window Step Outside the Cone at the Column-`-1` Slot on White Early and Late Centers (`periodic_winWitt_step_colm1_slot_at_both_white_centers_outside_cone`)**:
    for fixed `k` and all `d ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), whenever `center (d + 1) = false` and `center ((d + 1) + lag P k) = false`, every center term drops out of both the cross-carry and the Frobenius defect at `(d + 2) + 2^k`, leaving a pure sum of products of non-center cells at distance `2^k` and `2^(k+1)` apart! -/
theorem periodic_winWitt_step_colm1_slot_at_both_white_centers_outside_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    (winWitt (d + 2) (twopow k)).testBit ((d + 3) + twopow k) =
      bxor (bxor
        ((phi (winWitt (d + 1) (twopow k))).testBit ((d + 3) + twopow k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
        (bxor (bxor
          (ldiag (d - twopow k) (d + 1) && rdiag ((d + 1) - twopow k) (d + 1))
          (ldiag d (d + 1) &&
            bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
          (rdiag ((d + 2) - twopow k) (d + 1) && ldiag ((d + 1) - twopow k) (d + 1))) := by
  have hstep := winWitt_step_frobDefect_testBit_succ (d + 1) k ((d + 2) + twopow k)
  rw [show ((d + 2) + twopow k) + 1 = (d + 3) + twopow k by omega] at hstep
  rw [hstep,
    periodic_crossCarry_colm1_outside_cone_at_both_white_centers T P hP h d k ht hd hw1 hw2,
    frobDefect_row_colm1_slot_at_white_center_outside_cone d k hd hw1]

/-- **Multi-Period Shift (`+ m * P`) of the Window Step at the Center Slot on White Late Center Steps (`periodic_winWitt_step_center_slot_shift_mul_at_white_late_center`)**:
    for fixed `k`, all `s` with `T ≤ s + 1`, and ANY period multiple `m * P` under `CenterPeriodic T P` (`0 < P`), whenever `center ((s + 1) + lag P k) = false`, the `+ m * P` shift of the Rule 30 window step defect `wittRespBool (t0 + 1) k ⊕ (Φ(winWitt t0 (2^k)))_((t0 + 1) + 2^k) ⊕ (frobDefect k (row t0))_(t0 + 2^k)` equals the bilinear maskparity/Witt shift from Theorem 9.191! -/
theorem periodic_winWitt_step_center_slot_shift_mul_at_white_late_center (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m s k : Nat) (ht : T ≤ s + 1)
    (hw_late : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    bxor
      (bxor (bxor (wittRespBool ((s + m * P) + 2) k)
          ((phi (winWitt ((s + m * P) + 1) (twopow k))).testBit (((s + m * P) + 2) + twopow k)))
        ((frobDefect k (row ((s + m * P) + 1))).testBit (((s + m * P) + 1) + twopow k)))
      (bxor (bxor (wittRespBool (s + 2) k)
          ((phi (winWitt (s + 1) (twopow k))).testBit ((s + 2) + twopow k)))
        ((frobDefect k (row (s + 1))).testBit ((s + 1) + twopow k))) =
      bxor
        (bxor (wittRespBool ((s + m * P) + 1) k) (wittRespBool (s + 1) k) &&
          Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0)
        (wittRespBool (s + 1) k &&
          bxor (Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0)
            (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0)) := by
  have hs1 := winWitt_step_frobDefect_testBit_succ (s + 1) k ((s + 1) + twopow k)
  rw [show ((s + 1) + twopow k) + 1 = (s + 2) + twopow k by omega] at hs1
  change wittRespBool (s + 2) k = _ at hs1
  have hsm := winWitt_step_frobDefect_testBit_succ ((s + m * P) + 1) k (((s + m * P) + 1) + twopow k)
  rw [show (((s + m * P) + 1) + twopow k) + 1 = ((s + m * P) + 2) + twopow k by omega] at hsm
  change wittRespBool ((s + m * P) + 2) k = _ at hsm
  have hcc := periodic_crossCarry_center_bit_shift_mul_at_white_late_center T P hP h m s k ht hw_late
  rw [hs1, hsm, ← hcc]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((s + m * P) + 1) (twopow k))).testBit (((s + m * P) + 2) + twopow k) <;>
    cases (crossCarry (phiScale k (row ((s + m * P) + 1))) (winWitt ((s + m * P) + 1) (twopow k))).testBit
      (((s + m * P) + 1) + twopow k) <;>
    cases (frobDefect k (row ((s + m * P) + 1))).testBit (((s + m * P) + 1) + twopow k) <;>
    cases (phi (winWitt (s + 1) (twopow k))).testBit ((s + 2) + twopow k) <;>
    cases (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit
      ((s + 1) + twopow k) <;>
    cases (frobDefect k (row (s + 1))).testBit ((s + 1) + twopow k) <;> rfl

/-- Paper-facing `BitWinWittEq` wrapper for `winWitt_step_frobDefect_testBit_succ`. -/
theorem winWitt_step_frobDefect_testBit_succ_prop (t0 k j : Nat) :
    BitWinWittEq (t0 + 1) (twopow k) (j + 1)
      (bxor (bxor ((phi (winWitt t0 (twopow k))).testBit (j + 1))
        ((crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit j))
        ((frobDefect k (row t0)).testBit j)) := by
  rw [BitWinWittEq, bit_eq_bton_testBit, winWitt_step_frobDefect_testBit_succ t0 k j]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_testBit_outside_cone`. -/
theorem frobDefect_row_testBit_outside_cone_prop (t0 k r : Nat) (hr : twopow k ≤ r) :
    BitFrobDefectEq k (row t0) ((r + 1) + twopow k)
      (bxor (bxor
        (rdiag ((r + 1) + twopow k) t0 &&
          bxor (rdiag r t0) (rdiag (r - twopow k) t0))
        (rdiag (r + 1) t0 &&
          bxor (rdiag (r + twopow k) t0) (rdiag (r - twopow k) t0)))
        (rdiag ((r + 1) - twopow k) t0 &&
          bxor (rdiag (r + twopow k) t0) (rdiag r t0))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit, frobDefect_row_testBit_outside_cone t0 k r hr]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_center_slot_outside_cone`. -/
theorem frobDefect_row_center_slot_outside_cone_prop (s k : Nat) (hs : twopow k ≤ s) :
    BitFrobDefectEq k (row (s + 1)) ((s + 1) + twopow k)
      (bxor (bxor
        (ldiag ((s + 1) - twopow k) (s + 1) &&
          bxor (rdiag s (s + 1)) (rdiag (s - twopow k) (s + 1)))
        (Rule30UOR.Core.center (s + 1) &&
          bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag (s - twopow k) (s + 1))))
        (rdiag ((s + 1) - twopow k) (s + 1) &&
          bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit, frobDefect_row_center_slot_outside_cone s k hs]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_center_slot_at_white_center_outside_cone`. -/
theorem frobDefect_row_center_slot_at_white_center_outside_cone_prop (s k : Nat) (hs : twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    BitFrobDefectEq k (row (s + 1)) ((s + 1) + twopow k)
      (bxor
        (ldiag ((s + 1) - twopow k) (s + 1) &&
          bxor (Rule30UOR.Scale.maskparity (s + 1) 0) (rdiag (s - twopow k) (s + 1)))
        (rdiag ((s + 1) - twopow k) (s + 1) &&
          bxor (ldiag ((s + 2) - twopow k) (s + 1)) (Rule30UOR.Scale.maskparity (s + 1) 0))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit,
    frobDefect_row_center_slot_at_white_center_outside_cone s k hs hw]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_colm1_slot_outside_cone`. -/
theorem frobDefect_row_colm1_slot_outside_cone_prop (d k : Nat) (hd : twopow k ≤ d) :
    BitFrobDefectEq k (row (d + 1)) ((d + 2) + twopow k)
      (bxor (bxor
        (ldiag (d - twopow k) (d + 1) &&
          bxor (Rule30UOR.Core.center (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1)))
        (ldiag d (d + 1) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
        (rdiag ((d + 2) - twopow k) (d + 1) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit, frobDefect_row_colm1_slot_outside_cone d k hd]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_colm1_slot_at_white_center_outside_cone`. -/
theorem frobDefect_row_colm1_slot_at_white_center_outside_cone_prop (d k : Nat) (hd : twopow k ≤ d)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    BitFrobDefectEq k (row (d + 1)) ((d + 2) + twopow k)
      (bxor (bxor
        (ldiag (d - twopow k) (d + 1) && rdiag ((d + 1) - twopow k) (d + 1))
        (ldiag d (d + 1) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
        (rdiag ((d + 2) - twopow k) (d + 1) && ldiag ((d + 1) - twopow k) (d + 1))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit,
    frobDefect_row_colm1_slot_at_white_center_outside_cone d k hd hw]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_col1_slot_outside_cone`. -/
theorem frobDefect_row_col1_slot_outside_cone_prop (s k : Nat) (hs : twopow k ≤ s) :
    BitFrobDefectEq k (row (s + 2)) ((s + 1) + twopow k)
      (bxor (bxor
        (ldiag ((s + 3) - twopow k) (s + 2) &&
          bxor (rdiag s (s + 2)) (rdiag (s - twopow k) (s + 2)))
        (rdiag (s + 1) (s + 2) &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag (s - twopow k) (s + 2))))
        (rdiag ((s + 1) - twopow k) (s + 2) &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag s (s + 2)))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit, frobDefect_row_col1_slot_outside_cone s k hs]

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_col1_slot_at_white_center_outside_cone`. -/
theorem frobDefect_row_col1_slot_at_white_center_outside_cone_prop (s k : Nat) (hs : twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 2) = false) :
    BitFrobDefectEq k (row (s + 2)) ((s + 1) + twopow k)
      (bxor (bxor
        (ldiag ((s + 3) - twopow k) (s + 2) &&
          bxor (rdiag s (s + 2)) (rdiag (s - twopow k) (s + 2)))
        (Rule30UOR.Scale.maskparity (s + 2) 0 &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag (s - twopow k) (s + 2))))
        (rdiag ((s + 1) - twopow k) (s + 2) &&
          bxor (rdiag (s + twopow k) (s + 2)) (rdiag s (s + 2)))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit,
    frobDefect_row_col1_slot_at_white_center_outside_cone s k hs hw]

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_winWitt_step_colm1_slot_outside_cone`. -/
theorem periodic_winWitt_step_colm1_slot_outside_cone_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d) :
    BitWinWittEq (d + 2) (twopow k) ((d + 3) + twopow k)
      (bxor (bxor
        ((phi (winWitt (d + 1) (twopow k))).testBit ((d + 3) + twopow k))
        (bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
            (rdiag ((d + 2) - twopow k) (d + 1)) &&
          Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
          (ldiag (d + twopow k) ((d + 1) + twopow k) &&
            bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
              (rdiag ((d + 1) - twopow k) (d + 1)))))
        (bxor (bxor
          (ldiag (d - twopow k) (d + 1) &&
            bxor (Rule30UOR.Core.center (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1)))
          (ldiag d (d + 1) &&
            bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
          (rdiag ((d + 2) - twopow k) (d + 1) &&
            bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1))))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_winWitt_step_colm1_slot_outside_cone T P hP h d k ht hd]

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_winWitt_step_colm1_slot_at_both_white_centers_outside_cone`. -/
theorem periodic_winWitt_step_colm1_slot_at_both_white_centers_outside_cone_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    BitWinWittEq (d + 2) (twopow k) ((d + 3) + twopow k)
      (bxor (bxor
        ((phi (winWitt (d + 1) (twopow k))).testBit ((d + 3) + twopow k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
        (bxor (bxor
          (ldiag (d - twopow k) (d + 1) && rdiag ((d + 1) - twopow k) (d + 1))
          (ldiag d (d + 1) &&
            bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))))
          (rdiag ((d + 2) - twopow k) (d + 1) && ldiag ((d + 1) - twopow k) (d + 1)))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_winWitt_step_colm1_slot_at_both_white_centers_outside_cone T P hP h d k ht hd hw1 hw2]

/-- Boolean bit readout of a Witt row integer `y` at bit `j`: `wittBitBool y j = y.testBit j`. -/
def wittBitBool (y j : Nat) : Bool :=
  y.testBit j

/-- **The Periodic Window Step Outside the Cone at the Column-`+1` Slot `(s + 2) + 2^k` (`periodic_winWitt_step_col1_slot_outside_cone`)**:
    for fixed `k` and all `s ≥ 2^k` at time `t0 = s + 2`, advancing `winWitt (s + 2) (2^k) ↦ winWitt (s + 3) (2^k)` at the column-`+1` slot `(s + 2) + 2^k` combines `(phi (winWitt (s + 2) (2^k))).testBit ((s + 2) + 2^k)` with the column-`+1` cross-carry `(crossCarry (phiScale k (row (s + 2))) (winWitt (s + 2) (2^k))).testBit ((s + 1) + 2^k)` and the 3-term column-`+1` Frobenius defect `δ_k(row (s + 2))` at `(s + 1) + 2^k`! -/
theorem periodic_winWitt_step_col1_slot_outside_cone (s k : Nat) (hs : twopow k ≤ s) :
    (winWitt (s + 3) (twopow k)).testBit ((s + 2) + twopow k) =
      bxor (bxor
        ((phi (winWitt (s + 2) (twopow k))).testBit ((s + 2) + twopow k))
        ((crossCarry (phiScale k (row (s + 2))) (winWitt (s + 2) (twopow k))).testBit ((s + 1) + twopow k)))
        (bxor (bxor
          (ldiag ((s + 3) - twopow k) (s + 2) &&
            bxor (rdiag s (s + 2)) (rdiag (s - twopow k) (s + 2)))
          (rdiag (s + 1) (s + 2) &&
            bxor (rdiag (s + twopow k) (s + 2)) (rdiag (s - twopow k) (s + 2))))
          (rdiag ((s + 1) - twopow k) (s + 2) &&
            bxor (rdiag (s + twopow k) (s + 2)) (rdiag s (s + 2)))) := by
  have hstep := winWitt_step_frobDefect_testBit_succ (s + 2) k ((s + 1) + twopow k)
  rw [show (s + 2) + 1 = s + 3 by omega,
    show ((s + 1) + twopow k) + 1 = (s + 2) + twopow k by omega] at hstep
  rw [hstep, frobDefect_row_col1_slot_outside_cone s k hs]

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_winWitt_step_col1_slot_outside_cone`. -/
theorem periodic_winWitt_step_col1_slot_outside_cone_prop (s k : Nat) (hs : twopow k ≤ s) :
    BitWinWittEq (s + 3) (twopow k) ((s + 2) + twopow k)
      (bxor (bxor
        ((phi (winWitt (s + 2) (twopow k))).testBit ((s + 2) + twopow k))
        ((crossCarry (phiScale k (row (s + 2))) (winWitt (s + 2) (twopow k))).testBit ((s + 1) + twopow k)))
        (bxor (bxor
          (ldiag ((s + 3) - twopow k) (s + 2) &&
            bxor (rdiag s (s + 2)) (rdiag (s - twopow k) (s + 2)))
          (rdiag (s + 1) (s + 2) &&
            bxor (rdiag (s + twopow k) (s + 2)) (rdiag (s - twopow k) (s + 2))))
          (rdiag ((s + 1) - twopow k) (s + 2) &&
            bxor (rdiag (s + twopow k) (s + 2)) (rdiag s (s + 2))))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_winWitt_step_col1_slot_outside_cone s k hs]

/-! ### Tying the Single-Cell Seed In-Cone Laws (`R_periodic` and `δ_k = 0`) to the Three Targets -/

/-- **Bilinear Polarization of the Frobenius Defect (`frobDefect_xor`)**:
    for all `k, a, b : Nat`, `δ_k(a ⊕ b) = (δ_k(a) ⊕ δ_k(b)) ⊕ (crossCarry(S_k a, S_k b) ⊕ S_k(crossCarry(a, b)))`. -/
theorem frobDefect_xor (k a b : Nat) :
    frobDefect k (a ^^^ b) =
      (frobDefect k a ^^^ frobDefect k b) ^^^
        (crossCarry (phiScale k a) (phiScale k b) ^^^ phiScale k (crossCarry a b)) := by
  unfold frobDefect
  rw [phiScale_xor, carry_xor, carry_xor, phiScale_xor, phiScale_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases (carry (phiScale k a)).testBit i <;>
    cases (carry (phiScale k b)).testBit i <;>
    cases (crossCarry (phiScale k a) (phiScale k b)).testBit i <;>
    cases (phiScale k (carry a)).testBit i <;>
    cases (phiScale k (carry b)).testBit i <;>
    cases (phiScale k (crossCarry a b)).testBit i <;> rfl

/-- **In-Cone Vanishing of `δ_k(S_k(row t0))` (`frobDefect_phiScale_row_cone_eq_zero`)**:
    inside the light cone (`2 * t0 + 1 < 2^k`), both `δ_k(row t0) = 0` and `δ_(k+1)(row t0) = 0` hold, so by `phiScale_scale`, `δ_k(phiScale k (row t0)) = 0`! -/
theorem frobDefect_phiScale_row_cone_eq_zero (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    frobDefect k (phiScale k (row t0)) = 0 := by
  have hk1 : 2 * t0 + 1 < twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]
    omega
  unfold frobDefect
  rw [phiScale_scale k (row t0),
    carry_phiScale_row_cone t0 (k + 1) hk1,
    carry_phiScale_row_cone t0 k hcone,
    phiScale_scale k (carry (row t0)),
    Nat.xor_self]

/-- **Outside-the-Cone Frobenius Defect `δ_k(row (t0 + 2^k))` from In-Cone `δ_k = 0` (`frobDefect_row_late_from_cone`)**:
    for `2 * t0 + 1 < 2^k`, applying `frobDefect_xor` to `row (t0 + 2^k) = S_k(row t0) ⊕ win(t0, 2^k)` and using `δ_k(S_k(row t0)) = 0` expresses the outside-the-cone Frobenius defect `δ_k(row (t0 + 2^k))` purely in terms of the in-cone window `w = winWitt t0 (2^k)` and its cross-carries! -/
theorem frobDefect_row_late_from_cone (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    frobDefect k (row (t0 + twopow k)) =
      frobDefect k (winWitt t0 (twopow k)) ^^^
        (crossCarry (phiScale (k + 1) (row t0)) (phiScale k (winWitt t0 (twopow k))) ^^^
          phiScale k (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)))) := by
  rw [row_scale t0 k,
    frobDefect_xor k (phiScale k (row t0)) (winWitt t0 (twopow k)),
    frobDefect_phiScale_row_cone_eq_zero t0 k hcone,
    Nat.zero_xor,
    phiScale_scale k (row t0)]

/-- **Tying `R_periodic` to the Center-Slot Frobenius Defect at `t0 = (d + 1) + 2^k` (`frobDefect_row_late_center_slot_rperiodic`)**:
    for `d + 1 ≤ k`, time `t0 = (d + 1) + 2^k` is outside the cone of scale `k`, while its right-wing cells at distance `2^k` have depths `d + 1 ≤ k` and `d ≤ k` inside the exponential period `2^k`; therefore `R_periodic` reduces them to `center (d + 1)` and `rdiag d (d + 1)`! -/
theorem frobDefect_row_late_center_slot_rperiodic (d k : Nat) (hk : d + 1 ≤ k) :
    (frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 1) + twopow k) + twopow k) =
      bxor (bxor
        (ldiag (d + 1) ((d + 1) + twopow k) &&
          bxor (rdiag (d + twopow k) ((d + 1) + twopow k)) (rdiag d (d + 1)))
        (Rule30UOR.Core.center ((d + 1) + twopow k) &&
          bxor (ldiag (d + 2) ((d + 1) + twopow k)) (rdiag d (d + 1))))
        (Rule30UOR.Core.center (d + 1) &&
          bxor (ldiag (d + 2) ((d + 1) + twopow k)) (rdiag (d + twopow k) ((d + 1) + twopow k))) := by
  have hf := frobDefect_row_center_slot_outside_cone (d + twopow k) k (by omega)
  rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    show ((d + 1) + twopow k) - twopow k = d + 1 by omega,
    show (d + twopow k) + 2 = (d + 2) + twopow k by omega,
    show ((d + 2) + twopow k) - twopow k = d + 2 by omega,
    show (d + twopow k) - twopow k = d by omega] at hf
  have hr1 : rdiag (d + 1) ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
      rw [← Nat.pow_add, show k - (d + 1) + (d + 1) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 1) (2 ^ (k - (d + 1))) (d + 1), ← core_center_eq_rdiag (d + 1)]
  have hr0 : rdiag d ((d + 1) + twopow k) = rdiag d (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
      rw [← Nat.pow_add, show k - d + d = k by omega]
    rw [hpow, rdiag_periodic_mul d (2 ^ (k - d)) (d + 1)]
  rw [hr1, hr0] at hf
  exact hf

/-- **Single-Product Collapse of the Late Center-Slot Frobenius Defect (`frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump`)**:
    for `d + 1 ≤ k` and `SettledAt (d + 1) k`, whenever `center (d + 1) = false` and `center ((d + 1) + 2^k) = false`, `R_periodic` and settledness collapse `(frobDefect k (row ((d + 1) + 2^k))).testBit (((d + 1) + 2^k) + 2^k)` to the single AND-product `zcenter (d + 1) && (maskparity ((d + 1) + 2^k) 0 ⊕ maskparity (d + 1) 0)`! -/
theorem frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    (frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 1) + twopow k) + twopow k) =
      (zcenter (d + 1) &&
        bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
          (Rule30UOR.Scale.maskparity (d + 1) 0)) := by
  have hz : ldiag (d + 1) ((d + 1) + twopow k) = zcenter (d + 1) :=
    ldiag_settled_eq_zcenter (d + 1) k hk hset
  have hm1 : rdiag d (d + 1) = Rule30UOR.Scale.maskparity (d + 1) 0 := by
    have hm0 := maskparity_succ_zero_eq_rdiag d
    rw [← core_center_eq_rdiag (d + 1), hw1, Bool.not_false, Bool.true_and] at hm0
    exact hm0.symm
  have hm2 : rdiag (d + twopow k) ((d + 1) + twopow k) =
      Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 := by
    have hm0 := maskparity_succ_zero_eq_rdiag (d + twopow k)
    rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
      ← core_center_eq_rdiag ((d + 1) + twopow k), hw2, Bool.not_false, Bool.true_and] at hm0
    exact hm0.symm
  rw [frobDefect_row_late_center_slot_rperiodic d k hk, hz, hw1, hw2, hm1, hm2]
  simp only [bxor_eq_xor, Bool.false_and, Bool.xor_false]

/-- **Tying `R_periodic` to the Column-`-1` Frobenius Defect at `t0 = (d + 1) + 2^k` (`frobDefect_row_late_colm1_slot_rperiodic`)**:
    for `d + 2 ≤ k`, `R_periodic` folds the right-wing cells at distance `2^k` into `ldiag d (d + 1)` (the early column-`-1` cell!) and `center (d + 1)`! -/
theorem frobDefect_row_late_colm1_slot_rperiodic (d k : Nat) (hk : d + 2 ≤ k) :
    (frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 2) + twopow k) + twopow k) =
      bxor (bxor
        (ldiag d ((d + 1) + twopow k) &&
          bxor (Rule30UOR.Core.center ((d + 1) + twopow k)) (Rule30UOR.Core.center (d + 1)))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (ldiag (d + 1) ((d + 1) + twopow k)) (Rule30UOR.Core.center (d + 1))))
        (ldiag d (d + 1) &&
          bxor (ldiag (d + 1) ((d + 1) + twopow k)) (Rule30UOR.Core.center ((d + 1) + twopow k))) := by
  have hf := frobDefect_row_colm1_slot_outside_cone (d + twopow k) k (by omega)
  rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    show (d + twopow k) + 2 = (d + 2) + twopow k by omega,
    show (d + twopow k) - twopow k = d by omega,
    show ((d + 1) + twopow k) - twopow k = d + 1 by omega,
    show ((d + 2) + twopow k) - twopow k = d + 2 by omega] at hf
  have hr1 : rdiag (d + 1) ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
      rw [← Nat.pow_add, show k - (d + 1) + (d + 1) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 1) (2 ^ (k - (d + 1))) (d + 1), ← core_center_eq_rdiag (d + 1)]
  have hr2 : rdiag (d + 2) ((d + 1) + twopow k) = ldiag d (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 2)) * 2 ^ (d + 2) := by
      rw [← Nat.pow_add, show k - (d + 2) + (d + 2) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 2) (2 ^ (k - (d + 2))) (d + 1),
      show d + 2 = d + 2 * 1 by omega, ← ldiag_eq_rdiag d 1]
  rw [hr1, hr2] at hf
  exact hf

/-- **In-Phase Factorization of the Late Column-`-1` Frobenius Defect (`frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage`)**:
    for `d + 2 ≤ k` and `SettledAt (d + 1) k`, whenever `center ((d + 1) + 2^k) = center (d + 1)` (whether white OR black!), `(frobDefect k (row ((d + 1) + 2^k))).testBit (((d + 2) + 2^k) + 2^k)` factors into the column-`-1` dyadic jump `ldiag (d + 2^k) ((d + 1) + 2^k) ⊕ ldiag d (d + 1)` ANDed with the center damage `zcenter (d + 1) ⊕ center (d + 1)`! -/
theorem frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage
    (d k : Nat) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hphase : Rule30UOR.Core.center ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1)) :
    (frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 2) + twopow k) + twopow k) =
      (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1)) &&
        bxor (zcenter (d + 1)) (Rule30UOR.Core.center (d + 1))) := by
  have hz : ldiag (d + 1) ((d + 1) + twopow k) = zcenter (d + 1) :=
    ldiag_settled_eq_zcenter (d + 1) k (by omega) hset
  rw [frobDefect_row_late_colm1_slot_rperiodic d k hk, hz, hphase]
  simp only [bxor_eq_xor]
  cases ldiag d ((d + 1) + twopow k) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases ldiag d (d + 1) <;>
    cases zcenter (d + 1) <;>
    cases Rule30UOR.Core.center (d + 1) <;> rfl

/-- **Exact Difference Between the Column-`-1` and Center-Slot Frobenius Defects on White Centers (`frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers`)**:
    for `d + 2 ≤ k` and `SettledAt (d + 1) k`, whenever `center (d + 1) = false` and `center ((d + 1) + 2^k) = false`, `R_periodic`, settledness, and `scale_center_paper` at scale `0` prove that the XOR of bit `((d + 2) + 2^k) + 2^k` and bit `((d + 1) + 2^k) + 2^k` of `frobDefect k (row ((d + 1) + 2^k))` equals `zcenter (d + 1) && (center ((d + 2) + 2^k) ⊕ center (d + 2))`! -/
theorem frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers
    (d k : Nat) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    bxor
      ((frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 2) + twopow k) + twopow k))
      ((frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 1) + twopow k) + twopow k)) =
      (zcenter (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 2) + twopow k)) (Rule30UOR.Core.center (d + 2))) := by
  have hf_cent := frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump
    d k (by omega) hset hw1 hw2
  have hf_col := frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage
    d k hk hset (by rw [hw2, hw1])
  rw [hw1] at hf_col
  have hs1 := Rule30UOR.Scale.scale_center_paper (d + 1) 0
  have hs2 := Rule30UOR.Scale.scale_center_paper ((d + 1) + twopow k) 0
  rw [show twopow 0 = 1 from rfl,
    show Rule30UOR.Scale.negpow 0 = -1 from rfl,
    response_zero_eq_maskparity_zero] at hs1 hs2
  have hl1 : Rule30UOR.Core.cell (d + 1) (-1) = ldiag d (d + 1) :=
    (ldiag_eq_cell_neg d 1).symm
  have hl2 : Rule30UOR.Core.cell ((d + 1) + twopow k) (-1) = ldiag (d + twopow k) ((d + 1) + twopow k) := by
    rw [show (d + 1) + twopow k = (d + twopow k) + 1 by omega]
    exact (ldiag_eq_cell_neg (d + twopow k) 1).symm
  rw [hl1, hw1, show (d + 1) + 1 = d + 2 by omega] at hs1
  rw [hl2, hw2, show ((d + 1) + twopow k) + 1 = (d + 2) + twopow k by omega] at hs2
  rw [hf_col, hf_cent]
  revert hs1 hs2
  simp only [bxor_eq_xor]
  cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases ldiag d (d + 1) <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 <;>
    cases Rule30UOR.Scale.maskparity (d + 1) 0 <;>
    cases Rule30UOR.Core.center ((d + 2) + twopow k) <;>
    cases Rule30UOR.Core.center (d + 2) <;>
    cases zcenter (d + 1) <;> decide

/-- **Factored Window Step at `t0 = (d + 1) + 2^k` Tying `zcenter` to the Triality of `maskparity · 0` (`periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ d + 1`, `d + 1 ≤ k`, and `SettledAt (d + 1) k`, whenever `center (d + 1) = false`, `center ((d + 1) + lag P k) = false`, and `center ((d + 1) + lag P (k + 1)) = false`, `R_periodic` and settledness factor the entire nonlinear perturbation `↑crossCarry ⊕ ↑δ_k` at the center slot into `zcenter (d + 1) && (maskparity ((d + 1) + 2^(k+1)) 0 ⊕ maskparity ((d + 1) + 2^k) 0 ⊕ maskparity (d + 1) 0)`! -/
theorem periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    wittRespBool ((d + 2) + twopow k) k =
      bxor
        ((phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k))
        (zcenter (d + 1) &&
          bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
            (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
              (Rule30UOR.Scale.maskparity (d + 1) 0))) := by
  have hc_k : Rule30UOR.Core.center ((d + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht]
    exact hw1
  have hc_k1 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow (k + 1)) ht]
    exact hw2
  have hc_lag : Rule30UOR.Core.center (((d + 1) + twopow k) + Rule30UOR.Scale.lag P k) = false := by
    rw [show Rule30UOR.Scale.lag P k = twopow k % P from rfl,
      ← Rule30UOR.Scale.center_mod hP h ((d + 1) + twopow k) (twopow k) (by omega),
      show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
        rw [Rule30UOR.Core.twopow_succ]; omega]
    exact hc_k1
  have hstep := winWitt_step_frobDefect_testBit_succ ((d + 1) + twopow k) k (((d + 1) + twopow k) + twopow k)
  rw [show ((d + 1) + twopow k) + 1 = (d + 2) + twopow k by omega,
    show (((d + 1) + twopow k) + twopow k) + 1 = ((d + 2) + twopow k) + twopow k by omega] at hstep
  change wittRespBool ((d + 2) + twopow k) k = _ at hstep
  have hcc := periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity
    T P hP h (d + twopow k) k (by omega) (by omega)
    (by rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega]; exact hc_k)
    (by rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega]; exact hc_lag)
  rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    show ((d + 1) + twopow k) - twopow k = d + 1 by omega] at hcc
  have hr1 : rdiag (d + 1) ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
      rw [← Nat.pow_add, show k - (d + 1) + (d + 1) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 1) (2 ^ (k - (d + 1))) (d + 1), ← core_center_eq_rdiag (d + 1)]
  have hz : ldiag (d + 1) ((d + 1) + twopow k) = zcenter (d + 1) :=
    ldiag_settled_eq_zcenter (d + 1) k hk hset
  rw [hr1, hw0, hz,
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hcc
  have hf := frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump
    d k hk hset hw0 hc_k
  rw [show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hstep hf
  rw [hstep, hcc, hf]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k) <;>
    cases zcenter (d + 1) <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 <;>
    cases Rule30UOR.Scale.maskparity (d + 1) 0 <;> rfl

/-- **Factored Window Step at `t0 = (d + 1) + 2^k` Tying `zcenter` to the Triality of Column `-1` (`periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ d + 1`, `d + 2 ≤ k`, and `SettledAt (d + 1) k`, whenever `center (d + 1) = false`, `center ((d + 1) + lag P k) = false`, and `center ((d + 1) + lag P (k + 1)) = false`, `R_periodic` and settledness factor the entire nonlinear perturbation `↑crossCarry ⊕ ↑δ_k` at the column-`-1` slot into `zcenter (d + 1) && (ldiag (d + 2^(k+1)) ((d + 1) + 2^(k+1)) ⊕ ldiag (d + 2^k) ((d + 1) + 2^k) ⊕ ldiag d (d + 1))`! -/
theorem periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    (winWitt ((d + 2) + twopow k) (twopow k)).testBit (((d + 3) + twopow k) + twopow k) =
      bxor
        ((phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 3) + twopow k) + twopow k))
        (zcenter (d + 1) &&
          bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
            (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1)))) := by
  have hc_k : Rule30UOR.Core.center ((d + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht]
    exact hw1
  have hc_k1 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow (k + 1)) ht]
    exact hw2
  have hc_lag : Rule30UOR.Core.center (((d + 1) + twopow k) + Rule30UOR.Scale.lag P k) = false := by
    rw [show Rule30UOR.Scale.lag P k = twopow k % P from rfl,
      ← Rule30UOR.Scale.center_mod hP h ((d + 1) + twopow k) (twopow k) (by omega),
      show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
        rw [Rule30UOR.Core.twopow_succ]; omega]
    exact hc_k1
  have hstep := winWitt_step_frobDefect_testBit_succ ((d + 1) + twopow k) k (((d + 2) + twopow k) + twopow k)
  rw [show ((d + 1) + twopow k) + 1 = (d + 2) + twopow k by omega,
    show (((d + 2) + twopow k) + twopow k) + 1 = ((d + 3) + twopow k) + twopow k by omega] at hstep
  have hcc := periodic_crossCarry_colm1_outside_cone_at_both_white_centers
    T P hP h (d + twopow k) k (by omega) (by omega)
    (by rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega]; exact hc_k)
    (by rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega]; exact hc_lag)
  rw [show (d + twopow k) + 2 = (d + 2) + twopow k by omega,
    show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    show ((d + 1) + twopow k) - twopow k = d + 1 by omega,
    show (d + twopow k) + twopow k = d + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega,
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hcc
  have hr1 : rdiag (d + 1) ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
      rw [← Nat.pow_add, show k - (d + 1) + (d + 1) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 1) (2 ^ (k - (d + 1))) (d + 1), ← core_center_eq_rdiag (d + 1)]
  have hz : ldiag (d + 1) ((d + 1) + twopow k) = zcenter (d + 1) :=
    ldiag_settled_eq_zcenter (d + 1) k (by omega) hset
  rw [hr1, hw0, hz] at hcc
  have hf := frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage
    d k hk hset (by rw [hc_k, hw0])
  rw [hw0] at hf
  rw [show ((d + 2) + twopow k) + twopow k = (d + 2) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hstep hcc hf
  rw [hstep, hcc, hf]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 3) + twopow k) + twopow k) <;>
    cases zcenter (d + 1) <;>
    cases ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases ldiag d (d + 1) <;> rfl

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_late_center_slot_rperiodic`. -/
theorem frobDefect_row_late_center_slot_rperiodic_prop (d k : Nat) (hk : d + 1 ≤ k) :
    BitFrobDefectEq k (row ((d + 1) + twopow k)) (((d + 1) + twopow k) + twopow k)
      (bxor (bxor
        (ldiag (d + 1) ((d + 1) + twopow k) &&
          bxor (rdiag (d + twopow k) ((d + 1) + twopow k)) (rdiag d (d + 1)))
        (Rule30UOR.Core.center ((d + 1) + twopow k) &&
          bxor (ldiag (d + 2) ((d + 1) + twopow k)) (rdiag d (d + 1))))
        (Rule30UOR.Core.center (d + 1) &&
          bxor (ldiag (d + 2) ((d + 1) + twopow k)) (rdiag (d + twopow k) ((d + 1) + twopow k)))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit, frobDefect_row_late_center_slot_rperiodic d k hk]

/-- Paper-facing predicate `ZCenterAndEq d a c`: `(zcenter d && a) = c`. -/
def ZCenterAndEq (d : Nat) (a c : Bool) : Prop :=
  (zcenter d && a) = c

/-- Paper-facing `ZCenterAndEq` wrapper for `frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump`. -/
theorem frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump_prop
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    ZCenterAndEq (d + 1)
      (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0))
      (wittBitBool (frobDefect k (row ((d + 1) + twopow k))) (((d + 1) + twopow k) + twopow k)) := by
  unfold ZCenterAndEq wittBitBool
  exact (frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump
    d k hk hset hw1 hw2).symm

/-- Paper-facing `BitFrobDefectEq` wrapper for `frobDefect_row_late_colm1_slot_rperiodic`. -/
theorem frobDefect_row_late_colm1_slot_rperiodic_prop (d k : Nat) (hk : d + 2 ≤ k) :
    BitFrobDefectEq k (row ((d + 1) + twopow k)) (((d + 2) + twopow k) + twopow k)
      (bxor (bxor
        (ldiag d ((d + 1) + twopow k) &&
          bxor (Rule30UOR.Core.center ((d + 1) + twopow k)) (Rule30UOR.Core.center (d + 1)))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (ldiag (d + 1) ((d + 1) + twopow k)) (Rule30UOR.Core.center (d + 1))))
        (ldiag d (d + 1) &&
          bxor (ldiag (d + 1) ((d + 1) + twopow k)) (Rule30UOR.Core.center ((d + 1) + twopow k)))) := by
  rw [BitFrobDefectEq, bit_eq_bton_testBit, frobDefect_row_late_colm1_slot_rperiodic d k hk]

/-- Paper-facing `ZCenterAndEq` wrapper for `frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage`. -/
theorem frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage_prop
    (d k : Nat) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hphase : Rule30UOR.Core.center ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1)) :
    ZCenterAndEq (d + 1)
      (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1)))
      (bxor
        (wittBitBool (frobDefect k (row ((d + 1) + twopow k))) (((d + 2) + twopow k) + twopow k))
        (Rule30UOR.Core.center (d + 1) &&
          bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1)))) := by
  unfold ZCenterAndEq wittBitBool
  rw [frobDefect_row_late_colm1_slot_of_in_phase_eq_colm1_jump_and_damage d k hk hset hphase]
  simp only [bxor_eq_xor]
  cases zcenter (d + 1) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases (ldiag (d + twopow k) ((d + 1) + twopow k) ^^ ldiag d (d + 1)) <;> rfl

/-- Paper-facing `ZCenterAndEq` wrapper for `frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers`. -/
theorem frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers_prop
    (d k : Nat) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    ZCenterAndEq (d + 1)
      (bxor (Rule30UOR.Core.center ((d + 2) + twopow k)) (Rule30UOR.Core.center (d + 2)))
      (bxor
        (wittBitBool (frobDefect k (row ((d + 1) + twopow k))) (((d + 2) + twopow k) + twopow k))
        (wittBitBool (frobDefect k (row ((d + 1) + twopow k))) (((d + 1) + twopow k) + twopow k))) := by
  unfold ZCenterAndEq wittBitBool
  exact (frobDefect_row_late_colm1_xor_center_slot_at_both_white_centers d k hk hset hw1 hw2).symm

/-- Paper-facing `ZCenterAndEq` wrapper for `periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality`. -/
theorem periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    ZCenterAndEq (d + 1)
      (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
        (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
          (Rule30UOR.Scale.maskparity (d + 1) 0)))
      (bxor
        (wittRespBool ((d + 2) + twopow k) k)
        (wittBitBool (phi (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 2) + twopow k) + twopow k))) := by
  unfold ZCenterAndEq wittBitBool
  have hs := periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality
    T P hP h d k ht hk hset hw0 hw1 hw2
  rw [hs]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k) <;>
    cases (zcenter (d + 1) &&
      (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 ^^
        (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 ^^
          Rule30UOR.Scale.maskparity (d + 1) 0))) <;> rfl

/-- Paper-facing `ZCenterAndEq` wrapper for `periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality`. -/
theorem periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    ZCenterAndEq (d + 1)
      (bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1))))
      (bxor
        (wittBitBool (winWitt ((d + 2) + twopow k) (twopow k)) (((d + 3) + twopow k) + twopow k))
        (wittBitBool (phi (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 3) + twopow k) + twopow k))) := by
  unfold ZCenterAndEq wittBitBool
  have hs := periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality
    T P hP h d k ht hk hset hw0 hw1 hw2
  rw [hs]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 3) + twopow k) + twopow k) <;>
    cases (zcenter (d + 1) &&
      (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) ^^
        (ldiag (d + twopow k) ((d + 1) + twopow k) ^^ ldiag d (d + 1)))) <;> rfl

/-- **Exact Evaluation of `wittRespBool ((d + 1) + 2^k) k` via `R_periodic` and `zcenter` (`wittRespBool_late_eq_zcenter_xor_center_triality`)**:
    for `d + 1 ≤ k` and `SettledAt (d + 1) k`, at the outside-the-cone time `t0 = (d + 1) + 2^k`, `R_periodic` folds the right-wing cell `rdiag (d + 1) ((d + 1) + 2^k)` into `center (d + 1)` while `SettledAt (d + 1) k` stabilizes the left-wing cell `ldiag (d + 1) ((d + 1) + 2^k)` to `zcenter (d + 1)`, so `wittRespBool ((d + 1) + 2^k) k = zcenter (d + 1) ⊕ center ((d + 1) + 2^(k+1)) ⊕ center ((d + 1) + 2^k) ⊕ center (d + 1)`! -/
theorem wittRespBool_late_eq_zcenter_xor_center_triality
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k) :
    wittRespBool ((d + 1) + twopow k) k =
      bxor (zcenter (d + 1))
        (bxor (Rule30UOR.Core.center ((d + 1) + twopow (k + 1)))
          (bxor (Rule30UOR.Core.center ((d + 1) + twopow k))
            (Rule30UOR.Core.center (d + 1)))) := by
  have hw := winWitt_testBit_outside_cone ((d + 1) + twopow k) k ((d + 1) + twopow k) (by omega)
  change wittRespBool ((d + 1) + twopow k) k = _ at hw
  have hl : rdiag (((d + 1) + twopow k) + twopow k) ((d + 1) + twopow k) =
      ldiag (d + 1) ((d + 1) + twopow k) := by
    have h0 := ldiag_eq_rdiag (d + 1) (twopow k)
    rw [show (d + 1) + 2 * twopow k = ((d + 1) + twopow k) + twopow k by omega] at h0
    exact h0.symm
  have hz : ldiag (d + 1) ((d + 1) + twopow k) = zcenter (d + 1) :=
    ldiag_settled_eq_zcenter (d + 1) k hk hset
  have hr1 : rdiag (d + 1) ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
      rw [← Nat.pow_add, show k - (d + 1) + (d + 1) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 1) (2 ^ (k - (d + 1))) (d + 1), ← core_center_eq_rdiag (d + 1)]
  rw [show ((d + 1) + twopow k) - twopow k = d + 1 by omega,
    hl, hz, hr1,
    ← core_center_eq_rdiag (((d + 1) + twopow k) + twopow k),
    ← core_center_eq_rdiag ((d + 1) + twopow k),
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hw
  rw [hw]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) <;>
    cases zcenter (d + 1) <;>
    cases Rule30UOR.Core.center ((d + 1) + twopow k) <;>
    cases Rule30UOR.Core.center (d + 1) <;> rfl

/-- **Direct Readout of `zcenter (d + 1)` by `wittRespBool ((d + 1) + 2^k) k` on White Centers (`wittRespBool_late_at_white_centers_eq_zcenter`)**:
    for `d + 1 ≤ k` and `SettledAt (d + 1) k`, whenever `center (d + 1) = false`, `center ((d + 1) + 2^k) = false`, and `center ((d + 1) + 2^(k+1)) = false`, the outside-the-cone Witt center response `wittRespBool ((d + 1) + 2^k) k` equals `zcenter (d + 1)` directly! -/
theorem wittRespBool_late_at_white_centers_eq_zcenter
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + twopow k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false) :
    wittRespBool ((d + 1) + twopow k) k = zcenter (d + 1) := by
  rw [wittRespBool_late_eq_zcenter_xor_center_triality d k hk hset, hw0, hw1, hw2]
  simp only [bxor_eq_xor, Bool.xor_false]

/-- **Uniform-in-`m` Shift of `wittRespBool` from the `R_periodic` Anchor `t0 = (d + 1) + 2^k` (`periodic_wittRespBool_late_shift_mul_eq_zcenter_xor`)**:
    under `CenterPeriodic T P` (`0 < P`), for fixed `d, k` (`T ≤ d + 1`, `d + 1 ≤ k`, `SettledAt (d + 1) k`) and ALL `m : Nat` (unbounded time `t0 + m * P`), `R_periodic` and settledness anchor the base point `t0 = (d + 1) + 2^k` so `wittRespBool (((d + m * P) + 1) + 2^k) k ⊕ wittRespBool ((d + 1) + 2^k) k` equals `(ldiag ((d + m * P) + 1) (((d + m * P) + 1) + 2^k) ⊕ zcenter (d + 1)) ⊕ (rdiag ((d + m * P) + 1) (((d + m * P) + 1) + 2^k) ⊕ center (d + 1))`! -/
theorem periodic_wittRespBool_late_shift_mul_eq_zcenter_xor
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k) :
    bxor (wittRespBool (((d + m * P) + 1) + twopow k) k) (wittRespBool ((d + 1) + twopow k) k) =
      bxor
        (bxor (ldiag ((d + m * P) + 1) (((d + m * P) + 1) + twopow k)) (zcenter (d + 1)))
        (bxor (rdiag ((d + m * P) + 1) (((d + m * P) + 1) + twopow k))
          (Rule30UOR.Core.center (d + 1))) := by
  have hshift := periodic_wittRespBool_shift_mul_outside_cone
    T P hP h ((d + 1) + twopow k) k m (by omega) (by omega)
  rw [show ((d + 1) + twopow k) + m * P = ((d + m * P) + 1) + twopow k by omega,
    show (((d + m * P) + 1) + twopow k) - twopow k = (d + m * P) + 1 by omega,
    show ((d + 1) + twopow k) - twopow k = d + 1 by omega] at hshift
  have hz : ldiag (d + 1) ((d + 1) + twopow k) = zcenter (d + 1) :=
    ldiag_settled_eq_zcenter (d + 1) k hk hset
  have hr1 : rdiag (d + 1) ((d + 1) + twopow k) = Rule30UOR.Core.center (d + 1) := by
    rw [twopow_eq_pow k]
    have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
      rw [← Nat.pow_add, show k - (d + 1) + (d + 1) = k by omega]
    rw [hpow, rdiag_periodic_mul (d + 1) (2 ^ (k - (d + 1))) (d + 1), ← core_center_eq_rdiag (d + 1)]
  rw [hz, hr1] at hshift
  exact hshift

/-- **Uniform-in-`m` Shift of Center-Slot Cross-Carry Tying `zcenter (d + 1)` to the `m * P`-Periodicity Defect of `maskparity · 0` (`periodic_crossCarry_late_center_bit_shift_mul_at_white_centers`)**:
    under `CenterPeriodic T P` (`0 < P`), for fixed `d, k` (`T ≤ d + 1`, `d + 1 ≤ k`, `SettledAt (d + 1) k`) with white centers at `d + 1`, `(d + 1) + lag P k`, and `(d + 1) + lag P (k + 1)`, and for ALL `m : Nat` (unbounded time), the `m * P`-shift of the center-slot cross-carry from `t0 = (d + 1) + 2^k` to `((d + m * P) + 1) + 2^k` pairs `zcenter (d + 1)` directly with `maskparity (((d + m * P) + 1) + 2^(k+1)) 0 ⊕ maskparity ((d + 1) + 2^(k+1)) 0`! -/
theorem periodic_crossCarry_late_center_bit_shift_mul_at_white_centers
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor
      ((crossCarry (phiScale k (row (((d + m * P) + 1) + twopow k)))
        (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit
          ((((d + m * P) + 1) + twopow k) + twopow k))
      ((crossCarry (phiScale k (row ((d + 1) + twopow k)))
        (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 1) + twopow k) + twopow k)) =
      bxor
        (bxor (wittRespBool (((d + m * P) + 1) + twopow k) k) (zcenter (d + 1)) &&
          Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)
        (zcenter (d + 1) &&
          bxor (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)
            (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)) := by
  have hc_k : Rule30UOR.Core.center ((d + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht]
    exact hw1
  have hc_k1 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow (k + 1)) ht]
    exact hw2
  have hc_lag : Rule30UOR.Core.center (((d + 1) + twopow k) + Rule30UOR.Scale.lag P k) = false := by
    rw [show Rule30UOR.Scale.lag P k = twopow k % P from rfl,
      ← Rule30UOR.Scale.center_mod hP h ((d + 1) + twopow k) (twopow k) (by omega),
      show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
        rw [Rule30UOR.Core.twopow_succ]; omega]
    exact hc_k1
  have hcc := periodic_crossCarry_center_bit_shift_mul_at_white_late_center
    T P hP h m (d + twopow k) k (by omega)
    (by rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega]; exact hc_lag)
  rw [show ((d + twopow k) + m * P) + 1 = ((d + m * P) + 1) + twopow k by omega,
    show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    wittRespBool_late_at_white_centers_eq_zcenter d k hk hset hw0 hc_k hc_k1,
    show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega,
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hcc
  rw [show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega,
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega]
  exact hcc

/-- **Uniform-in-`m` Shift of Column-`-1` Cross-Carry Tying `zcenter (d + 1)` to the `m * P`-Periodicity Defect of `maskparity · 0` (`periodic_crossCarry_late_colm1_shift_mul_at_white_centers`)**:
    under `CenterPeriodic T P` (`0 < P`), for fixed `d, k` (`T ≤ d + 1`, `d + 1 ≤ k`, `SettledAt (d + 1) k`) with white centers at `d + 1`, `(d + 1) + lag P k`, and `(d + 1) + lag P (k + 1)`, and for ALL `m : Nat` (unbounded time), the `m * P`-shift of the column-`-1` cross-carry from `t0 = (d + 1) + 2^k` to `((d + m * P) + 1) + 2^k` pairs the `m * P`-defect of `maskparity · 0` at `((d + 1) + 2^(k+1))` with `wittRespBool (((d + m * P) + 1) + 2^k) k` and `zcenter (d + 1)`! -/
theorem periodic_crossCarry_late_colm1_shift_mul_at_white_centers
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor
      ((crossCarry (phiScale k (row (((d + m * P) + 1) + twopow k)))
        (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit
          ((((d + m * P) + 2) + twopow k) + twopow k))
      ((crossCarry (phiScale k (row ((d + 1) + twopow k)))
        (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k)) =
      bxor
        (bxor (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)
            (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0) &&
          wittRespBool (((d + m * P) + 1) + twopow k) k)
        (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) &&
          bxor (wittRespBool (((d + m * P) + 1) + twopow k) k) (zcenter (d + 1))) := by
  have hc_k : Rule30UOR.Core.center ((d + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht]
    exact hw1
  have hc_k1 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow (k + 1)) ht]
    exact hw2
  have hc_lag : Rule30UOR.Core.center (((d + 1) + twopow k) + Rule30UOR.Scale.lag P k) = false := by
    rw [show Rule30UOR.Scale.lag P k = twopow k % P from rfl,
      ← Rule30UOR.Scale.center_mod hP h ((d + 1) + twopow k) (twopow k) (by omega),
      show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
        rw [Rule30UOR.Core.twopow_succ]; omega]
    exact hc_k1
  have hcc := periodic_crossCarry_colm1_shift_mul_at_white_late_center
    T P hP h m (d + twopow k) k (by omega)
    (by rw [show (d + twopow k) + 1 = (d + 1) + twopow k by omega]; exact hc_lag)
  rw [show ((d + twopow k) + m * P) + 1 = ((d + m * P) + 1) + twopow k by omega,
    show ((d + twopow k) + m * P) + 2 = ((d + m * P) + 2) + twopow k by omega,
    show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    show (d + twopow k) + 2 = (d + 2) + twopow k by omega,
    wittRespBool_late_at_white_centers_eq_zcenter d k hk hset hw0 hc_k hc_k1,
    show (d + twopow k) + twopow k = d + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega,
    show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega,
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hcc
  exact hcc

/-- **Uniform-in-`m` Window Step from the `R_periodic` Anchor `t0 = (d + 1) + 2^k` (`periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers`)**:
    under `CenterPeriodic T P` (`0 < P`), for fixed `d, k` (`T ≤ d + 1`, `d + 1 ≤ k`, `SettledAt (d + 1) k`) with white centers at `d + 1`, `(d + 1) + lag P k`, and `(d + 1) + lag P (k + 1)`, and for ALL `m : Nat` (unbounded time), the `m * P`-shift of `wittRespBool ((s + 2)) k` from `s = d + 2^k` to `(d + m * P) + 2^k` ties the in-cone `R_periodic` anchor `zcenter (d + 1) && (maskparity ((d + 1) + 2^(k+1)) 0 ⊕ maskparity ((d + 1) + 2^k) 0 ⊕ maskparity (d + 1) 0)` directly to the outside-the-cone step at `((d + m * P) + 1) + 2^k`! -/
theorem periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor (wittRespBool (((d + m * P) + 2) + twopow k) k) (wittRespBool ((d + 2) + twopow k) k) =
      bxor
        (bxor
          ((phi (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit
            ((((d + m * P) + 2) + twopow k) + twopow k))
          ((phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k)))
        (bxor
          (bxor
            (wittRespBool (((d + m * P) + 1) + twopow k) k &&
              Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)
            ((frobDefect k (row (((d + m * P) + 1) + twopow k))).testBit
              ((((d + m * P) + 1) + twopow k) + twopow k)))
          (zcenter (d + 1) &&
            bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
              (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
                (Rule30UOR.Scale.maskparity (d + 1) 0)))) := by
  have hc_k1 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow (k + 1)) ht]
    exact hw2
  have hc_m_k1 : Rule30UOR.Core.center (((d + m * P) + 1) + twopow (k + 1)) = false := by
    rw [show ((d + m * P) + 1) + twopow (k + 1) = ((d + 1) + twopow (k + 1)) + m * P by omega,
      center_periodic_mul T P h m ((d + 1) + twopow (k + 1)) (by omega)]
    exact hc_k1
  have hc_m_lag : Rule30UOR.Core.center ((((d + m * P) + 1) + twopow k) + Rule30UOR.Scale.lag P k) = false := by
    rw [show Rule30UOR.Scale.lag P k = twopow k % P from rfl,
      ← Rule30UOR.Scale.center_mod hP h (((d + m * P) + 1) + twopow k) (twopow k) (by omega),
      show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
        rw [Rule30UOR.Core.twopow_succ]; omega]
    exact hc_m_k1
  have hstep_m := winWitt_step_frobDefect_testBit_succ
    (((d + m * P) + 1) + twopow k) k ((((d + m * P) + 1) + twopow k) + twopow k)
  rw [show (((d + m * P) + 1) + twopow k) + 1 = ((d + m * P) + 2) + twopow k by omega,
    show ((((d + m * P) + 1) + twopow k) + twopow k) + 1 = (((d + m * P) + 2) + twopow k) + twopow k by omega] at hstep_m
  change wittRespBool (((d + m * P) + 2) + twopow k) k = _ at hstep_m
  have hcc_m := crossCarry_at_white_late_center_eq_witt_and_maskparity ((d + m * P) + twopow k) k
    (by rw [show ((d + m * P) + twopow k) + 1 = ((d + m * P) + 1) + twopow k by omega,
          show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
            rw [Rule30UOR.Core.twopow_succ]; omega]
        exact hc_m_k1)
  rw [show ((d + m * P) + twopow k) + 1 = ((d + m * P) + 1) + twopow k by omega,
    show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hcc_m
  rw [show (((d + m * P) + 1) + twopow k) + twopow k = ((d + m * P) + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hstep_m
  rw [hcc_m,
    show ((d + m * P) + 1) + twopow (k + 1) = (((d + m * P) + 1) + twopow k) + twopow k by
      rw [Rule30UOR.Core.twopow_succ]; omega] at hstep_m
  have hstep_0 := periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality
    T P hP h d k ht hk hset hw0 hw1 hw2
  rw [hstep_m, hstep_0,
    show ((((d + m * P) + 1) + twopow k) + twopow k) = ((d + m * P) + 1) + twopow (k + 1) by
      rw [Rule30UOR.Core.twopow_succ]; omega]
  simp only [bxor_eq_xor]
  cases (phi (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit ((((d + m * P) + 2) + twopow k) + twopow k) <;>
    cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k) <;>
    cases (wittRespBool (((d + m * P) + 1) + twopow k) k &&
      Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0) <;>
    cases (frobDefect k (row (((d + m * P) + 1) + twopow k))).testBit (((d + m * P) + 1) + twopow (k + 1)) <;>
    cases (zcenter (d + 1) &&
      (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 ^^
        (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 ^^
          Rule30UOR.Scale.maskparity (d + 1) 0))) <;> rfl

/-- Paper-facing `ZCenterEq` wrapper for `wittRespBool_late_eq_zcenter_xor_center_triality`. -/
theorem wittRespBool_late_eq_zcenter_xor_center_triality_prop
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k) :
    ZCenterEq (d + 1)
      (bxor (wittRespBool ((d + 1) + twopow k) k)
        (bxor (Rule30UOR.Core.center ((d + 1) + twopow (k + 1)))
          (bxor (Rule30UOR.Core.center ((d + 1) + twopow k))
            (Rule30UOR.Core.center (d + 1))))) := by
  unfold ZCenterEq
  rw [wittRespBool_late_eq_zcenter_xor_center_triality d k hk hset]
  simp only [bxor_eq_xor]
  cases zcenter (d + 1) <;>
    cases (Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) ^^
      (Rule30UOR.Core.center ((d + 1) + twopow k) ^^
        Rule30UOR.Core.center (d + 1))) <;> rfl

/-- Paper-facing `ZCenterEq` wrapper for `wittRespBool_late_at_white_centers_eq_zcenter`. -/
theorem wittRespBool_late_at_white_centers_eq_zcenter_prop
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + twopow k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) = false) :
    ZCenterEq (d + 1) (wittRespBool ((d + 1) + twopow k) k) := by
  unfold ZCenterEq
  exact (wittRespBool_late_at_white_centers_eq_zcenter d k hk hset hw0 hw1 hw2).symm

/-- Paper-facing `ZCenterEq` wrapper for `periodic_wittRespBool_late_shift_mul_eq_zcenter_xor`. -/
theorem periodic_wittRespBool_late_shift_mul_eq_zcenter_xor_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k) :
    ZCenterEq (d + 1)
      (bxor
        (bxor (wittRespBool (((d + m * P) + 1) + twopow k) k) (wittRespBool ((d + 1) + twopow k) k))
        (bxor (ldiag ((d + m * P) + 1) (((d + m * P) + 1) + twopow k))
          (bxor (rdiag ((d + m * P) + 1) (((d + m * P) + 1) + twopow k))
            (Rule30UOR.Core.center (d + 1))))) := by
  unfold ZCenterEq
  rw [periodic_wittRespBool_late_shift_mul_eq_zcenter_xor T P hP h m d k ht hk hset]
  simp only [bxor_eq_xor]
  cases zcenter (d + 1) <;>
    cases ldiag ((d + m * P) + 1) (((d + m * P) + 1) + twopow k) <;>
    cases rdiag ((d + m * P) + 1) (((d + m * P) + 1) + twopow k) <;>
    cases Rule30UOR.Core.center (d + 1) <;> rfl

/-- Paper-facing `ZCenterAndEq` wrapper for `periodic_crossCarry_late_center_bit_shift_mul_at_white_centers`. -/
theorem periodic_crossCarry_late_center_bit_shift_mul_at_white_centers_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    ZCenterAndEq (d + 1)
      (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
      (bxor
        (bxor
          (wittBitBool (crossCarry (phiScale k (row (((d + m * P) + 1) + twopow k)))
            (winWitt (((d + m * P) + 1) + twopow k) (twopow k)))
              ((((d + m * P) + 1) + twopow k) + twopow k))
          (wittBitBool (crossCarry (phiScale k (row ((d + 1) + twopow k)))
            (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 1) + twopow k) + twopow k)))
        (wittRespBool (((d + m * P) + 1) + twopow k) k &&
          Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)) := by
  unfold ZCenterAndEq wittBitBool
  have hcc := periodic_crossCarry_late_center_bit_shift_mul_at_white_centers
    T P hP h m d k ht hk hset hw0 hw1 hw2
  revert hcc
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row (((d + m * P) + 1) + twopow k)))
    (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit ((((d + m * P) + 1) + twopow k) + twopow k) <;>
    cases (crossCarry (phiScale k (row ((d + 1) + twopow k)))
      (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 1) + twopow k) + twopow k) <;>
    cases wittRespBool (((d + m * P) + 1) + twopow k) k <;>
    cases zcenter (d + 1) <;>
    cases Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0 <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 <;> decide

/-- Paper-facing `ZCenterAndEq` wrapper for `periodic_crossCarry_late_colm1_shift_mul_at_white_centers`. -/
theorem periodic_crossCarry_late_colm1_shift_mul_at_white_centers_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    ZCenterAndEq (d + 1)
      (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
      (bxor
        (bxor
          (wittBitBool (crossCarry (phiScale k (row (((d + m * P) + 1) + twopow k)))
            (winWitt (((d + m * P) + 1) + twopow k) (twopow k)))
              ((((d + m * P) + 2) + twopow k) + twopow k))
          (wittBitBool (crossCarry (phiScale k (row ((d + 1) + twopow k)))
            (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 2) + twopow k) + twopow k)))
        (bxor
          (bxor (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)
              (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0) &&
            wittRespBool (((d + m * P) + 1) + twopow k) k)
          (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) &&
            wittRespBool (((d + m * P) + 1) + twopow k) k))) := by
  unfold ZCenterAndEq wittBitBool
  have hcc := periodic_crossCarry_late_colm1_shift_mul_at_white_centers
    T P hP h m d k ht hk hset hw0 hw1 hw2
  revert hcc
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row (((d + m * P) + 1) + twopow k)))
    (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit ((((d + m * P) + 2) + twopow k) + twopow k) <;>
    cases (crossCarry (phiScale k (row ((d + 1) + twopow k)))
      (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k) <;>
    cases (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0 ^^
      Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0) <;>
    cases wittRespBool (((d + m * P) + 1) + twopow k) k <;>
    cases ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) <;>
    cases zcenter (d + 1) <;> decide

/-- Paper-facing `ZCenterAndEq` wrapper for `periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers`. -/
theorem periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    ZCenterAndEq (d + 1)
      (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
        (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
          (Rule30UOR.Scale.maskparity (d + 1) 0)))
      (bxor
        (bxor (wittRespBool (((d + m * P) + 2) + twopow k) k) (wittRespBool ((d + 2) + twopow k) k))
        (bxor
          (bxor
            (wittBitBool (phi (winWitt (((d + m * P) + 1) + twopow k) (twopow k)))
              ((((d + m * P) + 2) + twopow k) + twopow k))
            (wittBitBool (phi (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 2) + twopow k) + twopow k)))
          (bxor
            (wittRespBool (((d + m * P) + 1) + twopow k) k &&
              Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0)
            (wittBitBool (frobDefect k (row (((d + m * P) + 1) + twopow k)))
              ((((d + m * P) + 1) + twopow k) + twopow k))))) := by
  unfold ZCenterAndEq wittBitBool
  have hs := periodic_winWitt_step_late_center_slot_shift_mul_at_white_centers
    T P hP h m d k ht hk hset hw0 hw1 hw2
  rw [hs]
  simp only [bxor_eq_xor]
  cases ((phi (winWitt (((d + m * P) + 1) + twopow k) (twopow k))).testBit ((((d + m * P) + 2) + twopow k) + twopow k) ^^
    (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k)) <;>
    cases ((wittRespBool (((d + m * P) + 1) + twopow k) k &&
      Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow (k + 1)) 0) ^^
      (frobDefect k (row (((d + m * P) + 1) + twopow k))).testBit ((((d + m * P) + 1) + twopow k) + twopow k)) <;>
    cases (zcenter (d + 1) &&
      (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 ^^
        (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 ^^
          Rule30UOR.Scale.maskparity (d + 1) 0))) <;> rfl

/-! ### In-Cone Seed Laws (`restart`, `R_periodic`, `frobDefect = 0`), Sector-2 Wronskian of `winWitt`, and Target Refutations -/

/-- **In-cone seed law `restart` (`rdiag_restart`)**: for every right diagonal `j ≤ k`, `rdiag j` repeats at every multiple `u * 2^k` uniformly for all `u, s : Nat`. -/
theorem rdiag_restart (k j u s : Nat) (hj : j ≤ k) :
    rdiag j (s + u * twopow k) = rdiag j s := by
  rw [twopow_eq_pow k, show u * 2 ^ k = (u * 2 ^ (k - j)) * 2 ^ j by
    rw [Nat.mul_assoc, ← Nat.pow_add, show k - j + j = k by omega]]
  exact rdiag_periodic_mul j (u * 2 ^ (k - j)) s

/-- **Threshold form of `restart` (`rdiag_restart_of_threshold`)**: for every right diagonal `j ≤ J` below the right-period threshold `J` of scale `k`, `rdiag j (s + u * 2^k) = rdiag j s` uniformly for all `u, s : Nat`. -/
theorem rdiag_restart_of_threshold (k J j u s : Nat) (hJ : IsRightThreshold k J) (hj : j ≤ J) :
    rdiag j (s + u * twopow k) = rdiag j s := by
  have hper := Rule30UOR.KitConstructive.per_mono_le hj hJ.1
  rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
  exact hper.mul u s

/-- **Center restart in `rdiag` coordinates (`center_restart_rdiag`)**: for every `s ≤ k` and every multiple `u : Nat`, `rdiag s (s + u * 2^k) = center s`. -/
theorem center_restart_rdiag (k s u : Nat) (hs : s ≤ k) :
    rdiag s (s + u * twopow k) = Rule30UOR.Core.center s := by
  rw [rdiag_restart k s u s hs, core_center_eq_rcenter]; rfl

/-- **Sector-0 vanishing of `frobDefect k (row t0)` uniformly for all `t0 : Nat`**: for every `t0`, `k`, and `j < 2^k` (with no cone restriction on `t0`), bit `j` of `frobDefect k (row t0)` is `false`. -/
theorem frobDefect_row_testBit_lt_twopow (t0 k j : Nat) (hj : j < twopow k) :
    (frobDefect k (row t0)).testBit j = false := by
  change (carry (phiScale k (row t0)) ^^^ phiScale k (carry (row t0))).testBit j = false
  simp only [Nat.testBit_xor]
  have hc1 : (carry (phiScale k (row t0))).testBit j =
      ((phiScale k (row t0)).testBit j &&
        (decide (j ≥ 1) && (phiScale k (row t0)).testBit (j - 1))) := by
    change ((phiScale k (row t0)) &&& ((phiScale k (row t0)) <<< 1)).testBit j = _
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
  have hc2 : (phiScale k (carry (row t0))).testBit j = (carry (row t0)).testBit j := by
    change (((carry (row t0)) ^^^ ((carry (row t0)) <<< twopow k)) ^^^
      ((carry (row t0)) <<< (twopow k + twopow k))).testBit j = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (j ≥ twopow k) = false := decide_eq_false (by omega)
    have d2 : decide (j ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false]
  have hc3 : (carry (row t0)).testBit j =
      ((row t0).testBit j && (decide (j ≥ 1) && (row t0).testBit (j - 1))) := by
    change ((row t0) &&& ((row t0) <<< 1)).testBit j = _
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
  have hs1 : (phiScale k (row t0)).testBit j = (row t0).testBit j := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit j = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (j ≥ twopow k) = false := decide_eq_false (by omega)
    have d2 : decide (j ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false]
  have hs2 : (phiScale k (row t0)).testBit (j - 1) = (row t0).testBit (j - 1) := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (j - 1) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (j - 1 ≥ twopow k) = false := decide_eq_false (by omega)
    have d2 : decide (j - 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false]
  rw [hc1, hc2, hc3, hs1, hs2, Bool.xor_self]

/-- **Sector-1 readout of `frobDefect k (row t0)` uniformly for all `t0 : Nat`**: for every `t0`, `k`, and `r` with `r + 1 < 2^k` (with no cone restriction on `t0`), bit `(r + 1) + 2^k` of `frobDefect k (row t0)` is the `2×2` Wronskian `(rdiag ((r + 1) + 2^k) t0 && rdiag r t0) ⊕ (rdiag (r + 1) t0 && rdiag (r + 2^k) t0)`. -/
theorem frobDefect_row_testBit_sector_one (t0 k r : Nat) (hr : r + 1 < twopow k) :
    (frobDefect k (row t0)).testBit ((r + 1) + twopow k) =
      bxor
        (rdiag ((r + 1) + twopow k) t0 && rdiag r t0)
        (rdiag (r + 1) t0 && rdiag (r + twopow k) t0) := by
  change (carry (phiScale k (row t0)) ^^^ phiScale k (carry (row t0))).testBit ((r + 1) + twopow k) = _
  simp only [Nat.testBit_xor, bxor_eq_xor]
  have hc1 : (carry (phiScale k (row t0))).testBit ((r + 1) + twopow k) =
      ((phiScale k (row t0)).testBit ((r + 1) + twopow k) &&
        (phiScale k (row t0)).testBit (r + twopow k)) := by
    change ((phiScale k (row t0)) &&& ((phiScale k (row t0)) <<< 1)).testBit ((r + 1) + twopow k) = _
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow k ≥ 1) = true := decide_eq_true (by omega)
    rw [d1, Bool.true_and, show (r + 1) + twopow k - 1 = r + twopow k by omega]
  have hs1 : (phiScale k (row t0)).testBit ((r + 1) + twopow k) =
      bxor (rdiag ((r + 1) + twopow k) t0) (rdiag (r + 1) t0) := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, bxor_eq_xor]
    have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show (r + 1) + twopow k - twopow k = r + 1 by omega,
      row_testBit t0 ((r + 1) + twopow k), row_testBit t0 (r + 1)]
  have hs2 : (phiScale k (row t0)).testBit (r + twopow k) =
      bxor (rdiag (r + twopow k) t0) (rdiag r t0) := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (r + twopow k) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, bxor_eq_xor]
    have d1 : decide (r + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (r + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show r + twopow k - twopow k = r by omega,
      row_testBit t0 (r + twopow k), row_testBit t0 r]
  have hc2 : (phiScale k (carry (row t0))).testBit ((r + 1) + twopow k) =
      ((rdiag ((r + 1) + twopow k) t0 && rdiag (r + twopow k) t0) ^^
        (rdiag (r + 1) t0 && rdiag r t0)) := by
    change (((carry (row t0)) ^^^ ((carry (row t0)) <<< twopow k)) ^^^
      ((carry (row t0)) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show (r + 1) + twopow k - twopow k = r + 1 by omega,
      show (r + 1) + twopow k = (r + twopow k) + 1 by omega,
      carry_row_testBit_succ t0 (r + twopow k), carry_row_testBit_succ t0 r,
      show (r + twopow k) + 1 = (r + 1) + twopow k by omega]
  rw [hc1, hs1, hs2, hc2]
  simp only [bxor_eq_xor]
  cases rdiag ((r + 1) + twopow k) t0 <;>
    cases rdiag (r + twopow k) t0 <;>
    cases rdiag (r + 1) t0 <;>
    cases rdiag r t0 <;> rfl

/-- **Sector-1 `frobDefect` folded by `restart` uniformly in `u : Nat` (`frobDefect_row_sector_one_restart`)**: for `d + 1 ≤ k` and every multiple `u : Nat`, at `t0 = (d + 1) + u * 2^k`, `restart` folds `rdiag (d + 1) t0 = center (d + 1)` and `rdiag d t0 = rdiag d (d + 1)` in bit `(d + 1) + 2^k` of `frobDefect k (row ((d + 1) + u * 2^k))`. -/
theorem frobDefect_row_sector_one_restart (d k u : Nat) (hk : d + 1 ≤ k) :
    (frobDefect k (row ((d + 1) + u * twopow k))).testBit ((d + 1) + twopow k) =
      bxor
        (rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k) && rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) && rdiag (d + twopow k) ((d + 1) + u * twopow k)) := by
  have hlt : d + 1 < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  rw [frobDefect_row_testBit_sector_one ((d + 1) + u * twopow k) k d hlt,
    rdiag_restart k d u (d + 1) (by omega),
    center_restart_rdiag k (d + 1) u hk]

/-- **Sector-2 `frobDefect` folded by `restart` uniformly in `u : Nat` (`frobDefect_row_sector_two_restart`)**: for `d + 1 ≤ k` and every multiple `u : Nat`, at `t0 = (d + 1) + u * 2^k`, `restart` folds `rdiag (d + 1) t0 = center (d + 1)` and `rdiag d t0 = rdiag d (d + 1)` in bit `(d + 1) + 2^(k+1)` of `frobDefect k (row ((d + 1) + u * 2^k))`. -/
theorem frobDefect_row_sector_two_restart (d k u : Nat) (hk : d + 1 ≤ k) :
    (frobDefect k (row ((d + 1) + u * twopow k))).testBit (((d + 1) + twopow k) + twopow k) =
      bxor
        (bxor
          (rdiag ((d + 1) + twopow (k + 1)) ((d + 1) + u * twopow k) &&
            bxor (rdiag (d + twopow k) ((d + 1) + u * twopow k)) (rdiag d (d + 1)))
          (rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k) &&
            bxor (rdiag (d + twopow (k + 1)) ((d + 1) + u * twopow k)) (rdiag d (d + 1))))
        (Rule30UOR.Core.center (d + 1) &&
          bxor (rdiag (d + twopow (k + 1)) ((d + 1) + u * twopow k))
            (rdiag (d + twopow k) ((d + 1) + u * twopow k))) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hf := frobDefect_row_testBit_outside_cone ((d + 1) + u * twopow k) k (d + twopow k) (by omega)
  rw [show d + twopow k + 1 + twopow k = ((d + 1) + twopow k) + twopow k by omega,
    show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by omega,
    show d + twopow k - twopow k = d by omega,
    show d + twopow k + 1 = (d + 1) + twopow k by omega,
    show d + twopow k + twopow k = d + twopow (k + 1) by omega,
    show (d + 1) + twopow k - twopow k = d + 1 by omega] at hf
  rw [show ((d + 1) + twopow k) + twopow k = (d + 1) + twopow (k + 1) by omega, hf,
    rdiag_restart k d u (d + 1) (by omega),
    center_restart_rdiag k (d + 1) u hk]

/-- **Sector-2 Wronskian of `frobDefect k (winWitt t0 (2^k))` from `R_periodic` (`frobDefect_winWitt_sector_two_wronskian`)**: for every `t0`, `k`, and `r` with `r + 1 ≤ k`, because bits `r` and `r + 1` of `winWitt t0 (2^k)` vanish by `R_periodic` (`winWitt_testBit_low`), bit `(r + 1) + 2^(k+1)` of `frobDefect k (winWitt t0 (2^k))` collapses to the `2×2` Wronskian between Sector 2 and Sector 1 of `winWitt t0 (2^k)`. -/
theorem frobDefect_winWitt_sector_two_wronskian (t0 k r : Nat) (hr : r + 1 ≤ k) :
    (frobDefect k (winWitt t0 (twopow k))).testBit ((r + 1) + twopow (k + 1)) =
      bxor
        ((winWitt t0 (twopow k)).testBit ((r + 1) + twopow (k + 1)) &&
          (winWitt t0 (twopow k)).testBit (r + twopow k))
        ((winWitt t0 (twopow k)).testBit ((r + 1) + twopow k) &&
          (winWitt t0 (twopow k)).testBit (r + twopow (k + 1))) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hlt : k < twopow k := twopow_gt_self k
  let w := winWitt t0 (twopow k)
  have hw0 : w.testBit r = false := winWitt_testBit_low t0 k r (by omega)
  have hw1 : w.testBit (r + 1) = false := winWitt_testBit_low t0 k (r + 1) hr
  change (carry (phiScale k w) ^^^ phiScale k (carry w)).testBit ((r + 1) + twopow (k + 1)) =
    bxor
      (w.testBit ((r + 1) + twopow (k + 1)) && w.testBit (r + twopow k))
      (w.testBit ((r + 1) + twopow k) && w.testBit (r + twopow (k + 1)))
  simp only [Nat.testBit_xor, bxor_eq_xor]
  have hc1 : (carry (phiScale k w)).testBit ((r + 1) + twopow (k + 1)) =
      ((phiScale k w).testBit ((r + 1) + twopow (k + 1)) &&
        (phiScale k w).testBit (r + twopow (k + 1))) := by
    change ((phiScale k w) &&& ((phiScale k w) <<< 1)).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ 1) = true := decide_eq_true (by omega)
    rw [d1, Bool.true_and, show (r + 1) + twopow (k + 1) - 1 = r + twopow (k + 1) by omega]
  have hs1 : (phiScale k w).testBit ((r + 1) + twopow (k + 1)) =
      (w.testBit ((r + 1) + twopow (k + 1)) ^^ w.testBit ((r + 1) + twopow k)) := by
    change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow (k + 1) - twopow k = (r + 1) + twopow k by omega,
      show (r + 1) + twopow (k + 1) - (twopow k + twopow k) = r + 1 by omega,
      hw1, Bool.xor_false]
  have hs2 : (phiScale k w).testBit (r + twopow (k + 1)) =
      (w.testBit (r + twopow (k + 1)) ^^ w.testBit (r + twopow k)) := by
    change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit (r + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (r + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (r + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show r + twopow (k + 1) - twopow k = r + twopow k by omega,
      show r + twopow (k + 1) - (twopow k + twopow k) = r by omega,
      hw0, Bool.xor_false]
  have hc2 : (phiScale k (carry w)).testBit ((r + 1) + twopow (k + 1)) =
      ((w.testBit ((r + 1) + twopow (k + 1)) && w.testBit (r + twopow (k + 1))) ^^
        (w.testBit ((r + 1) + twopow k) && w.testBit (r + twopow k))) := by
    change (((carry w) ^^^ ((carry w) <<< twopow k)) ^^^
      ((carry w) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    have hcw2 : (carry w).testBit ((r + 1) + twopow (k + 1)) =
        (w.testBit ((r + 1) + twopow (k + 1)) && w.testBit (r + twopow (k + 1))) := by
      change (w &&& (w <<< 1)).testBit ((r + 1) + twopow (k + 1)) = _
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
      have d3 : decide ((r + 1) + twopow (k + 1) ≥ 1) = true := decide_eq_true (by omega)
      rw [d3, Bool.true_and, show (r + 1) + twopow (k + 1) - 1 = r + twopow (k + 1) by omega]
    have hcw1 : (carry w).testBit ((r + 1) + twopow k) =
        (w.testBit ((r + 1) + twopow k) && w.testBit (r + twopow k)) := by
      change (w &&& (w <<< 1)).testBit ((r + 1) + twopow k) = _
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
      have d3 : decide ((r + 1) + twopow k ≥ 1) = true := decide_eq_true (by omega)
      rw [d3, Bool.true_and, show (r + 1) + twopow k - 1 = r + twopow k by omega]
    have hcw0 : (carry w).testBit (r + 1) = false := by
      change (w &&& (w <<< 1)).testBit (r + 1) = false
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, hw1, Bool.false_and]
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow (k + 1) - twopow k = (r + 1) + twopow k by omega,
      show (r + 1) + twopow (k + 1) - (twopow k + twopow k) = r + 1 by omega,
      hcw2, hcw1, hcw0, Bool.xor_false]
  rw [hc1, hs1, hs2, hc2]
  cases w.testBit ((r + 1) + twopow (k + 1)) <;>
    cases w.testBit ((r + 1) + twopow k) <;>
    cases w.testBit (r + twopow (k + 1)) <;>
    cases w.testBit (r + twopow k) <;> rfl

/-- **Exact Sector-2 cross-carry equivariance inside the cone (`crossCarry_scale_row_winWitt_sector_two_cone_eq`)**: for `2 * t0 + 1 < 2^k` and `r + 1 ≤ k`, `(crossCarry (phiScale (k + 1) (row t0)) (phiScale k w)).testBit ((r + 1) + 2^(k+1))` equals `(phiScale k (crossCarry (phiScale k (row t0)) w)).testBit ((r + 1) + 2^(k+1))`. -/
theorem crossCarry_scale_row_winWitt_sector_two_cone_eq (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    (crossCarry (phiScale (k + 1) (row t0)) (phiScale k (winWitt t0 (twopow k)))).testBit
        ((r + 1) + twopow (k + 1)) =
      (phiScale k (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)))).testBit
        ((r + 1) + twopow (k + 1)) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hlt : k < twopow k := twopow_gt_self k
  let w := winWitt t0 (twopow k)
  have hw0 : w.testBit r = false := winWitt_testBit_low t0 k r (by omega)
  have hw1 : w.testBit (r + 1) = false := winWitt_testBit_low t0 k (r + 1) hr
  have hr_hi1 : (row t0).testBit ((r + 1) + twopow k) = false := by
    rw [row_testBit]; exact rdiag_gt_two_mul t0 ((r + 1) + twopow k) (by omega)
  have hr_hi0 : (row t0).testBit (r + twopow k) = false := by
    rw [row_testBit]; exact rdiag_gt_two_mul t0 (r + twopow k) (by omega)
  have hr_hi2 : (row t0).testBit ((r + 1) + twopow (k + 1)) = false := by
    rw [row_testBit]; exact rdiag_gt_two_mul t0 ((r + 1) + twopow (k + 1)) (by omega)
  have hr_hi3 : (row t0).testBit (r + twopow (k + 1)) = false := by
    rw [row_testBit]; exact rdiag_gt_two_mul t0 (r + twopow (k + 1)) (by omega)
  have hs_k1_1 : (phiScale (k + 1) (row t0)).testBit ((r + 1) + twopow (k + 1)) =
      (row t0).testBit (r + 1) := by
    change (((row t0) ^^^ ((row t0) <<< twopow (k + 1))) ^^^
      ((row t0) <<< (twopow (k + 1) + twopow (k + 1)))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ twopow (k + 1)) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow (k + 1) ≥ twopow (k + 1) + twopow (k + 1)) = false :=
      decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show (r + 1) + twopow (k + 1) - twopow (k + 1) = r + 1 by omega,
      hr_hi2, Bool.false_xor]
  have hs_k1_0 : (phiScale (k + 1) (row t0)).testBit (r + twopow (k + 1)) =
      (row t0).testBit r := by
    change (((row t0) ^^^ ((row t0) <<< twopow (k + 1))) ^^^
      ((row t0) <<< (twopow (k + 1) + twopow (k + 1)))).testBit (r + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (r + twopow (k + 1) ≥ twopow (k + 1)) = true := decide_eq_true (by omega)
    have d2 : decide (r + twopow (k + 1) ≥ twopow (k + 1) + twopow (k + 1)) = false :=
      decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show r + twopow (k + 1) - twopow (k + 1) = r by omega,
      hr_hi3, Bool.false_xor]
  have hs_k_21 : (phiScale k (row t0)).testBit ((r + 1) + twopow (k + 1)) =
      (row t0).testBit (r + 1) := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow (k + 1) - twopow k = (r + 1) + twopow k by omega,
      show (r + 1) + twopow (k + 1) - (twopow k + twopow k) = r + 1 by omega,
      hr_hi2, hr_hi1, Bool.false_xor, Bool.false_xor]
  have hs_k_20 : (phiScale k (row t0)).testBit (r + twopow (k + 1)) =
      (row t0).testBit r := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (r + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (r + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (r + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show r + twopow (k + 1) - twopow k = r + twopow k by omega,
      show r + twopow (k + 1) - (twopow k + twopow k) = r by omega,
      hr_hi3, hr_hi0, Bool.false_xor, Bool.false_xor]
  have hs_k_11 : (phiScale k (row t0)).testBit ((r + 1) + twopow k) =
      (row t0).testBit (r + 1) := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show (r + 1) + twopow k - twopow k = r + 1 by omega,
      hr_hi1, Bool.false_xor]
  have hs_k_10 : (phiScale k (row t0)).testBit (r + twopow k) =
      (row t0).testBit r := by
    change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (r + twopow k) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (r + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (r + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show r + twopow k - twopow k = r by omega,
      hr_hi0, Bool.false_xor]
  have hsw1 : (phiScale k w).testBit ((r + 1) + twopow (k + 1)) =
      (w.testBit ((r + 1) + twopow (k + 1)) ^^ w.testBit ((r + 1) + twopow k)) := by
    change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow (k + 1) - twopow k = (r + 1) + twopow k by omega,
      show (r + 1) + twopow (k + 1) - (twopow k + twopow k) = r + 1 by omega,
      hw1, Bool.xor_false]
  have hsw0 : (phiScale k w).testBit (r + twopow (k + 1)) =
      (w.testBit (r + twopow (k + 1)) ^^ w.testBit (r + twopow k)) := by
    change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit (r + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (r + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (r + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show r + twopow (k + 1) - twopow k = r + twopow k by omega,
      show r + twopow (k + 1) - (twopow k + twopow k) = r by omega,
      hw0, Bool.xor_false]
  have hlhs : (crossCarry (phiScale (k + 1) (row t0)) (phiScale k w)).testBit ((r + 1) + twopow (k + 1)) =
      (((row t0).testBit (r + 1) && (w.testBit (r + twopow (k + 1)) ^^ w.testBit (r + twopow k))) ^^
        ((w.testBit ((r + 1) + twopow (k + 1)) ^^ w.testBit ((r + 1) + twopow k)) && (row t0).testBit r)) := by
    change (((phiScale (k + 1) (row t0)) &&& ((phiScale k w) <<< 1)) ^^^
      ((phiScale k w) &&& ((phiScale (k + 1) (row t0)) <<< 1))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ 1) = true := decide_eq_true (by omega)
    rw [d1, Bool.true_and, Bool.true_and, show (r + 1) + twopow (k + 1) - 1 = r + twopow (k + 1) by omega,
      hs_k1_1, hs_k1_0, hsw1, hsw0]
  have hrhs : (phiScale k (crossCarry (phiScale k (row t0)) w)).testBit ((r + 1) + twopow (k + 1)) =
      ((((row t0).testBit (r + 1) && w.testBit (r + twopow (k + 1))) ^^
        (w.testBit ((r + 1) + twopow (k + 1)) && (row t0).testBit r)) ^^
      (((row t0).testBit (r + 1) && w.testBit (r + twopow k)) ^^
        (w.testBit ((r + 1) + twopow k) && (row t0).testBit r))) := by
    let C := crossCarry (phiScale k (row t0)) w
    change ((C ^^^ (C <<< twopow k)) ^^^ (C <<< (twopow k + twopow k))).testBit ((r + 1) + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    have hC2 : C.testBit ((r + 1) + twopow (k + 1)) =
        (((row t0).testBit (r + 1) && w.testBit (r + twopow (k + 1))) ^^
          (w.testBit ((r + 1) + twopow (k + 1)) && (row t0).testBit r)) := by
      change (((phiScale k (row t0)) &&& (w <<< 1)) ^^^
        (w &&& ((phiScale k (row t0)) <<< 1))).testBit ((r + 1) + twopow (k + 1)) = _
      simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
      have d3 : decide ((r + 1) + twopow (k + 1) ≥ 1) = true := decide_eq_true (by omega)
      rw [d3, Bool.true_and, Bool.true_and, show (r + 1) + twopow (k + 1) - 1 = r + twopow (k + 1) by omega,
        hs_k_21, hs_k_20]
    have hC1 : C.testBit ((r + 1) + twopow k) =
        (((row t0).testBit (r + 1) && w.testBit (r + twopow k)) ^^
          (w.testBit ((r + 1) + twopow k) && (row t0).testBit r)) := by
      change (((phiScale k (row t0)) &&& (w <<< 1)) ^^^
        (w &&& ((phiScale k (row t0)) <<< 1))).testBit ((r + 1) + twopow k) = _
      simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
      have d3 : decide ((r + 1) + twopow k ≥ 1) = true := decide_eq_true (by omega)
      rw [d3, Bool.true_and, Bool.true_and, show (r + 1) + twopow k - 1 = r + twopow k by omega,
        hs_k_11, hs_k_10]
    have hC0 : C.testBit (r + 1) = false := by
      change (((phiScale k (row t0)) &&& (w <<< 1)) ^^^
        (w &&& ((phiScale k (row t0)) <<< 1))).testBit (r + 1) = false
      simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
      have d3 : decide (r + 1 ≥ 1) = true := decide_eq_true (by omega)
      rw [d3, Bool.true_and, Bool.true_and, show r + 1 - 1 = r by omega, hw0, hw1,
        Bool.and_false, Bool.false_and, Bool.xor_self]
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow (k + 1) - twopow k = (r + 1) + twopow k by omega,
      show (r + 1) + twopow (k + 1) - (twopow k + twopow k) = r + 1 by omega,
      hC2, hC1, hC0, Bool.xor_false]
  rw [hlhs, hrhs]
  cases (row t0).testBit (r + 1) <;>
    cases (row t0).testBit r <;>
    cases w.testBit ((r + 1) + twopow (k + 1)) <;>
    cases w.testBit ((r + 1) + twopow k) <;>
    cases w.testBit (r + twopow (k + 1)) <;>
    cases w.testBit (r + twopow k) <;> rfl

/-- **Exact Sector-2 identity between late row Frobenius defect and in-cone window Frobenius defect (`frobDefect_row_late_eq_frobDefect_winWitt_sector_two`)**: for `2 * t0 + 1 < 2^k` and `r + 1 ≤ k`, combining `frobDefect = 0` inside the cone (`frobDefect_row_late_from_cone`) with `R_periodic` (`crossCarry_scale_row_winWitt_sector_two_cone_eq`) proves that `(frobDefect k (row (t0 + 2^k))).testBit ((r + 1) + 2^(k+1))` equals `(frobDefect k (winWitt t0 (2^k))).testBit ((r + 1) + 2^(k+1))`. -/
theorem frobDefect_row_late_eq_frobDefect_winWitt_sector_two (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    (frobDefect k (row (t0 + twopow k))).testBit ((r + 1) + twopow (k + 1)) =
      (frobDefect k (winWitt t0 (twopow k))).testBit ((r + 1) + twopow (k + 1)) := by
  have hlate := congrArg (fun n => n.testBit ((r + 1) + twopow (k + 1)))
    (frobDefect_row_late_from_cone t0 k hcone)
  simp only [Nat.testBit_xor] at hlate
  rw [hlate, crossCarry_scale_row_winWitt_sector_two_cone_eq t0 k r hcone hr]
  cases (frobDefect k (winWitt t0 (twopow k))).testBit ((r + 1) + twopow (k + 1)) <;>
    cases (phiScale k (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)))).testBit ((r + 1) + twopow (k + 1)) <;> rfl

/-- **Late row Frobenius defect equals the in-cone window Sector-2 Wronskian (`frobDefect_row_late_eq_winWitt_sector_two_wronskian`)**: for `2 * t0 + 1 < 2^k` and `r + 1 ≤ k`, bit `(r + 1) + 2^(k+1)` of `frobDefect k (row (t0 + 2^k))` equals the `2×2` Wronskian between Sector 2 and Sector 1 of the in-cone window `winWitt t0 (2^k)`. -/
theorem frobDefect_row_late_eq_winWitt_sector_two_wronskian (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    (frobDefect k (row (t0 + twopow k))).testBit ((r + 1) + twopow (k + 1)) =
      bxor
        ((winWitt t0 (twopow k)).testBit ((r + 1) + twopow (k + 1)) &&
          (winWitt t0 (twopow k)).testBit (r + twopow k))
        ((winWitt t0 (twopow k)).testBit ((r + 1) + twopow k) &&
          (winWitt t0 (twopow k)).testBit (r + twopow (k + 1))) := by
  rw [frobDefect_row_late_eq_frobDefect_winWitt_sector_two t0 k r hcone hr,
    frobDefect_winWitt_sector_two_wronskian t0 k r hr]

/-- **Equivalence of left-wing column `-2^k` defect and `response · k` defect under `CenterPeriodic` (`periodic_ldiag_shift_mul_eq_response_shift_mul`)**: under `CenterPeriodic T P`, for every multiple `m`, scale `k`, and `t ≥ max(T, 2^k)`, the `m * P`-shift defect of `ldiag (t - 2^k) t` (`= cell t (-2^k)`) equals the `m * P`-shift defect of `response t k`. -/
theorem periodic_ldiag_shift_mul_eq_response_shift_mul
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hk : twopow k ≤ t) :
    bxor (ldiag ((t + m * P) - twopow k) (t + m * P)) (ldiag (t - twopow k) t) =
      bxor (Rule30UOR.Scale.response (t + m * P) k) (Rule30UOR.Scale.response t k) := by
  have hs1 := Rule30UOR.Scale.periodic_scale_paper T P hP h k t ht
  have hs2 := Rule30UOR.Scale.periodic_scale_paper T P hP h k (t + m * P) (by omega)
  have hl1 : Rule30UOR.Core.cell t (Rule30UOR.Scale.negpow k) = ldiag (t - twopow k) t := by
    have h0 := ldiag_eq_cell_neg (t - twopow k) (twopow k)
    rw [show t - twopow k + twopow k = t by omega] at h0
    exact h0.symm
  have hl2 : Rule30UOR.Core.cell (t + m * P) (Rule30UOR.Scale.negpow k) =
      ldiag ((t + m * P) - twopow k) (t + m * P) := by
    have h0 := ldiag_eq_cell_neg ((t + m * P) - twopow k) (twopow k)
    rw [show (t + m * P) - twopow k + twopow k = t + m * P by omega] at h0
    exact h0.symm
  have hc0 : Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t :=
    Rule30UOR.Scale.center_mul h m t ht
  have hc1 : Rule30UOR.Core.center ((t + m * P) + Rule30UOR.Scale.lag P k) =
      Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k) := by
    rw [show (t + m * P) + Rule30UOR.Scale.lag P k = (t + Rule30UOR.Scale.lag P k) + m * P by omega]
    exact Rule30UOR.Scale.center_mul h m (t + Rule30UOR.Scale.lag P k) (by omega)
  rw [hl1] at hs1
  rw [hl2, hc0, hc1, ← hs1] at hs2
  revert hs2
  simp only [bxor_eq_xor]
  cases ldiag ((t + m * P) - twopow k) (t + m * P) <;>
    cases ldiag (t - twopow k) t <;>
    cases Rule30UOR.Scale.response (t + m * P) k <;>
    cases Rule30UOR.Scale.response t k <;> decide

/-- **Refutation of Target 2 (`not_periodic_maskparity_zero_mul`)**: under `CenterPeriodic T P` (`0 < P`), for every threshold `T'` and every positive multiple `m > 0`, `maskparity (t + m * P) 0 = maskparity t 0` cannot hold for all `t ≥ T'` (refuted by `masked_jen_center`). -/
theorem not_periodic_maskparity_zero_mul
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (T' m : Nat) (hm : 0 < m)
    (hmask : ∀ t, T' ≤ t →
      Rule30UOR.Scale.maskparity ((t + 1) + m * P) 0 = Rule30UOR.Scale.maskparity (t + 1) 0) :
    False := by
  have hmP : 0 < m * P := Nat.mul_pos hm hP
  have hper_mP : Rule30UOR.Scale.CenterPeriodic (max T T') (m * P) := by
    intro t ht
    exact Rule30UOR.Scale.center_mul h m t (by omega)
  have hmasked : Rule30UOR.Right.MaskedPer (max T T') (m * P) :=
    (maskedPer_iff_maskparity_zero_periodic (max T T') (m * P) hper_mP).2
      (fun s hs => hmask s (by omega))
  refine Ruliology.CellularAutomata.Rule30MaskedJen.masked_jen 0 (T := max T T' + 1) hmP
    (fun t ht => by
      have hc := hper_mP t (by omega)
      rwa [Rule30UOR.Scale.center_eq_kit, Rule30UOR.Scale.center_eq_kit] at hc)
    (fun t ht hw => ?_)
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hw' : rdiag (s + 1) (s + 1) = false := by
    have hc : Rule30UOR.Core.center (s + 1) = false := by
      rw [Rule30UOR.Scale.center_eq_kit]; exact hw
    rwa [core_center_eq_rcenter] at hc
  have hm_eq := hmasked s (by omega) hw'
  rw [show (0 : Int) + 1 = 1 by rfl, show s + 1 + m * P = (s + m * P) + 1 by omega,
    Rule30UOR.Right.col1_readout, Rule30UOR.Right.col1_readout, hm_eq]

/-- **Refutation of Target 1 (`not_periodic_colm1_mul`)**: under `CenterPeriodic T P` (`0 < P`), for every threshold `T'` and every positive multiple `m > 0`, column `-1` (`ldiag t (t + 1)`) cannot have period `m * P` from `T'` (refuted by `not_adjacent (-1)` / `col_neg_one_not_periodic`). -/
theorem not_periodic_colm1_mul
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (T' m : Nat) (hm : 0 < m)
    (hcol : ∀ t, T' ≤ t → ldiag (t + m * P) ((t + 1) + m * P) = ldiag t (t + 1)) :
    False := by
  refine not_periodic_maskparity_zero_mul T P hP h (max T T') m hm (fun t ht => ?_)
  have hdef := periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul T P hP h m t (by omega)
  have hcol' : ldiag (t + m * P) ((t + m * P) + 1) = ldiag t (t + 1) := by
    rw [show (t + m * P) + 1 = (t + 1) + m * P by omega]
    exact hcol t (by omega)
  rw [hcol', bxor_eq_xor, bxor_eq_xor, Bool.xor_self] at hdef
  rw [show (t + 1) + m * P = (t + m * P) + 1 by omega]
  revert hdef
  cases Rule30UOR.Scale.maskparity ((t + m * P) + 1) 0 <;>
    cases Rule30UOR.Scale.maskparity (t + 1) 0 <;> decide

/-- Predicate for Target 1: column `-1` (`ldiag t (t + 1)`) is `Q`-periodic from `T'` on (`∀ t ≥ T', ldiag (t + Q) ((t + 1) + Q) = ldiag t (t + 1)`). -/
def ColNegOnePeriodic (T' Q : Nat) : Prop :=
  ∀ t, T' ≤ t → ldiag (t + Q) ((t + 1) + Q) = ldiag t (t + 1)

theorem not_periodic_maskparity_zero_mul_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (T' m : Nat) (hm : 0 < m) :
    ¬ MaskParityZeroPeriodic T' (m * P) :=
  not_periodic_maskparity_zero_mul T P hP h T' m hm

theorem not_periodic_colm1_mul_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (T' m : Nat) (hm : 0 < m) :
    ¬ ColNegOnePeriodic T' (m * P) :=
  not_periodic_colm1_mul T P hP h T' m hm

/-- **Sector-1 Identity of Late-Row Scaled Copy (`phiScale_row_late_sector_one_eq_winWitt_cone`)**: for `2 * t0 + 1 < 2^k` and `j ≤ k`, combining `R_periodic` (`winWitt_testBit_low`) with `row_scale` shows that bit `j + 2^k` of `phiScale k (row (t0 + 2^k))` is identically equal to bit `j + 2^k` of the in-cone window `winWitt t0 (2^k)`. -/
theorem phiScale_row_late_sector_one_eq_winWitt_cone (t0 k j : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hj : j ≤ k) :
    (phiScale k (row (t0 + twopow k))).testBit (j + twopow k) =
      (winWitt t0 (twopow k)).testBit (j + twopow k) := by
  have hj_lt : j < twopow k := Nat.lt_of_le_of_lt hj (twopow_gt_self k)
  rw [row_scale t0 k, phiScale_xor, phiScale_scale, Nat.testBit_xor]
  have h1 : (phiScale (k + 1) (row t0)).testBit (j + twopow k) = false := by
    change (((row t0) ^^^ ((row t0) <<< twopow (k + 1))) ^^^
      ((row t0) <<< (twopow (k + 1) + twopow (k + 1)))).testBit (j + twopow k) = false
    have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (j + twopow k ≥ twopow (k + 1)) = false := decide_eq_false (by omega)
    have d2 : decide (j + twopow k ≥ twopow (k + 1) + twopow (k + 1)) = false :=
      decide_eq_false (by omega)
    rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false,
      row_testBit, rdiag_gt_two_mul t0 (j + twopow k) (by omega)]
  have h2 : (phiScale k (winWitt t0 (twopow k))).testBit (j + twopow k) =
      (winWitt t0 (twopow k)).testBit (j + twopow k) := by
    let w := winWitt t0 (twopow k)
    change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit (j + twopow k) =
      w.testBit (j + twopow k)
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (j + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (j + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show j + twopow k - twopow k = j by omega,
      winWitt_testBit_low t0 k j hj, Bool.xor_false]
  rw [h1, h2, Bool.false_xor]

/-- **Exact Sector-1 Late-Row Frobenius Defect as In-Cone Cross-Carry (`frobDefect_row_late_sector_one_eq_crossCarry_cone`)**: for `2 * t0 + 1 < 2^k` and `r + 1 ≤ k`, combining `δ_k = 0` inside the cone (`frobDefect_row_late_from_cone`) with `R_periodic` (`winWitt_testBit_low`) shows that bit `(r + 1) + 2^k` of `frobDefect k (row (t0 + 2^k))` is identically equal to bit `(r + 1) + 2^k` of the in-cone cross-carry `crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))`. -/
theorem frobDefect_row_late_sector_one_eq_crossCarry_cone (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    (frobDefect k (row (t0 + twopow k))).testBit ((r + 1) + twopow k) =
      (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit ((r + 1) + twopow k) := by
  have hr_lt : r + 1 < twopow k := Nat.lt_of_le_of_lt hr (twopow_gt_self k)
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [frobDefect_row_late_from_cone t0 k hcone]
  simp only [Nat.testBit_xor]
  let w := winWitt t0 (twopow k)
  have hw0 : w.testBit r = false := winWitt_testBit_low t0 k r (by omega)
  have hw1 : w.testBit (r + 1) = false := winWitt_testBit_low t0 k (r + 1) hr
  have hdf : (frobDefect k w).testBit ((r + 1) + twopow k) = false := by
    change (carry (phiScale k w) ^^^ phiScale k (carry w)).testBit ((r + 1) + twopow k) = false
    simp only [Nat.testBit_xor]
    have hc1 : (carry (phiScale k w)).testBit ((r + 1) + twopow k) =
        ((phiScale k w).testBit ((r + 1) + twopow k) && (phiScale k w).testBit (r + twopow k)) := by
      change ((phiScale k w) &&& ((phiScale k w) <<< 1)).testBit ((r + 1) + twopow k) = _
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
      have d0 : decide ((r + 1) + twopow k ≥ 1) = true := decide_eq_true (by omega)
      rw [d0, Bool.true_and, show (r + 1) + twopow k - 1 = r + twopow k by omega]
    have hs1 : (phiScale k w).testBit ((r + 1) + twopow k) = w.testBit ((r + 1) + twopow k) := by
      change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) = _
      simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
      have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
      rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
        show (r + 1) + twopow k - twopow k = r + 1 by omega, hw1, Bool.xor_false]
    have hs0 : (phiScale k w).testBit (r + twopow k) = w.testBit (r + twopow k) := by
      change ((w ^^^ (w <<< twopow k)) ^^^ (w <<< (twopow k + twopow k))).testBit (r + twopow k) = _
      simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have d1 : decide (r + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
      have d2 : decide (r + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
      rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
        show r + twopow k - twopow k = r by omega, hw0, Bool.xor_false]
    have hc2 : (phiScale k (carry w)).testBit ((r + 1) + twopow k) =
        (w.testBit ((r + 1) + twopow k) && w.testBit (r + twopow k)) := by
      change (((carry w) ^^^ ((carry w) <<< twopow k)) ^^^
        ((carry w) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) = _
      simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
      have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
      have hcw1 : (carry w).testBit ((r + 1) + twopow k) =
          (w.testBit ((r + 1) + twopow k) && w.testBit (r + twopow k)) := by
        change (w &&& (w <<< 1)).testBit ((r + 1) + twopow k) = _
        simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
        have d3 : decide ((r + 1) + twopow k ≥ 1) = true := decide_eq_true (by omega)
        rw [d3, Bool.true_and, show (r + 1) + twopow k - 1 = r + twopow k by omega]
      have hcw0 : (carry w).testBit (r + 1) = false := by
        change (w &&& (w <<< 1)).testBit (r + 1) = false
        simp only [Nat.testBit_and, Nat.testBit_shiftLeft, hw1, Bool.false_and]
      rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
        show (r + 1) + twopow k - twopow k = r + 1 by omega, hcw1, hcw0, Bool.xor_false]
    rw [hc1, hs1, hs0, hc2, Bool.xor_self]
  have hcc1 : (crossCarry (phiScale (k + 1) (row t0)) (phiScale k w)).testBit
      ((r + 1) + twopow k) = false := by
    have hs1 : (phiScale (k + 1) (row t0)).testBit ((r + 1) + twopow k) = false := by
      change (((row t0) ^^^ ((row t0) <<< twopow (k + 1))) ^^^
        ((row t0) <<< (twopow (k + 1) + twopow (k + 1)))).testBit ((r + 1) + twopow k) = false
      simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have d1 : decide ((r + 1) + twopow k ≥ twopow (k + 1)) = false := decide_eq_false (by omega)
      have d2 : decide ((r + 1) + twopow k ≥ twopow (k + 1) + twopow (k + 1)) = false :=
        decide_eq_false (by omega)
      rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false,
        row_testBit, rdiag_gt_two_mul t0 ((r + 1) + twopow k) (by omega)]
    have hs0 : (phiScale (k + 1) (row t0)).testBit (r + twopow k) = false := by
      change (((row t0) ^^^ ((row t0) <<< twopow (k + 1))) ^^^
        ((row t0) <<< (twopow (k + 1) + twopow (k + 1)))).testBit (r + twopow k) = false
      simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have d1 : decide (r + twopow k ≥ twopow (k + 1)) = false := decide_eq_false (by omega)
      have d2 : decide (r + twopow k ≥ twopow (k + 1) + twopow (k + 1)) = false :=
        decide_eq_false (by omega)
      rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false,
        row_testBit, rdiag_gt_two_mul t0 (r + twopow k) (by omega)]
    change (((phiScale (k + 1) (row t0)) &&& ((phiScale k w) <<< 1)) ^^^
      ((phiScale k w) &&& ((phiScale (k + 1) (row t0)) <<< 1))).testBit ((r + 1) + twopow k) = false
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
    have d0 : decide ((r + 1) + twopow k ≥ 1) = true := decide_eq_true (by omega)
    rw [d0, Bool.true_and, Bool.true_and,
      show (r + 1) + twopow k - 1 = r + twopow k by omega,
      hs1, hs0, Bool.false_and, Bool.and_false, Bool.xor_self]
  have hcc2 : (phiScale k (crossCarry (phiScale k (row t0)) w)).testBit ((r + 1) + twopow k) =
      (crossCarry (phiScale k (row t0)) w).testBit ((r + 1) + twopow k) := by
    let c := crossCarry (phiScale k (row t0)) w
    have hc0 : c.testBit (r + 1) = false := by
      change (((phiScale k (row t0)) &&& (w <<< 1)) ^^^
        (w &&& ((phiScale k (row t0)) <<< 1))).testBit (r + 1) = false
      simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
      have d0 : decide (r + 1 ≥ 1) = true := decide_eq_true (by omega)
      rw [d0, Bool.true_and, Bool.true_and, show r + 1 - 1 = r by omega,
        hw0, hw1, Bool.and_false, Bool.false_and, Bool.xor_self]
    change ((c ^^^ (c <<< twopow k)) ^^^ (c <<< (twopow k + twopow k))).testBit
      ((r + 1) + twopow k) = c.testBit ((r + 1) + twopow k)
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false :=
      decide_eq_false (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
      show (r + 1) + twopow k - twopow k = r + 1 by omega, hc0, Bool.xor_false]
  rw [hdf, hcc1, hcc2, Bool.false_xor, Bool.false_xor]

/-- **Exact Wronskian of `(center, rdiag)` in Sector 1 of Late-Row Frobenius Defect (`frobDefect_row_late_sector_one_center_slot_wronskian`)**: for `d + 1 ≤ k`, bit `(d + 1) + 2^k` of `frobDefect k (row ((d + 1) + 2^k))` is the exact `2 × 2` Wronskian `(center ((d + 1) + 2^k) && rdiag d (d + 1)) ⊕ (center (d + 1) && rdiag (d + 2^k) ((d + 1) + 2^k))`. -/
theorem frobDefect_row_late_sector_one_center_slot_wronskian (d k : Nat) (hk : d + 1 ≤ k) :
    (frobDefect k (row ((d + 1) + twopow k))).testBit ((d + 1) + twopow k) =
      bxor
        (Rule30UOR.Core.center ((d + 1) + twopow k) && rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) && rdiag (d + twopow k) ((d + 1) + twopow k)) := by
  have h1 := frobDefect_row_sector_one_restart d k 1 hk
  simp only [Nat.one_mul] at h1
  have hc_late : rdiag ((d + 1) + twopow k) ((d + 1) + twopow k) =
      Rule30UOR.Core.center ((d + 1) + twopow k) := by
    rw [core_center_eq_rcenter]; rfl
  rw [hc_late] at h1
  exact h1

/-- **In-Cone Sector-2 Cross-Carry at a White Center (`crossCarry_row_winWitt_sector_two_center_slot`)**: for `d + 1 ≤ k`, `SettledAt (d + 1) k`, and `center (d + 1) = false`, bit `(d + 1) + 2^(k+1)` of the in-cone cross-carry `crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (2^k))` equals `zcenter (d + 1) && maskparity (d + 1) 0` (independent of `k`). -/
theorem crossCarry_row_winWitt_sector_two_center_slot (d k : Nat)
    (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hc : Rule30UOR.Core.center (d + 1) = false) :
    ZCenterAndEq (d + 1) (Rule30UOR.Scale.maskparity (d + 1) 0)
      ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit
        ((d + 1) + twopow (k + 1))) := by
  unfold ZCenterAndEq
  have hd_pos : 0 < d := by
    rcases d with _ | d
    · exact absurd hc (by decide)
    · omega
  have hlt2 : k + 2 ≤ twopow k := by
    have hge2 : 2 ≤ k := by omega
    clear hk hset hc hd_pos d
    induction k with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have hm1 : m = 1 := by omega
        subst hm1; decide
      · have ihm := ih hm
        have hstepm : twopow (m + 1) = twopow m + twopow m := Rule30UOR.Core.twopow_succ m
        omega
  have hlt : k < twopow k := twopow_gt_self k
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hs1 : (phiScale k (row (d + 1))).testBit ((d + 1) + twopow (k + 1)) = false := by
    change (((row (d + 1)) ^^^ ((row (d + 1)) <<< twopow k)) ^^^
      ((row (d + 1)) <<< (twopow k + twopow k))).testBit ((d + 1) + twopow (k + 1)) = false
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((d + 1) + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide ((d + 1) + twopow (k + 1) ≥ twopow k + twopow k) = true :=
      decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show (d + 1) + twopow (k + 1) - twopow k = (d + 1) + twopow k by omega,
      show (d + 1) + twopow (k + 1) - (twopow k + twopow k) = d + 1 by omega,
      row_testBit (d + 1) ((d + 1) + twopow (k + 1)),
      row_testBit (d + 1) ((d + 1) + twopow k),
      row_testBit_center (d + 1),
      rdiag_gt_two_mul (d + 1) ((d + 1) + twopow (k + 1)) (by omega),
      rdiag_gt_two_mul (d + 1) ((d + 1) + twopow k) (by omega),
      hc]
    rfl
  have hs0 : (phiScale k (row (d + 1))).testBit (d + twopow (k + 1)) =
      Rule30UOR.Scale.maskparity (d + 1) 0 := by
    have hm1 : rdiag d (d + 1) = Rule30UOR.Scale.maskparity (d + 1) 0 := by
      have hm0 := maskparity_succ_zero_eq_rdiag d
      rw [← core_center_eq_rdiag (d + 1), hc, Bool.not_false, Bool.true_and] at hm0
      exact hm0.symm
    change (((row (d + 1)) ^^^ ((row (d + 1)) <<< twopow k)) ^^^
      ((row (d + 1)) <<< (twopow k + twopow k))).testBit (d + twopow (k + 1)) =
      Rule30UOR.Scale.maskparity (d + 1) 0
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (d + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (d + twopow (k + 1) ≥ twopow k + twopow k) = true :=
      decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show d + twopow (k + 1) - twopow k = d + twopow k by omega,
      show d + twopow (k + 1) - (twopow k + twopow k) = d by omega,
      row_testBit (d + 1) (d + twopow (k + 1)),
      row_testBit (d + 1) (d + twopow k),
      row_testBit (d + 1) d,
      rdiag_gt_two_mul (d + 1) (d + twopow (k + 1)) (by omega),
      rdiag_gt_two_mul (d + 1) (d + twopow k) (by omega),
      hm1, Bool.false_xor, Bool.false_xor]
  have hw1 : (winWitt (d + 1) (twopow k)).testBit ((d + 1) + twopow (k + 1)) =
      zcenter (d + 1) := by
    rw [winWitt_testBit_archimedean (d + 1) k hk, hc, bxor_eq_xor, Bool.false_xor]
    exact ldiag_settled_eq_zcenter (d + 1) k hk hset
  change (zcenter (d + 1) && Rule30UOR.Scale.maskparity (d + 1) 0) =
    (((phiScale k (row (d + 1)) &&& (winWitt (d + 1) (twopow k) <<< 1)) ^^^
      (winWitt (d + 1) (twopow k) &&& (phiScale k (row (d + 1)) <<< 1)))).testBit
      ((d + 1) + twopow (k + 1))
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  have d0 : decide ((d + 1) + twopow (k + 1) ≥ 1) = true := decide_eq_true (by omega)
  rw [d0, Bool.true_and, Bool.true_and,
    show (d + 1) + twopow (k + 1) - 1 = d + twopow (k + 1) by omega,
    hs1, hs0, hw1, Bool.false_and, Bool.false_xor]

/-! ### Paper-facing wrappers for Theorems 9.225–9.242 -/


theorem bit_frobDefect_row_lt_twopow_prop (t0 k j : Nat) (hj : j < twopow k) :
    BitFrobDefectEq k (row t0) j false := by
  unfold BitFrobDefectEq
  rw [bit_eq_bton_testBit, frobDefect_row_testBit_lt_twopow t0 k j hj]

theorem bit_frobDefect_row_sector_one_prop (t0 k r : Nat) (hr : r + 1 < twopow k) :
    BitFrobDefectEq k (row t0) ((r + 1) + twopow k)
      (bxor
        (rdiag ((r + 1) + twopow k) t0 && rdiag r t0)
        (rdiag (r + 1) t0 && rdiag (r + twopow k) t0)) := by
  unfold BitFrobDefectEq
  rw [bit_eq_bton_testBit, frobDefect_row_testBit_sector_one t0 k r hr]

theorem bit_frobDefect_row_sector_one_restart_prop (d k u : Nat) (hk : d + 1 ≤ k) :
    BitFrobDefectEq k (row ((d + 1) + u * twopow k)) ((d + 1) + twopow k)
      (bxor
        (rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k) && rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) && rdiag (d + twopow k) ((d + 1) + u * twopow k))) := by
  unfold BitFrobDefectEq
  rw [bit_eq_bton_testBit, frobDefect_row_sector_one_restart d k u hk]

theorem bit_frobDefect_row_sector_two_restart_prop (d k u : Nat) (hk : d + 1 ≤ k) :
    BitFrobDefectEq k (row ((d + 1) + u * twopow k)) (((d + 1) + twopow k) + twopow k)
      (bxor
        (bxor
          (rdiag ((d + 1) + twopow (k + 1)) ((d + 1) + u * twopow k) &&
            bxor (rdiag (d + twopow k) ((d + 1) + u * twopow k)) (rdiag d (d + 1)))
          (rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k) &&
            bxor (rdiag (d + twopow (k + 1)) ((d + 1) + u * twopow k)) (rdiag d (d + 1))))
        (Rule30UOR.Core.center (d + 1) &&
          bxor (rdiag (d + twopow (k + 1)) ((d + 1) + u * twopow k))
            (rdiag (d + twopow k) ((d + 1) + u * twopow k)))) := by
  unfold BitFrobDefectEq
  rw [bit_eq_bton_testBit, frobDefect_row_sector_two_restart d k u hk]

theorem bit_frobDefect_winWitt_sector_two_wronskian_prop (t0 k r : Nat) (hr : r + 1 ≤ k) :
    BitFrobDefectEq k (winWitt t0 (twopow k)) ((r + 1) + twopow (k + 1))
      (bxor
        (wittBitBool (winWitt t0 (twopow k)) ((r + 1) + twopow (k + 1)) &&
          wittBitBool (winWitt t0 (twopow k)) (r + twopow k))
        (wittBitBool (winWitt t0 (twopow k)) ((r + 1) + twopow k) &&
          wittBitBool (winWitt t0 (twopow k)) (r + twopow (k + 1)))) := by
  unfold BitFrobDefectEq wittBitBool
  rw [bit_eq_bton_testBit, frobDefect_winWitt_sector_two_wronskian t0 k r hr]

theorem bit_frobDefect_row_late_eq_frobDefect_winWitt_sector_two_prop (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    BitFrobDefectEq k (row (t0 + twopow k)) ((r + 1) + twopow (k + 1))
      (wittBitBool (frobDefect k (winWitt t0 (twopow k))) ((r + 1) + twopow (k + 1))) := by
  unfold BitFrobDefectEq wittBitBool
  rw [bit_eq_bton_testBit, frobDefect_row_late_eq_frobDefect_winWitt_sector_two t0 k r hcone hr]

theorem bit_frobDefect_row_late_eq_winWitt_sector_two_wronskian_prop (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    BitFrobDefectEq k (row (t0 + twopow k)) ((r + 1) + twopow (k + 1))
      (bxor
        (wittBitBool (winWitt t0 (twopow k)) ((r + 1) + twopow (k + 1)) &&
          wittBitBool (winWitt t0 (twopow k)) (r + twopow k))
        (wittBitBool (winWitt t0 (twopow k)) ((r + 1) + twopow k) &&
          wittBitBool (winWitt t0 (twopow k)) (r + twopow (k + 1)))) := by
  unfold BitFrobDefectEq wittBitBool
  rw [bit_eq_bton_testBit, frobDefect_row_late_eq_winWitt_sector_two_wronskian t0 k r hcone hr]

theorem phiScale_row_late_sector_one_eq_winWitt_cone_prop (t0 k j : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hj : j ≤ k) :
    wittBitBool (phiScale k (row (t0 + twopow k))) (j + twopow k) =
      wittBitBool (winWitt t0 (twopow k)) (j + twopow k) := by
  unfold wittBitBool
  exact phiScale_row_late_sector_one_eq_winWitt_cone t0 k j hcone hj

theorem bit_frobDefect_row_late_sector_one_eq_crossCarry_cone_prop (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    BitFrobDefectEq k (row (t0 + twopow k)) ((r + 1) + twopow k)
      (wittBitBool (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))) ((r + 1) + twopow k)) := by
  unfold BitFrobDefectEq wittBitBool
  rw [bit_eq_bton_testBit, frobDefect_row_late_sector_one_eq_crossCarry_cone t0 k r hcone hr]

theorem bit_frobDefect_row_late_sector_one_center_slot_wronskian_prop (d k : Nat) (hk : d + 1 ≤ k) :
    BitFrobDefectEq k (row ((d + 1) + twopow k)) ((d + 1) + twopow k)
      (bxor
        (Rule30UOR.Core.center ((d + 1) + twopow k) && rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) && rdiag (d + twopow k) ((d + 1) + twopow k))) := by
  unfold BitFrobDefectEq
  rw [bit_eq_bton_testBit, frobDefect_row_late_sector_one_center_slot_wronskian d k hk]

theorem crossCarry_scale_row_winWitt_sector_two_cone_eq_prop (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hr : r + 1 ≤ k) :
    wittBitBool (crossCarry (phiScale (k + 1) (row t0)) (phiScale k (winWitt t0 (twopow k))))
        ((r + 1) + twopow (k + 1)) =
      wittBitBool (phiScale k (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))))
        ((r + 1) + twopow (k + 1)) := by
  unfold wittBitBool
  exact crossCarry_scale_row_winWitt_sector_two_cone_eq t0 k r hcone hr

theorem crossCarry_row_winWitt_sector_two_center_slot_prop (d k : Nat)
    (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hc : Rule30UOR.Core.center (d + 1) = false) :
    ZCenterAndEq (d + 1) (Rule30UOR.Scale.maskparity (d + 1) 0)
      (wittBitBool (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)))
        ((d + 1) + twopow (k + 1))) := by
  unfold wittBitBool
  exact crossCarry_row_winWitt_sector_two_center_slot d k hk hset hc

end Rule30UOR.Interfaces
