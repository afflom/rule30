module

public import Rule30UOR.Interfaces.Part02

/-!
# `Rule30UOR.Interfaces`, part 3

* Applying Theorem 9.53 (`carry_xor`) to Theorem 9.12 (`row_scale`): Bilinear Cross-Carry and AND-Structure
* Outside-the-Cone Fixed-`k` Unbounded-`t0` Cross-Carry Laws (Theorem 9.152 Outside the Cone)
* Outside-the-Cone Cross-Carry at the Center Bit `(s + 1) + 2^k` (Theorem 9.152 Outside the Cone at the Center Slot)
* Fixed-`k` Unbounded-`t` Period-Shift Laws Outside the Cone (Masked-Jen Form)
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

/-! ### Applying Theorem 9.53 (`carry_xor`) to Theorem 9.12 (`row_scale`): Bilinear Cross-Carry and AND-Structure -/

/-- **Theorem 9.53 Applied to Theorem 9.12 (`carry_row_scale_decomp`)**: for every base time `t0` and scale `k`, the carry of the scaled row `row (t0 + 2^k) = phiScale k (row t0) ^^^ winWitt t0 (2^k)` decomposes into `carry (phiScale k (row t0)) ^^^ carry (winWitt t0 (2^k)) ^^^ crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))`. -/
theorem carry_row_scale_decomp (t0 k : Nat) :
    carry (row (t0 + twopow k)) =
      (carry (phiScale k (row t0)) ^^^ carry (winWitt t0 (twopow k))) ^^^
        crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) := by
  rw [row_scale t0 k, carry_xor]

/-- **Theorem 9.53 Applied to Theorem 9.12 Inside the Light Cone (`carry_row_scale_cone`)**: for `2 * t0 + 1 < 2^k`, `carry` commutes with `phiScale k` on `row t0`, so `carry (row (t0 + 2^k))` decomposes into `phiScale k (carry (row t0)) ^^^ carry (winWitt t0 (2^k)) ^^^ crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))`. -/
theorem carry_row_scale_cone (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    carry (row (t0 + twopow k)) =
      (phiScale k (carry (row t0)) ^^^ carry (winWitt t0 (twopow k))) ^^^
        crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) := by
  rw [carry_row_scale_decomp t0 k, carry_phiScale_row_cone t0 k hcone]

/-- **Exact AND-Structure of `carry` at Bit `j + 1` (`carry_testBit_succ`)**: for any Witt integer `y` and bit index `j`, `(carry y).testBit (j + 1) = y.testBit (j + 1) && y.testBit j`. -/
theorem carry_testBit_succ (y j : Nat) :
    (carry y).testBit (j + 1) = (y.testBit (j + 1) && y.testBit j) := by
  change (y &&& (y <<< 1)).testBit (j + 1) = (y.testBit (j + 1) && y.testBit j)
  simp [Nat.testBit_and, Nat.testBit_shiftLeft]

/-- **Exact Bilinear AND-Structure of `crossCarry` at Bit `j + 1` (`crossCarry_testBit_succ`)**: for any Witt integers `a, b` and bit index `j`, `(crossCarry a b).testBit (j + 1)` is the `F₂`-determinant `(a.testBit (j + 1) && b.testBit j) ⊕ (b.testBit (j + 1) && a.testBit j)`. -/
theorem crossCarry_testBit_succ (a b j : Nat) :
    (crossCarry a b).testBit (j + 1) =
      bxor (a.testBit (j + 1) && b.testBit j) (b.testBit (j + 1) && a.testBit j) := by
  change ((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))).testBit (j + 1) =
    bxor (a.testBit (j + 1) && b.testBit j) (b.testBit (j + 1) && a.testBit j)
  simp [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, bxor_eq_xor]

/-- **Pointwise Bit-LevelCarry Polarization (`carry_xor_testBit_succ`)**: at bit `j + 1`, `carry (a ^^^ b)` decomposes into `(a_{j+1} && a_j) ⊕ (b_{j+1} && b_j) ⊕ (a_{j+1} && b_j) ⊕ (b_{j+1} && a_j)`. -/
theorem carry_xor_testBit_succ (a b j : Nat) :
    (carry (a ^^^ b)).testBit (j + 1) =
      bxor (bxor (a.testBit (j + 1) && a.testBit j) (b.testBit (j + 1) && b.testBit j))
        (bxor (a.testBit (j + 1) && b.testBit j) (b.testBit (j + 1) && a.testBit j)) := by
  rw [carry_xor a b, Nat.testBit_xor, Nat.testBit_xor,
    carry_testBit_succ a j, carry_testBit_succ b j, crossCarry_testBit_succ a b j]
  simp only [bxor_eq_xor]

/-- **In Sector 1 (`r < 2^k`, `2 * t0 < r + 2^k`), `phiScale k (carry (row t0))` Reads `carry (row t0)`**: bit `(r + 1) + 2^k` of `phiScale k (carry (row t0))` equals `rdiag (r + 1) t0 && rdiag r t0`. -/
theorem phiScale_carry_row_testBit_sector_one (t0 k r : Nat) (hr : r + 1 < twopow k)
    (hcone : 2 * t0 < r + twopow k) :
    (phiScale k (carry (row t0))).testBit ((r + 1) + twopow k) =
      (rdiag (r + 1) t0 && rdiag r t0) := by
  change (((carry (row t0)) ^^^ ((carry (row t0)) <<< twopow k)) ^^^
      ((carry (row t0)) <<< (twopow k + twopow k))).testBit ((r + 1) + twopow k) =
    (rdiag (r + 1) t0 && rdiag r t0)
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide ((r + 1) + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide ((r + 1) + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  have hzero : (carry (row t0)).testBit ((r + 1) + twopow k) = false := by
    rw [show (r + 1) + twopow k = (r + twopow k) + 1 by omega,
      carry_row_testBit_succ t0 (r + twopow k),
      rdiag_gt_two_mul t0 ((r + twopow k) + 1) (by omega), Bool.false_and]
  rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
    show (r + 1) + twopow k - twopow k = r + 1 by omega,
    hzero, Bool.false_xor, carry_row_testBit_succ t0 r]

/-- **Sector-1 Center-Slot Cross-Carry Decomposition (`j = t0 + 2^k`, `2 * t0 + 1 < 2^k`)**: applying Theorem 9.53 to Theorem 9.12 at the center slot `j = t0 + 2^k` (`t0 + 1 < 2^k`) expresses `(crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit ((t0 + 1) + 2^k)` in terms of the late carry `rdiag (t0 + 1 + 2^k) (t0 + 2^k) && center (t0 + 2^k)`, the early carry `rdiag (t0 + 1) t0 && center t0`, and the window carry `(winWitt t0 (2^k)).testBit ((t0 + 1) + 2^k) && wittRespBool t0 k`. -/
theorem carry_row_scale_center_slot (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    (rdiag ((t0 + 1) + twopow k) (t0 + twopow k) && Rule30UOR.Core.center (t0 + twopow k)) =
      bxor (bxor (rdiag (t0 + 1) t0 && Rule30UOR.Core.center t0)
        ((winWitt t0 (twopow k)).testBit ((t0 + 1) + twopow k) && wittRespBool t0 k))
        ((crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k)) := by
  have hbit := congrArg (fun n => n.testBit ((t0 + 1) + twopow k)) (carry_row_scale_cone t0 k hcone)
  rw [Nat.testBit_xor, Nat.testBit_xor,
    show (t0 + 1) + twopow k = (t0 + twopow k) + 1 by omega,
    carry_row_testBit_succ (t0 + twopow k) (t0 + twopow k),
    ← core_center_eq_rdiag (t0 + twopow k)] at hbit
  rw [show (t0 + twopow k) + 1 = (t0 + 1) + twopow k by omega,
    phiScale_carry_row_testBit_sector_one t0 k t0 (by omega) (by omega),
    ← core_center_eq_rdiag t0] at hbit
  have hwc : (carry (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k) =
      ((winWitt t0 (twopow k)).testBit ((t0 + 1) + twopow k) && wittRespBool t0 k) := by
    rw [show (t0 + 1) + twopow k = (t0 + twopow k) + 1 by omega,
      carry_testBit_succ (winWitt t0 (twopow k)) (t0 + twopow k)]
    rfl
  rw [hwc] at hbit
  rw [hbit]
  simp only [bxor_eq_xor]

/-- **Direct Bilinear AND-Evaluation of `crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))` at the Center Slot (`j = t0 + 2^k`)**: for `t0 + 1 < 2^k` and `2 * t0 < t0 + 2^k` (`t0 < 2^k`), the cross-carry at bit `(t0 + 1) + 2^k` equals `(rdiag (t0 + 1) t0 && wittRespBool t0 k) ⊕ ((winWitt t0 (2^k)).testBit ((t0 + 1) + 2^k) && center t0)`. -/
theorem crossCarry_row_scale_center_slot_and (t0 k : Nat) (ht0 : t0 + 1 < twopow k) :
    (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k) =
      bxor (rdiag (t0 + 1) t0 && wittRespBool t0 k)
        ((winWitt t0 (twopow k)).testBit ((t0 + 1) + twopow k) && Rule30UOR.Core.center t0) := by
  rw [show (t0 + 1) + twopow k = (t0 + twopow k) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row t0)) (winWitt t0 (twopow k)) (t0 + twopow k),
    show (t0 + twopow k) + 1 = (t0 + 1) + twopow k by omega,
    phiScale_row_testBit_sector_one t0 k (t0 + 1) ht0 (by omega),
    phiScale_row_testBit_sector_one t0 k t0 (by omega) (by omega),
    ← core_center_eq_rdiag t0]
  rfl

/-- **Exact Cross-Carry Formula under `CenterPeriodic T P` at the Center Slot (`T ≤ t0`, `t0 + 1 < 2^k`)**: under `CenterPeriodic T P` (`0 < P`), the center-slot cross-carry `(crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit ((t0 + 1) + 2^k)` evaluates via the carry's AND-structure to `(rdiag (t0 + 1) t0 && (center (t0 + lag P k) ⊕ center t0)) ⊕ ((rdiag (t0 + 1 + 2^k) (t0 + 2^k) ⊕ rdiag (t0 + 1) t0) && center t0)`. -/
theorem periodic_crossCarry_center_slot_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (ht0 : t0 + 1 < twopow k) :
    (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k) =
      bxor (rdiag (t0 + 1) t0 &&
        bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))
        (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center t0) := by
  rw [crossCarry_row_scale_center_slot_and t0 k ht0,
    periodic_witt_cone T P hP h k t0 ht (by omega),
    winWitt_testBit_middle_ray t0 k (t0 + 1) ht0 (by omega)]

/-- **Exact Cross-Carry Formula at `t0 = d + 1` in Left-Diagonal Coordinates under `CenterPeriodic T P`**: at base time `t0 = d + 1` (`T ≤ d + 1`, `d + 2 < 2^k`), `rdiag (d + 2) (d + 1) = ldiag d (d + 1)` and `rdiag (d + 2 + 2^k) (d + 1 + 2^k) = ldiag (d + 2^k) (d + 1 + 2^k)` (column `-1`), so the cross-carry at bit `(d + 2) + 2^k` directly couples `ldiag d (d + 1)`, `ldiag (d + 2^k) (d + 1 + 2^k)`, and the periodic center via `&&`: `(ldiag d (d + 1) && (center (d + 1 + lag P k) ⊕ center (d + 1))) ⊕ ((ldiag (d + 2^k) (d + 1 + 2^k) ⊕ ldiag d (d + 1)) && center (d + 1))`. -/
theorem periodic_crossCarry_colm1_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < twopow k) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      bxor (ldiag d (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center (d + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1)) &&
          Rule30UOR.Core.center (d + 1)) := by
  have hcc := periodic_crossCarry_center_slot_and T P hP h (d + 1) k ht (by omega)
  rw [show (d + 1) + 1 = d + 2 by omega] at hcc
  have hl1 : rdiag (d + 2) (d + 1) = ldiag d (d + 1) := by
    rw [show d + 2 = d + 2 * 1 by omega, ← ldiag_eq_rdiag d 1]
  have hl2 : rdiag ((d + 2) + twopow k) ((d + 1) + twopow k) =
      ldiag (d + twopow k) ((d + 1) + twopow k) := by
    rw [show (d + 2) + twopow k = (d + twopow k) + 2 * 1 by omega,
      show (d + 1) + twopow k = (d + twopow k) + 1 by omega,
      ← ldiag_eq_rdiag (d + twopow k) 1]
  rw [hl1, hl2] at hcc
  exact hcc

/-- **Exact Sector-0 Cross-Carry Localization at the Right Threshold (`j = J`, `J + 1 < 2^k`)**: applying `crossCarry_testBit_succ` to `phiScale k (row t0)` and `winWitt t0 (2^k)` at the right threshold `j = J` (`IsRightThreshold k J`), where `(winWitt t0 (2^k)).testBit J = false` and `(winWitt t0 (2^k)).testBit (J + 1) = true`, collapses the bilinear cross-carry at bit `J + 1` to the single AND term `(phiScale k (row t0)).testBit J = rdiag J t0`! -/
theorem crossCarry_row_scale_at_threshold_eq_rdiag (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 1 < twopow k) :
    (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (J + 1) =
      rdiag J t0 := by
  rw [crossCarry_testBit_succ (phiScale k (row t0)) (winWitt t0 (twopow k)) J,
    winWitt_zero_gap_of_threshold t0 k J J hJ (by omega) (by omega),
    winWitt_leading_bit_of_threshold t0 k J hJ hJlt,
    phiScale_row_testBit_sector_zero t0 k J (by omega),
    Bool.and_false, Bool.true_and, bxor_eq_xor, Bool.false_xor]

/-- **Exact Sector-0 Carry Decomposition at the Right Threshold (`j = J`, `J + 1 < 2^k`)**: applying Theorem 9.53 (`carry_xor`) to Theorem 9.12 (`row_scale`) at bit `J + 1` (`IsRightThreshold k J`, `J + 1 < 2^k`) proves that the late carry `rdiag (J + 1) (t0 + 2^k) && rdiag J (t0 + 2^k)` equals the early carry `rdiag (J + 1) t0 && rdiag J t0` XORed with the cross-carry `rdiag J t0` (since `carry (winWitt t0 (2^k))` vanishes at `J + 1` by the threshold zero gap). -/
theorem carry_row_scale_at_threshold (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 1 < twopow k) :
    (carry (row (t0 + twopow k))).testBit (J + 1) =
      bxor (rdiag (J + 1) t0 && rdiag J t0) (rdiag J t0) := by
  have hbit := congrArg (fun n => n.testBit (J + 1)) (carry_row_scale_decomp t0 k)
  rw [Nat.testBit_xor, Nat.testBit_xor,
    crossCarry_row_scale_at_threshold_eq_rdiag t0 k J hJ hJlt] at hbit
  have hcw : (carry (winWitt t0 (twopow k))).testBit (J + 1) = false := by
    rw [carry_testBit_succ (winWitt t0 (twopow k)) J,
      winWitt_zero_gap_of_threshold t0 k J J hJ (by omega) (by omega),
      Bool.and_false]
  have hcp : (carry (phiScale k (row t0))).testBit (J + 1) = (rdiag (J + 1) t0 && rdiag J t0) := by
    rw [carry_testBit_succ (phiScale k (row t0)) J,
      phiScale_row_testBit_sector_zero t0 k (J + 1) hJlt,
      phiScale_row_testBit_sector_zero t0 k J (by omega)]
  rw [hcw, hcp, Bool.xor_false, ← bxor_eq_xor] at hbit
  exact hbit

/-- **Exact Sector-0 Next-Bit Cross-Carry at `J + 1` (`j = J + 1`, `J + 2 < 2^k`)**: at bit `J + 2`, where `(winWitt t0 (2^k)).testBit (J + 1) = true`, the cross-carry `(crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit (J + 2)` equals `rdiag (J + 2) t0 ⊕ ((winWitt t0 (2^k)).testBit (J + 2) && rdiag (J + 1) t0)`! -/
theorem crossCarry_row_scale_at_threshold_succ (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 2 < twopow k) :
    (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (J + 2) =
      bxor (rdiag (J + 2) t0)
        ((winWitt t0 (twopow k)).testBit (J + 2) && rdiag (J + 1) t0) := by
  rw [show J + 2 = (J + 1) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row t0)) (winWitt t0 (twopow k)) (J + 1),
    winWitt_leading_bit_of_threshold t0 k J hJ (by omega),
    phiScale_row_testBit_sector_zero t0 k (J + 1 + 1) hJlt,
    phiScale_row_testBit_sector_zero t0 k (J + 1) (by omega),
    Bool.and_true]

/-- **Exact Cross-Carry Decomposition of the `winWitt` 1-Cocycle (`carry_winWitt_late_decomp`)**: applying Theorem 9.53 (`carry_xor`) to the `winWitt` scale cocycle `winWitt (t0 + 2^k) (2^k) = winWitt t0 (2^(k+1)) ^^^ phiScale k (winWitt t0 (2^k))` decomposes the carry of the late window `carry (winWitt (t0 + 2^k) (2^k))` into `carry (winWitt t0 (2^(k+1))) ^^^ carry (phiScale k (winWitt t0 (2^k))) ^^^ crossCarry (winWitt t0 (2^(k+1))) (phiScale k (winWitt t0 (2^k)))`. -/
theorem carry_winWitt_late_decomp (t0 k : Nat) :
    carry (winWitt (t0 + twopow k) (twopow k)) =
      (carry (winWitt t0 (twopow (k + 1))) ^^^ carry (phiScale k (winWitt t0 (twopow k)))) ^^^
        crossCarry (winWitt t0 (twopow (k + 1))) (phiScale k (winWitt t0 (twopow k))) := by
  rw [winWitt_scale_cocycle t0 k, carry_xor]

/-- **Base-Time Step of `winWitt` at Bit `j + 2` via `carry` and `crossCarry` (`winWitt_cone_step_testBit_add_two`)**: for `2 * t0 + 1 < 2^k` and any bit index `j`, bit `j + 2` of `winWitt (t0 + 1) (2^k)` equals the linear step `(phiLinear (winWitt t0 (2^k))).testBit (j + 2)` XORed with the window's own AND-carry `((winWitt t0 (2^k)).testBit (j + 1) && (winWitt t0 (2^k)).testBit j)` and the bilinear cross-carry `(crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit (j + 1)`. -/
theorem winWitt_cone_step_testBit_add_two (t0 k j : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit (j + 2) =
      bxor (bxor ((phiLinear (winWitt t0 (twopow k))).testBit (j + 2))
        ((winWitt t0 (twopow k)).testBit (j + 1) && (winWitt t0 (twopow k)).testBit j))
        ((crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (j + 1)) := by
  have hstep := congrArg (fun n => n.testBit (j + 2)) (winWitt_cone_step t0 k hcone)
  have hp : phi (winWitt t0 (twopow k)) =
      phiLinear (winWitt t0 (twopow k)) ^^^ (carry (winWitt t0 (twopow k)) <<< 1) :=
    Rule30UOR.Core.phi_split (winWitt t0 (twopow k))
  rw [hp, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft] at hstep
  have d1 : decide (j + 2 ≥ 1) = true := decide_eq_true (by omega)
  rw [d1, Bool.true_and, Bool.true_and, show j + 2 - 1 = j + 1 by omega,
    carry_testBit_succ (winWitt t0 (twopow k)) j] at hstep
  rw [hstep]
  simp only [bxor_eq_xor]

/-- **Exact Center-Slot Step Law of `winWitt` at `(t0 + 2) + 2^k` under `CenterPeriodic T P`**: combining `winWitt_cone_step_testBit_add_two` at `j = t0 + 2^k` (`2 * t0 + 1 < 2^k`, `T ≤ t0`) with the carry AND-structure and `periodic_crossCarry_center_slot_and` expresses `(winWitt (t0 + 1) (2^k)).testBit ((t0 + 2) + 2^k)` (`= wittRespBool (t0 + 1) k` shifted by 1) in terms of `(phiLinear (winWitt t0 (2^k))).testBit ((t0 + 2) + 2^k)` and the exact AND-coupled `center` and `rdiag (t0 + 1)` terms:
`((rdiag (t0 + 1 + 2^k) (t0 + 2^k) ⊕ rdiag (t0 + 1) t0) && center (t0 + lag P k)) ⊕ (rdiag (t0 + 1) t0 && (center (t0 + lag P k) ⊕ center t0))`! -/
theorem periodic_winWitt_step_center_slot_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (hcone : 2 * t0 + 1 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit ((t0 + 2) + twopow k) =
      bxor ((phiLinear (winWitt t0 (twopow k))).testBit ((t0 + 2) + twopow k))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
          (rdiag (t0 + 1) t0 &&
            bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))) := by
  have hj := winWitt_cone_step_testBit_add_two t0 k (t0 + twopow k) hcone
  rw [show (t0 + twopow k) + 2 = (t0 + 2) + twopow k by omega,
    show (t0 + twopow k) + 1 = (t0 + 1) + twopow k by omega] at hj
  have hcc := periodic_crossCarry_center_slot_and T P hP h t0 k ht (by omega)
  have hw0 : (winWitt t0 (twopow k)).testBit (t0 + twopow k) =
      bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0) :=
    periodic_witt_cone T P hP h k t0 ht (by omega)
  have hw1 : (winWitt t0 (twopow k)).testBit ((t0 + 1) + twopow k) =
      bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) :=
    winWitt_testBit_middle_ray t0 k (t0 + 1) (by omega) (by omega)
  rw [hj, hcc, hw0, hw1]
  simp only [bxor_eq_xor]
  cases (phiLinear (winWitt t0 (twopow k))).testBit ((t0 + 2) + twopow k) <;>
    cases rdiag ((t0 + 1) + twopow k) (t0 + twopow k) <;>
    cases rdiag (t0 + 1) t0 <;>
    cases Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center t0 <;> rfl

/-- **Polarized Total Carry Sum (`carry b ⊕ crossCarry a b`) at Bit `j + 1`**: combining the window's own AND-carry `b_{j+1} && b_j` with the bilinear cross-carry `(a_{j+1} && b_j) ⊕ (b_{j+1} && a_j)` factors cleanly into `((a_{j+1} ⊕ b_{j+1}) && b_j) ⊕ (b_{j+1} && a_j)`! When `a = phiScale k (row t0)` and `b = winWitt t0 (2^k)`, `a ⊕ b = row (t0 + 2^k)` by Theorem 9.12 (`row_scale`), so `a_{j+1} ⊕ b_{j+1} = (row (t0 + 2^k)).testBit (j + 1)`! -/
theorem carry_xor_crossCarry_factor (a1 a0 b1 b0 : Bool) :
    bxor (b1 && b0) (bxor (a1 && b0) (b1 && a0)) =
      bxor (bxor a1 b1 && b0) (b1 && a0) := by
  cases a1 <;> cases a0 <;> cases b1 <;> cases b0 <;> rfl

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_winWitt_step_center_slot_and`. -/
theorem periodic_winWitt_step_center_slot_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (hcone : 2 * t0 + 1 < twopow k) :
    BitWinWittEq (t0 + 1) (twopow k) ((t0 + 2) + twopow k)
      (bxor ((phiLinear (winWitt t0 (twopow k))).testBit ((t0 + 2) + twopow k))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
          (rdiag (t0 + 1) t0 &&
            bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0)))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_winWitt_step_center_slot_and T P hP h t0 k ht hcone]

/-- **Total Nonlinear Carry Injection into `winWitt (t0 + 1) (2^k)` at the Center Slot under `CenterPeriodic T P` (`periodic_carry_plus_crossCarry_center_slot_and`)**: applying Theorem 9.53 (`carry_xor`) to Theorem 9.12 (`row_scale`) at bit `(t0 + 1) + 2^k` (`T ≤ t0`, `t0 + 1 < 2^k`) evaluates the sum of the window carry `(carry (winWitt t0 (2^k))).testBit ((t0 + 1) + 2^k)` and the bilinear cross-carry `(crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit ((t0 + 1) + 2^k)` via the carry's AND-structure to `(rdiag ((t0 + 1) + 2^k) (t0 + 2^k) && (center (t0 + lag P k) ⊕ center t0)) ⊕ ((rdiag ((t0 + 1) + 2^k) (t0 + 2^k) ⊕ rdiag (t0 + 1) t0) && center t0)`. -/
theorem periodic_carry_plus_crossCarry_center_slot_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (ht0 : t0 + 1 < twopow k) :
    bxor ((carry (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k))
      ((crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k)) =
      bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k) &&
        bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))
        (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center t0) := by
  have hcw : (carry (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k) =
      (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
        bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0)) := by
    rw [show (t0 + 1) + twopow k = (t0 + twopow k) + 1 by omega,
      carry_testBit_succ (winWitt t0 (twopow k)) (t0 + twopow k),
      show (t0 + twopow k) + 1 = (t0 + 1) + twopow k by omega,
      winWitt_testBit_middle_ray t0 k (t0 + 1) ht0 (by omega),
      show (winWitt t0 (twopow k)).testBit (t0 + twopow k) = wittRespBool t0 k from rfl,
      periodic_witt_cone T P hP h k t0 ht (by omega)]
  rw [hcw, periodic_crossCarry_center_slot_and T P hP h t0 k ht ht0]
  simp only [bxor_eq_xor]
  cases rdiag ((t0 + 1) + twopow k) (t0 + twopow k) <;>
    cases rdiag (t0 + 1) t0 <;>
    cases Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center t0 <;> rfl

/-- **Exact Late-Row Carry Formula at the Center Slot under `CenterPeriodic T P` (`periodic_carry_row_scale_center_slot_and`)**: applying Theorem 9.53 (`carry_xor`) to Theorem 9.12 (`row_scale`) inside the light cone (`2 * t0 + 1 < 2^k`, `T ≤ t0`) proves that `(rdiag (t0 + 1 + 2^k) (t0 + 2^k) && center (t0 + lag P k)) ⊕ (rdiag (t0 + 1) t0 && center t0)` equals the total nonlinear carry injection `(carry (winWitt t0 (2^k))).testBit ((t0 + 1) + 2^k) ⊕ (crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))).testBit ((t0 + 1) + 2^k)`. -/
theorem periodic_carry_row_scale_center_slot_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (hcone : 2 * t0 + 1 < twopow k) :
    bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k) &&
      Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
      (rdiag (t0 + 1) t0 && Rule30UOR.Core.center t0) =
      bxor ((carry (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k))
        ((crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit ((t0 + 1) + twopow k)) := by
  rw [periodic_carry_plus_crossCarry_center_slot_and T P hP h t0 k ht (by omega)]
  simp only [bxor_eq_xor]
  cases rdiag ((t0 + 1) + twopow k) (t0 + twopow k) <;>
    cases rdiag (t0 + 1) t0 <;>
    cases Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center t0 <;> rfl

/-- **Exact Linear Part `(phiLinear (winWitt t0 (2^k))).testBit ((t0 + 2) + 2^k)` at the Center Slot (`2 * t0 + 2 < 2^k`)**: expanding both `(winWitt (t0 + 1) (2^k)).testBit ((t0 + 2) + 2^k)` and `(phiLinear (winWitt t0 (2^k))).testBit ((t0 + 2) + 2^k)` shows that their XOR is the exact carry-difference `(rdiag (t0 + 1 + 2^k) (t0 + 2^k) && center (t0 + 2^k)) ⊕ (rdiag (t0 + 1) t0 && center t0)`. -/
theorem phiLinear_winWitt_center_slot_testBit (t0 k : Nat) (hcone : 2 * t0 + 2 < twopow k) :
    (phiLinear (winWitt t0 (twopow k))).testBit ((t0 + 2) + twopow k) =
      bxor (bxor (rdiag ((t0 + 2) + twopow k) (t0 + twopow k)) (rdiag (t0 + 2) t0))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0))
          (wittRespBool t0 k)) := by
  change (((winWitt t0 (twopow k)) ^^^ ((winWitt t0 (twopow k)) <<< 1)) ^^^
      ((winWitt t0 (twopow k)) <<< 2)).testBit ((t0 + 2) + twopow k) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide ((t0 + 2) + twopow k ≥ 1) = true := decide_eq_true (by omega)
  have d2 : decide ((t0 + 2) + twopow k ≥ 2) = true := decide_eq_true (by omega)
  rw [d1, d2, Bool.true_and, Bool.true_and,
    show (t0 + 2) + twopow k - 1 = (t0 + 1) + twopow k by omega,
    show (t0 + 2) + twopow k - 2 = t0 + twopow k by omega,
    winWitt_testBit_middle_ray t0 k (t0 + 2) (by omega) (by omega),
    winWitt_testBit_middle_ray t0 k (t0 + 1) (by omega) (by omega),
    show (winWitt t0 (twopow k)).testBit (t0 + twopow k) = wittRespBool t0 k from rfl]
  simp only [bxor_eq_xor]
  cases rdiag ((t0 + 2) + twopow k) (t0 + twopow k) <;>
    cases rdiag (t0 + 2) t0 <;>
    cases rdiag ((t0 + 1) + twopow k) (t0 + twopow k) <;>
    cases rdiag (t0 + 1) t0 <;>
    cases wittRespBool t0 k <;> rfl

/-- Paper-facing `BitCarryEq` predicate: `bit (carry n) j = bton b`. -/
def BitCarryEq (n j : Nat) (b : Bool) : Prop :=
  bit (carry n) j = bton b

/-- Paper-facing `BitCrossCarryEq` predicate: `bit (crossCarry a b) j = bton c`. -/
def BitCrossCarryEq (a b j : Nat) (c : Bool) : Prop :=
  bit (crossCarry a b) j = bton c

theorem carry_testBit_succ_prop (y j : Nat) :
    BitCarryEq y (j + 1) (bit y (j + 1) == 1 && bit y j == 1) := by
  rw [BitCarryEq, bit_eq_bton_testBit, carry_testBit_succ,
    bit_eq_if_testBit y (j + 1), bit_eq_if_testBit y j]
  cases y.testBit (j + 1) <;> cases y.testBit j <;> rfl

theorem crossCarry_row_scale_center_slot_and_prop (t0 k : Nat) (ht0 : t0 + 1 < twopow k) :
    BitCrossCarryEq (phiScale k (row t0)) (winWitt t0 (twopow k)) ((t0 + 1) + twopow k)
      (bxor (rdiag (t0 + 1) t0 && wittRespBool t0 k)
        ((winWitt t0 (twopow k)).testBit ((t0 + 1) + twopow k) && Rule30UOR.Core.center t0)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_center_slot_and t0 k ht0]

theorem periodic_crossCarry_center_slot_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (ht0 : t0 + 1 < twopow k) :
    BitCrossCarryEq (phiScale k (row t0)) (winWitt t0 (twopow k)) ((t0 + 1) + twopow k)
      (bxor (rdiag (t0 + 1) t0 &&
        bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))
        (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center t0)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_center_slot_and T P hP h t0 k ht ht0]

theorem periodic_crossCarry_colm1_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < twopow k) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (bxor (ldiag d (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center (d + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1)) &&
          Rule30UOR.Core.center (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_and T P hP h d k ht hd]

theorem crossCarry_row_scale_at_threshold_eq_rdiag_prop (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 1 < twopow k) :
    BitCrossCarryEq (phiScale k (row t0)) (winWitt t0 (twopow k)) (J + 1) (rdiag J t0) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_at_threshold_eq_rdiag t0 k J hJ hJlt]

theorem carry_row_scale_at_threshold_prop (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 1 < twopow k) :
    BitCarryEq (row (t0 + twopow k)) (J + 1)
      (bxor (rdiag (J + 1) t0 && rdiag J t0) (rdiag J t0)) := by
  rw [BitCarryEq, bit_eq_bton_testBit,
    carry_row_scale_at_threshold t0 k J hJ hJlt]

/-- **Fully Expanded Center-Slot Step Law of `winWitt (t0 + 1) (2^k)` at `(t0 + 2) + 2^k` under `CenterPeriodic T P` (`periodic_winWitt_step_center_slot_expanded`)**: combining `periodic_winWitt_step_center_slot_and` and `phiLinear_winWitt_center_slot_testBit` (`2 * t0 + 2 < 2^k`, `T ≤ t0`) expresses bit `(t0 + 2) + 2^k` of `winWitt (t0 + 1) (2^k)` explicitly in terms of the spatial defects on `rdiag (t0 + 2)` and `rdiag (t0 + 1)` and the AND-structure of the periodic center at lag `lag P k` and lag `0`! -/
theorem periodic_winWitt_step_center_slot_expanded (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (hcone : 2 * t0 + 2 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit ((t0 + 2) + twopow k) =
      bxor (bxor (bxor (rdiag ((t0 + 2) + twopow k) (t0 + twopow k)) (rdiag (t0 + 2) t0))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0))
          (bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
          (rdiag (t0 + 1) t0 &&
            bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))) := by
  rw [periodic_winWitt_step_center_slot_and T P hP h t0 k ht (by omega),
    phiLinear_winWitt_center_slot_testBit t0 k hcone,
    periodic_witt_cone T P hP h k t0 ht (by omega)]

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_winWitt_step_center_slot_expanded`. -/
theorem periodic_winWitt_step_center_slot_expanded_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t0 k : Nat) (ht : T ≤ t0) (hcone : 2 * t0 + 2 < twopow k) :
    BitWinWittEq (t0 + 1) (twopow k) ((t0 + 2) + twopow k)
      (bxor (bxor (bxor (rdiag ((t0 + 2) + twopow k) (t0 + twopow k)) (rdiag (t0 + 2) t0))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0))
          (bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0))))
        (bxor (bxor (rdiag ((t0 + 1) + twopow k) (t0 + twopow k)) (rdiag (t0 + 1) t0) &&
          Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k))
          (rdiag (t0 + 1) t0 &&
            bxor (Rule30UOR.Core.center (t0 + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t0)))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_winWitt_step_center_slot_expanded T P hP h t0 k ht hcone]

/-- **Exact Cross-Carry at the Center-Right Slot `j = (t0 - 1) + 2^k` (`t0 = s + 1`, `s + 1 < 2^k`)**: applying `crossCarry_testBit_succ` to `phiScale k (row (s + 1))` and `winWitt (s + 1) (2^k)` at `j = s + 2^k` (`2 * (s + 1) < s + 2^k`, i.e., `s + 2 < 2^k`) evaluates the cross-carry at the exact center bit `(s + 1) + 2^k` via the carry's AND-structure to `(center (s + 1) && (rdiag (s + 2^k) (s + 1 + 2^k) ⊕ rdiag s (s + 1))) ⊕ (wittRespBool (s + 1) k && rdiag s (s + 1))`! -/
theorem crossCarry_row_scale_at_center_bit_and (s k : Nat) (hcone : s + 2 < twopow k) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (Rule30UOR.Core.center (s + 1) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)))
        (wittRespBool (s + 1) k && rdiag s (s + 1)) := by
  rw [show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) (s + twopow k),
    show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
    phiScale_row_testBit_sector_one (s + 1) k (s + 1) (by omega) (by omega),
    phiScale_row_testBit_sector_one (s + 1) k s (by omega) (by omega),
    ← core_center_eq_rdiag (s + 1),
    winWitt_testBit_middle_ray (s + 1) k s (by omega) (by omega)]
  rfl

/-- **Exact Cross-Carry at the Center Bit `(s + 1) + 2^k` under `CenterPeriodic T P` (`T ≤ s + 1`, `s + 2 < 2^k`)**: under `CenterPeriodic T P` (`0 < P`), the cross-carry `(crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` at the exact center slot `(s + 1) + 2^k` evaluates to `(center (s + 1) && (rdiag (s + 2^k) (s + 1 + 2^k) ⊕ rdiag s (s + 1))) ⊕ ((center (s + 1 + lag P k) ⊕ center (s + 1)) && rdiag s (s + 1))`. -/
theorem periodic_crossCarry_at_center_bit_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (Rule30UOR.Core.center (s + 1) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)))
        (bxor (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (s + 1)) && rdiag s (s + 1)) := by
  rw [crossCarry_row_scale_at_center_bit_and s k hcone,
    periodic_witt_cone T P hP h k (s + 1) ht (by omega)]

/-- **Exact Cross-Carry at the Center Bit on White Center Steps (`center (s + 1) = false`, the `MaskedPer` / `carry60` Channel!)**: whenever `center (s + 1) = false` (`s + 2 < 2^k`, `T ≤ s + 1`), the first AND-term in `periodic_crossCarry_at_center_bit_and` vanishes identically (`false && ... = false`), so the cross-carry at the center bit `(s + 1) + 2^k` collapses to `center (s + 1 + lag P k) && rdiag s (s + 1) = center (s + 1 + lag P k) && maskparity (s + 1) 0`! -/
theorem periodic_crossCarry_at_white_center_eq_maskparity (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) &&
        Rule30UOR.Scale.maskparity (s + 1) 0) := by
  rw [periodic_crossCarry_at_center_bit_and T P hP h s k ht hcone,
    maskparity_succ_zero_eq_rdiag s,
    ← core_center_eq_rdiag (s + 1), hw]
  simp only [bxor_eq_xor, Bool.false_and, Bool.xor_false, Bool.false_xor, Bool.not_false, Bool.true_and]

/-- **Universal Connection Between `carry (row (s + 1))` at the Center Bit `s + 1` and `maskparity (s + 1) 0` (`carry_row_xor_maskparity_zero_eq_col1`)**: at every time `s + 1`, the Witt row carry `(carry (row (s + 1))).testBit (s + 1) = center (s + 1) && rdiag s (s + 1)` and the Rule-60 masked carry `maskparity (s + 1) 0 = (!center (s + 1)) && rdiag s (s + 1)` are complementary AND-projections of column `1` (`rdiag s (s + 1)`), so their XOR is `rdiag s (s + 1)` unconditionally! -/
theorem carry_row_xor_maskparity_zero_eq_col1 (s : Nat) :
    bxor ((carry (row (s + 1))).testBit (s + 1)) (Rule30UOR.Scale.maskparity (s + 1) 0) =
      rdiag s (s + 1) := by
  rw [carry_row_testBit_succ (s + 1) s,
    maskparity_succ_zero_eq_rdiag s,
    bxor_eq_xor]
  cases rdiag (s + 1) (s + 1) <;> cases rdiag s (s + 1) <;> rfl

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_at_center_bit_and`. -/
theorem periodic_crossCarry_at_center_bit_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (Rule30UOR.Core.center (s + 1) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)))
        (bxor (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (s + 1)) && rdiag s (s + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_at_center_bit_and T P hP h s k ht hcone]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_at_white_center_eq_maskparity`. -/
theorem periodic_crossCarry_at_white_center_eq_maskparity_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) &&
        Rule30UOR.Scale.maskparity (s + 1) 0) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_at_white_center_eq_maskparity T P hP h s k ht hcone hw]

/-- Paper-facing `BitCarryEq` wrapper for `carry_row_xor_maskparity_zero_eq_col1`. -/
theorem carry_row_xor_maskparity_zero_eq_col1_prop (s : Nat) :
    BitCarryEq (row (s + 1)) (s + 1)
      (bxor (rdiag s (s + 1)) (Rule30UOR.Scale.maskparity (s + 1) 0)) := by
  rw [BitCarryEq, bit_eq_bton_testBit]
  have hc := carry_row_xor_maskparity_zero_eq_col1 s
  revert hc
  simp only [bxor_eq_xor]
  cases (carry (row (s + 1))).testBit (s + 1) <;>
    cases Rule30UOR.Scale.maskparity (s + 1) 0 <;>
    cases rdiag s (s + 1) <;> decide

/-- **White-Center Annihilation of the Late Column-`-1` Term in `crossCarry` (`periodic_crossCarry_colm1_at_white_center`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + 2 < 2^k`), whenever `center (d + 1) = false`, the second AND-term in `periodic_crossCarry_colm1_and` (which contains the late column-`-1` bit `ldiag (d + 2^k) (d + 1 + 2^k)`) is annihilated by `&& center (d + 1) = false`, so the cross-carry at bit `(d + 2) + 2^k` collapses to `ldiag d (d + 1) && center (d + 1 + lag P k)`! -/
theorem periodic_crossCarry_colm1_at_white_center (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < twopow k)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      (ldiag d (d + 1) && Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) := by
  rw [periodic_crossCarry_colm1_and T P hP h d k ht hd, hw]
  simp only [bxor_eq_xor, Bool.and_false, Bool.xor_false]

/-- **Repeat-Lag Scale Invariance of `crossCarry` at `(d + 2) + 2^k` on White Center Steps (`periodic_crossCarry_colm1_white_center_lag_eq`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`), whenever `center (d + 1) = false`, for any two scales `k1, k2` with `lag P k1 = lag P k2` (`d + 2 < 2^k1`, `d + 2 < 2^k2`), the cross-carry at bit `(d + 2) + 2^k` takes the exact same value at scales `k1` and `k2`! -/
theorem periodic_crossCarry_colm1_white_center_lag_eq (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d + 1) (hd1 : d + 2 < twopow k1) (hd2 : d + 2 < twopow k2)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    (crossCarry (phiScale k1 (row (d + 1))) (winWitt (d + 1) (twopow k1))).testBit ((d + 2) + twopow k1) =
      (crossCarry (phiScale k2 (row (d + 1))) (winWitt (d + 1) (twopow k2))).testBit ((d + 2) + twopow k2) := by
  rw [periodic_crossCarry_colm1_at_white_center T P hP h d k1 ht hd1 hw,
    periodic_crossCarry_colm1_at_white_center T P hP h d k2 ht hd2 hw,
    hlag]

/-- In Sector 2 (`2 * t0 < r + 2^k`), `phiScale k (row t0)` at bit `r + 2^(k+1)` reads `rdiag r t0`. -/
theorem phiScale_row_testBit_sector_two (t0 k r : Nat) (hcone : 2 * t0 < r + twopow k) :
    (phiScale k (row t0)).testBit (r + twopow (k + 1)) = rdiag r t0 := by
  change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (r + twopow (k + 1)) = rdiag r t0
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have d1 : decide (r + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (r + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [d1, d2, Bool.true_and, Bool.true_and,
    show r + twopow (k + 1) - twopow k = r + twopow k by omega,
    show r + twopow (k + 1) - (twopow k + twopow k) = r by omega,
    row_testBit t0 (r + twopow (k + 1)),
    row_testBit t0 (r + twopow k),
    row_testBit t0 r,
    rdiag_gt_two_mul t0 (r + twopow (k + 1)) (by omega),
    rdiag_gt_two_mul t0 (r + twopow k) hcone,
    Bool.false_xor, Bool.false_xor]

/-- **Exact Sector-2 Cross-Carry at Bit `(d + 2) + 2^(k+1)` (`crossCarry_row_scale_sector_two_colm1_and`)**: applying Theorem 9.53 (`crossCarry_testBit_succ`) to Theorem 9.12 (`row_scale`) at base time `t0 = d + 1` and Sector-2 bit `(d + 2) + 2^(k+1)` (`d + 1 ≤ k`) expresses `(crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (2^k))).testBit ((d + 2) + 2^(k+1))` via the carry's AND-structure in terms of `ldiag d (d + 1)`, `center (d + 1)`, and the late left diagonals `ldiag (d + 1) (d + 1 + 2^k)` and `ldiag d (d + 1 + 2^k)`. -/
theorem crossCarry_row_scale_sector_two_colm1_and (d k : Nat) (hk : d + 1 ≤ k) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag d (d + 1) && bxor (Rule30UOR.Core.center (d + 1)) (ldiag (d + 1) ((d + 1) + twopow k)))
        (bxor (ldiag d (d + 1)) (ldiag d ((d + 1) + twopow k)) && Rule30UOR.Core.center (d + 1)) := by
  have hdk : d + 1 < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hld : rdiag (d + 2) (d + 1) = ldiag d (d + 1) := by
    rw [show d + 2 = d + 2 * 1 by omega]
    exact (ldiag_eq_rdiag d 1).symm
  have hray : (winWitt (d + 1) (twopow k)).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag d (d + 1)) (ldiag d ((d + 1) + twopow k)) := by
    have hr := winWitt_testBit_left_ray d 1 k hdk
    simpa [show d + 2 * 1 + twopow (k + 1) = (d + 2) + twopow (k + 1) by omega] using hr
  rw [show (d + 2) + twopow (k + 1) = ((d + 1) + twopow (k + 1)) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 1) + twopow (k + 1)),
    show ((d + 1) + twopow (k + 1)) + 1 = (d + 2) + twopow (k + 1) by omega,
    phiScale_row_testBit_sector_two (d + 1) k (d + 2) (by omega),
    phiScale_row_testBit_sector_two (d + 1) k (d + 1) (by omega),
    hld, ← core_center_eq_rdiag (d + 1),
    winWitt_testBit_archimedean (d + 1) k hk,
    hray]

/-- **Settled Sector-2 Cross-Carry at Bit `(d + 2) + 2^(k+1)` (`crossCarry_row_scale_sector_two_colm1_settled_and`)**: for any scale `k ≥ d + 1` where `SettledAt d k` and `SettledAt (d + 1) k` hold, the Sector-2 cross-carry at bit `(d + 2) + 2^(k+1)` is completely independent of `k` and equals `(ldiag d (d + 1) && (center (d + 1) ⊕ zcenter (d + 1))) ⊕ ((ldiag d (d + 1) ⊕ E d (d + 1)) && center (d + 1))`! -/
theorem crossCarry_row_scale_sector_two_colm1_settled_and (d k : Nat) (hk : d + 1 ≤ k)
    (hset0 : SettledAt d k) (hset1 : SettledAt (d + 1) k) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag d (d + 1) && bxor (Rule30UOR.Core.center (d + 1)) (zcenter (d + 1)))
        (bxor (ldiag d (d + 1)) (E d (d + 1)) && Rule30UOR.Core.center (d + 1)) := by
  have hs0 : settle d ≤ (d + 1) + twopow k := by
    unfold SettledAt at hset0; omega
  rw [crossCarry_row_scale_sector_two_colm1_and d k hk,
    ldiag_settled_eq_zcenter (d + 1) k hk hset1,
    ldiag_settled_eq_E d (d + 1) k (by omega) hs0]

/-- **Homogeneous Triality Sector 1 ⊕ Sector 2 Cross-Carry Coupling with `zcenter` under `CenterPeriodic T P` (`periodic_crossCarry_sector_one_xor_two_colm1_settled`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + 1 ≤ k`, `d + 2 < 2^k`, `SettledAt d k`, `SettledAt (d + 1) k`), XORing the Sector-1 cross-carry at `(d + 2) + 2^k` and the Sector-2 cross-carry at `(d + 2) + 2^(k+1)` cancels the early inhomogeneous offsets identically and leaves `(ldiag d (d + 1) && (center (d + 1 + lag P k) ⊕ zcenter (d + 1))) ⊕ ((ldiag (d + 2^k) (d + 1 + 2^k) ⊕ E d (d + 1)) && center (d + 1))`! -/
theorem periodic_crossCarry_sector_one_xor_two_colm1_settled (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hd : d + 2 < twopow k)
    (hset0 : SettledAt d k) (hset1 : SettledAt (d + 1) k) :
    bxor ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k))
      ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1))) =
      bxor (ldiag d (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (zcenter (d + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (E d (d + 1)) &&
          Rule30UOR.Core.center (d + 1)) := by
  rw [periodic_crossCarry_colm1_and T P hP h d k ht hd,
    crossCarry_row_scale_sector_two_colm1_settled_and d k hk hset0 hset1]
  simp only [bxor_eq_xor]
  cases ldiag d (d + 1) <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases zcenter (d + 1) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases E d (d + 1) <;> rfl

/-- **Pure Late-Slice Readout of `phiScale k (winWitt (d + s) (2^k))` in the Low-Bit Zone (`d + 2 * s ≤ k`)**: for any `d, s, k` with `d + 2 * s ≤ k`, Sector 0 of `winWitt (d + s) (2^k)` vanishes at `d + 2 * s` (`winWitt_testBit_low`) and the early state `ldiag d (d + s)` cancels between Sector 1 and Sector 2 (`winWitt_testBit_sector_one_xor_two`), so bit `d + 2 * s + 2^(k+1)` of `phiScale k (winWitt (d + s) (2^k))` equals the pure late-time left-diagonal difference `ldiag (d + 2^k) (d + s + 2^k) ⊕ ldiag d (d + s + 2^k)`! -/
theorem phiScale_winWitt_testBit_triality_low (d s k : Nat) (hk : d + 2 * s ≤ k) :
    (phiScale k (winWitt (d + s) (twopow k))).testBit (d + 2 * s + twopow (k + 1)) =
      bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)) := by
  have hlt : d + 2 * s < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  rw [phiScale_testBit_triality k (winWitt (d + s) (twopow k)) (d + 2 * s),
    winWitt_testBit_low (d + s) k (d + 2 * s) hk,
    show bxor false ((winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k)) =
      (winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k) by
      cases (winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k) <;> rfl,
    winWitt_testBit_sector_one_xor_two d s k hlt]

/-- **Exact Bilinear Cross-Carry of the `winWitt` 1-Cocycle at Bit `(d + 2) + 2^(k+1)` under `CenterPeriodic T P` (`periodic_crossCarry_winWitt_cocycle_colm1_settled`)**: applying Theorem 9.53 (`crossCarry_testBit_succ`) to Theorem 9.143 (`carry_winWitt_late_decomp`) at `t0 = d + 1` and bit `(d + 2) + 2^(k+1)` (`T ≤ d + 1`, `d + 2 ≤ k`, `SettledAt d k`, `SettledAt (d + 1) k`) evaluates `crossCarry (winWitt (d + 1) (2^(k+1))) (phiScale k (winWitt (d + 1) (2^k)))` at `(d + 2) + 2^(k+1)` explicitly via `&&`! -/
theorem periodic_crossCarry_winWitt_cocycle_colm1_settled (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k)
    (hset0 : SettledAt d k) (hset1 : SettledAt (d + 1) k) :
    (crossCarry (winWitt (d + 1) (twopow (k + 1))) (phiScale k (winWitt (d + 1) (twopow k)))).testBit
        ((d + 2) + twopow (k + 1)) =
      bxor (bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1))) (ldiag d (d + 1)) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (zcenter (d + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (E d (d + 1)) &&
          bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + 1))) := by
  have hdk1 : d + 2 < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hs0 : settle d ≤ (d + 1) + twopow k := by
    unfold SettledAt at hset0; omega
  have hu1 : (winWitt (d + 1) (twopow (k + 1))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1))) (ldiag d (d + 1)) := by
    have hr := winWitt_testBit_sector_one_ldiag d 1 (k + 1) (by omega)
    simpa [show d + 2 * 1 + twopow (k + 1) = (d + 2) + twopow (k + 1) by omega] using hr
  have hu0 : (winWitt (d + 1) (twopow (k + 1))).testBit ((d + 1) + twopow (k + 1)) =
      bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + 1)) :=
    periodic_witt_cone T P hP h (k + 1) (d + 1) ht (by omega)
  have hv0 : (phiScale k (winWitt (d + 1) (twopow k))).testBit ((d + 1) + twopow (k + 1)) =
      bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (zcenter (d + 1)) := by
    have hp := phiScale_winWitt_testBit_triality_low (d + 1) 0 k (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at hp
    have hcent : ldiag ((d + 1) + twopow k) ((d + 1) + twopow k) =
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) := by
      have h0 := ldiag_eq_cell_neg ((d + 1) + twopow k) 0
      simp only [Nat.add_zero] at h0
      rw [h0]
      exact Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht
    rw [hp, hcent, ldiag_settled_eq_zcenter (d + 1) k (by omega) hset1]
  have hv1 : (phiScale k (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (E d (d + 1)) := by
    have hp := phiScale_winWitt_testBit_triality_low d 1 k (by omega)
    simpa [show d + 2 * 1 + twopow (k + 1) = (d + 2) + twopow (k + 1) by omega,
      ldiag_settled_eq_E d (d + 1) k (by omega) hs0] using hp
  rw [show (d + 2) + twopow (k + 1) = ((d + 1) + twopow (k + 1)) + 1 by omega,
    crossCarry_testBit_succ (winWitt (d + 1) (twopow (k + 1)))
      (phiScale k (winWitt (d + 1) (twopow k))) ((d + 1) + twopow (k + 1)),
    show ((d + 1) + twopow (k + 1)) + 1 = (d + 2) + twopow (k + 1) by omega,
    hu1, hu0, hv1, hv0]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_at_white_center`. -/
theorem periodic_crossCarry_colm1_at_white_center_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < twopow k)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (ldiag d (d + 1) && Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_at_white_center T P hP h d k ht hd hw]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_row_scale_sector_two_colm1_and`. -/
theorem crossCarry_row_scale_sector_two_colm1_and_prop (d k : Nat) (hk : d + 1 ≤ k) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow (k + 1))
      (bxor (ldiag d (d + 1) && bxor (Rule30UOR.Core.center (d + 1)) (ldiag (d + 1) ((d + 1) + twopow k)))
        (bxor (ldiag d (d + 1)) (ldiag d ((d + 1) + twopow k)) && Rule30UOR.Core.center (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_sector_two_colm1_and d k hk]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_row_scale_sector_two_colm1_settled_and`. -/
theorem crossCarry_row_scale_sector_two_colm1_settled_and_prop (d k : Nat) (hk : d + 1 ≤ k)
    (hset0 : SettledAt d k) (hset1 : SettledAt (d + 1) k) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow (k + 1))
      (bxor (ldiag d (d + 1) && bxor (Rule30UOR.Core.center (d + 1)) (zcenter (d + 1)))
        (bxor (ldiag d (d + 1)) (E d (d + 1)) && Rule30UOR.Core.center (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_sector_two_colm1_settled_and d k hk hset0 hset1]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_winWitt_cocycle_colm1_settled`. -/
theorem periodic_crossCarry_winWitt_cocycle_colm1_settled_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k)
    (hset0 : SettledAt d k) (hset1 : SettledAt (d + 1) k) :
    BitCrossCarryEq (winWitt (d + 1) (twopow (k + 1))) (phiScale k (winWitt (d + 1) (twopow k)))
      ((d + 2) + twopow (k + 1))
      (bxor (bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1))) (ldiag d (d + 1)) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (zcenter (d + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (E d (d + 1)) &&
          bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_winWitt_cocycle_colm1_settled T P hP h d k ht hk hset0 hset1]

/-- **Unconditional Homogeneous Triality Sector 1 ⊕ Sector 2 Cross-Carry Coupling under `CenterPeriodic T P` (`periodic_crossCarry_sector_one_xor_two_colm1_and`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + 1 ≤ k`), XORing the Sector-1 cross-carry at `(d + 2) + 2^k` and the Sector-2 cross-carry at `(d + 2) + 2^(k+1)` cancels the early inhomogeneous offsets identically (without any settling assumption!) and equals `(ldiag d (d + 1) && (center (d + 1 + lag P k) ⊕ ldiag (d + 1) (d + 1 + 2^k))) ⊕ ((ldiag (d + 2^k) (d + 1 + 2^k) ⊕ ldiag d (d + 1 + 2^k)) && center (d + 1))`! -/
theorem periodic_crossCarry_sector_one_xor_two_colm1_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hd : d + 2 < twopow k) :
    bxor ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k))
      ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1))) =
      bxor (ldiag d (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (ldiag (d + 1) ((d + 1) + twopow k)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d ((d + 1) + twopow k)) &&
          Rule30UOR.Core.center (d + 1)) := by
  rw [periodic_crossCarry_colm1_and T P hP h d k ht hd,
    crossCarry_row_scale_sector_two_colm1_and d k hk]
  simp only [bxor_eq_xor]
  cases ldiag d (d + 1) <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases ldiag (d + 1) ((d + 1) + twopow k) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases ldiag d ((d + 1) + twopow k) <;> rfl

/-- **Exact Bilinear Cross-Carry of the `winWitt` 1-Cocycle at Bit `(d + 2) + 2^(k+1)` under `CenterPeriodic T P` (`periodic_crossCarry_winWitt_cocycle_colm1_and`)**: applying Theorem 9.53 (`crossCarry_testBit_succ`) to Theorem 9.143 (`carry_winWitt_late_decomp`) at `t0 = d + 1` and bit `(d + 2) + 2^(k+1)` (`T ≤ d + 1`, `d + 2 ≤ k`) evaluates `crossCarry (winWitt (d + 1) (2^(k+1))) (phiScale k (winWitt (d + 1) (2^k)))` at `(d + 2) + 2^(k+1)` explicitly via `&&`! -/
theorem periodic_crossCarry_winWitt_cocycle_colm1_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) :
    (crossCarry (winWitt (d + 1) (twopow (k + 1))) (phiScale k (winWitt (d + 1) (twopow k)))).testBit
        ((d + 2) + twopow (k + 1)) =
      bxor (bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1))) (ldiag d (d + 1)) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (ldiag (d + 1) ((d + 1) + twopow k)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d ((d + 1) + twopow k)) &&
          bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + 1))) := by
  have hdk1 : d + 2 < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hu1 : (winWitt (d + 1) (twopow (k + 1))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1))) (ldiag d (d + 1)) := by
    have hr := winWitt_testBit_sector_one_ldiag d 1 (k + 1) (by omega)
    simpa [show d + 2 * 1 + twopow (k + 1) = (d + 2) + twopow (k + 1) by omega] using hr
  have hu0 : (winWitt (d + 1) (twopow (k + 1))).testBit ((d + 1) + twopow (k + 1)) =
      bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + 1)) :=
    periodic_witt_cone T P hP h (k + 1) (d + 1) ht (by omega)
  have hv0 : (phiScale k (winWitt (d + 1) (twopow k))).testBit ((d + 1) + twopow (k + 1)) =
      bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (ldiag (d + 1) ((d + 1) + twopow k)) := by
    have hp := phiScale_winWitt_testBit_triality_low (d + 1) 0 k (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at hp
    have hcent : ldiag ((d + 1) + twopow k) ((d + 1) + twopow k) =
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) := by
      have h0 := ldiag_eq_cell_neg ((d + 1) + twopow k) 0
      simp only [Nat.add_zero] at h0
      rw [h0]
      exact Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht
    rw [hp, hcent]
  have hv1 : (phiScale k (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d ((d + 1) + twopow k)) := by
    have hp := phiScale_winWitt_testBit_triality_low d 1 k (by omega)
    simpa [show d + 2 * 1 + twopow (k + 1) = (d + 2) + twopow (k + 1) by omega] using hp
  rw [show (d + 2) + twopow (k + 1) = ((d + 1) + twopow (k + 1)) + 1 by omega,
    crossCarry_testBit_succ (winWitt (d + 1) (twopow (k + 1)))
      (phiScale k (winWitt (d + 1) (twopow k))) ((d + 1) + twopow (k + 1)),
    show ((d + 1) + twopow (k + 1)) + 1 = (d + 2) + twopow (k + 1) by omega,
    hu1, hu0, hv1, hv0]

/-- **White-Center Annihilation in Sector 2 at `(d + 2) + 2^(k+1)` (`crossCarry_row_scale_sector_two_colm1_at_white_center`)**: for `d + 1 ≤ k`, whenever `center (d + 1) = false`, the second AND-term in `crossCarry_row_scale_sector_two_colm1_and` vanishes identically, so the Sector-2 cross-carry at `(d + 2) + 2^(k+1)` collapses to `ldiag d (d + 1) && ldiag (d + 1) (d + 1 + 2^k)`! -/
theorem crossCarry_row_scale_sector_two_colm1_at_white_center (d k : Nat) (hk : d + 1 ≤ k)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1)) =
      (ldiag d (d + 1) && ldiag (d + 1) ((d + 1) + twopow k)) := by
  rw [crossCarry_row_scale_sector_two_colm1_and d k hk, hw]
  simp only [bxor_eq_xor, Bool.false_xor, Bool.and_false, Bool.xor_false]

/-- Paper-facing `BitCrossCarryXorEq` predicate: `bxor ((crossCarry a b).testBit j1) ((crossCarry a b).testBit j2) = c`. -/
def BitCrossCarryXorEq (a b j1 j2 : Nat) (c : Bool) : Prop :=
  bxor ((crossCarry a b).testBit j1) ((crossCarry a b).testBit j2) = c

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_row_scale_sector_two_colm1_at_white_center`. -/
theorem crossCarry_row_scale_sector_two_colm1_at_white_center_prop (d k : Nat) (hk : d + 1 ≤ k)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow (k + 1))
      (ldiag d (d + 1) && ldiag (d + 1) ((d + 1) + twopow k)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_sector_two_colm1_at_white_center d k hk hw]

/-- Paper-facing `BitCrossCarryXorEq` wrapper for `periodic_crossCarry_sector_one_xor_two_colm1_and`. -/
theorem periodic_crossCarry_sector_one_xor_two_colm1_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hd : d + 2 < twopow k) :
    BitCrossCarryXorEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))
      ((d + 2) + twopow k) ((d + 2) + twopow (k + 1))
      (bxor (ldiag d (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (ldiag (d + 1) ((d + 1) + twopow k)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d ((d + 1) + twopow k)) &&
          Rule30UOR.Core.center (d + 1))) :=
  periodic_crossCarry_sector_one_xor_two_colm1_and T P hP h d k ht hk hd

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_winWitt_cocycle_colm1_and`. -/
theorem periodic_crossCarry_winWitt_cocycle_colm1_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) :
    BitCrossCarryEq (winWitt (d + 1) (twopow (k + 1))) (phiScale k (winWitt (d + 1) (twopow k)))
      ((d + 2) + twopow (k + 1))
      (bxor (bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1))) (ldiag d (d + 1)) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (ldiag (d + 1) ((d + 1) + twopow k)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d ((d + 1) + twopow k)) &&
          bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_winWitt_cocycle_colm1_and T P hP h d k ht hk]

/-- Paper-facing `BitCrossCarryXorEq` wrapper for `periodic_crossCarry_sector_one_xor_two_colm1_settled`. -/
theorem periodic_crossCarry_sector_one_xor_two_colm1_settled_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hd : d + 2 < twopow k)
    (hset0 : SettledAt d k) (hset1 : SettledAt (d + 1) k) :
    BitCrossCarryXorEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))
      ((d + 2) + twopow k) ((d + 2) + twopow (k + 1))
      (bxor (ldiag d (d + 1) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) (zcenter (d + 1)))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (E d (d + 1)) &&
          Rule30UOR.Core.center (d + 1))) :=
  periodic_crossCarry_sector_one_xor_two_colm1_settled T P hP h d k ht hk hd hset0 hset1

/-- Paper-facing `bit` wrapper for `periodic_crossCarry_colm1_white_center_lag_eq`. -/
theorem periodic_crossCarry_colm1_white_center_lag_eq_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d + 1) (hd1 : d + 2 < twopow k1) (hd2 : d + 2 < twopow k2)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    bit (crossCarry (phiScale k1 (row (d + 1))) (winWitt (d + 1) (twopow k1))) ((d + 2) + twopow k1) =
      bit (crossCarry (phiScale k2 (row (d + 1))) (winWitt (d + 1) (twopow k2))) ((d + 2) + twopow k2) := by
  rw [bit_eq_bton_testBit, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_white_center_lag_eq T P hP h d k1 k2 hlag ht hd1 hd2 hw]

/-- Paper-facing `bit` wrapper for `phiScale_winWitt_testBit_triality_low`. -/
theorem phiScale_winWitt_testBit_triality_low_prop (d s k : Nat) (hk : d + 2 * s ≤ k) :
    bit (phiScale k (winWitt (d + s) (twopow k))) (d + 2 * s + twopow (k + 1)) =
      bton (bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k))) := by
  rw [bit_eq_bton_testBit, phiScale_winWitt_testBit_triality_low d s k hk]

/-- **Exact Swap of Witt Row Carry and Rule-60 Masked Carry at the Right-Period Threshold (`carry_row_late_at_threshold_center_eq_maskparity`)**: at the threshold time `t0 = J + 1` (`IsRightThreshold k J`, `J + 1 < 2^k`), the late Witt row carry `(carry (row ((J + 1) + 2^k))).testBit (J + 1)` equals the early Rule-60 masked carry `maskparity (J + 1) 0` (`= (!center (J + 1)) && rdiag J (J + 1)`)! -/
theorem carry_row_late_at_threshold_center_eq_maskparity (k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 1 < twopow k) :
    (carry (row ((J + 1) + twopow k))).testBit (J + 1) =
      Rule30UOR.Scale.maskparity (J + 1) 0 := by
  rw [carry_row_scale_at_threshold (J + 1) k J hJ hJlt,
    maskparity_succ_zero_eq_rdiag J]
  simp only [bxor_eq_xor]
  cases rdiag (J + 1) (J + 1) <;> cases rdiag J (J + 1) <;> rfl

/-- **Exact Center-Right Carry Polarization (`carry_row_scale_center_bit`)**: for `s + 2 < 2^k`, applying Theorem 9.53 (`carry_xor`) to Theorem 9.12 (`row_scale`) at base time `t0 = s + 1` and bit `(s + 1) + 2^k` proves that `(center ((s + 1) + 2^k) && rdiag (s + 2^k) ((s + 1) + 2^k)) ⊕ (center (s + 1) && rdiag s (s + 1))` equals `(carry (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k) ⊕ (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)`. -/
theorem carry_row_scale_center_bit (s k : Nat) (hcone : s + 2 < twopow k) :
    bxor (Rule30UOR.Core.center ((s + 1) + twopow k) && rdiag (s + twopow k) ((s + 1) + twopow k))
      (Rule30UOR.Core.center (s + 1) && rdiag s (s + 1)) =
      bxor ((carry (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k))
        ((crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k)) := by
  have h1 : (carry (row ((s + 1) + twopow k))).testBit ((s + 1) + twopow k) =
      (Rule30UOR.Core.center ((s + 1) + twopow k) && rdiag (s + twopow k) ((s + 1) + twopow k)) := by
    have hc := carry_row_testBit_succ ((s + 1) + twopow k) (s + twopow k)
    rw [show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
      ← core_center_eq_rdiag ((s + 1) + twopow k)] at hc
    exact hc
  have h2 : (carry (phiScale k (row (s + 1)))).testBit ((s + 1) + twopow k) =
      (Rule30UOR.Core.center (s + 1) && rdiag s (s + 1)) := by
    rw [show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
      carry_testBit_succ (phiScale k (row (s + 1))) (s + twopow k),
      show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
      phiScale_row_testBit_sector_one (s + 1) k (s + 1) (by omega) (by omega),
      phiScale_row_testBit_sector_one (s + 1) k s (by omega) (by omega),
      ← core_center_eq_rdiag (s + 1)]
  have hbit := congrArg (fun n => n.testBit ((s + 1) + twopow k)) (carry_row_scale_decomp (s + 1) k)
  rw [Nat.testBit_xor, Nat.testBit_xor, h1, h2] at hbit
  revert hbit
  simp only [bxor_eq_xor]
  cases (Rule30UOR.Core.center ((s + 1) + twopow k) && rdiag (s + twopow k) ((s + 1) + twopow k)) <;>
    cases (Rule30UOR.Core.center (s + 1) && rdiag s (s + 1)) <;>
    cases (carry (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) <;>
    cases (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) <;>
    decide

/-- **Unconditional Decomposition of the `maskparity · 0` Dyadic Jump via `carry` and `crossCarry` (`maskparity_zero_dyadic_jump_eq_witt_carry_crossCarry`)**: for every `s` and `k` with `s + 2 < 2^k`, the dyadic jump `maskparity ((s + 1) + 2^k) 0 ⊕ maskparity (s + 1) 0` along the XOR channel equals `(winWitt (s + 1) (2^k)).testBit (s + 2^k) ⊕ (carry (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k) ⊕ (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)`! -/
theorem maskparity_zero_dyadic_jump_eq_witt_carry_crossCarry (s k : Nat) (hcone : s + 2 < twopow k) :
    bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0) =
      bxor ((winWitt (s + 1) (twopow k)).testBit (s + twopow k))
        (bxor ((carry (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k))
          ((crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k))) := by
  rw [← carry_row_scale_center_bit s k hcone,
    winWitt_testBit_middle_ray (s + 1) k s (by omega) (by omega),
    show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
    maskparity_succ_zero_eq_rdiag (s + twopow k),
    maskparity_succ_zero_eq_rdiag s,
    show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
    ← core_center_eq_rdiag ((s + 1) + twopow k),
    ← core_center_eq_rdiag (s + 1)]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center ((s + 1) + twopow k) <;>
    cases Rule30UOR.Core.center (s + 1) <;>
    cases rdiag (s + twopow k) ((s + 1) + twopow k) <;>
    cases rdiag s (s + 1) <;> rfl

/-- **Factored AND-Structure of the `maskparity · 0` Dyadic Jump (`maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry`)**: for every `s` and `k` with `s + 2 < 2^k`, combining `(winWitt (s + 1) (2^k)).testBit (s + 2^k)` and `(carry (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` factors the dyadic jump `maskparity ((s + 1) + 2^k) 0 ⊕ maskparity (s + 1) 0` into `((!wittRespBool (s + 1) k) && (winWitt (s + 1) (2^k)).testBit (s + 2^k)) ⊕ (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)`! -/
theorem maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry (s k : Nat)
    (hcone : s + 2 < twopow k) :
    bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0) =
      bxor ((!wittRespBool (s + 1) k) && (winWitt (s + 1) (twopow k)).testBit (s + twopow k))
        ((crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k)) := by
  rw [maskparity_zero_dyadic_jump_eq_witt_carry_crossCarry s k hcone,
    show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
    carry_testBit_succ (winWitt (s + 1) (twopow k)) (s + twopow k),
    show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
    show (winWitt (s + 1) (twopow k)).testBit ((s + 1) + twopow k) = wittRespBool (s + 1) k from rfl]
  simp only [bxor_eq_xor]
  cases wittRespBool (s + 1) k <;>
    cases (winWitt (s + 1) (twopow k)).testBit (s + twopow k) <;>
    cases (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) <;>
    rfl

/-- **Exact Equality of the `maskparity · 0` Dyadic Jump and `crossCarry` on Out-of-Phase Steps (`maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true`)**: whenever `wittRespBool (s + 1) k = true` (`s + 2 < 2^k`), the window carry `(carry (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` equals `(winWitt (s + 1) (2^k)).testBit (s + 2^k)`, so their XOR vanishes and the Rule-60 carry jump `maskparity ((s + 1) + 2^k) 0 ⊕ maskparity (s + 1) 0` (`= maskparity (s + 2) k ⊕ maskparity (s + 1) k`) equals the center-bit cross-carry directly! -/
theorem maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true (s k : Nat)
    (hcone : s + 2 < twopow k) (hw : wittRespBool (s + 1) k = true) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0) := by
  rw [maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry s k hcone, hw]
  simp only [bxor_eq_xor, Bool.not_true, Bool.false_and, Bool.false_xor]

/-- **Exact Equality of the `maskparity · 0` Dyadic Jump on In-Phase Steps (`maskparity_dyadic_jump_eq_not_center_and_witt_of_wittResp_false`)**: whenever `wittRespBool (s + 1) k = false` (`s + 2 < 2^k`), `(carry (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k) = false` and `(crossCarry ...).testBit ((s + 1) + 2^k) = center (s + 1) && (winWitt (s + 1) (2^k)).testBit (s + 2^k)`, so `maskparity ((s + 1) + 2^k) 0 ⊕ maskparity (s + 1) 0 = (!center (s + 1)) && (winWitt (s + 1) (2^k)).testBit (s + 2^k)`! -/
theorem maskparity_dyadic_jump_eq_not_center_and_witt_of_wittResp_false (s k : Nat)
    (hcone : s + 2 < twopow k) (hw : wittRespBool (s + 1) k = false) :
    bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0) =
      ((!Rule30UOR.Core.center (s + 1)) && (winWitt (s + 1) (twopow k)).testBit (s + twopow k)) := by
  rw [maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry s k hcone,
    crossCarry_row_scale_at_center_bit_and s k hcone,
    ← winWitt_testBit_middle_ray (s + 1) k s (by omega) (by omega),
    hw]
  simp only [bxor_eq_xor, Bool.not_false, Bool.true_and, Bool.false_and, Bool.xor_false]
  cases Rule30UOR.Core.center (s + 1) <;>
    cases (winWitt (s + 1) (twopow k)).testBit (s + twopow k) <;> rfl

/-- **Direct Two-Halves Bridge Locking `leftresponse` Derivative to `crossCarry` on Out-of-Phase Steps (`periodic_leftresponse_step_diff_eq_crossCarry_of_out_of_phase`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ s + 1`, `s + 2 < 2^k`), whenever `wittRespBool (s + 1) k = true`, the center-bit cross-carry `(crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` equals `(leftresponse (s + 2) k ⊕ leftresponse (s + 1) k) ⊕ (center (s + 2 + lag P k) ⊕ center (s + 1 + lag P k)) ⊕ (center (s + 2) ⊕ center (s + 1))`! -/
theorem periodic_leftresponse_step_diff_eq_crossCarry_of_out_of_phase (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k)
    (hw : wittRespBool (s + 1) k = true) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (bxor (Rule30UOR.Scale.leftresponse (s + 2) k) (Rule30UOR.Scale.leftresponse (s + 1) k))
        (bxor (bxor (Rule30UOR.Core.center ((s + 2) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k)))
          (bxor (Rule30UOR.Core.center (s + 2)) (Rule30UOR.Core.center (s + 1)))) := by
  rw [maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true s k hcone hw]
  have hj := periodic_maskparity_zero_dyadic_jump_cone T P hP h (s + 1) k ht hcone
  simpa [show (s + 1) + 1 = s + 2 by omega] using hj

/-- **1-Cocycle Cross-Carry Collapse at `J + 2` (`crossCarry_winWitt_cocycle_at_threshold_succ`)**: for any `t0, k, J` with `IsRightThreshold k J` and `J + 2 < 2^k`, because `(winWitt t0 (2^k)).testBit (J + 1) = true` and `(winWitt (t0 + 2^k) (2^k)).testBit (J + 1) = true`, `(winWitt t0 (2^(k+1))).testBit (J + 1) = false`, so the 1-cocycle cross-carry at bit `J + 2` collapses to `(winWitt t0 (2^(k+1))).testBit (J + 2)` (`= rdiag (J + 2) (t0 + 2^(k+1)) ⊕ rdiag (J + 2) t0`)! -/
theorem crossCarry_winWitt_cocycle_at_threshold_succ (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 2 < twopow k) :
    (crossCarry (winWitt t0 (twopow (k + 1))) (phiScale k (winWitt t0 (twopow k)))).testBit (J + 2) =
      bxor (rdiag (J + 2) (t0 + twopow (k + 1))) (rdiag (J + 2) t0) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hv1 : (phiScale k (winWitt t0 (twopow k))).testBit (J + 1) = true := by
    change (((winWitt t0 (twopow k)) ^^^ ((winWitt t0 (twopow k)) <<< twopow k)) ^^^
      ((winWitt t0 (twopow k)) <<< (twopow k + twopow k))).testBit (J + 1) = true
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (J + 1 ≥ twopow k) = false := decide_eq_false (by omega)
    have d2 : decide (J + 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false]
    exact winWitt_leading_bit_of_threshold t0 k J hJ (by omega)
  have hu1 : (winWitt t0 (twopow (k + 1))).testBit (J + 1) = false := by
    have hcoc := congrArg (fun n => n.testBit (J + 1)) (winWitt_scale_cocycle t0 k)
    rw [Nat.testBit_xor, hv1,
      winWitt_leading_bit_of_threshold (t0 + twopow k) k J hJ (by omega)] at hcoc
    revert hcoc
    cases (winWitt t0 (twopow (k + 1))).testBit (J + 1) <;> decide
  rw [show J + 2 = (J + 1) + 1 by omega,
    crossCarry_testBit_succ (winWitt t0 (twopow (k + 1))) (phiScale k (winWitt t0 (twopow k))) (J + 1),
    show (J + 1) + 1 = J + 2 by omega,
    hv1, hu1, Bool.and_true, Bool.and_false, bxor_eq_xor, Bool.xor_false,
    winWitt_testBit_lt_twopow t0 (k + 1) (J + 2) (by omega)]

/-- Paper-facing `BitCarryEq` wrapper for `carry_row_late_at_threshold_center_eq_maskparity`. -/
theorem carry_row_late_at_threshold_center_eq_maskparity_prop (k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 1 < twopow k) :
    BitCarryEq (row ((J + 1) + twopow k)) (J + 1) (Rule30UOR.Scale.maskparity (J + 1) 0) := by
  rw [BitCarryEq, bit_eq_bton_testBit,
    carry_row_late_at_threshold_center_eq_maskparity k J hJ hJlt]

/-- Paper-facing `BitWinWittEq` wrapper for `maskparity_zero_dyadic_jump_eq_witt_carry_crossCarry`. -/
theorem maskparity_zero_dyadic_jump_eq_witt_carry_crossCarry_prop (s k : Nat)
    (hcone : s + 2 < twopow k) :
    BitWinWittEq (s + 1) (twopow k) (s + twopow k)
      (bxor (bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0))
        (bxor (bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)) && wittRespBool (s + 1) k)
          (bxor (Rule30UOR.Core.center (s + 1) &&
            bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)))
            (wittRespBool (s + 1) k && rdiag s (s + 1))))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit]
  have hm := maskparity_zero_dyadic_jump_eq_witt_carry_crossCarry s k hcone
  have hcw : (carry (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      (bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)) && wittRespBool (s + 1) k) := by
    rw [show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
      carry_testBit_succ (winWitt (s + 1) (twopow k)) (s + twopow k),
      show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
      winWitt_testBit_middle_ray (s + 1) k s (by omega) (by omega),
      show (winWitt (s + 1) (twopow k)).testBit ((s + 1) + twopow k) = wittRespBool (s + 1) k from rfl]
    simp only [Bool.and_comm]
  rw [hcw, crossCarry_row_scale_at_center_bit_and s k hcone] at hm
  revert hm
  simp only [bxor_eq_xor]
  cases (winWitt (s + 1) (twopow k)).testBit (s + twopow k) <;>
    cases (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0 ^^ Rule30UOR.Scale.maskparity (s + 1) 0) <;>
    cases ((rdiag (s + twopow k) ((s + 1) + twopow k) ^^ rdiag s (s + 1)) && wittRespBool (s + 1) k) <;>
    cases ((Rule30UOR.Core.center (s + 1) && (rdiag (s + twopow k) ((s + 1) + twopow k) ^^ rdiag s (s + 1))) ^^
      (wittRespBool (s + 1) k && rdiag s (s + 1))) <;> decide

/-- Paper-facing `BitCrossCarryEq` wrapper for `maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry`. -/
theorem maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry_prop (s k : Nat)
    (hcone : s + 2 < twopow k) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0))
        ((!wittRespBool (s + 1) k) && bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit]
  have hm := maskparity_zero_dyadic_jump_eq_not_witt_and_xor_crossCarry s k hcone
  rw [winWitt_testBit_middle_ray (s + 1) k s (by omega) (by omega)] at hm
  revert hm
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) <;>
    cases (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0 ^^ Rule30UOR.Scale.maskparity (s + 1) 0) <;>
    cases ((!wittRespBool (s + 1) k) && (rdiag (s + twopow k) ((s + 1) + twopow k) ^^ rdiag s (s + 1))) <;>
    decide

/-- Paper-facing `BitCrossCarryEq` wrapper for `maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true`. -/
theorem maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true_prop (s k : Nat)
    (hcone : s + 2 < twopow k) (hw : wittRespBool (s + 1) k = true) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true s k hcone hw]

/-- Paper-facing `Eq` wrapper for `maskparity_dyadic_jump_eq_not_center_and_witt_of_wittResp_false`. -/
theorem maskparity_dyadic_jump_eq_not_center_and_witt_of_wittResp_false_prop (s k : Nat)
    (hcone : s + 2 < twopow k) (hw : wittRespBool (s + 1) k = false) :
    bxor (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) (Rule30UOR.Scale.maskparity (s + 1) 0) =
      ((!Rule30UOR.Core.center (s + 1)) && bxor (rdiag (s + twopow k) ((s + 1) + twopow k)) (rdiag s (s + 1))) := by
  rw [maskparity_dyadic_jump_eq_not_center_and_witt_of_wittResp_false s k hcone hw,
    winWitt_testBit_middle_ray (s + 1) k s (by omega) (by omega)]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_leftresponse_step_diff_eq_crossCarry_of_out_of_phase`. -/
theorem periodic_leftresponse_step_diff_eq_crossCarry_of_out_of_phase_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k)
    (hw : wittRespBool (s + 1) k = true) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (bxor (Rule30UOR.Scale.leftresponse (s + 2) k) (Rule30UOR.Scale.leftresponse (s + 1) k))
        (bxor (bxor (Rule30UOR.Core.center ((s + 2) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k)))
          (bxor (Rule30UOR.Core.center (s + 2)) (Rule30UOR.Core.center (s + 1))))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_leftresponse_step_diff_eq_crossCarry_of_out_of_phase T P hP h s k ht hcone hw]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_winWitt_cocycle_at_threshold_succ`. -/
theorem crossCarry_winWitt_cocycle_at_threshold_succ_prop (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJlt : J + 2 < twopow k) :
    BitCrossCarryEq (winWitt t0 (twopow (k + 1))) (phiScale k (winWitt t0 (twopow k))) (J + 2)
      (bxor (rdiag (J + 2) (t0 + twopow (k + 1))) (rdiag (J + 2) t0)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_winWitt_cocycle_at_threshold_succ t0 k J hJ hJlt]

/-- **Alternating Property of `crossCarry` (`crossCarry_self_eq_zero`)**: for every Witt integer `a`, `crossCarry a a = 0`. -/
theorem crossCarry_self_eq_zero (a : Nat) : crossCarry a a = 0 := by
  change (a &&& (a <<< 1)) ^^^ (a &&& (a <<< 1)) = 0
  exact Nat.xor_self (a &&& (a <<< 1))

/-- **Right-Absorption of `a ^^^ b` in `crossCarry` (`crossCarry_xor_self_left`)**: for any Witt integers `a, c`, `crossCarry a (a ^^^ c) = crossCarry a c`. -/
theorem crossCarry_xor_self_left (a c : Nat) : crossCarry a (a ^^^ c) = crossCarry a c := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (((a &&& ((a ^^^ c) <<< 1)) ^^^ ((a ^^^ c) &&& (a <<< 1)))).testBit j =
    (((a &&& (c <<< 1)) ^^^ (c &&& (a <<< 1)))).testBit j
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  cases a.testBit j <;> cases c.testBit j <;>
    cases decide (j ≥ 1) <;> cases a.testBit (j - 1) <;> cases c.testBit (j - 1) <;> rfl

/-- **Exact Equality of Scaled-Window Cross-Carry and Early-Late Row Cross-Carry (`crossCarry_row_scale_eq_crossCarry_late_row`)**: for every `t0` and `k`, because `winWitt t0 (2^k) = phiScale k (row t0) ^^^ row (t0 + 2^k)` and `crossCarry a a = 0`, the cross-carry `crossCarry (phiScale k (row t0)) (winWitt t0 (2^k))` equals the direct early-late cross-carry `crossCarry (phiScale k (row t0)) (row (t0 + 2^k))`! -/
theorem crossCarry_row_scale_eq_crossCarry_late_row (t0 k : Nat) :
    crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) =
      crossCarry (phiScale k (row t0)) (row (t0 + twopow k)) := by
  have hr := row_scale t0 k
  have hwin : winWitt t0 (twopow k) = phiScale k (row t0) ^^^ row (t0 + twopow k) := by
    rw [hr, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hwin, crossCarry_xor_self_left]

/-- **Pure 2×2 Wronskian Formula for Column-`-1` Cross-Carry under `CenterPeriodic T P` (`periodic_crossCarry_colm1_wronskian`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + 2 < 2^k`), cancelling the self-carry `ldiag d (d + 1) && center (d + 1)` reduces the cross-carry at bit `(d + 2) + 2^k` to the pure 2×2 determinant `(ldiag d (d + 1) && center (d + 1 + lag P k)) ⊕ (ldiag (d + 2^k) (d + 1 + 2^k) && center (d + 1))`! -/
theorem periodic_crossCarry_colm1_wronskian (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < twopow k) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      bxor (ldiag d (d + 1) && Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) && Rule30UOR.Core.center (d + 1)) := by
  rw [periodic_crossCarry_colm1_and T P hP h d k ht hd]
  simp only [bxor_eq_xor]
  cases ldiag d (d + 1) <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;> rfl

/-- **Pure 2×2 Wronskian Formula for Sector-2 Column-`-1` Cross-Carry (`crossCarry_row_scale_sector_two_colm1_wronskian`)**: for `d + 1 ≤ k`, cancelling the self-carry `ldiag d (d + 1) && center (d + 1)` reduces the Sector-2 cross-carry at bit `(d + 2) + 2^(k+1)` to the pure 2×2 determinant `(ldiag d (d + 1) && ldiag (d + 1) (d + 1 + 2^k)) ⊕ (ldiag d (d + 1 + 2^k) && center (d + 1))`! -/
theorem crossCarry_row_scale_sector_two_colm1_wronskian (d k : Nat) (hk : d + 1 ≤ k) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow (k + 1)) =
      bxor (ldiag d (d + 1) && ldiag (d + 1) ((d + 1) + twopow k))
        (ldiag d ((d + 1) + twopow k) && Rule30UOR.Core.center (d + 1)) := by
  rw [crossCarry_row_scale_sector_two_colm1_and d k hk]
  simp only [bxor_eq_xor]
  cases ldiag d (d + 1) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases ldiag (d + 1) ((d + 1) + twopow k) <;>
    cases ldiag d ((d + 1) + twopow k) <;> rfl

/-- **Universal Annihilation of `maskparity · 0` by `center` (`maskparity_zero_and_center_eq_false`)**: at every step `t`, `maskparity t 0 && center t = false`. -/
theorem maskparity_zero_and_center_eq_false (t : Nat) :
    (Rule30UOR.Scale.maskparity t 0 && Rule30UOR.Core.center t) = false := by
  cases t with
  | zero =>
    change (Rule30UOR.Core.carry60 0 0 && Rule30UOR.Core.center 0) = false
    rfl
  | succ s =>
    rw [maskparity_succ_zero_eq_rdiag s, ← core_center_eq_rdiag (s + 1)]
    cases Rule30UOR.Core.center (s + 1) <;> cases rdiag s (s + 1) <;> rfl

/-- **Black-Center Annihilation of the Column-`-1` `P`-Periodicity Defect under `CenterPeriodic T P` (`periodic_colm1_defect_and_center_eq_false`)**: for `0 < P` and `T ≤ d + 1`, `(ldiag (d + P) (d + P + 1) ⊕ ldiag d (d + 1)) && center (d + 1) = false` (in other words, on every black center step `center (d + 1) = true`, column `-1` is strictly `P`-periodic: `ldiag (d + P) (d + P + 1) = ldiag d (d + 1)`)! -/
theorem periodic_colm1_defect_and_center_eq_false (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d : Nat) (ht : T ≤ d + 1) :
    (bxor (ldiag (d + P) ((d + P) + 1)) (ldiag d (d + 1)) && Rule30UOR.Core.center (d + 1)) = false := by
  have h1 : ldiag (d + P) ((d + P) + 1) = Rule30UOR.Core.cell ((d + 1) + P) (-1) := by
    rw [show (d + 1) + P = (d + P) + 1 by omega, ldiag_eq_cell_neg (d + P) 1]
    rfl
  have h2 : ldiag d (d + 1) = Rule30UOR.Core.cell (d + 1) (-1) := by
    rw [ldiag_eq_cell_neg d 1]
    rfl
  rw [h1, h2, ← periodic_carry60_defect_eq_colm1_defect T P hP h (d + 1) ht,
    ← maskparity_zero ((d + 1) + P), ← maskparity_zero (d + 1)]
  have hm1 := maskparity_zero_and_center_eq_false ((d + 1) + P)
  have hm2 := maskparity_zero_and_center_eq_false (d + 1)
  rw [h (d + 1) ht] at hm1
  revert hm1 hm2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.maskparity ((d + 1) + P) 0 <;>
    cases Rule30UOR.Scale.maskparity (d + 1) 0 <;>
    cases Rule30UOR.Core.center (d + 1) <;> decide

/-- **Factored `P`-Shift Defect of the Column-`-1` Cross-Carry via `leftresponse` and `wittRespBool` (`periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + P + 2 < 2^k`), the `P`-shift defect of `crossCarry` at the column-`-1` bit `(d + 2) + 2^k` factors cleanly through `wittRespBool (d + 1) k` and the 1-step derivative of the `leftresponse` `P`-defect! -/
theorem periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < twopow k) :
    bxor ((crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))).testBit (((d + P) + 2) + twopow k))
      ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k)) =
      (bxor (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 2) k) (Rule30UOR.Scale.leftresponse (d + 2) k))
        (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 1) k) (Rule30UOR.Scale.leftresponse (d + 1) k)) &&
        wittRespBool (d + 1) k) := by
  rw [periodic_crossCarry_colm1_wronskian T P hP h (d + P) k (by omega) (by omega),
    periodic_crossCarry_colm1_wronskian T P hP h d k ht (by omega)]
  have hc1 : Rule30UOR.Core.center (((d + P) + 1) + Rule30UOR.Scale.lag P k) =
      Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) := by
    rw [show ((d + P) + 1) + Rule30UOR.Scale.lag P k = ((d + 1) + Rule30UOR.Scale.lag P k) + P by omega]
    exact h ((d + 1) + Rule30UOR.Scale.lag P k) (by omega)
  have hc2 : Rule30UOR.Core.center ((d + P) + 1) = Rule30UOR.Core.center (d + 1) := by
    rw [show (d + P) + 1 = (d + 1) + P by omega]
    exact h (d + 1) ht
  rw [hc1, hc2]
  have ha_early := periodic_colm1_defect_and_center_eq_false T P hP h d ht
  have ha_late := periodic_colm1_defect_and_center_eq_false T P hP h (d + twopow k) (by omega)
  rw [show (d + twopow k) + P = (d + P) + twopow k by omega,
    show (d + twopow k) + 1 = (d + 1) + twopow k by omega,
    show ((d + P) + twopow k) + 1 = ((d + P) + 1) + twopow k by omega,
    Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht,
    show twopow k % P = Rule30UOR.Scale.lag P k from rfl] at ha_late
  have hw := periodic_witt_cone T P hP h k (d + 1) ht (by omega)
  have hdef1 : bxor (ldiag (d + P) ((d + P) + 1)) (ldiag d (d + 1)) =
      bxor (Rule30UOR.Scale.maskparity ((d + P) + 1) 0) (Rule30UOR.Scale.maskparity (d + 1) 0) := by
    have h1 : ldiag (d + P) ((d + P) + 1) = Rule30UOR.Core.cell ((d + 1) + P) (-1) := by
      rw [show (d + 1) + P = (d + P) + 1 by omega, ldiag_eq_cell_neg (d + P) 1]; rfl
    have h2 : ldiag d (d + 1) = Rule30UOR.Core.cell (d + 1) (-1) := by
      rw [ldiag_eq_cell_neg d 1]; rfl
    rw [h1, h2, ← periodic_carry60_defect_eq_colm1_defect T P hP h (d + 1) ht,
      ← maskparity_zero ((d + 1) + P), ← maskparity_zero (d + 1),
      show (d + 1) + P = (d + P) + 1 by omega]
  have hdef2 : bxor (ldiag ((d + P) + twopow k) (((d + P) + 1) + twopow k))
      (ldiag (d + twopow k) ((d + 1) + twopow k)) =
      bxor (Rule30UOR.Scale.maskparity (((d + P) + 1) + twopow k) 0)
        (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0) := by
    have h1 : ldiag ((d + P) + twopow k) (((d + P) + 1) + twopow k) =
        Rule30UOR.Core.cell (((d + 1) + twopow k) + P) (-1) := by
      rw [show (((d + P) + 1) + twopow k) = ((d + P) + twopow k) + 1 by omega,
        ldiag_eq_cell_neg ((d + P) + twopow k) 1,
        show ((d + P) + twopow k) + 1 = ((d + 1) + twopow k) + P by omega]; rfl
    have h2 : ldiag (d + twopow k) ((d + 1) + twopow k) =
        Rule30UOR.Core.cell ((d + 1) + twopow k) (-1) := by
      rw [show (d + 1) + twopow k = (d + twopow k) + 1 by omega,
        ldiag_eq_cell_neg (d + twopow k) 1]; rfl
    rw [h1, h2, ← periodic_carry60_defect_eq_colm1_defect T P hP h ((d + 1) + twopow k) (by omega),
      ← maskparity_zero (((d + 1) + twopow k) + P), ← maskparity_zero ((d + 1) + twopow k),
      show ((d + 1) + twopow k) + P = ((d + P) + 1) + twopow k by omega]
  have hj := periodic_maskparity_zero_defect_dyadic_jump_cone T P hP h (d + 1) k ht (by omega)
  rw [show (d + 1) + P = (d + P) + 1 by omega,
    show ((d + P) + 1) + 1 = (d + P) + 2 by omega,
    show (d + 1) + 1 = d + 2 by omega] at hj
  rw [← hj, ← hdef1, ← hdef2, hw]
  revert ha_early ha_late
  simp only [bxor_eq_xor]
  cases ldiag (d + P) ((d + P) + 1) <;>
    cases ldiag d (d + 1) <;>
    cases ldiag ((d + P) + twopow k) (((d + P) + 1) + twopow k) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (d + 1) <;> decide

/-- **Exact `P`-Periodicity of the Column-`-1` Cross-Carry on In-Phase Steps (`periodic_crossCarry_colm1_shift_P_eq_of_wittResp_false`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + P + 2 < 2^k`), whenever `wittRespBool (d + 1) k = false`, the column-`-1` cross-carry at bit `(d + 2) + 2^k` is strictly invariant under `d ↦ d + P`! -/
theorem periodic_crossCarry_colm1_shift_P_eq_of_wittResp_false (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < twopow k)
    (hw : wittRespBool (d + 1) k = false) :
    (crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))).testBit (((d + P) + 2) + twopow k) =
      (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) := by
  have hxor := periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt T P hP h d k ht hdP
  rw [hw, Bool.and_false] at hxor
  revert hxor
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))).testBit (((d + P) + 2) + twopow k) <;>
    cases (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) <;> decide

/-- **Exact Agreement of Column-`-1` and Center-Bit Cross-Carry `P`-Defects on Out-of-Phase Steps (`periodic_crossCarry_colm1_shift_P_eq_center_bit_of_wittResp_true`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ d + 1`, `d + P + 2 < 2^k`), whenever `wittRespBool (d + 1) k = true`, the `P`-shift defect of `crossCarry` at the column-`-1` bit `(d + 2) + 2^k` (left of center) equals the `P`-shift defect of `crossCarry` at the center bit `(d + 1) + 2^k` (right of center)! -/
theorem periodic_crossCarry_colm1_shift_P_eq_center_bit_of_wittResp_true (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < twopow k)
    (hw : wittRespBool (d + 1) k = true) :
    bxor ((crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))).testBit (((d + P) + 2) + twopow k))
      ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k)) =
      bxor ((crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))).testBit (((d + P) + 1) + twopow k))
        ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 1) + twopow k)) := by
  have hwP : wittRespBool ((d + P) + 1) k = true := by
    rw [show (d + P) + 1 = (d + 1) + P by omega, periodic_witt_shift_P T P hP h (d + 1) k ht (by omega)]
    exact hw
  rw [periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt T P hP h d k ht hdP,
    hw, Bool.and_true,
    maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true (d + P) k (by omega) hwP,
    maskparity_dyadic_jump_eq_crossCarry_of_wittResp_true d k (by omega) hw]
  have hj := periodic_maskparity_zero_defect_dyadic_jump_cone T P hP h (d + 1) k ht (by omega)
  rw [show (d + 1) + P = (d + P) + 1 by omega,
    show ((d + P) + 1) + 1 = (d + P) + 2 by omega,
    show (d + 1) + 1 = d + 2 by omega] at hj
  rw [← hj]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.maskparity (((d + P) + 1) + twopow k) 0 <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 <;>
    cases Rule30UOR.Scale.maskparity ((d + P) + 1) 0 <;>
    cases Rule30UOR.Scale.maskparity (d + 1) 0 <;> rfl

/-- **Exact Locking of 1-Step `leftresponse` Derivative to `wittRespBool (s + 2) k` on In-Phase Black Center Steps (`periodic_leftresponse_step_diff_eq_witt_of_in_phase_black`)**: under `CenterPeriodic T P` (`0 < P`, `T ≤ s + 1`, `s + 2 < 2^k`), whenever `center (s + 1) = true` and `wittRespBool (s + 1) k = false`, `maskparity ((s + 1) + 2^k) 0 ⊕ maskparity (s + 1) 0 = false`, so `leftresponse (s + 2) k ⊕ leftresponse (s + 1) k = wittRespBool (s + 2) k`! -/
theorem periodic_leftresponse_step_diff_eq_witt_of_in_phase_black (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hcone : s + 2 < twopow k)
    (hblk : Rule30UOR.Core.center (s + 1) = true)
    (hw : wittRespBool (s + 1) k = false) :
    bxor (Rule30UOR.Scale.leftresponse (s + 2) k) (Rule30UOR.Scale.leftresponse (s + 1) k) =
      wittRespBool (s + 2) k := by
  have hm := maskparity_dyadic_jump_eq_not_center_and_witt_of_wittResp_false s k hcone hw
  rw [hblk, Bool.not_true, Bool.false_and] at hm
  have hj := periodic_maskparity_zero_dyadic_jump_cone T P hP h (s + 1) k ht hcone
  rw [show (s + 1) + 1 = s + 2 by omega, hm] at hj
  have hw1 := periodic_witt_cone T P hP h k (s + 1) ht (by omega)
  have hw2 := periodic_witt_cone T P hP h k (s + 2) (by omega) hcone
  rw [hw] at hw1
  revert hj hw1 hw2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (s + 2) k <;>
    cases Rule30UOR.Scale.leftresponse (s + 1) k <;>
    cases wittRespBool (s + 2) k <;>
    cases Rule30UOR.Core.center ((s + 2) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (s + 2) <;>
    cases Rule30UOR.Core.center (s + 1) <;> decide

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_wronskian`. -/
theorem periodic_crossCarry_colm1_wronskian_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : d + 2 < twopow k) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (bxor (ldiag d (d + 1) && Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) && Rule30UOR.Core.center (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_wronskian T P hP h d k ht hd]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_row_scale_sector_two_colm1_wronskian`. -/
theorem crossCarry_row_scale_sector_two_colm1_wronskian_prop (d k : Nat) (hk : d + 1 ≤ k) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow (k + 1))
      (bxor (ldiag d (d + 1) && ldiag (d + 1) ((d + 1) + twopow k))
        (ldiag d ((d + 1) + twopow k) && Rule30UOR.Core.center (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_sector_two_colm1_wronskian d k hk]

/-- Paper-facing `bit` wrapper for `periodic_crossCarry_colm1_shift_P_eq_of_wittResp_false`. -/
theorem periodic_crossCarry_colm1_shift_P_eq_of_wittResp_false_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < twopow k)
    (hw : wittRespBool (d + 1) k = false) :
    bit (crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))) (((d + P) + 2) + twopow k) =
      bit (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))) ((d + 2) + twopow k) := by
  rw [bit_eq_bton_testBit, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_shift_P_eq_of_wittResp_false T P hP h d k ht hdP hw]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt`. -/
theorem periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hdP : d + P + 2 < twopow k) :
    BitCrossCarryEq (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k)) (((d + P) + 2) + twopow k)
      (bxor (bxor (ldiag d (d + 1) && Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) && Rule30UOR.Core.center (d + 1)))
        (bxor (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 2) k) (Rule30UOR.Scale.leftresponse (d + 2) k))
          (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 1) k) (Rule30UOR.Scale.leftresponse (d + 1) k)) &&
          wittRespBool (d + 1) k)) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit]
  have hs := periodic_crossCarry_colm1_shift_P_eq_leftresponse_and_witt T P hP h d k ht hdP
  have hc := periodic_crossCarry_colm1_wronskian T P hP h d k ht (by omega)
  rw [hc] at hs
  revert hs
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row ((d + P) + 1))) (winWitt ((d + P) + 1) (twopow k))).testBit (((d + P) + 2) + twopow k) <;>
    cases ((ldiag d (d + 1) && Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)) ^^
      (ldiag (d + twopow k) ((d + 1) + twopow k) && Rule30UOR.Core.center (d + 1))) <;>
    cases (((Rule30UOR.Scale.leftresponse ((d + P) + 2) k ^^ Rule30UOR.Scale.leftresponse (d + 2) k) ^^
      (Rule30UOR.Scale.leftresponse ((d + P) + 1) k ^^ Rule30UOR.Scale.leftresponse (d + 1) k)) &&
      wittRespBool (d + 1) k) <;> decide

/-! ### Outside-the-Cone Fixed-`k` Unbounded-`t0` Cross-Carry Laws (Theorem 9.152 Outside the Cone) -/

/-- **Three-Copy Readout of `phiScale k (row t0)` Outside the Cone (`twopow k ≤ r`)**: for fixed `k` and any `r ≥ 2^k` (with no upper bound on `t0` or `r`), all three shifted copies of `row t0` in `phiScale k (row t0)` reach bit `r + 2^k`, so `(phiScale k (row t0)).testBit (r + 2^k) = rdiag (r + 2^k) t0 ⊕ rdiag r t0 ⊕ rdiag (r - 2^k) t0`. -/
theorem phiScale_row_testBit_outside_cone (t0 k r : Nat) (hr : twopow k ≤ r) :
    (phiScale k (row t0)).testBit (r + twopow k) =
      bxor (bxor (rdiag (r + twopow k) t0) (rdiag r t0)) (rdiag (r - twopow k) t0) := by
  change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (r + twopow k) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, bxor_eq_xor]
  have d1 : decide (r + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (r + twopow k ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [d1, d2, Bool.true_and, Bool.true_and,
    show r + twopow k - twopow k = r by omega,
    show r + twopow k - (twopow k + twopow k) = r - twopow k by omega,
    row_testBit t0 (r + twopow k),
    row_testBit t0 r,
    row_testBit t0 (r - twopow k)]

/-- **Four-Term Readout of `winWitt t0 (2^k)` Outside the Cone (`twopow k ≤ r`)**: for fixed `k` and any `r ≥ 2^k`, `(winWitt t0 (2^k)).testBit (r + 2^k) = rdiag (r + 2^k) (t0 + 2^k) ⊕ rdiag (r + 2^k) t0 ⊕ rdiag r t0 ⊕ rdiag (r - 2^k) t0`. -/
theorem winWitt_testBit_outside_cone (t0 k r : Nat) (hr : twopow k ≤ r) :
    (winWitt t0 (twopow k)).testBit (r + twopow k) =
      bxor (rdiag (r + twopow k) (t0 + twopow k))
        (bxor (bxor (rdiag (r + twopow k) t0) (rdiag r t0)) (rdiag (r - twopow k) t0)) := by
  have hs := congrArg (fun n => n.testBit (r + twopow k)) (row_scale t0 k)
  rw [Nat.testBit_xor, row_testBit (t0 + twopow k) (r + twopow k),
    phiScale_row_testBit_outside_cone t0 k r hr] at hs
  revert hs
  simp only [bxor_eq_xor]
  cases rdiag (r + twopow k) (t0 + twopow k) <;>
    cases (rdiag (r + twopow k) t0 ^^ rdiag r t0 ^^ rdiag (r - twopow k) t0) <;>
    cases (winWitt t0 (twopow k)).testBit (r + twopow k) <;> decide

/-- **Left-Diagonal Readout of `phiScale k (row (d + 1))` at the Center Slot `(d + 1) + 2^k` Outside the Cone (`2^k ≤ d + 1`)**: for fixed `k` and all `d + 1 ≥ 2^k`, the scaled row at the center slot `(d + 1) + 2^k` pairs the left wing `ldiag ((d + 1) - 2^k) (d + 1)`, the center `center (d + 1)`, and the right wing `rdiag ((d + 1) - 2^k) (d + 1)`. -/
theorem phiScale_row_center_slot_outside_cone (d k : Nat) (hd : twopow k ≤ d + 1) :
    (phiScale k (row (d + 1))).testBit ((d + 1) + twopow k) =
      bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
        (rdiag ((d + 1) - twopow k) (d + 1)) := by
  rw [phiScale_row_testBit_outside_cone (d + 1) k (d + 1) hd,
    ← core_center_eq_rdiag (d + 1)]
  have hl : rdiag ((d + 1) + twopow k) (d + 1) = ldiag ((d + 1) - twopow k) (d + 1) := by
    have h0 := ldiag_eq_rdiag ((d + 1) - twopow k) (twopow k)
    rw [show (d + 1) - twopow k + twopow k = d + 1 by omega,
      show (d + 1) - twopow k + 2 * twopow k = (d + 1) + twopow k by omega] at h0
    exact h0.symm
  rw [hl]

/-- **Left-Diagonal Readout of `phiScale k (row (d + 1))` at the Column-`-1` Slot `(d + 2) + 2^k` Outside the Cone (`2^k ≤ d`)**: for fixed `k` and all `d ≥ 2^k`, the scaled row at `(d + 2) + 2^k` pairs `ldiag (d - 2^k) (d + 1)`, `ldiag d (d + 1)`, and `rdiag ((d + 2) - 2^k) (d + 1)`. -/
theorem phiScale_row_colm1_outside_cone (d k : Nat) (hd : twopow k ≤ d) :
    (phiScale k (row (d + 1))).testBit ((d + 2) + twopow k) =
      bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
        (rdiag ((d + 2) - twopow k) (d + 1)) := by
  rw [phiScale_row_testBit_outside_cone (d + 1) k (d + 2) (by omega)]
  have hl1 : rdiag ((d + 2) + twopow k) (d + 1) = ldiag (d - twopow k) (d + 1) := by
    have h0 := ldiag_eq_rdiag (d - twopow k) (twopow k + 1)
    rw [show d - twopow k + (twopow k + 1) = d + 1 by omega,
      show d - twopow k + 2 * (twopow k + 1) = (d + 2) + twopow k by omega] at h0
    exact h0.symm
  have hl2 : rdiag (d + 2) (d + 1) = ldiag d (d + 1) := by
    rw [show d + 2 = d + 2 * 1 by omega, ← ldiag_eq_rdiag d 1]
  rw [hl1, hl2]

/-- **Direct Scaled-Row × Window Cross-Carry at `(d + 2) + 2^k` Outside the Cone (`periodic_crossCarry_colm1_outside_cone_and`)**: for fixed `k` and all `d ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), the cross-carry at bit `(d + 2) + 2^k` pairs the 3-term scaled row bits directly with the 4-term window bits, so neither factor in the second AND-term is a center value when `center (d + 1) = false`! -/
theorem periodic_crossCarry_colm1_outside_cone_and (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1)) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
          (bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
            (rdiag ((d + 1) - twopow k) (d + 1))))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k))
          (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
            (rdiag ((d + 2) - twopow k) (d + 1))) &&
          bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
            (rdiag ((d + 1) - twopow k) (d + 1))) := by
  have ha1 := phiScale_row_colm1_outside_cone d k hd
  have ha0 := phiScale_row_center_slot_outside_cone d k (by omega)
  have hb0 : (winWitt (d + 1) (twopow k)).testBit ((d + 1) + twopow k) =
      bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
          (rdiag ((d + 1) - twopow k) (d + 1))) := by
    have hs := congrArg (fun n => n.testBit ((d + 1) + twopow k)) (row_scale (d + 1) k)
    rw [Nat.testBit_xor, row_testBit_center ((d + 1) + twopow k),
      Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht,
      show twopow k % P = Rule30UOR.Scale.lag P k from rfl, ha0] at hs
    revert hs
    simp only [bxor_eq_xor]
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
      cases (ldiag ((d + 1) - twopow k) (d + 1) ^^ Rule30UOR.Core.center (d + 1) ^^ rdiag ((d + 1) - twopow k) (d + 1)) <;>
      cases (winWitt (d + 1) (twopow k)).testBit ((d + 1) + twopow k) <;> decide
  have hb1 : (winWitt (d + 1) (twopow k)).testBit ((d + 2) + twopow k) =
      bxor (ldiag (d + twopow k) ((d + 1) + twopow k))
        (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1))) := by
    have hs := congrArg (fun n => n.testBit ((d + 2) + twopow k)) (row_scale (d + 1) k)
    have hlate : (row ((d + 1) + twopow k)).testBit ((d + 2) + twopow k) =
        ldiag (d + twopow k) ((d + 1) + twopow k) := by
      rw [row_testBit, show (d + 2) + twopow k = (d + twopow k) + 2 * 1 by omega,
        show (d + 1) + twopow k = (d + twopow k) + 1 by omega,
        ← ldiag_eq_rdiag (d + twopow k) 1]
    rw [Nat.testBit_xor, hlate, ha1] at hs
    revert hs
    simp only [bxor_eq_xor]
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
      cases (ldiag (d - twopow k) (d + 1) ^^ ldiag d (d + 1) ^^ rdiag ((d + 2) - twopow k) (d + 1)) <;>
      cases (winWitt (d + 1) (twopow k)).testBit ((d + 2) + twopow k) <;> decide
  rw [show (d + 2) + twopow k = ((d + 1) + twopow k) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 1) + twopow k),
    show ((d + 1) + twopow k) + 1 = (d + 2) + twopow k by omega,
    ha1, ha0, hb1, hb0]

/-- **Wronskian Form of Column-`-1` Cross-Carry Outside the Cone (`periodic_crossCarry_colm1_outside_cone_wronskian`)**: for fixed `k` and all `d ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), cancelling the scaled-row self-carry reduces `(crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (2^k))).testBit ((d + 2) + 2^k)` to `((ldiag (d - 2^k) (d + 1) ⊕ ldiag d (d + 1) ⊕ rdiag ((d + 2) - 2^k) (d + 1)) && center ((d + 1) + lag P k)) ⊕ (ldiag (d + 2^k) ((d + 1) + 2^k) && (ldiag ((d + 1) - 2^k) (d + 1) ⊕ center (d + 1) ⊕ rdiag ((d + 1) - 2^k) (d + 1)))`! -/
theorem periodic_crossCarry_colm1_outside_cone_wronskian (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1)) &&
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
            (rdiag ((d + 1) - twopow k) (d + 1))) := by
  rw [periodic_crossCarry_colm1_outside_cone_and T P hP h d k ht hd]
  simp only [bxor_eq_xor]
  cases (ldiag (d - twopow k) (d + 1) ^^ ldiag d (d + 1) ^^ rdiag ((d + 2) - twopow k) (d + 1)) <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases (ldiag ((d + 1) - twopow k) (d + 1) ^^ Rule30UOR.Core.center (d + 1) ^^ rdiag ((d + 1) - twopow k) (d + 1)) <;>
    rfl

/-- **Theorem 9.152 Outside the Cone (`periodic_crossCarry_colm1_outside_cone_at_white_center`)**: for fixed `k` and all `d ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), whenever `center (d + 1) = false`, the second AND-term in `crossCarry` does NOT vanish as it did inside the cone; instead, `center (d + 1) = false` drops out and leaves the non-center AND-product `ldiag (d + 2^k) ((d + 1) + 2^k) && (ldiag ((d + 1) - 2^k) (d + 1) ⊕ rdiag ((d + 1) - 2^k) (d + 1))`! -/
theorem periodic_crossCarry_colm1_outside_cone_at_white_center (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1)) &&
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))) := by
  rw [periodic_crossCarry_colm1_outside_cone_wronskian T P hP h d k ht hd, hw]
  simp only [bxor_eq_xor, Bool.xor_false]

/-- **Pure Non-Center AND-Product at `(d + 2) + 2^k` Outside the Cone on White Early and Late Centers (`periodic_crossCarry_colm1_outside_cone_at_both_white_centers`)**: for fixed `k` and all `d ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), whenever `center (d + 1) = false` and `center ((d + 1) + lag P k) = false`, the cross-carry at bit `(d + 2) + 2^k` collapses to the single AND-product `ldiag (d + 2^k) ((d + 1) + 2^k) && (ldiag ((d + 1) - 2^k) (d + 1) ⊕ rdiag ((d + 1) - 2^k) (d + 1))`, whose two factors are both non-center values! -/
theorem periodic_crossCarry_colm1_outside_cone_at_both_white_centers (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      (ldiag (d + twopow k) ((d + 1) + twopow k) &&
        bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))) := by
  rw [periodic_crossCarry_colm1_outside_cone_at_white_center T P hP h d k ht hd hw1, hw2]
  simp only [bxor_eq_xor, Bool.and_false, Bool.false_xor]

/-- **Universal Reduction of Column-`-1` Cross-Carry on White Late Center Steps (`crossCarry_colm1_at_white_late_center_eq_and_witt`)**: at EVERY time `d` and scale `k` (inside OR outside the cone!), whenever `center ((d + 1) + 2^k) = false`, the first Wronskian branch in `crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (2^k))` at bit `(d + 2) + 2^k` vanishes and `(phiScale k (row (d + 1))).testBit ((d + 1) + 2^k) = wittRespBool (d + 1) k`, so the cross-carry equals `ldiag (d + 2^k) ((d + 1) + 2^k) && wittRespBool (d + 1) k`! -/
theorem crossCarry_colm1_at_white_late_center_eq_and_witt (d k : Nat)
    (hw_late : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      (ldiag (d + twopow k) ((d + 1) + twopow k) && wittRespBool (d + 1) k) := by
  rw [crossCarry_row_scale_eq_crossCarry_late_row (d + 1) k,
    show (d + 2) + twopow k = ((d + 1) + twopow k) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row (d + 1))) (row ((d + 1) + twopow k)) ((d + 1) + twopow k),
    show ((d + 1) + twopow k) + 1 = (d + 2) + twopow k by omega,
    row_testBit_center ((d + 1) + twopow k), hw_late,
    Bool.and_false, bxor_eq_xor, Bool.false_xor]
  have hlate : (row ((d + 1) + twopow k)).testBit ((d + 2) + twopow k) =
      ldiag (d + twopow k) ((d + 1) + twopow k) := by
    rw [row_testBit, show (d + 2) + twopow k = (d + twopow k) + 2 * 1 by omega,
      show (d + 1) + twopow k = (d + twopow k) + 1 by omega,
      ← ldiag_eq_rdiag (d + twopow k) 1]
  have ha0 : (phiScale k (row (d + 1))).testBit ((d + 1) + twopow k) = wittRespBool (d + 1) k := by
    have hs := congrArg (fun n => n.testBit ((d + 1) + twopow k)) (row_scale (d + 1) k)
    rw [Nat.testBit_xor, row_testBit_center ((d + 1) + twopow k), hw_late] at hs
    revert hs
    change (false = ((phiScale k (row (d + 1))).testBit ((d + 1) + twopow k) ^^ wittRespBool (d + 1) k)) → _
    cases (phiScale k (row (d + 1))).testBit ((d + 1) + twopow k) <;>
      cases wittRespBool (d + 1) k <;> decide
  rw [hlate, ha0]

/-- **Outside-the-Cone Column-`-1` Cross-Carry on White Late Center Steps via `response` and `rdiag` (`crossCarry_colm1_outside_cone_at_white_late_center_via_response`)**: for fixed `k` and all `d + 1 ≥ 2^k` with `center ((d + 1) + 2^k) = false`, combining `crossCarry_colm1_at_white_late_center_eq_and_witt` with `wittRespBool_xor_response_ge` expresses the cross-carry at `(d + 2) + 2^k` as the non-center AND-product `ldiag (d + 2^k) ((d + 1) + 2^k) && (response (d + 1) k ⊕ rdiag ((d + 1) - 2^k) (d + 1))`! -/
theorem crossCarry_colm1_outside_cone_at_white_late_center_via_response (d k : Nat)
    (hd : twopow k ≤ d + 1)
    (hw_late : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    (crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k) =
      (ldiag (d + twopow k) ((d + 1) + twopow k) &&
        bxor (Rule30UOR.Scale.response (d + 1) k) (rdiag ((d + 1) - twopow k) (d + 1))) := by
  rw [crossCarry_colm1_at_white_late_center_eq_and_witt d k hw_late]
  have hdu := wittRespBool_xor_response_ge (d + 1) k hd
  have hw : wittRespBool (d + 1) k =
      bxor (Rule30UOR.Scale.response (d + 1) k) (rdiag ((d + 1) - twopow k) (d + 1)) := by
    revert hdu
    simp only [bxor_eq_xor]
    cases wittRespBool (d + 1) k <;>
      cases Rule30UOR.Scale.response (d + 1) k <;>
      cases rdiag ((d + 1) - twopow k) (d + 1) <;> decide
  rw [hw]

/-- Paper-facing `bit` wrapper for `phiScale_row_testBit_outside_cone`. -/
theorem phiScale_row_testBit_outside_cone_prop (t0 k r : Nat) (hr : twopow k ≤ r) :
    bit (phiScale k (row t0)) (r + twopow k) =
      bton (bxor (bxor (rdiag (r + twopow k) t0) (rdiag r t0)) (rdiag (r - twopow k) t0)) := by
  rw [bit_eq_bton_testBit, phiScale_row_testBit_outside_cone t0 k r hr]

/-- Paper-facing `BitWinWittEq` wrapper for `winWitt_testBit_outside_cone`. -/
theorem winWitt_testBit_outside_cone_prop (t0 k r : Nat) (hr : twopow k ≤ r) :
    BitWinWittEq t0 (twopow k) (r + twopow k)
      (bxor (rdiag (r + twopow k) (t0 + twopow k))
        (bxor (bxor (rdiag (r + twopow k) t0) (rdiag r t0)) (rdiag (r - twopow k) t0))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit, winWitt_testBit_outside_cone t0 k r hr]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_outside_cone_and`. -/
theorem periodic_crossCarry_colm1_outside_cone_and_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1)) &&
        bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
          (bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
            (rdiag ((d + 1) - twopow k) (d + 1))))
        (bxor (ldiag (d + twopow k) ((d + 1) + twopow k))
          (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
            (rdiag ((d + 2) - twopow k) (d + 1))) &&
          bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
            (rdiag ((d + 1) - twopow k) (d + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_outside_cone_and T P hP h d k ht hd]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_outside_cone_wronskian`. -/
theorem periodic_crossCarry_colm1_outside_cone_wronskian_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1)) &&
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (bxor (ldiag ((d + 1) - twopow k) (d + 1)) (Rule30UOR.Core.center (d + 1)))
            (rdiag ((d + 1) - twopow k) (d + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_outside_cone_wronskian T P hP h d k ht hd]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_outside_cone_at_white_center`. -/
theorem periodic_crossCarry_colm1_outside_cone_at_white_center_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d)
    (hw : Rule30UOR.Core.center (d + 1) = false) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (bxor (bxor (bxor (ldiag (d - twopow k) (d + 1)) (ldiag d (d + 1)))
          (rdiag ((d + 2) - twopow k) (d + 1)) &&
        Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k))
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_outside_cone_at_white_center T P hP h d k ht hd hw]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_outside_cone_at_both_white_centers`. -/
theorem periodic_crossCarry_colm1_outside_cone_at_both_white_centers_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hd : twopow k ≤ d)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (ldiag (d + twopow k) ((d + 1) + twopow k) &&
        bxor (ldiag ((d + 1) - twopow k) (d + 1)) (rdiag ((d + 1) - twopow k) (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_colm1_outside_cone_at_both_white_centers T P hP h d k ht hd hw1 hw2]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_colm1_at_white_late_center_eq_and_witt`. -/
theorem crossCarry_colm1_at_white_late_center_eq_and_witt_prop (d k : Nat)
    (hw_late : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (ldiag (d + twopow k) ((d + 1) + twopow k) && wittRespBool (d + 1) k) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_colm1_at_white_late_center_eq_and_witt d k hw_late]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_colm1_outside_cone_at_white_late_center_via_response`. -/
theorem crossCarry_colm1_outside_cone_at_white_late_center_via_response_prop (d k : Nat)
    (hd : twopow k ≤ d + 1)
    (hw_late : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    BitCrossCarryEq (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k)) ((d + 2) + twopow k)
      (ldiag (d + twopow k) ((d + 1) + twopow k) &&
        bxor (Rule30UOR.Scale.response (d + 1) k) (rdiag ((d + 1) - twopow k) (d + 1))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_colm1_outside_cone_at_white_late_center_via_response d k hd hw_late]

/-! ### Outside-the-Cone Cross-Carry at the Center Bit `(s + 1) + 2^k` (Theorem 9.152 Outside the Cone at the Center Slot) -/

/-- **Left-Diagonal Readout of `phiScale k (row (s + 1))` at the Column-`+1` Slot `s + 2^k` Outside the Cone (`2^k ≤ s`)**: for fixed `k` and all `s ≥ 2^k` (with no upper bound on `s`), all three shifted copies of `row (s + 1)` in `phiScale k (row (s + 1))` reach bit `s + 2^k`, and `(phiScale k (row (s + 1))).testBit (s + 2^k) = ldiag ((s + 2) - 2^k) (s + 1) ⊕ rdiag s (s + 1) ⊕ rdiag (s - 2^k) (s + 1)`. -/
theorem phiScale_row_col1_outside_cone (s k : Nat) (hs : twopow k ≤ s) :
    (phiScale k (row (s + 1))).testBit (s + twopow k) =
      bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
        (rdiag (s - twopow k) (s + 1)) := by
  rw [phiScale_row_testBit_outside_cone (s + 1) k s hs]
  have hl : rdiag (s + twopow k) (s + 1) = ldiag ((s + 2) - twopow k) (s + 1) := by
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
  rw [hl]

/-- **Exact Cross-Carry at the Center Bit `(s + 1) + 2^k` Outside the Cone (`crossCarry_row_scale_at_center_bit_outside_cone_and`)**: for fixed `k` and all `s ≥ 2^k` (with NO upper bound on `s`), the cross-carry `(crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` at the center slot `(s + 1) + 2^k` pairs the 3-term scaled row bits at `(s + 1) + 2^k` and `s + 2^k` with the window bits `wittRespBool (s + 1) k` and `(winWitt (s + 1) (2^k)).testBit (s + 2^k)`! -/
theorem crossCarry_row_scale_at_center_bit_outside_cone_and (s k : Nat) (hs : twopow k ≤ s) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (Rule30UOR.Core.center (s + 1)))
          (rdiag ((s + 1) - twopow k) (s + 1)) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k))
          (bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))))
        (wittRespBool (s + 1) k &&
          bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))) := by
  have ha1 := phiScale_row_center_slot_outside_cone s k (by omega)
  have ha0 := phiScale_row_col1_outside_cone s k hs
  have hb0 : (winWitt (s + 1) (twopow k)).testBit (s + twopow k) =
      bxor (rdiag (s + twopow k) ((s + 1) + twopow k))
        (bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
          (rdiag (s - twopow k) (s + 1))) := by
    have hs0 := congrArg (fun n => n.testBit (s + twopow k)) (row_scale (s + 1) k)
    rw [Nat.testBit_xor, row_testBit ((s + 1) + twopow k) (s + twopow k), ha0] at hs0
    revert hs0
    simp only [bxor_eq_xor]
    cases rdiag (s + twopow k) ((s + 1) + twopow k) <;>
      cases (ldiag ((s + 2) - twopow k) (s + 1) ^^ rdiag s (s + 1) ^^ rdiag (s - twopow k) (s + 1)) <;>
      cases (winWitt (s + 1) (twopow k)).testBit (s + twopow k) <;> decide
  rw [show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
    crossCarry_testBit_succ (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) (s + twopow k),
    show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
    ha1, ha0, hb0]
  rfl

/-- **Theorem 9.152 Outside the Cone at the Center Slot on White Center Steps (`crossCarry_at_white_center_outside_cone_noncenter_and`)**: for fixed `k` and all `s ≥ 2^k` (with NO upper bound on `s`), whenever `center (s + 1) = false`, `center (s + 1)` drops out of `(phiScale k (row (s + 1))).testBit ((s + 1) + 2^k)`, leaving the non-center factor `ldiag ((s + 1) - 2^k) (s + 1) ⊕ rdiag ((s + 1) - 2^k) (s + 1)` paired directly with the window bit at `s + 2^k`! -/
theorem crossCarry_at_white_center_outside_cone_noncenter_and (s k : Nat) (hs : twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (rdiag ((s + 1) - twopow k) (s + 1)) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k))
          (bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))))
        (wittRespBool (s + 1) k &&
          bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))) := by
  rw [crossCarry_row_scale_at_center_bit_outside_cone_and s k hs, hw]
  simp only [bxor_eq_xor, Bool.xor_false]

/-- **Universal Wronskian Form of the Center-Slot Cross-Carry Outside the Cone (`crossCarry_at_center_bit_outside_cone_wronskian`)**: for fixed `k` and all `s ≥ 2^k` (with NO upper bound on `s`), cancelling the scaled-row self-carry reduces `(crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` to `((ldiag ((s + 1) - 2^k) (s + 1) ⊕ center (s + 1) ⊕ rdiag ((s + 1) - 2^k) (s + 1)) && rdiag (s + 2^k) (s + 1 + 2^k)) ⊕ (center (s + 1 + 2^k) && (ldiag ((s + 2) - 2^k) (s + 1) ⊕ rdiag s (s + 1) ⊕ rdiag (s - 2^k) (s + 1)))`! -/
theorem crossCarry_at_center_bit_outside_cone_wronskian (s k : Nat) (hs : twopow k ≤ s) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      bxor (bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (Rule30UOR.Core.center (s + 1)))
          (rdiag ((s + 1) - twopow k) (s + 1)) &&
        rdiag (s + twopow k) ((s + 1) + twopow k))
        (Rule30UOR.Core.center ((s + 1) + twopow k) &&
          bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))) := by
  have hc := crossCarry_testBit_succ (phiScale k (row (s + 1))) (row ((s + 1) + twopow k)) (s + twopow k)
  rw [show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
    phiScale_row_center_slot_outside_cone s k (by omega),
    phiScale_row_col1_outside_cone s k hs,
    row_testBit_center ((s + 1) + twopow k),
    row_testBit ((s + 1) + twopow k) (s + twopow k)] at hc
  rw [crossCarry_row_scale_eq_crossCarry_late_row (s + 1) k, hc]

/-- **Pure Non-Center AND-Product at the Center Slot `(s + 1) + 2^k` Outside the Cone on White Early and Late Centers (`periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity`)**: for fixed `k` and all `s ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), whenever `center (s + 1) = false` and `center (s + 1 + lag P k) = false`, the second Wronskian branch vanishes and `rdiag (s + 2^k) (s + 1 + 2^k) = maskparity (s + 1 + 2^k) 0` (since `center (s + 1 + 2^k) = false`), so the center-slot cross-carry collapses to the pure non-center AND-product `(ldiag ((s + 1) - 2^k) (s + 1) ⊕ rdiag ((s + 1) - 2^k) (s + 1)) && maskparity (s + 1 + 2^k) 0`! -/
theorem periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : twopow k ≤ s)
    (hw1 : Rule30UOR.Core.center (s + 1) = false)
    (hw2 : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (rdiag ((s + 1) - twopow k) (s + 1)) &&
        Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) := by
  have hw_late : Rule30UOR.Core.center ((s + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (s + 1) (twopow k) ht]
    exact hw2
  have hm_late : Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0 =
      rdiag (s + twopow k) ((s + 1) + twopow k) := by
    have hm0 := maskparity_succ_zero_eq_rdiag (s + twopow k)
    rw [show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
      ← core_center_eq_rdiag ((s + 1) + twopow k), hw_late,
      Bool.not_false, Bool.true_and] at hm0
    exact hm0
  rw [crossCarry_at_center_bit_outside_cone_wronskian s k hs, hw1, hw_late, hm_late]
  simp only [bxor_eq_xor, Bool.xor_false, Bool.false_and]

/-- **Universal Reduction of Center-Slot Cross-Carry on White Late Center Steps (`crossCarry_at_white_late_center_eq_witt_and_maskparity`)**: at EVERY time `s` and scale `k` (inside OR outside the cone!), whenever `center ((s + 1) + 2^k) = false`, the second Wronskian branch in `(crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (2^k))).testBit ((s + 1) + 2^k)` vanishes, `(phiScale k (row (s + 1))).testBit ((s + 1) + 2^k) = wittRespBool (s + 1) k`, and `rdiag (s + 2^k) (s + 1 + 2^k) = maskparity (s + 1 + 2^k) 0`, so the center-slot cross-carry equals `wittRespBool (s + 1) k && maskparity (s + 1 + 2^k) 0`! -/
theorem crossCarry_at_white_late_center_eq_witt_and_maskparity (s k : Nat)
    (hw_late : Rule30UOR.Core.center ((s + 1) + twopow k) = false) :
    (crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k) =
      (wittRespBool (s + 1) k && Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) := by
  have hc := crossCarry_testBit_succ (phiScale k (row (s + 1))) (row ((s + 1) + twopow k)) (s + twopow k)
  rw [show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
    row_testBit_center ((s + 1) + twopow k), hw_late,
    Bool.false_and, bxor_eq_xor, Bool.xor_false,
    row_testBit ((s + 1) + twopow k) (s + twopow k)] at hc
  rw [crossCarry_row_scale_eq_crossCarry_late_row (s + 1) k, hc]
  have ha1 : (phiScale k (row (s + 1))).testBit ((s + 1) + twopow k) = wittRespBool (s + 1) k := by
    have hs0 := congrArg (fun n => n.testBit ((s + 1) + twopow k)) (row_scale (s + 1) k)
    rw [Nat.testBit_xor, row_testBit_center ((s + 1) + twopow k), hw_late] at hs0
    revert hs0
    change (false = ((phiScale k (row (s + 1))).testBit ((s + 1) + twopow k) ^^ wittRespBool (s + 1) k)) → _
    cases (phiScale k (row (s + 1))).testBit ((s + 1) + twopow k) <;>
      cases wittRespBool (s + 1) k <;> decide
  have hm_late : Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0 =
      rdiag (s + twopow k) ((s + 1) + twopow k) := by
    have hm0 := maskparity_succ_zero_eq_rdiag (s + twopow k)
    rw [show (s + twopow k) + 1 = (s + 1) + twopow k by omega,
      ← core_center_eq_rdiag ((s + 1) + twopow k), hw_late,
      Bool.not_false, Bool.true_and] at hm0
    exact hm0
  rw [ha1, hm_late]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_row_scale_at_center_bit_outside_cone_and`. -/
theorem crossCarry_row_scale_at_center_bit_outside_cone_and_prop (s k : Nat) (hs : twopow k ≤ s) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (Rule30UOR.Core.center (s + 1)))
          (rdiag ((s + 1) - twopow k) (s + 1)) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k))
          (bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))))
        (wittRespBool (s + 1) k &&
          bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_row_scale_at_center_bit_outside_cone_and s k hs]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_at_white_center_outside_cone_noncenter_and`. -/
theorem crossCarry_at_white_center_outside_cone_noncenter_and_prop (s k : Nat) (hs : twopow k ≤ s)
    (hw : Rule30UOR.Core.center (s + 1) = false) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (rdiag ((s + 1) - twopow k) (s + 1)) &&
        bxor (rdiag (s + twopow k) ((s + 1) + twopow k))
          (bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1))))
        (wittRespBool (s + 1) k &&
          bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_at_white_center_outside_cone_noncenter_and s k hs hw]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_at_center_bit_outside_cone_wronskian`. -/
theorem crossCarry_at_center_bit_outside_cone_wronskian_prop (s k : Nat) (hs : twopow k ≤ s) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (bxor (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (Rule30UOR.Core.center (s + 1)))
          (rdiag ((s + 1) - twopow k) (s + 1)) &&
        rdiag (s + twopow k) ((s + 1) + twopow k))
        (Rule30UOR.Core.center ((s + 1) + twopow k) &&
          bxor (bxor (ldiag ((s + 2) - twopow k) (s + 1)) (rdiag s (s + 1)))
            (rdiag (s - twopow k) (s + 1)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_at_center_bit_outside_cone_wronskian s k hs]

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity`. -/
theorem periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (s k : Nat) (ht : T ≤ s + 1) (hs : twopow k ≤ s)
    (hw1 : Rule30UOR.Core.center (s + 1) = false)
    (hw2 : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (bxor (ldiag ((s + 1) - twopow k) (s + 1)) (rdiag ((s + 1) - twopow k) (s + 1)) &&
        Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    periodic_crossCarry_at_both_white_centers_outside_cone_eq_maskparity T P hP h s k ht hs hw1 hw2]

/-- Paper-facing `BitCrossCarryEq` wrapper for `crossCarry_at_white_late_center_eq_witt_and_maskparity`. -/
theorem crossCarry_at_white_late_center_eq_witt_and_maskparity_prop (s k : Nat)
    (hw_late : Rule30UOR.Core.center ((s + 1) + twopow k) = false) :
    BitCrossCarryEq (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k)) ((s + 1) + twopow k)
      (wittRespBool (s + 1) k && Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit,
    crossCarry_at_white_late_center_eq_witt_and_maskparity s k hw_late]

/-! ### Fixed-`k` Unbounded-`t` Period-Shift Laws Outside the Cone (Masked-Jen Form) -/

/-- **Universal Periodicity of `CenterPeriodic T P` at Multiples `m * P`**: if `CenterPeriodic T P` holds (`0 < P`), then for every `t ≥ T` and every multiple `m * P`, `center (t + m * P) = center t`. -/
theorem center_periodic_mul (T P : Nat) (h : Rule30UOR.Scale.CenterPeriodic T P) :
    ∀ m t : Nat, T ≤ t → Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t
  | 0, t, _ => by simp
  | m + 1, t, ht => by
    rw [show t + (m + 1) * P = (t + m * P) + P by rw [Nat.succ_mul]; omega,
      h (t + m * P) (by omega),
      center_periodic_mul T P h m t ht]

/-- **Under `CenterPeriodic T P`, `m * P`-Periodicity of `maskparity · 0` Equals `m * P`-Periodicity of Column `-1` (`periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul`)**: for every `m : Nat` and all `d + 1 ≥ T`, `maskparity (d + m * P + 1) 0 ⊕ maskparity (d + 1) 0 = ldiag (d + m * P) (d + m * P + 1) ⊕ ldiag d (d + 1)`. -/
theorem periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d : Nat) (ht : T ≤ d + 1) :
    bxor (Rule30UOR.Scale.maskparity ((d + m * P) + 1) 0) (Rule30UOR.Scale.maskparity (d + 1) 0) =
      bxor (ldiag (d + m * P) ((d + m * P) + 1)) (ldiag d (d + 1)) := by
  have hs1 := Rule30UOR.Scale.scale_center_paper (d + 1) 0
  have hs2 := Rule30UOR.Scale.scale_center_paper ((d + m * P) + 1) 0
  rw [show twopow 0 = 1 from rfl,
    show Rule30UOR.Scale.negpow 0 = -1 from rfl,
    response_zero_eq_maskparity_zero] at hs1 hs2
  have hl1 : Rule30UOR.Core.cell (d + 1) (-1) = ldiag d (d + 1) :=
    (ldiag_eq_cell_neg d 1).symm
  have hl2 : Rule30UOR.Core.cell ((d + m * P) + 1) (-1) = ldiag (d + m * P) ((d + m * P) + 1) :=
    (ldiag_eq_cell_neg (d + m * P) 1).symm
  have hc1 := center_periodic_mul T P h m (d + 1) ht
  have hc2 := center_periodic_mul T P h m (d + 2) (by omega)
  rw [show (d + 1) + m * P = (d + m * P) + 1 by omega] at hc1
  rw [show (d + 2) + m * P = ((d + m * P) + 1) + 1 by omega,
    show d + 2 = (d + 1) + 1 by omega] at hc2
  rw [hl1] at hs1
  rw [hl2, hc1, hc2] at hs2
  revert hs1 hs2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center ((d + 1) + 1) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases ldiag (d + m * P) ((d + m * P) + 1) <;>
    cases ldiag d (d + 1) <;>
    cases Rule30UOR.Scale.maskparity ((d + m * P) + 1) 0 <;>
    cases Rule30UOR.Scale.maskparity (d + 1) 0 <;> decide

/-- **Fixed-`k` Unbounded-`t` Outside-the-Cone `m * P`-Shift of `wittRespBool` vs `response` (`wittRespBool_xor_response_shift_mul_ outside_cone`)**: for fixed `k` and ALL `t ≥ 2^k` (unbounded `t`), shifting `t` by any period multiple `m * P` links the `m * P`-defect of `wittRespBool · k` and the `m * P`-defect of `response · k` directly to the `m * P`-defect along the right-diagonal ray `rdiag ((t + m * P) - 2^k) (t + m * P) ⊕ rdiag (t - 2^k) t` (cell `(t, +2^k)`)! -/
theorem wittRespBool_xor_response_shift_mul_outside_cone (t k m P : Nat) (hk : twopow k ≤ t) :
    bxor (bxor (wittRespBool (t + m * P) k) (wittRespBool t k))
      (bxor (Rule30UOR.Scale.response (t + m * P) k) (Rule30UOR.Scale.response t k)) =
      bxor (rdiag ((t + m * P) - twopow k) (t + m * P)) (rdiag (t - twopow k) t) := by
  have h1 := wittRespBool_xor_response_ge (t + m * P) k (by omega)
  have h2 := wittRespBool_xor_response_ge t k hk
  rw [bxor_four_swap, h1, h2]

/-- **Fixed-`k` Unbounded-`t` Outside-the-Cone `m * P`-Shift of `wittRespBool` under `CenterPeriodic T P` (`periodic_wittRespBool_shift_mul_outside_cone`)**: for fixed `k` and ALL `t ≥ max(T, 2^k)` under `CenterPeriodic T P` (`0 < P`), the center lag difference `center (t + lag P k) ⊕ center t` cancels identically between `t` and `t + m * P`, so the `m * P`-defect of `wittRespBool · k` equals the `m * P`-defect of the left-wing cell `ldiag (t - 2^k) t` (`cell t (-2^k)`) XORed with the `m * P`-defect of the right-wing cell `rdiag (t - 2^k) t` (`cell t (+2^k)`)! -/
theorem periodic_wittRespBool_shift_mul_outside_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k m : Nat) (ht : T ≤ t) (hk : twopow k ≤ t) :
    bxor (wittRespBool (t + m * P) k) (wittRespBool t k) =
      bxor (bxor (ldiag ((t + m * P) - twopow k) (t + m * P)) (ldiag (t - twopow k) t))
        (bxor (rdiag ((t + m * P) - twopow k) (t + m * P)) (rdiag (t - twopow k) t)) := by
  have hs1 := Rule30UOR.Scale.periodic_scale_paper T P hP h k (t + m * P) (by omega)
  have hs2 := Rule30UOR.Scale.periodic_scale_paper T P hP h k t ht
  have hl1 : Rule30UOR.Core.cell (t + m * P) (Rule30UOR.Scale.negpow k) =
      ldiag ((t + m * P) - twopow k) (t + m * P) := by
    have h0 := ldiag_eq_cell_neg ((t + m * P) - twopow k) (twopow k)
    rw [show (t + m * P) - twopow k + twopow k = t + m * P by omega] at h0
    exact h0.symm
  have hl2 : Rule30UOR.Core.cell t (Rule30UOR.Scale.negpow k) =
      ldiag (t - twopow k) t := by
    have h0 := ldiag_eq_cell_neg (t - twopow k) (twopow k)
    rw [show t - twopow k + twopow k = t by omega] at h0
    exact h0.symm
  have hc1 := center_periodic_mul T P h m (t + Rule30UOR.Scale.lag P k) (by omega)
  have hc2 := center_periodic_mul T P h m t ht
  rw [show (t + Rule30UOR.Scale.lag P k) + m * P = (t + m * P) + Rule30UOR.Scale.lag P k by omega] at hc1
  rw [hl1, hc1, hc2] at hs1
  rw [hl2] at hs2
  have hw := wittRespBool_xor_response_shift_mul_outside_cone t k m P hk
  revert hs1 hs2 hw
  simp only [bxor_eq_xor]
  cases wittRespBool (t + m * P) k <;>
    cases wittRespBool t k <;>
    cases Rule30UOR.Scale.response (t + m * P) k <;>
    cases Rule30UOR.Scale.response t k <;>
    cases ldiag ((t + m * P) - twopow k) (t + m * P) <;>
    cases ldiag (t - twopow k) t <;>
    cases rdiag ((t + m * P) - twopow k) (t + m * P) <;>
    cases rdiag (t - twopow k) t <;>
    cases (Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k) ^^ Rule30UOR.Core.center t) <;>
    decide

/-- **Fixed-`k` Unbounded-`d` `m * P`-Shift of Column-`-1` Cross-Carry on White Late Centers (`periodic_crossCarry_colm1_shift_mul_at_white_late_center`)**: for fixed `k`, any period multiple `m * P`, and ALL `d + 1 ≥ T` under `CenterPeriodic T P` (`0 < P`), whenever `center ((d + 1) + lag P k) = false`, shifting `d` by `m * P` in `crossCarry_colm1_at_white_late_center_eq_and_witt` yields an exact AND-difference where the late column-`-1` factor `ldiag (d + 2^k) ((d + 1) + 2^k)` has `m * P`-defect equal to the `maskparity · 0` `m * P`-defect `maskparity ((d + m * P + 1) + 2^k) 0 ⊕ maskparity ((d + 1) + 2^k) 0`! -/
theorem periodic_crossCarry_colm1_shift_mul_at_white_late_center (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1)
    (hw_late : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    bxor ((crossCarry (phiScale k (row ((d + m * P) + 1))) (winWitt ((d + m * P) + 1) (twopow k))).testBit
        (((d + m * P) + 2) + twopow k))
      ((crossCarry (phiScale k (row (d + 1))) (winWitt (d + 1) (twopow k))).testBit ((d + 2) + twopow k)) =
      bxor (bxor (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow k) 0)
          (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0) &&
        wittRespBool ((d + m * P) + 1) k)
        (ldiag (d + twopow k) ((d + 1) + twopow k) &&
          bxor (wittRespBool ((d + m * P) + 1) k) (wittRespBool (d + 1) k)) := by
  have hw1 : Rule30UOR.Core.center ((d + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht]
    exact hw_late
  have hw2 : Rule30UOR.Core.center (((d + m * P) + 1) + twopow k) = false := by
    rw [show ((d + m * P) + 1) + twopow k = ((d + 1) + twopow k) + m * P by omega,
      center_periodic_mul T P h m ((d + 1) + twopow k) (by omega)]
    exact hw1
  rw [crossCarry_colm1_at_white_late_center_eq_and_witt (d + m * P) k hw2,
    crossCarry_colm1_at_white_late_center_eq_and_witt d k hw1]
  have hm := periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul T P hP h m (d + twopow k) (by omega)
  rw [show (d + twopow k) + m * P = (d + m * P) + twopow k by omega,
    show ((d + m * P) + twopow k) + 1 = ((d + m * P) + 1) + twopow k by omega,
    show (d + twopow k) + 1 = (d + 1) + twopow k by omega] at hm
  revert hm
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow k) 0 <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 <;>
    cases ldiag ((d + m * P) + twopow k) (((d + m * P) + 1) + twopow k) <;>
    cases ldiag (d + twopow k) ((d + 1) + twopow k) <;>
    cases wittRespBool ((d + m * P) + 1) k <;>
    cases wittRespBool (d + 1) k <;> decide

/-- **Fixed-`k` Unbounded-`s` `m * P`-Shift of Center-Slot Cross-Carry on White Late Centers (`periodic_crossCarry_center_bit_shift_mul_at_white_late_center`)**: for fixed `k`, any period multiple `m * P`, and ALL `s + 1 ≥ T` under `CenterPeriodic T P` (`0 < P`), whenever `center ((s + 1) + lag P k) = false`, shifting `s` by `m * P` in `crossCarry_at_white_late_center_eq_witt_and_maskparity` expresses the `m * P`-shift of the center-slot cross-carry directly in terms of `wittRespBool (s + 1) k && (maskparity ((s + m * P + 1) + 2^k) 0 ⊕ maskparity ((s + 1) + 2^k) 0)` and `(wittRespBool (s + m * P + 1) k ⊕ wittRespBool (s + 1) k) && maskparity ((s + m * P + 1) + 2^k) 0`! -/
theorem periodic_crossCarry_center_bit_shift_mul_at_white_late_center (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m s k : Nat) (ht : T ≤ s + 1)
    (hw_late : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    bxor ((crossCarry (phiScale k (row ((s + m * P) + 1))) (winWitt ((s + m * P) + 1) (twopow k))).testBit
        (((s + m * P) + 1) + twopow k))
      ((crossCarry (phiScale k (row (s + 1))) (winWitt (s + 1) (twopow k))).testBit ((s + 1) + twopow k)) =
      bxor (bxor (wittRespBool ((s + m * P) + 1) k) (wittRespBool (s + 1) k) &&
        Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0)
        (wittRespBool (s + 1) k &&
          bxor (Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0)
            (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0)) := by
  have hw1 : Rule30UOR.Core.center ((s + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (s + 1) (twopow k) ht]
    exact hw_late
  have hw2 : Rule30UOR.Core.center (((s + m * P) + 1) + twopow k) = false := by
    rw [show ((s + m * P) + 1) + twopow k = ((s + 1) + twopow k) + m * P by omega,
      center_periodic_mul T P h m ((s + 1) + twopow k) (by omega)]
    exact hw1
  rw [crossCarry_at_white_late_center_eq_witt_and_maskparity (s + m * P) k hw2,
    crossCarry_at_white_late_center_eq_witt_and_maskparity s k hw1]
  simp only [bxor_eq_xor]
  cases wittRespBool ((s + m * P) + 1) k <;>
    cases wittRespBool (s + 1) k <;>
    cases Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0 <;>
    cases Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0 <;> rfl

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_colm1_shift_mul_at_white_late_center`. -/
theorem periodic_crossCarry_colm1_shift_mul_at_white_late_center_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m d k : Nat) (ht : T ≤ d + 1)
    (hw_late : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false) :
    BitCrossCarryEq (phiScale k (row ((d + m * P) + 1))) (winWitt ((d + m * P) + 1) (twopow k))
      (((d + m * P) + 2) + twopow k)
      (bxor (ldiag (d + twopow k) ((d + 1) + twopow k) && wittRespBool (d + 1) k)
        (bxor (bxor (Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow k) 0)
            (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0) &&
          wittRespBool ((d + m * P) + 1) k)
          (ldiag (d + twopow k) ((d + 1) + twopow k) &&
            bxor (wittRespBool ((d + m * P) + 1) k) (wittRespBool (d + 1) k)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit]
  have hs := periodic_crossCarry_colm1_shift_mul_at_white_late_center T P hP h m d k ht hw_late
  have hw1 : Rule30UOR.Core.center ((d + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht]
    exact hw_late
  rw [crossCarry_colm1_at_white_late_center_eq_and_witt d k hw1] at hs
  revert hs
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row ((d + m * P) + 1))) (winWitt ((d + m * P) + 1) (twopow k))).testBit
      (((d + m * P) + 2) + twopow k) <;>
    cases (ldiag (d + twopow k) ((d + 1) + twopow k) && wittRespBool (d + 1) k) <;>
    cases (((Rule30UOR.Scale.maskparity (((d + m * P) + 1) + twopow k) 0 ^^
      Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0) &&
      wittRespBool ((d + m * P) + 1) k) ^^
      (ldiag (d + twopow k) ((d + 1) + twopow k) &&
      (wittRespBool ((d + m * P) + 1) k ^^ wittRespBool (d + 1) k))) <;> decide

/-- Paper-facing `BitCrossCarryEq` wrapper for `periodic_crossCarry_center_bit_shift_mul_at_white_late_center`. -/
theorem periodic_crossCarry_center_bit_shift_mul_at_white_late_center_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m s k : Nat) (ht : T ≤ s + 1)
    (hw_late : Rule30UOR.Core.center ((s + 1) + Rule30UOR.Scale.lag P k) = false) :
    BitCrossCarryEq (phiScale k (row ((s + m * P) + 1))) (winWitt ((s + m * P) + 1) (twopow k))
      (((s + m * P) + 1) + twopow k)
      (bxor (wittRespBool (s + 1) k && Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0)
        (bxor (bxor (wittRespBool ((s + m * P) + 1) k) (wittRespBool (s + 1) k) &&
          Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0)
          (wittRespBool (s + 1) k &&
            bxor (Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0)
              (Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0)))) := by
  rw [BitCrossCarryEq, bit_eq_bton_testBit]
  have hs := periodic_crossCarry_center_bit_shift_mul_at_white_late_center T P hP h m s k ht hw_late
  have hw1 : Rule30UOR.Core.center ((s + 1) + twopow k) = false := by
    rw [Rule30UOR.Scale.center_mod hP h (s + 1) (twopow k) ht]
    exact hw_late
  rw [crossCarry_at_white_late_center_eq_witt_and_maskparity s k hw1] at hs
  revert hs
  simp only [bxor_eq_xor]
  cases (crossCarry (phiScale k (row ((s + m * P) + 1))) (winWitt ((s + m * P) + 1) (twopow k))).testBit
      (((s + m * P) + 1) + twopow k) <;>
    cases (wittRespBool (s + 1) k && Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0) <;>
    cases (((wittRespBool ((s + m * P) + 1) k ^^ wittRespBool (s + 1) k) &&
      Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0) ^^
      (wittRespBool (s + 1) k &&
      (Rule30UOR.Scale.maskparity (((s + m * P) + 1) + twopow k) 0 ^^
      Rule30UOR.Scale.maskparity ((s + 1) + twopow k) 0))) <;> decide

end Rule30UOR.Interfaces
