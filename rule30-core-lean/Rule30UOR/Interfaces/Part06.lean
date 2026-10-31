module

public import Rule30UOR.Interfaces.Part05

/-!
# `Rule30UOR.Interfaces`, part 6

* Unrestricted `2^k`-Scale `rhCenter` Laws (`p ≤ t`), Black-Cell Masking, `Z_down` Splitting, and Right-Threshold Geometry in `rhCenter`
* Batch 6: Finite-Horizon Left-Light-Cone Refutation Engine (`LhBandAgree`, `LhColAgree`), Finite-Sector Refutation of `RhBandAgree`, and Linear Defect Derivative at Column `-2`
* Batch 9: Complete `2^k`-Scale 5-Term Left-Half Calculus, Outer `$2^k$`-Strip 3-Term Collapse, and Left-Half Frobenius Defect Vanishing
* Batch 10: Single-Sector Window Evolution in the Outer `$2^k$`-Strip and Outer Cross-Center `$2^k$`-Scale Duality
* Batch 11: In-Cone Cross-Center Triality, Inter-Cone Zero-Gap Direct Readout of Late `lhCenter`, and Unconditional Left-Half Window Defect Step
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

/-! ### Unrestricted `2^k`-Scale `rhCenter` Laws (`p ≤ t`), Black-Cell Masking, `Z_down` Splitting, and Right-Threshold Geometry in `rhCenter` -/

/-- **Unrestricted `2^k`-Scale Forward Step of `rhCenter` (`rhCenter_scale_step_le`)**:
    because `rhCenter t q = false` outside the light cone (`q > t`), the `2^k`-scale step identity holds for ALL `p ≤ t` right up to the right edge `p = t` (weakening `p + 2^(k+1) ≤ t` to `p ≤ t`)! -/
theorem rhCenter_scale_step_le (t k p : Nat) (hp : p ≤ t) :
    rhCenter (t + twopow k) (p + twopow k) =
      bxor
        (bxor (bxor (rhCenter t p) (rhCenter t (p + twopow k)))
          (rhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t - p)) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [rhCenter_eq_row_testBit (t + twopow k) (p + twopow k) (by omega),
    show (t + twopow k) - (p + twopow k) = t - p by omega]
  have hsc := congrArg (fun n => n.testBit (t - p)) (row_scale t k)
  rw [Nat.testBit_xor] at hsc
  have hphi : (phiScale k (row t)).testBit (t - p) =
      ((rhCenter t p ^^ rhCenter t (p + twopow k)) ^^
        rhCenter t (p + twopow (k + 1))) := by
    change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit (t - p) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have h0 : (row t).testBit (t - p) = rhCenter t p :=
      (rhCenter_eq_row_testBit t p hp).symm
    have h1 : (decide (t - p ≥ twopow k) && (row t).testBit ((t - p) - twopow k)) =
        rhCenter t (p + twopow k) := by
      by_cases hle1 : p + twopow k ≤ t
      · have d1 : decide (t - p ≥ twopow k) = true := decide_eq_true (by omega)
        rw [d1, Bool.true_and, show (t - p) - twopow k = t - (p + twopow k) by omega,
          ← rhCenter_eq_row_testBit t (p + twopow k) hle1]
      · have d1 : decide (t - p ≥ twopow k) = false := decide_eq_false (by omega)
        rw [d1, Bool.false_and, rhCenter_gt_eq_false t (p + twopow k) (by omega)]
    have h2 : (decide (t - p ≥ twopow k + twopow k) &&
        (row t).testBit ((t - p) - (twopow k + twopow k))) =
        rhCenter t (p + twopow (k + 1)) := by
      by_cases hle2 : p + twopow (k + 1) ≤ t
      · have d2 : decide (t - p ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
        rw [d2, Bool.true_and,
          show (t - p) - (twopow k + twopow k) = t - (p + twopow (k + 1)) by omega,
          ← rhCenter_eq_row_testBit t (p + twopow (k + 1)) hle2]
      · have d2 : decide (t - p ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
        rw [d2, Bool.false_and, rhCenter_gt_eq_false t (p + twopow (k + 1)) (by omega)]
    rw [h0, h1, h2]
  rw [hsc, hphi]
  simp only [bxor_eq_xor]

/-- **Unrestricted `2^k`-Scale Inward Step of `rhCenter` (`rhCenter_scale_inward_step_le`)**:
    for ALL `p ≤ t` (right up to the right edge `p = t`), `rhCenter t p` is determined by `rhCenter (t + 2^k) (p + 2^k)`, `rhCenter t (p + 2^k)`, `rhCenter t (p + 2^(k+1))`, and `(winWitt t (2^k)).testBit (t - p)`. -/
theorem rhCenter_scale_inward_step_le (t k p : Nat) (hp : p ≤ t) :
    rhCenter t p =
      bxor
        (bxor (bxor (rhCenter (t + twopow k) (p + twopow k)) (rhCenter t (p + twopow k)))
          (rhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t - p)) := by
  rw [rhCenter_scale_step_le t k p hp]
  simp only [bxor_eq_xor]
  cases rhCenter t p <;>
    cases rhCenter t (p + twopow k) <;>
    cases rhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t - p) <;> rfl

/-- **Unrestricted `2^k`-Scale Forward Band Transport of `RhBandAgree` (`rhBandAgree_scale_step_le`)**:
    weakens `p0 + L + 2^(k+1) ≤ t` in `rhBandAgree_scale_step` to `p0 + L ≤ t` (allowing `[p0, p0 + L]` to reach all the way to the right edge `t`)! -/
theorem rhBandAgree_scale_step_le (t k Q p0 L : Nat)
    (hp : p0 + L ≤ t)
    (h0 : RhBandAgree t Q p0 L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t - (p0 + L)) L) :
    RhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  intro i hi
  have hsQ := rhCenter_scale_step_le (t + Q) k (p0 + i) (by omega)
  have hs0 := rhCenter_scale_step_le t k (p0 + i) (by omega)
  have hb0 := h0 i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw (L - i) (by omega)
  rw [show (t - (p0 + L)) + (L - i) + Q = (t + Q) - (p0 + i) by omega,
    show (t - (p0 + L)) + (L - i) = t - (p0 + i) by omega] at hwi
  rw [show ((t + twopow k) + Q) = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega,
    hsQ, hs0,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    hb0, hb1, hb2, hwi]

/-- **Unrestricted `2^k`-Scale Inward Band Transport of `RhBandAgree` (`rhBandAgree_scale_inward_step_le`)**:
    weakens `p0 + L + 2^(k+1) ≤ t` in `rhBandAgree_scale_inward_step` to `p0 + L ≤ t` (allowing `[p0, p0 + L]` to reach all the way to the right edge `t`)! -/
theorem rhBandAgree_scale_inward_step_le (t k Q p0 L : Nat)
    (hp : p0 + L ≤ t)
    (hlate : RhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t - (p0 + L)) L) :
    RhBandAgree t Q p0 L := by
  intro i hi
  have hsQ := rhCenter_scale_inward_step_le (t + Q) k (p0 + i) (by omega)
  have hs0 := rhCenter_scale_inward_step_le t k (p0 + i) (by omega)
  have hbl := hlate i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw (L - i) (by omega)
  rw [show (t - (p0 + L)) + (L - i) + Q = (t + Q) - (p0 + i) by omega,
    show (t - (p0 + L)) + (L - i) = t - (p0 + i) by omega] at hwi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [hsQ, hs0, hbl,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    hb1, hb2, hwi]

/-- **Unrestricted `WinWittAgree` from `RhBandAgree` on Three `2^k`-Bands and Late Band (`winWittAgree_of_rhBandAgree_scale_le`)**:
    weakens `p0 + L + 2^(k+1) ≤ t` in `winWittAgree_of_rhBandAgree_scale` to `p0 + L ≤ t`! -/
theorem winWittAgree_of_rhBandAgree_scale_le (t k Q p0 L : Nat)
    (hp : p0 + L ≤ t)
    (h0 : RhBandAgree t Q p0 L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hlate : RhBandAgree (t + twopow k) Q (p0 + twopow k) L) :
    WinWittAgree t k Q (t - (p0 + L)) L := by
  intro j hj
  have i := L - j
  have hi : L - j ≤ L := by omega
  have hsQ := rhCenter_scale_step_le (t + Q) k (p0 + (L - j)) (by omega)
  have hs0 := rhCenter_scale_step_le t k (p0 + (L - j)) (by omega)
  have hb0 := h0 (L - j) hi
  have hb1 := h1 (L - j) hi
  have hb2 := h2 (L - j) hi
  have hbl := hlate (L - j) hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hbl
  rw [show (p0 + (L - j)) + twopow k = (p0 + twopow k) + (L - j) by omega,
    show (p0 + (L - j)) + twopow (k + 1) = (p0 + twopow (k + 1)) + (L - j) by omega] at hsQ hs0
  rw [show (t - (p0 + L)) + j + Q = (t + Q) - (p0 + (L - j)) by omega,
    show (t - (p0 + L)) + j = t - (p0 + (L - j)) by omega]
  rw [hbl, hb0, hb1, hb2] at hsQ
  revert hsQ hs0
  simp only [bxor_eq_xor]
  cases rhCenter (t + twopow k) ((p0 + twopow k) + (L - j)) <;>
    cases rhCenter t (p0 + (L - j)) <;>
    cases rhCenter t ((p0 + twopow k) + (L - j)) <;>
    cases rhCenter t ((p0 + twopow (k + 1)) + (L - j)) <;>
    cases (winWitt (t + Q) (twopow k)).testBit ((t + Q) - (p0 + (L - j))) <;>
    cases (winWitt t (twopow k)).testBit (t - (p0 + (L - j))) <;> decide

/-- **Multi-Step `2^k`-Scale Inward Iteration of `RhBandAgree` (`rhBandAgree_scale_inward_steps`)**:
    for `p0 + M * 2^k + L ≤ t`, if `RhBandAgree` holds on the two outer bands `p0 + M * 2^k` and `p0 + (M + 1) * 2^k` at time `t`, and for every `m < M`, `RhBandAgree (t + 2^k) Q (p0 + (m + 1) * 2^k) L` and `WinWittAgree t k Q (t - (p0 + m * 2^k + L)) L` hold, then `RhBandAgree t Q p0 L` holds (marching `M * 2^k` columns inward across `M` scale steps)! -/
theorem rhBandAgree_scale_inward_steps (t k Q p0 L M : Nat)
    (hp : p0 + M * twopow k + L ≤ t)
    (hM : RhBandAgree t Q (p0 + M * twopow k) L)
    (hM1 : RhBandAgree t Q (p0 + (M + 1) * twopow k) L)
    (hlate : ∀ m, m < M → RhBandAgree (t + twopow k) Q (p0 + (m + 1) * twopow k) L)
    (hw : ∀ m, m < M → WinWittAgree t k Q (t - (p0 + m * twopow k + L)) L) :
    RhBandAgree t Q p0 L := by
  have hpair : RhBandAgree t Q p0 L ∧ RhBandAgree t Q (p0 + twopow k) L := by
    induction M generalizing p0 with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul] at hM hM1
      exact ⟨hM, hM1⟩
    | succ M ih =>
      have hp' : (p0 + twopow k) + M * twopow k + L ≤ t := by
        rw [Nat.add_mul, Nat.one_mul] at hp; omega
      have hM' : RhBandAgree t Q ((p0 + twopow k) + M * twopow k) L := by
        rwa [show (p0 + twopow k) + M * twopow k = p0 + (M + 1) * twopow k by
          rw [Nat.add_mul, Nat.one_mul]; omega]
      have hM1' : RhBandAgree t Q ((p0 + twopow k) + (M + 1) * twopow k) L := by
        rwa [show (p0 + twopow k) + (M + 1) * twopow k = p0 + (M + 1 + 1) * twopow k by
          rw [Nat.add_mul (M + 1) 1 (twopow k), Nat.one_mul]; omega]
      have hlate' : ∀ m, m < M →
          RhBandAgree (t + twopow k) Q ((p0 + twopow k) + (m + 1) * twopow k) L := by
        intro m hm
        have := hlate (m + 1) (by omega)
        rwa [show p0 + (m + 1 + 1) * twopow k = (p0 + twopow k) + (m + 1) * twopow k by
          rw [Nat.add_mul (m + 1) 1 (twopow k), Nat.one_mul]; omega] at this
      have hw' : ∀ m, m < M →
          WinWittAgree t k Q (t - ((p0 + twopow k) + m * twopow k + L)) L := by
        intro m hm
        have := hw (m + 1) (by omega)
        rwa [show p0 + (m + 1) * twopow k + L = (p0 + twopow k) + m * twopow k + L by
          rw [Nat.add_mul, Nat.one_mul]; omega] at this
      obtain ⟨hb1, hb2⟩ := ih (p0 + twopow k) hp' hM' hM1' hlate' hw'
      have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
      have hb2_eq : RhBandAgree t Q (p0 + twopow (k + 1)) L := by
        rwa [show p0 + twopow (k + 1) = (p0 + twopow k) + twopow k by omega]
      have hl0 : RhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
        have := hlate 0 (by omega)
        simpa using this
      have hw0 : WinWittAgree t k Q (t - (p0 + L)) L := by
        have := hw 0 (by omega)
        simpa using this
      have hb0 := rhBandAgree_scale_inward_step_le t k Q p0 L (by omega) hl0 hb1 hb2_eq hw0
      exact ⟨hb0, hb1⟩
  exact hpair.1

/-- **Black-Left Masking in `rhCenter` Inward Step (`rhCenter_inward_of_black_left`)**:
    whenever `rhCenter t (p + 1) = true`, the OR `rhCenter t (p + 1) || rhCenter t (p + 2)` is `true` regardless of column `p + 2`, so `rhCenter t p = !rhCenter (t + 1) (p + 1)`! -/
theorem rhCenter_inward_of_black_left (t p : Nat)
    (hb : rhCenter t (p + 1) = true) :
    rhCenter t p = !rhCenter (t + 1) (p + 1) := by
  rw [rhCenter_inward_step t p, hb, Bool.true_or, bxor_eq_xor]
  cases rhCenter (t + 1) (p + 1) <;> rfl

/-- **Black-Right Masking in `rhCenter` Inward Step (`rhCenter_inward_of_black_right`)**:
    whenever `rhCenter t (p + 2) = true`, the OR `rhCenter t (p + 1) || rhCenter t (p + 2)` is `true` regardless of column `p + 1` at time `t`, so `rhCenter t p = !rhCenter (t + 1) (p + 1)`! -/
theorem rhCenter_inward_of_black_right (t p : Nat)
    (hb : rhCenter t (p + 2) = true) :
    rhCenter t p = !rhCenter (t + 1) (p + 1) := by
  rw [rhCenter_inward_step t p, hb, Bool.or_true, bxor_eq_xor]
  cases rhCenter (t + 1) (p + 1) <;> rfl

/-- **Inward `Q`-Agreement Across a Black Column (`rhCenter_agree_of_black_left`)**:
    whenever `rhCenter (t + Q) (p + 1) = true` and `rhCenter t (p + 1) = true`, agreement of column `p + 1` at `t + 1` (`rhCenter ((t + 1) + Q) (p + 1) = rhCenter (t + 1) (p + 1)`) immediately implies `rhCenter (t + Q) p = rhCenter t p` without needing column `p + 2`! -/
theorem rhCenter_agree_of_black_left (t Q p : Nat)
    (hbQ : rhCenter (t + Q) (p + 1) = true)
    (hb0 : rhCenter t (p + 1) = true)
    (hnext : rhCenter ((t + 1) + Q) (p + 1) = rhCenter (t + 1) (p + 1)) :
    rhCenter (t + Q) p = rhCenter t p := by
  rw [rhCenter_inward_of_black_left (t + Q) p hbQ,
    rhCenter_inward_of_black_left t p hb0,
    show (t + Q) + 1 = (t + 1) + Q by omega,
    hnext]

/-- **White-Pair Splitting from Constant Diagonal Step (`rhCenter_white_pair_of_diag_eq`, `Z_down` in `rhCenter`)**:
    whenever `rhCenter (t + 1) (p + 1) = rhCenter t p`, the OR input `rhCenter t (p + 1) || rhCenter t (p + 2)` must be `false`, forcing BOTH `rhCenter t (p + 1) = false` and `rhCenter t (p + 2) = false` simultaneously! -/
theorem rhCenter_white_pair_of_diag_eq (t p : Nat)
    (heq : rhCenter (t + 1) (p + 1) = rhCenter t p) :
    rhCenter t (p + 1) = false ∧ rhCenter t (p + 2) = false := by
  have hs := rhCenter_step_succ t p
  rw [heq] at hs
  revert hs
  simp only [bxor_eq_xor]
  cases rhCenter t p <;>
    cases rhCenter t (p + 1) <;>
    cases rhCenter t (p + 2) <;> decide

/-- **Constant Diagonal Step from White Pair (`rhCenter_diag_eq_of_white_pair`)**:
    whenever `rhCenter t (p + 1) = false` and `rhCenter t (p + 2) = false`, `rhCenter (t + 1) (p + 1) = rhCenter t p`. -/
theorem rhCenter_diag_eq_of_white_pair (t p : Nat)
    (hw1 : rhCenter t (p + 1) = false)
    (hw2 : rhCenter t (p + 2) = false) :
    rhCenter (t + 1) (p + 1) = rhCenter t p := by
  rw [rhCenter_step_succ t p, hw1, hw2, Bool.false_or, bxor_eq_xor, Bool.xor_false]

/-- **Right-Threshold Diagonal Shift Law in `rhCenter` (`rhCenter_diag_shift_twopow_eq_of_threshold`)**:
    for `IsRightThreshold k J` and `s ≤ J` (up to the full 2-adic threshold `J` of scale `k`), shifting both time and column by any multiple `u * 2^k` preserves `rhCenter`:
    `rhCenter ((p + s) + u * 2^k) (p + u * 2^k) = rhCenter (p + s) p`. -/
theorem rhCenter_diag_shift_twopow_eq_of_threshold (k J p s u : Nat)
    (hJ : IsRightThreshold k J) (hs : s ≤ J) :
    rhCenter ((p + s) + u * twopow k) (p + u * twopow k) = rhCenter (p + s) p := by
  rw [rhCenter_eq_rdiag ((p + s) + u * twopow k) (p + u * twopow k) (by omega),
    rhCenter_eq_rdiag (p + s) p (by omega),
    show ((p + s) + u * twopow k) - (p + u * twopow k) = s by omega,
    show (p + s) - p = s by omega]
  exact rdiag_restart_of_threshold k J s u (p + s) hJ hs

/-- **Right-Threshold Sector-Column Center Law in `rhCenter` (`rhCenter_sector_diag_eq_center_of_threshold`)**:
    for `IsRightThreshold k J` and `s ≤ J`, column `u * 2^k` of `rhCenter` at time `s + u * 2^k` equals `center s`! -/
theorem rhCenter_sector_diag_eq_center_of_threshold (k J s u : Nat)
    (hJ : IsRightThreshold k J) (hs : s ≤ J) :
    rhCenter (s + u * twopow k) (u * twopow k) = Rule30UOR.Core.center s := by
  have h := rhCenter_diag_shift_twopow_eq_of_threshold k J 0 s u hJ hs
  simpa [rhCenter_zero_eq_center] using h

/-- **Right-Edge White Zero-Gap of Width `J` at Multiples of `2^k` in `rhCenter` (`rhCenter_zero_gap_of_threshold`)**:
    for `IsRightThreshold k J`, `1 ≤ j ≤ J`, and `j ≤ u * 2^k`, `rhCenter (u * 2^k) (u * 2^k - j) = false` (a white gap of width `J` immediately inside the right edge at every multiple `u * 2^k`)! -/
theorem rhCenter_zero_gap_of_threshold (k J u j : Nat)
    (hJ : IsRightThreshold k J) (hj1 : 1 ≤ j) (hjJ : j ≤ J) (hju : j ≤ u * twopow k) :
    rhCenter (u * twopow k) (u * twopow k - j) = false := by
  rw [rhCenter_eq_rdiag (u * twopow k) (u * twopow k - j) (by omega),
    show u * twopow k - (u * twopow k - j) = j by omega,
    show u * twopow k = 0 + u * twopow k by omega,
    rdiag_restart_of_threshold k J j u 0 hJ hjJ]
  exact rdiag_gt_two_mul 0 j (by omega)

/-- **Right-Edge Black Run of Width `J + 1` at `t = (u + 1) * 2^k - 1` in `rhCenter` (`rhCenter_last_one_of_threshold`)**:
    for `IsRightThreshold k J`, `j ≤ J`, and `j ≤ (u + 1) * 2^k - 1`, `rhCenter ((u + 1) * 2^k - 1) (((u + 1) * 2^k - 1) - j) = true` (every cell within distance `J` of the right edge is black one step before each multiple of `2^k`)! -/
theorem rhCenter_last_one_of_threshold (k J u j : Nat)
    (hJ : IsRightThreshold k J) (hjJ : j ≤ J) (hju : j ≤ (u + 1) * twopow k - 1) :
    rhCenter ((u + 1) * twopow k - 1) (((u + 1) * twopow k - 1) - j) = true := by
  have hp : 0 < twopow k := by
    rw [twopow_eq_pow k]
    exact Nat.two_pow_pos k
  rw [rhCenter_eq_rdiag ((u + 1) * twopow k - 1) (((u + 1) * twopow k - 1) - j) (by omega),
    show ((u + 1) * twopow k - 1) - (((u + 1) * twopow k - 1) - j) = j by omega,
    show (u + 1) * twopow k - 1 = (twopow k - 1) + u * twopow k by
      rw [Nat.add_mul, Nat.one_mul]; omega,
    rdiag_restart_of_threshold k J j u (twopow k - 1) hJ hjJ,
    Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
  exact Rule30UOR.KitConstructive.last_one j k
    (Rule30UOR.KitConstructive.per_mono_le hjJ hJ.1)

/-- **Right-Half Windowed Witt Column Agreement (`RhWinWittAgree`)**:
    the `2^k`-windowed Witt vector `winWitt · (2^k)` at rows `t + Q` and `t` has identical testBits at `t + Q - (p0 + i)` and `t - (p0 + i)` for all `0 ≤ i ≤ L`! -/
def RhWinWittAgree (t k Q p0 L : Nat) : Prop :=
  ∀ i : Nat, i ≤ L →
    (winWitt (t + Q) (twopow k)).testBit ((t + Q) - (p0 + i)) =
      (winWitt t (twopow k)).testBit (t - (p0 + i))

/-- **Bit `0` of `winWitt` is Always `false` (`winWitt_testBit_zero`)**:
    for all `t, n : Nat`, `(winWitt t n).testBit 0 = false` because every carry contribution in `winWitt_step` is shifted left by 1! -/
theorem winWitt_testBit_zero (t n : Nat) :
    (winWitt t n).testBit 0 = false := by
  induction n with
  | zero =>
    change (0 : Nat).testBit 0 = false
    decide
  | succ m ih =>
    have d1 : decide (0 ≥ 1) = false := rfl
    have d2 : decide (0 ≥ 2) = false := rfl
    change (((winWitt t m) ^^^ ((winWitt t m) <<< 1)) ^^^
      ((winWitt t m) <<< 2) ^^^ (carry (row (t + m)) <<< 1)).testBit 0 = false
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, ih, d1, d2, Bool.false_and, Bool.xor_false]

/-- **Unconditional `2^k`-Scale Step of `rhCenter` (`rhCenter_scale_step_uncond`)**:
    for all `t, k, p` (with no bound `p ≤ t` required!), `rhCenter (t + 2^k) (p + 2^k) = bxor (bxor (bxor (rhCenter t p) (rhCenter t (p + 2^k))) (rhCenter t (p + 2^(k+1)))) ((winWitt t (2^k)).testBit (t - p))`! -/
theorem rhCenter_scale_step_uncond (t k p : Nat) :
    rhCenter (t + twopow k) (p + twopow k) =
      bxor
        (bxor (bxor (rhCenter t p) (rhCenter t (p + twopow k)))
          (rhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t - p)) := by
  by_cases hpt : p ≤ t
  · exact rhCenter_scale_step_le t k p hpt
  · have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
    have hsub : t - p = 0 := by omega
    rw [rhCenter_gt_eq_false (t + twopow k) (p + twopow k) (by omega),
      rhCenter_gt_eq_false t p (by omega),
      rhCenter_gt_eq_false t (p + twopow k) (by omega),
      rhCenter_gt_eq_false t (p + twopow (k + 1)) (by omega),
      hsub, winWitt_testBit_zero t (twopow k)]
    rfl

/-- **Unconditional `2^k`-Scale Inward Step of `rhCenter` (`rhCenter_scale_inward_step_uncond`)**:
    for all `t, k, p` (with no bound `p ≤ t` required!), `rhCenter t p = bxor (bxor (bxor (rhCenter (t + 2^k) (p + 2^k)) (rhCenter t (p + 2^k))) (rhCenter t (p + 2^(k+1)))) ((winWitt t (2^k)).testBit (t - p))`! -/
theorem rhCenter_scale_inward_step_uncond (t k p : Nat) :
    rhCenter t p =
      bxor
        (bxor (bxor (rhCenter (t + twopow k) (p + twopow k)) (rhCenter t (p + twopow k)))
          (rhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t - p)) := by
  rw [rhCenter_scale_step_uncond t k p]
  simp only [bxor_eq_xor]
  cases rhCenter t p <;>
    cases rhCenter t (p + twopow k) <;>
    cases rhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t - p) <;> rfl

/-- **`RhWinWittAgree` from `WinWittAgree` Inside the Light Cone (`rhWinWittAgree_of_winWittAgree`)**:
    for `p0 + L ≤ t`, `WinWittAgree t k Q (t - (p0 + L)) L` implies `RhWinWittAgree t k Q p0 L`! -/
theorem rhWinWittAgree_of_winWittAgree (t k Q p0 L : Nat) (hpt : p0 + L ≤ t)
    (hw : WinWittAgree t k Q (t - (p0 + L)) L) :
    RhWinWittAgree t k Q p0 L := by
  intro i hi
  have hwi := hw (L - i) (by omega)
  rwa [show (t - (p0 + L)) + (L - i) + Q = (t + Q) - (p0 + i) by omega,
    show (t - (p0 + L)) + (L - i) = t - (p0 + i) by omega] at hwi

/-- **`RhWinWittAgree` Outside the Light Cone (`rhWinWittAgree_outside_cone`)**:
    if `t + Q ≤ p0`, then `RhWinWittAgree t k Q p0 L` holds unconditionally (since both `(t + Q) - (p0 + i) = 0` and `t - (p0 + i) = 0`, where bit `0` of `winWitt` is always `false`)! -/
theorem rhWinWittAgree_outside_cone (t k Q p0 L : Nat) (hout : t + Q ≤ p0) :
    RhWinWittAgree t k Q p0 L := by
  intro i _hi
  rw [show (t + Q) - (p0 + i) = 0 by omega,
    show t - (p0 + i) = 0 by omega,
    winWitt_testBit_zero (t + Q) (twopow k),
    winWitt_testBit_zero t (twopow k)]

/-- **Unconditional `2^k`-Scale Inward Step of `RhBandAgree` (`rhBandAgree_scale_inward_step_uncond`)**:
    for all `t, k, Q, p0, L`, `RhBandAgree (t + 2^k) Q (p0 + 2^k) L`, `RhBandAgree t Q (p0 + 2^k) L`, `RhBandAgree t Q (p0 + 2^(k+1)) L`, and `RhWinWittAgree t k Q p0 L` imply `RhBandAgree t Q p0 L`! -/
theorem rhBandAgree_scale_inward_step_uncond (t k Q p0 L : Nat)
    (hlate : RhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : RhWinWittAgree t k Q p0 L) :
    RhBandAgree t Q p0 L := by
  intro i hi
  have hsQ := rhCenter_scale_inward_step_uncond (t + Q) k (p0 + i)
  have hs0 := rhCenter_scale_inward_step_uncond t k (p0 + i)
  have hbl := hlate i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [hsQ, hs0, hbl,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    hb1, hb2, hwi]

/-- **Multi-Step Unconditional `2^k`-Scale Inward Propagation of `RhBandAgree` (`rhBandAgree_scale_inward_steps_uncond`)**:
    propagates `RhBandAgree` inward across `M` blocks of width `2^k` down to `RhBandAgree t Q p0 L` with no light-cone bound required! -/
theorem rhBandAgree_scale_inward_steps_uncond (t k Q p0 L M : Nat)
    (hM : RhBandAgree t Q (p0 + M * twopow k) L)
    (hM1 : RhBandAgree t Q (p0 + (M + 1) * twopow k) L)
    (hlate : ∀ m : Nat, m < M → RhBandAgree (t + twopow k) Q (p0 + (m + 1) * twopow k) L)
    (hw : ∀ m : Nat, m < M → RhWinWittAgree t k Q (p0 + m * twopow k) L) :
    RhBandAgree t Q p0 L := by
  have hpair : RhBandAgree t Q p0 L ∧ RhBandAgree t Q (p0 + twopow k) L := by
    induction M generalizing p0 with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul] at hM hM1
      exact ⟨hM, hM1⟩
    | succ M ih =>
      have hM' : RhBandAgree t Q ((p0 + twopow k) + M * twopow k) L := by
        rwa [show (p0 + twopow k) + M * twopow k = p0 + (M + 1) * twopow k by
          rw [Nat.add_mul, Nat.one_mul]; omega]
      have hM1' : RhBandAgree t Q ((p0 + twopow k) + (M + 1) * twopow k) L := by
        rwa [show (p0 + twopow k) + (M + 1) * twopow k = p0 + (M + 1 + 1) * twopow k by
          rw [Nat.add_mul (M + 1) 1 (twopow k), Nat.one_mul]; omega]
      have hlate' : ∀ m, m < M →
          RhBandAgree (t + twopow k) Q ((p0 + twopow k) + (m + 1) * twopow k) L := by
        intro m hm
        have := hlate (m + 1) (by omega)
        rwa [show p0 + (m + 1 + 1) * twopow k = (p0 + twopow k) + (m + 1) * twopow k by
          rw [Nat.add_mul (m + 1) 1 (twopow k), Nat.one_mul]; omega] at this
      have hw' : ∀ m, m < M →
          RhWinWittAgree t k Q ((p0 + twopow k) + m * twopow k) L := by
        intro m hm
        have := hw (m + 1) (by omega)
        rwa [show p0 + (m + 1) * twopow k = (p0 + twopow k) + m * twopow k by
          rw [Nat.add_mul, Nat.one_mul]; omega] at this
      obtain ⟨hb1, hb2⟩ := ih (p0 + twopow k) hM' hM1' hlate' hw'
      have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
      have hb2_eq : RhBandAgree t Q (p0 + twopow (k + 1)) L := by
        rwa [show p0 + twopow (k + 1) = (p0 + twopow k) + twopow k by omega]
      have hl0 : RhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
        have := hlate 0 (by omega)
        simpa using this
      have hw0 : RhWinWittAgree t k Q p0 L := by
        have := hw 0 (by omega)
        simpa using this
      have hb0 := rhBandAgree_scale_inward_step_uncond t k Q p0 L hl0 hb1 hb2_eq hw0
      exact ⟨hb0, hb1⟩
  exact hpair.1

/-- **Inward `2^k`-Scale Cone Reduction of `RhBandAgree` (`rhBandAgree_of_scale_inward_cone`)**:
    if `t + Q < p0 + M * 2^k` (so `p0 + M * 2^k` and `p0 + (M + 1) * 2^k` lie strictly outside the light cone of `t + Q`), then `RhBandAgree t Q p0 L` follows purely from `RhBandAgree (t + 2^k) Q (p0 + (m + 1) * 2^k) L` and `RhWinWittAgree t k Q (p0 + m * 2^k) L` for `m < M` (with both outer boundary conditions at time `t` discharged automatically by `rhBandAgree_outside_cone`)! -/
theorem rhBandAgree_of_scale_inward_cone (t k Q p0 L M : Nat)
    (hcone : t + Q < p0 + M * twopow k)
    (hlate : ∀ m : Nat, m < M → RhBandAgree (t + twopow k) Q (p0 + (m + 1) * twopow k) L)
    (hw : ∀ m : Nat, m < M → RhWinWittAgree t k Q (p0 + m * twopow k) L) :
    RhBandAgree t Q p0 L := by
  have hM1_cone : t + Q < p0 + (M + 1) * twopow k := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  exact rhBandAgree_scale_inward_steps_uncond t k Q p0 L M
    (rhBandAgree_outside_cone t Q (p0 + M * twopow k) L hcone)
    (rhBandAgree_outside_cone t Q (p0 + (M + 1) * twopow k) L hM1_cone)
    hlate
    hw

/-- **Diagonal Difference of `rhCenter` Equals OR of Right Pair (`rhCenter_diag_diff_eq_or`)**:
    for all `t, p`, `bxor (rhCenter (t + 1) (p + 1)) (rhCenter t p) = (rhCenter t (p + 1) || rhCenter t (p + 2))`! -/
theorem rhCenter_diag_diff_eq_or (t p : Nat) :
    bxor (rhCenter (t + 1) (p + 1)) (rhCenter t p) =
      (rhCenter t (p + 1) || rhCenter t (p + 2)) := by
  rw [rhCenter_step_succ t p]
  cases rhCenter t p <;> cases rhCenter t (p + 1) <;> cases rhCenter t (p + 2) <;> rfl

/-- **Right-Half `Q`-Defect Diagonal Conservation Law (`rhCenter_defect_diag_step`)**:
    for all `t, Q, p`, `bxor (bxor (rhCenter (t + 1 + Q) (p + 1)) (rhCenter (t + 1) (p + 1))) (bxor (rhCenter (t + Q) p) (rhCenter t p)) = bxor (rhCenter (t + Q) (p + 1) || rhCenter (t + Q) (p + 2)) (rhCenter t (p + 1) || rhCenter t (p + 2))`! -/
theorem rhCenter_defect_diag_step (t Q p : Nat) :
    bxor (bxor (rhCenter (t + 1 + Q) (p + 1)) (rhCenter (t + 1) (p + 1)))
      (bxor (rhCenter (t + Q) p) (rhCenter t p)) =
      bxor (rhCenter (t + Q) (p + 1) || rhCenter (t + Q) (p + 2))
        (rhCenter t (p + 1) || rhCenter t (p + 2)) := by
  rw [show t + 1 + Q = (t + Q) + 1 by omega,
    rhCenter_step_succ (t + Q) p, rhCenter_step_succ t p]
  cases rhCenter (t + Q) p <;>
    cases rhCenter (t + Q) (p + 1) <;>
    cases rhCenter (t + Q) (p + 2) <;>
    cases rhCenter t p <;>
    cases rhCenter t (p + 1) <;>
    cases rhCenter t (p + 2) <;>
    rfl

/-- **Generalized Masked-Jen Gate for `rhCenter` Defect Under Column `p + 1` Agreement (`rhCenter_defect_diag_step_of_col_eq`)**:
    if `rhCenter (t + Q) (p + 1) = rhCenter t (p + 1)`, then the diagonal step of the `Q`-defect equals the masked defect at column `p + 2`:
    `bxor (bxor (rhCenter (t + 1 + Q) (p + 1)) (rhCenter (t + 1) (p + 1))) (bxor (rhCenter (t + Q) p) (rhCenter t p)) = ((!rhCenter t (p + 1)) && bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2)))`! -/
theorem rhCenter_defect_diag_step_of_col_eq (t Q p : Nat)
    (hp1 : rhCenter (t + Q) (p + 1) = rhCenter t (p + 1)) :
    bxor (bxor (rhCenter (t + 1 + Q) (p + 1)) (rhCenter (t + 1) (p + 1)))
      (bxor (rhCenter (t + Q) p) (rhCenter t p)) =
      ((!rhCenter t (p + 1)) && bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2))) := by
  rw [rhCenter_defect_diag_step t Q p, hp1]
  cases rhCenter t (p + 1) <;>
    cases rhCenter (t + Q) (p + 2) <;>
    cases rhCenter t (p + 2) <;>
    rfl

/-- **Inward `Q`-Defect Gate Under Two-Time Agreement at Column `p + 1` (`rhCenter_defect_inward_of_col_eq_two`)**:
    if column `p + 1` agrees at `t` and `t + 1`, then the `Q`-defect at `(t, p)` equals the masked `Q`-defect at `(t, p + 2)`:
    `bxor (rhCenter (t + Q) p) (rhCenter t p) = ((!rhCenter t (p + 1)) && bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2)))`! -/
theorem rhCenter_defect_inward_of_col_eq_two (t Q p : Nat)
    (hp1 : rhCenter (t + Q) (p + 1) = rhCenter t (p + 1))
    (hp1_succ : rhCenter (t + 1 + Q) (p + 1) = rhCenter (t + 1) (p + 1)) :
    bxor (rhCenter (t + Q) p) (rhCenter t p) =
      ((!rhCenter t (p + 1)) && bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2))) := by
  have h := rhCenter_defect_diag_step_of_col_eq t Q p hp1
  rw [hp1_succ] at h
  revert h
  cases rhCenter (t + 1) (p + 1) <;>
    cases rhCenter (t + Q) p <;>
    cases rhCenter t p <;>
    cases rhCenter t (p + 1) <;>
    cases rhCenter (t + Q) (p + 2) <;>
    cases rhCenter t (p + 2) <;>
    decide

/-- **Local Right-Permutive Step Across a White Cell in `rhCenter` (`rhCenter_outward_of_white_mid`)**:
    when `rhCenter t (p + 1) = false`, column `p + 2` is determined uniquely by `(t + 1, p + 1)` and `(t, p)`:
    `rhCenter t (p + 2) = bxor (rhCenter (t + 1) (p + 1)) (rhCenter t p)`! -/
theorem rhCenter_outward_of_white_mid (t p : Nat)
    (hw : rhCenter t (p + 1) = false) :
    rhCenter t (p + 2) = bxor (rhCenter (t + 1) (p + 1)) (rhCenter t p) := by
  rw [rhCenter_step_succ t p, hw]
  cases rhCenter t p <;> cases rhCenter t (p + 2) <;> rfl

/-- **Outward `Q`-Agreement Across a White Cell in `rhCenter` (`rhCenter_agree_outward_of_white_mid`)**:
    if `rhCenter t (p + 1) = false`, `rhCenter (t + Q) p = rhCenter t p`, `rhCenter (t + Q) (p + 1) = rhCenter t (p + 1)`, and `rhCenter (t + 1 + Q) (p + 1) = rhCenter (t + 1) (p + 1)`, then `rhCenter (t + Q) (p + 2) = rhCenter t (p + 2)`! -/
theorem rhCenter_agree_outward_of_white_mid (t Q p : Nat)
    (hw : rhCenter t (p + 1) = false)
    (hp : rhCenter (t + Q) p = rhCenter t p)
    (hp1 : rhCenter (t + Q) (p + 1) = rhCenter t (p + 1))
    (hp1_succ : rhCenter (t + 1 + Q) (p + 1) = rhCenter (t + 1) (p + 1)) :
    rhCenter (t + Q) (p + 2) = rhCenter t (p + 2) := by
  have hwQ : rhCenter (t + Q) (p + 1) = false := by rw [hp1, hw]
  rw [rhCenter_outward_of_white_mid (t + Q) p hwQ,
    rhCenter_outward_of_white_mid t p hw,
    show t + Q + 1 = t + 1 + Q by omega,
    hp1_succ, hp]

/-- **Inward-Outward `Q`-Defect Equality Across a White Cell in `rhCenter` (`rhCenter_defect_inward_of_white_mid`)**:
    when `rhCenter t (p + 1) = false`, `rhCenter (t + Q) (p + 1) = rhCenter t (p + 1)`, and `rhCenter (t + 1 + Q) (p + 1) = rhCenter (t + 1) (p + 1)`, the `Q`-defect at `(t, p)` equals the `Q`-defect at `(t, p + 2)`:
    `bxor (rhCenter (t + Q) p) (rhCenter t p) = bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2))`! -/
theorem rhCenter_defect_inward_of_white_mid (t Q p : Nat)
    (hw : rhCenter t (p + 1) = false)
    (hp1 : rhCenter (t + Q) (p + 1) = rhCenter t (p + 1))
    (hp1_succ : rhCenter (t + 1 + Q) (p + 1) = rhCenter (t + 1) (p + 1)) :
    bxor (rhCenter (t + Q) p) (rhCenter t p) =
      bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2)) := by
  rw [rhCenter_defect_inward_of_col_eq_two t Q p hp1 hp1_succ, hw]
  rfl

/-- **Inward `Q`-Agreement from Vanishing Masked Defect Under Two-Time Agreement at Column `p + 1` (`rhCenter_agree_inward_of_col_eq_two`)**:
    if column `p + 1` agrees at `t` and `t + 1`, and `((!rhCenter t (p + 1)) && bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2))) = false`, then `rhCenter (t + Q) p = rhCenter t p`! -/
theorem rhCenter_agree_inward_of_col_eq_two (t Q p : Nat)
    (hp1 : rhCenter (t + Q) (p + 1) = rhCenter t (p + 1))
    (hp1_succ : rhCenter (t + 1 + Q) (p + 1) = rhCenter (t + 1) (p + 1))
    (hmask : ((!rhCenter t (p + 1)) && bxor (rhCenter (t + Q) (p + 2)) (rhCenter t (p + 2))) = false) :
    rhCenter (t + Q) p = rhCenter t p := by
  have h := rhCenter_defect_inward_of_col_eq_two t Q p hp1 hp1_succ
  rw [hmask] at h
  revert h
  cases rhCenter (t + Q) p <;> cases rhCenter t p <;> decide

/-! ### Batch 6: Finite-Horizon Left-Light-Cone Refutation Engine (`LhBandAgree`, `LhColAgree`), Finite-Sector Refutation of `RhBandAgree`, and Linear Defect Derivative at Column `-2` -/

/-- Spatial band `Q`-agreement of the driven left half `lhCenter`:
    at rows `t` and `t + Q`, columns `-(p0 + i)` (`0 ≤ i ≤ L`) of `lhCenter` agree. -/
def LhBandAgree (t Q p0 L : Nat) : Prop :=
  ∀ i : Nat, i ≤ L →
    lhCenter (t + Q) (p0 + i) = lhCenter t (p0 + i)

/-- Time-trace `Q`-agreement of column `-p0` of the driven left half `lhCenter`:
    at times `t + s` and `(t + s) + Q` (`s ≤ S`), column `-p0` of `lhCenter` agrees. -/
def LhColAgree (t Q p0 S : Nat) : Prop :=
  ∀ s : Nat, s ≤ S →
    lhCenter ((t + s) + Q) p0 = lhCenter (t + s) p0

/-- **Unconditional Left-Light-Cone Obstruction to `LhBandAgree` (`not_lhBandAgree_of_lt_add`)**:
    for any `t, Q, L` with `0 < Q` and `t + Q ≤ L`, `LhBandAgree t Q 0 L` is impossible because at `i = t + Q`, `lhCenter (t + Q) (t + Q) = true` while `lhCenter t (t + Q) = false`! -/
theorem not_lhBandAgree_of_lt_add (t Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) :
    ¬ LhBandAgree t Q 0 L := by
  intro h
  have hi := h (t + Q) hL
  rw [Nat.zero_add,
    lhCenter_self_eq_true (t + Q),
    lhCenter_gt_eq_false t (t + Q) (by omega)] at hi
  revert hi; decide

/-- **1-Column Outward Step of Left-Half Time-Trace Determination (`lhCenter_outward_determine_step`)**:
    by left-permutivity (`lhCenter_outward_step`), if `LhColAgree t Q p0 (S + 1)` and `LhColAgree t Q (p0 + 1) (S + 1)` hold, then `LhColAgree t Q (p0 + 2) S` holds! -/
theorem lhCenter_outward_determine_step (t Q p0 S : Nat)
    (h0 : LhColAgree t Q p0 (S + 1))
    (h1 : LhColAgree t Q (p0 + 1) (S + 1)) :
    LhColAgree t Q (p0 + 2) S := by
  intro s hs
  have hs0 := h0 s (by omega)
  have hs1 := h1 s (by omega)
  have hnext1 := h1 (s + 1) (by omega)
  rw [lhCenter_outward_step ((t + s) + Q) p0,
    lhCenter_outward_step (t + s) p0,
    show ((t + s) + Q) + 1 = (t + (s + 1)) + Q by omega,
    show (t + s) + 1 = t + (s + 1) by omega,
    hnext1, hs1, hs0]

/-- **Multi-Column Outward Left-Half Time-Trace Determination (`lhCenter_outward_determine`)**:
    if `LhColAgree t Q p0 (S + K)` and `LhColAgree t Q (p0 + 1) (S + K)` hold, then marching `K` columns outward toward the left edge determines `LhColAgree t Q (p0 + K) S ∧ LhColAgree t Q (p0 + K + 1) S`! -/
theorem lhCenter_outward_determine (t Q p0 S K : Nat)
    (h0 : LhColAgree t Q p0 (S + K))
    (h1 : LhColAgree t Q (p0 + 1) (S + K)) :
    LhColAgree t Q (p0 + K) S ∧ LhColAgree t Q (p0 + K + 1) S := by
  induction K generalizing p0 S with
  | zero =>
    simpa using And.intro h0 h1
  | succ K ih =>
    have h0' : LhColAgree t Q p0 ((S + 1) + K) := by
      intro s hs; exact h0 s (by omega)
    have h1' : LhColAgree t Q (p0 + 1) ((S + 1) + K) := by
      intro s hs; exact h1 s (by omega)
    obtain ⟨hcK, hcK1⟩ := ih p0 (S + 1) h0' h1'
    have hcK2 := lhCenter_outward_determine_step t Q (p0 + K) S hcK hcK1
    refine ⟨?_, ?_⟩
    · intro s hs
      have := hcK1 s (by omega)
      rwa [show p0 + (K + 1) = p0 + K + 1 by omega]
    · intro s hs
      have := hcK2 s hs
      rwa [show p0 + (K + 1) + 1 = (p0 + K) + 2 by omega]

/-- **Spatial Left-Half Band Agreement from Center Time-Trace (`lhBandAgree_of_outward_determine`)**:
    if `LhColAgree t Q p0 L` and `LhColAgree t Q (p0 + 1) L` hold on `[t, t + L]`, then `LhBandAgree t Q p0 (L + 1)` holds across the entire spatial band `[p0, p0 + L + 1]` at time `t`! -/
theorem lhBandAgree_of_outward_determine (t Q p0 L : Nat)
    (h0 : LhColAgree t Q p0 L)
    (h1 : LhColAgree t Q (p0 + 1) L) :
    LhBandAgree t Q p0 (L + 1) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have := h0 0 (by omega)
    simpa using this
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j ≤ L := by omega
    have h0_j : LhColAgree t Q p0 (0 + j) := by
      intro s hs; exact h0 s (by omega)
    have h1_j : LhColAgree t Q (p0 + 1) (0 + j) := by
      intro s hs; exact h1 s (by omega)
    have hdet := (lhCenter_outward_determine t Q p0 0 j h0_j h1_j).2 0 (by omega)
    simpa [Nat.add_assoc] using hdet

/-- **Finite-Horizon Incompatibility of `LhColAgree` at Columns `0` and `1` (`not_lhColAgree_zero_one_of_pos`)**:
    for any `t, Q, S` with `0 < Q` and `t + Q ≤ S + 1`, `LhColAgree t Q 0 S` and `LhColAgree t Q 1 S` cannot both hold! -/
theorem not_lhColAgree_zero_one_of_pos (t Q S : Nat)
    (hQ : 0 < Q) (hS : t + Q ≤ S + 1)
    (h0 : LhColAgree t Q 0 S) :
    ¬ LhColAgree t Q 1 S := by
  intro h1
  have hband := lhBandAgree_of_outward_determine t Q 0 S h0 h1
  exact not_lhBandAgree_of_lt_add t Q (S + 1) hQ hS hband

/-- **Periodic Center Supplies `LhColAgree` at Column `0` (`periodic_lhColAgree_zero`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S` with `T ≤ t`, `LhColAgree t (m * P) 0 S` holds unconditionally! -/
theorem periodic_lhColAgree_zero
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t) :
    LhColAgree t (m * P) 0 S := by
  intro s _hs
  rw [lhCenter_zero_eq_center, lhCenter_zero_eq_center]
  exact Rule30UOR.Scale.center_mul hper m (t + s) (by omega)

/-- **Finite-Horizon Death Clock for Column `-1` Under Periodic Center (`not_periodic_lhColAgree_one_horizon`)**:
    under `CenterPeriodic T P` (`0 < P`), for any `m, t, S` with `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, column `-1` (`lhCenter · 1`) cannot agree with period `m * P` across the finite horizon `[t, t + S]`! -/
theorem not_periodic_lhColAgree_one_horizon
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (hm : 0 < m) (ht : T ≤ t) (hS : t + m * P ≤ S + 1) :
    ¬ LhColAgree t (m * P) 1 S := by
  have hQ : 0 < m * P := Nat.mul_pos hm hP
  exact not_lhColAgree_zero_one_of_pos t (m * P) S hQ hS
    (periodic_lhColAgree_zero T P hP hper m t S ht)

/-- **Transfer of Time-Trace Agreement from `rhCenter · 1` to `lhCenter · 1` via the §6 `Φ` Fixed-Point Law (`periodic_lhColAgree_one_of_rhColAgree_one`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S` with `T ≤ t`, `RhColAgree t (m * P) 1 S` implies `LhColAgree t (m * P) 1 S`! -/
theorem periodic_lhColAgree_one_of_rhColAgree_one
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hrh : RhColAgree t (m * P) 1 S) :
    LhColAgree t (m * P) 1 S := by
  intro s hs
  have hr := hrh s hs
  have hc0 : Rule30UOR.Core.center ((t + s) + m * P) = Rule30UOR.Core.center (t + s) :=
    Rule30UOR.Scale.center_mul hper m (t + s) (by omega)
  have hc1 : Rule30UOR.Core.center (((t + s) + m * P) + 1) = Rule30UOR.Core.center ((t + s) + 1) := by
    rw [show ((t + s) + m * P) + 1 = ((t + s) + 1) + m * P by omega]
    exact Rule30UOR.Scale.center_mul hper m ((t + s) + 1) (by omega)
  rw [lhCenter_one_eq_of_center_fixed ((t + s) + m * P),
    lhCenter_one_eq_of_center_fixed (t + s),
    hc0, hc1, hr]

/-- **Finite-Horizon Death Clock for Right-Half Column `+1` Under Periodic Center (`not_periodic_rhColAgree_one_horizon`)**:
    under `CenterPeriodic T P` (`0 < P`), for any `m, t, S` with `0 < m`, `T ≤ t`, and `t + m * P ≤ S + 1`, column `+1` of the driven right half (`rhCenter · 1`) cannot agree with period `m * P` across the finite horizon `[t, t + S]`! -/
theorem not_periodic_rhColAgree_one_horizon
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (hm : 0 < m) (ht : T ≤ t) (hS : t + m * P ≤ S + 1) :
    ¬ RhColAgree t (m * P) 1 S := by
  intro hrh
  exact not_periodic_lhColAgree_one_horizon T P hP hper m t S hm ht hS
    (periodic_lhColAgree_one_of_rhColAgree_one T P hP hper m t S ht hrh)

/-- **Time-Trace Agreement `RhColAgree` at Column `+1` from Spatial `RhBandAgree` (`periodic_rhColAgree_one_of_rhBandAgree_zero`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S` with `T ≤ t`, `RhBandAgree t (m * P) 0 (S + 1)` at time `t` implies `RhColAgree t (m * P) 1 S` across `[t, t + S]`! -/
theorem periodic_rhColAgree_one_of_rhBandAgree_zero
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 0 (S + 1)) :
    RhColAgree t (m * P) 1 S := by
  intro s hs
  have hsub : RhBandAgree t (m * P) 0 (1 + s) := by
    intro i hi
    exact hband i (by omega)
  have hstep := periodic_rhBandAgree_zero_steps T P hP hper m t 1 s ht hsub
  exact hstep 1 (by omega)

/-- **Gluing `M` Finite Sector Bands into `RhColAgree` Across `M * 2^k` Steps (`periodic_rhColAgree_one_of_finite_sectors`)**:
    under `CenterPeriodic T P` (`0 < P`), for `1 ≤ M` and `T ≤ d + U * 2^k`, if `RhBandAgree ((d + (U + j) * 2^k) + 1) (m * P) 0 (2^k + 1)` holds for `j < M` (only `M` finite sector times!), then `RhColAgree ((d + U * 2^k) + 1) (m * P) 1 (M * 2^k)` holds! -/
theorem periodic_rhColAgree_one_of_finite_sectors
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U M m : Nat) (hM : 1 ≤ M) (ht : T ≤ d + U * twopow k)
    (hsec : ∀ j : Nat, j < M →
      RhBandAgree ((d + (U + j) * twopow k) + 1) (m * P) 0 (twopow k + 1)) :
    RhColAgree ((d + U * twopow k) + 1) (m * P) 1 (M * twopow k) := by
  rcases M with _ | M
  · omega
  · clear hM
    induction M with
    | zero =>
      have h0 := hsec 0 (by omega)
      rw [Nat.add_zero] at h0
      rw [Nat.one_mul]
      exact periodic_rhColAgree_one_of_rhBandAgree_zero T P hP hper m
        ((d + U * twopow k) + 1) (twopow k) (by omega) h0
    | succ M ih =>
      have h_prev := ih (fun j hj => hsec j (by omega))
      have h_last := hsec (M + 1) (by omega)
      have hU_le : U * twopow k ≤ (U + (M + 1)) * twopow k :=
        Nat.mul_le_mul_right (twopow k) (by omega)
      have h_last_col := periodic_rhColAgree_one_of_rhBandAgree_zero T P hP hper m
        ((d + (U + (M + 1)) * twopow k) + 1) (twopow k) (by omega) h_last
      intro s hs
      by_cases hle : s ≤ (M + 1) * twopow k
      · exact h_prev s hle
      · have hs' : s - (M + 1) * twopow k ≤ twopow k := by
          rw [Nat.add_mul (M + 1) 1 (twopow k), Nat.one_mul] at hs; omega
        have hstep := h_last_col (s - (M + 1) * twopow k) hs'
        have heq : ((d + (U + (M + 1)) * twopow k) + 1) + (s - (M + 1) * twopow k) =
            ((d + U * twopow k) + 1) + s := by
          rw [Nat.add_mul U (M + 1) (twopow k)]; omega
        rwa [heq] at hstep

/-- **Finite-Sector Refutation of `RhBandAgree` at Any Multiple `Q = m * P` (`not_periodic_finite_sector_rhBandAgree_mul`)**:
    under `CenterPeriodic T P` (`0 < P`), for `1 ≤ M`, `0 < m`, `T ≤ d + U * 2^k`, and `(d + U * 2^k) + m * P ≤ M * 2^k`, it is impossible that `RhBandAgree ((d + (U + j) * 2^k) + 1) (m * P) 0 (2^k + 1)` holds for all `j < M`! -/
theorem not_periodic_finite_sector_rhBandAgree_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U M m : Nat) (hM : 1 ≤ M) (hm : 0 < m)
    (ht : T ≤ d + U * twopow k)
    (hS : (d + U * twopow k) + m * P ≤ M * twopow k) :
    ¬ (∀ j : Nat, j < M →
      RhBandAgree ((d + (U + j) * twopow k) + 1) (m * P) 0 (twopow k + 1)) := by
  intro hsec
  have hcol := periodic_rhColAgree_one_of_finite_sectors T P hP hper k d U M m hM ht hsec
  exact not_periodic_rhColAgree_one_horizon T P hP hper m
    ((d + U * twopow k) + 1) (M * twopow k) hm (by omega) (by omega) hcol

/-- **Finite-Sector Refutation of `RhBandAgree` at `Q = lcm(P, 2^k)` (`not_periodic_finite_sector_rhBandAgree_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for `1 ≤ M`, `T ≤ d + U * 2^k`, and `(d + U * 2^k) + lcmPeriod P k ≤ M * 2^k`, it is impossible that `RhBandAgree ((d + (U + j) * 2^k) + 1) (lcmPeriod P k) 0 (2^k + 1)` holds for all `j < M` (eliminating the infinite quantifier `∀ u ≥ U` in `not_sector_rhBandAgree_lcmPeriod`)! -/
theorem not_periodic_finite_sector_rhBandAgree_lcmPeriod
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U M : Nat) (hM : 1 ≤ M)
    (ht : T ≤ d + U * twopow k)
    (hS : (d + U * twopow k) + lcmPeriod P k ≤ M * twopow k) :
    ¬ (∀ j : Nat, j < M →
      RhBandAgree ((d + (U + j) * twopow k) + 1) (lcmPeriod P k) 0 (twopow k + 1)) := by
  intro hsec
  have hm : 0 < twopow k / Nat.gcd P (twopow k) := lcmPeriod_div_pos P k hP
  have hsec' : ∀ j : Nat, j < M →
      RhBandAgree ((d + (U + j) * twopow k) + 1)
        ((twopow k / Nat.gcd P (twopow k)) * P) 0 (twopow k + 1) := by
    intro j hj
    rw [← lcmPeriod_eq_mul_period P k]
    exact hsec j hj
  have hS' : (d + U * twopow k) + (twopow k / Nat.gcd P (twopow k)) * P ≤ M * twopow k := by
    rwa [← lcmPeriod_eq_mul_period P k]
  exact not_periodic_finite_sector_rhBandAgree_mul T P hP hper k d U M
    (twopow k / Nat.gcd P (twopow k)) hM hm ht hS' hsec'

/-- **Exact Linearization of the Center-Adjacent OR Defect in `lhCenter` via the §6 `Φ` Fixed-Point Law (`periodic_lhCenter_or_zero_defect_eq`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t` with `T ≤ t`, because `lhCenter · 1` defect already vanishes at black center times by `lhCenter_one_eq_of_center_fixed`, the `m * P`-defect of `lhCenter · 1 || lhCenter · 0` equals the `m * P`-defect of `lhCenter · 1`! -/
theorem periodic_lhCenter_or_zero_defect_eq
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    bxor (lhCenter (t + m * P) 1 || lhCenter (t + m * P) 0)
      (lhCenter t 1 || lhCenter t 0) =
      bxor (lhCenter (t + m * P) 1) (lhCenter t 1) := by
  have hc0 : Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t :=
    Rule30UOR.Scale.center_mul hper m t ht
  have hc1 : Rule30UOR.Core.center ((t + m * P) + 1) = Rule30UOR.Core.center (t + 1) := by
    rw [show (t + m * P) + 1 = (t + 1) + m * P by omega]
    exact Rule30UOR.Scale.center_mul hper m (t + 1) (by omega)
  rw [lhCenter_zero_eq_center (t + m * P), lhCenter_zero_eq_center t,
    lhCenter_one_eq_of_center_fixed (t + m * P),
    lhCenter_one_eq_of_center_fixed t,
    hc0, hc1]
  cases Rule30UOR.Core.center (t + 1) <;>
    cases Rule30UOR.Core.center t <;>
    cases rhCenter (t + m * P) 1 <;>
    cases rhCenter t 1 <;> rfl

/-- **Exact Linear Time-Derivative Law for the Column `-2` Defect in `lhCenter` (`periodic_lhCenter_two_defect_eq`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t` with `T ≤ t`, the `m * P`-defect of `lhCenter · 2` equals the linear discrete time-derivative of the `lhCenter · 1` defect:
    `bxor (lhCenter (t + m * P) 2) (lhCenter t 2) = bxor (bxor (lhCenter ((t + 1) + m * P) 1) (lhCenter (t + 1) 1)) (bxor (lhCenter (t + m * P) 1) (lhCenter t 1))`! -/
theorem periodic_lhCenter_two_defect_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    bxor (lhCenter (t + m * P) 2) (lhCenter t 2) =
      bxor
        (bxor (lhCenter ((t + 1) + m * P) 1) (lhCenter (t + 1) 1))
        (bxor (lhCenter (t + m * P) 1) (lhCenter t 1)) := by
  have hor := periodic_lhCenter_or_zero_defect_eq T P hP hper m t ht
  rw [lhCenter_outward_step (t + m * P) 0,
    lhCenter_outward_step t 0,
    show (t + m * P) + 1 = (t + 1) + m * P by omega]
  change bxor
      (bxor (lhCenter ((t + 1) + m * P) 1) (lhCenter (t + m * P) 1 || lhCenter (t + m * P) 0))
      (bxor (lhCenter (t + 1) 1) (lhCenter t 1 || lhCenter t 0)) = _
  rw [← hor]
  cases lhCenter ((t + 1) + m * P) 1 <;>
    cases lhCenter (t + 1) 1 <;>
    cases (lhCenter (t + m * P) 1 || lhCenter (t + m * P) 0) <;>
    cases (lhCenter t 1 || lhCenter t 0) <;> rfl

/-- **Unconditional Identity Between `lhCenter` and `row` Bit Readout (`lhCenter_eq_row_testBit_uncond`)**:
    for ALL `t, p : Nat` (no light-cone bound `p ≤ t` required, since both sides vanish when `t < p`), `lhCenter t p = (row t).testBit (t + p)`! -/
theorem lhCenter_eq_row_testBit_uncond (t p : Nat) :
    lhCenter t p = (row t).testBit (t + p) := by
  by_cases hp : p ≤ t
  · exact lhCenter_eq_row_testBit t p hp
  · rw [lhCenter_gt_eq_false t p (by omega),
      row_testBit,
      rdiag_gt_two_mul t (t + p) (by omega)]

theorem lhCenter_eq_row_testBit_uncond_prop (t p : Nat) :
    lhCenter t p = wittBitBool (row t) (t + p) :=
  lhCenter_eq_row_testBit_uncond t p

/-- **Fully Unconditional `2^k`-Scale Forward Step of `lhCenter` (`lhCenter_scale_step_uncond`)**:
    for ALL `t, k, p : Nat` (no light-cone bound required!), `lhCenter (t + 2^k) (p + 2^k)` equals `bxor (bxor (bxor (lhCenter t p) (lhCenter t (p + 2^k))) (lhCenter t (p + 2^(k+1)))) ((winWitt t (2^k)).testBit (t + p + 2^(k+1)))`! -/
theorem lhCenter_scale_step_uncond (t k p : Nat) :
    lhCenter (t + twopow k) (p + twopow k) =
      bxor
        (bxor (bxor (lhCenter t p) (lhCenter t (p + twopow k)))
          (lhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [lhCenter_eq_row_testBit_uncond (t + twopow k) (p + twopow k),
    show (t + twopow k) + (p + twopow k) = t + p + twopow (k + 1) by omega]
  have hsc := congrArg (fun n => n.testBit (t + p + twopow (k + 1))) (row_scale t k)
  rw [Nat.testBit_xor] at hsc
  have hphi : (phiScale k (row t)).testBit (t + p + twopow (k + 1)) =
      ((lhCenter t p ^^ lhCenter t (p + twopow k)) ^^
        lhCenter t (p + twopow (k + 1))) := by
    change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit (t + p + twopow (k + 1)) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide (t + p + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (t + p + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show t + p + twopow (k + 1) - twopow k = t + (p + twopow k) by omega,
      show t + p + twopow (k + 1) - (twopow k + twopow k) = t + p by omega,
      show t + p + twopow (k + 1) = t + (p + twopow (k + 1)) by omega,
      ← lhCenter_eq_row_testBit_uncond t (p + twopow (k + 1)),
      ← lhCenter_eq_row_testBit_uncond t (p + twopow k),
      ← lhCenter_eq_row_testBit_uncond t p]
    cases lhCenter t p <;>
      cases lhCenter t (p + twopow k) <;>
      cases lhCenter t (p + twopow (k + 1)) <;> rfl
  rw [hsc, hphi]
  simp only [bxor_eq_xor]

theorem lhCenter_scale_step_uncond_prop (t k p : Nat) :
    lhCenter (t + twopow k) (p + twopow k) =
      bxor
        (bxor (bxor (lhCenter t p) (lhCenter t (p + twopow k)))
          (lhCenter t (p + twopow (k + 1))))
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) :=
  lhCenter_scale_step_uncond t k p

/-- **Fully Unconditional `2^k`-Scale Outward Step of `lhCenter` (`lhCenter_scale_outward_step_uncond`)**:
    for ALL `t, k, p : Nat`, solving `lhCenter_scale_step_uncond` for the outer column `lhCenter t (p + 2^(k+1))` expresses it in terms of `lhCenter (t + 2^k) (p + 2^k)`, `lhCenter t p`, `lhCenter t (p + 2^k)`, and `(winWitt t (2^k)).testBit (t + p + 2^(k+1))`! -/
theorem lhCenter_scale_outward_step_uncond (t k p : Nat) :
    lhCenter t (p + twopow (k + 1)) =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p))
          (lhCenter t (p + twopow k)))
        ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) := by
  rw [lhCenter_scale_step_uncond t k p]
  simp only [bxor_eq_xor]
  cases lhCenter t p <;>
    cases lhCenter t (p + twopow k) <;>
    cases lhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem lhCenter_scale_outward_step_uncond_prop (t k p : Nat) :
    lhCenter t (p + twopow (k + 1)) =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p))
          (lhCenter t (p + twopow k)))
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) :=
  lhCenter_scale_outward_step_uncond t k p

/-- **Unconditional Cross-Center `2^k`-Scale Step Between `lhCenter` and `rhCenter` (`lhCenter_scale_cross_step`)**:
    for ALL `t, k, r : Nat` with `r ≤ 2^k` (no light-cone bound `r ≤ t` required!), `lhCenter (t + 2^k) (2^k - r)` equals `bxor (bxor (bxor (rhCenter t r) (lhCenter t (2^k - r))) (lhCenter t (2^(k+1) - r))) ((winWitt t (2^k)).testBit ((t + 2^(k+1)) - r))`! -/
theorem lhCenter_scale_cross_step (t k r : Nat) (hr : r ≤ twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      bxor
        (bxor (bxor (rhCenter t r) (lhCenter t (twopow k - r)))
          (lhCenter t (twopow (k + 1) - r)))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [lhCenter_eq_row_testBit_uncond (t + twopow k) (twopow k - r),
    show (t + twopow k) + (twopow k - r) = (t + twopow (k + 1)) - r by omega]
  have hsc := congrArg (fun n => n.testBit ((t + twopow (k + 1)) - r)) (row_scale t k)
  rw [Nat.testBit_xor] at hsc
  have hphi : (phiScale k (row t)).testBit ((t + twopow (k + 1)) - r) =
      ((rhCenter t r ^^ lhCenter t (twopow k - r)) ^^
        lhCenter t (twopow (k + 1) - r)) := by
    change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit ((t + twopow (k + 1)) - r) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d1 : decide ((t + twopow (k + 1)) - r ≥ twopow k) = true := decide_eq_true (by omega)
    have h0 : (row t).testBit ((t + twopow (k + 1)) - r) = lhCenter t (twopow (k + 1) - r) := by
      rw [show (t + twopow (k + 1)) - r = t + (twopow (k + 1) - r) by omega,
        ← lhCenter_eq_row_testBit_uncond t (twopow (k + 1) - r)]
    have h1 : (decide ((t + twopow (k + 1)) - r ≥ twopow k) &&
        (row t).testBit (((t + twopow (k + 1)) - r) - twopow k)) =
        lhCenter t (twopow k - r) := by
      rw [d1, Bool.true_and,
        show ((t + twopow (k + 1)) - r) - twopow k = t + (twopow k - r) by omega,
        ← lhCenter_eq_row_testBit_uncond t (twopow k - r)]
    have h2 : (decide ((t + twopow (k + 1)) - r ≥ twopow k + twopow k) &&
        (row t).testBit (((t + twopow (k + 1)) - r) - (twopow k + twopow k))) =
        rhCenter t r := by
      by_cases hrt : r ≤ t
      · have d2 : decide ((t + twopow (k + 1)) - r ≥ twopow k + twopow k) = true :=
          decide_eq_true (by omega)
        rw [d2, Bool.true_and,
          show ((t + twopow (k + 1)) - r) - (twopow k + twopow k) = t - r by omega,
          ← rhCenter_eq_row_testBit t r hrt]
      · have d2 : decide ((t + twopow (k + 1)) - r ≥ twopow k + twopow k) = false :=
          decide_eq_false (by omega)
        rw [d2, Bool.false_and, rhCenter_gt_eq_false t r (by omega)]
    rw [h0, h1, h2]
    cases rhCenter t r <;>
      cases lhCenter t (twopow k - r) <;>
      cases lhCenter t (twopow (k + 1) - r) <;> rfl
  rw [hsc, hphi]
  simp only [bxor_eq_xor]

theorem lhCenter_scale_cross_step_prop (t k r : Nat) (hr : r ≤ twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      bxor
        (bxor (bxor (rhCenter t r) (lhCenter t (twopow k - r)))
          (lhCenter t (twopow (k + 1) - r)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  lhCenter_scale_cross_step t k r hr

/-- **Unconditional Cross-Center `2^k`-Scale Formula for `rhCenter` in Terms of `lhCenter` and `winWitt` (`rhCenter_eq_lhCenter_scale_cross`)**:
    for ALL `t, k, r : Nat` with `r ≤ 2^k`, solving `lhCenter_scale_cross_step` for `rhCenter t r` expresses every right-half column `r ∈ [0, 2^k]` directly in terms of `lhCenter (t + 2^k) (2^k - r)`, `lhCenter t (2^k - r)`, `lhCenter t (2^(k+1) - r)`, and `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)`! -/
theorem rhCenter_eq_lhCenter_scale_cross (t k r : Nat) (hr : r ≤ twopow k) :
    rhCenter t r =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (twopow k - r)) (lhCenter t (twopow k - r)))
          (lhCenter t (twopow (k + 1) - r)))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)) := by
  rw [lhCenter_scale_cross_step t k r hr]
  simp only [bxor_eq_xor]
  cases rhCenter t r <;>
    cases lhCenter t (twopow k - r) <;>
    cases lhCenter t (twopow (k + 1) - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;> rfl

theorem rhCenter_eq_lhCenter_scale_cross_prop (t k r : Nat) (hr : r ≤ twopow k) :
    rhCenter t r =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (twopow k - r)) (lhCenter t (twopow k - r)))
          (lhCenter t (twopow (k + 1) - r)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  rhCenter_eq_lhCenter_scale_cross t k r hr

/-- **Cross-Center `2^k`-Scale Transport from `LhBandAgree` and `WinWittAgree` to `RhBandAgree` (`rhBandAgree_of_lhBandAgree_scale_cross`)**:
    for `L ≤ 2^k`, if `LhBandAgree (t + 2^k) Q (2^k - L) L`, `LhBandAgree t Q (2^k - L) L`, `LhBandAgree t Q (2^(k+1) - L) L`, and `WinWittAgree t k Q ((t + 2^(k+1)) - L) L` hold, then `RhBandAgree t Q 0 L` holds across the right half `[0, L]`! -/
theorem rhBandAgree_of_lhBandAgree_scale_cross (t k Q L : Nat)
    (hL : L ≤ twopow k)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L)
    (h1 : LhBandAgree t Q (twopow k - L) L)
    (h2 : LhBandAgree t Q (twopow (k + 1) - L) L)
    (hw : WinWittAgree t k Q ((t + twopow (k + 1)) - L) L) :
    RhBandAgree t Q 0 L := by
  intro r hr
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [Nat.zero_add,
    rhCenter_eq_lhCenter_scale_cross (t + Q) k r (by omega),
    rhCenter_eq_lhCenter_scale_cross t k r (by omega)]
  have hbl := hlate (L - r) (by omega)
  have hb1 := h1 (L - r) (by omega)
  have hb2 := h2 (L - r) (by omega)
  have hwi := hw (L - r) (by omega)
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (twopow k - L) + (L - r) = twopow k - r by omega] at hbl
  rw [show (twopow k - L) + (L - r) = twopow k - r by omega] at hb1
  rw [show (twopow (k + 1) - L) + (L - r) = twopow (k + 1) - r by omega] at hb2
  rw [show ((t + twopow (k + 1)) - L) + (L - r) + Q =
      ((t + Q) + twopow (k + 1)) - r by omega,
    show ((t + twopow (k + 1)) - L) + (L - r) =
      (t + twopow (k + 1)) - r by omega] at hwi
  rw [hbl, hb1, hb2, hwi]

/-- **Converse Cross-Center `2^k`-Scale Transport to `WinWittAgree` (`winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross`)**:
    for `L ≤ 2^k`, if `RhBandAgree t Q 0 L`, `LhBandAgree (t + 2^k) Q (2^k - L) L`, `LhBandAgree t Q (2^k - L) L`, and `LhBandAgree t Q (2^(k+1) - L) L` hold, then `WinWittAgree t k Q ((t + 2^(k+1)) - L) L` holds! -/
theorem winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross (t k Q L : Nat)
    (hL : L ≤ twopow k)
    (hrh : RhBandAgree t Q 0 L)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L)
    (h1 : LhBandAgree t Q (twopow k - L) L)
    (h2 : LhBandAgree t Q (twopow (k + 1) - L) L) :
    WinWittAgree t k Q ((t + twopow (k + 1)) - L) L := by
  intro j hj
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hsQ := rhCenter_eq_lhCenter_scale_cross (t + Q) k (L - j) (by omega)
  have hs0 := rhCenter_eq_lhCenter_scale_cross t k (L - j) (by omega)
  have hbr := hrh (L - j) (by omega)
  have hbl := hlate j hj
  have hb1 := h1 j hj
  have hb2 := h2 j hj
  rw [Nat.zero_add] at hbr
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (twopow k - L) + j = twopow k - (L - j) by omega] at hbl
  rw [show (twopow k - L) + j = twopow k - (L - j) by omega] at hb1
  rw [show (twopow (k + 1) - L) + j = twopow (k + 1) - (L - j) by omega] at hb2
  rw [show ((t + twopow (k + 1)) - L) + j + Q = ((t + Q) + twopow (k + 1)) - (L - j) by omega,
    show ((t + twopow (k + 1)) - L) + j = (t + twopow (k + 1)) - (L - j) by omega]
  rw [hbr, hbl, hb1, hb2] at hsQ
  revert hsQ hs0
  simp only [bxor_eq_xor]
  cases rhCenter t (L - j) <;>
    cases lhCenter (t + twopow k) (twopow k - (L - j)) <;>
    cases lhCenter t (twopow k - (L - j)) <;>
    cases lhCenter t (twopow (k + 1) - (L - j)) <;>
    cases (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (L - j)) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (L - j)) <;> decide

/-- **Deriving `RhBandAgree` on `[0, 2^k]` from `LhColAgree · 1` and `WinWittAgree` (`periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t`, if `LhColAgree t (m * P) 1 (2^(k+1))` and `WinWittAgree t k (m * P) (t + 2^k) (2^k)` hold, then outward left-half determination supplies all three `LhBandAgree` terms in `rhBandAgree_of_lhBandAgree_scale_cross`, establishing `RhBandAgree t (m * P) 0 (2^k)`! -/
theorem periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : LhColAgree t (m * P) 1 (twopow (k + 1)))
    (hw : WinWittAgree t k (m * P) (t + twopow k) (twopow k)) :
    RhBandAgree t (m * P) 0 (twopow k) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hcol0 := periodic_lhColAgree_zero T P hP hper m t (twopow (k + 1)) ht
  have hl_full := lhBandAgree_of_outward_determine t (m * P) 0 (twopow (k + 1)) hcol0 hcol1
  have h1 : LhBandAgree t (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hl_full i (by omega)
  have h2 : LhBandAgree t (m * P) (twopow (k + 1) - twopow k) (twopow k) := by
    intro i hi
    have heq := hl_full (twopow k + i) (by omega)
    rwa [show 0 + (twopow k + i) = (twopow (k + 1) - twopow k) + i by omega] at heq
  have hcol0_late := periodic_lhColAgree_zero T P hP hper m (t + twopow k) (twopow k) (by omega)
  have hcol1_late : LhColAgree (t + twopow k) (m * P) 1 (twopow k) := by
    intro s hs
    have heq := hcol1 (twopow k + s) (by omega)
    rwa [show t + (twopow k + s) = (t + twopow k) + s by omega] at heq
  have hl_late := lhBandAgree_of_outward_determine (t + twopow k) (m * P) 0 (twopow k)
    hcol0_late hcol1_late
  have hlate : LhBandAgree (t + twopow k) (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hl_late i (by omega)
  have hw' : WinWittAgree t k (m * P) ((t + twopow (k + 1)) - twopow k) (twopow k) := by
    rwa [show (t + twopow (k + 1)) - twopow k = t + twopow k by omega]
  exact rhBandAgree_of_lhBandAgree_scale_cross t k (m * P) (twopow k)
    (by omega) hlate h1 h2 hw'

/-- **Converse Derivation of `WinWittAgree` from `LhColAgree · 1` and `RhBandAgree` (`periodic_winWittAgree_of_lhColAgree_one_and_rhBandAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t`, if `LhColAgree t (m * P) 1 (2^(k+1))` and `RhBandAgree t (m * P) 0 (2^k)` hold, then `WinWittAgree t k (m * P) (t + 2^k) (2^k)` holds! -/
theorem periodic_winWittAgree_of_lhColAgree_one_and_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : LhColAgree t (m * P) 1 (twopow (k + 1)))
    (hrh : RhBandAgree t (m * P) 0 (twopow k)) :
    WinWittAgree t k (m * P) (t + twopow k) (twopow k) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hcol0 := periodic_lhColAgree_zero T P hP hper m t (twopow (k + 1)) ht
  have hl_full := lhBandAgree_of_outward_determine t (m * P) 0 (twopow (k + 1)) hcol0 hcol1
  have h1 : LhBandAgree t (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hl_full i (by omega)
  have h2 : LhBandAgree t (m * P) (twopow (k + 1) - twopow k) (twopow k) := by
    intro i hi
    have heq := hl_full (twopow k + i) (by omega)
    rwa [show 0 + (twopow k + i) = (twopow (k + 1) - twopow k) + i by omega] at heq
  have hcol0_late := periodic_lhColAgree_zero T P hP hper m (t + twopow k) (twopow k) (by omega)
  have hcol1_late : LhColAgree (t + twopow k) (m * P) 1 (twopow k) := by
    intro s hs
    have heq := hcol1 (twopow k + s) (by omega)
    rwa [show t + (twopow k + s) = (t + twopow k) + s by omega] at heq
  have hl_late := lhBandAgree_of_outward_determine (t + twopow k) (m * P) 0 (twopow k)
    hcol0_late hcol1_late
  have hlate : LhBandAgree (t + twopow k) (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hl_late i (by omega)
  have hw := winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross t k (m * P) (twopow k)
    (by omega) hrh hlate h1 h2
  rwa [show (t + twopow (k + 1)) - twopow k = t + twopow k by omega] at hw

/-- **Unconditional `2^k`-Scale Forward Band Transport of `LhBandAgree` (`lhBandAgree_scale_step_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if `LhBandAgree` holds on `p0`, `p0 + 2^k`, and `p0 + 2^(k+1)` at time `t`, and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` holds at time `t`, then `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` holds! -/
theorem lhBandAgree_scale_step_uncond (t k Q p0 L : Nat)
    (h0 : LhBandAgree t Q p0 L)
    (h1 : LhBandAgree t Q (p0 + twopow k) L)
    (h2 : LhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  intro i hi
  have hsQ := lhCenter_scale_step_uncond (t + Q) k (p0 + i)
  have hs0 := lhCenter_scale_step_uncond t k (p0 + i)
  have hb0 := h0 i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega,
    hsQ, hs0,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    show (t + Q) + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i + Q by omega,
    show t + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i by omega,
    hb0, hb1, hb2, hwi]

/-- **Unconditional `2^k`-Scale Outward Band Transport of `LhBandAgree` (`lhBandAgree_scale_outward_step_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if `LhBandAgree (t + 2^k) Q (p0 + 2^k) L`, `LhBandAgree t Q p0 L`, `LhBandAgree t Q (p0 + 2^k) L`, and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` hold, then `LhBandAgree t Q (p0 + 2^(k+1)) L` holds! -/
theorem lhBandAgree_scale_outward_step_uncond (t k Q p0 L : Nat)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h0 : LhBandAgree t Q p0 L)
    (h1 : LhBandAgree t Q (p0 + twopow k) L)
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree t Q (p0 + twopow (k + 1)) L := by
  intro i hi
  have hsQ := lhCenter_scale_outward_step_uncond (t + Q) k (p0 + i)
  have hs0 := lhCenter_scale_outward_step_uncond t k (p0 + i)
  have hbl := hlate i hi
  have hb0 := h0 i hi
  have hb1 := h1 i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [show (p0 + twopow (k + 1)) + i = (p0 + i) + twopow (k + 1) by omega,
    hsQ, hs0, hbl,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (t + Q) + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i + Q by omega,
    show t + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i by omega,
    hb0, hb1, hwi]

/-- **Exact Diagonal Difference Law of the Driven Left Half `lhCenter` (`lhCenter_diag_diff_eq_or`)**:
    for all `t, p : Nat`, `bxor (lhCenter (t + 1) (p + 1)) (lhCenter t (p + 2)) = (lhCenter t (p + 1) || lhCenter t p)`! -/
theorem lhCenter_diag_diff_eq_or (t p : Nat) :
    bxor (lhCenter (t + 1) (p + 1)) (lhCenter t (p + 2)) =
      (lhCenter t (p + 1) || lhCenter t p) := by
  rw [lhCenter_step_succ t p]
  cases lhCenter t (p + 2) <;>
    cases (lhCenter t (p + 1) || lhCenter t p) <;> rfl

/-- **Exact Outward Step Law for the Left-Half `Q`-Defect (`lhCenter_defect_outward_step`)**:
    for all `t, Q, p : Nat`, the outward `Q`-defect `bxor (lhCenter (t + Q) (p + 2)) (lhCenter t (p + 2))` equals `bxor (bxor (lhCenter ((t + 1) + Q) (p + 1)) (lhCenter (t + 1) (p + 1))) (bxor (lhCenter (t + Q) (p + 1) || lhCenter (t + Q) p) (lhCenter t (p + 1) || lhCenter t p))`! -/
theorem lhCenter_defect_outward_step (t Q p : Nat) :
    bxor (lhCenter (t + Q) (p + 2)) (lhCenter t (p + 2)) =
      bxor
        (bxor (lhCenter ((t + 1) + Q) (p + 1)) (lhCenter (t + 1) (p + 1)))
        (bxor (lhCenter (t + Q) (p + 1) || lhCenter (t + Q) p)
          (lhCenter t (p + 1) || lhCenter t p)) := by
  rw [lhCenter_outward_step (t + Q) p,
    lhCenter_outward_step t p,
    show (t + Q) + 1 = (t + 1) + Q by omega]
  cases lhCenter ((t + 1) + Q) (p + 1) <;>
    cases lhCenter (t + 1) (p + 1) <;>
    cases (lhCenter (t + Q) (p + 1) || lhCenter (t + Q) p) <;>
    cases (lhCenter t (p + 1) || lhCenter t p) <;> rfl

/-- **Linearized Outward Defect Step in `lhCenter` When Column `p` Agrees (`lhCenter_defect_outward_of_col_eq`)**:
    whenever `lhCenter (t + Q) p = lhCenter t p` (which is already known when marching outward from the center!), the outward `Q`-defect at `p + 2` is linear in the column-`p + 1` defects:
    `bxor (lhCenter (t + Q) (p + 2)) (lhCenter t (p + 2)) = bxor (bxor (lhCenter ((t + 1) + Q) (p + 1)) (lhCenter (t + 1) (p + 1))) (!lhCenter t p && bxor (lhCenter (t + Q) (p + 1)) (lhCenter t (p + 1)))`! -/
theorem lhCenter_defect_outward_of_col_eq (t Q p : Nat)
    (heq : lhCenter (t + Q) p = lhCenter t p) :
    bxor (lhCenter (t + Q) (p + 2)) (lhCenter t (p + 2)) =
      bxor
        (bxor (lhCenter ((t + 1) + Q) (p + 1)) (lhCenter (t + 1) (p + 1)))
        (!lhCenter t p && bxor (lhCenter (t + Q) (p + 1)) (lhCenter t (p + 1))) := by
  rw [lhCenter_defect_outward_step t Q p, heq]
  cases lhCenter ((t + 1) + Q) (p + 1) <;>
    cases lhCenter (t + 1) (p + 1) <;>
    cases lhCenter (t + Q) (p + 1) <;>
    cases lhCenter t (p + 1) <;>
    cases lhCenter t p <;> rfl

/-- **Black-Cell Shielding in Outward Left-Half Defect Propagation (`lhCenter_defect_outward_of_black`)**:
    whenever `lhCenter (t + Q) p = true` and `lhCenter t p = true`, the column-`p + 1` defect at time `t` is completely shielded out, so `bxor (lhCenter (t + Q) (p + 2)) (lhCenter t (p + 2)) = bxor (lhCenter ((t + 1) + Q) (p + 1)) (lhCenter (t + 1) (p + 1))`! -/
theorem lhCenter_defect_outward_of_black (t Q p : Nat)
    (hbQ : lhCenter (t + Q) p = true)
    (hb0 : lhCenter t p = true) :
    bxor (lhCenter (t + Q) (p + 2)) (lhCenter t (p + 2)) =
      bxor (lhCenter ((t + 1) + Q) (p + 1)) (lhCenter (t + 1) (p + 1)) := by
  have heq : lhCenter (t + Q) p = lhCenter t p := by rw [hbQ, hb0]
  rw [lhCenter_defect_outward_of_col_eq t Q p heq, hb0]
  cases lhCenter ((t + 1) + Q) (p + 1) <;>
    cases lhCenter (t + 1) (p + 1) <;>
    cases lhCenter (t + Q) (p + 1) <;>
    cases lhCenter t (p + 1) <;> rfl

/-- **Exact Left-Edge Vanishing of `winWitt` (`winWitt_testBit_left_edge`)**:
    for all `t, k : Nat`, at the left edge `p = t`, `lhCenter (t + 2^k) (t + 2^k) = true` and `lhCenter t t = true` cancel in `lhCenter_scale_step_uncond`, proving `(winWitt t (2^k)).testBit (t + t + 2^(k+1)) = false`! -/
theorem winWitt_testBit_left_edge (t k : Nat) :
    (winWitt t (twopow k)).testBit (t + t + twopow (k + 1)) = false := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hpos : 0 < twopow k := by
    have := twopow_gt_self k
    omega
  have hs := lhCenter_scale_step_uncond t k t
  rw [lhCenter_self_eq_true (t + twopow k),
    lhCenter_self_eq_true t,
    lhCenter_gt_eq_false t (t + twopow k) (by omega),
    lhCenter_gt_eq_false t (t + twopow (k + 1)) (by omega)] at hs
  revert hs
  cases (winWitt t (twopow k)).testBit (t + t + twopow (k + 1)) <;> decide

theorem winWitt_testBit_left_edge_prop (t k : Nat) :
    wittBitBool (winWitt t (twopow k)) (t + t + twopow (k + 1)) = false :=
  winWitt_testBit_left_edge t k

/-- **Vanishing of `winWitt` Strictly Outside the Left Light Cone (`winWitt_testBit_gt_left_edge`)**:
    for all `t, k, p : Nat` with `t < p`, all four `lhCenter` terms in `lhCenter_scale_step_uncond` vanish, proving `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = false`! -/
theorem winWitt_testBit_gt_left_edge (t k p : Nat) (hp : t < p) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) = false := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hs := lhCenter_scale_step_uncond t k p
  rw [lhCenter_gt_eq_false (t + twopow k) (p + twopow k) (by omega),
    lhCenter_gt_eq_false t p (by omega),
    lhCenter_gt_eq_false t (p + twopow k) (by omega),
    lhCenter_gt_eq_false t (p + twopow (k + 1)) (by omega)] at hs
  revert hs
  cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> decide

theorem winWitt_testBit_gt_left_edge_prop (t k p : Nat) (hp : t < p) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) = false :=
  winWitt_testBit_gt_left_edge t k p hp

/-- **Vanishing of `winWitt` At and Outside the Left Light Cone (`winWitt_testBit_ge_left_edge`)**:
    for all `t, k, p : Nat` with `t ≤ p`, `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = false`! -/
theorem winWitt_testBit_ge_left_edge (t k p : Nat) (hp : t ≤ p) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) = false := by
  rcases Nat.eq_or_lt_of_le hp with rfl | hlt
  · exact winWitt_testBit_left_edge t k
  · exact winWitt_testBit_gt_left_edge t k p hlt

theorem winWitt_testBit_ge_left_edge_prop (t k p : Nat) (hp : t ≤ p) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) = false :=
  winWitt_testBit_ge_left_edge t k p hp

/-- **Settled Left-Edge Vanishing of `winWitt` Inside the Light Cone (`winWitt_testBit_settled_left`)**:
    for all `t, k, j : Nat` with `j ≤ k`, `j ≤ t`, and `settle j ≤ t`, left-wing settled `2^k`-periodicity (`ldiag_settled_restart`) cancels `lhCenter (t + 2^k) ((t - j) + 2^k)` against `lhCenter t (t - j)` in `lhCenter_scale_step_uncond`, proving `(winWitt t (2^k)).testBit (t + (t - j) + 2^(k+1)) = false` (the exact left-wing counterpart of `winWitt_testBit_low`)! -/
theorem winWitt_testBit_settled_left (t k j : Nat)
    (hj : j ≤ k) (hjt : j ≤ t) (hset : settle j ≤ t) :
    (winWitt t (twopow k)).testBit (t + (t - j) + twopow (k + 1)) = false := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hk_lt : k < twopow k := twopow_gt_self k
  have hs := lhCenter_scale_step_uncond t k (t - j)
  have hl_late : lhCenter (t + twopow k) ((t - j) + twopow k) = ldiag j t := by
    rw [lhCenter_eq_ldiag (t + twopow k) ((t - j) + twopow k) (by omega),
      show (t + twopow k) - ((t - j) + twopow k) = j by omega]
    have hres := ldiag_settled_restart k j 1 t hj hset
    rwa [Nat.one_mul] at hres
  have hl_early : lhCenter t (t - j) = ldiag j t := by
    rw [lhCenter_eq_ldiag t (t - j) (by omega),
      show t - (t - j) = j by omega]
  rw [hl_late, hl_early,
    lhCenter_gt_eq_false t ((t - j) + twopow k) (by omega),
    lhCenter_gt_eq_false t ((t - j) + twopow (k + 1)) (by omega)] at hs
  revert hs
  cases ldiag j t <;>
    cases (winWitt t (twopow k)).testBit (t + (t - j) + twopow (k + 1)) <;> decide

theorem winWitt_testBit_settled_left_prop (t k j : Nat)
    (hj : j ≤ k) (hjt : j ≤ t) (hset : SettledBy j t) :
    wittBitBool (winWitt t (twopow k)) (t + (t - j) + twopow (k + 1)) = false :=
  winWitt_testBit_settled_left t k j hj hjt hset

/-- **Unconditional Left-Edge `LhBandAgree` Outside the Light Cone (`lhBandAgree_outside_cone`)**:
    for `t + Q < p0`, `LhBandAgree t Q p0 L` holds unconditionally. -/
theorem lhBandAgree_outside_cone (t Q p0 L : Nat) (h : t + Q < p0) :
    LhBandAgree t Q p0 L := by
  intro i _
  rw [lhCenter_gt_eq_false (t + Q) (p0 + i) (by omega),
    lhCenter_gt_eq_false t (p0 + i) (by omega)]

/-- **Sub-interval Monotonicity of `LhBandAgree` (`lhBandAgree_mono`)**:
    if `LhBandAgree t Q p0 L` holds on `[p0, p0 + L]` and `[p0', p0' + L'] ⊆ [p0, p0 + L]`, then `LhBandAgree t Q p0' L'` holds. -/
theorem lhBandAgree_mono (t Q p0 L p0' L' : Nat)
    (hp : p0 ≤ p0') (hL : p0' + L' ≤ p0 + L)
    (h : LhBandAgree t Q p0 L) :
    LhBandAgree t Q p0' L' := by
  intro i hi
  have hj : (p0' - p0) + i ≤ L := by omega
  have heq := h ((p0' - p0) + i) hj
  rwa [show p0 + ((p0' - p0) + i) = p0' + i by omega] at heq

/-- **Sub-interval Monotonicity of `LhColAgree` (`lhColAgree_mono`)**:
    if `LhColAgree t Q p0 S` holds on `[t, t + S]` and `[t + s0, t + s0 + S'] ⊆ [t, t + S]`, then `LhColAgree (t + s0) Q p0 S'` holds. -/
theorem lhColAgree_mono (t Q p0 S s0 S' : Nat)
    (hs : s0 + S' ≤ S)
    (h : LhColAgree t Q p0 S) :
    LhColAgree (t + s0) Q p0 S' := by
  intro s hs'
  have heq := h (s0 + s) (by omega)
  rwa [show t + (s0 + s) = (t + s0) + s by omega] at heq

/-- **One-Step Forward Propagation of `LhBandAgree` (`lhBandAgree_step`)**:
    each step `t ↦ t + 1` in the driven left half carries `LhBandAgree t Q p0 (L + 2)` on `[p0, p0 + L + 2]` to `LhBandAgree (t + 1) Q (p0 + 1) L` on `[p0 + 1, p0 + 1 + L]`. -/
theorem lhBandAgree_step (t Q p0 L : Nat)
    (h : LhBandAgree t Q p0 (L + 2)) :
    LhBandAgree (t + 1) Q (p0 + 1) L := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 1) (by omega)
  have h2 := h (i + 2) (by omega)
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show (p0 + 1) + i = (p0 + i) + 1 by omega,
    lhCenter_step_succ (t + Q) (p0 + i),
    lhCenter_step_succ t (p0 + i),
    show (p0 + i) + 1 = p0 + (i + 1) by omega,
    show (p0 + i) + 2 = p0 + (i + 2) by omega,
    h0, h1, h2]

/-- **Multi-Step Forward Propagation of `LhBandAgree` (`lhBandAgree_steps`)**:
    by induction on `s : Nat`, `LhBandAgree t Q p0 (L + 2 * s)` implies `LhBandAgree (t + s) Q (p0 + s) L`. -/
theorem lhBandAgree_steps (t Q p0 L s : Nat)
    (h : LhBandAgree t Q p0 (L + 2 * s)) :
    LhBandAgree (t + s) Q (p0 + s) L := by
  induction s generalizing t p0 L with
  | zero =>
    simpa using h
  | succ s ih =>
    have h' : LhBandAgree t Q p0 ((L + 2 * s) + 2) := by
      intro i hi
      exact h i (by omega)
    have h1 := lhBandAgree_step t Q p0 (L + 2 * s) h'
    have h2 := ih (t + 1) (p0 + 1) L h1
    rw [show (t + 1) + s = t + (s + 1) by omega,
      show (p0 + 1) + s = p0 + (s + 1) by omega] at h2
    exact h2

/-- **Free Inward Extension of `LhBandAgree` from Column `-1` to Column `0` under `CenterPeriodic` (`periodic_lhBandAgree_zero_of_one`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t`, `LhBandAgree t (m * P) 1 L` automatically extends to `LhBandAgree t (m * P) 0 (L + 1)` because `lhCenter · 0 = center ·` is `m * P`-periodic! -/
theorem periodic_lhBandAgree_zero_of_one
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : LhBandAgree t (m * P) 1 L) :
    LhBandAgree t (m * P) 0 (L + 1) := by
  intro i hi
  rcases i with _ | i
  · simp only [Nat.zero_add, lhCenter_zero_eq_center]
    exact Rule30UOR.Scale.center_mul hper m t ht
  · have hi' : i ≤ L := by omega
    have h1 := h i hi'
    rwa [show 0 + (i + 1) = 1 + i by omega]

/-- **Deriving `RhBandAgree` on `[0, 2^k]` from `RhColAgree · 1` and `WinWittAgree` (`periodic_rhBandAgree_of_rhColAgree_one_and_winWittAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t`, if `RhColAgree t (m * P) 1 (2^(k+1))` and `WinWittAgree t k (m * P) (t + 2^k) (2^k)` hold, then `periodic_lhColAgree_one_of_rhColAgree_one` and `periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree` establish `RhBandAgree t (m * P) 0 (2^k)`! -/
theorem periodic_rhBandAgree_of_rhColAgree_one_and_winWittAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : RhColAgree t (m * P) 1 (twopow (k + 1)))
    (hw : WinWittAgree t k (m * P) (t + twopow k) (twopow k)) :
    RhBandAgree t (m * P) 0 (twopow k) := by
  have hlcol1 := periodic_lhColAgree_one_of_rhColAgree_one T P hP hper m t (twopow (k + 1)) ht hcol1
  exact periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree T P hP hper m t k ht hlcol1 hw

/-- **Converse Derivation of `WinWittAgree` from `RhColAgree · 1` and `RhBandAgree` (`periodic_winWittAgree_of_rhColAgree_one_and_rhBandAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t`, if `RhColAgree t (m * P) 1 (2^(k+1))` and `RhBandAgree t (m * P) 0 (2^k)` hold, then `WinWittAgree t k (m * P) (t + 2^k) (2^k)` holds! -/
theorem periodic_winWittAgree_of_rhColAgree_one_and_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t)
    (hcol1 : RhColAgree t (m * P) 1 (twopow (k + 1)))
    (hrh : RhBandAgree t (m * P) 0 (twopow k)) :
    WinWittAgree t k (m * P) (t + twopow k) (twopow k) := by
  have hlcol1 := periodic_lhColAgree_one_of_rhColAgree_one T P hP hper m t (twopow (k + 1)) ht hcol1
  exact periodic_winWittAgree_of_lhColAgree_one_and_rhBandAgree T P hP hper m t k ht hlcol1 hrh

/-- **Fully Unconditional `2^k`-Scale Inward Step of `lhCenter` (`lhCenter_scale_inward_step_uncond`)**:
    for ALL `t, k, p : Nat`, solving `lhCenter_scale_step_uncond` for the inner column `lhCenter t p` expresses it in terms of `lhCenter (t + 2^k) (p + 2^k)`, `lhCenter t (p + 2^k)`, `lhCenter t (p + 2^(k+1))`, and `(winWitt t (2^k)).testBit (t + p + 2^(k+1))`! -/
theorem lhCenter_scale_inward_step_uncond (t k p : Nat) :
    lhCenter t p =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t (p + twopow k)))
          (lhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) := by
  rw [lhCenter_scale_step_uncond t k p]
  simp only [bxor_eq_xor]
  cases lhCenter t p <;>
    cases lhCenter t (p + twopow k) <;>
    cases lhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem lhCenter_scale_inward_step_uncond_prop (t k p : Nat) :
    lhCenter t p =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t (p + twopow k)))
          (lhCenter t (p + twopow (k + 1))))
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) :=
  lhCenter_scale_inward_step_uncond t k p

/-- **Unconditional `2^k`-Scale Inward Band Transport of `LhBandAgree` (`lhBandAgree_scale_inward_step_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if `LhBandAgree (t + 2^k) Q (p0 + 2^k) L`, `LhBandAgree t Q (p0 + 2^k) L`, `LhBandAgree t Q (p0 + 2^(k+1)) L`, and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` hold, then `LhBandAgree t Q p0 L` holds! -/
theorem lhBandAgree_scale_inward_step_uncond (t k Q p0 L : Nat)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h1 : LhBandAgree t Q (p0 + twopow k) L)
    (h2 : LhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree t Q p0 L := by
  intro i hi
  have hsQ := lhCenter_scale_inward_step_uncond (t + Q) k (p0 + i)
  have hs0 := lhCenter_scale_inward_step_uncond t k (p0 + i)
  have hbl := hlate i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [hsQ, hs0, hbl,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    show (t + Q) + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i + Q by omega,
    show t + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i by omega,
    hb1, hb2, hwi]

/-- **Unconditional `WinWittAgree` At and Outside the Left Light Cone (`winWittAgree_outside_left_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q ≤ p0`, `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` holds unconditionally by `winWitt_testBit_ge_left_edge`! -/
theorem winWittAgree_outside_left_cone (t k Q p0 L : Nat) (hp : t + Q ≤ p0) :
    WinWittAgree t k Q (t + p0 + twopow (k + 1)) L := by
  intro i _
  rw [show (t + p0 + twopow (k + 1)) + i + Q = (t + Q) + (p0 + i) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + i = t + (p0 + i) + twopow (k + 1) by omega,
    winWitt_testBit_ge_left_edge (t + Q) k (p0 + i) (by omega),
    winWitt_testBit_ge_left_edge t k (p0 + i) (by omega)]

/-! ### Batch 9: Complete `2^k`-Scale 5-Term Left-Half Calculus, Outer `$2^k$`-Strip 3-Term Collapse, and Left-Half Frobenius Defect Vanishing -/

/-- **Unconditional Identity Between `rdiag (t + p) t` and `lhCenter t p` (`rdiag_add_eq_lhCenter_uncond`)**:
    for ALL `t, p : Nat` (no light-cone bound `p ≤ t` required), `rdiag (t + p) t = lhCenter t p`! -/
theorem rdiag_add_eq_lhCenter_uncond (t p : Nat) :
    rdiag (t + p) t = lhCenter t p := by
  rw [lhCenter_eq_row_testBit_uncond t p, row_testBit t (t + p)]

theorem rdiag_add_eq_lhCenter_uncond_prop (t p : Nat) :
    rdiag (t + p) t = lhCenter t p :=
  rdiag_add_eq_lhCenter_uncond t p

/-- **Unconditional `2^k`-Scale Readout of `winWitt` in `lhCenter` Coordinates (`winWitt_testBit_eq_lhCenter_scale_uncond`)**:
    for ALL `t, k, p : Nat`, solving `lhCenter_scale_step_uncond` for `(winWitt t (2^k)).testBit (t + p + 2^(k+1))` expresses it as the 4-term XOR of `lhCenter (t + 2^k) (p + 2^k)`, `lhCenter t p`, `lhCenter t (p + 2^k)`, and `lhCenter t (p + 2^(k+1))`! -/
theorem winWitt_testBit_eq_lhCenter_scale_uncond (t k p : Nat) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p))
          (lhCenter t (p + twopow k)))
        (lhCenter t (p + twopow (k + 1))) := by
  rw [lhCenter_scale_step_uncond t k p]
  simp only [bxor_eq_xor]
  cases lhCenter t p <;>
    cases lhCenter t (p + twopow k) <;>
    cases lhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem winWitt_testBit_eq_lhCenter_scale_uncond_prop (t k p : Nat) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p))
          (lhCenter t (p + twopow k)))
        (lhCenter t (p + twopow (k + 1))) :=
  winWitt_testBit_eq_lhCenter_scale_uncond t k p

/-- **Unconditional `2^k`-Scale Band Derivation of `WinWittAgree` from Four `LhBandAgree` Bands (`winWittAgree_of_lhBandAgree_scale_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if `LhBandAgree (t + 2^k) Q (p0 + 2^k) L`, `LhBandAgree t Q p0 L`, `LhBandAgree t Q (p0 + 2^k) L`, and `LhBandAgree t Q (p0 + 2^(k+1)) L` hold, then `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` holds! -/
theorem winWittAgree_of_lhBandAgree_scale_uncond (t k Q p0 L : Nat)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h0 : LhBandAgree t Q p0 L)
    (h1 : LhBandAgree t Q (p0 + twopow k) L)
    (h2 : LhBandAgree t Q (p0 + twopow (k + 1)) L) :
    WinWittAgree t k Q (t + p0 + twopow (k + 1)) L := by
  intro i hi
  have hsQ := winWitt_testBit_eq_lhCenter_scale_uncond (t + Q) k (p0 + i)
  have hs0 := winWitt_testBit_eq_lhCenter_scale_uncond t k (p0 + i)
  have hbl := hlate i hi
  have hb0 := h0 i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [show (t + p0 + twopow (k + 1)) + i + Q = (t + Q) + (p0 + i) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + i = t + (p0 + i) + twopow (k + 1) by omega,
    hsQ, hs0, hbl, hb0,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    hb1, hb2]

/-- **Fully Unconditional `2^k`-Scale Middle-Column Step of `lhCenter` (`lhCenter_scale_mid_step_uncond`)**:
    for ALL `t, k, p : Nat`, solving `lhCenter_scale_step_uncond` for the middle column `lhCenter t (p + 2^k)` expresses it in terms of `lhCenter (t + 2^k) (p + 2^k)`, `lhCenter t p`, `lhCenter t (p + 2^(k+1))`, and `(winWitt t (2^k)).testBit (t + p + 2^(k+1))`! -/
theorem lhCenter_scale_mid_step_uncond (t k p : Nat) :
    lhCenter t (p + twopow k) =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p))
          (lhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) := by
  rw [lhCenter_scale_step_uncond t k p]
  simp only [bxor_eq_xor]
  cases lhCenter t p <;>
    cases lhCenter t (p + twopow k) <;>
    cases lhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem lhCenter_scale_mid_step_uncond_prop (t k p : Nat) :
    lhCenter t (p + twopow k) =
      bxor
        (bxor (bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p))
          (lhCenter t (p + twopow (k + 1))))
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) :=
  lhCenter_scale_mid_step_uncond t k p

/-- **Unconditional `2^k`-Scale Middle-Band Transport of `LhBandAgree` (`lhBandAgree_scale_mid_step_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if `LhBandAgree (t + 2^k) Q (p0 + 2^k) L`, `LhBandAgree t Q p0 L`, `LhBandAgree t Q (p0 + 2^(k+1)) L`, and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` hold, then `LhBandAgree t Q (p0 + 2^k) L` holds! -/
theorem lhBandAgree_scale_mid_step_uncond (t k Q p0 L : Nat)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h0 : LhBandAgree t Q p0 L)
    (h2 : LhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree t Q (p0 + twopow k) L := by
  intro i hi
  have hsQ := lhCenter_scale_mid_step_uncond (t + Q) k (p0 + i)
  have hs0 := lhCenter_scale_mid_step_uncond t k (p0 + i)
  have hbl := hlate i hi
  have hb0 := h0 i hi
  have hb2 := h2 i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [show (p0 + twopow k) + i = (p0 + i) + twopow k by omega,
    hsQ, hs0, hbl, hb0,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    show (t + Q) + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i + Q by omega,
    show t + (p0 + i) + twopow (k + 1) = (t + p0 + twopow (k + 1)) + i by omega,
    hb2, hwi]

/-- **Outer `$2^k$`-Strip 3-Term Forward Scale Step of `lhCenter` (`lhCenter_scale_step_outer_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k` (the outer `2^k`-strip of the left cone and beyond, valid at ANY time `t`), both `lhCenter t (p + 2^k)` and `lhCenter t (p + 2^(k+1))` lie outside the light cone and vanish, collapsing `lhCenter_scale_step_uncond` to the 3-term law `lhCenter (t + 2^k) (p + 2^k) = lhCenter t p ⊕ (winWitt t (2^k)).testBit (t + p + 2^(k+1))`! -/
theorem lhCenter_scale_step_outer_strip (t k p : Nat) (hp : t < p + twopow k) :
    lhCenter (t + twopow k) (p + twopow k) =
      bxor (lhCenter t p) ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [lhCenter_scale_step_uncond t k p,
    lhCenter_gt_eq_false t (p + twopow k) hp,
    lhCenter_gt_eq_false t (p + twopow (k + 1)) (by omega)]
  cases lhCenter t p <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem lhCenter_scale_step_outer_strip_prop (t k p : Nat) (hp : t < p + twopow k) :
    lhCenter (t + twopow k) (p + twopow k) =
      bxor (lhCenter t p) (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) :=
  lhCenter_scale_step_outer_strip t k p hp

/-- **Outer `$2^k$`-Strip 3-Term Inward Scale Step of `lhCenter` (`lhCenter_scale_inward_outer_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k`, `lhCenter t p = lhCenter (t + 2^k) (p + 2^k) ⊕ (winWitt t (2^k)).testBit (t + p + 2^(k+1))`! -/
theorem lhCenter_scale_inward_outer_strip (t k p : Nat) (hp : t < p + twopow k) :
    lhCenter t p =
      bxor (lhCenter (t + twopow k) (p + twopow k))
        ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) := by
  rw [lhCenter_scale_step_outer_strip t k p hp]
  cases lhCenter t p <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem lhCenter_scale_inward_outer_strip_prop (t k p : Nat) (hp : t < p + twopow k) :
    lhCenter t p =
      bxor (lhCenter (t + twopow k) (p + twopow k))
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) :=
  lhCenter_scale_inward_outer_strip t k p hp

/-- **Outer `$2^k$`-Strip 3-Term Readout of `winWitt` (`winWitt_testBit_outer_left_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k`, `(winWitt t (2^k)).testBit (t + p + 2^(k+1)) = lhCenter (t + 2^k) (p + 2^k) ⊕ lhCenter t p`! -/
theorem winWitt_testBit_outer_left_strip (t k p : Nat) (hp : t < p + twopow k) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) =
      bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p) := by
  rw [lhCenter_scale_step_outer_strip t k p hp]
  cases lhCenter t p <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) <;> rfl

theorem winWitt_testBit_outer_left_strip_prop (t k p : Nat) (hp : t < p + twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) =
      bxor (lhCenter (t + twopow k) (p + twopow k)) (lhCenter t p) :=
  winWitt_testBit_outer_left_strip t k p hp

/-- **Outer `$2^k$`-Strip Left-Diagonal Difference Law for `winWitt` (`winWitt_testBit_outer_left_strip_eq_ldiag_xor`)**:
    for all `t, k, p : Nat` with `p ≤ t` and `t < p + 2^k` (the first `2^k` left diagonals `j = t - p < 2^k` at ANY time `t`), `(winWitt t (2^k)).testBit (t + p + 2^(k+1))` equals the `2^k`-step difference `ldiag (t - p) (t + 2^k) ⊕ ldiag (t - p) t` along left diagonal `t - p`! -/
theorem winWitt_testBit_outer_left_strip_eq_ldiag_xor (t k p : Nat)
    (hpt : p ≤ t) (hp : t < p + twopow k) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) =
      bxor (ldiag (t - p) (t + twopow k)) (ldiag (t - p) t) := by
  rw [winWitt_testBit_outer_left_strip t k p hp,
    lhCenter_eq_ldiag (t + twopow k) (p + twopow k) (by omega),
    lhCenter_eq_ldiag t p hpt,
    show (t + twopow k) - (p + twopow k) = t - p by omega]

theorem winWitt_testBit_outer_left_strip_eq_ldiag_xor_prop (t k p : Nat)
    (hpt : p ≤ t) (hp : t < p + twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) =
      bxor (ldiag (t - p) (t + twopow k)) (ldiag (t - p) t) :=
  winWitt_testBit_outer_left_strip_eq_ldiag_xor t k p hpt hp

/-- **Outer `$2^k$`-Strip Inward Band Transport of `LhBandAgree` (`lhBandAgree_scale_inward_outer_strip`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0 + 2^k`, both outer bands at `p0 + 2^k` and `p0 + 2^(k+1)` hold unconditionally outside the light cone, so `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` alone imply `LhBandAgree t Q p0 L`! -/
theorem lhBandAgree_scale_inward_outer_strip (t k Q p0 L : Nat)
    (hp : t + Q < p0 + twopow k)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree t Q p0 L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  exact lhBandAgree_scale_inward_step_uncond t k Q p0 L hlate
    (lhBandAgree_outside_cone t Q (p0 + twopow k) L hp)
    (lhBandAgree_outside_cone t Q (p0 + twopow (k + 1)) L (by omega))
    hw

/-- **Outer `$2^k$`-Strip Forward Band Transport of `LhBandAgree` (`lhBandAgree_scale_step_outer_strip`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0 + 2^k`, `LhBandAgree t Q p0 L` and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` alone imply `LhBandAgree (t + 2^k) Q (p0 + 2^k) L`! -/
theorem lhBandAgree_scale_step_outer_strip (t k Q p0 L : Nat)
    (hp : t + Q < p0 + twopow k)
    (h0 : LhBandAgree t Q p0 L)
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  exact lhBandAgree_scale_step_uncond t k Q p0 L h0
    (lhBandAgree_outside_cone t Q (p0 + twopow k) L hp)
    (lhBandAgree_outside_cone t Q (p0 + twopow (k + 1)) L (by omega))
    hw

/-- **Outer `$2^k$`-Strip Band Derivation of `WinWittAgree` (`winWittAgree_outer_left_strip`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0 + 2^k`, `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` and `LhBandAgree t Q p0 L` alone imply `WinWittAgree t k Q (t + p0 + 2^(k+1)) L`! -/
theorem winWittAgree_outer_left_strip (t k Q p0 L : Nat)
    (hp : t + Q < p0 + twopow k)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h0 : LhBandAgree t Q p0 L) :
    WinWittAgree t k Q (t + p0 + twopow (k + 1)) L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  exact winWittAgree_of_lhBandAgree_scale_uncond t k Q p0 L hlate h0
    (lhBandAgree_outside_cone t Q (p0 + twopow k) L hp)
    (lhBandAgree_outside_cone t Q (p0 + twopow (k + 1)) L (by omega))

/-- **Mutual Incompatibility of `LhBandAgree (t + 2^k) Q (2^k) L` and `WinWittAgree t k Q (t + 2^(k+1)) L` Inside Scale `2^k` (`not_lhBandAgree_and_winWittAgree_of_lt_twopow`)**:
    for any `t, k, Q, L : Nat` with `0 < Q`, `t + Q ≤ L`, and `t + Q < 2^k`, `LhBandAgree (t + 2^k) Q (2^k) L` and `WinWittAgree t k Q (t + 2^(k+1)) L` cannot both hold, since their conjunction forces `LhBandAgree t Q 0 L` via `lhBandAgree_scale_inward_outer_strip`, contradicting `not_lhBandAgree_of_lt_add`! -/
theorem not_lhBandAgree_and_winWittAgree_of_lt_twopow (t k Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) (hk : t + Q < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k) L) :
    ¬ WinWittAgree t k Q (t + twopow (k + 1)) L := by
  intro hw
  have hlate' : LhBandAgree (t + twopow k) Q (0 + twopow k) L := by
    simpa [Nat.zero_add] using hlate
  have hw' : WinWittAgree t k Q (t + 0 + twopow (k + 1)) L := by
    simpa [Nat.add_zero] using hw
  have h0 := lhBandAgree_scale_inward_outer_strip t k Q 0 L (by omega) hlate' hw'
  exact not_lhBandAgree_of_lt_add t Q L hQ hL h0

/-- **Unconditional Bit Readout of `frobDefect k (row t)` in `lhCenter` Coordinates (`frobDefect_row_testBit_lhCenter_uncond`)**:
    for ALL `t, k, p : Nat` (no light-cone bound required!), bit `(t + p + 1) + 2^(k+1)` of `frobDefect k (row t)` is the 3-term sum of pairwise products of `lhCenter t` cells at distances `2^k` and `2^(k+1)` apart! -/
theorem frobDefect_row_testBit_lhCenter_uncond (t k p : Nat) :
    (frobDefect k (row t)).testBit ((t + p + 1) + twopow (k + 1)) =
      bxor (bxor
        (lhCenter t ((p + 1) + twopow (k + 1)) &&
          bxor (lhCenter t (p + twopow k)) (lhCenter t p))
        (lhCenter t ((p + 1) + twopow k) &&
          bxor (lhCenter t (p + twopow (k + 1))) (lhCenter t p)))
        (lhCenter t (p + 1) &&
          bxor (lhCenter t (p + twopow (k + 1))) (lhCenter t (p + twopow k))) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hf := frobDefect_row_testBit_outside_cone t k (t + p + twopow k) (by omega)
  rw [show ((t + p + twopow k) + 1) + twopow k = (t + p + 1) + twopow (k + 1) by omega] at hf
  rw [hf,
    show (t + p + 1) + twopow (k + 1) = t + ((p + 1) + twopow (k + 1)) by omega,
    show ((t + p + twopow k) + 1) - twopow k = t + (p + 1) by omega,
    show (t + p + twopow k) + twopow k = t + (p + twopow (k + 1)) by omega,
    show (t + p + twopow k) + 1 = t + ((p + 1) + twopow k) by omega,
    show (t + p + twopow k) - twopow k = t + p by omega,
    show t + p + twopow k = t + (p + twopow k) by omega,
    rdiag_add_eq_lhCenter_uncond t ((p + 1) + twopow (k + 1)),
    rdiag_add_eq_lhCenter_uncond t (p + twopow k),
    rdiag_add_eq_lhCenter_uncond t p,
    rdiag_add_eq_lhCenter_uncond t ((p + 1) + twopow k),
    rdiag_add_eq_lhCenter_uncond t (p + twopow (k + 1)),
    rdiag_add_eq_lhCenter_uncond t (p + 1)]

theorem frobDefect_row_testBit_lhCenter_uncond_prop (t k p : Nat) :
    wittBitBool (frobDefect k (row t)) ((t + p + 1) + twopow (k + 1)) =
      bxor (bxor
        (lhCenter t ((p + 1) + twopow (k + 1)) &&
          bxor (lhCenter t (p + twopow k)) (lhCenter t p))
        (lhCenter t ((p + 1) + twopow k) &&
          bxor (lhCenter t (p + twopow (k + 1))) (lhCenter t p)))
        (lhCenter t (p + 1) &&
          bxor (lhCenter t (p + twopow (k + 1))) (lhCenter t (p + twopow k))) :=
  frobDefect_row_testBit_lhCenter_uncond t k p

/-- **Vanishing of `frobDefect k (row t)` Across the Outer `$2^k$`-Strip of the Left Cone (`frobDefect_row_testBit_lhCenter_outer_strip_eq_false`)**:
    for all `t, k, p : Nat` with `t < p + 2^k` (valid at ANY time `t`, even `t ≫ 2^k`!), all four shifted `lhCenter t` cells at `+ 2^k` and `+ 2^(k+1)` lie outside the left light cone and vanish, so `(frobDefect k (row t)).testBit ((t + p + 1) + 2^(k+1)) = false`! -/
theorem frobDefect_row_testBit_lhCenter_outer_strip_eq_false (t k p : Nat)
    (hp : t < p + twopow k) :
    (frobDefect k (row t)).testBit ((t + p + 1) + twopow (k + 1)) = false := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [frobDefect_row_testBit_lhCenter_uncond t k p,
    lhCenter_gt_eq_false t ((p + 1) + twopow (k + 1)) (by omega),
    lhCenter_gt_eq_false t ((p + 1) + twopow k) (by omega),
    lhCenter_gt_eq_false t (p + twopow (k + 1)) (by omega),
    lhCenter_gt_eq_false t (p + twopow k) hp]
  cases lhCenter t (p + 1) <;> cases lhCenter t p <;> rfl

theorem frobDefect_row_testBit_lhCenter_outer_strip_eq_false_prop (t k p : Nat)
    (hp : t < p + twopow k) :
    wittBitBool (frobDefect k (row t)) ((t + p + 1) + twopow (k + 1)) = false :=
  frobDefect_row_testBit_lhCenter_outer_strip_eq_false t k p hp

/-! ### Batch 10: Single-Sector Window Evolution in the Outer `$2^k$`-Strip and Outer Cross-Center `$2^k$`-Scale Duality -/

/-- **Unconditional Bit Readout of `phiScale k (row t)` in `lhCenter` Coordinates (`phiScale_row_testBit_lhCenter_uncond`)**:
    for ALL `t, k, p : Nat` (no light-cone bound required!), bit `t + p + 2^(k+1)` of `phiScale k (row t)` is the 3-term XOR of `lhCenter t (p + 2^(k+1))`, `lhCenter t (p + 2^k)`, and `lhCenter t p`! -/
theorem phiScale_row_testBit_lhCenter_uncond (t k p : Nat) :
    (phiScale k (row t)).testBit (t + p + twopow (k + 1)) =
      bxor (bxor (lhCenter t (p + twopow (k + 1))) (lhCenter t (p + twopow k))) (lhCenter t p) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hp := phiScale_row_testBit_outside_cone t k (t + p + twopow k) (by omega)
  rw [show (t + p + twopow k) + twopow k = t + p + twopow (k + 1) by omega] at hp
  rw [hp,
    show t + p + twopow (k + 1) = t + (p + twopow (k + 1)) by omega,
    show (t + p + twopow k) - twopow k = t + p by omega,
    show t + p + twopow k = t + (p + twopow k) by omega,
    rdiag_add_eq_lhCenter_uncond t (p + twopow (k + 1)),
    rdiag_add_eq_lhCenter_uncond t (p + twopow k),
    rdiag_add_eq_lhCenter_uncond t p]

theorem phiScale_row_testBit_lhCenter_uncond_prop (t k p : Nat) :
    wittBitBool (phiScale k (row t)) (t + p + twopow (k + 1)) =
      bxor (bxor (lhCenter t (p + twopow (k + 1))) (lhCenter t (p + twopow k))) (lhCenter t p) :=
  phiScale_row_testBit_lhCenter_uncond t k p

/-- **Single-Cell Collapse of `phiScale k (row t)` Across the Outer `$2^k$`-Strip of the Left Cone (`phiScale_row_testBit_lhCenter_outer_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k` (valid at ANY time `t`), both `lhCenter t (p + 2^(k+1))` and `lhCenter t (p + 2^k)` vanish, so `(phiScale k (row t)).testBit (t + p + 2^(k+1)) = lhCenter t p`! -/
theorem phiScale_row_testBit_lhCenter_outer_strip (t k p : Nat)
    (hp : t < p + twopow k) :
    (phiScale k (row t)).testBit (t + p + twopow (k + 1)) = lhCenter t p := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [phiScale_row_testBit_lhCenter_uncond t k p,
    lhCenter_gt_eq_false t (p + twopow (k + 1)) (by omega),
    lhCenter_gt_eq_false t (p + twopow k) hp]
  cases lhCenter t p <;> rfl

theorem phiScale_row_testBit_lhCenter_outer_strip_prop (t k p : Nat)
    (hp : t < p + twopow k) :
    wittBitBool (phiScale k (row t)) (t + p + twopow (k + 1)) = lhCenter t p :=
  phiScale_row_testBit_lhCenter_outer_strip t k p hp

/-- **Single-Sector Collapse of `crossCarry (phiScale k (row t)) (winWitt t (2^k))` Across the Outer `$2^k$`-Strip (`crossCarry_row_scale_lhCenter_outer_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k`, at bit `(t + p + 1) + 2^(k+1)`, `phiScale k (row t)` reads only `lhCenter t (p + 1)` and `lhCenter t p`, collapsing the cross-carry to a pure single-sector bilinear pairing! -/
theorem crossCarry_row_scale_lhCenter_outer_strip (t k p : Nat)
    (hp : t < p + twopow k) :
    (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit ((t + p + 1) + twopow (k + 1)) =
      bxor
        (lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)))
        ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) && lhCenter t p) := by
  have hc := crossCarry_testBit_succ (phiScale k (row t)) (winWitt t (twopow k)) (t + p + twopow (k + 1))
  rw [show (t + p + twopow (k + 1)) + 1 = (t + p + 1) + twopow (k + 1) by omega] at hc
  rw [hc,
    show (t + p + 1) + twopow (k + 1) = t + (p + 1) + twopow (k + 1) by omega,
    phiScale_row_testBit_lhCenter_outer_strip t k (p + 1) (by omega),
    phiScale_row_testBit_lhCenter_outer_strip t k p hp]

theorem crossCarry_row_scale_lhCenter_outer_strip_prop (t k p : Nat)
    (hp : t < p + twopow k) :
    wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k))) ((t + p + 1) + twopow (k + 1)) =
      bxor
        (lhCenter t (p + 1) && wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)))
        (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow (k + 1)) && lhCenter t p) :=
  crossCarry_row_scale_lhCenter_outer_strip t k p hp

/-- **Single-Sector Window Step Law Across the Outer `$2^k$`-Strip of the Left Cone (`winWitt_step_outer_left_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k` (valid at ANY time `t`), because `frobDefect k (row t)` vanishes (`frobDefect_row_testBit_lhCenter_outer_strip_eq_false`) and `phiScale k (row t)` collapses to `lhCenter t`, the universal window step `winWitt_step_frobDefect_testBit_succ` depends ONLY on `lhCenter t p`, `lhCenter t (p + 1)` and `winWitt t (2^k)`! -/
theorem winWitt_step_outer_left_strip (t k p : Nat)
    (hp : t < p + twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p + 1) + twopow (k + 1)) =
      bxor
        ((phi (winWitt t (twopow k))).testBit ((t + 1) + (p + 1) + twopow (k + 1)))
        (bxor
          (lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)))
          ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) && lhCenter t p)) := by
  have hs := winWitt_step_frobDefect_testBit_succ t k ((t + p + 1) + twopow (k + 1))
  rw [show ((t + p + 1) + twopow (k + 1)) + 1 = (t + 1) + (p + 1) + twopow (k + 1) by omega,
    crossCarry_row_scale_lhCenter_outer_strip t k p hp,
    frobDefect_row_testBit_lhCenter_outer_strip_eq_false t k p hp] at hs
  rw [hs]
  cases (phi (winWitt t (twopow k))).testBit ((t + 1) + (p + 1) + twopow (k + 1)) <;>
    cases (bxor
      (lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)))
      ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) && lhCenter t p)) <;> rfl

theorem winWitt_step_outer_left_strip_prop (t k p : Nat)
    (hp : t < p + twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + (p + 1) + twopow (k + 1)) =
      bxor
        (wittBitBool (phi (winWitt t (twopow k))) ((t + 1) + (p + 1) + twopow (k + 1)))
        (bxor
          (lhCenter t (p + 1) && wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)))
          (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow (k + 1)) && lhCenter t p)) :=
  winWitt_step_outer_left_strip t k p hp

/-- **Single-Sector 1-Step Forward Propagation of `WinWittAgree` in the Outer `$2^k$`-Strip (`winWittAgree_step_outer_left_strip`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0 + 2^k`, if `LhBandAgree t Q p0 (L + 1)` and `WinWittAgree t k Q (t + p0 + 2^(k+1)) (L + 2)` hold at time `t` alone (requiring ONLY the single inner `LhBandAgree` band at `p0`, and NO `LhBandAgree` hypotheses at `p0 + 2^k`, `p0 + 2^(k+1)`, or `t + 2^k`!), then `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^(k+1)) L` holds at time `t + 1`! -/
theorem winWittAgree_step_outer_left_strip (t k Q p0 L : Nat)
    (hp : t + Q < p0 + twopow k)
    (h0 : LhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) (L + 2)) :
    WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow (k + 1)) L := by
  intro i hi
  have hsQ := winWitt_step_outer_left_strip (t + Q) k (p0 + i) (by omega)
  have hs0 := winWitt_step_outer_left_strip t k (p0 + i) (by omega)
  have hb0 := h0 i (by omega)
  have hb1 := h0 (i + 1) (by omega)
  have hw0 := hw i (by omega)
  have hw1 := hw (i + 1) (by omega)
  have hw2 := hw (i + 2) (by omega)
  rw [show p0 + (i + 1) = (p0 + i) + 1 by omega] at hb1
  rw [show (t + p0 + twopow (k + 1)) + i + Q = (t + Q) + (p0 + i) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + i = t + (p0 + i) + twopow (k + 1) by omega] at hw0
  rw [show (t + p0 + twopow (k + 1)) + (i + 1) + Q = (t + Q) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + (i + 1) = t + ((p0 + i) + 1) + twopow (k + 1) by omega] at hw1
  rw [show (t + p0 + twopow (k + 1)) + (i + 2) + Q = ((t + Q) + (p0 + i) + twopow (k + 1)) + 2 by omega,
    show (t + p0 + twopow (k + 1)) + (i + 2) = (t + (p0 + i) + twopow (k + 1)) + 2 by omega] at hw2
  have hphiQ : (phi (winWitt (t + Q) (twopow k))).testBit (((t + Q) + 1) + ((p0 + i) + 1) + twopow (k + 1)) =
      bxor ((winWitt (t + Q) (twopow k)).testBit (((t + Q) + (p0 + i) + twopow (k + 1)) + 2))
        ((winWitt (t + Q) (twopow k)).testBit ((t + Q) + ((p0 + i) + 1) + twopow (k + 1)) ||
          (winWitt (t + Q) (twopow k)).testBit ((t + Q) + (p0 + i) + twopow (k + 1))) := by
    have hp0 := phi_testBit_add_two (winWitt (t + Q) (twopow k)) ((t + Q) + (p0 + i) + twopow (k + 1))
    rw [show (((t + Q) + 1) + ((p0 + i) + 1) + twopow (k + 1)) =
        ((t + Q) + (p0 + i) + twopow (k + 1)) + 2 by omega,
      hp0,
      show ((t + Q) + (p0 + i) + twopow (k + 1)) + 1 = (t + Q) + ((p0 + i) + 1) + twopow (k + 1) by omega,
      bxor_eq_xor]
  have hphi0 : (phi (winWitt t (twopow k))).testBit ((t + 1) + ((p0 + i) + 1) + twopow (k + 1)) =
      bxor ((winWitt t (twopow k)).testBit ((t + (p0 + i) + twopow (k + 1)) + 2))
        ((winWitt t (twopow k)).testBit (t + ((p0 + i) + 1) + twopow (k + 1)) ||
          (winWitt t (twopow k)).testBit (t + (p0 + i) + twopow (k + 1))) := by
    have hp0 := phi_testBit_add_two (winWitt t (twopow k)) (t + (p0 + i) + twopow (k + 1))
    rw [show ((t + 1) + ((p0 + i) + 1) + twopow (k + 1)) =
        (t + (p0 + i) + twopow (k + 1)) + 2 by omega,
      hp0,
      show (t + (p0 + i) + twopow (k + 1)) + 1 = t + ((p0 + i) + 1) + twopow (k + 1) by omega,
      bxor_eq_xor]
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i + Q =
      ((t + Q) + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i =
      (t + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    hsQ, hs0, hphiQ, hphi0, hb0, hb1, hw0, hw1, hw2]

/-- **Multi-Step Single-Sector Forward Propagation of `WinWittAgree` in the Outer `$2^k$`-Strip (`winWittAgree_steps_outer_left_strip`)**:
    by induction on `s : Nat`, for all `t, k, Q, p0, L, s : Nat` with `t + Q < p0 + 2^k`, if `LhBandAgree t Q p0 (L + 2 * s)` and `WinWittAgree t k Q (t + p0 + 2^(k+1)) (L + 2 * s)` hold at time `t` alone, then `WinWittAgree (t + s) k Q ((t + s) + (p0 + s) + 2^(k+1)) L` holds at time `t + s`! -/
theorem winWittAgree_steps_outer_left_strip (t k Q p0 L s : Nat)
    (hp : t + Q < p0 + twopow k)
    (h0 : LhBandAgree t Q p0 (L + 2 * s))
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) (L + 2 * s)) :
    WinWittAgree (t + s) k Q ((t + s) + (p0 + s) + twopow (k + 1)) L := by
  induction s generalizing t p0 L with
  | zero =>
    simpa using hw
  | succ s ih =>
    have h0_step : LhBandAgree t Q p0 ((L + 2 * s) + 2) := by
      intro i hi; exact h0 i (by omega)
    have h0_sub : LhBandAgree t Q p0 ((L + 2 * s) + 1) := by
      intro i hi; exact h0 i (by omega)
    have hw_step : WinWittAgree t k Q (t + p0 + twopow (k + 1)) ((L + 2 * s) + 2) := by
      intro i hi; exact hw i (by omega)
    have h0_next := lhBandAgree_step t Q p0 (L + 2 * s) h0_step
    have hw_next := winWittAgree_step_outer_left_strip t k Q p0 (L + 2 * s) hp h0_sub hw_step
    have h_ih := ih (t + 1) (p0 + 1) L (by omega) h0_next hw_next
    rw [show (t + 1) + s = t + (s + 1) by omega,
      show (p0 + 1) + s = p0 + (s + 1) by omega] at h_ih
    exact h_ih

/-- **Outward Spatial Step of `winWitt` Across the Outer `$2^k$`-Strip of the Left Cone (`winWitt_outward_step_outer_left_strip`)**:
    for all `t, k, p : Nat` with `t < p + 2^k`, solving `winWitt_step_outer_left_strip` for the outer window bit `(winWitt t (2^k)).testBit (t + (p + 2) + 2^(k+1))` expresses it in terms of `(winWitt (t + 1) (2^k)).testBit ((t + 1) + (p + 1) + 2^(k+1))`, the two inner window bits at `p + 1` and `p`, and `lhCenter t (p + 1)`, `lhCenter t p`! -/
theorem winWitt_outward_step_outer_left_strip (t k p : Nat)
    (hp : t < p + twopow k) :
    (winWitt t (twopow k)).testBit (t + (p + 2) + twopow (k + 1)) =
      bxor
        (bxor
          ((winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p + 1) + twopow (k + 1)))
          ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) ||
            (winWitt t (twopow k)).testBit (t + p + twopow (k + 1))))
        (bxor
          (lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)))
          ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) && lhCenter t p)) := by
  have hs := winWitt_step_outer_left_strip t k p hp
  have hphi := phi_testBit_add_two (winWitt t (twopow k)) (t + p + twopow (k + 1))
  rw [show (t + 1) + (p + 1) + twopow (k + 1) = (t + p + twopow (k + 1)) + 2 by omega,
    hphi,
    show (t + p + twopow (k + 1)) + 2 = t + (p + 2) + twopow (k + 1) by omega,
    show (t + p + twopow (k + 1)) + 1 = t + (p + 1) + twopow (k + 1) by omega] at hs
  rw [show (t + 1) + (p + 1) + twopow (k + 1) = t + (p + 2) + twopow (k + 1) by omega, hs]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit (t + (p + 2) + twopow (k + 1)) <;>
    cases ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) ||
      (winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) <;>
    cases ((lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) ^^
      ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)) && lhCenter t p)) <;> rfl

theorem winWitt_outward_step_outer_left_strip_prop (t k p : Nat)
    (hp : t < p + twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + (p + 2) + twopow (k + 1)) =
      bxor
        (bxor
          (wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + (p + 1) + twopow (k + 1)))
          (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow (k + 1)) ||
            wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))))
        (bxor
          (lhCenter t (p + 1) && wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)))
          (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow (k + 1)) && lhCenter t p)) :=
  winWitt_outward_step_outer_left_strip t k p hp

/-- **Single-Sector 1-Cell Outward Spatial Extension of `WinWittAgree` in the Outer `$2^k$`-Strip (`winWittAgree_extend_outer_left_strip`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0 + 2^k`, if `LhBandAgree t Q p0 (L + 1)` and `WinWittAgree t k Q (t + p0 + 2^(k+1)) (L + 1)` hold at time `t`, and bit `(t + 1) + (p0 + L + 1) + 2^(k+1)` of `winWitt (t + 1) (2^k)` agrees between `t + 1` and `(t + 1) + Q`, then `WinWittAgree t k Q (t + p0 + 2^(k+1)) (L + 2)` holds at time `t`! -/
theorem winWittAgree_extend_outer_left_strip (t k Q p0 L : Nat)
    (hp : t + Q < p0 + twopow k)
    (h0 : LhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) (L + 1))
    (hstep : (winWitt ((t + 1) + Q) (twopow k)).testBit ((t + 1) + (p0 + L + 1) + twopow (k + 1) + Q) =
      (winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p0 + L + 1) + twopow (k + 1))) :
    WinWittAgree t k Q (t + p0 + twopow (k + 1)) (L + 2) := by
  intro i hi
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · exact hw i (by omega)
  · have hsQ := winWitt_outward_step_outer_left_strip (t + Q) k (p0 + L) (by omega)
    have hs0 := winWitt_outward_step_outer_left_strip t k (p0 + L) (by omega)
    have hb0 := h0 L (by omega)
    have hb1 := h0 (L + 1) (by omega)
    have hw0 := hw L (by omega)
    have hw1 := hw (L + 1) (by omega)
    rw [show p0 + (L + 1) = (p0 + L) + 1 by omega] at hb1
    rw [show (t + p0 + twopow (k + 1)) + L + Q = (t + Q) + (p0 + L) + twopow (k + 1) by omega,
      show (t + p0 + twopow (k + 1)) + L = t + (p0 + L) + twopow (k + 1) by omega] at hw0
    rw [show (t + p0 + twopow (k + 1)) + (L + 1) + Q = (t + Q) + ((p0 + L) + 1) + twopow (k + 1) by omega,
      show (t + p0 + twopow (k + 1)) + (L + 1) = t + ((p0 + L) + 1) + twopow (k + 1) by omega] at hw1
    rw [show (t + 1) + Q = (t + Q) + 1 by omega,
      show (t + 1) + (p0 + L + 1) + twopow (k + 1) + Q =
        ((t + Q) + 1) + ((p0 + L) + 1) + twopow (k + 1) by omega,
      show (t + 1) + (p0 + L + 1) + twopow (k + 1) =
        (t + 1) + ((p0 + L) + 1) + twopow (k + 1) by omega] at hstep
    rw [show (t + p0 + twopow (k + 1)) + (L + 2) + Q =
        (t + Q) + ((p0 + L) + 2) + twopow (k + 1) by omega,
      show (t + p0 + twopow (k + 1)) + (L + 2) =
        t + ((p0 + L) + 2) + twopow (k + 1) by omega,
      hsQ, hs0, hstep, hw0, hw1, hb0, hb1]

/-- **Single-Sector Outward Band Step of `WinWittAgree` in the Outer `$2^k$`-Strip (`winWittAgree_outward_step_outer_left_strip`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0 + 2^k`, if `LhBandAgree t Q p0 (L + 1)`, `WinWittAgree t k Q (t + p0 + 2^(k+1)) (L + 1)`, and `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^(k+1)) L` hold, then `WinWittAgree t k Q (t + (p0 + 2) + 2^(k+1)) L` holds! -/
theorem winWittAgree_outward_step_outer_left_strip (t k Q p0 L : Nat)
    (hp : t + Q < p0 + twopow k)
    (h0 : LhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q (t + p0 + twopow (k + 1)) (L + 1))
    (hnext : WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow (k + 1)) L) :
    WinWittAgree t k Q (t + (p0 + 2) + twopow (k + 1)) L := by
  intro i hi
  have hsQ := winWitt_outward_step_outer_left_strip (t + Q) k (p0 + i) (by omega)
  have hs0 := winWitt_outward_step_outer_left_strip t k (p0 + i) (by omega)
  have hb0 := h0 i (by omega)
  have hb1 := h0 (i + 1) (by omega)
  have hw0 := hw i (by omega)
  have hw1 := hw (i + 1) (by omega)
  have hwn := hnext i hi
  rw [show p0 + (i + 1) = (p0 + i) + 1 by omega] at hb1
  rw [show (t + p0 + twopow (k + 1)) + i + Q = (t + Q) + (p0 + i) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + i = t + (p0 + i) + twopow (k + 1) by omega] at hw0
  rw [show (t + p0 + twopow (k + 1)) + (i + 1) + Q = (t + Q) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    show (t + p0 + twopow (k + 1)) + (i + 1) = t + ((p0 + i) + 1) + twopow (k + 1) by omega] at hw1
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i + Q =
      ((t + Q) + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i =
      (t + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega] at hwn
  rw [show (t + (p0 + 2) + twopow (k + 1)) + i + Q =
      (t + Q) + ((p0 + i) + 2) + twopow (k + 1) by omega,
    show (t + (p0 + 2) + twopow (k + 1)) + i =
      t + ((p0 + i) + 2) + twopow (k + 1) by omega,
    hsQ, hs0, hwn, hw0, hw1, hb0, hb1]

/-- **3-Term Cross-Center `$2^k$`-Scale Duality in the Outer `$2^{k+1}$`-Regime (`rhCenter_eq_lhCenter_scale_cross_outer`)**:
    for all `t, k, r : Nat` with `r ≤ 2^k` and `t + r < 2^(k+1)` (which holds for all `r ≤ 2^k` whenever `t < 2^k`), `lhCenter t (2^(k+1) - r) = false`, so `rhCenter_eq_lhCenter_scale_cross` collapses to the 3-term cross-center law `rhCenter t r = lhCenter (t + 2^k) (2^k - r) ⊕ lhCenter t (2^k - r) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)`! -/
theorem rhCenter_eq_lhCenter_scale_cross_outer (t k r : Nat)
    (hr : r ≤ twopow k) (htr : t + r < twopow (k + 1)) :
    rhCenter t r =
      bxor
        (bxor (lhCenter (t + twopow k) (twopow k - r)) (lhCenter t (twopow k - r)))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)) := by
  rw [rhCenter_eq_lhCenter_scale_cross t k r hr,
    lhCenter_gt_eq_false t (twopow (k + 1) - r) (by omega)]
  cases lhCenter (t + twopow k) (twopow k - r) <;>
    cases lhCenter t (twopow k - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;> rfl

theorem rhCenter_eq_lhCenter_scale_cross_outer_prop (t k r : Nat)
    (hr : r ≤ twopow k) (htr : t + r < twopow (k + 1)) :
    rhCenter t r =
      bxor
        (bxor (lhCenter (t + twopow k) (twopow k - r)) (lhCenter t (twopow k - r)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  rhCenter_eq_lhCenter_scale_cross_outer t k r hr htr

/-- **Outer Cross-Center `$2^k$`-Scale Band Transport to `RhBandAgree` (`rhBandAgree_of_lhBandAgree_scale_cross_outer`)**:
    for all `t, k, Q, L : Nat` with `L ≤ 2^k` and `t + Q + L < 2^(k+1)`, the outer band `LhBandAgree t Q (2^(k+1) - L) L` holds unconditionally outside the light cone, so `LhBandAgree (t + 2^k) Q (2^k - L) L`, `LhBandAgree t Q (2^k - L) L`, and `WinWittAgree t k Q ((t + 2^(k+1)) - L) L` alone imply `RhBandAgree t Q 0 L`! -/
theorem rhBandAgree_of_lhBandAgree_scale_cross_outer (t k Q L : Nat)
    (hL : L ≤ twopow k) (ht : t + Q + L < twopow (k + 1))
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L)
    (h1 : LhBandAgree t Q (twopow k - L) L)
    (hw : WinWittAgree t k Q ((t + twopow (k + 1)) - L) L) :
    RhBandAgree t Q 0 L := by
  exact rhBandAgree_of_lhBandAgree_scale_cross t k Q L hL hlate h1
    (lhBandAgree_outside_cone t Q (twopow (k + 1) - L) L (by omega))
    hw

/-- **Outer Cross-Center `$2^k$`-Scale Band Transport to `WinWittAgree` (`winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross_outer`)**:
    for all `t, k, Q, L : Nat` with `L ≤ 2^k` and `t + Q + L < 2^(k+1)`, `RhBandAgree t Q 0 L`, `LhBandAgree (t + 2^k) Q (2^k - L) L`, and `LhBandAgree t Q (2^k - L) L` alone imply `WinWittAgree t k Q ((t + 2^(k+1)) - L) L`! -/
theorem winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross_outer (t k Q L : Nat)
    (hL : L ≤ twopow k) (ht : t + Q + L < twopow (k + 1))
    (hrh : RhBandAgree t Q 0 L)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L)
    (h1 : LhBandAgree t Q (twopow k - L) L) :
    WinWittAgree t k Q ((t + twopow (k + 1)) - L) L := by
  exact winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross t k Q L hL hrh hlate h1
    (lhBandAgree_outside_cone t Q (twopow (k + 1) - L) L (by omega))

/-- **Half-Horizon Derivation of `RhBandAgree` on `[0, 2^k]` when `t + m * P < 2^k` (`periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree_outer`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t` and `t + m * P < 2^k`, we only need `LhColAgree t (m * P) 1 (2^k)` and `LhColAgree (t + 2^k) (m * P) 1 (2^k)` (each of horizon `2^k` instead of `2^(k+1)`!) together with `WinWittAgree t k (m * P) (t + 2^k) (2^k)` to establish `RhBandAgree t (m * P) 0 (2^k)`! -/
theorem periodic_rhBandAgree_of_lhColAgree_one_and_winWittAgree_outer
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < twopow k)
    (hcol_early : LhColAgree t (m * P) 1 (twopow k))
    (hcol_late : LhColAgree (t + twopow k) (m * P) 1 (twopow k))
    (hw : WinWittAgree t k (m * P) (t + twopow k) (twopow k)) :
    RhBandAgree t (m * P) 0 (twopow k) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h0_early := periodic_lhColAgree_zero T P hP hper m t (twopow k) ht
  have h0_late := periodic_lhColAgree_zero T P hP hper m (t + twopow k) (twopow k) (by omega)
  have hb_early := lhBandAgree_of_outward_determine t (m * P) 0 (twopow k) h0_early hcol_early
  have hb_late := lhBandAgree_of_outward_determine (t + twopow k) (m * P) 0 (twopow k) h0_late hcol_late
  have h1 : LhBandAgree t (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hb_early i (by omega)
  have hlate : LhBandAgree (t + twopow k) (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hb_late i (by omega)
  have hw' : WinWittAgree t k (m * P) ((t + twopow (k + 1)) - twopow k) (twopow k) := by
    rw [show (t + twopow (k + 1)) - twopow k = t + twopow k by omega]
    exact hw
  exact rhBandAgree_of_lhBandAgree_scale_cross_outer t k (m * P) (twopow k)
    (Nat.le_refl _) (by omega) hlate h1 hw'

/-- **Half-Horizon Converse Derivation of `WinWittAgree` when `t + m * P < 2^k` (`periodic_winWittAgree_of_lhColAgree_one_and_rhBandAgree_outer`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t` and `t + m * P < 2^k`, `LhColAgree t (m * P) 1 (2^k)`, `LhColAgree (t + 2^k) (m * P) 1 (2^k)`, and `RhBandAgree t (m * P) 0 (2^k)` imply `WinWittAgree t k (m * P) (t + 2^k) (2^k)`! -/
theorem periodic_winWittAgree_of_lhColAgree_one_and_rhBandAgree_outer
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < twopow k)
    (hcol_early : LhColAgree t (m * P) 1 (twopow k))
    (hcol_late : LhColAgree (t + twopow k) (m * P) 1 (twopow k))
    (hrh : RhBandAgree t (m * P) 0 (twopow k)) :
    WinWittAgree t k (m * P) (t + twopow k) (twopow k) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h0_early := periodic_lhColAgree_zero T P hP hper m t (twopow k) ht
  have h0_late := periodic_lhColAgree_zero T P hP hper m (t + twopow k) (twopow k) (by omega)
  have hb_early := lhBandAgree_of_outward_determine t (m * P) 0 (twopow k) h0_early hcol_early
  have hb_late := lhBandAgree_of_outward_determine (t + twopow k) (m * P) 0 (twopow k) h0_late hcol_late
  have h1 : LhBandAgree t (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hb_early i (by omega)
  have hlate : LhBandAgree (t + twopow k) (m * P) (twopow k - twopow k) (twopow k) := by
    rw [Nat.sub_self]
    intro i hi
    exact hb_late i (by omega)
  have hw := winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross_outer t k (m * P) (twopow k)
    (Nat.le_refl _) (by omega) hrh hlate h1
  rwa [show (t + twopow (k + 1)) - twopow k = t + twopow k by omega] at hw

/-- **2-Term In-Cone Cross-Center `$2^k$`-Scale Duality (`rhCenter_eq_lhCenter_scale_cross_cone`)**:
    for all `t, k, r : Nat` with `t + r < 2^k` (where both `lhCenter t (2^k - r)` and `lhCenter t (2^(k+1) - r)` lie outside the light cone at time `t` and vanish!), `rhCenter_eq_lhCenter_scale_cross` collapses to the 2-term law `rhCenter t r = lhCenter (t + 2^k) (2^k - r) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)`! -/
theorem rhCenter_eq_lhCenter_scale_cross_cone (t k r : Nat)
    (htr : t + r < twopow k) :
    rhCenter t r =
      bxor (lhCenter (t + twopow k) (twopow k - r))
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [rhCenter_eq_lhCenter_scale_cross_outer t k r (by omega) (by omega),
    lhCenter_gt_eq_false t (twopow k - r) (by omega)]
  cases lhCenter (t + twopow k) (twopow k - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;> rfl

theorem rhCenter_eq_lhCenter_scale_cross_cone_prop (t k r : Nat)
    (htr : t + r < twopow k) :
    rhCenter t r =
      bxor (lhCenter (t + twopow k) (twopow k - r))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  rhCenter_eq_lhCenter_scale_cross_cone t k r htr

/-! ### Batch 11: In-Cone Cross-Center Triality, Inter-Cone Zero-Gap Direct Readout of Late `lhCenter`, and Unconditional Left-Half Window Defect Step -/

/-- **2-Term In-Cone Cross-Center Readout of Late `lhCenter` (`lhCenter_scale_cross_cone`)**:
    for all `t, k, r : Nat` with `t + r < 2^k`, solving `rhCenter_eq_lhCenter_scale_cross_cone` for `lhCenter (t + 2^k) (2^k - r)` gives `lhCenter (t + 2^k) (2^k - r) = rhCenter t r ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)`! -/
theorem lhCenter_scale_cross_cone (t k r : Nat)
    (htr : t + r < twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      bxor (rhCenter t r)
        ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)) := by
  rw [rhCenter_eq_lhCenter_scale_cross_cone t k r htr]
  cases lhCenter (t + twopow k) (twopow k - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;> rfl

theorem lhCenter_scale_cross_cone_prop (t k r : Nat)
    (htr : t + r < twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      bxor (rhCenter t r)
        (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  lhCenter_scale_cross_cone t k r htr

/-- **2-Term In-Cone Cross-Center Readout of `winWitt` (`winWitt_testBit_scale_cross_cone`)**:
    for all `t, k, r : Nat` with `t + r < 2^k`, `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = lhCenter (t + 2^k) (2^k - r) ⊕ rhCenter t r`! -/
theorem winWitt_testBit_scale_cross_cone (t k r : Nat)
    (htr : t + r < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      bxor (lhCenter (t + twopow k) (twopow k - r)) (rhCenter t r) := by
  rw [rhCenter_eq_lhCenter_scale_cross_cone t k r htr]
  cases lhCenter (t + twopow k) (twopow k - r) <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) <;> rfl

theorem winWitt_testBit_scale_cross_cone_prop (t k r : Nat)
    (htr : t + r < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      bxor (lhCenter (t + twopow k) (twopow k - r)) (rhCenter t r) :=
  winWitt_testBit_scale_cross_cone t k r htr

/-- **Direct Window Readout in the Inter-Cone Zero Gap (`winWitt_testBit_scale_cross_zero_gap`)**:
    for all `t, k, r : Nat` with `t < r` and `t + r < 2^k` (the inter-cone zero gap between the lower cone `r ≤ t` and the middle cone `t + r ≥ 2^k`), `rhCenter t r = false`, so `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = lhCenter (t + 2^k) (2^k - r)`! -/
theorem winWitt_testBit_scale_cross_zero_gap (t k r : Nat)
    (ht : t < r) (htr : t + r < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      lhCenter (t + twopow k) (twopow k - r) := by
  rw [winWitt_testBit_scale_cross_cone t k r htr,
    rhCenter_gt_eq_false t r ht]
  cases lhCenter (t + twopow k) (twopow k - r) <;> rfl

theorem winWitt_testBit_scale_cross_zero_gap_prop (t k r : Nat)
    (ht : t < r) (htr : t + r < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      lhCenter (t + twopow k) (twopow k - r) :=
  winWitt_testBit_scale_cross_zero_gap t k r ht htr

/-- **Direct Readout of Late `lhCenter (t + 2^k) p` from `winWitt t (2^k)` in the Inter-Cone Zero Gap (`winWitt_testBit_zero_gap_eq_lhCenter_late`)**:
    for all `t, k, p : Nat` with `t < p` and `t + p < 2^k`, all three shifted copies of `row t` in `phiScale k (row t)` vanish at bit `t + p + 2^k`, so `(winWitt t (2^k)).testBit (t + p + 2^k) = lhCenter (t + 2^k) p`! -/
theorem winWitt_testBit_zero_gap_eq_lhCenter_late (t k p : Nat)
    (htp : t < p) (hp : t + p < twopow k) :
    (winWitt t (twopow k)).testBit (t + p + twopow k) =
      lhCenter (t + twopow k) p := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hz := winWitt_testBit_scale_cross_zero_gap t k (twopow k - p) (by omega) (by omega)
  rwa [show (t + twopow (k + 1)) - (twopow k - p) = t + p + twopow k by omega,
    show twopow k - (twopow k - p) = p by omega] at hz

theorem winWitt_testBit_zero_gap_eq_lhCenter_late_prop (t k p : Nat)
    (htp : t < p) (hp : t + p < twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow k) =
      lhCenter (t + twopow k) p :=
  winWitt_testBit_zero_gap_eq_lhCenter_late t k p htp hp

/-- **Deriving Late `LhBandAgree (t + 2^k)` Directly from `WinWittAgree t` in the Inter-Cone Zero Gap (`lhBandAgree_of_winWittAgree_zero_gap`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0` and `t + Q + p0 + L < 2^k`, `WinWittAgree t k Q (t + p0 + 2^k) L` at time `t` directly implies `LhBandAgree (t + 2^k) Q p0 L` at time `t + 2^k` with zero `lhCenter` hypotheses at time `t`! -/
theorem lhBandAgree_of_winWittAgree_zero_gap (t k Q p0 L : Nat)
    (hp0 : t + Q < p0) (hL : t + Q + p0 + L < twopow k)
    (hw : WinWittAgree t k Q (t + p0 + twopow k) L) :
    LhBandAgree (t + twopow k) Q p0 L := by
  intro i hi
  have hwi := hw i hi
  have hzQ := winWitt_testBit_zero_gap_eq_lhCenter_late (t + Q) k (p0 + i) (by omega) (by omega)
  have hz0 := winWitt_testBit_zero_gap_eq_lhCenter_late t k (p0 + i) (by omega) (by omega)
  rw [show (t + p0 + twopow k) + i + Q = (t + Q) + (p0 + i) + twopow k by omega,
    show (t + p0 + twopow k) + i = t + (p0 + i) + twopow k by omega,
    hzQ, hz0] at hwi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega]
  exact hwi

/-- **Deriving `WinWittAgree t` Directly from Late `LhBandAgree (t + 2^k)` in the Inter-Cone Zero Gap (`winWittAgree_of_lhBandAgree_zero_gap`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0` and `t + Q + p0 + L < 2^k`, `LhBandAgree (t + 2^k) Q p0 L` at time `t + 2^k` directly implies `WinWittAgree t k Q (t + p0 + 2^k) L` at time `t`! -/
theorem winWittAgree_of_lhBandAgree_zero_gap (t k Q p0 L : Nat)
    (hp0 : t + Q < p0) (hL : t + Q + p0 + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q p0 L) :
    WinWittAgree t k Q (t + p0 + twopow k) L := by
  intro i hi
  have hbl := hlate i hi
  have hzQ := winWitt_testBit_zero_gap_eq_lhCenter_late (t + Q) k (p0 + i) (by omega) (by omega)
  have hz0 := winWitt_testBit_zero_gap_eq_lhCenter_late t k (p0 + i) (by omega) (by omega)
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hbl
  rw [show (t + p0 + twopow k) + i + Q = (t + Q) + (p0 + i) + twopow k by omega,
    show (t + p0 + twopow k) + i = t + (p0 + i) + twopow k by omega,
    hzQ, hz0, hbl]

/-- **In-Cone Cross-Center Derivation of `RhBandAgree` without Early `LhBandAgree` (`rhBandAgree_of_lhBandAgree_and_winWittAgree_cross_cone`)**:
    for all `t, k, Q, L : Nat` with `t + Q + L < 2^k`, both early `LhBandAgree` bands at `2^k - L` and `2^(k+1) - L` lie outside the light cone at time `t + Q` and hold unconditionally, so `LhBandAgree (t + 2^k) Q (2^k - L) L` and `WinWittAgree t k Q ((t + 2^(k+1)) - L) L` alone imply `RhBandAgree t Q 0 L`! -/
theorem rhBandAgree_of_lhBandAgree_and_winWittAgree_cross_cone (t k Q L : Nat)
    (ht : t + Q + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L)
    (hw : WinWittAgree t k Q ((t + twopow (k + 1)) - L) L) :
    RhBandAgree t Q 0 L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  exact rhBandAgree_of_lhBandAgree_scale_cross_outer t k Q L (by omega) (by omega) hlate
    (lhBandAgree_outside_cone t Q (twopow k - L) L (by omega))
    hw

/-- **In-Cone Cross-Center Derivation of `WinWittAgree` without Early `LhBandAgree` (`winWittAgree_of_rhBandAgree_and_lhBandAgree_cross_cone`)**:
    for all `t, k, Q, L : Nat` with `t + Q + L < 2^k`, `RhBandAgree t Q 0 L` and `LhBandAgree (t + 2^k) Q (2^k - L) L` alone imply `WinWittAgree t k Q ((t + 2^(k+1)) - L) L`! -/
theorem winWittAgree_of_rhBandAgree_and_lhBandAgree_cross_cone (t k Q L : Nat)
    (ht : t + Q + L < twopow k)
    (hrh : RhBandAgree t Q 0 L)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L) :
    WinWittAgree t k Q ((t + twopow (k + 1)) - L) L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  exact winWittAgree_of_rhBandAgree_lhBandAgree_scale_cross_outer t k Q L (by omega) (by omega) hrh hlate
    (lhBandAgree_outside_cone t Q (twopow k - L) L (by omega))

/-- **In-Cone Cross-Center Derivation of Late `LhBandAgree` from `RhBandAgree` and `WinWittAgree` (`lhBandAgree_of_rhBandAgree_and_winWittAgree_cross_cone`)**:
    for all `t, k, Q, L : Nat` with `t + Q + L < 2^k`, `RhBandAgree t Q 0 L` and `WinWittAgree t k Q ((t + 2^(k+1)) - L) L` alone imply `LhBandAgree (t + 2^k) Q (2^k - L) L`! -/
theorem lhBandAgree_of_rhBandAgree_and_winWittAgree_cross_cone (t k Q L : Nat)
    (ht : t + Q + L < twopow k)
    (hrh : RhBandAgree t Q 0 L)
    (hw : WinWittAgree t k Q ((t + twopow (k + 1)) - L) L) :
    LhBandAgree (t + twopow k) Q (twopow k - L) L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  intro i hi
  have hsQ := lhCenter_scale_cross_cone (t + Q) k (L - i) (by omega)
  have hs0 := lhCenter_scale_cross_cone t k (L - i) (by omega)
  have hr := hrh (L - i) (by omega)
  have hwi := hw i hi
  rw [Nat.zero_add] at hr
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (twopow k - L) + i = twopow k - (L - i) by omega,
    hsQ, hs0, hr,
    show ((t + Q) + twopow (k + 1)) - (L - i) = ((t + twopow (k + 1)) - L) + i + Q by omega,
    show (t + twopow (k + 1)) - (L - i) = ((t + twopow (k + 1)) - L) + i by omega,
    hwi]

/-- **Deriving `RhBandAgree` from Late `LhColAgree (t + 2^k)` Alone when `t + m * P + L < 2^k` (`periodic_rhBandAgree_of_lhColAgree_late_and_winWittAgree_cone`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t` and `t + m * P + L < 2^k`, we ONLY need `LhColAgree (t + 2^k) (m * P) 1 (2^k)` at late time `t + 2^k` (and NO `LhColAgree` at early time `t`!) together with `WinWittAgree t k (m * P) ((t + 2^(k+1)) - L) L` to establish `RhBandAgree t (m * P) 0 L`! -/
theorem periodic_rhBandAgree_of_lhColAgree_late_and_winWittAgree_cone
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k L : Nat) (ht : T ≤ t) (htk : t + m * P + L < twopow k)
    (hcol_late : LhColAgree (t + twopow k) (m * P) 1 (twopow k))
    (hw : WinWittAgree t k (m * P) ((t + twopow (k + 1)) - L) L) :
    RhBandAgree t (m * P) 0 L := by
  have h0_late := periodic_lhColAgree_zero T P hP hper m (t + twopow k) (twopow k) (by omega)
  have hb_late := lhBandAgree_of_outward_determine (t + twopow k) (m * P) 0 (twopow k) h0_late hcol_late
  have hlate : LhBandAgree (t + twopow k) (m * P) (twopow k - L) L :=
    lhBandAgree_mono (t + twopow k) (m * P) 0 (twopow k + 1) (twopow k - L) L (by omega) (by omega) hb_late
  exact rhBandAgree_of_lhBandAgree_and_winWittAgree_cross_cone t k (m * P) L htk hlate hw

/-- **Converse Derivation of `WinWittAgree` from Late `LhColAgree (t + 2^k)` and `RhBandAgree` when `t + m * P + L < 2^k` (`periodic_winWittAgree_of_lhColAgree_late_and_rhBandAgree_cone`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t` and `t + m * P + L < 2^k`, `LhColAgree (t + 2^k) (m * P) 1 (2^k)` and `RhBandAgree t (m * P) 0 L` alone imply `WinWittAgree t k (m * P) ((t + 2^(k+1)) - L) L`! -/
theorem periodic_winWittAgree_of_lhColAgree_late_and_rhBandAgree_cone
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k L : Nat) (ht : T ≤ t) (htk : t + m * P + L < twopow k)
    (hcol_late : LhColAgree (t + twopow k) (m * P) 1 (twopow k))
    (hrh : RhBandAgree t (m * P) 0 L) :
    WinWittAgree t k (m * P) ((t + twopow (k + 1)) - L) L := by
  have h0_late := periodic_lhColAgree_zero T P hP hper m (t + twopow k) (twopow k) (by omega)
  have hb_late := lhBandAgree_of_outward_determine (t + twopow k) (m * P) 0 (twopow k) h0_late hcol_late
  have hlate : LhBandAgree (t + twopow k) (m * P) (twopow k - L) L :=
    lhBandAgree_mono (t + twopow k) (m * P) 0 (twopow k + 1) (twopow k - L) L (by omega) (by omega) hb_late
  exact winWittAgree_of_rhBandAgree_and_lhBandAgree_cross_cone t k (m * P) L htk hrh hlate

/-- **1-Step Evolution of Late `lhCenter` in the Outer `$2^k$`-Strip via `winWitt` (`lhCenter_step_outer_strip_from_winWitt`)**:
    for all `t, k, p : Nat` with `t < p + 2^k`, combining `lhCenter_step_succ` at `(t + 2^k, p + 2^k)` with `lhCenter_scale_step_outer_strip` at `p`, `p + 1`, and `p + 2` expresses `lhCenter ((t + 1) + 2^k) ((p + 1) + 2^k)` purely in terms of `lhCenter t` and `winWitt t (2^k)`! -/
theorem lhCenter_step_outer_strip_from_winWitt (t k p : Nat)
    (hp : t < p + twopow k) :
    lhCenter ((t + 1) + twopow k) ((p + 1) + twopow k) =
      bxor
        (bxor (lhCenter t (p + 2)) ((winWitt t (twopow k)).testBit (t + (p + 2) + twopow (k + 1))))
        ((bxor (lhCenter t (p + 1)) ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow (k + 1)))) ||
          (bxor (lhCenter t p) ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))))) := by
  rw [show (t + 1) + twopow k = (t + twopow k) + 1 by omega,
    show (p + 1) + twopow k = (p + twopow k) + 1 by omega,
    lhCenter_step_succ (t + twopow k) (p + twopow k),
    show (p + twopow k) + 2 = (p + 2) + twopow k by omega,
    show (p + twopow k) + 1 = (p + 1) + twopow k by omega,
    lhCenter_scale_step_outer_strip t k (p + 2) (by omega),
    lhCenter_scale_step_outer_strip t k (p + 1) (by omega),
    lhCenter_scale_step_outer_strip t k p hp]

theorem lhCenter_step_outer_strip_from_winWitt_prop (t k p : Nat)
    (hp : t < p + twopow k) :
    lhCenter ((t + 1) + twopow k) ((p + 1) + twopow k) =
      bxor
        (bxor (lhCenter t (p + 2)) (wittBitBool (winWitt t (twopow k)) (t + (p + 2) + twopow (k + 1))))
        ((bxor (lhCenter t (p + 1)) (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow (k + 1)))) ||
          (bxor (lhCenter t p) (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))))) :=
  lhCenter_step_outer_strip_from_winWitt t k p hp

/-- **Unconditional 1-Step Spatiotemporal Difference Law of `winWitt` in `lhCenter` Coordinates (`winWitt_step_lhCenter_defect_uncond`)**:
    for ALL `t, k, p : Nat` (unconditional!), substituting `lhCenter_step_succ` into `winWitt_testBit_eq_lhCenter_scale_uncond (t + 1) k (p + 1)` relates the window bit at `(t + 1, p + 1)` directly to the window bit at `(t, p + 2)` XORed with the four adjacent-column OR-pairs in `lhCenter`! -/
theorem winWitt_step_lhCenter_defect_uncond (t k p : Nat) :
    (winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p + 1) + twopow (k + 1)) =
      bxor
        ((winWitt t (twopow k)).testBit (t + (p + 2) + twopow (k + 1)))
        (bxor
          (bxor
            (bxor
              (lhCenter (t + twopow k) ((p + 1) + twopow k) || lhCenter (t + twopow k) (p + twopow k))
              (lhCenter t (p + 1) || lhCenter t p))
            (lhCenter t ((p + 1) + twopow k) || lhCenter t (p + twopow k)))
          (lhCenter t ((p + 1) + twopow (k + 1)) || lhCenter t (p + twopow (k + 1)))) := by
  rw [winWitt_testBit_eq_lhCenter_scale_uncond (t + 1) k (p + 1),
    winWitt_testBit_eq_lhCenter_scale_uncond t k (p + 2),
    show (t + 1) + twopow k = (t + twopow k) + 1 by omega,
    show (p + 1) + twopow k = (p + twopow k) + 1 by omega,
    show (p + 1) + twopow (k + 1) = (p + twopow (k + 1)) + 1 by omega,
    show (p + 2) + twopow k = (p + twopow k) + 2 by omega,
    show (p + 2) + twopow (k + 1) = (p + twopow (k + 1)) + 2 by omega,
    lhCenter_step_succ (t + twopow k) (p + twopow k),
    lhCenter_step_succ t p,
    lhCenter_step_succ t (p + twopow k),
    lhCenter_step_succ t (p + twopow (k + 1))]
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) ((p + twopow k) + 2) <;>
    cases (lhCenter (t + twopow k) ((p + twopow k) + 1) || lhCenter (t + twopow k) (p + twopow k)) <;>
    cases lhCenter t (p + 2) <;>
    cases (lhCenter t (p + 1) || lhCenter t p) <;>
    cases lhCenter t ((p + twopow k) + 2) <;>
    cases (lhCenter t ((p + twopow k) + 1) || lhCenter t (p + twopow k)) <;>
    cases lhCenter t ((p + twopow (k + 1)) + 2) <;>
    cases (lhCenter t ((p + twopow (k + 1)) + 1) || lhCenter t (p + twopow (k + 1))) <;> rfl

theorem winWitt_step_lhCenter_defect_uncond_prop (t k p : Nat) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + (p + 1) + twopow (k + 1)) =
      bxor
        (wittBitBool (winWitt t (twopow k)) (t + (p + 2) + twopow (k + 1)))
        (bxor
          (bxor
            (bxor
              (lhCenter (t + twopow k) ((p + 1) + twopow k) || lhCenter (t + twopow k) (p + twopow k))
              (lhCenter t (p + 1) || lhCenter t p))
            (lhCenter t ((p + 1) + twopow k) || lhCenter t (p + twopow k)))
          (lhCenter t ((p + 1) + twopow (k + 1)) || lhCenter t (p + twopow (k + 1)))) :=
  winWitt_step_lhCenter_defect_uncond t k p

/-- **Unconditional 1-Step Forward Transport of `WinWittAgree` via Four `LhBandAgree` Bands (`winWittAgree_step_of_lhBandAgree_scale_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if the four `LhBandAgree` bands of width `L + 1` hold at `(t + 2^k, p0 + 2^k)`, `(t, p0)`, `(t, p0 + 2^k)`, and `(t, p0 + 2^(k+1))`, and `WinWittAgree t k Q (t + (p0 + 2) + 2^(k+1)) L` holds at time `t`, then `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^(k+1)) L` holds at time `t + 1`! -/
theorem winWittAgree_step_of_lhBandAgree_scale_uncond (t k Q p0 L : Nat)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) (L + 1))
    (h0 : LhBandAgree t Q p0 (L + 1))
    (h1 : LhBandAgree t Q (p0 + twopow k) (L + 1))
    (h2 : LhBandAgree t Q (p0 + twopow (k + 1)) (L + 1))
    (hw : WinWittAgree t k Q (t + (p0 + 2) + twopow (k + 1)) L) :
    WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow (k + 1)) L := by
  intro i hi
  have hsQ := winWitt_step_lhCenter_defect_uncond (t + Q) k (p0 + i)
  have hs0 := winWitt_step_lhCenter_defect_uncond t k (p0 + i)
  have hbl0 := hlate i (by omega)
  have hbl1 := hlate (i + 1) (by omega)
  have hb00 := h0 i (by omega)
  have hb01 := h0 (i + 1) (by omega)
  have hb10 := h1 i (by omega)
  have hb11 := h1 (i + 1) (by omega)
  have hb20 := h2 i (by omega)
  have hb21 := h2 (i + 1) (by omega)
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl0
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + (i + 1) = ((p0 + i) + 1) + twopow k by omega] at hbl1
  rw [show p0 + (i + 1) = (p0 + i) + 1 by omega] at hb01
  rw [show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hb10
  rw [show (p0 + twopow k) + (i + 1) = ((p0 + i) + 1) + twopow k by omega] at hb11
  rw [show (p0 + twopow (k + 1)) + i = (p0 + i) + twopow (k + 1) by omega] at hb20
  rw [show (p0 + twopow (k + 1)) + (i + 1) = ((p0 + i) + 1) + twopow (k + 1) by omega] at hb21
  rw [show (t + (p0 + 2) + twopow (k + 1)) + i + Q =
      (t + Q) + ((p0 + i) + 2) + twopow (k + 1) by omega,
    show (t + (p0 + 2) + twopow (k + 1)) + i =
      t + ((p0 + i) + 2) + twopow (k + 1) by omega] at hwi
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i + Q =
      ((t + Q) + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i =
      (t + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    hsQ, hs0, hwi, hbl0, hbl1, hb00, hb01, hb10, hb11, hb20, hb21]

/-- **Unconditional 1-Step Outward Transport of `WinWittAgree` via Four `LhBandAgree` Bands (`winWittAgree_outward_of_lhBandAgree_scale_uncond`)**:
    for ALL `t, k, Q, p0, L : Nat`, if the four `LhBandAgree` bands of width `L + 1` hold at `(t + 2^k, p0 + 2^k)`, `(t, p0)`, `(t, p0 + 2^k)`, and `(t, p0 + 2^(k+1))`, and `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^(k+1)) L` holds at time `t + 1`, then `WinWittAgree t k Q (t + (p0 + 2) + 2^(k+1)) L` holds at time `t`! -/
theorem winWittAgree_outward_of_lhBandAgree_scale_uncond (t k Q p0 L : Nat)
    (hlate : LhBandAgree (t + twopow k) Q (p0 + twopow k) (L + 1))
    (h0 : LhBandAgree t Q p0 (L + 1))
    (h1 : LhBandAgree t Q (p0 + twopow k) (L + 1))
    (h2 : LhBandAgree t Q (p0 + twopow (k + 1)) (L + 1))
    (hnext : WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow (k + 1)) L) :
    WinWittAgree t k Q (t + (p0 + 2) + twopow (k + 1)) L := by
  intro i hi
  have hsQ := winWitt_step_lhCenter_defect_uncond (t + Q) k (p0 + i)
  have hs0 := winWitt_step_lhCenter_defect_uncond t k (p0 + i)
  have hbl0 := hlate i (by omega)
  have hbl1 := hlate (i + 1) (by omega)
  have hb00 := h0 i (by omega)
  have hb01 := h0 (i + 1) (by omega)
  have hb10 := h1 i (by omega)
  have hb11 := h1 (i + 1) (by omega)
  have hb20 := h2 i (by omega)
  have hb21 := h2 (i + 1) (by omega)
  have hwn := hnext i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl0
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + (i + 1) = ((p0 + i) + 1) + twopow k by omega] at hbl1
  rw [show p0 + (i + 1) = (p0 + i) + 1 by omega] at hb01
  rw [show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hb10
  rw [show (p0 + twopow k) + (i + 1) = ((p0 + i) + 1) + twopow k by omega] at hb11
  rw [show (p0 + twopow (k + 1)) + i = (p0 + i) + twopow (k + 1) by omega] at hb20
  rw [show (p0 + twopow (k + 1)) + (i + 1) = ((p0 + i) + 1) + twopow (k + 1) by omega] at hb21
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i + Q =
      ((t + Q) + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega,
    show ((t + 1) + (p0 + 1) + twopow (k + 1)) + i =
      (t + 1) + ((p0 + i) + 1) + twopow (k + 1) by omega] at hwn
  rw [hsQ, hs0, hbl0, hbl1, hb00, hb01, hb10, hb11, hb20, hb21] at hwn
  rw [show (t + (p0 + 2) + twopow (k + 1)) + i + Q =
      (t + Q) + ((p0 + i) + 2) + twopow (k + 1) by omega,
    show (t + (p0 + 2) + twopow (k + 1)) + i =
      t + ((p0 + i) + 2) + twopow (k + 1) by omega]
  revert hwn
  simp only [bxor_eq_xor]
  cases (winWitt (t + Q) (twopow k)).testBit ((t + Q) + ((p0 + i) + 2) + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t + ((p0 + i) + 2) + twopow (k + 1)) <;>
    cases ((((lhCenter (t + twopow k) (((p0 + i) + 1) + twopow k) ||
      lhCenter (t + twopow k) ((p0 + i) + twopow k)) ^^
      (lhCenter t ((p0 + i) + 1) || lhCenter t (p0 + i))) ^^
      (lhCenter t (((p0 + i) + 1) + twopow k) || lhCenter t ((p0 + i) + twopow k))) ^^
      (lhCenter t (((p0 + i) + 1) + twopow (k + 1)) || lhCenter t ((p0 + i) + twopow (k + 1)))) <;> decide

end Rule30UOR.Interfaces
