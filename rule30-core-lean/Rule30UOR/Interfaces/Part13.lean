module

public import Rule30UOR.Interfaces.Part12

/-!
# `Rule30UOR.Interfaces`, part 13

* Batch 43: White-Center OR-Agreement Horizon Refutation, White-Column-1 Linearization, and Unconditional Dyadic Scale Laws for `lhCenter`, `response`, `leftresponse`, and `maskparity` (9.937–9.951)
* Batch 44: Dyadic Jump Laws of `lhCenter · 1` vs `leftresponse · k`, Unconditional Outside-the-Cone Dyadic Scale Laws at Zero Diagonals Dropping `z ≤ k`, and `LhBandAgree`-Driven Outside-the-Cone `response`/`maskparity` Laws (9.952–9.966)
* Batch 45: Universal Unconditional Dyadic Coboundaries of `response` and `leftresponse` (Dropping `d ≤ k`), Unconditional Zero-Diagonal and Doubling Dyadic Laws, and Outside-the-Cone `maskparity`/`response` Laws at Zero Diagonals (9.967–9.981)
* Batch 46: `maskcount`/`maskparity`/`leftresponse`/`response` Determination from First-Bit `maskparity · 0` and White-Center Column-`1` Agreement & Unconditional Dyadic Scale-Step Laws Along Settled and Doubling Left Diagonals (9.982–9.996)
* Batch 47: Unconditional Late Dyadic Scale Laws Along Settled & Doubling Left Diagonals Without `d ≤ k` & Dyadic `2^k`-Window Refutations of `CenterPeriodic` at Cone Boundary, Zero-Diagonal, and Doubling Points (9.997–9.1011)
* Batch 48: Strict Exponential Growth `n < 2^n`, `LhColAgree` Dyadic Window Refutations, Direct `2^k - m * P` Cone-Boundary Refutations, and Unconditional Flip-Witness Existence Theorems Over `2^k` Windows Under `CenterPeriodic` Alone (9.1012–9.1026)
* Batch 49: Monotonicity of `twopow`, Unconditional Scale-`k ≥ T + P` Fundamental-Period `P` Flip Witnesses, Two-Zero-Diagonal Flip Witnesses, and Scale-Step `maskparity ⊕ leftresponse` Defect Flip Across Dyadic Doubling Zero Diagonals (9.1027–9.1041)
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

/-! ### Batch 43: White-Center OR-Agreement Horizon Refutation, White-Column-1 Linearization, and Unconditional Dyadic Scale Laws for `lhCenter`, `response`, `leftresponse`, and `maskparity` (9.937–9.951) -/

/-- **Scale-Free Universal-in-`m, P` Refutation of `CenterPeriodic T P` from White-Center-Conditioned OR-Agreement at Any Doubling Zero Diagonal `z = t - (p + 1)` Shrinking the Horizon by `z` (`not_centerPeriodic_of_white_center_rhOrAgree_one_doubles`, 9.937)**:
    for EVERY `T, P, m, t, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `IsZeroDiag (t - (p + 1))`, `DoublesAt (m * P) (t - (p + 1))`, `settle ((t - (p + 1)) + 1) ≤ t`, `settle (t - (p + m * P)) ≤ t`, and `p + 3 * (m * P) ≤ S + 1`, if `center t = false → rhCenter (t + m * P) 1 = rhCenter t 1` at the initial step `t` and `∀ s < S, center (t + (s + 1)) = false → (rhCenter ((t + s) + m * P) 1 || rhCenter ((t + s) + m * P) 2) = (rhCenter (t + s) 1 || rhCenter (t + s) 2)` (requiring OR-agreement ONLY at steps `s` whose next center `center (t + (s + 1)) = false` is white!), then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhOrAgree_one_doubles
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : settle ((t - (p + 1)) + 1) ≤ t)
    (hsetQ : settle (t - (p + m * P)) ≤ t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h0 : Rule30UOR.Core.center t = false → rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : ∀ s : Nat, s < S →
      Rule30UOR.Core.center (t + (s + 1)) = false →
        (rhCenter ((t + s) + m * P) 1 || rhCenter ((t + s) + m * P) 2) =
          (rhCenter (t + s) 1 || rhCenter (t + s) 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  apply not_centerPeriodic_of_white_center_rhCenter_one_doubles
    T P m t p S hP hm ht hz hd hset1 hsetQ hS ?_ hper
  intro s hs hc
  rcases s with _ | s
  · rw [Nat.add_zero] at hc ⊢
    exact h0 hc
  · have hstep := periodic_rhCenter_step_one_eq_of_or_eq
      T P hP hper m (t + s) (by omega) (hor s (by omega) hc)
    rwa [show (t + s) + 1 = t + (s + 1) by omega] at hstep

theorem not_centerPeriodic_of_white_center_rhOrAgree_one_doubles_prop
    (T P m t p S : Nat) (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt (m * P) (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + m * P)) t)
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h0 : Rule30UOR.Core.center t = false → rhCenter (t + m * P) 1 = rhCenter t 1)
    (hor : ∀ s : Nat, s < S →
      Rule30UOR.Core.center (t + (s + 1)) = false →
        (rhCenter ((t + s) + m * P) 1 || rhCenter ((t + s) + m * P) 2) =
          (rhCenter (t + s) 1 || rhCenter (t + s) 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhOrAgree_one_doubles
    T P m t p S hP hm ht hz hd hset1 hsetQ hS h0 hor

/-- **White Column-`1` Linearization Law (`rhCenter_step_one_eq_center_xor_two_of_white_one`, 9.938)**:
    for every `t ∈ ℕ`, whenever `rhCenter t 1 = false`, the boolean OR in `rhCenter (t + 1) 1 = center t ⊕ (rhCenter t 1 || rhCenter t 2)` reduces to `rhCenter t 2`, so `rhCenter (t + 1) 1 = center t ⊕ rhCenter t 2` is purely linear in column `2`! -/
theorem rhCenter_step_one_eq_center_xor_two_of_white_one (t : Nat)
    (hw : rhCenter t 1 = false) :
    rhCenter (t + 1) 1 = bxor (Rule30UOR.Core.center t) (rhCenter t 2) := by
  rw [rhCenter_step_one_eq_center_xor_or t, hw, Bool.false_or]

/-- **1-Step Forward Propagation of Right-Half Column-`1` Agreement Across a White Column-`1` Cell from Column-`2` Agreement (`periodic_rhCenter_step_one_eq_of_white_one_and_two_eq`, 9.939)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `rhCenter (t + m * P) 1 = false`, `rhCenter t 1 = false`, and `rhCenter (t + m * P) 2 = rhCenter t 2`, then `rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1`! -/
theorem periodic_rhCenter_step_one_eq_of_white_one_and_two_eq
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hwQ : rhCenter (t + m * P) 1 = false)
    (hw0 : rhCenter t 1 = false)
    (h2 : rhCenter (t + m * P) 2 = rhCenter t 2) :
    rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1 := by
  rw [show (t + 1) + m * P = (t + m * P) + 1 by omega,
    rhCenter_step_one_eq_center_xor_two_of_white_one (t + m * P) hwQ,
    rhCenter_step_one_eq_center_xor_two_of_white_one t hw0,
    Rule30UOR.Scale.center_mul hper m t ht, h2]

/-- **Unified 1-Step Forward Propagation of Left-Half Column-`-1` Agreement Requiring Column `2` Only When `center (t + 1) = false` and `rhCenter t 1 = false` (`periodic_lhCenter_step_one_eq_of_white_or_black_one`, 9.940)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `rhCenter (t + m * P) 1 = rhCenter t 1` and `(center (t + 1) = false → rhCenter t 1 = false → rhCenter (t + m * P) 2 = rhCenter t 2)`, then `lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1`! -/
theorem periodic_lhCenter_step_one_eq_of_white_or_black_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (h1 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (h2 : Rule30UOR.Core.center (t + 1) = false →
      rhCenter t 1 = false → rhCenter (t + m * P) 2 = rhCenter t 2) :
    lhCenter ((t + 1) + m * P) 1 = lhCenter (t + 1) 1 := by
  apply periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + 1) (by omega)
  intro hc1
  cases hb0 : rhCenter t 1
  · have hbQ : rhCenter (t + m * P) 1 = false := by rw [h1, hb0]
    exact periodic_rhCenter_step_one_eq_of_white_one_and_two_eq
      T P hP hper m t ht hbQ hb0 (h2 hc1 hb0)
  · have hbQ : rhCenter (t + m * P) 1 = true := by rw [h1, hb0]
    exact periodic_rhCenter_step_one_eq_of_black_one T P hP hper m t ht hbQ hb0

/-- **Unconditional Identification of the Dyadic Left Wing `cell t (negpow k)` with `lhCenter t (twopow k)` (`cell_negpow_eq_lhCenter_twopow`, 9.941)**:
    for EVERY `t, k ∈ ℕ` (with NO `2^k ≤ t` cone bound!), `cell t (negpow k) = lhCenter t (twopow k)`! -/
theorem cell_negpow_eq_lhCenter_twopow (t k : Nat) :
    Rule30UOR.Core.cell t (Rule30UOR.Scale.negpow k) = lhCenter t (twopow k) := by
  unfold Rule30UOR.Scale.negpow lhCenter
  rw [Rule30UOR.Scale.cell_eq_kit,
    Rule30UOR.Fixed.Lh_center t (- ((twopow k : Nat) : Int)) (by omega)]

/-- **Unconditional Dyadic Scale Identity at the Center in Terms of `lhCenter` (`scale_center_lhCenter`, 9.942)**:
    for EVERY `t, k ∈ ℕ` (with NO `2^k ≤ t` bound!), `center (t + twopow k) = (center t ⊕ lhCenter t (twopow k)) ⊕ response t k`! -/
theorem scale_center_lhCenter (t k : Nat) :
    Rule30UOR.Core.center (t + twopow k) =
      bxor (bxor (Rule30UOR.Core.center t) (lhCenter t (twopow k)))
        (Rule30UOR.Scale.response t k) := by
  rw [← cell_negpow_eq_lhCenter_twopow t k]
  exact Rule30UOR.Scale.scale_center_paper t k

/-- **Unconditional `m * P`-Defect Lock Between `lhCenter · (2^k)` and `response · k` Under `CenterPeriodic T P` (`periodic_lhCenter_twopow_defect_eq_response_defect`, 9.943)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k ∈ ℕ` with `T ≤ t` (with NO `2^k ≤ t` cone bound!), `lhCenter (t + m * P) (twopow k) ⊕ lhCenter t (twopow k) = response (t + m * P) k ⊕ response t k`! -/
theorem periodic_lhCenter_twopow_defect_eq_response_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    bxor (lhCenter (t + m * P) (twopow k)) (lhCenter t (twopow k)) =
      bxor (Rule30UOR.Scale.response (t + m * P) k) (Rule30UOR.Scale.response t k) := by
  have hsQ := Rule30UOR.Scale.periodic_scale_paper T P hP hper k (t + m * P) (by omega)
  have hs0 := Rule30UOR.Scale.periodic_scale_paper T P hP hper k t ht
  rw [cell_negpow_eq_lhCenter_twopow (t + m * P) k] at hsQ
  rw [cell_negpow_eq_lhCenter_twopow t k] at hs0
  have hc1 : Rule30UOR.Core.center ((t + m * P) + Rule30UOR.Scale.lag P k) =
      Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k) := by
    rw [show (t + m * P) + Rule30UOR.Scale.lag P k =
      (t + Rule30UOR.Scale.lag P k) + m * P by omega]
    exact Rule30UOR.Scale.center_mul hper m (t + Rule30UOR.Scale.lag P k) (by omega)
  have hc0 : Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t :=
    Rule30UOR.Scale.center_mul hper m t ht
  rw [hc1, hc0, ← hs0] at hsQ
  revert hsQ
  cases lhCenter (t + m * P) (twopow k) <;>
    cases lhCenter t (twopow k) <;>
    cases Rule30UOR.Scale.response (t + m * P) k <;>
    cases Rule30UOR.Scale.response t k <;> decide

/-- **Unconditional `m * P`-Defect Decomposition of `maskparity · k` into `lhCenter · (2^k)` and `leftresponse · k` Under `CenterPeriodic T P` (`periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect`, 9.944)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k ∈ ℕ` with `T ≤ t` (with NO `2^k ≤ t` cone bound!), `maskparity (t + m * P) k ⊕ maskparity t k = (lhCenter (t + m * P) (twopow k) ⊕ lhCenter t (twopow k)) ⊕ (leftresponse (t + m * P) k ⊕ leftresponse t k)`! -/
theorem periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    bxor (Rule30UOR.Scale.maskparity (t + m * P) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (bxor (lhCenter (t + m * P) (twopow k)) (lhCenter t (twopow k)))
        (bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
          (Rule30UOR.Scale.leftresponse t k)) := by
  have hd := periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m t k ht
  rw [Rule30UOR.Scale.split_paper (t + m * P) k,
    Rule30UOR.Scale.split_paper t k] at hd
  revert hd
  cases lhCenter (t + m * P) (twopow k) <;>
    cases lhCenter t (twopow k) <;>
    cases Rule30UOR.Scale.leftresponse (t + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;>
    cases Rule30UOR.Scale.maskparity (t + m * P) k <;>
    cases Rule30UOR.Scale.maskparity t k <;> decide

/-- **Inside-the-Cone `m * P`-Invariance of `response · k` Under `CenterPeriodic T P` (`periodic_response_eq_cone_mul`, 9.945)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k ∈ ℕ` with `T ≤ t` and `t + m * P < twopow k`, `response (t + m * P) k = response t k`! -/
theorem periodic_response_eq_cone_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hcone : t + m * P < twopow k) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k := by
  have hd := periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m t k ht
  rw [lhCenter_gt_eq_false (t + m * P) (twopow k) hcone,
    lhCenter_gt_eq_false t (twopow k) (by omega)] at hd
  revert hd
  cases Rule30UOR.Scale.response (t + m * P) k <;>
    cases Rule30UOR.Scale.response t k <;> decide

/-- **Inside-the-Cone `m * P`-Defect Lock Between `maskparity · k` and `leftresponse · k` Under `CenterPeriodic T P` (`periodic_maskparity_defect_eq_leftresponse_defect_cone_mul`, 9.946)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k ∈ ℕ` with `T ≤ t` and `t + m * P < twopow k`, `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k`! -/
theorem periodic_maskparity_defect_eq_leftresponse_defect_cone_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hcone : t + m * P < twopow k) :
    bxor (Rule30UOR.Scale.maskparity (t + m * P) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) := by
  have hd := periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m t k ht
  rw [lhCenter_gt_eq_false (t + m * P) (twopow k) hcone,
    lhCenter_gt_eq_false t (twopow k) (by omega)] at hd
  revert hd
  cases Rule30UOR.Scale.maskparity (t + m * P) k <;>
    cases Rule30UOR.Scale.maskparity t k <;>
    cases Rule30UOR.Scale.leftresponse (t + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;> decide

/-- **Unconditional `m * P`-Antiperiodicity of `response · k` at the Left Light-Cone Boundary `t + m * P = 2^k` Under `CenterPeriodic T P` (`periodic_response_flip_at_twopow_mul`, 9.947)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k ∈ ℕ` with `0 < m`, `T ≤ t`, and `t + m * P = twopow k`, because `lhCenter (t + m * P) (2^k) = true` at the light-cone edge while `lhCenter t (2^k) = false` outside the light cone, `response (t + m * P) k = !response t k` holds UNCONDITIONALLY! -/
theorem periodic_response_flip_at_twopow_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (hm : 0 < m) (ht : T ≤ t) (heq : t + m * P = twopow k) :
    Rule30UOR.Scale.response (t + m * P) k = !Rule30UOR.Scale.response t k := by
  have hQ : 0 < m * P := Nat.mul_pos hm hP
  have hd := periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m t k ht
  have hlQ : lhCenter (t + m * P) (twopow k) = true := by
    rw [heq, lhCenter_self_eq_true (twopow k)]
  have hl0 : lhCenter t (twopow k) = false :=
    lhCenter_gt_eq_false t (twopow k) (by omega)
  rw [hlQ, hl0] at hd
  revert hd
  cases Rule30UOR.Scale.response (t + m * P) k <;>
    cases Rule30UOR.Scale.response t k <;> decide

/-- **Unconditional `m * P`-Defect Inversion Between `maskparity · k` and `leftresponse · k` at the Left Light-Cone Boundary `t + m * P = 2^k` Under `CenterPeriodic T P` (`periodic_maskparity_defect_eq_not_leftresponse_defect_at_twopow_mul`, 9.948)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k ∈ ℕ` with `0 < m`, `T ≤ t`, and `t + m * P = twopow k`, `maskparity (t + m * P) k ⊕ maskparity t k = !(leftresponse (t + m * P) k ⊕ leftresponse t k)` holds UNCONDITIONALLY! -/
theorem periodic_maskparity_defect_eq_not_leftresponse_defect_at_twopow_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (hm : 0 < m) (ht : T ≤ t) (heq : t + m * P = twopow k) :
    bxor (Rule30UOR.Scale.maskparity (t + m * P) k) (Rule30UOR.Scale.maskparity t k) =
      !bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) := by
  have hQ : 0 < m * P := Nat.mul_pos hm hP
  have hd := periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m t k ht
  have hlQ : lhCenter (t + m * P) (twopow k) = true := by
    rw [heq, lhCenter_self_eq_true (twopow k)]
  have hl0 : lhCenter t (twopow k) = false :=
    lhCenter_gt_eq_false t (twopow k) (by omega)
  rw [hlQ, hl0] at hd
  revert hd
  cases Rule30UOR.Scale.maskparity (t + m * P) k <;>
    cases Rule30UOR.Scale.maskparity t k <;>
    cases Rule30UOR.Scale.leftresponse (t + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;> decide

/-- **Exact Pointwise Equality of `m * P`-Defects Between `lhCenter · 1` and `maskparity · 0` Under `CenterPeriodic T P` (`periodic_lhCenter_one_defect_eq_maskparity_zero_defect`, 9.949)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t ∈ ℕ` with `T ≤ t`, `lhCenter (t + m * P) 1 ⊕ lhCenter t 1 = maskparity (t + m * P) 0 ⊕ maskparity t 0`! -/
theorem periodic_lhCenter_one_defect_eq_maskparity_zero_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    bxor (lhCenter (t + m * P) 1) (lhCenter t 1) =
      bxor (Rule30UOR.Scale.maskparity (t + m * P) 0)
        (Rule30UOR.Scale.maskparity t 0) := by
  rw [periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect T P hP hper m t ht,
    maskparity_zero_eq_not_center_and_rhCenter_one (t + m * P),
    maskparity_zero_eq_not_center_and_rhCenter_one t,
    Rule30UOR.Scale.center_mul hper m t ht]
  cases Rule30UOR.Core.center t <;>
    cases rhCenter (t + m * P) 1 <;>
    cases rhCenter t 1 <;> rfl

/-- **Converse Pointwise Equivalence: `lhCenter (t + m * P) 1 = lhCenter t 1 → maskparity (t + m * P) 0 = maskparity t 0` Under `CenterPeriodic T P` (`periodic_maskparity_zero_eq_of_lhCenter_one_eq`, 9.950)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `lhCenter (t + m * P) 1 = lhCenter t 1`, then `maskparity (t + m * P) 0 = maskparity t 0`! -/
theorem periodic_maskparity_zero_eq_of_lhCenter_one_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hlh : lhCenter (t + m * P) 1 = lhCenter t 1) :
    Rule30UOR.Scale.maskparity (t + m * P) 0 = Rule30UOR.Scale.maskparity t 0 := by
  have hd := periodic_lhCenter_one_defect_eq_maskparity_zero_defect T P hP hper m t ht
  rw [hlh] at hd
  revert hd
  cases lhCenter t 1 <;>
    cases Rule30UOR.Scale.maskparity (t + m * P) 0 <;>
    cases Rule30UOR.Scale.maskparity t 0 <;> decide

/-- **Unconditional Dyadic Jump of the `lhCenter · 1` Period-Shift Defect Equals the 1-Step Difference of the Scale-`k` `maskparity · k` Period-Shift Defect (`periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect`, 9.951)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k ∈ ℕ` with `T ≤ t`, `(lhCenter ((t + twopow k) + m * P) 1 ⊕ lhCenter (t + twopow k) 1) ⊕ (lhCenter (t + m * P) 1 ⊕ lhCenter t 1) = (maskparity ((t + 1) + m * P) k ⊕ maskparity (t + 1) k) ⊕ (maskparity (t + m * P) k ⊕ maskparity t k)`! -/
theorem periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    bxor (bxor (lhCenter ((t + twopow k) + m * P) 1) (lhCenter (t + twopow k) 1))
      (bxor (lhCenter (t + m * P) 1) (lhCenter t 1)) =
      bxor (bxor (Rule30UOR.Scale.maskparity ((t + 1) + m * P) k)
        (Rule30UOR.Scale.maskparity (t + 1) k))
        (bxor (Rule30UOR.Scale.maskparity (t + m * P) k)
          (Rule30UOR.Scale.maskparity t k)) := by
  rw [periodic_lhCenter_one_defect_eq_maskparity_zero_defect T P hP hper m (t + twopow k) (by omega),
    periodic_lhCenter_one_defect_eq_maskparity_zero_defect T P hP hper m t ht]
  have hsQ := maskparity_step_diff_zero (t + m * P) k
  have hs0 := maskparity_step_diff_zero t k
  rw [show (t + m * P) + 1 = (t + 1) + m * P by omega,
    show (t + m * P) + twopow k = (t + twopow k) + m * P by omega] at hsQ
  rw [bxor_four_swap, ← hsQ, ← hs0, bxor_four_swap]

/-! ### Batch 44: Dyadic Jump Laws of `lhCenter · 1` vs `leftresponse · k`, Unconditional Outside-the-Cone Dyadic Scale Laws at Zero Diagonals Dropping `z ≤ k`, and `LhBandAgree`-Driven Outside-the-Cone `response`/`maskparity` Laws (9.952–9.966) -/

/-- **Inside-the-Cone Dyadic Jump of the `lhCenter · 1` Period-Shift Defect Equals the 1-Step Difference of the `leftresponse · k` Period-Shift Defect (`periodic_lhCenter_one_dyadic_jump_defect_eq_leftresponse_step_defect_cone_mul`, 9.952)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k ∈ ℕ` with `T ≤ t` and `(t + 1) + m * P < twopow k`, `(lhCenter ((t + twopow k) + m * P) 1 ⊕ lhCenter (t + twopow k) 1) ⊕ (lhCenter (t + m * P) 1 ⊕ lhCenter t 1) = (leftresponse ((t + 1) + m * P) k ⊕ leftresponse (t + 1) k) ⊕ (leftresponse (t + m * P) k ⊕ leftresponse t k)`! -/
theorem periodic_lhCenter_one_dyadic_jump_defect_eq_leftresponse_step_defect_cone_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (hcone : (t + 1) + m * P < twopow k) :
    bxor (bxor (lhCenter ((t + twopow k) + m * P) 1) (lhCenter (t + twopow k) 1))
      (bxor (lhCenter (t + m * P) 1) (lhCenter t 1)) =
      bxor (bxor (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k)
        (Rule30UOR.Scale.leftresponse (t + 1) k))
        (bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
          (Rule30UOR.Scale.leftresponse t k)) := by
  rw [periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect T P hP hper m t k ht,
    periodic_maskparity_defect_eq_leftresponse_defect_cone_mul T P hP hper m (t + 1) k (by omega) hcone,
    periodic_maskparity_defect_eq_leftresponse_defect_cone_mul T P hP hper m t k ht (by omega)]

/-- **Unconditional Inversion of the `lhCenter · 1` Dyadic Jump Defect at the Left Light-Cone Boundary `(t + 1) + m * P = 2^k` (`periodic_lhCenter_one_dyadic_jump_defect_eq_not_leftresponse_step_defect_at_twopow_mul`, 9.953)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k ∈ ℕ` with `0 < m`, `T ≤ t`, and `(t + 1) + m * P = twopow k`, `(lhCenter ((t + twopow k) + m * P) 1 ⊕ lhCenter (t + twopow k) 1) ⊕ (lhCenter (t + m * P) 1 ⊕ lhCenter t 1) = !((leftresponse ((t + 1) + m * P) k ⊕ leftresponse (t + 1) k) ⊕ (leftresponse (t + m * P) k ⊕ leftresponse t k))`! -/
theorem periodic_lhCenter_one_dyadic_jump_defect_eq_not_leftresponse_step_defect_at_twopow_mul
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (hm : 0 < m) (ht : T ≤ t) (heq : (t + 1) + m * P = twopow k) :
    bxor (bxor (lhCenter ((t + twopow k) + m * P) 1) (lhCenter (t + twopow k) 1))
      (bxor (lhCenter (t + m * P) 1) (lhCenter t 1)) =
      !bxor (bxor (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k)
        (Rule30UOR.Scale.leftresponse (t + 1) k))
        (bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
          (Rule30UOR.Scale.leftresponse t k)) := by
  rw [periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect T P hP hper m t k ht,
    periodic_maskparity_defect_eq_not_leftresponse_defect_at_twopow_mul T P hP hper m (t + 1) k hm (by omega) heq,
    periodic_maskparity_defect_eq_leftresponse_defect_cone_mul T P hP hper m t k ht (by omega)]
  cases bxor (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k) (Rule30UOR.Scale.leftresponse (t + 1) k) <;>
    cases bxor (Rule30UOR.Scale.leftresponse (t + m * P) k) (Rule30UOR.Scale.leftresponse t k) <;> rfl

/-- **General Unconditional Decomposition of the `lhCenter · 1` Dyadic Jump Defect into the 1-Step Difference of `lhCenter · (2^k)` and the 1-Step Difference of `leftresponse · k` (`periodic_lhCenter_one_dyadic_jump_defect_eq_lhCenter_twopow_step_xor_leftresponse_step_defect`, 9.954)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k ∈ ℕ` with `T ≤ t` (with NO `2^k` bound!), the dyadic jump across `2^k` of `lhCenter (s + m * P) 1 ⊕ lhCenter s 1` equals the 1-step time difference of `lhCenter (s + m * P) (2^k) ⊕ lhCenter s (2^k)` XORed with the 1-step time difference of `leftresponse (s + m * P) k ⊕ leftresponse s k`! -/
theorem periodic_lhCenter_one_dyadic_jump_defect_eq_lhCenter_twopow_step_xor_leftresponse_step_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) :
    bxor (bxor (lhCenter ((t + twopow k) + m * P) 1) (lhCenter (t + twopow k) 1))
      (bxor (lhCenter (t + m * P) 1) (lhCenter t 1)) =
      bxor
        (bxor (bxor (lhCenter ((t + 1) + m * P) (twopow k)) (lhCenter (t + 1) (twopow k)))
          (bxor (lhCenter (t + m * P) (twopow k)) (lhCenter t (twopow k))))
        (bxor (bxor (Rule30UOR.Scale.leftresponse ((t + 1) + m * P) k)
          (Rule30UOR.Scale.leftresponse (t + 1) k))
          (bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
            (Rule30UOR.Scale.leftresponse t k))) := by
  rw [periodic_lhCenter_one_dyadic_jump_defect_eq_maskparity_step_defect T P hP hper m t k ht,
    periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect T P hP hper m (t + 1) k (by omega),
    periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect T P hP hper m t k ht,
    bxor_four_swap]

/-- **Unconditional Dyadic Left-Wing Vanishing Along Any Settled Zero Diagonal `z` Without `z ≤ k` (`lhCenter_twopow_of_zero_diag`, 9.955)**:
    for EVERY `z, k ∈ ℕ` (with NO `z ≤ k` bound!), if `IsZeroDiag z` and `settle z ≤ z + twopow k`, then `lhCenter (z + twopow k) (twopow k) = false`! -/
theorem lhCenter_twopow_of_zero_diag (z k : Nat)
    (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    lhCenter (z + twopow k) (twopow k) = false := by
  exact lhCenter_of_zero_diag (z + twopow k) (twopow k)
    (by rwa [show (z + twopow k) - twopow k = z by omega])
    (by rwa [show (z + twopow k) - twopow k = z by omega])

theorem lhCenter_twopow_of_zero_diag_prop (z k : Nat)
    (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    lhCenter (z + twopow k) (twopow k) = false :=
  lhCenter_twopow_of_zero_diag z k hz hset

/-- **Unconditional Dyadic Left-Wing Blackness Two Diagonals After Any Settled Zero Diagonal `z` Without `z ≤ k` (`lhCenter_twopow_after_zero_diag`, 9.956)**:
    for EVERY `z, k ∈ ℕ` (with NO `z ≤ k` bound!), if `IsZeroDiag z` and `settle (z + 2) ≤ (z + 2) + twopow k`, then `lhCenter ((z + 2) + twopow k) (twopow k) = true`! -/
theorem lhCenter_twopow_after_zero_diag (z k : Nat)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    lhCenter ((z + 2) + twopow k) (twopow k) = true := by
  exact lhCenter_at_t_after_zero_diag ((z + 2) + twopow k) (twopow k)
    (by rwa [show ((z + 2) + twopow k) - (twopow k + 2) = z by omega])
    (by rwa [show (((z + 2) + twopow k) - (twopow k + 2)) + 2 = z + 2 by omega])

theorem lhCenter_twopow_after_zero_diag_prop (z k : Nat)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    lhCenter ((z + 2) + twopow k) (twopow k) = true :=
  lhCenter_twopow_after_zero_diag z k hz hset

/-- **Unconditional Outside-the-Cone Collapse of the Dyadic Scale Identity Along Any Settled Zero Diagonal `z` Without `z ≤ k` (`scale_center_at_zero_diag`, 9.957)**:
    for EVERY `z, k ∈ ℕ` (with NO `z ≤ k` bound!), if `IsZeroDiag z` and `settle z ≤ z + twopow k`, then `center ((z + twopow k) + twopow k) = center (z + twopow k) ⊕ response (z + twopow k) k`! -/
theorem scale_center_at_zero_diag (z k : Nat)
    (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    Rule30UOR.Core.center ((z + twopow k) + twopow k) =
      bxor (Rule30UOR.Core.center (z + twopow k))
        (Rule30UOR.Scale.response (z + twopow k) k) := by
  rw [scale_center_lhCenter (z + twopow k) k,
    lhCenter_twopow_of_zero_diag z k hz hset]
  cases Rule30UOR.Core.center (z + twopow k) <;>
    cases Rule30UOR.Scale.response (z + twopow k) k <;> rfl

theorem scale_center_at_zero_diag_prop (z k : Nat)
    (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    Rule30UOR.Core.center ((z + twopow k) + twopow k) =
      bxor (Rule30UOR.Core.center (z + twopow k))
        (Rule30UOR.Scale.response (z + twopow k) k) :=
  scale_center_at_zero_diag z k hz hset

/-- **Unconditional Outside-the-Cone Inversion of the Dyadic Scale Identity Two Diagonals After Any Settled Zero Diagonal `z` Without `z ≤ k` (`scale_center_after_zero_diag`, 9.958)**:
    for EVERY `z, k ∈ ℕ` (with NO `z ≤ k` bound!), if `IsZeroDiag z` and `settle (z + 2) ≤ (z + 2) + twopow k`, then `center (((z + 2) + twopow k) + twopow k) = !(center ((z + 2) + twopow k) ⊕ response ((z + 2) + twopow k) k)`! -/
theorem scale_center_after_zero_diag (z k : Nat)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    Rule30UOR.Core.center (((z + 2) + twopow k) + twopow k) =
      !bxor (Rule30UOR.Core.center ((z + 2) + twopow k))
        (Rule30UOR.Scale.response ((z + 2) + twopow k) k) := by
  rw [scale_center_lhCenter ((z + 2) + twopow k) k,
    lhCenter_twopow_after_zero_diag z k hz hset]
  cases Rule30UOR.Core.center ((z + 2) + twopow k) <;>
    cases Rule30UOR.Scale.response ((z + 2) + twopow k) k <;> rfl

theorem scale_center_after_zero_diag_prop (z k : Nat)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    Rule30UOR.Core.center (((z + 2) + twopow k) + twopow k) =
      !bxor (Rule30UOR.Core.center ((z + 2) + twopow k))
        (Rule30UOR.Scale.response ((z + 2) + twopow k) k) :=
  scale_center_after_zero_diag z k hz hset

/-- **Unconditional Outside-the-Cone Center-Lag Formula for `response (z + 2^k) k` Along Any Settled Zero Diagonal `z` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_response_at_zero_diag`, 9.959)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `z, k ∈ ℕ` with `T ≤ z + twopow k`, `IsZeroDiag z`, and `settle z ≤ z + twopow k` (with NO `z ≤ k` bound!), `response (z + twopow k) k = center ((z + twopow k) + lag P k) ⊕ center (z + twopow k)`! -/
theorem periodic_response_at_zero_diag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    Rule30UOR.Scale.response (z + twopow k) k =
      bxor (Rule30UOR.Core.center ((z + twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center (z + twopow k)) := by
  have hs := Rule30UOR.Scale.periodic_scale_paper T P hP hper k (z + twopow k) ht
  rw [cell_negpow_eq_lhCenter_twopow (z + twopow k) k,
    lhCenter_twopow_of_zero_diag z k hz hset] at hs
  rw [← hs]
  cases Rule30UOR.Scale.response (z + twopow k) k <;> rfl

theorem periodic_response_at_zero_diag_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    Rule30UOR.Scale.response (z + twopow k) k =
      bxor (Rule30UOR.Core.center ((z + twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center (z + twopow k)) :=
  periodic_response_at_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional Outside-the-Cone Inverted Center-Lag Formula for `response ((z + 2) + 2^k) k` Two Diagonals After Any Settled Zero Diagonal `z` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_response_after_zero_diag`, 9.960)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `z, k ∈ ℕ` with `T ≤ (z + 2) + twopow k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + twopow k` (with NO `z ≤ k` bound!), `response ((z + 2) + twopow k) k = !(center (((z + 2) + twopow k) + lag P k) ⊕ center ((z + 2) + twopow k))`! -/
theorem periodic_response_after_zero_diag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    Rule30UOR.Scale.response ((z + 2) + twopow k) k =
      !bxor (Rule30UOR.Core.center (((z + 2) + twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center ((z + 2) + twopow k)) := by
  have hs := Rule30UOR.Scale.periodic_scale_paper T P hP hper k ((z + 2) + twopow k) ht
  rw [cell_negpow_eq_lhCenter_twopow ((z + 2) + twopow k) k,
    lhCenter_twopow_after_zero_diag z k hz hset] at hs
  rw [← hs]
  cases Rule30UOR.Scale.response ((z + 2) + twopow k) k <;> rfl

theorem periodic_response_after_zero_diag_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    Rule30UOR.Scale.response ((z + 2) + twopow k) k =
      !bxor (Rule30UOR.Core.center (((z + 2) + twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center ((z + 2) + twopow k)) :=
  periodic_response_after_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional `m * P`-Defect Readout of `response` at `z + 2^k` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_response_defect_at_zero_diag_eq_lhCenter_twopow`, 9.961)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k ∈ ℕ` with `T ≤ z + twopow k`, `IsZeroDiag z`, and `settle z ≤ z + twopow k` (with NO `z ≤ k` bound!), `response ((z + twopow k) + m * P) k ⊕ response (z + twopow k) k = lhCenter ((z + twopow k) + m * P) (twopow k)`! -/
theorem periodic_response_defect_at_zero_diag_eq_lhCenter_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    bxor (Rule30UOR.Scale.response ((z + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (z + twopow k) k) =
      lhCenter ((z + twopow k) + m * P) (twopow k) := by
  have hd := periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (z + twopow k) k ht
  rw [lhCenter_twopow_of_zero_diag z k hz hset] at hd
  rw [← hd]
  cases lhCenter ((z + twopow k) + m * P) (twopow k) <;> rfl

theorem periodic_response_defect_at_zero_diag_eq_lhCenter_twopow_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    bxor (Rule30UOR.Scale.response ((z + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (z + twopow k) k) =
      lhCenter ((z + twopow k) + m * P) (twopow k) :=
  periodic_response_defect_at_zero_diag_eq_lhCenter_twopow T P hP hper m z k ht hz hset

/-- **Unconditional `m * P`-Defect Readout of `response` at `(z + 2) + 2^k` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow`, 9.962)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k ∈ ℕ` with `T ≤ (z + 2) + twopow k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + twopow k` (with NO `z ≤ k` bound!), `response (((z + 2) + twopow k) + m * P) k ⊕ response ((z + 2) + twopow k) k = !lhCenter (((z + 2) + twopow k) + m * P) (twopow k)`! -/
theorem periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor (Rule30UOR.Scale.response (((z + 2) + twopow k) + m * P) k)
      (Rule30UOR.Scale.response ((z + 2) + twopow k) k) =
      !lhCenter (((z + 2) + twopow k) + m * P) (twopow k) := by
  have hd := periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m ((z + 2) + twopow k) k ht
  rw [lhCenter_twopow_after_zero_diag z k hz hset] at hd
  rw [← hd]
  cases lhCenter (((z + 2) + twopow k) + m * P) (twopow k) <;> rfl

theorem periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    bxor (Rule30UOR.Scale.response (((z + 2) + twopow k) + m * P) k)
      (Rule30UOR.Scale.response ((z + 2) + twopow k) k) =
      !lhCenter (((z + 2) + twopow k) + m * P) (twopow k) :=
  periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow T P hP hper m z k ht hz hset

/-- **Outside-the-Cone `m * P`-Invariance of `response · k` Under `LhBandAgree` Covering `2^k` (`periodic_response_eq_of_lhBandAgree_twopow`, 9.963)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, p0, L ∈ ℕ` with `T ≤ t`, `p0 ≤ twopow k`, and `twopow k ≤ p0 + L`, if `LhBandAgree t (m * P) p0 L` holds at time `t`, then `response (t + m * P) k = response t k`! -/
theorem periodic_response_eq_of_lhBandAgree_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k p0 L : Nat) (ht : T ≤ t)
    (hp0 : p0 ≤ twopow k) (hL : twopow k ≤ p0 + L)
    (hband : LhBandAgree t (m * P) p0 L) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k := by
  have hd := periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m t k ht
  have hb := hband (twopow k - p0) (by omega)
  rw [show p0 + (twopow k - p0) = twopow k by omega] at hb
  rw [hb] at hd
  revert hd
  cases lhCenter t (twopow k) <;>
    cases Rule30UOR.Scale.response (t + m * P) k <;>
    cases Rule30UOR.Scale.response t k <;> decide

/-- **Outside-the-Cone `m * P`-Defect Lock Between `maskparity · k` and `leftresponse · k` Under `LhBandAgree` Covering `2^k` (`periodic_maskparity_defect_eq_leftresponse_defect_of_lhBandAgree_twopow`, 9.964)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, p0, L ∈ ℕ` with `T ≤ t`, `p0 ≤ twopow k`, and `twopow k ≤ p0 + L`, if `LhBandAgree t (m * P) p0 L` holds at time `t`, then `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k`! -/
theorem periodic_maskparity_defect_eq_leftresponse_defect_of_lhBandAgree_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k p0 L : Nat) (ht : T ≤ t)
    (hp0 : p0 ≤ twopow k) (hL : twopow k ≤ p0 + L)
    (hband : LhBandAgree t (m * P) p0 L) :
    bxor (Rule30UOR.Scale.maskparity (t + m * P) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) := by
  have hd := periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m t k ht
  have hb := hband (twopow k - p0) (by omega)
  rw [show p0 + (twopow k - p0) = twopow k by omega] at hb
  rw [hb] at hd
  revert hd
  cases lhCenter t (twopow k) <;>
    cases Rule30UOR.Scale.maskparity (t + m * P) k <;>
    cases Rule30UOR.Scale.maskparity t k <;>
    cases Rule30UOR.Scale.leftresponse (t + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;> decide

/-- **Producing Outside-the-Cone `response (t + m * P) k = response t k` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`periodic_response_eq_of_white_center_rhCenter_one_twopow`, 9.965)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1`, then `response (t + m * P) k = response t k`! -/
theorem periodic_response_eq_of_white_center_rhCenter_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k := by
  exact periodic_response_eq_of_lhBandAgree_twopow T P hP hper m t k 0 (S + 1) ht
    (by omega) (by omega)
    (periodic_lhBandAgree_zero_of_white_center_rhCenter_one T P hP hper m t S ht hw)

/-- **Producing Outside-the-Cone `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhCenter_one_twopow`, 9.966)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1`, then `maskparity (t + m * P) k ⊕ maskparity t k = leftresponse (t + m * P) k ⊕ leftresponse t k`! -/
theorem periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhCenter_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    bxor (Rule30UOR.Scale.maskparity (t + m * P) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Scale.leftresponse (t + m * P) k)
        (Rule30UOR.Scale.leftresponse t k) := by
  exact periodic_maskparity_defect_eq_leftresponse_defect_of_lhBandAgree_twopow
    T P hP hper m t k 0 (S + 1) ht (by omega) (by omega)
    (periodic_lhBandAgree_zero_of_white_center_rhCenter_one T P hP hper m t S ht hw)

/-! ### Batch 45: Universal Unconditional Dyadic Coboundaries of `response` and `leftresponse` (Dropping `d ≤ k`), Unconditional Zero-Diagonal and Doubling Dyadic Laws, and Outside-the-Cone `maskparity`/`response` Laws at Zero Diagonals (9.967–9.981) -/

/-- **Universal Unconditional Dyadic Coboundary of `response` for Every `t, k ∈ ℕ` (`response_coboundary_eq_lhCenter_twopow`, 9.967)**:
    for EVERY `t, k ∈ ℕ` (with NO `t ≤ k` or `t < 2^k` bound at all!), `(response t (k + 1) ⊕ response t k) ⊕ response (t + twopow k) k = (lhCenter (t + twopow k) (twopow k) ⊕ lhCenter t (twopow k)) ⊕ lhCenter t (twopow (k + 1))`! -/
theorem response_coboundary_eq_lhCenter_twopow (t k : Nat) :
    bxor (bxor (Rule30UOR.Scale.response t (k + 1)) (Rule30UOR.Scale.response t k))
      (Rule30UOR.Scale.response (t + twopow k) k) =
      bxor (bxor (lhCenter (t + twopow k) (twopow k)) (lhCenter t (twopow k)))
        (lhCenter t (twopow (k + 1))) := by
  have hs1 := scale_center_lhCenter t k
  have hs2 := scale_center_lhCenter (t + twopow k) k
  have hs3 := scale_center_lhCenter t (k + 1)
  have hstep : (t + twopow k) + twopow k = t + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep, hs3, hs1] at hs2
  revert hs2
  cases Rule30UOR.Core.center t <;>
    cases lhCenter t (twopow (k + 1)) <;>
    cases Rule30UOR.Scale.response t (k + 1) <;>
    cases lhCenter t (twopow k) <;>
    cases Rule30UOR.Scale.response t k <;>
    cases lhCenter (t + twopow k) (twopow k) <;>
    cases Rule30UOR.Scale.response (t + twopow k) k <;> decide

/-- **Universal Unconditional Dyadic Coboundary of `leftresponse` for Every `t, k ∈ ℕ` (`leftresponse_coboundary_eq_lhCenter_twopow`, 9.968)**:
    for EVERY `t, k ∈ ℕ` (with NO `t ≤ k` or `t < 2^k` bound at all!), `(leftresponse t (k + 1) ⊕ leftresponse t k) ⊕ leftresponse (t + twopow k) k = (lhCenter (t + twopow k) (twopow k) ⊕ lhCenter t (twopow k)) ⊕ lhCenter t (twopow (k + 1))`! -/
theorem leftresponse_coboundary_eq_lhCenter_twopow (t k : Nat) :
    bxor (bxor (Rule30UOR.Scale.leftresponse t (k + 1)) (Rule30UOR.Scale.leftresponse t k))
      (Rule30UOR.Scale.leftresponse (t + twopow k) k) =
      bxor (bxor (lhCenter (t + twopow k) (twopow k)) (lhCenter t (twopow k)))
        (lhCenter t (twopow (k + 1))) := by
  have hr := response_coboundary_eq_lhCenter_twopow t k
  rw [Rule30UOR.Scale.split_paper t (k + 1),
    Rule30UOR.Scale.split_paper t k,
    Rule30UOR.Scale.split_paper (t + twopow k) k] at hr
  have hm := maskparity_coboundary t k
  rw [← hr]
  revert hm
  cases Rule30UOR.Scale.leftresponse t (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse t k <;>
    cases Rule30UOR.Scale.leftresponse (t + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity t (k + 1) <;>
    cases Rule30UOR.Scale.maskparity t k <;>
    cases Rule30UOR.Scale.maskparity (t + twopow k) k <;> decide

/-- **Inside-the-Cone Readout of `lhCenter (t + 2^k) (2^k)` as the `response` Dyadic Coboundary Dropping `t ≤ k` (`lhCenter_twopow_eq_response_coboundary_cone`, 9.969)**:
    for all `t, k ∈ ℕ` with `t < twopow k` (linear in-cone bound `t < 2^k` instead of logarithmic `t ≤ k`!), `lhCenter (t + twopow k) (twopow k) = (response t (k + 1) ⊕ response t k) ⊕ response (t + twopow k) k`! -/
theorem lhCenter_twopow_eq_response_coboundary_cone (t k : Nat) (ht : t < twopow k) :
    lhCenter (t + twopow k) (twopow k) =
      bxor (bxor (Rule30UOR.Scale.response t (k + 1)) (Rule30UOR.Scale.response t k))
        (Rule30UOR.Scale.response (t + twopow k) k) := by
  have hr := response_coboundary_eq_lhCenter_twopow t k
  have h1 : lhCenter t (twopow k) = false := lhCenter_gt_eq_false t (twopow k) ht
  have h2 : lhCenter t (twopow (k + 1)) = false := by
    apply lhCenter_gt_eq_false t (twopow (k + 1))
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hr, h1, h2]
  cases lhCenter (t + twopow k) (twopow k) <;> rfl

/-- **Inside-the-Cone Readout of `lhCenter (t + 2^k) (2^k)` as the Pure Left-Half `leftresponse` Dyadic Coboundary Dropping `t ≤ k` (`lhCenter_twopow_eq_leftresponse_coboundary_cone`, 9.970)**:
    for all `t, k ∈ ℕ` with `t < twopow k` (dropping `t ≤ k`!), `lhCenter (t + twopow k) (twopow k) = (leftresponse t (k + 1) ⊕ leftresponse t k) ⊕ leftresponse (t + twopow k) k`! -/
theorem lhCenter_twopow_eq_leftresponse_coboundary_cone (t k : Nat) (ht : t < twopow k) :
    lhCenter (t + twopow k) (twopow k) =
      bxor (bxor (Rule30UOR.Scale.leftresponse t (k + 1)) (Rule30UOR.Scale.leftresponse t k))
        (Rule30UOR.Scale.leftresponse (t + twopow k) k) := by
  have hl := leftresponse_coboundary_eq_lhCenter_twopow t k
  have h1 : lhCenter t (twopow k) = false := lhCenter_gt_eq_false t (twopow k) ht
  have h2 : lhCenter t (twopow (k + 1)) = false := by
    apply lhCenter_gt_eq_false t (twopow (k + 1))
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hl, h1, h2]
  cases lhCenter (t + twopow k) (twopow k) <;> rfl

/-- **Inside-the-Cone Vanishing of the `leftresponse` Dyadic Coboundary Along Any Settled Zero Diagonal `z` Dropping `z ≤ k` (`leftresponse_coboundary_at_zero_diag_cone`, 9.971)**:
    for all `z, k ∈ ℕ` with `z < twopow k`, `IsZeroDiag z`, and `settle z ≤ z + twopow k` (dropping `z ≤ k`!), `(leftresponse z (k + 1) ⊕ leftresponse z k) ⊕ leftresponse (z + twopow k) k = false`! -/
theorem leftresponse_coboundary_at_zero_diag_cone (z k : Nat)
    (hcone : z < twopow k) (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    bxor (bxor (Rule30UOR.Scale.leftresponse z (k + 1)) (Rule30UOR.Scale.leftresponse z k))
      (Rule30UOR.Scale.leftresponse (z + twopow k) k) = false := by
  rw [← lhCenter_twopow_eq_leftresponse_coboundary_cone z k hcone]
  exact lhCenter_twopow_of_zero_diag z k hz hset

theorem leftresponse_coboundary_at_zero_diag_cone_prop (z k : Nat)
    (hcone : z < twopow k) (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    bxor (bxor (Rule30UOR.Scale.leftresponse z (k + 1)) (Rule30UOR.Scale.leftresponse z k))
      (Rule30UOR.Scale.leftresponse (z + twopow k) k) = false :=
  leftresponse_coboundary_at_zero_diag_cone z k hcone hz hset

/-- **Inside-the-Cone Non-Vanishing (`= true`) of the `leftresponse` Dyadic Coboundary Two Diagonals After Any Settled Zero Diagonal `z` Dropping `z + 2 ≤ k` (`leftresponse_coboundary_after_zero_diag_cone`, 9.972)**:
    for all `z, k ∈ ℕ` with `z + 2 < twopow k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + twopow k` (dropping `z + 2 ≤ k`!), `(leftresponse (z + 2) (k + 1) ⊕ leftresponse (z + 2) k) ⊕ leftresponse ((z + 2) + twopow k) k = true`! -/
theorem leftresponse_coboundary_after_zero_diag_cone (z k : Nat)
    (hcone : z + 2 < twopow k) (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor (bxor (Rule30UOR.Scale.leftresponse (z + 2) (k + 1))
      (Rule30UOR.Scale.leftresponse (z + 2) k))
      (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k) = true := by
  rw [← lhCenter_twopow_eq_leftresponse_coboundary_cone (z + 2) k hcone]
  exact lhCenter_twopow_after_zero_diag z k hz hset

theorem leftresponse_coboundary_after_zero_diag_cone_prop (z k : Nat)
    (hcone : z + 2 < twopow k) (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    bxor (bxor (Rule30UOR.Scale.leftresponse (z + 2) (k + 1))
      (Rule30UOR.Scale.leftresponse (z + 2) k))
      (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k) = true :=
  leftresponse_coboundary_after_zero_diag_cone z k hcone hz hset

/-- **Unconditional Dyadic Left-Wing Scale-Step Flip Along Any Settled Doubling Diagonal `z + 1` Without `z ≤ k` or `z < 2^k` (`lhCenter_twopow_succ_antiperiodic_of_doubles`, 9.973)**:
    for EVERY `z, k ∈ ℕ` (with NO `z ≤ k` or `z < 2^k` bound at all!), if `IsZeroDiag z`, `DoublesAt (twopow k) z`, and `settle (z + 1) ≤ (z + 1) + twopow k`, then `lhCenter ((z + 1) + twopow (k + 1)) (twopow (k + 1)) = !lhCenter ((z + 1) + twopow k) (twopow k)`! -/
theorem lhCenter_twopow_succ_antiperiodic_of_doubles (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : settle (z + 1) ≤ (z + 1) + twopow k) :
    lhCenter ((z + 1) + twopow (k + 1)) (twopow (k + 1)) =
      !lhCenter ((z + 1) + twopow k) (twopow k) := by
  rw [lhCenter_eq_ldiag ((z + 1) + twopow (k + 1)) (twopow (k + 1)) (by omega),
    lhCenter_eq_ldiag ((z + 1) + twopow k) (twopow k) (by omega),
    show ((z + 1) + twopow (k + 1)) - twopow (k + 1) = z + 1 by omega,
    show ((z + 1) + twopow k) - twopow k = z + 1 by omega,
    show (z + 1) + twopow (k + 1) = ((z + 1) + twopow k) + twopow k by
      rw [Rule30UOR.Core.twopow_succ]; omega]
  exact ldiag_settled_antiperiodic_of_doubles (twopow k) z ((z + 1) + twopow k) hz hd hset

theorem lhCenter_twopow_succ_antiperiodic_of_doubles_prop (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : SettledBy (z + 1) ((z + 1) + twopow k)) :
    lhCenter ((z + 1) + twopow (k + 1)) (twopow (k + 1)) =
      !lhCenter ((z + 1) + twopow k) (twopow k) :=
  lhCenter_twopow_succ_antiperiodic_of_doubles z k hz hd hset

/-- **Unconditional Outside-the-Cone Formula for `maskparity (z + 2^k) k` Along Any Settled Zero Diagonal `z` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_maskparity_at_zero_diag`, 9.974)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `z, k ∈ ℕ` with `T ≤ z + twopow k`, `IsZeroDiag z`, and `settle z ≤ z + twopow k` (with NO `z ≤ k` bound!), `maskparity (z + twopow k) k = leftresponse (z + twopow k) k ⊕ (center ((z + twopow k) + lag P k) ⊕ center (z + twopow k))`! -/
theorem periodic_maskparity_at_zero_diag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    Rule30UOR.Scale.maskparity (z + twopow k) k =
      bxor (Rule30UOR.Scale.leftresponse (z + twopow k) k)
        (bxor (Rule30UOR.Core.center ((z + twopow k) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (z + twopow k))) := by
  have hr := periodic_response_at_zero_diag T P hP hper z k ht hz hset
  rw [Rule30UOR.Scale.split_paper (z + twopow k) k] at hr
  revert hr
  cases Rule30UOR.Scale.leftresponse (z + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity (z + twopow k) k <;>
    cases bxor (Rule30UOR.Core.center ((z + twopow k) + Rule30UOR.Scale.lag P k))
      (Rule30UOR.Core.center (z + twopow k)) <;> decide

theorem periodic_maskparity_at_zero_diag_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    Rule30UOR.Scale.maskparity (z + twopow k) k =
      bxor (Rule30UOR.Scale.leftresponse (z + twopow k) k)
        (bxor (Rule30UOR.Core.center ((z + twopow k) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (z + twopow k))) :=
  periodic_maskparity_at_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional Outside-the-Cone Inverted Formula for `maskparity ((z + 2) + 2^k) k` Two Diagonals After Any Settled Zero Diagonal `z` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_maskparity_after_zero_diag`, 9.975)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `z, k ∈ ℕ` with `T ≤ (z + 2) + twopow k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + twopow k` (with NO `z ≤ k` bound!), `maskparity ((z + 2) + twopow k) k = !(leftresponse ((z + 2) + twopow k) k ⊕ (center (((z + 2) + twopow k) + lag P k) ⊕ center ((z + 2) + twopow k)))`! -/
theorem periodic_maskparity_after_zero_diag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    Rule30UOR.Scale.maskparity ((z + 2) + twopow k) k =
      !bxor (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k)
        (bxor (Rule30UOR.Core.center (((z + 2) + twopow k) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center ((z + 2) + twopow k))) := by
  have hr := periodic_response_after_zero_diag T P hP hper z k ht hz hset
  rw [Rule30UOR.Scale.split_paper ((z + 2) + twopow k) k] at hr
  revert hr
  cases Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity ((z + 2) + twopow k) k <;>
    cases bxor (Rule30UOR.Core.center (((z + 2) + twopow k) + Rule30UOR.Scale.lag P k))
      (Rule30UOR.Core.center ((z + 2) + twopow k)) <;> decide

theorem periodic_maskparity_after_zero_diag_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    Rule30UOR.Scale.maskparity ((z + 2) + twopow k) k =
      !bxor (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k)
        (bxor (Rule30UOR.Core.center (((z + 2) + twopow k) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center ((z + 2) + twopow k))) :=
  periodic_maskparity_after_zero_diag T P hP hper z k ht hz hset

/-- **Unconditional `m * P`-Defect Law for `maskparity` at `z + 2^k` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_maskparity_defect_at_zero_diag_eq_lhCenter_twopow_xor_leftresponse_defect`, 9.976)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k ∈ ℕ` with `T ≤ z + twopow k`, `IsZeroDiag z`, and `settle z ≤ z + twopow k` (with NO `z ≤ k` bound!), `maskparity ((z + twopow k) + m * P) k ⊕ maskparity (z + twopow k) k = lhCenter ((z + twopow k) + m * P) (twopow k) ⊕ (leftresponse ((z + twopow k) + m * P) k ⊕ leftresponse (z + twopow k) k)`! -/
theorem periodic_maskparity_defect_at_zero_diag_eq_lhCenter_twopow_xor_leftresponse_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    bxor (Rule30UOR.Scale.maskparity ((z + twopow k) + m * P) k)
      (Rule30UOR.Scale.maskparity (z + twopow k) k) =
      bxor (lhCenter ((z + twopow k) + m * P) (twopow k))
        (bxor (Rule30UOR.Scale.leftresponse ((z + twopow k) + m * P) k)
          (Rule30UOR.Scale.leftresponse (z + twopow k) k)) := by
  have hd := periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m (z + twopow k) k ht
  rw [lhCenter_twopow_of_zero_diag z k hz hset] at hd
  rw [hd]
  cases lhCenter ((z + twopow k) + m * P) (twopow k) <;>
    cases bxor (Rule30UOR.Scale.leftresponse ((z + twopow k) + m * P) k)
      (Rule30UOR.Scale.leftresponse (z + twopow k) k) <;> rfl

theorem periodic_maskparity_defect_at_zero_diag_eq_lhCenter_twopow_xor_leftresponse_defect_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy z (z + twopow k)) :
    bxor (Rule30UOR.Scale.maskparity ((z + twopow k) + m * P) k)
      (Rule30UOR.Scale.maskparity (z + twopow k) k) =
      bxor (lhCenter ((z + twopow k) + m * P) (twopow k))
        (bxor (Rule30UOR.Scale.leftresponse ((z + twopow k) + m * P) k)
          (Rule30UOR.Scale.leftresponse (z + twopow k) k)) :=
  periodic_maskparity_defect_at_zero_diag_eq_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m z k ht hz hset

/-- **Unconditional `m * P`-Defect Law for `maskparity` at `(z + 2) + 2^k` Under `CenterPeriodic T P` Without `z ≤ k` (`periodic_maskparity_defect_after_zero_diag_eq_not_lhCenter_twopow_xor_leftresponse_defect`, 9.977)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k ∈ ℕ` with `T ≤ (z + 2) + twopow k`, `IsZeroDiag z`, and `settle (z + 2) ≤ (z + 2) + twopow k` (with NO `z ≤ k` bound!), `maskparity (((z + 2) + twopow k) + m * P) k ⊕ maskparity ((z + 2) + twopow k) k = !(lhCenter (((z + 2) + twopow k) + m * P) (twopow k) ⊕ (leftresponse (((z + 2) + twopow k) + m * P) k ⊕ leftresponse ((z + 2) + twopow k) k))`! -/
theorem periodic_maskparity_defect_after_zero_diag_eq_not_lhCenter_twopow_xor_leftresponse_defect
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor (Rule30UOR.Scale.maskparity (((z + 2) + twopow k) + m * P) k)
      (Rule30UOR.Scale.maskparity ((z + 2) + twopow k) k) =
      !bxor (lhCenter (((z + 2) + twopow k) + m * P) (twopow k))
        (bxor (Rule30UOR.Scale.leftresponse (((z + 2) + twopow k) + m * P) k)
          (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k)) := by
  have hd := periodic_maskparity_defect_eq_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m ((z + 2) + twopow k) k ht
  rw [lhCenter_twopow_after_zero_diag z k hz hset] at hd
  rw [hd]
  cases lhCenter (((z + 2) + twopow k) + m * P) (twopow k) <;>
    cases bxor (Rule30UOR.Scale.leftresponse (((z + 2) + twopow k) + m * P) k)
      (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k) <;> rfl

theorem periodic_maskparity_defect_after_zero_diag_eq_not_lhCenter_twopow_xor_leftresponse_defect_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (ht : T ≤ (z + 2) + twopow k)
    (hz : IsZeroDiag z) (hset : SettledBy (z + 2) ((z + 2) + twopow k)) :
    bxor (Rule30UOR.Scale.maskparity (((z + 2) + twopow k) + m * P) k)
      (Rule30UOR.Scale.maskparity ((z + 2) + twopow k) k) =
      !bxor (lhCenter (((z + 2) + twopow k) + m * P) (twopow k))
        (bxor (Rule30UOR.Scale.leftresponse (((z + 2) + twopow k) + m * P) k)
          (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k)) :=
  periodic_maskparity_defect_after_zero_diag_eq_not_lhCenter_twopow_xor_leftresponse_defect
    T P hP hper m z k ht hz hset

/-- **Unconditional Shift-`2` (`m * P = 2`) Antiperiodicity of `response · k` at `z + 2^k` for Every Zero Diagonal `z` Without `z ≤ k` (`periodic_response_flip_at_zero_diag_step_two`, 9.978)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k ∈ ℕ` with `m * P = 2`, `T ≤ z + twopow k`, `IsZeroDiag z`, `settle z ≤ z + twopow k`, and `settle (z + 2) ≤ (z + 2) + twopow k` (with NO `z ≤ k` bound!), `response ((z + twopow k) + m * P) k = !response (z + twopow k) k`! -/
theorem periodic_response_flip_at_zero_diag_step_two
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (hmP : m * P = 2) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z)
    (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k) :
    Rule30UOR.Scale.response ((z + twopow k) + m * P) k =
      !Rule30UOR.Scale.response (z + twopow k) k := by
  have hd := periodic_response_defect_at_zero_diag_eq_lhCenter_twopow T P hP hper m z k ht hz hset0
  have h2 : (z + twopow k) + m * P = (z + 2) + twopow k := by omega
  rw [h2, lhCenter_twopow_after_zero_diag z k hz hset2] at hd
  rw [h2]
  revert hd
  cases Rule30UOR.Scale.response ((z + 2) + twopow k) k <;>
    cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem periodic_response_flip_at_zero_diag_step_two_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k : Nat) (hmP : m * P = 2) (ht : T ≤ z + twopow k)
    (hz : IsZeroDiag z)
    (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k)) :
    Rule30UOR.Scale.response ((z + twopow k) + m * P) k =
      !Rule30UOR.Scale.response (z + twopow k) k :=
  periodic_response_flip_at_zero_diag_step_two T P hP hper m z k hmP ht hz hset0 hset2

/-- **Unconditional `m * P`-Antiperiodicity of `response · k` Between Any Two Settled Zero Diagonals Separated by `z1 + m * P = z2 + 2` (`periodic_response_flip_of_two_zero_diags`, 9.979)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z1, z2, k ∈ ℕ` with `T ≤ z1 + twopow k`, `z1 + m * P = z2 + 2`, `IsZeroDiag z1`, `IsZeroDiag z2`, `settle z1 ≤ z1 + twopow k`, and `settle (z2 + 2) ≤ (z2 + 2) + twopow k` (with NO `z1 ≤ k` or `z2 ≤ k` bound!), `response ((z1 + twopow k) + m * P) k = !response (z1 + twopow k) k`! -/
theorem periodic_response_flip_of_two_zero_diags
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k : Nat) (ht : T ≤ z1 + twopow k) (hshift : z1 + m * P = z2 + 2)
    (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2)
    (hset1 : settle z1 ≤ z1 + twopow k)
    (hset2 : settle (z2 + 2) ≤ (z2 + 2) + twopow k) :
    Rule30UOR.Scale.response ((z1 + twopow k) + m * P) k =
      !Rule30UOR.Scale.response (z1 + twopow k) k := by
  have hd := periodic_response_defect_at_zero_diag_eq_lhCenter_twopow T P hP hper m z1 k ht hz1 hset1
  have h2 : (z1 + twopow k) + m * P = (z2 + 2) + twopow k := by omega
  rw [h2, lhCenter_twopow_after_zero_diag z2 k hz2 hset2] at hd
  rw [h2]
  revert hd
  cases Rule30UOR.Scale.response ((z2 + 2) + twopow k) k <;>
    cases Rule30UOR.Scale.response (z1 + twopow k) k <;> decide

theorem periodic_response_flip_of_two_zero_diags_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k : Nat) (ht : T ≤ z1 + twopow k) (hshift : z1 + m * P = z2 + 2)
    (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2)
    (hset1 : SettledBy z1 (z1 + twopow k))
    (hset2 : SettledBy (z2 + 2) ((z2 + 2) + twopow k)) :
    Rule30UOR.Scale.response ((z1 + twopow k) + m * P) k =
      !Rule30UOR.Scale.response (z1 + twopow k) k :=
  periodic_response_flip_of_two_zero_diags T P hP hper m z1 z2 k ht hshift hz1 hz2 hset1 hset2

/-- **Unconditional `m * P`-Equality of `response · k` Between Any Two Settled Zero Diagonals Separated by `z1 + m * P = z2` (`periodic_response_eq_of_two_zero_diags`, 9.980)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z1, z2, k ∈ ℕ` with `T ≤ z1 + twopow k`, `z1 + m * P = z2`, `IsZeroDiag z1`, `IsZeroDiag z2`, `settle z1 ≤ z1 + twopow k`, and `settle z2 ≤ z2 + twopow k` (with NO `z1 ≤ k` or `z2 ≤ k` bound!), `response ((z1 + twopow k) + m * P) k = response (z1 + twopow k) k`! -/
theorem periodic_response_eq_of_two_zero_diags
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k : Nat) (ht : T ≤ z1 + twopow k) (hshift : z1 + m * P = z2)
    (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2)
    (hset1 : settle z1 ≤ z1 + twopow k)
    (hset2 : settle z2 ≤ z2 + twopow k) :
    Rule30UOR.Scale.response ((z1 + twopow k) + m * P) k =
      Rule30UOR.Scale.response (z1 + twopow k) k := by
  have hd := periodic_response_defect_at_zero_diag_eq_lhCenter_twopow T P hP hper m z1 k ht hz1 hset1
  have h2 : (z1 + twopow k) + m * P = z2 + twopow k := by omega
  rw [h2, lhCenter_twopow_of_zero_diag z2 k hz2 hset2] at hd
  rw [h2]
  revert hd
  cases Rule30UOR.Scale.response (z2 + twopow k) k <;>
    cases Rule30UOR.Scale.response (z1 + twopow k) k <;> decide

theorem periodic_response_eq_of_two_zero_diags_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k : Nat) (ht : T ≤ z1 + twopow k) (hshift : z1 + m * P = z2)
    (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2)
    (hset1 : SettledBy z1 (z1 + twopow k))
    (hset2 : SettledBy z2 (z2 + twopow k)) :
    Rule30UOR.Scale.response ((z1 + twopow k) + m * P) k =
      Rule30UOR.Scale.response (z1 + twopow k) k :=
  periodic_response_eq_of_two_zero_diags T P hP hper m z1 z2 k ht hshift hz1 hz2 hset1 hset2

/-- **Universal-in-`Q` Inside-the-Cone Late `leftresponse` Shift-Defect Law Dropping `d + Q ≤ k` (`late_leftresponse_defect_eq_lhCenter_twopow_defect_cone`, 9.981)**:
    for EVERY shift `Q` and all `d, k ∈ ℕ` with `d + Q < twopow k` (dropping `d + Q ≤ k`!), `leftresponse ((d + twopow k) + Q) k ⊕ leftresponse (d + twopow k) k = (lhCenter ((d + twopow k) + Q) (twopow k) ⊕ lhCenter (d + twopow k) (twopow k)) ⊕ ((leftresponse (d + Q) (k + 1) ⊕ leftresponse d (k + 1)) ⊕ (leftresponse (d + Q) k ⊕ leftresponse d k))`! -/
theorem late_leftresponse_defect_eq_lhCenter_twopow_defect_cone
    (Q d k : Nat) (hcone : d + Q < twopow k) :
    bxor (Rule30UOR.Scale.leftresponse ((d + twopow k) + Q) k)
      (Rule30UOR.Scale.leftresponse (d + twopow k) k) =
      bxor
        (bxor (lhCenter ((d + twopow k) + Q) (twopow k))
          (lhCenter (d + twopow k) (twopow k)))
        (bxor
          (bxor (Rule30UOR.Scale.leftresponse (d + Q) (k + 1))
            (Rule30UOR.Scale.leftresponse d (k + 1)))
          (bxor (Rule30UOR.Scale.leftresponse (d + Q) k)
            (Rule30UOR.Scale.leftresponse d k))) := by
  have hc0 := lhCenter_twopow_eq_leftresponse_coboundary_cone d k (by omega)
  have hc1 := lhCenter_twopow_eq_leftresponse_coboundary_cone (d + Q) k hcone
  rw [show (d + Q) + twopow k = (d + twopow k) + Q by omega] at hc1
  rw [hc1, hc0]
  cases Rule30UOR.Scale.leftresponse (d + Q) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + Q) k <;>
    cases Rule30UOR.Scale.leftresponse d k <;>
    cases Rule30UOR.Scale.leftresponse ((d + twopow k) + Q) k <;>
    cases Rule30UOR.Scale.leftresponse (d + twopow k) k <;> rfl

/-! ### Batch 46: `maskcount`/`maskparity`/`leftresponse`/`response` Determination from First-Bit `maskparity · 0` and White-Center Column-`1` Agreement & Unconditional Dyadic Scale-Step Laws Along Settled and Doubling Left Diagonals (9.982–9.996) -/

/-- **Exact Identification of `carry60 t 0` with the First-Bit White-Center Readout `maskparity t 0`**:
    for every `t ∈ ℕ`, `carry60 t 0 = maskparity t 0`! -/
theorem carry60_zero_eq_maskparity_zero (t : Nat) :
    Rule30UOR.Core.carry60 t 0 = Rule30UOR.Scale.maskparity t 0 := by
  show Rule30UOR.Core.carry60 t 0 = xor false (Rule30UOR.Core.carry60 (t + 0) 0)
  rw [Nat.add_zero]
  cases Rule30UOR.Core.carry60 t 0 <;> rfl

/-- **Exact Recurrence of `maskcount t (n + 1)` via the First-Bit White-Center Readout `maskparity (t + n) 0` (`maskcount_succ_eq_xor_maskparity_zero`, 9.982)**:
    for every `t, n ∈ ℕ`, `maskcount t (n + 1) = bxor (maskcount t n) (maskparity (t + n) 0)`! -/
theorem maskcount_succ_eq_xor_maskparity_zero (t n : Nat) :
    Rule30UOR.Scale.maskcount t (n + 1) =
      bxor (Rule30UOR.Scale.maskcount t n) (Rule30UOR.Scale.maskparity (t + n) 0) := by
  rw [bxor_eq_xor, ← carry60_zero_eq_maskparity_zero (t + n)]
  rfl

/-- **Universal-in-`Q` Determination of `maskcount · n` from First-Bit `maskparity · 0` Agreement (`maskcount_eq_of_maskparity_zero_agree`, 9.983)**:
    for every shift `Q` and all `t, n ∈ ℕ`, if `∀ s < n, maskparity ((t + s) + Q) 0 = maskparity (t + s) 0`, then `maskcount (t + Q) n = maskcount t n`! -/
theorem maskcount_eq_of_maskparity_zero_agree (t Q : Nat) : ∀ n : Nat,
    (∀ s : Nat, s < n →
      Rule30UOR.Scale.maskparity ((t + s) + Q) 0 = Rule30UOR.Scale.maskparity (t + s) 0) →
    Rule30UOR.Scale.maskcount (t + Q) n = Rule30UOR.Scale.maskcount t n
  | 0, _ => rfl
  | n + 1, h => by
    show xor (Rule30UOR.Scale.maskcount (t + Q) n) (Rule30UOR.Core.carry60 ((t + Q) + n) 0) =
      xor (Rule30UOR.Scale.maskcount t n) (Rule30UOR.Core.carry60 (t + n) 0)
    rw [maskcount_eq_of_maskparity_zero_agree t Q n (fun s hs => h s (by omega)),
      show (t + Q) + n = (t + n) + Q by omega,
      carry60_zero_eq_maskparity_zero ((t + n) + Q),
      carry60_zero_eq_maskparity_zero (t + n),
      h n (by omega)]

/-- **Universal-in-`Q` Determination of `maskparity · k` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` (`maskparity_eq_of_maskparity_zero_agree`, 9.984)**:
    for every shift `Q` and all `t, k, S ∈ ℕ` with `twopow k ≤ S + 1`, if `∀ s ≤ S, maskparity ((t + s) + Q) 0 = maskparity (t + s) 0`, then `maskparity (t + Q) k = maskparity t k`! -/
theorem maskparity_eq_of_maskparity_zero_agree (t Q k S : Nat) (hS : twopow k ≤ S + 1)
    (hm : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + Q) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.maskparity (t + Q) k = Rule30UOR.Scale.maskparity t k := by
  unfold Rule30UOR.Scale.maskparity
  exact maskcount_eq_of_maskparity_zero_agree t Q (twopow k) (fun s hs => hm s (by omega))

/-- **Producing `maskparity (t + m * P) k = maskparity t k` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`periodic_maskparity_eq_of_white_center_rhCenter_one_twopow`, 9.985)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1`, then `maskparity (t + m * P) k = maskparity t k`! -/
theorem periodic_maskparity_eq_of_white_center_rhCenter_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    Rule30UOR.Scale.maskparity (t + m * P) k = Rule30UOR.Scale.maskparity t k := by
  apply maskparity_eq_of_maskparity_zero_agree t (m * P) k S hS
  intro s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega)
    (periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + s) (by omega) (hw s hs))

/-- **Producing `leftresponse (t + m * P) k = leftresponse t k` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`periodic_leftresponse_eq_of_white_center_rhCenter_one_twopow`, 9.986)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1`, then `leftresponse (t + m * P) k = leftresponse t k`! -/
theorem periodic_leftresponse_eq_of_white_center_rhCenter_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    Rule30UOR.Scale.leftresponse (t + m * P) k = Rule30UOR.Scale.leftresponse t k := by
  have hd := periodic_maskparity_defect_eq_leftresponse_defect_of_white_center_rhCenter_one_twopow
    T P hP hper m t k S ht hS hw
  have hm := periodic_maskparity_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m t k S ht hS hw
  rw [hm] at hd
  revert hd
  cases Rule30UOR.Scale.maskparity t k <;>
    cases Rule30UOR.Scale.leftresponse (t + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;> decide

/-- **Producing `leftresponse (t + m * P) k = leftresponse t k` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` (`periodic_leftresponse_eq_of_maskparity_zero_agree_twopow`, 9.987)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `∀ s ≤ S, maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`, then `leftresponse (t + m * P) k = leftresponse t k`! -/
theorem periodic_leftresponse_eq_of_maskparity_zero_agree_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hm : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.leftresponse (t + m * P) k = Rule30UOR.Scale.leftresponse t k := by
  have hband := periodic_lhBandAgree_zero_of_maskparity_zero_agree T P hP hper m t S ht hm
  have hd := periodic_maskparity_defect_eq_leftresponse_defect_of_lhBandAgree_twopow
    T P hP hper m t k 0 (S + 1) ht (by omega) (by omega) hband
  have hmk := maskparity_eq_of_maskparity_zero_agree t (m * P) k S hS hm
  rw [hmk] at hd
  revert hd
  cases Rule30UOR.Scale.maskparity t k <;>
    cases Rule30UOR.Scale.leftresponse (t + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;> decide

/-- **Producing `response (t + m * P) k = response t k` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` (`periodic_response_eq_of_maskparity_zero_agree_twopow`, 9.988)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `∀ s ≤ S, maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`, then `response (t + m * P) k = response t k`! -/
theorem periodic_response_eq_of_maskparity_zero_agree_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hm : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k := by
  exact periodic_response_eq_of_lhBandAgree_twopow T P hP hper m t k 0 (S + 1) ht
    (by omega) (by omega)
    (periodic_lhBandAgree_zero_of_maskparity_zero_agree T P hP hper m t S ht hm)

/-- **Producing `leftresponse (t + m * P) k = leftresponse t k` from `LhColAgree t (m * P) 1 S` Over `2^k ≤ S + 1` (`periodic_leftresponse_eq_of_lhColAgree_one_twopow`, 9.989)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `LhColAgree t (m * P) 1 S` holds, then `leftresponse (t + m * P) k = leftresponse t k`! -/
theorem periodic_leftresponse_eq_of_lhColAgree_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    Rule30UOR.Scale.leftresponse (t + m * P) k = Rule30UOR.Scale.leftresponse t k := by
  apply periodic_leftresponse_eq_of_maskparity_zero_agree_twopow T P hP hper m t k S ht hS
  intro s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) (hlh s hs)

/-- **Producing `maskparity (t + m * P) k = maskparity t k` from `LhColAgree t (m * P) 1 S` Over `2^k ≤ S + 1` (`periodic_maskparity_eq_of_lhColAgree_one_twopow`, 9.990)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `LhColAgree t (m * P) 1 S` holds, then `maskparity (t + m * P) k = maskparity t k`! -/
theorem periodic_maskparity_eq_of_lhColAgree_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    Rule30UOR.Scale.maskparity (t + m * P) k = Rule30UOR.Scale.maskparity t k := by
  apply maskparity_eq_of_maskparity_zero_agree t (m * P) k S hS
  intro s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) (hlh s hs)

/-- **Producing `response (t + m * P) k = response t k` from `LhColAgree t (m * P) 1 S` Over `2^k ≤ S + 1` (`periodic_response_eq_of_lhColAgree_one_twopow`, 9.991)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, S ∈ ℕ` with `T ≤ t` and `twopow k ≤ S + 1`, if `LhColAgree t (m * P) 1 S` holds, then `response (t + m * P) k = response t k`! -/
theorem periodic_response_eq_of_lhColAgree_one_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (ht : T ≤ t) (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    Rule30UOR.Scale.response (t + m * P) k = Rule30UOR.Scale.response t k := by
  apply periodic_response_eq_of_maskparity_zero_agree_twopow T P hP hper m t k S ht hS
  intro s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) (hlh s hs)

/-- **Unconditional Identification of `lhCenter (d + 2^k) (2^k)` with `ldiag d (d + 2^k)` Without `d ≤ k` (`lhCenter_twopow_eq_ldiag`, 9.992)**:
    for EVERY `d, k ∈ ℕ` (with NO `d ≤ k` bound!), `lhCenter (d + twopow k) (twopow k) = ldiag d (d + twopow k)`! -/
theorem lhCenter_twopow_eq_ldiag (d k : Nat) :
    lhCenter (d + twopow k) (twopow k) = ldiag d (d + twopow k) := by
  rw [lhCenter_eq_ldiag (d + twopow k) (twopow k) (by omega),
    show (d + twopow k) - twopow k = d by omega]

/-- **Settled Dyadic Left Wing Equals the Zero-State Center `zcenter d` (`lhCenter_twopow_settled_eq_zcenter`, 9.993)**:
    for every `d, k ∈ ℕ` with `d ≤ k` and `settle d ≤ d + twopow k`, `lhCenter (d + twopow k) (twopow k) = zcenter d`! -/
theorem lhCenter_twopow_settled_eq_zcenter (d k : Nat)
    (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    lhCenter (d + twopow k) (twopow k) = zcenter d := by
  rw [lhCenter_twopow_eq_ldiag d k]
  exact ldiag_settled_eq_zcenter d k hk hset

theorem lhCenter_twopow_settled_eq_zcenter_prop (d k : Nat)
    (hk : d ≤ k) (hset : SettledBy d (d + twopow k)) :
    ZCenterEq d (lhCenter (d + twopow k) (twopow k)) :=
  (lhCenter_twopow_settled_eq_zcenter d k hk hset).symm

/-- **Scale-Step Invariance of the Settled Dyadic Left Wing `lhCenter (d + 2^k) (2^k)` (`lhCenter_twopow_settled_scale_invariant`, 9.994)**:
    for every `d, k ∈ ℕ` with `d ≤ k` and `settle d ≤ d + twopow k`, `lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k)`! -/
theorem lhCenter_twopow_settled_scale_invariant (d k : Nat)
    (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k) := by
  have h1 := lhCenter_twopow_settled_eq_zcenter d (k + 1) (by omega)
    (by rw [Rule30UOR.Core.twopow_succ]; omega)
  have h0 := lhCenter_twopow_settled_eq_zcenter d k hk hset
  rw [h1, h0]

theorem lhCenter_twopow_settled_scale_invariant_prop (d k : Nat)
    (hk : d ≤ k) (hset : SettledBy d (d + twopow k)) :
    lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k) :=
  lhCenter_twopow_settled_scale_invariant d k hk hset

/-- **Unconditional Scale-Step Invariance of `lhCenter (d + 2^k) (2^k)` Below Any Dyadic Doubling Threshold `z` Without `d ≤ k` (`lhCenter_twopow_succ_periodic_of_doubles_le`, 9.995)**:
    for EVERY `z, d, k ∈ ℕ` with `DoublesAt (twopow k) z`, `d ≤ z`, and `settle d ≤ d + twopow k` (with NO `d ≤ k` bound!), `lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k)`! -/
theorem lhCenter_twopow_succ_periodic_of_doubles_le (z d k : Nat)
    (hd : DoublesAt (twopow k) z) (hdz : d ≤ z)
    (hset : settle d ≤ d + twopow k) :
    lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k) := by
  rw [lhCenter_twopow_eq_ldiag d (k + 1), lhCenter_twopow_eq_ldiag d k,
    show d + twopow (k + 1) = (d + twopow k) + twopow k by
      rw [Rule30UOR.Core.twopow_succ]; omega]
  exact ldiag_settled_periodic_of_doubles_le (twopow k) z d (d + twopow k) hd hdz hset

theorem lhCenter_twopow_succ_periodic_of_doubles_le_prop (z d k : Nat)
    (hd : DoublesAt (twopow k) z) (hdz : d ≤ z)
    (hset : SettledBy d (d + twopow k)) :
    lhCenter (d + twopow (k + 1)) (twopow (k + 1)) = lhCenter (d + twopow k) (twopow k) :=
  lhCenter_twopow_succ_periodic_of_doubles_le z d k hd hdz hset

/-- **Unconditional Dyadic Left-Wing Scale-Step Flip Along the Reset Diagonal `z + 3` Without `z ≤ k` (`lhCenter_twopow_reset_succ_antiperiodic_of_doubles`, 9.996)**:
    for EVERY `z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, and `settle (z + 3) ≤ (z + 3) + twopow k` (with NO `z ≤ k` bound!), `lhCenter ((z + 3) + twopow (k + 1)) (twopow (k + 1)) = !lhCenter ((z + 3) + twopow k) (twopow k)`! -/
theorem lhCenter_twopow_reset_succ_antiperiodic_of_doubles (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : settle (z + 3) ≤ (z + 3) + twopow k) :
    lhCenter ((z + 3) + twopow (k + 1)) (twopow (k + 1)) =
      !lhCenter ((z + 3) + twopow k) (twopow k) := by
  rw [lhCenter_twopow_eq_ldiag (z + 3) (k + 1), lhCenter_twopow_eq_ldiag (z + 3) k,
    show (z + 3) + twopow (k + 1) = ((z + 3) + twopow k) + twopow k by
      rw [Rule30UOR.Core.twopow_succ]; omega]
  exact ldiag_settled_reset_antiperiodic_of_doubles (twopow k) z ((z + 3) + twopow k) hz hd hset

theorem lhCenter_twopow_reset_succ_antiperiodic_of_doubles_prop (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : SettledBy (z + 3) ((z + 3) + twopow k)) :
    lhCenter ((z + 3) + twopow (k + 1)) (twopow (k + 1)) =
      !lhCenter ((z + 3) + twopow k) (twopow k) :=
  lhCenter_twopow_reset_succ_antiperiodic_of_doubles z k hz hd hset

/-! ### Batch 47: Unconditional Late Dyadic Scale Laws Along Settled & Doubling Left Diagonals Without `d ≤ k` & Dyadic `2^k`-Window Refutations of `CenterPeriodic` at Cone Boundary, Zero-Diagonal, and Doubling Points (9.997–9.1011) -/

/-- **Unconditional Identification of `lhCenter (d + 2^k) (2^k)` with the Late Rule-60 Scale Increment Without `d ≤ k` (`lhCenter_twopow_eq_late_scale_center`, 9.997)**:
    for EVERY `d, k ∈ ℕ` (with NO `d ≤ k` bound and NO `SettledBy` hypothesis!), `lhCenter (d + twopow k) (twopow k) = (center (d + twopow (k + 1)) ⊕ center (d + twopow k)) ⊕ response (d + twopow k) k`! -/
theorem lhCenter_twopow_eq_late_scale_center (d k : Nat) :
    lhCenter (d + twopow k) (twopow k) =
      bxor (bxor (Rule30UOR.Core.center (d + twopow (k + 1)))
        (Rule30UOR.Core.center (d + twopow k)))
        (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hs := scale_center_lhCenter (d + twopow k) k
  have h2 : (d + twopow k) + twopow k = d + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [h2] at hs
  revert hs
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Core.center (d + twopow (k + 1)) <;>
    cases Rule30UOR.Core.center (d + twopow k) <;>
    cases lhCenter (d + twopow k) (twopow k) <;>
    cases Rule30UOR.Scale.response (d + twopow k) k <;> decide

/-- **Unconditional Scale-Step Invariance of the Late Rule-60 Scale Increment Below a Dyadic Doubling Threshold `z` Without `d ≤ k` (`late_scale_center_periodic_of_doubles_le`, 9.998)**:
    for EVERY `z, d, k ∈ ℕ` with `DoublesAt (twopow k) z`, `d ≤ z`, and `settle d ≤ d + twopow k` (with NO `d ≤ k` bound!), `(center (d + 2^(k+2)) ⊕ center (d + 2^(k+1))) ⊕ response (d + 2^(k+1)) (k + 1) = (center (d + 2^(k+1)) ⊕ center (d + 2^k)) ⊕ response (d + 2^k) k`! -/
theorem late_scale_center_periodic_of_doubles_le (z d k : Nat)
    (hd : DoublesAt (twopow k) z) (hdz : d ≤ z)
    (hset : settle d ≤ d + twopow k) :
    bxor (bxor (Rule30UOR.Core.center (d + twopow (k + 2)))
      (Rule30UOR.Core.center (d + twopow (k + 1))))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    bxor (bxor (Rule30UOR.Core.center (d + twopow (k + 1)))
      (Rule30UOR.Core.center (d + twopow k)))
      (Rule30UOR.Scale.response (d + twopow k) k) := by
  rw [← lhCenter_twopow_eq_late_scale_center d (k + 1),
    ← lhCenter_twopow_eq_late_scale_center d k]
  exact lhCenter_twopow_succ_periodic_of_doubles_le z d k hd hdz hset

theorem late_scale_center_periodic_of_doubles_le_prop (z d k : Nat)
    (hd : DoublesAt (twopow k) z) (hdz : d ≤ z)
    (hset : SettledBy d (d + twopow k)) :
    bxor (bxor (Rule30UOR.Core.center (d + twopow (k + 2)))
      (Rule30UOR.Core.center (d + twopow (k + 1))))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    bxor (bxor (Rule30UOR.Core.center (d + twopow (k + 1)))
      (Rule30UOR.Core.center (d + twopow k)))
      (Rule30UOR.Scale.response (d + twopow k) k) :=
  late_scale_center_periodic_of_doubles_le z d k hd hdz hset

/-- **Unconditional Scale-Step Flip of the Late Rule-60 Scale Increment Along `z + 1` at a Dyadic Doubling Zero Diagonal `z` Without `z ≤ k` (`late_scale_center_antiperiodic_of_doubles`, 9.999)**:
    for EVERY `z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, and `settle (z + 1) ≤ (z + 1) + twopow k` (with NO `z ≤ k` bound!), `(center ((z + 1) + 2^(k+2)) ⊕ center ((z + 1) + 2^(k+1))) ⊕ response ((z + 1) + 2^(k+1)) (k + 1) = !((center ((z + 1) + 2^(k+1)) ⊕ center ((z + 1) + 2^k)) ⊕ response ((z + 1) + 2^k) k)`! -/
theorem late_scale_center_antiperiodic_of_doubles (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : settle (z + 1) ≤ (z + 1) + twopow k) :
    bxor (bxor (Rule30UOR.Core.center ((z + 1) + twopow (k + 2)))
      (Rule30UOR.Core.center ((z + 1) + twopow (k + 1))))
      (Rule30UOR.Scale.response ((z + 1) + twopow (k + 1)) (k + 1)) =
    !bxor (bxor (Rule30UOR.Core.center ((z + 1) + twopow (k + 1)))
      (Rule30UOR.Core.center ((z + 1) + twopow k)))
      (Rule30UOR.Scale.response ((z + 1) + twopow k) k) := by
  rw [← lhCenter_twopow_eq_late_scale_center (z + 1) (k + 1),
    ← lhCenter_twopow_eq_late_scale_center (z + 1) k]
  exact lhCenter_twopow_succ_antiperiodic_of_doubles z k hz hd hset

theorem late_scale_center_antiperiodic_of_doubles_prop (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : SettledBy (z + 1) ((z + 1) + twopow k)) :
    bxor (bxor (Rule30UOR.Core.center ((z + 1) + twopow (k + 2)))
      (Rule30UOR.Core.center ((z + 1) + twopow (k + 1))))
      (Rule30UOR.Scale.response ((z + 1) + twopow (k + 1)) (k + 1)) =
    !bxor (bxor (Rule30UOR.Core.center ((z + 1) + twopow (k + 1)))
      (Rule30UOR.Core.center ((z + 1) + twopow k)))
      (Rule30UOR.Scale.response ((z + 1) + twopow k) k) :=
  late_scale_center_antiperiodic_of_doubles z k hz hd hset

/-- **Unconditional Scale-Step Flip of the Late Rule-60 Scale Increment Along the Reset Diagonal `z + 3` Without `z ≤ k` (`late_scale_center_reset_antiperiodic_of_doubles`, 9.1000)**:
    for EVERY `z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, and `settle (z + 3) ≤ (z + 3) + twopow k` (with NO `z ≤ k` bound!), `(center ((z + 3) + 2^(k+2)) ⊕ center ((z + 3) + 2^(k+1))) ⊕ response ((z + 3) + 2^(k+1)) (k + 1) = !((center ((z + 3) + 2^(k+1)) ⊕ center ((z + 3) + 2^k)) ⊕ response ((z + 3) + 2^k) k)`! -/
theorem late_scale_center_reset_antiperiodic_of_doubles (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : settle (z + 3) ≤ (z + 3) + twopow k) :
    bxor (bxor (Rule30UOR.Core.center ((z + 3) + twopow (k + 2)))
      (Rule30UOR.Core.center ((z + 3) + twopow (k + 1))))
      (Rule30UOR.Scale.response ((z + 3) + twopow (k + 1)) (k + 1)) =
    !bxor (bxor (Rule30UOR.Core.center ((z + 3) + twopow (k + 1)))
      (Rule30UOR.Core.center ((z + 3) + twopow k)))
      (Rule30UOR.Scale.response ((z + 3) + twopow k) k) := by
  rw [← lhCenter_twopow_eq_late_scale_center (z + 3) (k + 1),
    ← lhCenter_twopow_eq_late_scale_center (z + 3) k]
  exact lhCenter_twopow_reset_succ_antiperiodic_of_doubles z k hz hd hset

theorem late_scale_center_reset_antiperiodic_of_doubles_prop (z k : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hset : SettledBy (z + 3) ((z + 3) + twopow k)) :
    bxor (bxor (Rule30UOR.Core.center ((z + 3) + twopow (k + 2)))
      (Rule30UOR.Core.center ((z + 3) + twopow (k + 1))))
      (Rule30UOR.Scale.response ((z + 3) + twopow (k + 1)) (k + 1)) =
    !bxor (bxor (Rule30UOR.Core.center ((z + 3) + twopow (k + 1)))
      (Rule30UOR.Core.center ((z + 3) + twopow k)))
      (Rule30UOR.Scale.response ((z + 3) + twopow k) k) :=
  late_scale_center_reset_antiperiodic_of_doubles z k hz hd hset

/-- **Scale-Step Invariance of the Late `response` Shift Defect Below a Dyadic Doubling Threshold `z` Without `z ≤ k` (`periodic_late_response_defect_eq_of_doubles_le`, 9.1001)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `DoublesAt (twopow k) z`, `d + m * P ≤ z`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (d + m * P) ≤ (d + m * P) + twopow k` (with NO `z ≤ k` bound!), `response ((d + twopow (k + 1)) + m * P) (k + 1) ⊕ response (d + twopow (k + 1)) (k + 1) = response ((d + twopow k) + m * P) k ⊕ response (d + twopow k) k`! -/
theorem periodic_late_response_defect_eq_of_doubles_le
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hd : DoublesAt (twopow k) z) (hdz : d + m * P ≤ z)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset1 : settle (d + m * P) ≤ (d + m * P) + twopow k) :
    bxor (Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    bxor (Rule30UOR.Scale.response ((d + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hr0 := (periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (d + twopow k) k ht).symm
  have hr1 := (periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (d + twopow (k + 1)) (k + 1)
    (by rw [Rule30UOR.Core.twopow_succ]; omega)).symm
  have hp0 := lhCenter_twopow_succ_periodic_of_doubles_le z d k hd (by omega) hset0
  have hp1 := lhCenter_twopow_succ_periodic_of_doubles_le z (d + m * P) k hd hdz hset1
  rw [show (d + twopow k) + m * P = (d + m * P) + twopow k by omega] at hr0 ⊢
  rw [show (d + twopow (k + 1)) + m * P = (d + m * P) + twopow (k + 1) by omega] at hr1 ⊢
  rw [hr1, hr0, hp0, hp1]

theorem periodic_late_response_defect_eq_of_doubles_le_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hd : DoublesAt (twopow k) z) (hdz : d + m * P ≤ z)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset1 : SettledBy (d + m * P) ((d + m * P) + twopow k)) :
    bxor (Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    bxor (Rule30UOR.Scale.response ((d + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + twopow k) k) :=
  periodic_late_response_defect_eq_of_doubles_le T P hP hper m d z k hd hdz ht hset0 hset1

/-- **Scale-Step Flip of the Late `response` Shift Defect Across a Dyadic Doubling Zero Diagonal `z` Without `z ≤ k` or `DoublesAt (m * P) z` (`periodic_late_response_defect_flip_of_doubles`, 9.1002)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (z + 1) ≤ (z + 1) + twopow k` (requiring ONLY `DoublesAt (twopow k) z`, NOT `DoublesAt (m * P) z` and NOT `z ≤ k`!), `response ((d + twopow (k + 1)) + m * P) (k + 1) ⊕ response (d + twopow (k + 1)) (k + 1) = !(response ((d + twopow k) + m * P) k ⊕ response (d + twopow k) k)`! -/
theorem periodic_late_response_defect_flip_of_doubles
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k) :
    bxor (Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    !bxor (Rule30UOR.Scale.response ((d + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hr0 := (periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (d + twopow k) k ht).symm
  have hr1 := (periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (d + twopow (k + 1)) (k + 1)
    (by rw [Rule30UOR.Core.twopow_succ]; omega)).symm
  have hp0 := lhCenter_twopow_succ_periodic_of_doubles_le z d k hd hdz hset0
  have hp1 := lhCenter_twopow_succ_antiperiodic_of_doubles z k hz hd hset1
  rw [show (d + twopow k) + m * P = (z + 1) + twopow k by omega] at hr0 ⊢
  rw [show (d + twopow (k + 1)) + m * P = (z + 1) + twopow (k + 1) by omega] at hr1 ⊢
  rw [hr1, hr0, hp0, hp1, bxor_eq_xor, bxor_eq_xor]
  cases lhCenter ((z + 1) + twopow k) (twopow k) <;>
    cases lhCenter (d + twopow k) (twopow k) <;> decide

theorem periodic_late_response_defect_flip_of_doubles_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k)) :
    bxor (Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    !bxor (Rule30UOR.Scale.response ((d + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + twopow k) k) :=
  periodic_late_response_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset1

/-- **Scale-Step `response` Inversion at `k + 1` from Scale-`k` Agreement Across a Dyadic Doubling Zero Diagonal `z` (`periodic_late_response_flip_of_doubles_and_eq`, 9.1003)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (z + 1) ≤ (z + 1) + twopow k`, if `response ((d + twopow k) + m * P) k = response (d + twopow k) k`, then `response ((d + twopow (k + 1)) + m * P) (k + 1) = !response (d + twopow (k + 1)) (k + 1)`! -/
theorem periodic_late_response_flip_of_doubles_and_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hreq : Rule30UOR.Scale.response ((d + twopow k) + m * P) k =
      Rule30UOR.Scale.response (d + twopow k) k) :
    Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1) =
      !Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) := by
  have hf := periodic_late_response_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset1
  rw [hreq] at hf
  revert hf
  rw [bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.response (d + twopow k) k <;>
    cases Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1) <;>
    cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem periodic_late_response_flip_of_doubles_and_eq_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hreq : Rule30UOR.Scale.response ((d + twopow k) + m * P) k =
      Rule30UOR.Scale.response (d + twopow k) k) :
    Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1) =
      !Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) :=
  periodic_late_response_flip_of_doubles_and_eq T P hP hper m d z k hz hd hdz hdm ht hset0 hset1 hreq

/-- **Refuting `CenterPeriodic` at the Dyadic Cone Boundary `t + m * P = 2^k` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`not_centerPeriodic_of_white_center_rhCenter_one_at_twopow`, 9.1004)**:
    for every `T, P, m, t, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = twopow k`, and `twopow k ≤ S + 1`, if `∀ s ≤ S, center (t + s) = false → rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_at_twopow
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hcone : t + m * P = twopow k) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m t k S ht hS hw
  have hflip := periodic_response_flip_at_twopow_mul T P hP hper m t k hm ht hcone
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response t k <;> decide

/-- **Refuting `CenterPeriodic` at the Dyadic Cone Boundary `t + m * P = 2^k` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` (`not_centerPeriodic_of_maskparity_zero_agree_at_twopow`, 9.1005)**:
    for every `T, P, m, t, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = twopow k`, and `twopow k ≤ S + 1`, if `∀ s ≤ S, maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hcone : t + m * P = twopow k) (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m t k S ht hS hmp
  have hflip := periodic_response_flip_at_twopow_mul T P hP hper m t k hm ht hcone
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response t k <;> decide

/-- **Refuting `CenterPeriodic` at `z + 2^k` for `m * P = 2` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` Without `z`-Horizon Growth (`not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_step_two`, 9.1006)**:
    for every `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `m * P = 2`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + 2) ≤ (z + 2) + twopow k`, and `twopow k ≤ S + 1`, if white-center column-`1` agreement holds over `[z + twopow k, (z + twopow k) + S]`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_step_two
    (T P m z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k)
    (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + twopow k) + s) = false →
        rhCenter (((z + twopow k) + s) + m * P) 1 = rhCenter ((z + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m (z + twopow k) k S ht hS hw
  have hflip := periodic_response_flip_at_zero_diag_step_two
    T P hP hper m z k hm ht hz hset0 hset2
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_step_two_prop
    (T P m z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + twopow k) + s) = false →
        rhCenter (((z + twopow k) + s) + m * P) 1 = rhCenter ((z + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_step_two
    T P m z k S hP hz hm ht hset0 hset2 hS hw

/-- **Refuting `CenterPeriodic` at `z + 2^k` for `m * P = 2` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` Without `z`-Horizon Growth (`not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_step_two`, 9.1007)**:
    for every `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `m * P = 2`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + 2) ≤ (z + 2) + twopow k`, and `twopow k ≤ S + 1`, if `maskparity · 0` agreement holds over `[z + twopow k, (z + twopow k) + S]`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_step_two
    (T P m z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k)
    (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m (z + twopow k) k S ht hS hmp
  have hflip := periodic_response_flip_at_zero_diag_step_two
    T P hP hper m z k hm ht hz hset0 hset2
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_step_two_prop
    (T P m z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_step_two
    T P m z k S hP hz hm ht hset0 hset2 hS hmp

/-- **Refuting `CenterPeriodic` at `z + 2^k` from Two Zero Diagonals and White-Center Column-`1` Agreement Over `2^k ≤ S + 1` Without `z`-Horizon Growth (`not_centerPeriodic_of_white_center_rhCenter_one_of_two_zero_diags`, 9.1008)**:
    for every `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + m * P) ≤ (z + m * P) + twopow k`, and `twopow k ≤ S + 1`, if white-center column-`1` agreement holds over `[z + twopow k, (z + twopow k) + S]`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_of_two_zero_diags
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k) (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + twopow k) + s) = false →
        rhCenter (((z + twopow k) + s) + m * P) 1 = rhCenter ((z + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m (z + twopow k) k S ht hS hw
  have hflip := periodic_response_flip_of_two_zero_diags
    T P hP hper m z ((z + m * P) - 2) k ht (by omega) hz0 hz1 hset0
    (by rw [show ((z + m * P) - 2) + 2 = z + m * P by omega]; exact hset1)
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem not_centerPeriodic_of_white_center_rhCenter_one_of_two_zero_diags_prop
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k) (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + twopow k) + s) = false →
        rhCenter (((z + twopow k) + s) + m * P) 1 = rhCenter ((z + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_of_two_zero_diags
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hw

/-- **Refuting `CenterPeriodic` at `z + 2^k` from Two Zero Diagonals and First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` Without `z`-Horizon Growth (`not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags`, 9.1009)**:
    for every `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + m * P) ≤ (z + m * P) + twopow k`, and `twopow k ≤ S + 1`, if `maskparity · 0` agreement holds over `[z + twopow k, (z + twopow k) + S]`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k) (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m (z + twopow k) k S ht hS hmp
  have hflip := periodic_response_flip_of_two_zero_diags
    T P hP hper m z ((z + m * P) - 2) k ht (by omega) hz0 hz1 hset0
    (by rw [show ((z + m * P) - 2) + 2 = z + m * P by omega]; exact hset1)
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k) (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hmp

/-- **Two-Scale Refutation of `CenterPeriodic` Across ANY Dyadic Doubling Zero Diagonal `z` (`DoublesAt (twopow k) z`) from White-Center Column-`1` Agreement Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_white_center_rhCenter_one_scale_step_doubles`, 9.1010)**:
    for every `T, P, m, d, z, k, S0, S1 ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 1) ≤ (z + 1) + twopow k`, `twopow k ≤ S0 + 1`, and `twopow (k + 1) ≤ S1 + 1`, if white-center column-`1` agreement holds at `d + twopow k` over `S0` and at `d + twopow (k + 1)` over `S1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_scale_step_doubles
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hS0 : twopow k ≤ S0 + 1) (hS1 : twopow (k + 1) ≤ S1 + 1)
    (hw0 : ∀ s : Nat, s ≤ S0 →
      Rule30UOR.Core.center ((d + twopow k) + s) = false →
        rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1)
    (hw1 : ∀ s : Nat, s ≤ S1 →
      Rule30UOR.Core.center ((d + twopow (k + 1)) + s) = false →
        rhCenter (((d + twopow (k + 1)) + s) + m * P) 1 = rhCenter ((d + twopow (k + 1)) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq0 := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m (d + twopow k) k S0 ht hS0 hw0
  have heq1 := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m (d + twopow (k + 1)) (k + 1) S1
    (by rw [Rule30UOR.Core.twopow_succ]; omega) hS1 hw1
  have hflip := periodic_late_response_flip_of_doubles_and_eq
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset1 heq0
  rw [heq1] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem not_centerPeriodic_of_white_center_rhCenter_one_scale_step_doubles_prop
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hS0 : twopow k ≤ S0 + 1) (hS1 : twopow (k + 1) ≤ S1 + 1)
    (hw0 : ∀ s : Nat, s ≤ S0 →
      Rule30UOR.Core.center ((d + twopow k) + s) = false →
        rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1)
    (hw1 : ∀ s : Nat, s ≤ S1 →
      Rule30UOR.Core.center ((d + twopow (k + 1)) + s) = false →
        rhCenter (((d + twopow (k + 1)) + s) + m * P) 1 = rhCenter ((d + twopow (k + 1)) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_scale_step_doubles
    T P m d z k S0 S1 hP hz hd hdz hdm ht hset0 hset1 hS0 hS1 hw0 hw1

/-- **Two-Scale Refutation of `CenterPeriodic` Across ANY Dyadic Doubling Zero Diagonal `z` (`DoublesAt (twopow k) z`) from First-Bit `maskparity · 0` Agreement Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_maskparity_zero_agree_scale_step_doubles`, 9.1011)**:
    for every `T, P, m, d, z, k, S0, S1 ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 1) ≤ (z + 1) + twopow k`, `twopow k ≤ S0 + 1`, and `twopow (k + 1) ≤ S1 + 1`, if `maskparity · 0` agreement holds at `d + twopow k` over `S0` and at `d + twopow (k + 1)` over `S1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_scale_step_doubles
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hS0 : twopow k ≤ S0 + 1) (hS1 : twopow (k + 1) ≤ S1 + 1)
    (hm0 : ∀ s : Nat, s ≤ S0 →
      Rule30UOR.Scale.maskparity (((d + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow k) + s) 0)
    (hm1 : ∀ s : Nat, s ≤ S1 →
      Rule30UOR.Scale.maskparity (((d + twopow (k + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow (k + 1)) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq0 := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m (d + twopow k) k S0 ht hS0 hm0
  have heq1 := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m (d + twopow (k + 1)) (k + 1) S1
    (by rw [Rule30UOR.Core.twopow_succ]; omega) hS1 hm1
  have hflip := periodic_late_response_flip_of_doubles_and_eq
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset1 heq0
  rw [heq1] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem not_centerPeriodic_of_maskparity_zero_agree_scale_step_doubles_prop
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hS0 : twopow k ≤ S0 + 1) (hS1 : twopow (k + 1) ≤ S1 + 1)
    (hm0 : ∀ s : Nat, s ≤ S0 →
      Rule30UOR.Scale.maskparity (((d + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow k) + s) 0)
    (hm1 : ∀ s : Nat, s ≤ S1 →
      Rule30UOR.Scale.maskparity (((d + twopow (k + 1)) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow (k + 1)) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_scale_step_doubles
    T P m d z k S0 S1 hP hz hd hdz hdm ht hset0 hset1 hS0 hS1 hm0 hm1

/-! ### Batch 48: Strict Exponential Growth `n < 2^n`, `LhColAgree` Dyadic Window Refutations, Direct `2^k - m * P` Cone-Boundary Refutations, and Unconditional Flip-Witness Existence Theorems Over `2^k` Windows Under `CenterPeriodic` Alone (9.1012–9.1026) -/

/-- **Strict Exponential Dominance `n < 2^n` (`lt_twopow_self`, 9.1012)**:
    for every `n ∈ ℕ`, `n < twopow n`! -/
theorem lt_twopow_self : ∀ n : Nat, n < twopow n
  | 0 => by decide
  | n + 1 => by
    have ih := lt_twopow_self n
    have hpos := Rule30UOR.Scale.twopow_pos n
    rw [Rule30UOR.Core.twopow_succ]
    omega

/-- **Refuting `CenterPeriodic` at the Dyadic Cone Boundary `t + m * P = 2^k` from `LhColAgree t (m * P) 1 S` Over `2^k ≤ S + 1` (`not_centerPeriodic_of_lhColAgree_one_at_twopow`, 9.1013)**:
    for every `T, P, m, t, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = twopow k`, and `twopow k ≤ S + 1`, if `LhColAgree t (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_at_twopow
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (hcone : t + m * P = twopow k) (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_lhColAgree_one_twopow T P hP hper m t k S ht hS hlh
  have hflip := periodic_response_flip_at_twopow_mul T P hP hper m t k hm ht hcone
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response t k <;> decide

/-- **Refuting `CenterPeriodic` at `z + 2^k` for `m * P = 2` from `LhColAgree (z + 2^k) (m * P) 1 S` Over `2^k ≤ S + 1` (`not_centerPeriodic_of_lhColAgree_one_at_zero_diag_step_two`, 9.1014)**:
    for every `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `m * P = 2`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + 2) ≤ (z + 2) + twopow k`, and `twopow k ≤ S + 1`, if `LhColAgree (z + twopow k) (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_at_zero_diag_step_two
    (T P m z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k)
    (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree (z + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_lhColAgree_one_twopow
    T P hP hper m (z + twopow k) k S ht hS hlh
  have hflip := periodic_response_flip_at_zero_diag_step_two
    T P hP hper m z k hm ht hz hset0 hset2
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem not_centerPeriodic_of_lhColAgree_one_at_zero_diag_step_two_prop
    (T P m z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z)
    (hm : m * P = 2) (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree (z + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhColAgree_one_at_zero_diag_step_two
    T P m z k S hP hz hm ht hset0 hset2 hS hlh

/-- **Refuting `CenterPeriodic` at `z + 2^k` from Two Zero Diagonals and `LhColAgree (z + 2^k) (m * P) 1 S` Over `2^k ≤ S + 1` (`not_centerPeriodic_of_lhColAgree_one_of_two_zero_diags`, 9.1015)**:
    for every `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + m * P) ≤ (z + m * P) + twopow k`, and `twopow k ≤ S + 1`, if `LhColAgree (z + twopow k) (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_of_two_zero_diags
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k) (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree (z + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq := periodic_response_eq_of_lhColAgree_one_twopow
    T P hP hper m (z + twopow k) k S ht hS hlh
  have hflip := periodic_response_flip_of_two_zero_diags
    T P hP hper m z ((z + m * P) - 2) k ht (by omega) hz0 hz1 hset0
    (by rw [show ((z + m * P) - 2) + 2 = z + m * P by omega]; exact hset1)
  rw [heq] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (z + twopow k) k <;> decide

theorem not_centerPeriodic_of_lhColAgree_one_of_two_zero_diags_prop
    (T P m z k S : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k) (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hlh : LhColAgree (z + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhColAgree_one_of_two_zero_diags
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hlh

/-- **Two-Scale Refutation of `CenterPeriodic` Across ANY Dyadic Doubling Zero Diagonal `z` (`DoublesAt (twopow k) z`) from `LhColAgree` Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_lhColAgree_one_scale_step_doubles`, 9.1016)**:
    for every `T, P, m, d, z, k, S0, S1 ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 1) ≤ (z + 1) + twopow k`, `twopow k ≤ S0 + 1`, and `twopow (k + 1) ≤ S1 + 1`, if `LhColAgree (d + twopow k) (m * P) 1 S0` and `LhColAgree (d + twopow (k + 1)) (m * P) 1 S1` hold, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_scale_step_doubles
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hS0 : twopow k ≤ S0 + 1) (hS1 : twopow (k + 1) ≤ S1 + 1)
    (hlh0 : LhColAgree (d + twopow k) (m * P) 1 S0)
    (hlh1 : LhColAgree (d + twopow (k + 1)) (m * P) 1 S1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have heq0 := periodic_response_eq_of_lhColAgree_one_twopow
    T P hP hper m (d + twopow k) k S0 ht hS0 hlh0
  have heq1 := periodic_response_eq_of_lhColAgree_one_twopow
    T P hP hper m (d + twopow (k + 1)) (k + 1) S1
    (by rw [Rule30UOR.Core.twopow_succ]; omega) hS1 hlh1
  have hflip := periodic_late_response_flip_of_doubles_and_eq
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset1 heq0
  rw [heq1] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem not_centerPeriodic_of_lhColAgree_one_scale_step_doubles_prop
    (T P m d z k S0 S1 : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hS0 : twopow k ≤ S0 + 1) (hS1 : twopow (k + 1) ≤ S1 + 1)
    (hlh0 : LhColAgree (d + twopow k) (m * P) 1 S0)
    (hlh1 : LhColAgree (d + twopow (k + 1)) (m * P) 1 S1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhColAgree_one_scale_step_doubles
    T P m d z k S0 S1 hP hz hd hdz hdm ht hset0 hset1 hS0 hS1 hlh0 hlh1

/-- **Direct `twopow k - m * P` Cone-Boundary Refutation of `CenterPeriodic` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow`, 9.1017)**:
    for every `T, P, m, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T + m * P ≤ twopow k`, and `twopow k ≤ S + 1` (no `t`, `z`, `DoublesAt`, or `SettledBy`!), if `∀ s ≤ S, center ((twopow k - m * P) + s) = false → rhCenter (((twopow k - m * P) + s) + m * P) 1 = rhCenter ((twopow k - m * P) + s) 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ twopow k) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((twopow k - m * P) + s) = false →
        rhCenter (((twopow k - m * P) + s) + m * P) 1 = rhCenter ((twopow k - m * P) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_at_twopow
    T P m (twopow k - m * P) k S hP hm (by omega) (by omega) hS hw

/-- **Direct `twopow k - m * P` Cone-Boundary Refutation of `CenterPeriodic` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` (`not_centerPeriodic_of_maskparity_zero_agree_sub_twopow`, 9.1018)**:
    for every `T, P, m, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T + m * P ≤ twopow k`, and `twopow k ≤ S + 1` (no `t`, `z`, `DoublesAt`, or `SettledBy`!), if `∀ s ≤ S, maskparity (((twopow k - m * P) + s) + m * P) 0 = maskparity ((twopow k - m * P) + s) 0`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_sub_twopow
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ twopow k) (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((twopow k - m * P) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((twopow k - m * P) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m (twopow k - m * P) k S hP hm (by omega) (by omega) hS hmp

/-- **Unconditional Existence of a White-Center `rhCenter · 1` Flip Within `2^k` Steps of the Cone Boundary `t + m * P = 2^k` Under `CenterPeriodic` Alone (`exists_white_center_rhCenter_one_flip_at_twopow_of_periodic`, 9.1019)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k, S ∈ ℕ` with `0 < m`, `T ≤ t`, `t + m * P = twopow k`, and `twopow k ≤ S + 1` (with ZERO agreement hypotheses and NO `SettledBy`!), there exists `s ≤ S` such that `center (t + s) = false ∧ rhCenter ((t + s) + m * P) 1 = !rhCenter (t + s) 1`! -/
theorem exists_white_center_rhCenter_one_flip_at_twopow_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hcone : t + m * P = twopow k) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center (t + s) = false ∧
      rhCenter ((t + s) + m * P) 1 = !rhCenter (t + s) 1 := by
  have hnot : ¬ ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center (t + s) = false →
        rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1 :=
    fun hw => not_centerPeriodic_of_white_center_rhCenter_one_at_twopow
      T P m t k S hP hm ht hcone hS hw hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hc : Rule30UOR.Core.center (t + s) = false := by
    cases hc' : Rule30UOR.Core.center (t + s)
    · rfl
    · exfalso; exact hs_not (fun _ h => by rw [hc'] at h; contradiction)
  have hneq : rhCenter ((t + s) + m * P) 1 ≠ rhCenter (t + s) 1 :=
    fun heq => hs_not (fun _ _ => heq)
  refine ⟨s, hs, hc, ?_⟩
  revert hneq
  cases rhCenter ((t + s) + m * P) 1 <;> cases rhCenter (t + s) 1 <;> decide

/-- **Unconditional Existence of a First-Bit `maskparity · 0` Flip Within `2^k` Steps of the Cone Boundary `t + m * P = 2^k` Under `CenterPeriodic` Alone (`exists_maskparity_zero_flip_at_twopow_of_periodic`, 9.1020)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k, S ∈ ℕ` with `0 < m`, `T ≤ t`, `t + m * P = twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `maskparity ((t + s) + m * P) 0 = !maskparity (t + s) 0`! -/
theorem exists_maskparity_zero_flip_at_twopow_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hcone : t + m * P = twopow k) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hnot : ¬ ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity (t + s) 0 :=
    fun hmp => not_centerPeriodic_of_maskparity_zero_agree_at_twopow
      T P m t k S hP hm ht hcone hS hmp hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hneq : Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 ≠
      Rule30UOR.Scale.maskparity (t + s) 0 :=
    fun heq => hs_not (fun _ => heq)
  refine ⟨s, hs, ?_⟩
  revert hneq
  cases Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 <;>
    cases Rule30UOR.Scale.maskparity (t + s) 0 <;> decide

/-- **Unconditional Existence of a Left-Column-`-1` `lhCenter · 1` Flip Within `2^k` Steps of the Cone Boundary `t + m * P = 2^k` Under `CenterPeriodic` Alone (`exists_lhCenter_one_flip_at_twopow_of_periodic`, 9.1021)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, t, k, S ∈ ℕ` with `0 < m`, `T ≤ t`, `t + m * P = twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `lhCenter ((t + s) + m * P) 1 = !lhCenter (t + s) 1`! -/
theorem exists_lhCenter_one_flip_at_twopow_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k S : Nat) (hm : 0 < m) (ht : T ≤ t)
    (hcone : t + m * P = twopow k) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      lhCenter ((t + s) + m * P) 1 = !lhCenter (t + s) 1 := by
  have hnot : ¬ LhColAgree t (m * P) 1 S :=
    fun hlh => not_centerPeriodic_of_lhColAgree_one_at_twopow
      T P m t k S hP hm ht hcone hS hlh hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hneq : lhCenter ((t + s) + m * P) 1 ≠ lhCenter (t + s) 1 :=
    fun heq => hs_not (fun _ => heq)
  refine ⟨s, hs, ?_⟩
  revert hneq
  cases lhCenter ((t + s) + m * P) 1 <;> cases lhCenter (t + s) 1 <;> decide

/-- **Unconditional Existence of a White-Center `rhCenter · 1` Flip in `[2^k - m * P, 2^(k+1) - m * P)` for Every Scale `k` with `T + m * P ≤ 2^k` Under `CenterPeriodic` Alone (`exists_white_center_rhCenter_one_flip_sub_twopow_of_periodic`, 9.1022)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, k ∈ ℕ` with `0 < m` and `T + m * P ≤ twopow k` (valid at every sufficiently large scale `k`, with NO `t`, `S`, `z`, `DoublesAt`, or `SettledBy`!), there exists `s < twopow k` such that `center ((twopow k - m * P) + s) = false ∧ rhCenter (((twopow k - m * P) + s) + m * P) 1 = !rhCenter ((twopow k - m * P) + s) 1`! -/
theorem exists_white_center_rhCenter_one_flip_sub_twopow_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ twopow k) :
    ∃ s : Nat, s < twopow k ∧
      Rule30UOR.Core.center ((twopow k - m * P) + s) = false ∧
      rhCenter (((twopow k - m * P) + s) + m * P) 1 =
        !rhCenter ((twopow k - m * P) + s) 1 := by
  have hpos := Rule30UOR.Scale.twopow_pos k
  obtain ⟨s, hs, hc, hf⟩ := exists_white_center_rhCenter_one_flip_at_twopow_of_periodic
    T P hP hper m (twopow k - m * P) k (twopow k - 1) hm (by omega) (by omega) (by omega)
  exact ⟨s, by omega, hc, hf⟩

/-- **Unconditional Existence of a First-Bit `maskparity · 0` Flip in `[2^k - m * P, 2^(k+1) - m * P)` for Every Scale `k` with `T + m * P ≤ 2^k` Under `CenterPeriodic` Alone (`exists_maskparity_zero_flip_sub_twopow_of_periodic`, 9.1023)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, k ∈ ℕ` with `0 < m` and `T + m * P ≤ twopow k`, there exists `s < twopow k` such that `maskparity (((twopow k - m * P) + s) + m * P) 0 = !maskparity ((twopow k - m * P) + s) 0`! -/
theorem exists_maskparity_zero_flip_sub_twopow_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ twopow k) :
    ∃ s : Nat, s < twopow k ∧
      Rule30UOR.Scale.maskparity (((twopow k - m * P) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((twopow k - m * P) + s) 0 := by
  have hpos := Rule30UOR.Scale.twopow_pos k
  obtain ⟨s, hs, hf⟩ := exists_maskparity_zero_flip_at_twopow_of_periodic
    T P hP hper m (twopow k - m * P) k (twopow k - 1) hm (by omega) (by omega) (by omega)
  exact ⟨s, by omega, hf⟩

/-- **Unconditional Existence of a Left-Column-`-1` `lhCenter · 1` Flip in `[2^k - m * P, 2^(k+1) - m * P)` for Every Scale `k` with `T + m * P ≤ 2^k` Under `CenterPeriodic` Alone (`exists_lhCenter_one_flip_sub_twopow_of_periodic`, 9.1024)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, k ∈ ℕ` with `0 < m` and `T + m * P ≤ twopow k`, there exists `s < twopow k` such that `lhCenter (((twopow k - m * P) + s) + m * P) 1 = !lhCenter ((twopow k - m * P) + s) 1`! -/
theorem exists_lhCenter_one_flip_sub_twopow_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ twopow k) :
    ∃ s : Nat, s < twopow k ∧
      lhCenter (((twopow k - m * P) + s) + m * P) 1 =
        !lhCenter ((twopow k - m * P) + s) 1 := by
  have hpos := Rule30UOR.Scale.twopow_pos k
  obtain ⟨s, hs, hf⟩ := exists_lhCenter_one_flip_at_twopow_of_periodic
    T P hP hper m (twopow k - m * P) k (twopow k - 1) hm (by omega) (by omega) (by omega)
  exact ⟨s, by omega, hf⟩

/-- **Unconditional Existence of a White-Center `rhCenter · 1` Flip Within `2^k` Steps of `z + 2^k` When `m * P = 2` Under `CenterPeriodic` Alone (`exists_white_center_rhCenter_one_flip_at_zero_diag_step_two_of_periodic`, 9.1025)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k, S ∈ ℕ` with `IsZeroDiag z`, `m * P = 2`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + 2) ≤ (z + 2) + twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `center ((z + twopow k) + s) = false ∧ rhCenter (((z + twopow k) + s) + m * P) 1 = !rhCenter ((z + twopow k) + s) 1`! -/
theorem exists_white_center_rhCenter_one_flip_at_zero_diag_step_two_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + twopow k) (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center ((z + twopow k) + s) = false ∧
      rhCenter (((z + twopow k) + s) + m * P) 1 = !rhCenter ((z + twopow k) + s) 1 := by
  have hnot : ¬ ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + twopow k) + s) = false →
        rhCenter (((z + twopow k) + s) + m * P) 1 = rhCenter ((z + twopow k) + s) 1 :=
    fun hw => not_centerPeriodic_of_white_center_rhCenter_one_at_zero_diag_step_two
      T P m z k S hP hz hm ht hset0 hset2 hS hw hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hc : Rule30UOR.Core.center ((z + twopow k) + s) = false := by
    cases hc' : Rule30UOR.Core.center ((z + twopow k) + s)
    · rfl
    · exfalso; exact hs_not (fun _ h => by rw [hc'] at h; contradiction)
  have hneq : rhCenter (((z + twopow k) + s) + m * P) 1 ≠ rhCenter ((z + twopow k) + s) 1 :=
    fun heq => hs_not (fun _ _ => heq)
  refine ⟨s, hs, hc, ?_⟩
  revert hneq
  cases rhCenter (((z + twopow k) + s) + m * P) 1 <;>
    cases rhCenter ((z + twopow k) + s) 1 <;> decide

theorem exists_white_center_rhCenter_one_flip_at_zero_diag_step_two_of_periodic_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + twopow k) (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k)) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center ((z + twopow k) + s) = false ∧
      rhCenter (((z + twopow k) + s) + m * P) 1 = !rhCenter ((z + twopow k) + s) 1 :=
  exists_white_center_rhCenter_one_flip_at_zero_diag_step_two_of_periodic
    T P hP hper m z k S hz hm ht hset0 hset2 hS

/-- **Unconditional Existence of a First-Bit `maskparity · 0` Flip Within `2^k` Steps of `z + 2^k` When `m * P = 2` Under `CenterPeriodic` Alone (`exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic`, 9.1026)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k, S ∈ ℕ` with `IsZeroDiag z`, `m * P = 2`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + 2) ≤ (z + 2) + twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `maskparity (((z + twopow k) + s) + m * P) 0 = !maskparity ((z + twopow k) + s) 0`! -/
theorem exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + twopow k) (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 := by
  have hnot : ¬ ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 :=
    fun hmp => not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_step_two
      T P m z k S hP hz hm ht hset0 hset2 hS hmp hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hneq : Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 ≠
      Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 :=
    fun heq => hs_not (fun _ => heq)
  refine ⟨s, hs, ?_⟩
  revert hneq
  cases Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 <;>
    cases Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 <;> decide

theorem exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + twopow k) (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k)) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 :=
  exists_maskparity_zero_flip_at_zero_diag_step_two_of_periodic
    T P hP hper m z k S hz hm ht hset0 hset2 hS

/-! ### Batch 49: Monotonicity of `twopow`, Unconditional Scale-`k ≥ T + P` Fundamental-Period `P` Flip Witnesses, Two-Zero-Diagonal Flip Witnesses, and Scale-Step `maskparity ⊕ leftresponse` Defect Flip Across Dyadic Doubling Zero Diagonals (9.1027–9.1041) -/

/-- **Monotonicity of `twopow` (`twopow_mono`, 9.1027)**:
    for every `a, b ∈ ℕ`, if `a ≤ b`, then `twopow a ≤ twopow b`! -/
theorem twopow_mono (a : Nat) : ∀ b : Nat, a ≤ b → twopow a ≤ twopow b
  | 0, h => by
    have ha : a = 0 := by omega
    subst ha; omega
  | b + 1, h => by
    by_cases hab : a ≤ b
    · have ih := twopow_mono a b hab
      rw [Rule30UOR.Core.twopow_succ]
      omega
    · have ha : a = b + 1 := by omega
      subst ha; omega

/-- **Strict Exponential Bound `n < 2^k` from `n ≤ k` (`lt_twopow_of_le`, 9.1028)**:
    for every `n, k ∈ ℕ`, if `n ≤ k`, then `n < twopow k`! -/
theorem lt_twopow_of_le (n k : Nat) (h : n ≤ k) : n < twopow k :=
  Nat.lt_of_lt_of_le (lt_twopow_self n) (twopow_mono n k h)

/-- **Refuting `CenterPeriodic` at Every Scale `k ≥ T + m * P` from White-Center Column-`1` Agreement Over `2^k ≤ S + 1` (`not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow_ge`, 9.1029)**:
    for every `T, P, m, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T + m * P ≤ k`, and `twopow k ≤ S + 1`, if `∀ s ≤ S, center ((twopow k - m * P) + s) = false → rhCenter (((twopow k - m * P) + s) + m * P) 1 = rhCenter ((twopow k - m * P) + s) 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow_ge
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ k) (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((twopow k - m * P) + s) = false →
        rhCenter (((twopow k - m * P) + s) + m * P) 1 = rhCenter ((twopow k - m * P) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_sub_twopow
    T P m k S hP hm (Nat.le_of_lt (lt_twopow_of_le (T + m * P) k hk)) hS hw

/-- **Refuting `CenterPeriodic` at Every Scale `k ≥ T + m * P` from First-Bit `maskparity · 0` Agreement Over `2^k ≤ S + 1` (`not_centerPeriodic_of_maskparity_zero_agree_sub_twopow_ge`, 9.1030)**:
    for every `T, P, m, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T + m * P ≤ k`, and `twopow k ≤ S + 1`, if `∀ s ≤ S, maskparity (((twopow k - m * P) + s) + m * P) 0 = maskparity ((twopow k - m * P) + s) 0`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_sub_twopow_ge
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hk : T + m * P ≤ k) (hS : twopow k ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((twopow k - m * P) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((twopow k - m * P) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_sub_twopow
    T P m k S hP hm (Nat.le_of_lt (lt_twopow_of_le (T + m * P) k hk)) hS hmp

/-- **Unconditional Existence of a White-Center `rhCenter · 1` Flip in `[2^k - m * P, 2^(k+1) - m * P)` for Every Scale `k ≥ T + m * P` Under `CenterPeriodic` Alone (`exists_white_center_rhCenter_one_flip_sub_twopow_ge_of_periodic`, 9.1031)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, k ∈ ℕ` with `0 < m` and `T + m * P ≤ k`, there exists `s < twopow k` such that `center ((twopow k - m * P) + s) = false ∧ rhCenter (((twopow k - m * P) + s) + m * P) 1 = !rhCenter ((twopow k - m * P) + s) 1`! -/
theorem exists_white_center_rhCenter_one_flip_sub_twopow_ge_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ k) :
    ∃ s : Nat, s < twopow k ∧
      Rule30UOR.Core.center ((twopow k - m * P) + s) = false ∧
      rhCenter (((twopow k - m * P) + s) + m * P) 1 =
        !rhCenter ((twopow k - m * P) + s) 1 :=
  exists_white_center_rhCenter_one_flip_sub_twopow_of_periodic
    T P hP hper m k hm (Nat.le_of_lt (lt_twopow_of_le (T + m * P) k hk))

/-- **Unconditional Existence of a First-Bit `maskparity · 0` Flip in `[2^k - m * P, 2^(k+1) - m * P)` for Every Scale `k ≥ T + m * P` Under `CenterPeriodic` Alone (`exists_maskparity_zero_flip_sub_twopow_ge_of_periodic`, 9.1032)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, k ∈ ℕ` with `0 < m` and `T + m * P ≤ k`, there exists `s < twopow k` such that `maskparity (((twopow k - m * P) + s) + m * P) 0 = !maskparity ((twopow k - m * P) + s) 0`! -/
theorem exists_maskparity_zero_flip_sub_twopow_ge_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ k) :
    ∃ s : Nat, s < twopow k ∧
      Rule30UOR.Scale.maskparity (((twopow k - m * P) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((twopow k - m * P) + s) 0 :=
  exists_maskparity_zero_flip_sub_twopow_of_periodic
    T P hP hper m k hm (Nat.le_of_lt (lt_twopow_of_le (T + m * P) k hk))

/-- **Unconditional Existence of a Left-Column-`-1` `lhCenter · 1` Flip in `[2^k - m * P, 2^(k+1) - m * P)` for Every Scale `k ≥ T + m * P` Under `CenterPeriodic` Alone (`exists_lhCenter_one_flip_sub_twopow_ge_of_periodic`, 9.1033)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, k ∈ ℕ` with `0 < m` and `T + m * P ≤ k`, there exists `s < twopow k` such that `lhCenter (((twopow k - m * P) + s) + m * P) 1 = !lhCenter ((twopow k - m * P) + s) 1`! -/
theorem exists_lhCenter_one_flip_sub_twopow_ge_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m k : Nat) (hm : 0 < m) (hk : T + m * P ≤ k) :
    ∃ s : Nat, s < twopow k ∧
      lhCenter (((twopow k - m * P) + s) + m * P) 1 =
        !lhCenter ((twopow k - m * P) + s) 1 :=
  exists_lhCenter_one_flip_sub_twopow_of_periodic
    T P hP hper m k hm (Nat.le_of_lt (lt_twopow_of_le (T + m * P) k hk))

/-- **Unconditional Fundamental-Period (`P` Itself, No Multiplier `m`!) White-Center `rhCenter · 1` Flip in `[2^k - P, 2^(k+1) - P)` for Every Scale `k ≥ T + P` Under `CenterPeriodic` Alone (`exists_white_center_rhCenter_one_flip_sub_twopow_P_of_periodic`, 9.1034)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `k ∈ ℕ` with `T + P ≤ k` (with NO multiplier `m`, NO `t`, NO `S`, NO `z`, NO `DoublesAt`, and NO `SettledBy`!), there exists `s < twopow k` such that `center ((twopow k - P) + s) = false ∧ rhCenter (((twopow k - P) + s) + P) 1 = !rhCenter ((twopow k - P) + s) 1`! -/
theorem exists_white_center_rhCenter_one_flip_sub_twopow_P_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k : Nat) (hk : T + P ≤ k) :
    ∃ s : Nat, s < twopow k ∧
      Rule30UOR.Core.center ((twopow k - P) + s) = false ∧
      rhCenter (((twopow k - P) + s) + P) 1 =
        !rhCenter ((twopow k - P) + s) 1 := by
  have h := exists_white_center_rhCenter_one_flip_sub_twopow_ge_of_periodic
    T P hP hper 1 k (by omega) (by rw [Nat.one_mul]; exact hk)
  rwa [Nat.one_mul] at h

/-- **Unconditional Fundamental-Period (`P` Itself, No Multiplier `m`!) First-Bit `maskparity · 0` Flip in `[2^k - P, 2^(k+1) - P)` for Every Scale `k ≥ T + P` Under `CenterPeriodic` Alone (`exists_maskparity_zero_flip_sub_twopow_P_of_periodic`, 9.1035)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `k ∈ ℕ` with `T + P ≤ k`, there exists `s < twopow k` such that `maskparity (((twopow k - P) + s) + P) 0 = !maskparity ((twopow k - P) + s) 0`! -/
theorem exists_maskparity_zero_flip_sub_twopow_P_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k : Nat) (hk : T + P ≤ k) :
    ∃ s : Nat, s < twopow k ∧
      Rule30UOR.Scale.maskparity (((twopow k - P) + s) + P) 0 =
        !Rule30UOR.Scale.maskparity ((twopow k - P) + s) 0 := by
  have h := exists_maskparity_zero_flip_sub_twopow_ge_of_periodic
    T P hP hper 1 k (by omega) (by rw [Nat.one_mul]; exact hk)
  rwa [Nat.one_mul] at h

/-- **Unconditional Fundamental-Period (`P` Itself, No Multiplier `m`!) Left-Column-`-1` `lhCenter · 1` Flip in `[2^k - P, 2^(k+1) - P)` for Every Scale `k ≥ T + P` Under `CenterPeriodic` Alone (`exists_lhCenter_one_flip_sub_twopow_P_of_periodic`, 9.1036)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `k ∈ ℕ` with `T + P ≤ k`, there exists `s < twopow k` such that `lhCenter (((twopow k - P) + s) + P) 1 = !lhCenter ((twopow k - P) + s) 1`! -/
theorem exists_lhCenter_one_flip_sub_twopow_P_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k : Nat) (hk : T + P ≤ k) :
    ∃ s : Nat, s < twopow k ∧
      lhCenter (((twopow k - P) + s) + P) 1 =
        !lhCenter ((twopow k - P) + s) 1 := by
  have h := exists_lhCenter_one_flip_sub_twopow_ge_of_periodic
    T P hP hper 1 k (by omega) (by rw [Nat.one_mul]; exact hk)
  rwa [Nat.one_mul] at h

/-- **Unconditional Existence of a Left-Column-`-1` `lhCenter · 1` Flip Within `2^k` Steps of `z + 2^k` When `m * P = 2` Under `CenterPeriodic` Alone (`exists_lhCenter_one_flip_at_zero_diag_step_two_of_periodic`, 9.1037)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k, S ∈ ℕ` with `IsZeroDiag z`, `m * P = 2`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + 2) ≤ (z + 2) + twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `lhCenter (((z + twopow k) + s) + m * P) 1 = !lhCenter ((z + twopow k) + s) 1`! -/
theorem exists_lhCenter_one_flip_at_zero_diag_step_two_of_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + twopow k) (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      lhCenter (((z + twopow k) + s) + m * P) 1 =
        !lhCenter ((z + twopow k) + s) 1 := by
  have hnot : ¬ LhColAgree (z + twopow k) (m * P) 1 S :=
    fun hlh => not_centerPeriodic_of_lhColAgree_one_at_zero_diag_step_two
      T P m z k S hP hz hm ht hset0 hset2 hS hlh hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hneq : lhCenter (((z + twopow k) + s) + m * P) 1 ≠
      lhCenter ((z + twopow k) + s) 1 :=
    fun heq => hs_not (fun _ => heq)
  refine ⟨s, hs, ?_⟩
  revert hneq
  cases lhCenter (((z + twopow k) + s) + m * P) 1 <;>
    cases lhCenter ((z + twopow k) + s) 1 <;> decide

theorem exists_lhCenter_one_flip_at_zero_diag_step_two_of_periodic_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz : IsZeroDiag z) (hm : m * P = 2)
    (ht : T ≤ z + twopow k) (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k)) (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      lhCenter (((z + twopow k) + s) + m * P) 1 =
        !lhCenter ((z + twopow k) + s) 1 :=
  exists_lhCenter_one_flip_at_zero_diag_step_two_of_periodic
    T P hP hper m z k S hz hm ht hset0 hset2 hS

/-- **Unconditional Existence of a White-Center `rhCenter · 1` Flip Within `2^k` Steps of `z + 2^k` for Any Two Zero Diagonals Under `CenterPeriodic` Alone (`exists_white_center_rhCenter_one_flip_of_two_zero_diags_and_periodic`, 9.1038)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k, S ∈ ℕ` with `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + m * P) ≤ (z + m * P) + twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `center ((z + twopow k) + s) = false ∧ rhCenter (((z + twopow k) + s) + m * P) 1 = !rhCenter ((z + twopow k) + s) 1`! -/
theorem exists_white_center_rhCenter_one_flip_of_two_zero_diags_and_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center ((z + twopow k) + s) = false ∧
      rhCenter (((z + twopow k) + s) + m * P) 1 = !rhCenter ((z + twopow k) + s) 1 := by
  have hnot : ¬ ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + twopow k) + s) = false →
        rhCenter (((z + twopow k) + s) + m * P) 1 = rhCenter ((z + twopow k) + s) 1 :=
    fun hw => not_centerPeriodic_of_white_center_rhCenter_one_of_two_zero_diags
      T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hw hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hc : Rule30UOR.Core.center ((z + twopow k) + s) = false := by
    cases hc' : Rule30UOR.Core.center ((z + twopow k) + s)
    · rfl
    · exfalso; exact hs_not (fun _ h => by rw [hc'] at h; contradiction)
  have hneq : rhCenter (((z + twopow k) + s) + m * P) 1 ≠ rhCenter ((z + twopow k) + s) 1 :=
    fun heq => hs_not (fun _ _ => heq)
  refine ⟨s, hs, hc, ?_⟩
  revert hneq
  cases rhCenter (((z + twopow k) + s) + m * P) 1 <;>
    cases rhCenter ((z + twopow k) + s) 1 <;> decide

theorem exists_white_center_rhCenter_one_flip_of_two_zero_diags_and_periodic_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Core.center ((z + twopow k) + s) = false ∧
      rhCenter (((z + twopow k) + s) + m * P) 1 = !rhCenter ((z + twopow k) + s) 1 :=
  exists_white_center_rhCenter_one_flip_of_two_zero_diags_and_periodic
    T P hP hper m z k S hz0 h2 hz1 ht hset0 hset1 hS

/-- **Unconditional Existence of a First-Bit `maskparity · 0` Flip Within `2^k` Steps of `z + 2^k` for Any Two Zero Diagonals Under `CenterPeriodic` Alone (`exists_maskparity_zero_flip_of_two_zero_diags_and_periodic`, 9.1039)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k, S ∈ ℕ` with `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + m * P) ≤ (z + m * P) + twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `maskparity (((z + twopow k) + s) + m * P) 0 = !maskparity ((z + twopow k) + s) 0`! -/
theorem exists_maskparity_zero_flip_of_two_zero_diags_and_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 := by
  have hnot : ¬ ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 :=
    fun hmp => not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags
      T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hmp hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hneq : Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 ≠
      Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 :=
    fun heq => hs_not (fun _ => heq)
  refine ⟨s, hs, ?_⟩
  revert hneq
  cases Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 <;>
    cases Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 <;> decide

theorem exists_maskparity_zero_flip_of_two_zero_diags_and_periodic_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      Rule30UOR.Scale.maskparity (((z + twopow k) + s) + m * P) 0 =
        !Rule30UOR.Scale.maskparity ((z + twopow k) + s) 0 :=
  exists_maskparity_zero_flip_of_two_zero_diags_and_periodic
    T P hP hper m z k S hz0 h2 hz1 ht hset0 hset1 hS

/-- **Unconditional Existence of a Left-Column-`-1` `lhCenter · 1` Flip Within `2^k` Steps of `z + 2^k` for Any Two Zero Diagonals Under `CenterPeriodic` Alone (`exists_lhCenter_one_flip_of_two_zero_diags_and_periodic`, 9.1040)**:
    under `CenterPeriodic T P` (`0 < P`), for EVERY `m, z, k, S ∈ ℕ` with `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + twopow k`, `settle z ≤ z + twopow k`, `settle (z + m * P) ≤ (z + m * P) + twopow k`, and `twopow k ≤ S + 1`, there exists `s ≤ S` such that `lhCenter (((z + twopow k) + s) + m * P) 1 = !lhCenter ((z + twopow k) + s) 1`! -/
theorem exists_lhCenter_one_flip_of_two_zero_diags_and_periodic
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      lhCenter (((z + twopow k) + s) + m * P) 1 =
        !lhCenter ((z + twopow k) + s) 1 := by
  have hnot : ¬ LhColAgree (z + twopow k) (m * P) 1 S :=
    fun hlh => not_centerPeriodic_of_lhColAgree_one_of_two_zero_diags
      T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hlh hper
  obtain ⟨s, hs_not⟩ := Rule30UOR.Constructive.exists_not_of_not_forall_le _ hnot
  have hs : s ≤ S := by
    by_cases hns : s ≤ S
    · exact hns
    · exfalso; exact hs_not (fun h => absurd h hns)
  have hneq : lhCenter (((z + twopow k) + s) + m * P) 1 ≠
      lhCenter ((z + twopow k) + s) 1 :=
    fun heq => hs_not (fun _ => heq)
  refine ⟨s, hs, ?_⟩
  revert hneq
  cases lhCenter (((z + twopow k) + s) + m * P) 1 <;>
    cases lhCenter ((z + twopow k) + s) 1 <;> decide

theorem exists_lhCenter_one_flip_of_two_zero_diags_and_periodic_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z k S : Nat) (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2)) (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1) :
    ∃ s : Nat, s ≤ S ∧
      lhCenter (((z + twopow k) + s) + m * P) 1 =
        !lhCenter ((z + twopow k) + s) 1 :=
  exists_lhCenter_one_flip_of_two_zero_diags_and_periodic
    T P hP hper m z k S hz0 h2 hz1 ht hset0 hset1 hS

/-- **Scale-Step Flip of the Combined `maskparity ⊕ leftresponse` Shift Defect Across a Dyadic Doubling Zero Diagonal `z` Without `z ≤ k` or `DoublesAt (m * P) z` (`periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles`, 9.1041)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (z + 1) ≤ (z + 1) + twopow k`, `(maskparity ((d + 2^(k+1)) + m * P) (k + 1) ⊕ maskparity (d + 2^(k+1)) (k + 1)) ⊕ (leftresponse ((d + 2^(k+1)) + m * P) (k + 1) ⊕ leftresponse (d + 2^(k+1)) (k + 1)) = !((maskparity ((d + 2^k) + m * P) k ⊕ maskparity (d + 2^k) k) ⊕ (leftresponse ((d + 2^k) + m * P) k ⊕ leftresponse (d + 2^k) k))`! -/
theorem periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset1 : settle (z + 1) ≤ (z + 1) + twopow k) :
    bxor
      (bxor (Rule30UOR.Scale.maskparity ((d + twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.maskparity (d + twopow (k + 1)) (k + 1)))
      (bxor (Rule30UOR.Scale.leftresponse ((d + twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + twopow (k + 1)) (k + 1))) =
    !bxor
      (bxor (Rule30UOR.Scale.maskparity ((d + twopow k) + m * P) k)
        (Rule30UOR.Scale.maskparity (d + twopow k) k))
      (bxor (Rule30UOR.Scale.leftresponse ((d + twopow k) + m * P) k)
        (Rule30UOR.Scale.leftresponse (d + twopow k) k)) := by
  have hr := periodic_late_response_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset1
  rw [Rule30UOR.Scale.split_paper ((d + twopow (k + 1)) + m * P) (k + 1),
    Rule30UOR.Scale.split_paper (d + twopow (k + 1)) (k + 1),
    Rule30UOR.Scale.split_paper ((d + twopow k) + m * P) k,
    Rule30UOR.Scale.split_paper (d + twopow k) k] at hr
  revert hr
  cases Rule30UOR.Scale.leftresponse ((d + twopow (k + 1)) + m * P) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + twopow (k + 1)) (k + 1) <;>
    cases Rule30UOR.Scale.maskparity ((d + twopow (k + 1)) + m * P) (k + 1) <;>
    cases Rule30UOR.Scale.maskparity (d + twopow (k + 1)) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse ((d + twopow k) + m * P) k <;>
    cases Rule30UOR.Scale.leftresponse (d + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity ((d + twopow k) + m * P) k <;>
    cases Rule30UOR.Scale.maskparity (d + twopow k) k <;> decide

theorem periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k)) :
    bxor
      (bxor (Rule30UOR.Scale.maskparity ((d + twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.maskparity (d + twopow (k + 1)) (k + 1)))
      (bxor (Rule30UOR.Scale.leftresponse ((d + twopow (k + 1)) + m * P) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + twopow (k + 1)) (k + 1))) =
    !bxor
      (bxor (Rule30UOR.Scale.maskparity ((d + twopow k) + m * P) k)
        (Rule30UOR.Scale.maskparity (d + twopow k) k))
      (bxor (Rule30UOR.Scale.leftresponse ((d + twopow k) + m * P) k)
        (Rule30UOR.Scale.leftresponse (d + twopow k) k)) :=
  periodic_late_maskparity_xor_leftresponse_defect_flip_of_doubles
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset1

end Rule30UOR.Interfaces
