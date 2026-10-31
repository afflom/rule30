module

public import Rule30UOR.Interfaces.Part13

/-!
# `Rule30UOR.Interfaces`, part 14

* Batch 50: Reset-Diagonal (`d + m * P = z + 3`) Scale-Step Defect Flip Laws, Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Dyadic Doubling Refutations, and the Driven Right Half `rdrv` (`kit [33]`) Under a Periodic Center (9.1042–9.1056)
* Batch 51: Drive-Cone Causality of `rdrv` (`kit [33]`), Derivation of `maskparity · 0` Agreement from Same-Drive Right-Half Slice and Strip Agreement, and Zero-Diagonal / Dyadic Refutation Engines (9.1057–9.1071)
* Batch 52: Inward Determination of the Driven Right Half `rdrv` (`kit [33]` + `kit [23]`), Drive-Cancelling Column-`1` Defect Laws, Right-Edge `2^e`-Periodicity in `rdrv`, and Multi-Column Inward Propagation to `maskparity · 0` Agreement (9.1072–9.1086)
* Batch 53: Right-Threshold `2^e`-Periodicity, Zero-Gaps, and Black Runs in `rdrv`, Interior Defect Evolution, and Column-Plus-OR Inward Propagation to `maskparity · 0` Agreement and Refutations (9.1087–9.1101)
* Batch 54: The Pure-Drive All-White-Seed Right Half `rdrv td 0 k p` (`kit [33]`), White-Run Pinning of Column `1`, White-Slice Agreement with the Pure-Drive Evolution, and Pure-Drive Synchronized Refutations (9.1102–9.1116)
* Batch 55: Universal `2^d`-Diagonal Periodicity & Scale Laws of Pure-Drive `rdrv` (`kit [33]`, 9.1117–9.1131)
* Batch 56: Drive-Wavefront Constancy & Inward Initial-Wavefront Shielding Laws of `rdrv` (`kit [33]`, 9.1132–9.1146)
* Batch 57: Black-Boundary Strip Shielding & Main-Diagonal Gate Determination of the Drive Cone in `rdrv` (`kit [33]`, 9.1147–9.1161)
* Batch 58: Two-Cell Diagonal Corridor Determination of the Drive Cone & Pure-Drive Scale Transfer (`kit [33]`, 9.1162–9.1176)
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

/-! ### Batch 50: Reset-Diagonal (`d + m * P = z + 3`) Scale-Step Defect Flip Laws, Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Dyadic Doubling Refutations, and the Driven Right Half `rdrv` (`kit [33]`) Under a Periodic Center (9.1042–9.1056) -/

/-- **Scale-Step Flip of the Late `response` Shift Defect Across the Reset Diagonal `z + 3` of a Dyadic Doubling Zero Diagonal `z` Without `z ≤ k` or `DoublesAt (m * P) z` (`periodic_late_response_reset_defect_flip_of_doubles`, 9.1042)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 3`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (z + 3) ≤ (z + 3) + twopow k` (requiring ONLY `DoublesAt (twopow k) z`, NOT `DoublesAt (m * P) z` and NOT `z ≤ k`!), `response ((d + twopow (k + 1)) + m * P) (k + 1) ⊕ response (d + twopow (k + 1)) (k + 1) = !(response ((d + twopow k) + m * P) k ⊕ response (d + twopow k) k)`! -/
theorem periodic_late_response_reset_defect_flip_of_doubles
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset3 : settle (z + 3) ≤ (z + 3) + twopow k) :
    bxor (Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    !bxor (Rule30UOR.Scale.response ((d + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hr0 := (periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (d + twopow k) k ht).symm
  have hr1 := (periodic_lhCenter_twopow_defect_eq_response_defect T P hP hper m (d + twopow (k + 1)) (k + 1)
    (by rw [Rule30UOR.Core.twopow_succ]; omega)).symm
  have hp0 := lhCenter_twopow_succ_periodic_of_doubles_le z d k hd hdz hset0
  have hp3 := lhCenter_twopow_reset_succ_antiperiodic_of_doubles z k hz hd hset3
  rw [show (d + twopow k) + m * P = (z + 3) + twopow k by omega] at hr0 ⊢
  rw [show (d + twopow (k + 1)) + m * P = (z + 3) + twopow (k + 1) by omega] at hr1 ⊢
  rw [hr1, hr0, hp0, hp3, bxor_eq_xor, bxor_eq_xor]
  cases lhCenter ((z + 3) + twopow k) (twopow k) <;>
    cases lhCenter (d + twopow k) (twopow k) <;> decide

theorem periodic_late_response_reset_defect_flip_of_doubles_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset3 : SettledBy (z + 3) ((z + 3) + twopow k)) :
    bxor (Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1))
      (Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1)) =
    !bxor (Rule30UOR.Scale.response ((d + twopow k) + m * P) k)
      (Rule30UOR.Scale.response (d + twopow k) k) :=
  periodic_late_response_reset_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset3

/-- **Scale-Step `response` Inversion at `k + 1` from Scale-`k` Agreement Across the Reset Diagonal `z + 3` (`periodic_late_response_reset_flip_of_doubles_and_eq`, 9.1043)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 3`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (z + 3) ≤ (z + 3) + twopow k`, if `response ((d + twopow k) + m * P) k = response (d + twopow k) k`, then `response ((d + twopow (k + 1)) + m * P) (k + 1) = !response (d + twopow (k + 1)) (k + 1)`! -/
theorem periodic_late_response_reset_flip_of_doubles_and_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset3 : settle (z + 3) ≤ (z + 3) + twopow k)
    (hreq : Rule30UOR.Scale.response ((d + twopow k) + m * P) k =
      Rule30UOR.Scale.response (d + twopow k) k) :
    Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1) =
      !Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) := by
  have hf := periodic_late_response_reset_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset3
  rw [hreq] at hf
  revert hf
  rw [bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.response (d + twopow k) k <;>
    cases Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1) <;>
    cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem periodic_late_response_reset_flip_of_doubles_and_eq_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset3 : SettledBy (z + 3) ((z + 3) + twopow k))
    (hreq : Rule30UOR.Scale.response ((d + twopow k) + m * P) k =
      Rule30UOR.Scale.response (d + twopow k) k) :
    Rule30UOR.Scale.response ((d + twopow (k + 1)) + m * P) (k + 1) =
      !Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) :=
  periodic_late_response_reset_flip_of_doubles_and_eq T P hP hper m d z k hz hd hdz hdm ht hset0 hset3 hreq

/-- **Scale-Step Flip of the Combined `maskparity ⊕ leftresponse` Shift Defect Across the Reset Diagonal `z + 3` Without `z ≤ k` or `DoublesAt (m * P) z` (`periodic_late_maskparity_xor_leftresponse_reset_defect_flip_of_doubles`, 9.1044)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, d, z, k ∈ ℕ` with `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 3`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, and `settle (z + 3) ≤ (z + 3) + twopow k`, `(maskparity ((d + 2^(k+1)) + m * P) (k + 1) ⊕ maskparity (d + 2^(k+1)) (k + 1)) ⊕ (leftresponse ((d + 2^(k+1)) + m * P) (k + 1) ⊕ leftresponse (d + 2^(k+1)) (k + 1)) = !((maskparity ((d + 2^k) + m * P) k ⊕ maskparity (d + 2^k) k) ⊕ (leftresponse ((d + 2^k) + m * P) k ⊕ leftresponse (d + 2^k) k))`! -/
theorem periodic_late_maskparity_xor_leftresponse_reset_defect_flip_of_doubles
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3)
    (ht : T ≤ d + twopow k) (hset0 : settle d ≤ d + twopow k)
    (hset3 : settle (z + 3) ≤ (z + 3) + twopow k) :
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
  have hr := periodic_late_response_reset_defect_flip_of_doubles T P hP hper m d z k hz hd hdz hdm ht hset0 hset3
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

theorem periodic_late_maskparity_xor_leftresponse_reset_defect_flip_of_doubles_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m d z k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3)
    (ht : T ≤ d + twopow k) (hset0 : SettledBy d (d + twopow k))
    (hset3 : SettledBy (z + 3) ((z + 3) + twopow k)) :
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
  periodic_late_maskparity_xor_leftresponse_reset_defect_flip_of_doubles
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset3

/-- **Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Refutation of `CenterPeriodic` Across ANY Dyadic Doubling Zero Diagonal `z` (`DoublesAt (twopow k) z`) from White-Center Column-`1` Agreement Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_doubles`, 9.1045)**:
    for every `T, P, m, d, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 1) ≤ (z + 1) + twopow k`, and `twopow k + twopow (k + 1) ≤ S + 1`, if `∀ s ≤ S, center ((d + twopow k) + s) = false → rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_doubles
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((d + twopow k) + s) = false →
        rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hpos0 := Rule30UOR.Scale.twopow_pos k
  have hpos1 := Rule30UOR.Scale.twopow_pos (k + 1)
  refine not_centerPeriodic_of_white_center_rhCenter_one_scale_step_doubles
    T P m d z k (twopow k - 1) (twopow (k + 1) - 1) hP hz hd hdz hdm ht hset0 hset1
    (by omega) (by omega) (fun s hs hc => hw s (by omega) hc) (fun s hs hc => ?_)
  have hstep : (d + twopow (k + 1)) + s = (d + twopow k) + (twopow k + s) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep] at hc ⊢
  exact hw (twopow k + s) (by omega) hc

theorem not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_doubles_prop
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((d + twopow k) + s) = false →
        rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_doubles
    T P m d z k S hP hz hd hdz hdm ht hset0 hset1 hS hw

/-- **Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Refutation of `CenterPeriodic` Across ANY Dyadic Doubling Zero Diagonal `z` (`DoublesAt (twopow k) z`) from First-Bit `maskparity · 0` Agreement Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_maskparity_zero_agree_three_twopow_doubles`, 9.1046)**:
    for every `T, P, m, d, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 1) ≤ (z + 1) + twopow k`, and `twopow k + twopow (k + 1) ≤ S + 1`, if `∀ s ≤ S, maskparity (((d + twopow k) + s) + m * P) 0 = maskparity ((d + twopow k) + s) 0`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_three_twopow_doubles
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((d + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hpos0 := Rule30UOR.Scale.twopow_pos k
  have hpos1 := Rule30UOR.Scale.twopow_pos (k + 1)
  refine not_centerPeriodic_of_maskparity_zero_agree_scale_step_doubles
    T P m d z k (twopow k - 1) (twopow (k + 1) - 1) hP hz hd hdz hdm ht hset0 hset1
    (by omega) (by omega) (fun s hs => hmp s (by omega)) (fun s hs => ?_)
  have hstep : (d + twopow (k + 1)) + s = (d + twopow k) + (twopow k + s) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep]
  exact hmp (twopow k + s) (by omega)

theorem not_centerPeriodic_of_maskparity_zero_agree_three_twopow_doubles_prop
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((d + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_three_twopow_doubles
    T P m d z k S hP hz hd hdz hdm ht hset0 hset1 hS hmp

/-- **Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Refutation of `CenterPeriodic` Across ANY Dyadic Doubling Zero Diagonal `z` (`DoublesAt (twopow k) z`) from `LhColAgree` Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_lhColAgree_one_three_twopow_doubles`, 9.1047)**:
    for every `T, P, m, d, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 1`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 1) ≤ (z + 1) + twopow k`, and `twopow k + twopow (k + 1) ≤ S + 1`, if `LhColAgree (d + twopow k) (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_three_twopow_doubles
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset1 : settle (z + 1) ≤ (z + 1) + twopow k)
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hlh : LhColAgree (d + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hpos0 := Rule30UOR.Scale.twopow_pos k
  have hpos1 := Rule30UOR.Scale.twopow_pos (k + 1)
  refine not_centerPeriodic_of_lhColAgree_one_scale_step_doubles
    T P m d z k (twopow k - 1) (twopow (k + 1) - 1) hP hz hd hdz hdm ht hset0 hset1
    (by omega) (by omega) (fun s hs => hlh s (by omega)) (fun s hs => ?_)
  have hstep : (d + twopow (k + 1)) + s = (d + twopow k) + (twopow k + s) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep]
  exact hlh (twopow k + s) (by omega)

theorem not_centerPeriodic_of_lhColAgree_one_three_twopow_doubles_prop
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 1) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hlh : LhColAgree (d + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhColAgree_one_three_twopow_doubles
    T P m d z k S hP hz hd hdz hdm ht hset0 hset1 hS hlh

/-- **Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Refutation of `CenterPeriodic` Across the Reset Diagonal `d + m * P = z + 3` from White-Center Column-`1` Agreement Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_reset_doubles`, 9.1048)**:
    for every `T, P, m, d, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 3`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 3) ≤ (z + 3) + twopow k`, and `twopow k + twopow (k + 1) ≤ S + 1`, if `∀ s ≤ S, center ((d + twopow k) + s) = false → rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_reset_doubles
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset3 : settle (z + 3) ≤ (z + 3) + twopow k)
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((d + twopow k) + s) = false →
        rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hpos0 := Rule30UOR.Scale.twopow_pos k
  have hpos1 := Rule30UOR.Scale.twopow_pos (k + 1)
  have heq0 := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m (d + twopow k) k (twopow k - 1) ht (by omega)
    (fun s hs hc => hw s (by omega) hc)
  have heq1 := periodic_response_eq_of_white_center_rhCenter_one_twopow
    T P hP hper m (d + twopow (k + 1)) (k + 1) (twopow (k + 1) - 1)
    (by rw [Rule30UOR.Core.twopow_succ]; omega) (by omega) (fun s hs hc => by
      have hstep : (d + twopow (k + 1)) + s = (d + twopow k) + (twopow k + s) := by
        rw [Rule30UOR.Core.twopow_succ]; omega
      rw [hstep] at hc ⊢
      exact hw (twopow k + s) (by omega) hc)
  have hflip := periodic_late_response_reset_flip_of_doubles_and_eq
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset3 heq0
  rw [heq1] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_reset_doubles_prop
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset3 : SettledBy (z + 3) ((z + 3) + twopow k))
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((d + twopow k) + s) = false →
        rhCenter (((d + twopow k) + s) + m * P) 1 = rhCenter ((d + twopow k) + s) 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_white_center_rhCenter_one_three_twopow_reset_doubles
    T P m d z k S hP hz hd hdz hdm ht hset0 hset3 hS hw

/-- **Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Refutation of `CenterPeriodic` Across the Reset Diagonal `d + m * P = z + 3` from First-Bit `maskparity · 0` Agreement Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_maskparity_zero_agree_three_twopow_reset_doubles`, 9.1049)**:
    for every `T, P, m, d, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 3`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 3) ≤ (z + 3) + twopow k`, and `twopow k + twopow (k + 1) ≤ S + 1`, if `∀ s ≤ S, maskparity (((d + twopow k) + s) + m * P) 0 = maskparity ((d + twopow k) + s) 0`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_maskparity_zero_agree_three_twopow_reset_doubles
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset3 : settle (z + 3) ≤ (z + 3) + twopow k)
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((d + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hpos0 := Rule30UOR.Scale.twopow_pos k
  have hpos1 := Rule30UOR.Scale.twopow_pos (k + 1)
  have heq0 := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m (d + twopow k) k (twopow k - 1) ht (by omega)
    (fun s hs => hmp s (by omega))
  have heq1 := periodic_response_eq_of_maskparity_zero_agree_twopow
    T P hP hper m (d + twopow (k + 1)) (k + 1) (twopow (k + 1) - 1)
    (by rw [Rule30UOR.Core.twopow_succ]; omega) (by omega) (fun s hs => by
      have hstep : (d + twopow (k + 1)) + s = (d + twopow k) + (twopow k + s) := by
        rw [Rule30UOR.Core.twopow_succ]; omega
      rw [hstep]
      exact hmp (twopow k + s) (by omega))
  have hflip := periodic_late_response_reset_flip_of_doubles_and_eq
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset3 heq0
  rw [heq1] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem not_centerPeriodic_of_maskparity_zero_agree_three_twopow_reset_doubles_prop
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset3 : SettledBy (z + 3) ((z + 3) + twopow k))
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hmp : ∀ s : Nat, s ≤ S →
      Rule30UOR.Scale.maskparity (((d + twopow k) + s) + m * P) 0 =
        Rule30UOR.Scale.maskparity ((d + twopow k) + s) 0) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_maskparity_zero_agree_three_twopow_reset_doubles
    T P m d z k S hP hz hd hdz hdm ht hset0 hset3 hS hmp

/-- **Single-Window (`2^k + 2^(k+1) ≤ S + 1`) Refutation of `CenterPeriodic` Across the Reset Diagonal `d + m * P = z + 3` from `LhColAgree` Without `DoublesAt (m * P) z` or `z ≤ k` (`not_centerPeriodic_of_lhColAgree_one_three_twopow_reset_doubles`, 9.1050)**:
    for every `T, P, m, d, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `DoublesAt (twopow k) z`, `d ≤ z`, `d + m * P = z + 3`, `T ≤ d + twopow k`, `settle d ≤ d + twopow k`, `settle (z + 3) ≤ (z + 3) + twopow k`, and `twopow k + twopow (k + 1) ≤ S + 1`, if `LhColAgree (d + twopow k) (m * P) 1 S` holds, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhColAgree_one_three_twopow_reset_doubles
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + twopow k)
    (hset0 : settle d ≤ d + twopow k) (hset3 : settle (z + 3) ≤ (z + 3) + twopow k)
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hlh : LhColAgree (d + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hpos0 := Rule30UOR.Scale.twopow_pos k
  have hpos1 := Rule30UOR.Scale.twopow_pos (k + 1)
  have heq0 := periodic_response_eq_of_lhColAgree_one_twopow
    T P hP hper m (d + twopow k) k (twopow k - 1) ht (by omega)
    (fun s hs => hlh s (by omega))
  have heq1 := periodic_response_eq_of_lhColAgree_one_twopow
    T P hP hper m (d + twopow (k + 1)) (k + 1) (twopow (k + 1) - 1)
    (by rw [Rule30UOR.Core.twopow_succ]; omega) (by omega) (fun s hs => by
      have hstep : (d + twopow (k + 1)) + s = (d + twopow k) + (twopow k + s) := by
        rw [Rule30UOR.Core.twopow_succ]; omega
      rw [hstep]
      exact hlh (twopow k + s) (by omega))
  have hflip := periodic_late_response_reset_flip_of_doubles_and_eq
    T P hP hper m d z k hz hd hdz hdm ht hset0 hset3 heq0
  rw [heq1] at hflip
  revert hflip
  cases Rule30UOR.Scale.response (d + twopow (k + 1)) (k + 1) <;> decide

theorem not_centerPeriodic_of_lhColAgree_one_three_twopow_reset_doubles_prop
    (T P m d z k S : Nat) (hP : 0 < P) (hz : IsZeroDiag z) (hd : DoublesAt (twopow k) z)
    (hdz : d ≤ z) (hdm : d + m * P = z + 3) (ht : T ≤ d + twopow k)
    (hset0 : SettledBy d (d + twopow k)) (hset3 : SettledBy (z + 3) ((z + 3) + twopow k))
    (hS : twopow k + twopow (k + 1) ≤ S + 1)
    (hlh : LhColAgree (d + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhColAgree_one_three_twopow_reset_doubles
    T P m d z k S hP hz hd hdz hdm ht hset0 hset3 hS hlh

/-- Rule 30 on the right-half columns `p ≥ 1` with column `0` prescribed by the driver `c`
    and initial right half `x` (`kit [33]`, `Rule30Ether.drv`). -/
def drv (c x : Nat → Bool) : Nat → Nat → Bool
  | 0, p => if p = 0 then c 0 else x p
  | k + 1, 0 => c (k + 1)
  | k + 1, p + 1 => bxor (drv c x k p) (drv c x k (p + 1) || drv c x k (p + 2))

/-- The driven right half (`kit [33]`) with center driver started at time `td` (`s ↦ center (td + s)`)
    and initial right-half state taken from row `tx` (`q ↦ rhCenter tx q`). -/
def rdrv (td tx k p : Nat) : Bool :=
  drv (fun s => Rule30UOR.Core.center (td + s)) (fun q => rhCenter tx q) k p

theorem drv_col0 (c x : Nat → Bool) : ∀ k : Nat, drv c x k 0 = c k
  | 0 => by simp [drv]
  | _ + 1 => rfl

theorem drv_init (c x : Nat → Bool) (p : Nat) (hp : 1 ≤ p) : drv c x 0 p = x p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp [drv]

theorem rdrv_col0 (td tx k : Nat) : rdrv td tx k 0 = Rule30UOR.Core.center (td + k) :=
  drv_col0 _ _ k

theorem rdrv_init (td tx p : Nat) (hp : 1 ≤ p) : rdrv td tx 0 p = rhCenter tx p :=
  drv_init _ _ p hp

theorem drv_congr_drive {c c' x : Nat → Bool} :
    ∀ k : Nat, (∀ s : Nat, s ≤ k → c s = c' s) → ∀ p : Nat, drv c x k p = drv c' x k p
  | 0, hc, 0 => by rw [drv_col0, drv_col0, hc 0 (Nat.le_refl 0)]
  | 0, _hc, p + 1 => by rw [drv_init _ _ (p + 1) (by omega), drv_init _ _ (p + 1) (by omega)]
  | k + 1, hc, 0 => by rw [drv_col0, drv_col0, hc (k + 1) (Nat.le_refl _)]
  | k + 1, hc, p + 1 => by
    have hc' : ∀ s : Nat, s ≤ k → c s = c' s := fun s hs => hc s (by omega)
    show bxor (drv c x k p) (drv c x k (p + 1) || drv c x k (p + 2)) =
      bxor (drv c' x k p) (drv c' x k (p + 1) || drv c' x k (p + 2))
    rw [drv_congr_drive k hc' p, drv_congr_drive k hc' (p + 1), drv_congr_drive k hc' (p + 2)]

/-- **Exact Diagonal Readout of the Driven Right Half `rdrv` (`rdrv_diag_eq_rhCenter`, 9.1051, `kit [33]`)**:
    for all `t, k, p ∈ ℕ`, when the drive time `td` and initial-state time `tx` both equal `t`, `rdrv t t k p = rhCenter (t + k) p` — from any time `t` on, the true right half is the right half driven by the true center column from the true row at time `t`! -/
theorem rdrv_diag_eq_rhCenter (t k p : Nat) :
    rdrv t t k p = rhCenter (t + k) p := by
  induction k generalizing p with
  | zero =>
    rcases p with _ | p
    · rw [rdrv_col0, Nat.add_zero, rhCenter_zero_eq_center]
    · rw [rdrv_init t t (p + 1) (by omega)]; rfl
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rhCenter_zero_eq_center]
    · show bxor (rdrv t t k p) (rdrv t t k (p + 1) || rdrv t t k (p + 2)) =
        rhCenter (t + (k + 1)) (p + 1)
      rw [ih p, ih (p + 1), ih (p + 2),
        show t + (k + 1) = (t + k) + 1 by omega,
        rhCenter_step_succ (t + k) p]

/-- **All-White Seed Readout of the Driven Right Half `rdrv` (`rdrv_zero_eq_rhCenter`, 9.1052, `kit [33]`)**:
    for all `t, p ∈ ℕ`, `rdrv 0 0 t p = rhCenter t p` — from time `0` (where the initial right half is white, `rhCenter 0 q = false` for all `q ≥ 1`), the right half `rhCenter t p` (and in particular column `1`, `rhCenter t 1 = rdrv 0 0 t 1`) is driven purely by the center column `center`! -/
theorem rdrv_zero_eq_rhCenter (t p : Nat) :
    rdrv 0 0 t p = rhCenter t p := by
  have h := rdrv_diag_eq_rhCenter 0 t p
  rwa [Nat.zero_add] at h

/-- **Interior Rule-30 Evolution Law of the Driven Right Half `rdrv` (`rdrv_step_succ`, 9.1053)**:
    for all `td, tx, k, p ∈ ℕ`, `rdrv td tx (k + 1) (p + 1) = bxor (rdrv td tx k p) (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))`! -/
theorem rdrv_step_succ (td tx k p : Nat) :
    rdrv td tx (k + 1) (p + 1) =
      bxor (rdrv td tx k p) (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) := rfl

/-- **Complete Independence of the Center Drive Outside the Drive Cone (`rdrv_drive_indep_of_lt`, 9.1054)**:
    for all `td, td', tx, k, p ∈ ℕ` with `k < p`, `rdrv td tx k p = rdrv td' tx k p` — because signals from column `0` travel right at speed at most `1`, at step `k < p` the cell `rdrv td tx k p` is completely independent of the center drive `td`! -/
theorem rdrv_drive_indep_of_lt (td td' tx k p : Nat) (hkp : k < p) :
    rdrv td tx k p = rdrv td' tx k p := by
  induction k generalizing p with
  | zero =>
    rw [rdrv_init td tx p (by omega), rdrv_init td' tx p (by omega)]
  | succ k ih =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [rdrv_step_succ td tx k q, rdrv_step_succ td' tx k q,
      ih q (by omega), ih (q + 1) (by omega), ih (q + 2) (by omega)]

/-- **Drive-Shift Invariance of the Driven Right Half `rdrv` Under `CenterPeriodic` (`periodic_rdrv_drive_shift_eq`, 9.1055)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, td, tx, k, p ∈ ℕ` with `T ≤ td`, shifting the drive start time by `m * P` leaves the driven right half identically unchanged: `rdrv (td + m * P) tx k p = rdrv td tx k p`! -/
theorem periodic_rdrv_drive_shift_eq
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m td tx k p : Nat) (htd : T ≤ td) :
    rdrv (td + m * P) tx k p = rdrv td tx k p := by
  unfold rdrv
  refine drv_congr_drive k (fun s _hs => ?_) p
  rw [show (td + m * P) + s = (td + s) + m * P by omega]
  exact Rule30UOR.Scale.center_mul hper m (td + s) (by omega)

/-- **Same-Drive Representation of the `m * P`-Shifted Right Half Under `CenterPeriodic` (`periodic_rhCenter_shift_eq_rdrv_same_drive`, 9.1056)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, p ∈ ℕ` with `T ≤ t`, `rhCenter ((t + m * P) + k) p = rdrv t (t + m * P) k p` — the `m * P`-shifted right half `rhCenter ((t + m * P) + k) p` and the unshifted right half `rhCenter (t + k) p = rdrv t t k p` are evolved by the exact same center drive `t`, differing only in their initial right-half row `t + m * P` vs `t`! -/
theorem periodic_rhCenter_shift_eq_rdrv_same_drive
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k p : Nat) (ht : T ≤ t) :
    rhCenter ((t + m * P) + k) p = rdrv t (t + m * P) k p := by
  rw [← rdrv_diag_eq_rhCenter (t + m * P) k p,
    periodic_rdrv_drive_shift_eq T P hP hper m t (t + m * P) k p ht]

/-! ### Batch 51: Drive-Cone Causality of `rdrv` (`kit [33]`), Derivation of `maskparity · 0` Agreement from Same-Drive Right-Half Slice and Strip Agreement, and Zero-Diagonal / Dyadic Refutation Engines (9.1057–9.1071) -/

/-- **Outside-the-Drive-Cone Exact Readout of `rdrv` (`rdrv_outside_cone_eq_rhCenter`, 9.1057)**:
    for all `td, tx, k, p ∈ ℕ` with `k < p`, `rdrv td tx k p = rhCenter (tx + k) p` — outside the drive cone `k < p`, for ANY drive time `td`, the driven right half equals the true right half `rhCenter (tx + k) p` evolved from `tx`! -/
theorem rdrv_outside_cone_eq_rhCenter (td tx k p : Nat) (hkp : k < p) :
    rdrv td tx k p = rhCenter (tx + k) p := by
  rw [rdrv_drive_indep_of_lt td tx tx k p hkp, rdrv_diag_eq_rhCenter tx k p]

/-- **Semigroup Restart Law of the Driven Right Half `rdrv` (`rdrv_semigroup_add`, 9.1058)**:
    for all `t, a, k, p ∈ ℕ`, `rdrv t t (a + k) p = rdrv (t + a) (t + a) k p` — running the driven right half for `a + k` steps from `t` is identical to restarting it at `t + a` for `k` steps! -/
theorem rdrv_semigroup_add (t a k p : Nat) :
    rdrv t t (a + k) p = rdrv (t + a) (t + a) k p := by
  rw [rdrv_diag_eq_rhCenter t (a + k) p,
    rdrv_diag_eq_rhCenter (t + a) k p,
    Nat.add_assoc]

/-- **Sharp Drive-Cone Causality of the Driven Right Half `rdrv` (`rdrv_drive_causal_cone`, 9.1059, `kit [33]`)**:
    for all `td, td', tx, k, p ∈ ℕ`, if `∀ s, s + p ≤ k → center (td + s) = center (td' + s)`, then `rdrv td tx k p = rdrv td' tx k p` — at step `k` and column `p`, `rdrv td tx k p` depends on the center drive `s ↦ center (td + s)` ONLY inside the causal drive cone `s + p ≤ k`! -/
theorem rdrv_drive_causal_cone (td td' tx k p : Nat)
    (hc : ∀ s : Nat, s + p ≤ k →
      Rule30UOR.Core.center (td + s) = Rule30UOR.Core.center (td' + s)) :
    rdrv td tx k p = rdrv td' tx k p := by
  induction k generalizing p with
  | zero =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0, hc 0 (by omega)]
    · rw [rdrv_init td tx (p + 1) (by omega), rdrv_init td' tx (p + 1) (by omega)]
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0, hc (k + 1) (by omega)]
    · rw [rdrv_step_succ td tx k p, rdrv_step_succ td' tx k p,
        ih p (fun s hs => hc s (by omega)),
        ih (p + 1) (fun s hs => hc s (by omega)),
        ih (p + 2) (fun s hs => hc s (by omega))]

/-- **Initial-Slice Causality of the Driven Right Half `rdrv` Under a Shared Drive (`rdrv_init_causal_cone`, 9.1060, `kit [33]`)**:
    for all `td, tx, Q, L, k, p ∈ ℕ`, if `RhBandAgree tx Q 1 L` holds (columns `1, …, L + 1` agree between `tx + Q` and `tx`) and `p + k ≤ L + 1`, then `rdrv td (tx + Q) k p = rdrv td tx k p` under the shared drive `td`! -/
theorem rdrv_init_causal_cone (td tx Q L k p : Nat)
    (hband : RhBandAgree tx Q 1 L) (hpk : p + k ≤ L + 1) :
    rdrv td (tx + Q) k p = rdrv td tx k p := by
  induction k generalizing p with
  | zero =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [rdrv_init td (tx + Q) (p + 1) (by omega),
        rdrv_init td tx (p + 1) (by omega),
        show p + 1 = 1 + p by omega]
      exact hband p (by omega)
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [rdrv_step_succ td (tx + Q) k p, rdrv_step_succ td tx k p,
        ih p (by omega), ih (p + 1) (by omega), ih (p + 2) (by omega)]

/-- **Same-Drive Column-`1` Agreement of `rdrv` Over `[0, S]` from Initial Slice `RhBandAgree` (`rdrv_col_one_agree_of_rhBandAgree_one`, 9.1061)**:
    for all `td, tx, Q, S, s ∈ ℕ`, if `RhBandAgree tx Q 1 S` holds and `s ≤ S`, then `rdrv td (tx + Q) s 1 = rdrv td tx s 1`! -/
theorem rdrv_col_one_agree_of_rhBandAgree_one (td tx Q S s : Nat)
    (hband : RhBandAgree tx Q 1 S) (hs : s ≤ S) :
    rdrv td (tx + Q) s 1 = rdrv td tx s 1 :=
  rdrv_init_causal_cone td tx Q S s 1 hband (by omega)

/-- **Derivation of `RhColAgree t (m * P) 1 S` from `RhBandAgree t (m * P) 1 S` via the Driven Right Half `rdrv` (`periodic_rhColAgree_one_of_rhBandAgree_one`, 9.1062)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S ∈ ℕ` with `T ≤ t`, `RhBandAgree t (m * P) 1 S` implies `RhColAgree t (m * P) 1 S` because both `t + m * P` and `t` are driven by the identical center drive `t`! -/
theorem periodic_rhColAgree_one_of_rhBandAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t) (hband : RhBandAgree t (m * P) 1 S) :
    RhColAgree t (m * P) 1 S := by
  intro s hs
  rw [show (t + s) + m * P = (t + m * P) + s by omega,
    periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t s 1 ht,
    ← rdrv_diag_eq_rhCenter t s 1]
  exact rdrv_col_one_agree_of_rhBandAgree_one t t (m * P) S s hband hs

/-- **Derivation of `maskparity · 0` Agreement Over `[t, t + S]` from `RhBandAgree t (m * P) 1 S` Under `CenterPeriodic` (`periodic_maskparity_zero_agree_of_rhBandAgree_one`, 9.1063)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 S` holds and `s ≤ S`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhBandAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t) (hband : RhBandAgree t (m * P) 1 S) (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hcol := periodic_rhColAgree_one_of_rhBandAgree_one T P hP hper m t S ht hband s hs
  have hlh := periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + s) (by omega) (fun _ => hcol)
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlh

/-- **Derivation of `maskparity · 0` Agreement from Same-Drive `rdrv` Column-`1` Agreement at White Centers (`periodic_maskparity_zero_agree_of_rdrv_one_agree`, 9.1064)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t`, if `center (t + s) = false → rdrv t (t + m * P) s 1 = rdrv t t s 1`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rdrv_one_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hw : Rule30UOR.Core.center (t + s) = false →
      rdrv t (t + m * P) s 1 = rdrv t t s 1) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlh : lhCenter ((t + s) + m * P) 1 = lhCenter (t + s) 1 := by
    refine periodic_lhCenter_one_eq_of_white_center T P hP hper m (t + s) (by omega) (fun hc => ?_)
    rw [show (t + s) + m * P = (t + m * P) + s by omega,
      periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t s 1 ht,
      ← rdrv_diag_eq_rhCenter t s 1]
    exact hw hc
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlh

/-- **Bounded-Width Strip Determination Law of the Driven Right Half `rdrv` (`rdrv_strip_agree_of_rhBandAgree_and_col_agree`, 9.1065)**:
    for all `td, tx, Q, B, S, s, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at step `0` (across columns `1, …, B + 1`) and `∀ u < S, rdrv td (tx + Q) u (B + 2) = rdrv td tx u (B + 2)` holds at the right boundary column `B + 2`, then for ALL `s ≤ S` and ALL `p ≤ B + 1`, `rdrv td (tx + Q) s p = rdrv td tx s p` (without widening the spatial slice `B + 1` as `S` grows)! -/
theorem rdrv_strip_agree_of_rhBandAgree_and_col_agree
    (td tx Q B S s p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hcol : ∀ u : Nat, u < S →
      rdrv td (tx + Q) u (B + 2) = rdrv td tx u (B + 2))
    (hs : s ≤ S) (hp : p ≤ B + 1) :
    rdrv td (tx + Q) s p = rdrv td tx s p := by
  induction s generalizing p with
  | zero =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [rdrv_init td (tx + Q) (p + 1) (by omega),
        rdrv_init td tx (p + 1) (by omega),
        show p + 1 = 1 + p by omega]
      exact hband p (by omega)
  | succ s ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [rdrv_step_succ td (tx + Q) s p, rdrv_step_succ td tx s p,
        ih p (by omega) (by omega),
        ih (p + 1) (by omega) (by omega)]
      by_cases hlt : p < B
      · rw [ih (p + 2) (by omega) (by omega)]
      · have hpB : p + 2 = B + 2 := by omega
        rw [hpB, hcol s (by omega)]

/-- **Derivation of `maskparity · 0` Agreement Over `[t, t + S]` from Fixed-Width Strip Agreement (`periodic_maskparity_zero_agree_of_rhBandAgree_and_rhColAgree`, 9.1066)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, S, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` and `RhColAgree t (m * P) (B + 2) S` hold and `s ≤ S`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhBandAgree_and_rhColAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B S s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hcol : RhColAgree t (m * P) (B + 2) S) (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  refine rdrv_strip_agree_of_rhBandAgree_and_col_agree t t (m * P) B S s 1 hband (fun u hu => ?_) hs (by omega)
  rw [← periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t u (B + 2) ht,
    rdrv_diag_eq_rhCenter t u (B + 2),
    show (t + m * P) + u = (t + u) + m * P by omega]
  exact hcol u (by omega)

/-- **Refutation of `CenterPeriodic` from Same-Drive `rdrv` Column-`1` Agreement Over `p + 3 * (m * P)` Steps After a Zero Diagonal (`not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two`, 9.1067)**:
    for every `T, P, m, z, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if at every white center `center ((z + (p + 1)) + s) = false` (`s ≤ S`), `rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 = rdrv (z + (p + 1)) (z + (p + 1)) s 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 =
          rdrv (z + (p + 1)) (z + (p + 1)) s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hsetQ hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_one_agree
    T P hP hper m (z + (p + 1)) s ht (hw s hs)

theorem not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 =
          rdrv (z + (p + 1)) (z + (p + 1)) s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two
    T P m z p S hP hm ht hz hd hset1 hsetQ hS hw

/-- **Refutation of `CenterPeriodic` from Spatial Right-Half Slice Agreement `RhBandAgree (z + (p + 1)) (m * P) 1 S` at a Zero Diagonal (`not_centerPeriodic_of_rhBandAgree_one_at_zero_diag_step_two`, 9.1068)**:
    for every `T, P, m, z, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if `RhBandAgree (z + (p + 1)) (m * P) 1 S` holds at the single time `z + (p + 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_one_at_zero_diag_step_two
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two
    T P m z p S hP hm ht hz hd hset1 hsetQ hS (fun s hs _hc => ?_)
  exact rdrv_col_one_agree_of_rhBandAgree_one (z + (p + 1)) (z + (p + 1)) (m * P) S s hband hs

theorem not_centerPeriodic_of_rhBandAgree_one_at_zero_diag_step_two_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_one_at_zero_diag_step_two
    T P m z p S hP hm ht hz hd hset1 hsetQ hS hband

/-- **Refutation of `CenterPeriodic` from Fixed-Width Right-Half Strip Agreement at a Zero Diagonal (`not_centerPeriodic_of_strip_agree_at_zero_diag_step_two`, 9.1069)**:
    for every `T, P, m, z, p, B, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if `RhBandAgree (z + (p + 1)) (m * P) 1 B` and `RhColAgree (z + (p + 1)) (m * P) (B + 2) S` hold, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_strip_agree_at_zero_diag_step_two
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hcol : RhColAgree (z + (p + 1)) (m * P) (B + 2) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hsetQ hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree_and_rhColAgree
    T P hP hper m (z + (p + 1)) B S s ht hband hcol hs

theorem not_centerPeriodic_of_strip_agree_at_zero_diag_step_two_prop
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hcol : RhColAgree (z + (p + 1)) (m * P) (B + 2) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_strip_agree_at_zero_diag_step_two
    T P m z p B S hP hm ht hz hd hset1 hsetQ hS hband hcol

/-- **Dyadic (`2^k - m * P`) Refutation of `CenterPeriodic` from Same-Drive `rdrv` Column-`1` Agreement (`not_centerPeriodic_of_rdrv_one_agree_sub_twopow_ge`, 9.1070)**:
    for every `T, P, m, k, S ∈ ℕ` with `0 < P`, `0 < m`, `m * P ≤ twopow k`, `T + m * P ≤ twopow k`, and `twopow k ≤ S + 1`, if at every white center `center ((twopow k - m * P) + s) = false` (`s ≤ S`), `rdrv (twopow k - m * P) (twopow k) s 1 = rdrv (twopow k - m * P) (twopow k - m * P) s 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_one_agree_sub_twopow_ge
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((twopow k - m * P) + s) = false →
        rdrv (twopow k - m * P) (twopow k) s 1 =
          rdrv (twopow k - m * P) (twopow k - m * P) s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_sub_twopow
    T P m k S hP hm ht hS (fun s hs => ?_) hper
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree
    T P hP hper m (twopow k - m * P) s (by omega) (fun hc => ?_)
  rw [show (twopow k - m * P) + m * P = twopow k by omega]
  exact hw s hs hc

theorem not_centerPeriodic_of_rdrv_one_agree_sub_twopow_ge_prop
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((twopow k - m * P) + s) = false →
        rdrv (twopow k - m * P) (twopow k) s 1 =
          rdrv (twopow k - m * P) (twopow k - m * P) s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rdrv_one_agree_sub_twopow_ge
    T P m k S hP hm hmP ht hS hw

/-- **Dyadic (`2^k - m * P`) Refutation of `CenterPeriodic` from Spatial Right-Half Slice Agreement `RhBandAgree (2^k - m * P) (m * P) 1 S` (`not_centerPeriodic_of_rhBandAgree_one_sub_twopow_ge`, 9.1071)**:
    for every `T, P, m, k, S ∈ ℕ` with `0 < P`, `0 < m`, `m * P ≤ twopow k`, `T + m * P ≤ twopow k`, and `twopow k ≤ S + 1`, if `RhBandAgree (twopow k - m * P) (m * P) 1 S` holds at time `twopow k - m * P`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_one_sub_twopow_ge
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hband : RhBandAgree (twopow k - m * P) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_rdrv_one_agree_sub_twopow_ge
    T P m k S hP hm hmP ht hS (fun s hs _hc => ?_)
  have h := rdrv_col_one_agree_of_rhBandAgree_one
    (twopow k - m * P) (twopow k - m * P) (m * P) S s hband hs
  rwa [show (twopow k - m * P) + m * P = twopow k by omega] at h

theorem not_centerPeriodic_of_rhBandAgree_one_sub_twopow_ge_prop
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hband : RhBandAgree (twopow k - m * P) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_one_sub_twopow_ge
    T P m k S hP hm hmP ht hS hband

/-! ### Batch 52: Inward Determination of the Driven Right Half `rdrv` (`kit [33]` + `kit [23]`), Drive-Cancelling Column-`1` Defect Laws, Right-Edge `2^e`-Periodicity in `rdrv`, and Multi-Column Inward Propagation to `maskparity · 0` Agreement (9.1072–9.1086) -/

/-- **Exact Inward Rule-30 Inversion in the Driven Right Half `rdrv` (`rdrv_inward_bxor`, 9.1072, `kit [33]` + `kit [23]`)**:
    for all `td, tx, k, p ∈ ℕ`, `rdrv td tx k p = bxor (rdrv td tx (k + 1) (p + 1)) (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))` — every cell `(k, p)` of the driven right half is algebraically determined by columns `p + 1` and `p + 2` to its right! -/
theorem rdrv_inward_bxor (td tx k p : Nat) :
    rdrv td tx k p =
      bxor (rdrv td tx (k + 1) (p + 1)) (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) := by
  rw [rdrv_step_succ td tx k p]
  cases rdrv td tx k p <;> cases (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) <;> rfl

/-- **Black-Left OR-Masking in the Inward Step of `rdrv` (`rdrv_inward_of_black_left`, 9.1073)**:
    for all `td, tx, k, p ∈ ℕ`, whenever `rdrv td tx k (p + 1) = true`, `rdrv td tx k p = !rdrv td tx (k + 1) (p + 1)` unconditionally (absorbing `rdrv td tx k (p + 2)`)! -/
theorem rdrv_inward_of_black_left (td tx k p : Nat)
    (hb : rdrv td tx k (p + 1) = true) :
    rdrv td tx k p = !rdrv td tx (k + 1) (p + 1) := by
  rw [rdrv_inward_bxor td tx k p, hb, Bool.true_or]
  cases rdrv td tx (k + 1) (p + 1) <;> rfl

/-- **Black-Right OR-Masking in the Inward Step of `rdrv` (`rdrv_inward_of_black_right`, 9.1074)**:
    for all `td, tx, k, p ∈ ℕ`, whenever `rdrv td tx k (p + 2) = true`, `rdrv td tx k p = !rdrv td tx (k + 1) (p + 1)` unconditionally (absorbing `rdrv td tx k (p + 1)`)! -/
theorem rdrv_inward_of_black_right (td tx k p : Nat)
    (hb : rdrv td tx k (p + 2) = true) :
    rdrv td tx k p = !rdrv td tx (k + 1) (p + 1) := by
  rw [rdrv_inward_bxor td tx k p, hb, Bool.or_true]
  cases rdrv td tx (k + 1) (p + 1) <;> rfl

/-- **Direct Center-Drive Evolution of Column `1` of `rdrv` (`rdrv_step_one_eq_center_xor_or`, 9.1075, `kit [33]`)**:
    for all `td, tx, k ∈ ℕ`, `rdrv td tx (k + 1) 1 = bxor (center (td + k)) (rdrv td tx k 1 || rdrv td tx k 2)`! -/
theorem rdrv_step_one_eq_center_xor_or (td tx k : Nat) :
    rdrv td tx (k + 1) 1 =
      bxor (Rule30UOR.Core.center (td + k)) (rdrv td tx k 1 || rdrv td tx k 2) := by
  rw [rdrv_step_succ td tx k 0, rdrv_col0]

/-- **Black Column-`1` OR-Absorption in `rdrv` (`rdrv_step_one_eq_not_center_of_black_one`, 9.1076)**:
    for all `td, tx, k ∈ ℕ`, whenever `rdrv td tx k 1 = true`, `rdrv td tx (k + 1) 1 = !center (td + k)` — completely independent of the initial state `tx` and of column `2`! -/
theorem rdrv_step_one_eq_not_center_of_black_one (td tx k : Nat)
    (hb : rdrv td tx k 1 = true) :
    rdrv td tx (k + 1) 1 = !Rule30UOR.Core.center (td + k) := by
  rw [rdrv_step_one_eq_center_xor_or td tx k, hb, Bool.true_or]
  cases Rule30UOR.Core.center (td + k) <;> rfl

/-- **Unconditional Drive-Cancellation Law for Column-`1` Defects in `rdrv` (`rdrv_step_one_defect_eq_or_defect`, 9.1077, `kit [33]`)**:
    for all `td, tx2, tx, k ∈ ℕ` (with NO `CenterPeriodic` hypothesis needed because both share the drive `td`!), `rdrv td tx2 (k + 1) 1 ⊕ rdrv td tx (k + 1) 1 = (rdrv td tx2 k 1 || rdrv td tx2 k 2) ⊕ (rdrv td tx k 1 || rdrv td tx k 2)`! -/
theorem rdrv_step_one_defect_eq_or_defect (td tx2 tx k : Nat) :
    bxor (rdrv td tx2 (k + 1) 1) (rdrv td tx (k + 1) 1) =
      bxor (rdrv td tx2 k 1 || rdrv td tx2 k 2) (rdrv td tx k 1 || rdrv td tx k 2) := by
  rw [rdrv_step_one_eq_center_xor_or td tx2 k, rdrv_step_one_eq_center_xor_or td tx k]
  cases Rule30UOR.Core.center (td + k) <;>
    cases (rdrv td tx2 k 1 || rdrv td tx2 k 2) <;>
    cases (rdrv td tx k 1 || rdrv td tx k 2) <;> rfl

/-- **Unconditional 1-Step Forward Pinning of Column `1` in `rdrv` Across a Black Cell (`rdrv_step_one_eq_of_black_one`, 9.1078)**:
    for all `td, tx2, tx, k ∈ ℕ`, whenever `rdrv td tx2 k 1 = true` and `rdrv td tx k 1 = true`, `rdrv td tx2 (k + 1) 1 = rdrv td tx (k + 1) 1` holds unconditionally for ANY drive `td` and ANY initial states `tx2, tx`! -/
theorem rdrv_step_one_eq_of_black_one (td tx2 tx k : Nat)
    (hb2 : rdrv td tx2 k 1 = true) (hb0 : rdrv td tx k 1 = true) :
    rdrv td tx2 (k + 1) 1 = rdrv td tx (k + 1) 1 := by
  rw [rdrv_step_one_eq_not_center_of_black_one td tx2 k hb2,
    rdrv_step_one_eq_not_center_of_black_one td tx k hb0]

/-- **Vanishing of the Driven Right Half `rdrv` Outside the Light Cone `p > tx + k` (`rdrv_gt_eq_false`, 9.1079)**:
    for all `td, tx, k, p ∈ ℕ` with `tx + k < p`, `rdrv td tx k p = false` for ANY center drive `td`! -/
theorem rdrv_gt_eq_false (td tx k p : Nat) (hgt : tx + k < p) :
    rdrv td tx k p = false := by
  rw [rdrv_outside_cone_eq_rhCenter td tx k p (by omega),
    rhCenter_gt_eq_false (tx + k) p hgt]

/-- **Black Right-Edge Diagonal of the Driven Right Half `rdrv` (`rdrv_self_eq_true`, 9.1080)**:
    for all `td, tx, k ∈ ℕ` with `0 < tx`, `rdrv td tx k (tx + k) = true` for ANY center drive `td`! -/
theorem rdrv_self_eq_true (td tx k : Nat) (htx : 0 < tx) :
    rdrv td tx k (tx + k) = true := by
  rw [rdrv_outside_cone_eq_rhCenter td tx k (tx + k) (by omega),
    rhCenter_self_eq_true (tx + k)]

/-- **Unconditional Right-Edge `2^e`-Shift Invariance of `rdrv` Outside the Drive Cone (`rdrv_diag_shift_twopow_eq`, 9.1081)**:
    for all `td, tx, e, k, p, v ∈ ℕ` with `k < p`, `p ≤ tx + k`, and `(tx + k) - p ≤ e`, `rdrv td (tx + v * twopow e) k (p + v * twopow e) = rdrv td tx k p`! -/
theorem rdrv_diag_shift_twopow_eq (td tx e k p v : Nat)
    (hkp : k < p) (hpt : p ≤ tx + k) (he : (tx + k) - p ≤ e) :
    rdrv td (tx + v * twopow e) k (p + v * twopow e) = rdrv td tx k p := by
  rw [rdrv_outside_cone_eq_rhCenter td (tx + v * twopow e) k (p + v * twopow e) (by omega),
    rdrv_outside_cone_eq_rhCenter td tx k p hkp,
    show (tx + v * twopow e) + k = (tx + k) + v * twopow e by omega]
  exact rhCenter_diag_shift_twopow_eq e (tx + k) p v hpt he

/-- **Single-Cell Inward Agreement Step in `rdrv` (`rdrv_inward_step_agree`, 9.1082)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, if `rdrv td tx2 (k + 1) (p + 1) = rdrv td tx (k + 1) (p + 1)` and `(rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2)) = (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))`, then `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_inward_step_agree (td tx2 tx k p : Nat)
    (hnext : rdrv td tx2 (k + 1) (p + 1) = rdrv td tx (k + 1) (p + 1))
    (hor : (rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2)) =
      (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))) :
    rdrv td tx2 k p = rdrv td tx k p := by
  rw [rdrv_inward_bxor td tx2 k p, rdrv_inward_bxor td tx k p, hnext, hor]

/-- **1-Column Inward Propagation of Temporal Agreement in `rdrv` (`rdrv_inward_two_col_step_agree`, 9.1083)**:
    for all `td, tx2, tx, S, p, s ∈ ℕ`, if column `p + 1` agrees over `[0, S + 1]` and column `p + 2` agrees over `[0, S]`, then column `p` agrees at every step `s ≤ S`! -/
theorem rdrv_inward_two_col_step_agree (td tx2 tx S p s : Nat)
    (hc1 : ∀ u : Nat, u ≤ S + 1 → rdrv td tx2 u (p + 1) = rdrv td tx u (p + 1))
    (hc2 : ∀ u : Nat, u ≤ S → rdrv td tx2 u (p + 2) = rdrv td tx u (p + 2))
    (hs : s ≤ S) :
    rdrv td tx2 s p = rdrv td tx s p := by
  refine rdrv_inward_step_agree td tx2 tx s p (hc1 (s + 1) (by omega)) ?_
  rw [hc1 s (by omega), hc2 s hs]

/-- **Multi-Column (`K`-Step) Inward Propagation of Temporal Agreement in `rdrv` (`rdrv_inward_two_col_propagate`, 9.1084)**:
    for all `td, tx2, tx, K, p0, S, s ∈ ℕ`, if two adjacent columns `p0 + K` and `(p0 + K) + 1` agree in `rdrv` over `[0, S + K]`, then marching `K` columns leftward forces `rdrv td tx2 s p0 = rdrv td tx s p0` for all `s ≤ S` (with ZERO spatial initial slice hypothesis `RhBandAgree` on columns `p0, …, p0 + K - 1`!)! -/
theorem rdrv_inward_two_col_propagate_aux (td tx2 tx K p0 S : Nat)
    (hc1 : ∀ u : Nat, u ≤ S + K → rdrv td tx2 u (p0 + K) = rdrv td tx u (p0 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K → rdrv td tx2 u ((p0 + K) + 1) = rdrv td tx u ((p0 + K) + 1)) :
    (∀ s : Nat, s ≤ S → rdrv td tx2 s p0 = rdrv td tx s p0) ∧
      (∀ s : Nat, s ≤ S → rdrv td tx2 s (p0 + 1) = rdrv td tx s (p0 + 1)) := by
  induction K generalizing p0 S with
  | zero =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have h := hc1 s (by omega)
      rwa [Nat.add_zero] at h
    · have h := hc2 s (by omega)
      rwa [Nat.add_zero] at h
  | succ K ih =>
    have hc1' : ∀ u : Nat, u ≤ (S + 1) + K →
        rdrv td tx2 u ((p0 + 1) + K) = rdrv td tx u ((p0 + 1) + K) := by
      intro u hu
      have h := hc1 u (by omega)
      rwa [show p0 + (K + 1) = (p0 + 1) + K by omega] at h
    have hc2' : ∀ u : Nat, u ≤ (S + 1) + K →
        rdrv td tx2 u (((p0 + 1) + K) + 1) = rdrv td tx u (((p0 + 1) + K) + 1) := by
      intro u hu
      have h := hc2 u (by omega)
      rwa [show p0 + (K + 1) = (p0 + 1) + K by omega] at h
    obtain ⟨ih1, ih2⟩ := ih (p0 + 1) (S + 1) hc1' hc2'
    refine ⟨fun s hs => ?_, fun s hs => ih1 s (by omega)⟩
    exact rdrv_inward_two_col_step_agree td tx2 tx S p0 s ih1
      (fun u hu => by
        have h := ih2 u (by omega)
        rwa [show (p0 + 1) + 1 = p0 + 2 by omega] at h) hs

theorem rdrv_inward_two_col_propagate (td tx2 tx K p0 S s : Nat)
    (hc1 : ∀ u : Nat, u ≤ S + K → rdrv td tx2 u (p0 + K) = rdrv td tx u (p0 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K → rdrv td tx2 u ((p0 + K) + 1) = rdrv td tx u ((p0 + K) + 1))
    (hs : s ≤ S) :
    rdrv td tx2 s p0 = rdrv td tx s p0 :=
  (rdrv_inward_two_col_propagate_aux td tx2 tx K p0 S hc1 hc2).1 s hs

/-- **Derivation of `maskparity · 0` Agreement Over `[t, t + S]` from Two-Column `rdrv` Agreement at Depth `1 + K` (`periodic_maskparity_zero_agree_of_rdrv_two_col_agree`, 9.1085)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, S, s ∈ ℕ` with `T ≤ t`, if columns `1 + K` and `(1 + K) + 1` of `rdrv` agree over `[0, S + K]`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for all `s ≤ S`! -/
theorem periodic_maskparity_zero_agree_of_rdrv_two_col_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K S s : Nat) (ht : T ≤ t)
    (hc1 : ∀ u : Nat, u ≤ S + K →
      rdrv t (t + m * P) u (1 + K) = rdrv t t u (1 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K →
      rdrv t (t + m * P) u ((1 + K) + 1) = rdrv t t u ((1 + K) + 1))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_inward_two_col_propagate t (t + m * P) t K 1 S s hc1 hc2 hs

/-- **Refutation of `CenterPeriodic` from Two-Column `rdrv` Agreement at Depth `1 + K` After a Zero Diagonal (`not_centerPeriodic_of_rdrv_two_col_agree_at_zero_diag`, 9.1086)**:
    for every `T, P, m, z, p, K, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if columns `1 + K` and `(1 + K) + 1` of `rdrv` agree over `[0, S + K]`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_two_col_agree_at_zero_diag
    (T P m z p K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S + K →
      rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) =
        rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K →
      rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u ((1 + K) + 1) =
        rdrv (z + (p + 1)) (z + (p + 1)) u ((1 + K) + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two
    T P m z p S hP hm ht hz hd hset1 hsetQ hS (fun s hs _hc => ?_)
  exact rdrv_inward_two_col_propagate
    (z + (p + 1)) ((z + (p + 1)) + m * P) (z + (p + 1)) K 1 S s hc1 hc2 hs

theorem not_centerPeriodic_of_rdrv_two_col_agree_at_zero_diag_prop
    (T P m z p K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S + K →
      rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) =
        rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K))
    (hc2 : ∀ u : Nat, u ≤ S + K →
      rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u ((1 + K) + 1) =
        rdrv (z + (p + 1)) (z + (p + 1)) u ((1 + K) + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rdrv_two_col_agree_at_zero_diag
    T P m z p K S hP hm ht hz hd hset1 hsetQ hS hc1 hc2

/-! ### Batch 53: Right-Threshold `2^e`-Periodicity, Zero-Gaps, and Black Runs in `rdrv`, Interior Defect Evolution, and Column-Plus-OR Inward Propagation to `maskparity · 0` Agreement and Refutations (9.1087–9.1101) -/

/-- **Right-Threshold Diagonal `2^e`-Shift Law in `rdrv` (`rdrv_diag_shift_twopow_eq_of_threshold`, 9.1087)**:
    for `IsRightThreshold e J`, `k < p`, `p ≤ tx + k`, and `(tx + k) - p ≤ J`, `rdrv td (tx + v * twopow e) k (p + v * twopow e) = rdrv td tx k p`! -/
theorem rdrv_diag_shift_twopow_eq_of_threshold (td tx e J k p v : Nat)
    (hJ : IsRightThreshold e J) (hkp : k < p) (hpt : p ≤ tx + k)
    (hJle : (tx + k) - p ≤ J) :
    rdrv td (tx + v * twopow e) k (p + v * twopow e) = rdrv td tx k p := by
  rw [rdrv_outside_cone_eq_rhCenter td (tx + v * twopow e) k (p + v * twopow e) (by omega),
    rdrv_outside_cone_eq_rhCenter td tx k p hkp]
  have h := rhCenter_diag_shift_twopow_eq_of_threshold e J p ((tx + k) - p) v hJ hJle
  rwa [show p + ((tx + k) - p) + v * twopow e = (tx + v * twopow e) + k by omega,
    show p + ((tx + k) - p) = tx + k by omega] at h

/-- **Right-Edge White Zero-Gap of Width `J` at Multiples of `2^e` in `rdrv` (`rdrv_zero_gap_of_threshold`, 9.1088)**:
    for `IsRightThreshold e J`, `1 ≤ j ≤ J`, and `k + j < u * twopow e`, `rdrv td (u * twopow e - k) k (u * twopow e - j) = false` for ANY center drive `td`! -/
theorem rdrv_zero_gap_of_threshold (td e J u k j : Nat)
    (hJ : IsRightThreshold e J) (hj1 : 1 ≤ j) (hjJ : j ≤ J)
    (hkju : k + j < u * twopow e) :
    rdrv td (u * twopow e - k) k (u * twopow e - j) = false := by
  rw [rdrv_outside_cone_eq_rhCenter td (u * twopow e - k) k (u * twopow e - j) (by omega),
    show (u * twopow e - k) + k = u * twopow e by omega]
  exact rhCenter_zero_gap_of_threshold e J u j hJ hj1 hjJ (by omega)

/-- **Right-Edge Black Run of Width `J + 1` at `(u + 1) * 2^e - 1` in `rdrv` (`rdrv_last_one_of_threshold`, 9.1089)**:
    for `IsRightThreshold e J`, `j ≤ J`, and `k + j < (u + 1) * twopow e - 1`, `rdrv td (((u + 1) * twopow e - 1) - k) k (((u + 1) * twopow e - 1) - j) = true` for ANY center drive `td`! -/
theorem rdrv_last_one_of_threshold (td e J u k j : Nat)
    (hJ : IsRightThreshold e J) (hjJ : j ≤ J)
    (hkju : k + j < (u + 1) * twopow e - 1) :
    rdrv td (((u + 1) * twopow e - 1) - k) k (((u + 1) * twopow e - 1) - j) = true := by
  rw [rdrv_outside_cone_eq_rhCenter td (((u + 1) * twopow e - 1) - k) k
      (((u + 1) * twopow e - 1) - j) (by omega),
    show (((u + 1) * twopow e - 1) - k) + k = (u + 1) * twopow e - 1 by omega]
  exact rhCenter_last_one_of_threshold e J u j hJ hjJ (by omega)

/-- **Interior Defect Evolution Law in `rdrv` (`rdrv_defect_step_succ`, 9.1090)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, the defect at `(k + 1, p + 1)` equals the defect at `(k, p)` XOR the OR-defect at `(k, p + 1), (k, p + 2)`! -/
theorem rdrv_defect_step_succ (td tx2 tx k p : Nat) :
    bxor (rdrv td tx2 (k + 1) (p + 1)) (rdrv td tx (k + 1) (p + 1)) =
      bxor (bxor (rdrv td tx2 k p) (rdrv td tx k p))
        (bxor (rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2))
          (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))) := by
  rw [rdrv_step_succ td tx2 k p, rdrv_step_succ td tx k p]
  cases rdrv td tx2 k p <;>
    cases rdrv td tx k p <;>
    cases (rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2)) <;>
    cases (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) <;> rfl

/-- **Inward Defect Evolution Law in `rdrv` (`rdrv_defect_inward_step`, 9.1091)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, the defect at `(k, p)` equals the defect at `(k + 1, p + 1)` XOR the OR-defect at `(k, p + 1), (k, p + 2)`! -/
theorem rdrv_defect_inward_step (td tx2 tx k p : Nat) :
    bxor (rdrv td tx2 k p) (rdrv td tx k p) =
      bxor (bxor (rdrv td tx2 (k + 1) (p + 1)) (rdrv td tx (k + 1) (p + 1)))
        (bxor (rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2))
          (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))) := by
  rw [rdrv_inward_bxor td tx2 k p, rdrv_inward_bxor td tx k p]
  cases rdrv td tx2 (k + 1) (p + 1) <;>
    cases rdrv td tx (k + 1) (p + 1) <;>
    cases (rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2)) <;>
    cases (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) <;> rfl

/-- **Unconditional Column-`1` Step Agreement from OR-Agreement in `rdrv` (`rdrv_step_one_eq_of_or_eq`, 9.1092)**:
    for all `td, tx2, tx, k ∈ ℕ` (with NO `CenterPeriodic` needed!), if `(rdrv td tx2 k 1 || rdrv td tx2 k 2) = (rdrv td tx k 1 || rdrv td tx k 2)`, then `rdrv td tx2 (k + 1) 1 = rdrv td tx (k + 1) 1`! -/
theorem rdrv_step_one_eq_of_or_eq (td tx2 tx k : Nat)
    (hor : (rdrv td tx2 k 1 || rdrv td tx2 k 2) = (rdrv td tx k 1 || rdrv td tx k 2)) :
    rdrv td tx2 (k + 1) 1 = rdrv td tx (k + 1) 1 := by
  rw [rdrv_step_one_eq_center_xor_or td tx2 k,
    rdrv_step_one_eq_center_xor_or td tx k, hor]

/-- **Unconditional OR-Agreement from Column-`1` Step Agreement in `rdrv` (`rdrv_or_one_eq_of_step_one_eq`, 9.1093)**:
    for all `td, tx2, tx, k ∈ ℕ`, if `rdrv td tx2 (k + 1) 1 = rdrv td tx (k + 1) 1`, then `(rdrv td tx2 k 1 || rdrv td tx2 k 2) = (rdrv td tx k 1 || rdrv td tx k 2)`! -/
theorem rdrv_or_one_eq_of_step_one_eq (td tx2 tx k : Nat)
    (hstep : rdrv td tx2 (k + 1) 1 = rdrv td tx (k + 1) 1) :
    (rdrv td tx2 k 1 || rdrv td tx2 k 2) = (rdrv td tx k 1 || rdrv td tx k 2) := by
  have hd := rdrv_step_one_defect_eq_or_defect td tx2 tx k
  rw [hstep] at hd
  revert hd
  cases rdrv td tx (k + 1) 1 <;>
    cases (rdrv td tx2 k 1 || rdrv td tx2 k 2) <;>
    cases (rdrv td tx k 1 || rdrv td tx k 2) <;> decide

/-- **Constant Diagonal Step Across a White Pair in `rdrv` (`rdrv_diag_eq_of_white_pair`, 9.1094)**:
    for all `td, tx, k, p ∈ ℕ`, whenever `rdrv td tx k (p + 1) = false` and `rdrv td tx k (p + 2) = false`, `rdrv td tx (k + 1) (p + 1) = rdrv td tx k p`! -/
theorem rdrv_diag_eq_of_white_pair (td tx k p : Nat)
    (hw1 : rdrv td tx k (p + 1) = false) (hw2 : rdrv td tx k (p + 2) = false) :
    rdrv td tx (k + 1) (p + 1) = rdrv td tx k p := by
  rw [rdrv_step_succ td tx k p, hw1, hw2, Bool.false_or]
  cases rdrv td tx k p <;> rfl

/-- **Linear Diagonal Defect Step Under OR-Agreement in `rdrv` (`rdrv_defect_diag_eq_of_or_eq`, 9.1095)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, whenever `(rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2)) = (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))`, the defect propagates linearly down-right: `bxor (rdrv td tx2 (k + 1) (p + 1)) (rdrv td tx (k + 1) (p + 1)) = bxor (rdrv td tx2 k p) (rdrv td tx k p)`! -/
theorem rdrv_defect_diag_eq_of_or_eq (td tx2 tx k p : Nat)
    (hor : (rdrv td tx2 k (p + 1) || rdrv td tx2 k (p + 2)) =
      (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))) :
    bxor (rdrv td tx2 (k + 1) (p + 1)) (rdrv td tx (k + 1) (p + 1)) =
      bxor (rdrv td tx2 k p) (rdrv td tx k p) := by
  rw [rdrv_defect_step_succ td tx2 tx k p, hor]
  cases bxor (rdrv td tx2 k p) (rdrv td tx k p) <;>
    cases (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) <;> rfl

/-- **Inward Agreement Across a Black Left Column in `rdrv` (`rdrv_agree_inward_of_black_left`, 9.1096)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, whenever `rdrv td tx2 k (p + 1) = true`, `rdrv td tx k (p + 1) = true`, and `rdrv td tx2 (k + 1) (p + 1) = rdrv td tx (k + 1) (p + 1)`, we have `rdrv td tx2 k p = rdrv td tx k p` without needing column `p + 2`! -/
theorem rdrv_agree_inward_of_black_left (td tx2 tx k p : Nat)
    (hb2 : rdrv td tx2 k (p + 1) = true) (hb0 : rdrv td tx k (p + 1) = true)
    (hnext : rdrv td tx2 (k + 1) (p + 1) = rdrv td tx (k + 1) (p + 1)) :
    rdrv td tx2 k p = rdrv td tx k p := by
  rw [rdrv_inward_of_black_left td tx2 k p hb2,
    rdrv_inward_of_black_left td tx k p hb0, hnext]

/-- **Derivation of `maskparity · 0` Agreement from White-Center-Conditioned `rdrv` OR-Agreement (`periodic_maskparity_zero_agree_of_rdrv_or_one_agree`, 9.1097)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S, s ∈ ℕ` with `T ≤ t`, if `center t = false → rdrv t (t + m * P) 0 1 = rdrv t t 0 1` at `s = 0` and for all `u < S`, `center (t + (u + 1)) = false → (rdrv t (t + m * P) u 1 || rdrv t (t + m * P) u 2) = (rdrv t t u 1 || rdrv t t u 2)`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for all `s ≤ S`! -/
theorem periodic_maskparity_zero_agree_of_rdrv_or_one_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t)
    (h0 : Rule30UOR.Core.center t = false →
      rdrv t (t + m * P) 0 1 = rdrv t t 0 1)
    (hor : ∀ u : Nat, u < S →
      Rule30UOR.Core.center (t + (u + 1)) = false →
        (rdrv t (t + m * P) u 1 || rdrv t (t + m * P) u 2) =
          (rdrv t t u 1 || rdrv t t u 2))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun hc => ?_)
  rcases s with _ | u
  · rw [Nat.add_zero] at hc
    exact h0 hc
  · exact rdrv_step_one_eq_of_or_eq t (t + m * P) t u (hor u (by omega) hc)

/-- **Multi-Column (`K`-Step) Inward Propagation of Column-Plus-OR Agreement in `rdrv` (`rdrv_inward_col_or_propagate`, 9.1098)**:
    for all `td, tx2, tx, K, p0, S, s ∈ ℕ`, if column `p0 + K` agrees over `[0, S + K]` and the OR `rdrv · (p0 + K) || rdrv · ((p0 + K) + 1)` agrees over `[0, S + K)`, then marching `K` columns leftward forces `rdrv td tx2 s p0 = rdrv td tx s p0` for all `s ≤ S`! -/
theorem rdrv_inward_col_or_propagate_aux (td tx2 tx K p0 S : Nat)
    (hc : ∀ u : Nat, u ≤ S + K → rdrv td tx2 u (p0 + K) = rdrv td tx u (p0 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv td tx2 u (p0 + K) || rdrv td tx2 u ((p0 + K) + 1)) =
        (rdrv td tx u (p0 + K) || rdrv td tx u ((p0 + K) + 1))) :
    (∀ s : Nat, s ≤ S → rdrv td tx2 s p0 = rdrv td tx s p0) ∧
      (∀ s : Nat, s < S →
        (rdrv td tx2 s p0 || rdrv td tx2 s (p0 + 1)) =
          (rdrv td tx s p0 || rdrv td tx s (p0 + 1))) := by
  induction K generalizing p0 S with
  | zero =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have h := hc s (by omega)
      rwa [Nat.add_zero] at h
    · have h := ho s (by omega)
      rwa [Nat.add_zero] at h
  | succ K ih =>
    have hc' : ∀ u : Nat, u ≤ (S + 1) + K →
        rdrv td tx2 u ((p0 + 1) + K) = rdrv td tx u ((p0 + 1) + K) := by
      intro u hu
      have h := hc u (by omega)
      rwa [show p0 + (K + 1) = (p0 + 1) + K by omega] at h
    have ho' : ∀ u : Nat, u < (S + 1) + K →
        (rdrv td tx2 u ((p0 + 1) + K) || rdrv td tx2 u (((p0 + 1) + K) + 1)) =
          (rdrv td tx u ((p0 + 1) + K) || rdrv td tx u (((p0 + 1) + K) + 1)) := by
      intro u hu
      have h := ho u (by omega)
      rwa [show p0 + (K + 1) = (p0 + 1) + K by omega] at h
    obtain ⟨ihc, iho⟩ := ih (p0 + 1) (S + 1) hc' ho'
    have hc0 : ∀ s : Nat, s ≤ S → rdrv td tx2 s p0 = rdrv td tx s p0 := by
      intro s hs
      have h_or := iho s (by omega)
      rw [show (p0 + 1) + 1 = p0 + 2 by omega] at h_or
      exact rdrv_inward_step_agree td tx2 tx s p0 (ihc (s + 1) (by omega)) h_or
    refine ⟨hc0, fun s hs => ?_⟩
    rw [hc0 s (by omega), ihc s (by omega)]

theorem rdrv_inward_col_or_propagate (td tx2 tx K p0 S s : Nat)
    (hc : ∀ u : Nat, u ≤ S + K → rdrv td tx2 u (p0 + K) = rdrv td tx u (p0 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv td tx2 u (p0 + K) || rdrv td tx2 u ((p0 + K) + 1)) =
        (rdrv td tx u (p0 + K) || rdrv td tx u ((p0 + K) + 1)))
    (hs : s ≤ S) :
    rdrv td tx2 s p0 = rdrv td tx s p0 :=
  (rdrv_inward_col_or_propagate_aux td tx2 tx K p0 S hc ho).1 s hs

/-- **Derivation of `maskparity · 0` Agreement Over `[t, t + S]` from `rdrv` Column-Plus-OR Agreement at Depth `1 + K` (`periodic_maskparity_zero_agree_of_rdrv_col_or_agree`, 9.1099)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, S, s ∈ ℕ` with `T ≤ t`, if column `1 + K` of `rdrv` agrees over `[0, S + K]` and the OR `rdrv · (1 + K) || rdrv · ((1 + K) + 1)` agrees over `[0, S + K)`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for all `s ≤ S`! -/
theorem periodic_maskparity_zero_agree_of_rdrv_col_or_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K S s : Nat) (ht : T ≤ t)
    (hc : ∀ u : Nat, u ≤ S + K →
      rdrv t (t + m * P) u (1 + K) = rdrv t t u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv t (t + m * P) u (1 + K) || rdrv t (t + m * P) u ((1 + K) + 1)) =
        (rdrv t t u (1 + K) || rdrv t t u ((1 + K) + 1)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_inward_col_or_propagate t (t + m * P) t K 1 S s hc ho hs

/-- **Refutation of `CenterPeriodic` from `rdrv` Column-Plus-OR Agreement at Depth `1 + K` After a Zero Diagonal (`not_centerPeriodic_of_rdrv_col_or_agree_at_zero_diag`, 9.1100)**:
    for every `T, P, m, z, p, K, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if column `1 + K` of `rdrv` agrees over `[0, S + K]` and its right-OR agrees over `[0, S + K)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_col_or_agree_at_zero_diag
    (T P m z p K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc : ∀ u : Nat, u ≤ S + K →
      rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) =
        rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) ||
        rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u ((1 + K) + 1)) =
      (rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K) ||
        rdrv (z + (p + 1)) (z + (p + 1)) u ((1 + K) + 1))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two
    T P m z p S hP hm ht hz hd hset1 hsetQ hS (fun s hs _hc => ?_)
  exact rdrv_inward_col_or_propagate
    (z + (p + 1)) ((z + (p + 1)) + m * P) (z + (p + 1)) K 1 S s hc ho hs

theorem not_centerPeriodic_of_rdrv_col_or_agree_at_zero_diag_prop
    (T P m z p K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc : ∀ u : Nat, u ≤ S + K →
      rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) =
        rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u (1 + K) ||
        rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) u ((1 + K) + 1)) =
      (rdrv (z + (p + 1)) (z + (p + 1)) u (1 + K) ||
        rdrv (z + (p + 1)) (z + (p + 1)) u ((1 + K) + 1))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rdrv_col_or_agree_at_zero_diag
    T P m z p K S hP hm ht hz hd hset1 hsetQ hS hc ho

/-- **Dyadic (`2^k - m * P`) Refutation of `CenterPeriodic` from `rdrv` Column-Plus-OR Agreement at Depth `1 + K` (`not_centerPeriodic_of_rdrv_col_or_agree_sub_twopow_ge`, 9.1101)**:
    for every `T, P, m, k, K, S ∈ ℕ` with `0 < P`, `0 < m`, `m * P ≤ twopow k`, `T + m * P ≤ twopow k`, and `twopow k ≤ S + 1`, if column `1 + K` of `rdrv` agrees over `[0, S + K]` and its right-OR agrees over `[0, S + K)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_col_or_agree_sub_twopow_ge
    (T P m k K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hc : ∀ u : Nat, u ≤ S + K →
      rdrv (twopow k - m * P) (twopow k) u (1 + K) =
        rdrv (twopow k - m * P) (twopow k - m * P) u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv (twopow k - m * P) (twopow k) u (1 + K) ||
        rdrv (twopow k - m * P) (twopow k) u ((1 + K) + 1)) =
      (rdrv (twopow k - m * P) (twopow k - m * P) u (1 + K) ||
        rdrv (twopow k - m * P) (twopow k - m * P) u ((1 + K) + 1))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_rdrv_one_agree_sub_twopow_ge
    T P m k S hP hm hmP ht hS (fun s hs _hc => ?_)
  exact rdrv_inward_col_or_propagate
    (twopow k - m * P) (twopow k) (twopow k - m * P) K 1 S s hc ho hs

theorem not_centerPeriodic_of_rdrv_col_or_agree_sub_twopow_ge_prop
    (T P m k K S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hc : ∀ u : Nat, u ≤ S + K →
      rdrv (twopow k - m * P) (twopow k) u (1 + K) =
        rdrv (twopow k - m * P) (twopow k - m * P) u (1 + K))
    (ho : ∀ u : Nat, u < S + K →
      (rdrv (twopow k - m * P) (twopow k) u (1 + K) ||
        rdrv (twopow k - m * P) (twopow k) u ((1 + K) + 1)) =
      (rdrv (twopow k - m * P) (twopow k - m * P) u (1 + K) ||
        rdrv (twopow k - m * P) (twopow k - m * P) u ((1 + K) + 1))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rdrv_col_or_agree_sub_twopow_ge
    T P m k K S hP hm hmP ht hS hc ho

/-! ### Batch 54: The Pure-Drive All-White-Seed Right Half `rdrv td 0 k p` (`kit [33]`), White-Run Pinning of Column `1`, White-Slice Agreement with the Pure-Drive Evolution, and Pure-Drive Synchronized Refutations (9.1102–9.1116) -/

/-- **All-White Initial Slice of the Pure-Drive Right Half `rdrv td 0 0 p` (`rdrv_white_seed_init_eq_false`, 9.1102, `kit [33]`)**:
    for all `td, p ∈ ℕ` with `0 < p`, `rdrv td 0 0 p = false` — at `tx = 0`, the driven right half starts from the all-white initial state (`q ↦ false` for all `q ≥ 1`) and is driven purely by `s ↦ center (td + s)`! -/
theorem rdrv_white_seed_init_eq_false (td p : Nat) (hp : 0 < p) :
    rdrv td 0 0 p = false := by
  rw [rdrv_init td 0 p hp, rhCenter_gt_eq_false 0 p hp]

/-- **Vanishing of the Pure-Drive Right Half `rdrv td 0 k p` Outside the Drive Cone `k < p` (`rdrv_white_seed_gt_eq_false`, 9.1103)**:
    for all `td, k, p ∈ ℕ` with `k < p`, `rdrv td 0 k p = false`! -/
theorem rdrv_white_seed_gt_eq_false (td k p : Nat) (hkp : k < p) :
    rdrv td 0 k p = false := by
  have hgt : 0 + k < p := by omega
  exact rdrv_gt_eq_false td 0 k p hgt

/-- **Exact Drive-Cone Edge Readout of the Pure-Drive Right Half `rdrv td 0 k k` (`rdrv_white_seed_diag_eq_center`, 9.1104)**:
    for all `td, k ∈ ℕ`, `rdrv td 0 k k = center td` — along the drive-cone edge `p = k`, the initial center bit `center td` propagates down-right without alteration for all `k`! -/
theorem rdrv_white_seed_diag_eq_center (td k : Nat) :
    rdrv td 0 k k = Rule30UOR.Core.center td := by
  induction k with
  | zero =>
    rw [rdrv_col0, Nat.add_zero]
  | succ k ih =>
    rw [rdrv_step_succ td 0 k k, ih,
      rdrv_white_seed_gt_eq_false td k (k + 1) (by omega),
      rdrv_white_seed_gt_eq_false td k (k + 2) (by omega),
      Bool.false_or]
    cases Rule30UOR.Core.center td <;> rfl

/-- **Exact `m * P`-Periodicity of the Pure-Drive Right Half `rdrv td 0 k p` Under `CenterPeriodic` (`periodic_rdrv_white_seed_shift_eq`, 9.1105, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, td, k, p ∈ ℕ` with `T ≤ td`, `rdrv (td + m * P) 0 k p = rdrv td 0 k p` holds unconditionally for ALL `k, p ∈ ℕ`! -/
theorem periodic_rdrv_white_seed_shift_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m td k p : Nat) (htd : T ≤ td) :
    rdrv (td + m * P) 0 k p = rdrv td 0 k p :=
  periodic_rdrv_drive_shift_eq T P hP hper m td 0 k p htd

/-- **Reduction of `rdrv td tx k p` to the Pure-Drive Right Half `rdrv td 0 k p` Over an Initial White Band (`rdrv_eq_white_seed_of_initial_white_band`, 9.1106, `kit [33]`)**:
    for all `td, tx, L, k, p ∈ ℕ`, if `∀ i ≤ L, rhCenter tx (1 + i) = false` (columns `1, …, L + 1` of row `tx` are white) and `p + k ≤ L + 1`, then `rdrv td tx k p = rdrv td 0 k p` (completely independent of `tx`!)! -/
theorem rdrv_eq_white_seed_of_initial_white_band (td tx L k p : Nat)
    (hw : ∀ i : Nat, i ≤ L → rhCenter tx (1 + i) = false)
    (hpk : p + k ≤ L + 1) :
    rdrv td tx k p = rdrv td 0 k p := by
  have hband : RhBandAgree 0 tx 1 L := by
    intro i hi
    rw [Nat.zero_add, hw i hi, rhCenter_gt_eq_false 0 (1 + i) (by omega)]
  have h := rdrv_init_causal_cone td 0 tx L k p hband hpk
  rwa [Nat.zero_add] at h

/-- **Column-`1` Agreement with the Pure-Drive Right Half `rdrv td 0 s 1` Over an Initial White Band (`rdrv_col_one_eq_white_seed_of_initial_white_band`, 9.1107)**:
    for all `td, tx, S, s ∈ ℕ`, if `∀ i ≤ S, rhCenter tx (1 + i) = false` and `s ≤ S`, then `rdrv td tx s 1 = rdrv td 0 s 1`! -/
theorem rdrv_col_one_eq_white_seed_of_initial_white_band (td tx S s : Nat)
    (hw : ∀ i : Nat, i ≤ S → rhCenter tx (1 + i) = false) (hs : s ≤ S) :
    rdrv td tx s 1 = rdrv td 0 s 1 :=
  rdrv_eq_white_seed_of_initial_white_band td tx S s 1 hw (by omega)

/-- **1-Step Black Persistence of Column `1` in `rdrv` at a White Drive Bit (`rdrv_step_one_eq_true_of_white_center_and_black_one`, 9.1108)**:
    for all `td, tx, k ∈ ℕ`, if `center (td + k) = false` and `rdrv td tx k 1 = true`, then `rdrv td tx (k + 1) 1 = true` unconditionally (with zero dependence on column `2`)! -/
theorem rdrv_step_one_eq_true_of_white_center_and_black_one (td tx k : Nat)
    (hc : Rule30UOR.Core.center (td + k) = false)
    (hb : rdrv td tx k 1 = true) :
    rdrv td tx (k + 1) 1 = true := by
  rw [rdrv_step_one_eq_not_center_of_black_one td tx k hb, hc]
  rfl

/-- **Multi-Step Black Persistence of Column `1` in `rdrv` Across a White Center Run (`rdrv_white_center_run_black_one_persist`, 9.1109, `kit [33]`)**:
    for all `td, tx, k, W, j ∈ ℕ`, if `rdrv td tx k 1 = true` and `∀ u < W, center (td + (k + u)) = false`, then for all `j ≤ W`, `rdrv td tx (k + j) 1 = true` (remaining locked at `true` throughout the entire white center run regardless of `tx` or columns `≥ 2`!)! -/
theorem rdrv_white_center_run_black_one_persist (td tx k W j : Nat)
    (hb : rdrv td tx k 1 = true)
    (hrun : ∀ u : Nat, u < W → Rule30UOR.Core.center (td + (k + u)) = false)
    (hj : j ≤ W) :
    rdrv td tx (k + j) 1 = true := by
  induction j with
  | zero =>
    rwa [Nat.add_zero]
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 by omega]
    exact rdrv_step_one_eq_true_of_white_center_and_black_one td tx (k + j)
      (hrun j (by omega)) (ih (by omega))

/-- **Multi-Step Column-`1` Agreement in `rdrv` Across a White Center Run Plus One Step (`rdrv_white_center_run_black_one_agree`, 9.1110)**:
    for all `td, tx2, tx, k, W, j ∈ ℕ`, if `rdrv td tx2 k 1 = true`, `rdrv td tx k 1 = true`, and `∀ u < W, center (td + (k + u)) = false`, then for all `j ≤ W + 1`, `rdrv td tx2 (k + j) 1 = rdrv td tx (k + j) 1`! -/
theorem rdrv_white_center_run_black_one_agree (td tx2 tx k W j : Nat)
    (hb2 : rdrv td tx2 k 1 = true) (hb0 : rdrv td tx k 1 = true)
    (hrun : ∀ u : Nat, u < W → Rule30UOR.Core.center (td + (k + u)) = false)
    (hj : j ≤ W + 1) :
    rdrv td tx2 (k + j) 1 = rdrv td tx (k + j) 1 := by
  by_cases hjW : j ≤ W
  · rw [rdrv_white_center_run_black_one_persist td tx2 k W j hb2 hrun hjW,
      rdrv_white_center_run_black_one_persist td tx k W j hb0 hrun hjW]
  · have hj_eq : j = W + 1 := by omega
    rw [hj_eq, show k + (W + 1) = (k + W) + 1 by omega]
    exact rdrv_step_one_eq_of_black_one td tx2 tx (k + W)
      (rdrv_white_center_run_black_one_persist td tx2 k W W hb2 hrun (by omega))
      (rdrv_white_center_run_black_one_persist td tx k W W hb0 hrun (by omega))

/-- **1-Step Black Pinning `rdrv t t 1 1 = true` from `maskparity t 0 = true` (`rdrv_step_one_eq_true_of_maskparity_zero_true`, 9.1111)**:
    for all `t ∈ ℕ`, if `maskparity t 0 = true`, then `rdrv t t 1 1 = true`! -/
theorem rdrv_step_one_eq_true_of_maskparity_zero_true (t : Nat)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true) :
    rdrv t t 1 1 = true := by
  rw [rdrv_diag_eq_rhCenter t 1 1]
  exact rhCenter_step_one_eq_true_of_maskparity_zero_true t hm0

/-- **1-Step Black Pinning `rdrv t (t + m * P) 1 1 = true` from `maskparity (t + m * P) 0 = true` Under `CenterPeriodic` (`periodic_rdrv_step_one_eq_true_of_maskparity_zero_true`, 9.1112)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t ∈ ℕ` with `T ≤ t`, if `maskparity (t + m * P) 0 = true`, then `rdrv t (t + m * P) 1 1 = true`! -/
theorem periodic_rdrv_step_one_eq_true_of_maskparity_zero_true
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hmQ : Rule30UOR.Scale.maskparity (t + m * P) 0 = true) :
    rdrv t (t + m * P) 1 1 = true := by
  rw [← periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t 1 1 ht]
  exact rhCenter_step_one_eq_true_of_maskparity_zero_true (t + m * P) hmQ

/-- **Multi-Step Propagation of `maskparity · 0` Agreement Across a White Center Run from a Single `maskparity · 0 = true` Match (`periodic_maskparity_zero_agree_on_white_run_of_maskparity_zero_true`, 9.1113)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, W, s ∈ ℕ` with `T ≤ t`, if `maskparity (t + m * P) 0 = true` and `maskparity t 0 = true` at time `t`, and `∀ u < W, center (t + (1 + u)) = false`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` holds for ALL `s ≤ W + 2` (with zero hypotheses on columns `≥ 2`!)! -/
theorem periodic_maskparity_zero_agree_on_white_run_of_maskparity_zero_true
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t W s : Nat) (ht : T ≤ t)
    (hmQ : Rule30UOR.Scale.maskparity (t + m * P) 0 = true)
    (hm0 : Rule30UOR.Scale.maskparity t 0 = true)
    (hrun : ∀ u : Nat, u < W → Rule30UOR.Core.center (t + (1 + u)) = false)
    (hs : s ≤ W + 2) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  rcases s with _ | j
  · simp only [Nat.add_zero]
    rw [hmQ, hm0]
  · refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t (j + 1) ht (fun _ => ?_)
    rw [show j + 1 = 1 + j by omega]
    exact rdrv_white_center_run_black_one_agree t (t + m * P) t 1 W j
      (periodic_rdrv_step_one_eq_true_of_maskparity_zero_true T P hP hper m t ht hmQ)
      (rdrv_step_one_eq_true_of_maskparity_zero_true t hm0)
      hrun (by omega)

/-- **Two-Column Agreement of `rdrv` with the Pure-Drive Right Half `rdrv td 0 k ·` Inside the Right-Threshold White Zero-Gap (`rdrv_two_col_eq_white_seed_of_zero_gap`, 9.1114)**:
    for `IsRightThreshold e J`, `1 ≤ j`, `j + 1 ≤ J`, and `k + (j + 1) < u * twopow e`, both adjacent columns `u * twopow e - (j + 1)` and `u * twopow e - j` of `rdrv td (u * twopow e - k) k ·` equal the pure-drive all-white-seed evolution `rdrv td 0 k ·`! -/
theorem rdrv_two_col_eq_white_seed_of_zero_gap (td e J u k j : Nat)
    (hJ : IsRightThreshold e J) (hj1 : 1 ≤ j) (hjJ : j + 1 ≤ J)
    (hkju : k + (j + 1) < u * twopow e) :
    rdrv td (u * twopow e - k) k (u * twopow e - (j + 1)) =
      rdrv td 0 k (u * twopow e - (j + 1)) ∧
    rdrv td (u * twopow e - k) k (u * twopow e - j) =
      rdrv td 0 k (u * twopow e - j) := by
  refine ⟨?_, ?_⟩
  · rw [rdrv_zero_gap_of_threshold td e J u k (j + 1) hJ (by omega) hjJ hkju,
      rdrv_white_seed_gt_eq_false td k (u * twopow e - (j + 1)) (by omega)]
  · rw [rdrv_zero_gap_of_threshold td e J u k j hJ hj1 (by omega) (by omega),
      rdrv_white_seed_gt_eq_false td k (u * twopow e - j) (by omega)]

/-- **Derivation of `maskparity · 0` Agreement When Both `t + m * P` and `t` Agree with the Pure-Drive Evolution `rdrv t 0 s 1` (`periodic_maskparity_zero_agree_of_both_eq_white_seed`, 9.1115)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t`, if at white centers `center (t + s) = false`, both `rdrv t (t + m * P) s 1 = rdrv t 0 s 1` and `rdrv t t s 1 = rdrv t 0 s 1` agree with the pure-drive right half `rdrv t 0 s 1`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_both_eq_white_seed
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hw : Rule30UOR.Core.center (t + s) = false →
      rdrv t (t + m * P) s 1 = rdrv t 0 s 1 ∧ rdrv t t s 1 = rdrv t 0 s 1) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun hc => ?_)
  obtain ⟨h1, h2⟩ := hw hc
  rw [h1, h2]

/-- **Refutation of `CenterPeriodic` When Both `t + m * P` and `t` Agree with the Pure-Drive Evolution `rdrv · 0 s 1` Over `p + 3 * (m * P)` Steps After a Zero Diagonal (`not_centerPeriodic_of_both_eq_white_seed_at_zero_diag`, 9.1116)**:
    for every `T, P, m, z, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `p + 3 * (m * P) ≤ S + 1`, if at every white center `center ((z + (p + 1)) + s) = false` (`s ≤ S`), both `rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 = rdrv (z + (p + 1)) 0 s 1` and `rdrv (z + (p + 1)) (z + (p + 1)) s 1 = rdrv (z + (p + 1)) 0 s 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_both_eq_white_seed_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hsetQ : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 = rdrv (z + (p + 1)) 0 s 1 ∧
        rdrv (z + (p + 1)) (z + (p + 1)) s 1 = rdrv (z + (p + 1)) 0 s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_rdrv_one_agree_at_zero_diag_step_two
    T P m z p S hP hm ht hz hd hset1 hsetQ hS (fun s hs hc => ?_)
  obtain ⟨h1, h2⟩ := hw s hs hc
  rw [h1, h2]

theorem not_centerPeriodic_of_both_eq_white_seed_at_zero_diag_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hsetQ : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hw : ∀ s : Nat, s ≤ S →
      Rule30UOR.Core.center ((z + (p + 1)) + s) = false →
        rdrv (z + (p + 1)) ((z + (p + 1)) + m * P) s 1 = rdrv (z + (p + 1)) 0 s 1 ∧
        rdrv (z + (p + 1)) (z + (p + 1)) s 1 = rdrv (z + (p + 1)) 0 s 1) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_both_eq_white_seed_at_zero_diag
    T P m z p S hP hm ht hz hd hset1 hsetQ hS hw

/-! ### Batch 55: Universal `2^d`-Diagonal Periodicity & Scale Laws of Pure-Drive `rdrv` (`kit [33]`, 9.1117–9.1131) -/

/-- **First Sub-Diagonal Step Identity of the Pure-Drive Right Half (`rdrv_white_seed_subdiag_one_step`, 9.1117, `kit [33]`)**:
    for all `td, k ∈ ℕ`, `rdrv td 0 (k + 2) (k + 1) = bxor (rdrv td 0 (k + 1) k) (center td)`! -/
theorem rdrv_white_seed_subdiag_one_step (td k : Nat) :
    rdrv td 0 (k + 2) (k + 1) = bxor (rdrv td 0 (k + 1) k) (Rule30UOR.Core.center td) := by
  have hstep := rdrv_step_succ td 0 (k + 1) k
  have h1 : (k + 1) + 1 = k + 2 := by omega
  rw [h1] at hstep
  rw [hstep, rdrv_white_seed_diag_eq_center td (k + 1),
      rdrv_white_seed_gt_eq_false td (k + 1) (k + 2) (by omega), Bool.or_false]

/-- **Period-`2` Invariance of the First Sub-Diagonal of the Pure-Drive Right Half (`rdrv_white_seed_subdiag_one_period_two`, 9.1118)**:
    for all `td, k ∈ ℕ`, `rdrv td 0 (k + 3) (k + 2) = rdrv td 0 (k + 1) k`! -/
theorem rdrv_white_seed_subdiag_one_period_two (td k : Nat) :
    rdrv td 0 (k + 3) (k + 2) = rdrv td 0 (k + 1) k := by
  have h1 : k + 3 = (k + 1) + 2 := by omega
  have h2 : k + 2 = (k + 1) + 1 := by omega
  rw [h1, h2, rdrv_white_seed_subdiag_one_step td (k + 1),
      rdrv_white_seed_subdiag_one_step td k]
  cases rdrv td 0 (k + 1) k <;> cases Rule30UOR.Core.center td <;> rfl

/-- **Closed Form of the First Sub-Diagonal of the Pure-Drive Right Half at Even Indices (`rdrv_white_seed_subdiag_one_even`, 9.1119)**:
    for all `td, u ∈ ℕ`, `rdrv td 0 (2 * u + 1) (2 * u) = center (td + 1)`! -/
theorem rdrv_white_seed_subdiag_one_even (td u : Nat) :
    rdrv td 0 (2 * u + 1) (2 * u) = Rule30UOR.Core.center (td + 1) := by
  induction u with
  | zero =>
    have h1 : 2 * 0 + 1 = 1 := by omega
    have h2 : 2 * 0 = 0 := by omega
    rw [h1, h2, rdrv_col0]
  | succ u ih =>
    have h1 : 2 * (u + 1) + 1 = (2 * u) + 3 := by omega
    have h2 : 2 * (u + 1) = (2 * u) + 2 := by omega
    rw [h1, h2, rdrv_white_seed_subdiag_one_period_two td (2 * u), ih]

/-- **Closed Form of the First Sub-Diagonal of the Pure-Drive Right Half at Odd Indices (`rdrv_white_seed_subdiag_one_odd`, 9.1120)**:
    for all `td, u ∈ ℕ`, `rdrv td 0 (2 * u + 2) (2 * u + 1) = bxor (center (td + 1)) (center td)`! -/
theorem rdrv_white_seed_subdiag_one_odd (td u : Nat) :
    rdrv td 0 (2 * u + 2) (2 * u + 1) =
    bxor (Rule30UOR.Core.center (td + 1)) (Rule30UOR.Core.center td) := by
  rw [rdrv_white_seed_subdiag_one_step td (2 * u), rdrv_white_seed_subdiag_one_even td u]

theorem bxor_step_shift_defect_const (f g : Nat → Bool) (Q : Nat)
    (hstep : ∀ k, f (k + 1) = bxor (f k) (g k))
    (hper : ∀ k, g (k + Q) = g k) :
    ∀ k, bxor (f (k + Q)) (f k) = bxor (f Q) (f 0) := by
  intro k
  induction k with
  | zero =>
    have h0 : 0 + Q = Q := by omega
    rw [h0]
  | succ k ih =>
    have h1 : k + 1 + Q = (k + Q) + 1 := by omega
    rw [h1, hstep (k + Q), hstep k, hper k]
    have h2 : bxor (bxor (f (k + Q)) (g k)) (bxor (f k) (g k)) = bxor (f (k + Q)) (f k) := by
      cases f (k + Q) <;> cases f k <;> cases g k <;> rfl
    rw [h2, ih]

theorem bxor_step_period_double (f g : Nat → Bool) (Q : Nat)
    (hstep : ∀ k, f (k + 1) = bxor (f k) (g k))
    (hper : ∀ k, g (k + Q) = g k) (k : Nat) :
    f (k + (Q + Q)) = f k := by
  have hd1 := bxor_step_shift_defect_const f g Q hstep hper k
  have hd2 := bxor_step_shift_defect_const f g Q hstep hper (k + Q)
  have h1 : k + (Q + Q) = (k + Q) + Q := by omega
  rw [h1]
  have h2 : bxor (f ((k + Q) + Q)) (f (k + Q)) = bxor (f (k + Q)) (f k) := by
    rw [hd2, hd1]
  revert h2
  cases f ((k + Q) + Q) <;> cases f (k + Q) <;> cases f k <;> decide

theorem rdrv_white_seed_subdiag_period_twopow_le (td d : Nat) :
    ∀ d', d' ≤ d → ∀ k u,
      rdrv td 0 ((k + d') + u * twopow d') (k + u * twopow d') = rdrv td 0 (k + d') k := by
  induction d with
  | zero =>
    intro d' hd' k u
    have hd0 : d' = 0 := by omega
    subst hd0
    have h1 : (k + 0) + u * twopow 0 = k + u * twopow 0 := by omega
    have h2 : k + 0 = k := by omega
    rw [h1, h2, rdrv_white_seed_diag_eq_center td (k + u * twopow 0),
        rdrv_white_seed_diag_eq_center td k]
  | succ d ih =>
    intro d' hd' k u
    by_cases hlt : d' ≤ d
    · exact ih d' hlt k u
    · have hd1 : d' = d + 1 := by omega
      subst hd1
      have hstep1 : ∀ j,
          rdrv td 0 ((j + (d + 1)) + twopow (d + 1)) (j + twopow (d + 1)) =
          rdrv td 0 (j + (d + 1)) j := by
        intro j
        let f : Nat → Bool := fun x => rdrv td 0 (x + (d + 1)) x
        let g : Nat → Bool := fun x =>
          rdrv td 0 (x + d + 1) (x + 1) || rdrv td 0 (x + d + 1) (x + 2)
        have hfstep : ∀ x, f (x + 1) = bxor (f x) (g x) := by
          intro x
          dsimp [f, g]
          have hx1 : (x + 1) + (d + 1) = (x + d + 1) + 1 := by omega
          have hx2 : x + (d + 1) = x + d + 1 := by omega
          rw [hx1, hx2]
          exact rdrv_step_succ td 0 (x + d + 1) x
        have hgper : ∀ x, g (x + twopow d) = g x := by
          intro x
          dsimp [g]
          have hg1 : rdrv td 0 ((x + twopow d) + d + 1) ((x + twopow d) + 1) =
              rdrv td 0 (x + d + 1) (x + 1) := by
            have ha1 : (x + twopow d) + d + 1 = ((x + 1) + d) + 1 * twopow d := by omega
            have ha2 : (x + twopow d) + 1 = (x + 1) + 1 * twopow d := by omega
            have ha3 : (x + 1) + d = x + d + 1 := by omega
            rw [ha1, ha2, ih d (by omega) (x + 1) 1, ha3]
          have hg2 : rdrv td 0 ((x + twopow d) + d + 1) ((x + twopow d) + 2) =
              rdrv td 0 (x + d + 1) (x + 2) := by
            cases d with
            | zero =>
              rw [rdrv_white_seed_gt_eq_false td ((x + twopow 0) + 0 + 1) ((x + twopow 0) + 2) (by omega),
                  rdrv_white_seed_gt_eq_false td (x + 0 + 1) (x + 2) (by omega)]
            | succ d0 =>
              have htp : twopow (d0 + 1) = 2 * twopow d0 := by
                rw [twopow_succ]
                omega
              have hb1 : (x + twopow (d0 + 1)) + (d0 + 1) + 1 = ((x + 2) + d0) + 2 * twopow d0 := by omega
              have hb2 : (x + twopow (d0 + 1)) + 2 = (x + 2) + 2 * twopow d0 := by omega
              have hb3 : (x + 2) + d0 = x + (d0 + 1) + 1 := by omega
              rw [hb1, hb2, ih d0 (by omega) (x + 2) 2, hb3]
          rw [hg1, hg2]
        have hpd := bxor_step_period_double f g (twopow d) hfstep hgper j
        dsimp [f] at hpd
        have htp2 : twopow (d + 1) = twopow d + twopow d := twopow_succ d
        have hj1 : (j + (d + 1)) + twopow (d + 1) = (j + (twopow d + twopow d)) + (d + 1) := by omega
        have hj2 : j + twopow (d + 1) = j + (twopow d + twopow d) := by omega
        rw [hj1, hj2, hpd]
      induction u with
      | zero =>
        have hu1 : (k + (d + 1)) + 0 * twopow (d + 1) = k + (d + 1) := by omega
        have hu2 : k + 0 * twopow (d + 1) = k := by omega
        rw [hu1, hu2]
      | succ u ihu =>
        have hu0 : (u + 1) * twopow (d + 1) = u * twopow (d + 1) + twopow (d + 1) := by
          rw [Nat.succ_mul]
        have hu1 : (k + (d + 1)) + (u + 1) * twopow (d + 1) =
            ((k + u * twopow (d + 1)) + (d + 1)) + twopow (d + 1) := by omega
        have hu2 : k + (u + 1) * twopow (d + 1) =
            (k + u * twopow (d + 1)) + twopow (d + 1) := by omega
        have hu3 : (k + u * twopow (d + 1)) + (d + 1) =
            (k + (d + 1)) + u * twopow (d + 1) := by omega
        rw [hu1, hu2, hstep1 (k + u * twopow (d + 1)), hu3, ihu]

/-- **Universal `2^d`-Diagonal Periodicity of the Pure-Drive Right Half (`rdrv_white_seed_subdiag_period_twopow`, 9.1121, `kit [33]`)**:
    for all `td, d, k, u ∈ ℕ` (with NO periodicity hypothesis on the drive!), `rdrv td 0 ((k + d) + u * 2^d) (k + u * 2^d) = rdrv td 0 (k + d) k`! -/
theorem rdrv_white_seed_subdiag_period_twopow (td d k u : Nat) :
    rdrv td 0 ((k + d) + u * twopow d) (k + u * twopow d) = rdrv td 0 (k + d) k :=
  rdrv_white_seed_subdiag_period_twopow_le td d d (by omega) k u

/-- **Uniform `2^d`-Diagonal Periodicity Across the First `d + 1` Sub-Diagonals of `rdrv td 0` (`rdrv_white_seed_diag_shift_twopow_eq`, 9.1122)**:
    for all `td, d, k, p, u ∈ ℕ` with `p ≤ k` and `k - p ≤ d`, `rdrv td 0 (k + u * 2^d) (p + u * 2^d) = rdrv td 0 k p`! -/
theorem rdrv_white_seed_diag_shift_twopow_eq (td d k p u : Nat)
    (hpk : p ≤ k) (hkd : k - p ≤ d) :
    rdrv td 0 (k + u * twopow d) (p + u * twopow d) = rdrv td 0 k p := by
  have htp : twopow d = twopow (d - (k - p)) * twopow (k - p) := by
    rw [twopow_eq_pow, twopow_eq_pow, twopow_eq_pow, ← Nat.pow_add]
    have heq : (d - (k - p)) + (k - p) = d := by omega
    rw [heq]
  have h1 : k + u * twopow d =
      (p + (k - p)) + (u * twopow (d - (k - p))) * twopow (k - p) := by
    rw [htp, ← Nat.mul_assoc]
    omega
  have h2 : p + u * twopow d =
      p + (u * twopow (d - (k - p))) * twopow (k - p) := by
    rw [htp, ← Nat.mul_assoc]
  have h3 : p + (k - p) = k := by omega
  rw [h1, h2, rdrv_white_seed_subdiag_period_twopow td (k - p) p (u * twopow (d - (k - p))), h3]

/-- **Universal Dyadic-Multiple Scale Identity of the Pure-Drive Right Half (`rdrv_white_seed_scale_mult_eq_center`, 9.1123, `kit [33]`)**:
    for all `td, d, u ∈ ℕ`, `rdrv td 0 (d + u * 2^d) (u * 2^d) = center (td + d)`! -/
theorem rdrv_white_seed_scale_mult_eq_center (td d u : Nat) :
    rdrv td 0 (d + u * twopow d) (u * twopow d) = Rule30UOR.Core.center (td + d) := by
  have h := rdrv_white_seed_subdiag_period_twopow td d 0 u
  have h1 : (0 + d) + u * twopow d = d + u * twopow d := by omega
  have h2 : 0 + u * twopow d = u * twopow d := by omega
  have h3 : 0 + d = d := by omega
  rw [h1, h2, h3] at h
  rw [h, rdrv_col0]

/-- **Universal Dyadic Scale Identity of the Pure-Drive Right Half (`rdrv_white_seed_scale_eq_center`, 9.1124, `kit [33]`)**:
    for all `td, d ∈ ℕ`, `rdrv td 0 (d + 2^d) (2^d) = center (td + d)` — the pure-drive right-half analogue of `lhCenter_add_twopow_eq_center` (`9.941`), valid for EVERY drive start time `td`! -/
theorem rdrv_white_seed_scale_eq_center (td d : Nat) :
    rdrv td 0 (d + twopow d) (twopow d) = Rule30UOR.Core.center (td + d) := by
  have h := rdrv_white_seed_scale_mult_eq_center td d 1
  have h1 : 1 * twopow d = twopow d := by omega
  rw [h1] at h
  exact h

/-- **Universal High-Scale Identity of the Pure-Drive Right Half (`rdrv_white_seed_scale_ge_eq_center`, 9.1125)**:
    for all `td, d, k ∈ ℕ` with `d ≤ k`, `rdrv td 0 (d + 2^k) (2^k) = center (td + d)`! -/
theorem rdrv_white_seed_scale_ge_eq_center (td d k : Nat) (hdk : d ≤ k) :
    rdrv td 0 (d + twopow k) (twopow k) = Rule30UOR.Core.center (td + d) := by
  have htp : twopow k = twopow (k - d) * twopow d := by
    rw [twopow_eq_pow, twopow_eq_pow, twopow_eq_pow, ← Nat.pow_add]
    have heq : (k - d) + d = k := by omega
    rw [heq]
  rw [htp]
  exact rdrv_white_seed_scale_mult_eq_center td d (twopow (k - d))

/-- **Scale-Doubling Stabilization Law of the Pure-Drive Right Half (`rdrv_white_seed_scale_double_eq_scale`, 9.1126)**:
    for all `td, d, k ∈ ℕ` with `d ≤ k`, `rdrv td 0 (d + 2^(k+1)) (2^(k+1)) = rdrv td 0 (d + 2^k) (2^k)` — the pure-drive right-half analogue of `9.994`! -/
theorem rdrv_white_seed_scale_double_eq_scale (td d k : Nat) (hdk : d ≤ k) :
    rdrv td 0 (d + twopow (k + 1)) (twopow (k + 1)) =
    rdrv td 0 (d + twopow k) (twopow k) := by
  rw [rdrv_white_seed_scale_ge_eq_center td d (k + 1) (by omega),
      rdrv_white_seed_scale_ge_eq_center td d k hdk]

/-- **Dyadic Scale Readout of `rdrv td tx` Inside an Initial Right-Half White Band (`rdrv_scale_eq_center_of_initial_white_band`, 9.1127)**:
    for all `td, tx, L, d, k ∈ ℕ`, if `∀ i ≤ L, rhCenter tx (1 + i) = false`, `d ≤ k`, and `d + 2 * 2^k ≤ L + 1`, then `rdrv td tx (d + 2^k) (2^k) = center (td + d)`! -/
theorem rdrv_scale_eq_center_of_initial_white_band (td tx L d k : Nat)
    (hw : ∀ i : Nat, i ≤ L → rhCenter tx (1 + i) = false)
    (hdk : d ≤ k) (hL : d + 2 * twopow k ≤ L + 1) :
    rdrv td tx (d + twopow k) (twopow k) = Rule30UOR.Core.center (td + d) := by
  have heq := rdrv_eq_white_seed_of_initial_white_band td tx L (d + twopow k) (twopow k) hw (by omega)
  rw [heq, rdrv_white_seed_scale_ge_eq_center td d k hdk]

/-- **Right-Half Dyadic Scale Identity Inside an Initial White Band (`rhCenter_scale_eq_center_of_initial_white_band`, 9.1128)**:
    for all `t, L, d, k ∈ ℕ`, if `∀ i ≤ L, rhCenter t (1 + i) = false`, `d ≤ k`, and `d + 2 * 2^k ≤ L + 1`, then `rhCenter (t + (d + 2^k)) (2^k) = center (t + d)`! -/
theorem rhCenter_scale_eq_center_of_initial_white_band (t L d k : Nat)
    (hw : ∀ i : Nat, i ≤ L → rhCenter t (1 + i) = false)
    (hdk : d ≤ k) (hL : d + 2 * twopow k ≤ L + 1) :
    rhCenter (t + (d + twopow k)) (twopow k) = Rule30UOR.Core.center (t + d) := by
  rw [← rdrv_diag_eq_rhCenter t (d + twopow k) (twopow k)]
  exact rdrv_scale_eq_center_of_initial_white_band t t L d k hw hdk hL

/-- **Transfer of `2^d`-Diagonal Periodicity to `rdrv td tx` Inside an Initial White Band (`rdrv_subdiag_period_twopow_of_initial_white_band`, 9.1129)**:
    for all `td, tx, L, d, k, u ∈ ℕ`, if `∀ i ≤ L, rhCenter tx (1 + i) = false` and `(k + u * 2^d) + ((k + d) + u * 2^d) ≤ L + 1`, then `rdrv td tx ((k + d) + u * 2^d) (k + u * 2^d) = rdrv td tx (k + d) k`! -/
theorem rdrv_subdiag_period_twopow_of_initial_white_band (td tx L d k u : Nat)
    (hw : ∀ i : Nat, i ≤ L → rhCenter tx (1 + i) = false)
    (hL : (k + u * twopow d) + ((k + d) + u * twopow d) ≤ L + 1) :
    rdrv td tx ((k + d) + u * twopow d) (k + u * twopow d) =
    rdrv td tx (k + d) k := by
  have heq1 := rdrv_eq_white_seed_of_initial_white_band td tx L
    ((k + d) + u * twopow d) (k + u * twopow d) hw hL
  have heq2 := rdrv_eq_white_seed_of_initial_white_band td tx L
    (k + d) k hw (by omega)
  rw [heq1, heq2, rdrv_white_seed_subdiag_period_twopow td d k u]

/-- **Triangle-Cone Agreement of Two Same-Drive Right Halves Over Shared Initial White Bands (`rdrv_eq_of_both_initial_white_band`, 9.1130)**:
    for all `td, tx2, tx, L, k, p ∈ ℕ`, if both `rhCenter tx2` and `rhCenter tx` are white on columns `1, …, L + 1` and `p + k ≤ L + 1`, then `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_eq_of_both_initial_white_band (td tx2 tx L k p : Nat)
    (hw2 : ∀ i : Nat, i ≤ L → rhCenter tx2 (1 + i) = false)
    (hw1 : ∀ i : Nat, i ≤ L → rhCenter tx (1 + i) = false)
    (hpk : p + k ≤ L + 1) :
    rdrv td tx2 k p = rdrv td tx k p := by
  rw [rdrv_eq_white_seed_of_initial_white_band td tx2 L k p hw2 hpk,
      rdrv_eq_white_seed_of_initial_white_band td tx L k p hw1 hpk]

/-- **Periodic Right-Half Triangle Agreement Over Shared Initial White Bands (`periodic_rhCenter_shift_eq_of_both_initial_white_band`, 9.1131)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, L, k, p ∈ ℕ` with `T ≤ t`, if both `rhCenter (t + m * P)` and `rhCenter t` are white on columns `1, …, L + 1` and `p + k ≤ L + 1`, then `rhCenter ((t + m * P) + k) p = rhCenter (t + k) p`! -/
theorem periodic_rhCenter_shift_eq_of_both_initial_white_band
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L k p : Nat) (ht : T ≤ t)
    (hw2 : ∀ i : Nat, i ≤ L → rhCenter (t + m * P) (1 + i) = false)
    (hw1 : ∀ i : Nat, i ≤ L → rhCenter t (1 + i) = false)
    (hpk : p + k ≤ L + 1) :
    rhCenter ((t + m * P) + k) p = rhCenter (t + k) p := by
  rw [periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t k p ht,
      ← rdrv_diag_eq_rhCenter t k p]
  exact rdrv_eq_of_both_initial_white_band t (t + m * P) t L k p hw2 hw1 hpk

/-! ### Batch 56: Drive-Wavefront Constancy & Inward Initial-Wavefront Shielding Laws of `rdrv` (`kit [33]`, 9.1132–9.1146) -/

/-- **Main-Diagonal Step Law of the Driven Right Half `rdrv` (`rdrv_main_diag_step_rhCenter`, 9.1132, `kit [33]`)**:
    for all `td, tx, k ∈ ℕ`, `rdrv td tx (k + 1) (k + 1) = bxor (rdrv td tx k k) (rhCenter (tx + k) (k + 1) || rhCenter (tx + k) (k + 2))` — on the main drive-cone diagonal `p = k`, the step increment depends ONLY on the initial state `tx` and is completely independent of the drive `td`! -/
theorem rdrv_main_diag_step_rhCenter (td tx k : Nat) :
    rdrv td tx (k + 1) (k + 1) =
    bxor (rdrv td tx k k) (rhCenter (tx + k) (k + 1) || rhCenter (tx + k) (k + 2)) := by
  rw [rdrv_step_succ td tx k k,
      rdrv_outside_cone_eq_rhCenter td tx k (k + 1) (by omega),
      rdrv_outside_cone_eq_rhCenter td tx k (k + 2) (by omega)]

/-- **Main-Diagonal Drive-Defect Constancy Law of `rdrv` (`rdrv_main_diag_drive_defect_const`, 9.1133)**:
    for all `td2, td, tx, k ∈ ℕ`, `bxor (rdrv td2 tx k k) (rdrv td tx k k) = bxor (center td2) (center td)` — changing the entire drive sequence changes the main diagonal `p = k` by the constant initial drive defect `bxor (center td2) (center td)`! -/
theorem rdrv_main_diag_drive_defect_const (td2 td tx k : Nat) :
    bxor (rdrv td2 tx k k) (rdrv td tx k k) =
    bxor (Rule30UOR.Core.center td2) (Rule30UOR.Core.center td) := by
  induction k with
  | zero =>
    rw [rdrv_col0, rdrv_col0, Nat.add_zero, Nat.add_zero]
  | succ k ih =>
    rw [rdrv_main_diag_step_rhCenter td2 tx k, rdrv_main_diag_step_rhCenter td tx k]
    have hxor : bxor (bxor (rdrv td2 tx k k) (rhCenter (tx + k) (k + 1) || rhCenter (tx + k) (k + 2)))
                     (bxor (rdrv td tx k k) (rhCenter (tx + k) (k + 1) || rhCenter (tx + k) (k + 2))) =
                bxor (rdrv td2 tx k k) (rdrv td tx k k) := by
      cases rdrv td2 tx k k <;> cases rdrv td tx k k <;>
        cases (rhCenter (tx + k) (k + 1) || rhCenter (tx + k) (k + 2)) <;> rfl
    rw [hxor, ih]

/-- **Exact Drive/State Separation Formula on the Main Diagonal of `rdrv` (`rdrv_main_diag_eq_rhCenter_xor_centers`, 9.1134, `kit [33]`)**:
    for all `td, tx, k ∈ ℕ`, `rdrv td tx k k = bxor (rhCenter (tx + k) k) (bxor (center td) (center tx))`! -/
theorem rdrv_main_diag_eq_rhCenter_xor_centers (td tx k : Nat) :
    rdrv td tx k k =
    bxor (rhCenter (tx + k) k) (bxor (Rule30UOR.Core.center td) (Rule30UOR.Core.center tx)) := by
  have hd := rdrv_main_diag_drive_defect_const td tx tx k
  rw [rdrv_diag_eq_rhCenter tx k k] at hd
  revert hd
  cases rdrv td tx k k <;> cases rhCenter (tx + k) k <;>
    cases Rule30UOR.Core.center td <;> cases Rule30UOR.Core.center tx <;> decide

/-- **Main-Diagonal Agreement of `rdrv td tx k k` with `rhCenter (tx + k) k` When `center td = center tx` (`rdrv_main_diag_eq_rhCenter_of_center_eq`, 9.1135)**:
    for all `td, tx, k ∈ ℕ`, if `center td = center tx`, then `rdrv td tx k k = rhCenter (tx + k) k`! -/
theorem rdrv_main_diag_eq_rhCenter_of_center_eq (td tx k : Nat)
    (hc : Rule30UOR.Core.center td = Rule30UOR.Core.center tx) :
    rdrv td tx k k = rhCenter (tx + k) k := by
  rw [rdrv_main_diag_eq_rhCenter_xor_centers td tx k, hc]
  cases rhCenter (tx + k) k <;> cases Rule30UOR.Core.center tx <;> rfl

/-- **Unattenuated Drive-Wavefront Defect Law Along Sub-Diagonal `d` (`rdrv_drive_wavefront_defect_const`, 9.1136, `kit [33]`)**:
    for all `td2, td, tx, d, p ∈ ℕ`, if `∀ j < d, center (td2 + j) = center (td + j)`, then `bxor (rdrv td2 tx (p + d) p) (rdrv td tx (p + d) p) = bxor (center (td2 + d)) (center (td + d))` — the first drive difference at step `d` propagates unattenuated along the entire wavefront diagonal `(p + d, p)` for all `p` and any initial state `tx`! -/
theorem rdrv_drive_wavefront_defect_const (td2 td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td2 + j) = Rule30UOR.Core.center (td + j)) :
    bxor (rdrv td2 tx (p + d) p) (rdrv td tx (p + d) p) =
    bxor (Rule30UOR.Core.center (td2 + d)) (Rule30UOR.Core.center (td + d)) := by
  induction p with
  | zero =>
    have h0 : 0 + d = d := by omega
    rw [h0, rdrv_col0, rdrv_col0]
  | succ p ih =>
    have h1 : (p + 1) + d = (p + d) + 1 := by omega
    rw [h1, rdrv_step_succ td2 tx (p + d) p, rdrv_step_succ td tx (p + d) p]
    have hc1 := rdrv_drive_causal_cone td2 td tx (p + d) (p + 1)
      (fun s hs => hc s (by omega))
    have hc2 := rdrv_drive_causal_cone td2 td tx (p + d) (p + 2)
      (fun s hs => hc s (by omega))
    rw [hc1, hc2]
    have hxor : bxor (bxor (rdrv td2 tx (p + d) p) (rdrv td tx (p + d) (p + 1) || rdrv td tx (p + d) (p + 2)))
                     (bxor (rdrv td tx (p + d) p) (rdrv td tx (p + d) (p + 1) || rdrv td tx (p + d) (p + 2))) =
                bxor (rdrv td2 tx (p + d) p) (rdrv td tx (p + d) p) := by
      cases rdrv td2 tx (p + d) p <;> cases rdrv td tx (p + d) p <;>
        cases (rdrv td tx (p + d) (p + 1) || rdrv td tx (p + d) (p + 2)) <;> rfl
    rw [hxor, ih]

/-- **Exact Drive-Wavefront Readout Formula Relative to `rhCenter` (`rdrv_drive_wavefront_eq_rhCenter_xor`, 9.1137)**:
    for all `td, tx, d, p ∈ ℕ`, if `∀ j < d, center (td + j) = center (tx + j)`, then `rdrv td tx (p + d) p = bxor (rhCenter (tx + (p + d)) p) (bxor (center (td + d)) (center (tx + d)))`! -/
theorem rdrv_drive_wavefront_eq_rhCenter_xor (td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = Rule30UOR.Core.center (tx + j)) :
    rdrv td tx (p + d) p =
    bxor (rhCenter (tx + (p + d)) p)
         (bxor (Rule30UOR.Core.center (td + d)) (Rule30UOR.Core.center (tx + d))) := by
  have hd := rdrv_drive_wavefront_defect_const td tx tx d p hc
  rw [rdrv_diag_eq_rhCenter tx (p + d) p] at hd
  revert hd
  cases rdrv td tx (p + d) p <;> cases rhCenter (tx + (p + d)) p <;>
    cases Rule30UOR.Core.center (td + d) <;> cases Rule30UOR.Core.center (tx + d) <;> decide

/-- **Exact Drive-Wavefront Flip Law at the First Drive Disagreement (`rdrv_drive_wavefront_flip_of_first_center_diff`, 9.1138)**:
    for all `td2, td, tx, d, p ∈ ℕ`, if `∀ j < d, center (td2 + j) = center (td + j)` and `center (td2 + d) = !(center (td + d))`, then `rdrv td2 tx (p + d) p = !(rdrv td tx (p + d) p)` for all `p`! -/
theorem rdrv_drive_wavefront_flip_of_first_center_diff (td2 td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td2 + j) = Rule30UOR.Core.center (td + j))
    (hdiff : Rule30UOR.Core.center (td2 + d) = !(Rule30UOR.Core.center (td + d))) :
    rdrv td2 tx (p + d) p = !(rdrv td tx (p + d) p) := by
  have hd := rdrv_drive_wavefront_defect_const td2 td tx d p hc
  rw [hdiff] at hd
  revert hd
  cases rdrv td2 tx (p + d) p <;> cases rdrv td tx (p + d) p <;>
    cases Rule30UOR.Core.center (td + d) <;> decide

/-- **1-Step Inward Wavefront Shielding by a Black Cell (`rdrv_inward_agree_step_of_black_shield`, 9.1139, `kit [33]`)**:
    for all `td, tx2, tx, k, d ∈ ℕ`, if `rdrv td tx2 k d = rdrv td tx k d`, `rdrv td tx2 k (d + 1) = rdrv td tx k (d + 1)`, and `rdrv td tx k (d + 1) = true`, then `rdrv td tx2 (k + 1) (d + 1) = rdrv td tx (k + 1) (d + 1)` (completely blocking any disagreement at `(k, d + 2)`)! -/
theorem rdrv_inward_agree_step_of_black_shield (td tx2 tx k d : Nat)
    (hd0 : rdrv td tx2 k d = rdrv td tx k d)
    (hd1 : rdrv td tx2 k (d + 1) = rdrv td tx k (d + 1))
    (hb : rdrv td tx k (d + 1) = true) :
    rdrv td tx2 (k + 1) (d + 1) = rdrv td tx (k + 1) (d + 1) := by
  rw [rdrv_step_succ td tx2 k d, rdrv_step_succ td tx k d, hd0, hd1, hb,
      Bool.true_or, Bool.true_or]

/-- **1-Step Inward Wavefront Defect Transmission Across a White Cell (`rdrv_inward_defect_step_of_white_shield`, 9.1140)**:
    for all `td, tx2, tx, k, d ∈ ℕ`, if `rdrv td tx2 k d = rdrv td tx k d`, `rdrv td tx2 k (d + 1) = rdrv td tx k (d + 1)`, and `rdrv td tx k (d + 1) = false`, then `bxor (rdrv td tx2 (k + 1) (d + 1)) (rdrv td tx (k + 1) (d + 1)) = bxor (rdrv td tx2 k (d + 2)) (rdrv td tx k (d + 2))`! -/
theorem rdrv_inward_defect_step_of_white_shield (td tx2 tx k d : Nat)
    (hd0 : rdrv td tx2 k d = rdrv td tx k d)
    (hd1 : rdrv td tx2 k (d + 1) = rdrv td tx k (d + 1))
    (hw : rdrv td tx k (d + 1) = false) :
    bxor (rdrv td tx2 (k + 1) (d + 1)) (rdrv td tx (k + 1) (d + 1)) =
    bxor (rdrv td tx2 k (d + 2)) (rdrv td tx k (d + 2)) := by
  rw [rdrv_step_succ td tx2 k d, rdrv_step_succ td tx k d, hd0, hd1, hw,
      Bool.false_or, Bool.false_or]
  cases rdrv td tx k d <;> cases rdrv td tx2 k (d + 2) <;> cases rdrv td tx k (d + 2) <;> rfl

/-- **1-Step Inward Agreement from Three-Column Agreement (`rdrv_inward_agree_step_of_three_agree`, 9.1141)**:
    for all `td, tx2, tx, k, d ∈ ℕ`, if `rdrv td tx2` and `rdrv td tx` agree at `(k, d)`, `(k, d + 1)`, and `(k, d + 2)`, then they agree at `(k + 1, d + 1)`! -/
theorem rdrv_inward_agree_step_of_three_agree (td tx2 tx k d : Nat)
    (hd0 : rdrv td tx2 k d = rdrv td tx k d)
    (hd1 : rdrv td tx2 k (d + 1) = rdrv td tx k (d + 1))
    (hd2 : rdrv td tx2 k (d + 2) = rdrv td tx k (d + 2)) :
    rdrv td tx2 (k + 1) (d + 1) = rdrv td tx (k + 1) (d + 1) := by
  rw [rdrv_step_succ td tx2 k d, rdrv_step_succ td tx k d, hd0, hd1, hd2]

/-- **Inward Wavefront Defect Transmission Outside `RhBandAgree` Across a White Boundary Cell (`rdrv_init_wavefront_defect_of_white`, 9.1142)**:
    for all `td, tx, Q, L, d, k ∈ ℕ`, if `RhBandAgree tx Q 1 L`, `d + k ≤ L`, and `rdrv td tx k (d + 1) = false`, then `bxor (rdrv td (tx + Q) (k + 1) (d + 1)) (rdrv td tx (k + 1) (d + 1)) = bxor (rdrv td (tx + Q) k (d + 2)) (rdrv td tx k (d + 2))`! -/
theorem rdrv_init_wavefront_defect_of_white (td tx Q L d k : Nat)
    (hband : RhBandAgree tx Q 1 L) (hdk : d + k ≤ L)
    (hw : rdrv td tx k (d + 1) = false) :
    bxor (rdrv td (tx + Q) (k + 1) (d + 1)) (rdrv td tx (k + 1) (d + 1)) =
    bxor (rdrv td (tx + Q) k (d + 2)) (rdrv td tx k (d + 2)) := by
  apply rdrv_inward_defect_step_of_white_shield td (tx + Q) tx k d
  · exact rdrv_init_causal_cone td tx Q L k d hband (by omega)
  · exact rdrv_init_causal_cone td tx Q L k (d + 1) hband (by omega)
  · exact hw

/-- **Inward Wavefront Absorption Outside `RhBandAgree` by a Black Boundary Cell (`rdrv_init_wavefront_absorb_of_black`, 9.1143, `kit [33]`)**:
    for all `td, tx, Q, L, d, k ∈ ℕ`, if `RhBandAgree tx Q 1 L`, `d + k ≤ L`, and `rdrv td tx k (d + 1) = true`, then `rdrv td (tx + Q) (k + 1) (d + 1) = rdrv td tx (k + 1) (d + 1)` — a black cell on the boundary `p + k = L + 1` absorbs the wavefront defect on `p + k = L + 2`! -/
theorem rdrv_init_wavefront_absorb_of_black (td tx Q L d k : Nat)
    (hband : RhBandAgree tx Q 1 L) (hdk : d + k ≤ L)
    (hb : rdrv td tx k (d + 1) = true) :
    rdrv td (tx + Q) (k + 1) (d + 1) = rdrv td tx (k + 1) (d + 1) := by
  apply rdrv_inward_agree_step_of_black_shield td (tx + Q) tx k d
  · exact rdrv_init_causal_cone td tx Q L k d hband (by omega)
  · exact rdrv_init_causal_cone td tx Q L k (d + 1) hband (by omega)
  · exact hb

/-- **Inward Wavefront Agreement Propagation Along `p + k = L + 2` (`rdrv_init_wavefront_agree_propagate`, 9.1144)**:
    for all `td, tx, Q, L, d, k, j ∈ ℕ`, if `RhBandAgree tx Q 1 L`, `d + (k + j) ≤ L + 1`, and `rdrv td (tx + Q) k ((d + 1) + j) = rdrv td tx k ((d + 1) + j)`, then `rdrv td (tx + Q) (k + j) (d + 1) = rdrv td tx (k + j) (d + 1)` — once the wavefront `p + k = L + 2` agrees at step `k`, it remains in agreement for all subsequent inward steps `k + j`! -/
theorem rdrv_init_wavefront_agree_propagate (td tx Q L d k j : Nat)
    (hband : RhBandAgree tx Q 1 L)
    (hd : d + (k + j) ≤ L + 1)
    (h0 : rdrv td (tx + Q) k ((d + 1) + j) = rdrv td tx k ((d + 1) + j)) :
    rdrv td (tx + Q) (k + j) (d + 1) = rdrv td tx (k + j) (d + 1) := by
  induction j generalizing d with
  | zero =>
    have h1 : k + 0 = k := by omega
    have h2 : (d + 1) + 0 = d + 1 := by omega
    rw [h1]
    rw [h2] at h0
    exact h0
  | succ j ih =>
    have hstep : rdrv td (tx + Q) ((k + j) + 1) (d + 1) = rdrv td tx ((k + j) + 1) (d + 1) := by
      apply rdrv_inward_agree_step_of_three_agree td (tx + Q) tx (k + j) d
      · exact rdrv_init_causal_cone td tx Q L (k + j) d hband (by omega)
      · exact rdrv_init_causal_cone td tx Q L (k + j) (d + 1) hband (by omega)
      · have h3 : d + 2 = (d + 1) + 1 := by omega
        rw [h3]
        apply ih (d + 1) (by omega)
        have h4 : ((d + 1) + 1) + j = (d + 1) + (j + 1) := by omega
        rw [h4]
        exact h0
    have h5 : k + (j + 1) = (k + j) + 1 := by omega
    rw [h5]
    exact hstep

/-- **Extension of Column-`1` Agreement from `L` to `L + 1` by a Single Black Shield Cell (`rdrv_init_wavefront_col_one_agree_of_black_shield`, 9.1145, `kit [33]`)**:
    for all `td, tx, Q, L, k ∈ ℕ`, if `RhBandAgree tx Q 1 L`, `k ≤ L`, and `rdrv td tx k ((L + 1) - k) = true`, then `rdrv td (tx + Q) (L + 1) 1 = rdrv td tx (L + 1) 1`! -/
theorem rdrv_init_wavefront_col_one_agree_of_black_shield (td tx Q L k : Nat)
    (hband : RhBandAgree tx Q 1 L) (hk : k ≤ L)
    (hb : rdrv td tx k ((L + 1) - k) = true) :
    rdrv td (tx + Q) (L + 1) 1 = rdrv td tx (L + 1) 1 := by
  have hb' : rdrv td tx k ((L - k) + 1) = true := by
    have h1 : (L - k) + 1 = (L + 1) - k := by omega
    rw [h1]
    exact hb
  have habs := rdrv_init_wavefront_absorb_of_black td tx Q L (L - k) k hband (by omega) hb'
  have hprop := rdrv_init_wavefront_agree_propagate td tx Q L 0 (k + 1) (L - k) hband (by omega)
  have h2 : (k + 1) + (L - k) = L + 1 := by omega
  have h3 : (0 + 1) + (L - k) = (L - k) + 1 := by omega
  rw [h2, h3] at hprop
  exact hprop habs

/-- **Extension of `maskparity · 0` Agreement from `L` to `L + 1` by a Single Black Shield Cell (`periodic_maskparity_zero_agree_of_rhBandAgree_and_black_shield`, 9.1146)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, L, k, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 L`, `k ≤ L`, `rdrv t t k ((L + 1) - k) = true`, and `s ≤ L + 1`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhBandAgree_and_black_shield
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L k s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 L) (hk : k ≤ L)
    (hb : rdrv t t k ((L + 1) - k) = true) (hs : s ≤ L + 1) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  by_cases hlt : s ≤ L
  · exact periodic_maskparity_zero_agree_of_rhBandAgree_one T P hP hper m t L s ht hband hlt
  · have hsL : s = L + 1 := by omega
    subst hsL
    refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t (L + 1) ht (fun _ => ?_)
    exact rdrv_init_wavefront_col_one_agree_of_black_shield t t (m * P) L k hband hk hb

/-! ### Batch 57: Black-Boundary Strip Shielding & Main-Diagonal Gate Determination of the Drive Cone in `rdrv` (`kit [33]`, 9.1147–9.1161) -/

/-- **Bounded-Width Strip Determination of `rdrv` Requiring Boundary Column `B + 2` Agreement ONLY When Column `B + 1` Is White (`rdrv_strip_agree_of_white_boundary_col_agree`, 9.1147, `kit [33]`)**:
    for all `td, tx, Q, B, S, s, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at step `0` and `∀ u < S, rdrv td tx u (B + 1) = false → rdrv td (tx + Q) u (B + 2) = rdrv td tx u (B + 2)`, then for all `s ≤ S` and `p ≤ B + 1`, `rdrv td (tx + Q) s p = rdrv td tx s p`! -/
theorem rdrv_strip_agree_of_white_boundary_col_agree
    (td tx Q B S s p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hcol : ∀ u : Nat, u < S →
      rdrv td tx u (B + 1) = false →
      rdrv td (tx + Q) u (B + 2) = rdrv td tx u (B + 2))
    (hs : s ≤ S) (hp : p ≤ B + 1) :
    rdrv td (tx + Q) s p = rdrv td tx s p := by
  induction s generalizing p with
  | zero =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [rdrv_init td (tx + Q) (p + 1) (by omega),
          rdrv_init td tx (p + 1) (by omega),
          show p + 1 = 1 + p by omega]
      exact hband p (by omega)
  | succ s ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [rdrv_step_succ td (tx + Q) s p, rdrv_step_succ td tx s p,
          ih p (by omega) (by omega),
          ih (p + 1) (by omega) (by omega)]
      by_cases hlt : p < B
      · rw [ih (p + 2) (by omega) (by omega)]
      · have hp1 : p + 1 = B + 1 := by omega
        have hp2 : p + 2 = B + 2 := by omega
        rw [hp1, hp2]
        cases hb : rdrv td tx s (B + 1)
        · rw [hcol s (by omega) hb]
        · rw [Bool.true_or, Bool.true_or]

/-- **Bounded-Width Strip Shielding by a Black Boundary Column `B + 1` (`rdrv_strip_agree_of_black_boundary_col`, 9.1148, `kit [33]`)**:
    for all `td, tx, Q, B, S, s, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at step `0` and `∀ u < S, rdrv td tx u (B + 1) = true`, then for all `s ≤ S` and `p ≤ B + 1`, `rdrv td (tx + Q) s p = rdrv td tx s p` (with zero dependence on columns `≥ B + 2`)! -/
theorem rdrv_strip_agree_of_black_boundary_col
    (td tx Q B S s p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hb : ∀ u : Nat, u < S → rdrv td tx u (B + 1) = true)
    (hs : s ≤ S) (hp : p ≤ B + 1) :
    rdrv td (tx + Q) s p = rdrv td tx s p := by
  refine rdrv_strip_agree_of_white_boundary_col_agree td tx Q B S s p hband (fun u hu hw => ?_) hs hp
  rw [hb u hu] at hw
  cases hw

/-- **Derivation of `maskparity · 0` Agreement Over `[t, t + S]` from a Black Boundary Column `B + 1` (`periodic_maskparity_zero_agree_of_black_boundary_col`, 9.1149)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, S, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` and `∀ u < S, rdrv t t u (B + 1) = true` hold and `s ≤ S`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_black_boundary_col
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B S s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hb : ∀ u : Nat, u < S → rdrv t t u (B + 1) = true) (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_strip_agree_of_black_boundary_col t t (m * P) B S s 1 hband hb hs (by omega)

/-- **First Sub-Diagonal Step Flip Law at a Black Main-Diagonal Gate (`rdrv_subdiag_one_step_of_black_main_diag`, 9.1150, `kit [33]`)**:
    for all `td, tx, k ∈ ℕ`, if `rdrv td tx (k + 1) (k + 1) = true`, then `rdrv td tx (k + 2) (k + 1) = !(rdrv td tx (k + 1) k)` — a black cell on the main diagonal `p = k + 1` shields the first sub-diagonal from `(k + 1, k + 2)`! -/
theorem rdrv_subdiag_one_step_of_black_main_diag (td tx k : Nat)
    (hb : rdrv td tx (k + 1) (k + 1) = true) :
    rdrv td tx (k + 2) (k + 1) = !(rdrv td tx (k + 1) k) := by
  have h1 : k + 2 = (k + 1) + 1 := by omega
  rw [h1, rdrv_step_succ td tx (k + 1) k, hb, Bool.true_or]
  cases rdrv td tx (k + 1) k <;> rfl

/-- **First Sub-Diagonal Step Law at a White Main-Diagonal Gate (`rdrv_subdiag_one_step_of_white_main_diag`, 9.1151)**:
    for all `td, tx, k ∈ ℕ`, if `rdrv td tx (k + 1) (k + 1) = false`, then `rdrv td tx (k + 2) (k + 1) = bxor (rdrv td tx (k + 1) k) (rhCenter (tx + (k + 1)) (k + 2))`! -/
theorem rdrv_subdiag_one_step_of_white_main_diag (td tx k : Nat)
    (hw : rdrv td tx (k + 1) (k + 1) = false) :
    rdrv td tx (k + 2) (k + 1) =
    bxor (rdrv td tx (k + 1) k) (rhCenter (tx + (k + 1)) (k + 2)) := by
  have h1 : k + 2 = (k + 1) + 1 := by omega
  rw [h1, rdrv_step_succ td tx (k + 1) k, hw, Bool.false_or,
      rdrv_outside_cone_eq_rhCenter td tx (k + 1) (k + 2) (by omega)]

/-- **Main-Diagonal Gate Determination Theorem for the Entire Drive Cone `p ≤ k` (`rdrv_drive_cone_agree_of_main_diag_gate`, 9.1152, `kit [33]`)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, if for all `1 ≤ u ≤ k`, `rdrv td tx2 u u = rdrv td tx u u` and (`rdrv td tx u u = false → rdrv td tx2 u (u + 1) = rdrv td tx u (u + 1)`), then for ALL `p ≤ k` inside the drive cone, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_drive_cone_agree_of_main_diag_gate (td tx2 tx k p : Nat)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ k → rdrv td tx2 u u = rdrv td tx u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ k →
      rdrv td tx u u = false → rdrv td tx2 u (u + 1) = rdrv td tx u (u + 1))
    (hpk : p ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  induction k generalizing p with
  | zero =>
    have hp0 : p = 0 := by omega
    subst hp0
    rw [rdrv_col0, rdrv_col0]
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · by_cases heq : p + 1 = k + 1
      · rw [heq]
        exact hdiag (k + 1) (by omega) (by omega)
      · have hpk' : p + 1 ≤ k := by omega
        rw [rdrv_step_succ td tx2 k p, rdrv_step_succ td tx k p]
        have ih0 := ih p (fun u hu1 hu2 => hdiag u hu1 (by omega))
          (fun u hu1 hu2 => hgate u hu1 (by omega)) (by omega)
        have ih1 := ih (p + 1) (fun u hu1 hu2 => hdiag u hu1 (by omega))
          (fun u hu1 hu2 => hgate u hu1 (by omega)) hpk'
        rw [ih0, ih1]
        by_cases hlt : p + 2 ≤ k
        · have ih2 := ih (p + 2) (fun u hu1 hu2 => hdiag u hu1 (by omega))
            (fun u hu1 hu2 => hgate u hu1 (by omega)) hlt
          rw [ih2]
        · have hp1k : p + 1 = k := by omega
          have hp2k : p + 2 = k + 1 := by omega
          rw [hp1k, hp2k]
          cases hkk : rdrv td tx k k
          · rw [hgate k (by omega) (by omega) hkk]
          · rw [Bool.true_or, Bool.true_or]

/-- **Total Drive-Cone Shielding by a Black Main Diagonal (`rdrv_drive_cone_agree_of_black_main_diag`, 9.1153, `kit [33]`)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, if `rdrv td tx2 u u = true` and `rdrv td tx u u = true` for all `1 ≤ u ≤ k`, then for ALL `p ≤ k` inside the drive cone, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_drive_cone_agree_of_black_main_diag (td tx2 tx k p : Nat)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ k → rdrv td tx2 u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ k → rdrv td tx u u = true)
    (hpk : p ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  refine rdrv_drive_cone_agree_of_main_diag_gate td tx2 tx k p
    (fun u hu1 hu2 => by rw [hb2 u hu1 hu2, hb1 u hu1 hu2])
    (fun u hu1 hu2 hw => ?_) hpk
  rw [hb1 u hu1 hu2] at hw
  cases hw

/-- **Exact Collapse of the Drive Cone `p ≤ k` to the Pure-Drive Right Half `rdrv td 0` Under a Black Main Diagonal (`rdrv_drive_cone_eq_white_seed_of_black_main_diag`, 9.1154, `kit [33]`)**:
    for all `td, tx, k, p ∈ ℕ`, if `center td = true` and `∀ u, 1 ≤ u → u ≤ k → rdrv td tx u u = true`, then for all `p ≤ k`, `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_drive_cone_eq_white_seed_of_black_main_diag (td tx k p : Nat)
    (hc : Rule30UOR.Core.center td = true)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ k → rdrv td tx u u = true)
    (hpk : p ≤ k) :
    rdrv td tx k p = rdrv td 0 k p := by
  refine rdrv_drive_cone_agree_of_black_main_diag td tx 0 k p hb
    (fun u _ _ => ?_) hpk
  rw [rdrv_white_seed_diag_eq_center td u, hc]

/-- **Exact Collapse of `rdrv td tx` to `rdrv td 0` Inside `p ≤ k` When `rhCenter (tx + u) u = true` (`rdrv_drive_cone_eq_white_seed_of_black_center_and_rhCenter_diag`, 9.1155)**:
    for all `td, tx, k, p ∈ ℕ`, if `center td = true`, `center tx = true`, and `∀ u, 1 ≤ u → u ≤ k → rhCenter (tx + u) u = true`, then for all `p ≤ k`, `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_drive_cone_eq_white_seed_of_black_center_and_rhCenter_diag (td tx k p : Nat)
    (hcd : Rule30UOR.Core.center td = true)
    (hcx : Rule30UOR.Core.center tx = true)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ k → rhCenter (tx + u) u = true)
    (hpk : p ≤ k) :
    rdrv td tx k p = rdrv td 0 k p := by
  refine rdrv_drive_cone_eq_white_seed_of_black_main_diag td tx k p hcd (fun u hu1 hu2 => ?_) hpk
  rw [rdrv_main_diag_eq_rhCenter_of_center_eq td tx u (by rw [hcd, hcx]), hb u hu1 hu2]

/-- **Exact Collapse of `rhCenter (t + k) p` to the Pure-Drive Right Half `rdrv t 0 k p` Inside `p ≤ k` (`rhCenter_drive_cone_eq_white_seed_of_black_diag`, 9.1156)**:
    for all `t, k, p ∈ ℕ`, if `center t = true` and `∀ u, 1 ≤ u → u ≤ k → rhCenter (t + u) u = true`, then for all `p ≤ k`, `rhCenter (t + k) p = rdrv t 0 k p`! -/
theorem rhCenter_drive_cone_eq_white_seed_of_black_diag (t k p : Nat)
    (hc : Rule30UOR.Core.center t = true)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ k → rhCenter (t + u) u = true)
    (hpk : p ≤ k) :
    rhCenter (t + k) p = rdrv t 0 k p := by
  rw [← rdrv_diag_eq_rhCenter t k p]
  exact rdrv_drive_cone_eq_white_seed_of_black_center_and_rhCenter_diag t t k p hc hc hb hpk

/-- **Derivation of `maskparity · 0` Agreement from Main-Diagonal Gate Agreement (`periodic_maskparity_zero_agree_of_main_diag_gate`, 9.1157, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t` and `1 ≤ s`, if for all `1 ≤ u ≤ s`, `rdrv t (t + m * P) u u = rdrv t t u u` and (`rdrv t t u u = false → rdrv t (t + m * P) u (u + 1) = rdrv t t u (u + 1)`), then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_main_diag_gate
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ s → rdrv t (t + m * P) u u = rdrv t t u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ s →
      rdrv t t u u = false → rdrv t (t + m * P) u (u + 1) = rdrv t t u (u + 1)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_drive_cone_agree_of_main_diag_gate t (t + m * P) t s 1 hdiag hgate hs

/-- **Derivation of `maskparity · 0` Agreement from a Black Main-Diagonal Gate (`periodic_maskparity_zero_agree_of_black_main_diag`, 9.1158)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t` and `1 ≤ s`, if `rdrv t (t + m * P) u u = true` and `rdrv t t u u = true` for all `1 ≤ u ≤ s`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_black_main_diag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ s → rdrv t (t + m * P) u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ s → rdrv t t u u = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_drive_cone_agree_of_black_main_diag t (t + m * P) t s 1 hb2 hb1 hs

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from Main-Diagonal Gate Agreement (`not_centerPeriodic_of_main_diag_gate_at_zero_diag`, 9.1159)**:
    if `T ≤ z + p`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and the main-diagonal gate condition holds from `z + p` over `1 ≤ u ≤ S + 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_main_diag_gate_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 →
      rdrv (z + p) ((z + p) + m * P) u u = rdrv (z + p) (z + p) u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 →
      rdrv (z + p) (z + p) u u = false →
      rdrv (z + p) ((z + p) + m * P) u (u + 1) = rdrv (z + p) (z + p) u (u + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm (by omega) hz hd hset1 hset2 hS (fun s hs => ?_) hper
  have h1 : (z + (p + 1)) + s = (z + p) + (s + 1) := by omega
  rw [h1]
  exact periodic_maskparity_zero_agree_of_main_diag_gate T P hP hper m (z + p) (s + 1) ht (by omega)
    (fun u hu1 hu2 => hdiag u hu1 (by omega))
    (fun u hu1 hu2 => hgate u hu1 (by omega))

theorem not_centerPeriodic_of_main_diag_gate_at_zero_diag_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hdiag : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 →
      rdrv (z + p) ((z + p) + m * P) u u = rdrv (z + p) (z + p) u u)
    (hgate : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 →
      rdrv (z + p) (z + p) u u = false →
      rdrv (z + p) ((z + p) + m * P) u (u + 1) = rdrv (z + p) (z + p) u (u + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_main_diag_gate_at_zero_diag T P m z p S hP hm ht
    hz hd hset1 hset2 hS hdiag hgate

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from a Black Main-Diagonal Gate (`not_centerPeriodic_of_black_main_diag_at_zero_diag`, 9.1160)**:
    if `T ≤ z + p`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and `rdrv (z + p) ((z + p) + m * P) u u = true` and `rdrv (z + p) (z + p) u u = true` for all `1 ≤ u ≤ S + 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_main_diag_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 → rdrv (z + p) ((z + p) + m * P) u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 → rdrv (z + p) (z + p) u u = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_main_diag_gate_at_zero_diag T P m z p S hP hm ht hz hd hset1 hset2 hS
    (fun u hu1 hu2 => by rw [hb2 u hu1 hu2, hb1 u hu1 hu2])
    (fun u hu1 hu2 hw => ?_)
  rw [hb1 u hu1 hu2] at hw
  cases hw

theorem not_centerPeriodic_of_black_main_diag_at_zero_diag_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 → rdrv (z + p) ((z + p) + m * P) u u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u ≤ S + 1 → rdrv (z + p) (z + p) u u = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_main_diag_at_zero_diag T P m z p S hP hm ht
    hz hd hset1 hset2 hS hb2 hb1

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from a Black Boundary Column `B + 1` (`not_centerPeriodic_of_black_boundary_col_at_zero_diag`, 9.1161)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, `RhBandAgree (z + (p + 1)) (m * P) 1 B`, and `∀ u < S, rdrv (z + (p + 1)) (z + (p + 1)) u (B + 1) = true`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_boundary_col_at_zero_diag
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hb : ∀ u : Nat, u < S → rdrv (z + (p + 1)) (z + (p + 1)) u (B + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_black_boundary_col
    T P hP hper m (z + (p + 1)) B S s ht hband hb hs

theorem not_centerPeriodic_of_black_boundary_col_at_zero_diag_prop
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hb : ∀ u : Nat, u < S → rdrv (z + (p + 1)) (z + (p + 1)) u (B + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_boundary_col_at_zero_diag T P m z p B S hP hm ht
    hz hd hset1 hset2 hS hband hb

/-! ### Batch 58: Two-Cell Diagonal Corridor Determination of the Drive Cone & Pure-Drive Scale Transfer (`kit [33]`, 9.1162–9.1176) -/

/-- **Main-Diagonal Agreement of `rdrv` from 2-Cell Super-Diagonal Corridor OR Agreement (`rdrv_main_diag_agree_of_corridor_or_agree`, 9.1162, `kit [33]`)**:
    for all `td, tx2, tx, k ∈ ℕ`, if for all `u < k`, `(rhCenter (tx2 + u) (u + 1) || rhCenter (tx2 + u) (u + 2)) = (rhCenter (tx + u) (u + 1) || rhCenter (tx + u) (u + 2))`, then `rdrv td tx2 k k = rdrv td tx k k`! -/
theorem rdrv_main_diag_agree_of_corridor_or_agree (td tx2 tx k : Nat)
    (hor : ∀ u : Nat, u < k →
      (rhCenter (tx2 + u) (u + 1) || rhCenter (tx2 + u) (u + 2)) =
      (rhCenter (tx + u) (u + 1) || rhCenter (tx + u) (u + 2))) :
    rdrv td tx2 k k = rdrv td tx k k := by
  induction k with
  | zero =>
    rw [rdrv_col0, rdrv_col0]
  | succ k ih =>
    rw [rdrv_main_diag_step_rhCenter td tx2 k,
        rdrv_main_diag_step_rhCenter td tx k,
        ih (fun u hu => hor u (by omega)),
        hor k (by omega)]

/-- **Main-Diagonal Constancy `rdrv td tx k k = center td` Under a 2-Cell White Super-Diagonal Corridor (`rdrv_main_diag_eq_center_of_white_corridor`, 9.1163, `kit [33]`)**:
    for all `td, tx, k ∈ ℕ`, if for all `u < k`, `rhCenter (tx + u) (u + 1) = false ∧ rhCenter (tx + u) (u + 2) = false`, then `rdrv td tx k k = center td`! -/
theorem rdrv_main_diag_eq_center_of_white_corridor (td tx k : Nat)
    (hw : ∀ u : Nat, u < k →
      rhCenter (tx + u) (u + 1) = false ∧ rhCenter (tx + u) (u + 2) = false) :
    rdrv td tx k k = Rule30UOR.Core.center td := by
  rw [← rdrv_white_seed_diag_eq_center td k]
  refine rdrv_main_diag_agree_of_corridor_or_agree td tx 0 k (fun u hu => ?_)
  obtain ⟨h1, h2⟩ := hw u hu
  rw [h1, h2, Nat.zero_add,
      rhCenter_gt_eq_false u (u + 1) (by omega),
      rhCenter_gt_eq_false u (u + 2) (by omega)]

/-- **2-Cell Super-Diagonal Corridor Determination of the Entire Drive Cone `p ≤ k` (`rdrv_drive_cone_agree_of_corridor_gate`, 9.1164, `kit [33]`)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, if for all `u ≤ k`, `rhCenter (tx2 + u) (u + 1) = rhCenter (tx + u) (u + 1)` and (`rhCenter (tx + u) (u + 1) = false → rhCenter (tx2 + u) (u + 2) = rhCenter (tx + u) (u + 2)`), then for ALL `p ≤ k`, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_drive_cone_agree_of_corridor_gate (td tx2 tx k p : Nat)
    (hc1 : ∀ u : Nat, u ≤ k → rhCenter (tx2 + u) (u + 1) = rhCenter (tx + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ k →
      rhCenter (tx + u) (u + 1) = false →
      rhCenter (tx2 + u) (u + 2) = rhCenter (tx + u) (u + 2))
    (hpk : p ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  refine rdrv_drive_cone_agree_of_main_diag_gate td tx2 tx k p
    (fun u _ hu2 => ?_) (fun u _ hu2 _ => ?_) hpk
  · refine rdrv_main_diag_agree_of_corridor_or_agree td tx2 tx u (fun j hj => ?_)
    rw [hc1 j (by omega)]
    cases h1 : rhCenter (tx + j) (j + 1)
    · rw [hc2 j (by omega) h1]
    · rw [Bool.true_or, Bool.true_or]
  · rw [rdrv_outside_cone_eq_rhCenter td tx2 u (u + 1) (by omega),
        rdrv_outside_cone_eq_rhCenter td tx u (u + 1) (by omega)]
    exact hc1 u hu2

/-- **Single Black First-Super-Diagonal Shielding of the Entire Drive Cone `p ≤ k` (`rdrv_drive_cone_agree_of_black_first_superdiag`, 9.1165, `kit [33]`)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, if for all `u ≤ k`, `rhCenter (tx2 + u) (u + 1) = true` and `rhCenter (tx + u) (u + 1) = true`, then for ALL `p ≤ k`, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_drive_cone_agree_of_black_first_superdiag (td tx2 tx k p : Nat)
    (hb2 : ∀ u : Nat, u ≤ k → rhCenter (tx2 + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ k → rhCenter (tx + u) (u + 1) = true)
    (hpk : p ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  refine rdrv_drive_cone_agree_of_corridor_gate td tx2 tx k p
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_) hpk
  rw [hb1 u hu] at hw
  cases hw

/-- **Exact Collapse of the Drive Cone `p ≤ k` to the Pure-Drive Right Half `rdrv td 0` Under a 2-Cell White Super-Diagonal Corridor (`rdrv_drive_cone_eq_white_seed_of_white_corridor`, 9.1166, `kit [33]`)**:
    for all `td, tx, k, p ∈ ℕ`, if for all `u ≤ k`, `rhCenter (tx + u) (u + 1) = false ∧ rhCenter (tx + u) (u + 2) = false`, then for ALL `p ≤ k`, `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_drive_cone_eq_white_seed_of_white_corridor (td tx k p : Nat)
    (hw : ∀ u : Nat, u ≤ k →
      rhCenter (tx + u) (u + 1) = false ∧ rhCenter (tx + u) (u + 2) = false)
    (hpk : p ≤ k) :
    rdrv td tx k p = rdrv td 0 k p := by
  refine rdrv_drive_cone_agree_of_corridor_gate td tx 0 k p
    (fun u hu => ?_) (fun u hu _ => ?_) hpk
  · rw [(hw u hu).1, Nat.zero_add, rhCenter_gt_eq_false u (u + 1) (by omega)]
  · rw [(hw u hu).2, Nat.zero_add, rhCenter_gt_eq_false u (u + 2) (by omega)]

/-- **Exact Collapse of `rhCenter (t + k) p` to `rdrv t 0 k p` Inside `p ≤ k` Under a 2-Cell White Super-Diagonal Corridor (`rhCenter_drive_cone_eq_white_seed_of_white_corridor`, 9.1167)**:
    for all `t, k, p ∈ ℕ`, if for all `u ≤ k`, `rhCenter (t + u) (u + 1) = false ∧ rhCenter (t + u) (u + 2) = false`, then for ALL `p ≤ k`, `rhCenter (t + k) p = rdrv t 0 k p`! -/
theorem rhCenter_drive_cone_eq_white_seed_of_white_corridor (t k p : Nat)
    (hw : ∀ u : Nat, u ≤ k →
      rhCenter (t + u) (u + 1) = false ∧ rhCenter (t + u) (u + 2) = false)
    (hpk : p ≤ k) :
    rhCenter (t + k) p = rdrv t 0 k p := by
  rw [← rdrv_diag_eq_rhCenter t k p]
  exact rdrv_drive_cone_eq_white_seed_of_white_corridor t t k p hw hpk

/-- **Dyadic Scale Readout of `rdrv td tx` Under a Black Main Diagonal (`rdrv_scale_eq_center_of_black_main_diag`, 9.1168, `kit [33]`)**:
    for all `td, tx, d, k ∈ ℕ`, if `center td = true`, `d ≤ k`, and `∀ u, 1 ≤ u → u ≤ d + 2^k → rdrv td tx u u = true`, then `rdrv td tx (d + 2^k) (2^k) = center (td + d)`! -/
theorem rdrv_scale_eq_center_of_black_main_diag (td tx d k : Nat)
    (hc : Rule30UOR.Core.center td = true) (hdk : d ≤ k)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ d + twopow k → rdrv td tx u u = true) :
    rdrv td tx (d + twopow k) (twopow k) = Rule30UOR.Core.center (td + d) := by
  rw [rdrv_drive_cone_eq_white_seed_of_black_main_diag td tx (d + twopow k) (twopow k) hc hb (by omega),
      rdrv_white_seed_scale_ge_eq_center td d k hdk]

/-- **Right-Half Dyadic Scale Identity Under a Black Main Diagonal (`rhCenter_scale_eq_center_of_black_diag`, 9.1169)**:
    for all `t, d, k ∈ ℕ`, if `center t = true`, `d ≤ k`, and `∀ u, 1 ≤ u → u ≤ d + 2^k → rhCenter (t + u) u = true`, then `rhCenter (t + (d + 2^k)) (2^k) = center (t + d)`! -/
theorem rhCenter_scale_eq_center_of_black_diag (t d k : Nat)
    (hc : Rule30UOR.Core.center t = true) (hdk : d ≤ k)
    (hb : ∀ u : Nat, 1 ≤ u → u ≤ d + twopow k → rhCenter (t + u) u = true) :
    rhCenter (t + (d + twopow k)) (twopow k) = Rule30UOR.Core.center (t + d) := by
  rw [rhCenter_drive_cone_eq_white_seed_of_black_diag t (d + twopow k) (twopow k) hc hb (by omega),
      rdrv_white_seed_scale_ge_eq_center t d k hdk]

/-- **Dyadic Scale Readout of `rdrv td tx` Under a 2-Cell White Super-Diagonal Corridor (`rdrv_scale_eq_center_of_white_corridor`, 9.1170, `kit [33]`)**:
    for all `td, tx, d, k ∈ ℕ`, if `d ≤ k` and `∀ u ≤ d + 2^k, rhCenter (tx + u) (u + 1) = false ∧ rhCenter (tx + u) (u + 2) = false`, then `rdrv td tx (d + 2^k) (2^k) = center (td + d)`! -/
theorem rdrv_scale_eq_center_of_white_corridor (td tx d k : Nat)
    (hdk : d ≤ k)
    (hw : ∀ u : Nat, u ≤ d + twopow k →
      rhCenter (tx + u) (u + 1) = false ∧ rhCenter (tx + u) (u + 2) = false) :
    rdrv td tx (d + twopow k) (twopow k) = Rule30UOR.Core.center (td + d) := by
  rw [rdrv_drive_cone_eq_white_seed_of_white_corridor td tx (d + twopow k) (twopow k) hw (by omega),
      rdrv_white_seed_scale_ge_eq_center td d k hdk]

/-- **Right-Half Dyadic Scale Identity Under a 2-Cell White Super-Diagonal Corridor (`rhCenter_scale_eq_center_of_white_corridor`, 9.1171)**:
    for all `t, d, k ∈ ℕ`, if `d ≤ k` and `∀ u ≤ d + 2^k, rhCenter (t + u) (u + 1) = false ∧ rhCenter (t + u) (u + 2) = false`, then `rhCenter (t + (d + 2^k)) (2^k) = center (t + d)`! -/
theorem rhCenter_scale_eq_center_of_white_corridor (t d k : Nat)
    (hdk : d ≤ k)
    (hw : ∀ u : Nat, u ≤ d + twopow k →
      rhCenter (t + u) (u + 1) = false ∧ rhCenter (t + u) (u + 2) = false) :
    rhCenter (t + (d + twopow k)) (twopow k) = Rule30UOR.Core.center (t + d) := by
  rw [rhCenter_drive_cone_eq_white_seed_of_white_corridor t (d + twopow k) (twopow k) hw (by omega),
      rdrv_white_seed_scale_ge_eq_center t d k hdk]

/-- **Transfer of `2^d`-Diagonal Periodicity to `rdrv td tx` Under a Black Main Diagonal (`rdrv_subdiag_period_twopow_of_black_main_diag`, 9.1172)**:
    for all `td, tx, d, k, u ∈ ℕ`, if `center td = true` and `∀ j, 1 ≤ j → j ≤ (k + d) + u * 2^d → rdrv td tx j j = true`, then `rdrv td tx ((k + d) + u * 2^d) (k + u * 2^d) = rdrv td tx (k + d) k`! -/
theorem rdrv_subdiag_period_twopow_of_black_main_diag (td tx d k u : Nat)
    (hc : Rule30UOR.Core.center td = true)
    (hb : ∀ j : Nat, 1 ≤ j → j ≤ (k + d) + u * twopow d → rdrv td tx j j = true) :
    rdrv td tx ((k + d) + u * twopow d) (k + u * twopow d) =
    rdrv td tx (k + d) k := by
  rw [rdrv_drive_cone_eq_white_seed_of_black_main_diag td tx
        ((k + d) + u * twopow d) (k + u * twopow d) hc hb (by omega),
      rdrv_drive_cone_eq_white_seed_of_black_main_diag td tx
        (k + d) k hc (fun j hj1 hj2 => hb j hj1 (by omega)) (by omega),
      rdrv_white_seed_subdiag_period_twopow td d k u]

/-- **Derivation of `maskparity · 0` Agreement from 2-Cell Super-Diagonal Corridor Agreement (`periodic_maskparity_zero_agree_of_corridor_gate`, 9.1173, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t` and `1 ≤ s`, if for all `u ≤ s`, `rhCenter ((t + m * P) + u) (u + 1) = rhCenter (t + u) (u + 1)` and (`rhCenter (t + u) (u + 1) = false → rhCenter ((t + m * P) + u) (u + 2) = rhCenter (t + u) (u + 2)`), then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_corridor_gate
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hc1 : ∀ u : Nat, u ≤ s → rhCenter ((t + m * P) + u) (u + 1) = rhCenter (t + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ s →
      rhCenter (t + u) (u + 1) = false →
      rhCenter ((t + m * P) + u) (u + 2) = rhCenter (t + u) (u + 2)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_drive_cone_agree_of_corridor_gate t (t + m * P) t s 1 hc1 hc2 hs

/-- **Derivation of `maskparity · 0` Agreement from a Single Black First Super-Diagonal (`periodic_maskparity_zero_agree_of_black_first_superdiag`, 9.1174)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t` and `1 ≤ s`, if for all `u ≤ s`, `rhCenter ((t + m * P) + u) (u + 1) = true` and `rhCenter (t + u) (u + 1) = true`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_black_first_superdiag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t) (hs : 1 ≤ s)
    (hb2 : ∀ u : Nat, u ≤ s → rhCenter ((t + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ s → rhCenter (t + u) (u + 1) = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_drive_cone_agree_of_black_first_superdiag t (t + m * P) t s 1 hb2 hb1 hs

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from 2-Cell Super-Diagonal Corridor Agreement (`not_centerPeriodic_of_corridor_gate_at_zero_diag`, 9.1175)**:
    if `T ≤ z + p`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and the 2-cell super-diagonal corridor gate holds from `z + p` over `u ≤ S + 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_corridor_gate_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S + 1 →
      rhCenter (((z + p) + m * P) + u) (u + 1) = rhCenter ((z + p) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S + 1 →
      rhCenter ((z + p) + u) (u + 1) = false →
      rhCenter (((z + p) + m * P) + u) (u + 2) = rhCenter ((z + p) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm (by omega) hz hd hset1 hset2 hS (fun s hs => ?_) hper
  have h1 : (z + (p + 1)) + s = (z + p) + (s + 1) := by omega
  rw [h1]
  exact periodic_maskparity_zero_agree_of_corridor_gate T P hP hper m (z + p) (s + 1) ht (by omega)
    (fun u hu => hc1 u (by omega))
    (fun u hu => hc2 u (by omega))

theorem not_centerPeriodic_of_corridor_gate_at_zero_diag_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S + 1 →
      rhCenter (((z + p) + m * P) + u) (u + 1) = rhCenter ((z + p) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S + 1 →
      rhCenter ((z + p) + u) (u + 1) = false →
      rhCenter (((z + p) + m * P) + u) (u + 2) = rhCenter ((z + p) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_corridor_gate_at_zero_diag T P m z p S hP hm ht
    hz hd hset1 hset2 hS hc1 hc2

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from a Single Black First Super-Diagonal (`not_centerPeriodic_of_black_first_superdiag_at_zero_diag`, 9.1176)**:
    if `T ≤ z + p`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and `rhCenter (((z + p) + m * P) + u) (u + 1) = true` and `rhCenter ((z + p) + u) (u + 1) = true` for all `u ≤ S + 1`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_first_superdiag_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S + 1 → rhCenter (((z + p) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S + 1 → rhCenter ((z + p) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_corridor_gate_at_zero_diag T P m z p S hP hm ht hz hd hset1 hset2 hS
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_)
  rw [hb1 u hu] at hw
  cases hw

theorem not_centerPeriodic_of_black_first_superdiag_at_zero_diag_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + p)
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S + 1 → rhCenter (((z + p) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S + 1 → rhCenter ((z + p) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_first_superdiag_at_zero_diag T P m z p S hP hm ht
    hz hd hset1 hset2 hS hb2 hb1

end Rule30UOR.Interfaces
