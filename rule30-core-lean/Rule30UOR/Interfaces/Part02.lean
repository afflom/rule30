module

public import Rule30UOR.Interfaces.Part01

/-!
# `Rule30UOR.Interfaces`, part 2

* Step 1–3: Reduction of the Late Term under `CenterPeriodic`, Bridge to `ZCenterPeriodic`, and Zero-State Non-Periodicity Laws
* Exact `Nat`-Level 1-Cocycle of `winWitt`, Triality Sector Readouts, and Vacuum-Tree `zcenter` Laws
* The XOR Channel: Masked Column-1 Parity (`carry60`, `maskcount`, `maskparity`) and `MaskPos`
* Two-Half Dyadic Scale Equations: Right Threshold `J` vs. Left `ldiag` / `leftresponse` and Periodic Center
* Exact OR-Gate Factorization of the Right and Left Laws Across Scale `2^k`
* Off-Center Two-Half Triality and Coboundary Equations at Slot `r = d + 2 * s < 2^k`
* Column `-1` (`s = 1`) Off-Center Scale Equations and Coupling to the XOR Channel (`maskparity · 0`)
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

/-! ### Step 1–3: Reduction of the Late Term under `CenterPeriodic`, Bridge to `ZCenterPeriodic`, and Zero-State Non-Periodicity Laws -/

/-- Under `CenterPeriodic T P` (`0 < P`), inside the light cone (`T ≤ t`, `t + P < 2^k`), the Rule-60 response `response t k` is periodic in `t` with period `P`. -/
theorem periodic_response_shift_P (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P < twopow k) :
    Rule30UOR.Scale.response (t + P) k = Rule30UOR.Scale.response t k := by
  rw [Rule30UOR.Scale.periodic_scale_cone_paper T P hP h k (t + P) (by omega) htP,
    Rule30UOR.Scale.periodic_scale_cone_paper T P hP h k t ht (by omega),
    show (t + P) + Rule30UOR.Scale.lag P k = (t + Rule30UOR.Scale.lag P k) + P by omega,
    h (t + Rule30UOR.Scale.lag P k) (by omega),
    h t ht]

/-- Under `CenterPeriodic T P` (`0 < P`), inside the light cone (`T ≤ t`, `t + P < 2^k`), the Witt center response `wittRespBool t k` is periodic in `t` with period `P`. -/
theorem periodic_witt_shift_P (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P < twopow k) :
    wittRespBool (t + P) k = wittRespBool t k := by
  rw [wittRespBool_eq_response_cone (t + P) k htP,
    wittRespBool_eq_response_cone t k (by omega)]
  exact periodic_response_shift_P T P hP h t k ht htP

/-- Under `CenterPeriodic T P` (`0 < P`), for `T ≤ d` and `d + P < 2^k`, Triality Sector 1 of `winWitt` at the center slot is invariant under `d ↦ d + P`. -/
theorem periodic_winWitt_sector_one_shift_P (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hdP : d + P < twopow k) :
    (winWitt (d + P) (twopow k)).testBit ((d + P) + twopow k) =
      (winWitt d (twopow k)).testBit (d + twopow k) :=
  periodic_witt_shift_P T P hP h d k ht hdP

/-- Paper-facing `bit` (`wittbit`) wrapper for `periodic_winWitt_sector_one_shift_P`. -/
theorem bit_periodic_winWitt_sector_one_shift_P (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hdP : d + P < twopow k) :
    bit (winWitt (d + P) (twopow k)) ((d + P) + twopow k) =
      bit (winWitt d (twopow k)) (d + twopow k) := by
  rw [bit_eq_bton_testBit, bit_eq_bton_testBit,
    periodic_winWitt_sector_one_shift_P T P hP h d k ht hdP]

/-- **Unsettled Reduction of the Late Term `response (d + 2^k) k` under `CenterPeriodic T P`**: for `T ≤ d ≤ k`, `response (d + 2^k) k` reduces to the lag-class center difference `center (d + lag P (k + 1)) ⊕ center (d + lag P k)` XORed with the left diagonal `ldiag d (d + 2^k)`. -/
theorem periodic_late_response_unsettled_decomp (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Scale.response (d + twopow k) k =
      bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (ldiag d (d + twopow k)) := by
  have hdk : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hdk1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hcob := ldiag_eq_response_coboundary d k hk
  have hr0 := Rule30UOR.Scale.periodic_scale_cone_paper T P hP h k d ht hdk
  have hr1 := Rule30UOR.Scale.periodic_scale_cone_paper T P hP h (k + 1) d ht hdk1
  rw [hr0, hr1] at hcob
  revert hcob
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center d <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Scale.response (d + twopow k) k <;>
    cases ldiag d (d + twopow k) <;> decide

/-- **Settled Reduction of the Late Term `response (d + 2^k) k` under `CenterPeriodic T P`**: for `T ≤ d ≤ k` with `SettledAt d k`, `response (d + 2^k) k` reduces to `center (d + lag P (k + 1)) ⊕ center (d + lag P k) ⊕ zcenter d`. -/
theorem periodic_late_response_settled_decomp (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) (hset : SettledAt d k) :
    Rule30UOR.Scale.response (d + twopow k) k =
      bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (zcenter d) := by
  rw [← ldiag_settled_eq_zcenter d k hk hset]
  exact periodic_late_response_unsettled_decomp T P hP h d k ht hk

/-- **Zero-State Diagonal Readout `zcenter d` from Lag Class and Late Response under `CenterPeriodic T P`**: for `T ≤ d ≤ k` with `SettledAt d k`, `zcenter d = center (d + lag P (k + 1)) ⊕ center (d + lag P k) ⊕ response (d + 2^k) k`. -/
theorem periodic_zcenter_from_lag_and_late_response (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) (hset : SettledAt d k) :
    zcenter d =
      bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hd := periodic_late_response_settled_decomp T P hP h d k ht hk hset
  revert hd
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Scale.response (d + twopow k) k <;>
    cases zcenter d <;> decide

/-- **Exact Shift-by-`P` Defect Reduction for `zcenter` via Late Rule-60 Response**: under `CenterPeriodic T P`, for any `T ≤ d` and any scale `k ≥ d + P` where both `d` and `d + P` have settled (`SettledAt d k`, `SettledAt (d + P) k`), the `zcenter` periodicity defect `zcenter (d + P) ⊕ zcenter d` equals the late response difference `response (d + P + 2^k) k ⊕ response (d + 2^k) k`. -/
theorem periodic_zcenter_shift_xor_eq_late_response_xor (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k)
    (hset1 : SettledAt d k) (hset2 : SettledAt (d + P) k) :
    bxor (zcenter (d + P)) (zcenter d) =
      bxor (Rule30UOR.Scale.response ((d + P) + twopow k) k)
        (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hz1 := zcenter_from_late_scale d k (by omega) hset1
  have hz2 := zcenter_from_late_scale (d + P) k hk hset2
  have hc1 : Rule30UOR.Core.center ((d + P) + twopow k) = Rule30UOR.Core.center (d + twopow k) := by
    rw [show (d + P) + twopow k = (d + twopow k) + P by omega]
    exact h (d + twopow k) (by omega)
  have hc2 : Rule30UOR.Core.center (((d + P) + twopow k) + twopow k) =
      Rule30UOR.Core.center ((d + twopow k) + twopow k) := by
    rw [show ((d + P) + twopow k) + twopow k = ((d + twopow k) + twopow k) + P by omega]
    exact h ((d + twopow k) + twopow k) (by omega)
  rw [hz1, hz2, hc1, hc2]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center ((d + twopow k) + twopow k) <;>
    cases Rule30UOR.Core.center (d + twopow k) <;>
    cases Rule30UOR.Scale.response ((d + P) + twopow k) k <;>
    cases Rule30UOR.Scale.response (d + twopow k) k <;> rfl

/-- **Exact Shift-by-`P` Defect Reduction for `zcenter` via Late Witt Response**: under `CenterPeriodic T P`, for any `T ≤ d` and `k ≥ d + P` with `SettledAt d k` and `SettledAt (d + P) k`, `zcenter (d + P) ⊕ zcenter d = wittRespBool (d + P + 2^k) k ⊕ wittRespBool (d + 2^k) k`. -/
theorem periodic_zcenter_shift_xor_eq_late_witt_xor (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k)
    (hset1 : SettledAt d k) (hset2 : SettledAt (d + P) k) :
    bxor (zcenter (d + P)) (zcenter d) =
      bxor (wittRespBool ((d + P) + twopow k) k)
        (wittRespBool (d + twopow k) k) := by
  have hr := periodic_zcenter_shift_xor_eq_late_response_xor T P h d k ht hk hset1 hset2
  have hc1 := center_from_late_responses d k (by omega)
  have hc2 := center_from_late_responses (d + P) k hk
  have hcp := h d ht
  rw [hcp] at hc2
  revert hr hc1 hc2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center d <;>
    cases zcenter (d + P) <;>
    cases zcenter d <;>
    cases wittRespBool ((d + P) + twopow k) k <;>
    cases wittRespBool (d + twopow k) k <;>
    cases Rule30UOR.Scale.response ((d + P) + twopow k) k <;>
    cases Rule30UOR.Scale.response (d + twopow k) k <;> decide

/-- **Exact Shift-by-`P` Defect Reduction for `zcenter` via Triality Sector 2 of `winWitt`**: under `CenterPeriodic T P`, for any `T ≤ d` and `k ≥ d + P` with `SettledAt d k` and `SettledAt (d + P) k`, `zcenter (d + P) ⊕ zcenter d` equals the XOR of Sector 2 of `winWitt (d + P) (2^k)` at slot `d + P` and Sector 2 of `winWitt d (2^k)` at slot `d`. -/
theorem periodic_zcenter_shift_xor_eq_sector_two_xor (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k)
    (hset1 : SettledAt d k) (hset2 : SettledAt (d + P) k) :
    bxor (zcenter (d + P)) (zcenter d) =
      bxor ((winWitt (d + P) (twopow k)).testBit ((d + P) + twopow (k + 1)))
        ((winWitt d (twopow k)).testBit (d + twopow (k + 1))) := by
  rw [winWitt_testBit_archimedean (d + P) k hk,
    winWitt_testBit_archimedean d k (by omega),
    ldiag_settled_eq_zcenter (d + P) k hk hset2,
    ldiag_settled_eq_zcenter d k (by omega) hset1,
    h d ht]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center d <;>
    cases zcenter (d + P) <;>
    cases zcenter d <;> rfl

/-- For every pair of depths `d1, d2`, there exists a scale `k` with `d1 ≤ k`, `d2 ≤ k`, `SettledAt d1 k`, and `SettledAt d2 k`. -/
theorem exists_settled_scale_pair (d1 d2 : Nat) :
    ∃ k, d1 ≤ k ∧ d2 ≤ k ∧ SettledAt d1 k ∧ SettledAt d2 k := by
  let k := d1 + d2 + settle d1 + settle d2
  have hgt := twopow_gt_self k
  refine ⟨k, by omega, by omega, ?_, ?_⟩
  · unfold SettledAt; omega
  · unfold SettledAt; omega

/-- Eventual periodicity of the zero-state diagonal readout `zcenter` with period `Q` from threshold `T`. -/
def ZCenterPeriodic (T Q : Nat) : Prop :=
  ∀ d, T ≤ d → zcenter (d + Q) = zcenter d

/-- **Step 2 Bridge (Rule-60 Form)**: if `CenterPeriodic T P` holds and the settled late Rule-60 response `response (d + 2^k) k` is invariant under `d ↦ d + P` at jointly settled scales `k ≥ d + P`, then `zcenter` is periodic with period `P` from `T` (`ZCenterPeriodic T P`). -/
theorem zcenter_periodic_of_late_response_shift (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hlate : ∀ d k, T ≤ d → d + P ≤ k → SettledAt d k → SettledAt (d + P) k →
      Rule30UOR.Scale.response ((d + P) + twopow k) k = Rule30UOR.Scale.response (d + twopow k) k) :
    ZCenterPeriodic T P := by
  intro d ht
  obtain ⟨k, _, hk2, hset1, hset2⟩ := exists_settled_scale_pair d (d + P)
  have hxor := periodic_zcenter_shift_xor_eq_late_response_xor T P h d k ht hk2 hset1 hset2
  rw [hlate d k ht hk2 hset1 hset2, bxor_eq_xor, bxor_eq_xor, Bool.xor_self] at hxor
  revert hxor
  cases zcenter (d + P) <;> cases zcenter d <;> decide

/-- **Step 2 Bridge (Witt Form)**: if `CenterPeriodic T P` holds and the settled late Witt response `wittRespBool (d + 2^k) k` is invariant under `d ↦ d + P` at jointly settled scales `k ≥ d + P`, then `zcenter` is periodic with period `P` from `T` (`ZCenterPeriodic T P`). -/
theorem zcenter_periodic_of_late_witt_shift (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hlate : ∀ d k, T ≤ d → d + P ≤ k → SettledAt d k → SettledAt (d + P) k →
      wittRespBool ((d + P) + twopow k) k = wittRespBool (d + twopow k) k) :
    ZCenterPeriodic T P := by
  intro d ht
  obtain ⟨k, _, hk2, hset1, hset2⟩ := exists_settled_scale_pair d (d + P)
  have hxor := periodic_zcenter_shift_xor_eq_late_witt_xor T P h d k ht hk2 hset1 hset2
  rw [hlate d k ht hk2 hset1 hset2, bxor_eq_xor, bxor_eq_xor, Bool.xor_self] at hxor
  revert hxor
  cases zcenter (d + P) <;> cases zcenter d <;> decide

/-- **Step 3 Anchor 1 (`zcenter` is never periodic of period `1`)**: for every threshold `T`, `¬ ZCenterPeriodic T 1`. -/
theorem zcenter_not_periodic_one (T : Nat) : ¬ ZCenterPeriodic T 1 := by
  intro hper
  obtain ⟨z, hzT, hz0, hz2⟩ := zcenter_oscillates T
  have h1 := hper z hzT
  have h2 := hper (z + 1) (by omega)
  rw [show z + 1 + 1 = z + 2 by omega] at h2
  rw [hz0] at h1
  rw [h1] at h2
  rw [hz2] at h2
  contradiction

/-- **Step 3 Anchor 2 (`zcenter` is never periodic of period `2`)**: for every threshold `T`, `¬ ZCenterPeriodic T 2`. -/
theorem zcenter_not_periodic_two (T : Nat) : ¬ ZCenterPeriodic T 2 := by
  intro hper
  obtain ⟨z, hzT, hz0, hz2⟩ := zcenter_oscillates T
  have h2 := hper z hzT
  rw [hz0, hz2] at h2
  contradiction

/-- Under `ZCenterPeriodic T Q`, shifting by any multiple `m * Q` preserves `zcenter d` for `T ≤ d`. -/
theorem zcenter_periodic_mul {T Q : Nat} (h : ZCenterPeriodic T Q) :
    ∀ m d, T ≤ d → zcenter (d + m * Q) = zcenter d
  | 0, d, _ => by simp
  | m + 1, d, hd => by
    rw [show d + (m + 1) * Q = (d + m * Q) + Q by rw [Nat.succ_mul]; omega,
      h (d + m * Q) (by omega), zcenter_periodic_mul h m d hd]

/-- **Step 3 Anchor 3 (Zero-Diagonal Resonance Obstruction to `ZCenterPeriodic T Q`)**: if `ZCenterPeriodic T Q` holds, then for every zero diagonal `z ≥ T` and every multiple `m`, `z + 2 + m * Q` can never be a zero diagonal (`¬ IsZeroDiag (z + 2 + m * Q)`). -/
theorem zcenter_periodic_not_zero_diag_shift (T Q : Nat) (h : ZCenterPeriodic T Q)
    (z m : Nat) (hz : IsZeroDiag z) (hzT : T ≤ z) :
    ¬ IsZeroDiag ((z + 2) + m * Q) := by
  intro hz_shift
  have hfalse := zcenter_of_zero_diag ((z + 2) + m * Q) hz_shift
  have htrue : zcenter ((z + 2) + m * Q) = true := by
    rw [zcenter_periodic_mul h m (z + 2) (by omega)]
    exact zcenter_after_zero_diag z hz
  rw [hfalse] at htrue
  contradiction

/-- Prop-valued XOR comparison `bxor (zcenter d1) (zcenter d2) = b` for paper-facing theorems. -/
def ZCenterXorEq (d1 d2 : Nat) (b : Bool) : Prop :=
  bxor (zcenter d1) (zcenter d2) = b

theorem periodic_zcenter_from_lag_and_late_response_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) (hset : SettledAt d k) :
    ZCenterEq d
      (bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (Rule30UOR.Scale.response (d + twopow k) k)) :=
  periodic_zcenter_from_lag_and_late_response T P hP h d k ht hk hset

theorem periodic_zcenter_shift_xor_eq_late_response_xor_prop (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k)
    (hset1 : SettledAt d k) (hset2 : SettledAt (d + P) k) :
    ZCenterXorEq (d + P) d
      (bxor (Rule30UOR.Scale.response ((d + P) + twopow k) k)
        (Rule30UOR.Scale.response (d + twopow k) k)) :=
  periodic_zcenter_shift_xor_eq_late_response_xor T P h d k ht hk hset1 hset2

theorem periodic_zcenter_shift_xor_eq_late_witt_xor_prop (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k)
    (hset1 : SettledAt d k) (hset2 : SettledAt (d + P) k) :
    ZCenterXorEq (d + P) d
      (bxor (wittRespBool ((d + P) + twopow k) k)
        (wittRespBool (d + twopow k) k)) :=
  periodic_zcenter_shift_xor_eq_late_witt_xor T P h d k ht hk hset1 hset2

theorem exists_settled_scale_pair_prop (d1 d2 : Nat) :
    ∃ k, ((d1 ≤ k ∧ d2 ≤ k) ∧ SettledAt d1 k) ∧ SettledAt d2 k := by
  obtain ⟨k, h1, h2, hs1, hs2⟩ := exists_settled_scale_pair d1 d2
  exact ⟨k, ⟨⟨h1, h2⟩, hs1⟩, hs2⟩

/-! ### Exact `Nat`-Level 1-Cocycle of `winWitt`, Triality Sector Readouts, and Vacuum-Tree `zcenter` Laws -/

/-- **Exact `Nat`-Level 1-Cocycle Law for the Witt Window Integer `winWitt` Across Dyadic Scales**: for every base time `t0` and scale `k`, the late Witt window integer `winWitt (t0 + 2^k) (2^k)` equals `winWitt t0 (2^(k+1)) ^^^ phiScale k (winWitt t0 (2^k))`. -/
theorem winWitt_scale_cocycle (t0 k : Nat) :
    winWitt (t0 + twopow k) (twopow k) =
      winWitt t0 (twopow (k + 1)) ^^^ phiScale k (winWitt t0 (twopow k)) := by
  have hr1 := row_scale t0 (k + 1)
  have hstep : t0 + twopow (k + 1) = (t0 + twopow k) + twopow k := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep] at hr1
  have hr2 := row_scale (t0 + twopow k) k
  rw [row_scale t0 k, phiScale_xor, phiScale_scale] at hr2
  rw [hr1] at hr2
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun n => n.testBit i) hr2
  simp only [Nat.testBit_xor] at hi ⊢
  revert hi
  cases (phiScale (k + 1) (row t0)).testBit i <;>
    cases (winWitt t0 (twopow (k + 1))).testBit i <;>
    cases (phiScale k (winWitt t0 (twopow k))).testBit i <;>
    cases (winWitt (t0 + twopow k) (twopow k)).testBit i <;> decide

/-- **Triality Sector 2 Readout of `phiScale k y`**: for any `r`, bit `r + 2^(k+1)` of `phiScale k y` is the exact XOR of the three Triality Sectors (`r`, `r + 2^k`, `r + 2^(k+1)`) of `y` at slot `r`. -/
theorem phiScale_testBit_triality (k y r : Nat) :
    (phiScale k y).testBit (r + twopow (k + 1)) =
      bxor (bxor (y.testBit r) (y.testBit (r + twopow k))) (y.testBit (r + twopow (k + 1))) := by
  change (((y ^^^ (y <<< twopow k)) ^^^ (y <<< (twopow k + twopow k)))).testBit
      (r + twopow (k + 1)) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hm1 : decide (r + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
  have hm2 : decide (r + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [hm1, hm2, Bool.true_and, Bool.true_and,
    show r + twopow (k + 1) - twopow k = r + twopow k by omega,
    show r + twopow (k + 1) - (twopow k + twopow k) = r by omega]
  simp only [bxor_eq_xor]
  cases y.testBit (r + twopow (k + 1)) <;>
    cases y.testBit (r + twopow k) <;>
    cases y.testBit r <;> rfl

/-- **Sector-1 Readout of `phiScale k y`**: for any `r < 2^k`, bit `r + 2^k` of `phiScale k y` is the XOR of Sector 0 (`r`) and Sector 1 (`r + 2^k`) of `y` at slot `r`. -/
theorem phiScale_testBit_sector_one (k y r : Nat) (hr : r < twopow k) :
    (phiScale k y).testBit (r + twopow k) =
      bxor (y.testBit r) (y.testBit (r + twopow k)) := by
  change (((y ^^^ (y <<< twopow k)) ^^^ (y <<< (twopow k + twopow k)))).testBit
      (r + twopow k) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have hm1 : decide (r + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have hm2 : decide (r + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [hm1, hm2, Bool.true_and, Bool.false_and, Bool.xor_false,
    show r + twopow k - twopow k = r by omega]
  simp only [bxor_eq_xor]
  cases y.testBit (r + twopow k) <;> cases y.testBit r <;> rfl

/-- **Exact Early-Window Triality Decomposition of Late `winWitt` Sector 1 (`r + 2^(k+1)`)**: for any `t0`, `k`, and `r`, bit `r + 2^(k+1)` of the late Witt window `winWitt (t0 + 2^k) (2^k)` equals bit `r + 2^(k+1)` of `winWitt t0 (2^(k+1))` XORed with all three Triality Sectors of `winWitt t0 (2^k)` at slot `r`. -/
theorem winWitt_late_testBit_triality (t0 k r : Nat) :
    (winWitt (t0 + twopow k) (twopow k)).testBit (r + twopow (k + 1)) =
      bxor ((winWitt t0 (twopow (k + 1))).testBit (r + twopow (k + 1)))
        (bxor (bxor ((winWitt t0 (twopow k)).testBit r)
          ((winWitt t0 (twopow k)).testBit (r + twopow k)))
          ((winWitt t0 (twopow k)).testBit (r + twopow (k + 1)))) := by
  rw [winWitt_scale_cocycle t0 k, Nat.testBit_xor,
    phiScale_testBit_triality k (winWitt t0 (twopow k)) r]
  simp only [bxor_eq_xor]

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_late_testBit_triality`. -/
theorem bit_winWitt_late_triality (t0 k r : Nat) :
    bit (winWitt (t0 + twopow k) (twopow k)) (r + twopow (k + 1)) =
      bton (bxor ((winWitt t0 (twopow (k + 1))).testBit (r + twopow (k + 1)))
        (bxor (bxor ((winWitt t0 (twopow k)).testBit r)
          ((winWitt t0 (twopow k)).testBit (r + twopow k)))
          ((winWitt t0 (twopow k)).testBit (r + twopow (k + 1))))) := by
  rw [bit_eq_bton_testBit, winWitt_late_testBit_triality t0 k r]

/-- **Exact Early-Window Triality Decomposition of the Late Witt Response `wittRespBool (d + 2^k) k`**: for `d ≤ k`, `wittRespBool (d + 2^k) k` equals `wittRespBool d (k + 1)` XORed with the Sector-1 (`wittRespBool d k`) and Sector-2 (`(winWitt d (2^k)).testBit (d + 2^(k+1))`) bits of `winWitt d (2^k)` at slot `d` (with Sector 0 vanishing by `winWitt_testBit_low`). -/
theorem wittRespBool_late_from_early_triality (d k : Nat) (hk : d ≤ k) :
    wittRespBool (d + twopow k) k =
      bxor (wittRespBool d (k + 1))
        (bxor (wittRespBool d k)
          ((winWitt d (twopow k)).testBit (d + twopow (k + 1)))) := by
  have hstep : (d + twopow k) + twopow k = d + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  unfold wittRespBool
  rw [hstep, winWitt_late_testBit_triality d k d,
    winWitt_testBit_low d k d hk]
  simp only [bxor_eq_xor, Bool.false_xor]

/-- **Step 1 Reduction of the Late Witt Term `wittRespBool (d + 2^k) k` under `CenterPeriodic T P`**: for `T ≤ d ≤ k`, `wittRespBool (d + 2^k) k` reduces to the lag-class difference `center (d + lag P (k + 1)) ⊕ center (d + lag P k)` XORed with Triality Sector 2 `(winWitt d (2^k)).testBit (d + 2^(k+1))` of the early Witt window. -/
theorem periodic_late_witt_from_lag_and_sector_two (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    wittRespBool (d + twopow k) k =
      bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        ((winWitt d (twopow k)).testBit (d + twopow (k + 1))) := by
  have hdk : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hdk1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  rw [wittRespBool_late_from_early_triality d k hk,
    periodic_witt_cone T P hP h (k + 1) d ht hdk1,
    periodic_witt_cone T P hP h k d ht hdk]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center d <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;>
    cases (winWitt d (twopow k)).testBit (d + twopow (k + 1)) <;> rfl

/-- **Step 1 Reduction of the Late Masked Column-1 Parity `maskparity (d + 2^k) k` under `CenterPeriodic T P`**: for `T ≤ d ≤ k`, `maskparity (d + 2^k) k` is completely determined by the early left responses `leftresponse d (k + 1) ⊕ leftresponse d k` and the lag-class difference `center (d + lag P (k + 1)) ⊕ center (d + lag P k)`. -/
theorem periodic_late_maskparity_decomp (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Scale.maskparity (d + twopow k) k =
      bxor (bxor (Rule30UOR.Scale.leftresponse d (k + 1))
        (Rule30UOR.Scale.leftresponse d k))
        (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k))) := by
  have hdk : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hdk1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hmc := maskparity_coboundary d k
  have hm0 := Rule30UOR.Scale.periodic_mask_paper T P hP h k d ht hdk
  have hm1 := Rule30UOR.Scale.periodic_mask_paper T P hP h (k + 1) d ht hdk1
  rw [hm0, hm1] at hmc
  revert hmc
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d k <;>
    cases Rule30UOR.Core.center d <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Scale.maskparity (d + twopow k) k <;> decide

/-- **Step 2 Bridge (Left-Response Coboundary Form)**: if `zcenter` has vanishing `P`-shift defect on the settled `leftresponse` coboundary at jointly settled scales `k ≥ d + P`, then `ZCenterPeriodic T P` holds. -/
theorem zcenter_periodic_of_leftresponse_coboundary_shift (T P : Nat)
    (hlr : ∀ d k, T ≤ d → d + P ≤ k → SettledAt d k → SettledAt (d + P) k →
      bxor (bxor (Rule30UOR.Scale.leftresponse (d + P) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + P) k))
        (Rule30UOR.Scale.leftresponse ((d + P) + twopow k) k) =
      bxor (bxor (Rule30UOR.Scale.leftresponse d (k + 1))
        (Rule30UOR.Scale.leftresponse d k))
        (Rule30UOR.Scale.leftresponse (d + twopow k) k)) :
    ZCenterPeriodic T P := by
  intro d ht
  obtain ⟨k, hk1, hk2, hset1, hset2⟩ := exists_settled_scale_pair d (d + P)
  rw [zcenter_eq_leftresponse_coboundary (d + P) k hk2 hset2,
    zcenter_eq_leftresponse_coboundary d k hk1 hset1]
  exact hlr d k ht hk2 hset1 hset2

/-- **Step 2 Bridge (Triality Sector 2 Form)**: if `CenterPeriodic T P` holds and Triality Sector 2 of `winWitt` at the center slot `(winWitt d (2^k)).testBit (d + 2^(k+1))` is invariant under `d ↦ d + P` at jointly settled scales `k ≥ d + P`, then `ZCenterPeriodic T P` holds. -/
theorem zcenter_periodic_of_sector_two_shift (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hs2 : ∀ d k, T ≤ d → d + P ≤ k → SettledAt d k → SettledAt (d + P) k →
      (winWitt (d + P) (twopow k)).testBit ((d + P) + twopow (k + 1)) =
        (winWitt d (twopow k)).testBit (d + twopow (k + 1))) :
    ZCenterPeriodic T P := by
  intro d ht
  obtain ⟨k, _, hk2, hset1, hset2⟩ := exists_settled_scale_pair d (d + P)
  have hxor := periodic_zcenter_shift_xor_eq_sector_two_xor T P h d k ht hk2 hset1 hset2
  rw [hs2 d k ht hk2 hset1 hset2, bxor_eq_xor, bxor_eq_xor, Bool.xor_self] at hxor
  revert hxor
  cases zcenter (d + P) <;> cases zcenter d <;> decide

/-- **Zero-State Diagonal Recurrence (`zcenter_step`)**: at every depth `d`, `zcenter (d + 2) = E d (d + 1) ⊕ (zcenter (d + 1) || E (d + 2) (d + 1))`. -/
theorem zcenter_step (d : Nat) :
    zcenter (d + 2) = bxor (E d (d + 1)) (zcenter (d + 1) || E (d + 2) (d + 1)) := by
  unfold zcenter
  rw [show d + 2 = (d + 1) + 1 by omega, Rule30UOR.Intent.E_step d (d + 1), bxor_eq_xor]

/-- **Zero-State Diagonal Reversibility (`zcenter_back`)**: at every depth `d`, the off-diagonal zero-state bit `E d (d + 1)` is uniquely recovered from `zcenter (d + 1)`, `zcenter (d + 2)`, and `E (d + 2) (d + 1)`. -/
theorem zcenter_back (d : Nat) :
    E d (d + 1) = bxor (zcenter (d + 2)) (zcenter (d + 1) || E (d + 2) (d + 1)) := by
  unfold zcenter
  rw [Rule30UOR.ZeroDiagonals.E_back d (d + 1), bxor_eq_xor]

/-- **Twin Law for `zcenter` Before a Zero Diagonal**: if `j + 2` is a zero diagonal (`IsZeroDiag (j + 2)`), then `zcenter j = E (j + 1) j` and `E j (j + 1) = zcenter (j + 1)`. -/
theorem zcenter_twin_before_zero_diag (j : Nat) (hz : IsZeroDiag (j + 2)) :
    zcenter j = E (j + 1) j ∧ E j (j + 1) = zcenter (j + 1) := by
  unfold zcenter
  exact ⟨Rule30UOR.CompilePoints.twin_before_zero hz j,
    Rule30UOR.CompilePoints.twin_before_zero hz (j + 1)⟩

/-- **Three Steps Past a Zero Diagonal for `zcenter`**: if `z` is a zero diagonal (`IsZeroDiag z`), then `zcenter (z + 3) = !E (z + 1) (z + 2)`. -/
theorem zcenter_three_after_zero_diag (z : Nat) (hz : IsZeroDiag z) :
    zcenter (z + 3) = !E (z + 1) (z + 2) := by
  unfold zcenter
  exact Rule30UOR.CompilePoints.reset_three_after_zero z hz (z + 2)

/-- **Antiperiodic Flip of `zcenter (z + 1)` at a Doubling Zero Diagonal**: if `z` is a zero diagonal where period `P` doubles (`DoublesAt P z`), then shifting time by `P` on diagonal `z + 1` flips `zcenter (z + 1)`: `E (z + 1) ((z + 1) + P) = !zcenter (z + 1)`. -/
theorem zcenter_antiperiodic_after_doubles (P z : Nat) (hz : IsZeroDiag z) (hd : DoublesAt P z) :
    E (z + 1) ((z + 1) + P) = !zcenter (z + 1) := by
  unfold zcenter
  exact Rule30UOR.CompilePoints.antiperiodic_of_doubles P z hz hd (z + 1)

/-- Prop-valued equality of `winWitt` and an integer `n` for paper-facing theorems. -/
def WinWittEq (t0 m n : Nat) : Prop := winWitt t0 m = n

theorem winWitt_scale_cocycle_prop (t0 k : Nat) :
    WinWittEq (t0 + twopow k) (twopow k)
      (winWitt t0 (twopow (k + 1)) ^^^ phiScale k (winWitt t0 (twopow k))) :=
  winWitt_scale_cocycle t0 k

theorem zcenter_step_prop (d : Nat) :
    ZCenterEq (d + 2) (bxor (E d (d + 1)) (zcenter (d + 1) || E (d + 2) (d + 1))) :=
  zcenter_step d

theorem zcenter_three_after_zero_diag_prop (z : Nat) (hz : IsZeroDiag z) :
    ZCenterEq (z + 3) (!E (z + 1) (z + 2)) :=
  zcenter_three_after_zero_diag z hz

/-- Prop-valued equality of `bit (winWitt t0 m) j` and `bton b` for paper-facing theorems. -/
def BitWinWittEq (t0 m j : Nat) (b : Bool) : Prop :=
  bit (winWitt t0 m) j = bton b

theorem bit_winWitt_late_triality_prop (t0 k r : Nat) :
    BitWinWittEq (t0 + twopow k) (twopow k) (r + twopow (k + 1))
      (bxor ((winWitt t0 (twopow (k + 1))).testBit (r + twopow (k + 1)))
        (bxor (bxor ((winWitt t0 (twopow k)).testBit r)
          ((winWitt t0 (twopow k)).testBit (r + twopow k)))
          ((winWitt t0 (twopow k)).testBit (r + twopow (k + 1))))) :=
  bit_winWitt_late_triality t0 k r

theorem wittRespBool_late_from_early_triality_prop (d k : Nat) (hk : d ≤ k) :
    BitWinWittEq d (twopow k) (d + twopow (k + 1))
      (bxor (wittRespBool (d + twopow k) k)
        (bxor (wittRespBool d (k + 1)) (wittRespBool d k))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit]
  have hw := wittRespBool_late_from_early_triality d k hk
  revert hw
  simp only [bxor_eq_xor]
  cases wittRespBool (d + twopow k) k <;>
    cases wittRespBool d (k + 1) <;>
    cases wittRespBool d k <;>
    cases (winWitt d (twopow k)).testBit (d + twopow (k + 1)) <;> decide

theorem periodic_late_witt_from_lag_and_sector_two_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    BitWinWittEq d (twopow k) (d + twopow (k + 1))
      (bxor (wittRespBool (d + twopow k) k)
        (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit]
  have hw := periodic_late_witt_from_lag_and_sector_two T P hP h d k ht hk
  revert hw
  simp only [bxor_eq_xor]
  cases wittRespBool (d + twopow k) k <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;>
    cases (winWitt d (twopow k)).testBit (d + twopow (k + 1)) <;> decide

/-- **Canonical Target on the Universal Settled Structure `Ξ` (`NoZCenterPeriod`)**: the universal settled readout `zcenter` is never eventually periodic for any positive period `Q`. -/
def NoZCenterPeriod : Prop :=
  ∀ T Q, 0 < Q → ¬ ZCenterPeriodic T Q

/-- **Zero-State Transparency Law (`zcenter_toggle_of_transparent`)**: whenever column `-1` of the zero-state is white (`E (d + 1) (d + 1) = false`), the next center diagonal value toggles the previous off-diagonal value by `E d (d + 1)`: `zcenter (d + 2) = E d (d + 1) ⊕ E (d + 2) (d + 1)`. -/
theorem zcenter_toggle_of_transparent (d : Nat) (htrans : zcenter (d + 1) = false) :
    zcenter (d + 2) = bxor (E d (d + 1)) (E (d + 2) (d + 1)) := by
  rw [zcenter_step d, htrans, Bool.false_or]

/-- **Zero-State Reset Law (`zcenter_reset_of_opaque`)**: whenever the previous center diagonal bit is black (`zcenter (d + 1) = true`), the next center diagonal bit forgets `E (d + 2) (d + 1)` and equals `!E d (d + 1)`. -/
theorem zcenter_reset_of_opaque (d : Nat) (hopaq : zcenter (d + 1) = true) :
    zcenter (d + 2) = !E d (d + 1) := by
  rw [zcenter_step d, hopaq, Bool.true_or, bxor_eq_xor, Bool.xor_true]

/-- **Zero-State Left-Of-Black Law for `zcenter` (`zcenter_left_of_black`)**: whenever `zcenter (d + 1) = true` (or `E (d + 2) (d + 1) = true`), `E d (d + 1) = !zcenter (d + 2)`. -/
theorem zcenter_left_of_black (d : Nat) (hb : zcenter (d + 1) = true) :
    E d (d + 1) = !zcenter (d + 2) := by
  rw [zcenter_back d, hb, Bool.true_or, bxor_eq_xor, Bool.xor_true]

/-- **Under `ZCenterPeriodic T Q`, Opaque Reset Transfers Period `Q` to the Off-Diagonal `E d (d + 1)`**: for any `T ≤ d` where both `zcenter (d + 1) = true` and `zcenter ((d + Q) + 1) = true` (which holds automatically from `ZCenterPeriodic T Q` since `T ≤ d + 1`), `E (d + Q) ((d + Q) + 1) = E d (d + 1)`. -/
theorem zcenter_periodic_offdiag_eq_of_black (T Q : Nat) (h : ZCenterPeriodic T Q)
    (d : Nat) (hd : T ≤ d) (hb : zcenter (d + 1) = true) :
    E (d + Q) ((d + Q) + 1) = E d (d + 1) := by
  have hbQ : zcenter ((d + Q) + 1) = true := by
    rw [show (d + Q) + 1 = (d + 1) + Q by omega, h (d + 1) (by omega), hb]
  rw [zcenter_left_of_black (d + Q) hbQ, zcenter_left_of_black d hb,
    show (d + Q) + 2 = (d + 2) + Q by omega, h (d + 2) (by omega)]

/-- **Under `ZCenterPeriodic T Q`, Black Pairs on `zcenter` Force Vanishing Off-Diagonal `E d (d + 1) = false`**: if `ZCenterPeriodic T Q` holds and `zcenter (d + 1) = true` and `zcenter (d + 2) = true`, then `E d (d + 1) = false` and `E (d + Q) ((d + Q) + 1) = false`. -/
theorem zcenter_black_pair_forces_offdiag_false (d : Nat)
    (hb1 : zcenter (d + 1) = true) (hb2 : zcenter (d + 2) = true) :
    E d (d + 1) = false := by
  rw [zcenter_left_of_black d hb1, hb2]; rfl

/-! ### The XOR Channel: Masked Column-1 Parity (`carry60`, `maskcount`, `maskparity`) and `MaskPos` -/

/-- **Single-Step Masked Count**: `maskcount t 1` is the single-step column-1 carry `carry60 t 0 = !center t && cell t 1`. -/
theorem maskcount_one (t : Nat) :
    Rule30UOR.Scale.maskcount t 1 = Rule30UOR.Core.carry60 t 0 := by
  show xor false (Rule30UOR.Core.carry60 (t + 0) 0) = Rule30UOR.Core.carry60 t 0
  rw [Bool.false_xor, Nat.add_zero]

/-- **Scale-0 Masked Parity**: at scale `k = 0` (`2^0 = 1`), `maskparity t 0 = carry60 t 0`. -/
theorem maskparity_zero (t : Nat) :
    Rule30UOR.Scale.maskparity t 0 = Rule30UOR.Core.carry60 t 0 :=
  maskcount_one t

/-- **Shift-by-`s` Difference of `maskcount`**: shifting the start of a length-`n` window by `s` changes `maskcount` by `maskcount (t + n) s ⊕ maskcount t s`. -/
theorem maskcount_shift_diff (t s n : Nat) :
    bxor (Rule30UOR.Scale.maskcount (t + s) n) (Rule30UOR.Scale.maskcount t n) =
      bxor (Rule30UOR.Scale.maskcount (t + n) s) (Rule30UOR.Scale.maskcount t s) := by
  have h1 := maskcount_add t s n
  have h2 := maskcount_add t n s
  rw [show s + n = n + s by omega] at h1
  rw [h2] at h1
  revert h1
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.maskcount t n <;>
    cases Rule30UOR.Scale.maskcount (t + n) s <;>
    cases Rule30UOR.Scale.maskcount t s <;>
    cases Rule30UOR.Scale.maskcount (t + s) n <;> decide

/-- **Shift-by-`s` Difference of `maskparity`**: shifting the start of a scale-`k` dyadic window by `s` changes `maskparity t k` by `maskcount (t + 2^k) s ⊕ maskcount t s`. -/
theorem maskparity_shift_diff (t s k : Nat) :
    bxor (Rule30UOR.Scale.maskparity (t + s) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Scale.maskcount (t + twopow k) s) (Rule30UOR.Scale.maskcount t s) :=
  maskcount_shift_diff t s (twopow k)

/-- **1-Step Discrete Derivative of `maskcount`**: stepping `t ↦ t + 1` in `maskcount t n` extracts the exact `n`-step jump `carry60 (t + n) 0 ⊕ carry60 t 0` along the XOR channel at position `0`. -/
theorem maskcount_step_diff (t n : Nat) :
    bxor (Rule30UOR.Scale.maskcount (t + 1) n) (Rule30UOR.Scale.maskcount t n) =
      bxor (Rule30UOR.Core.carry60 (t + n) 0) (Rule30UOR.Core.carry60 t 0) := by
  rw [maskcount_shift_diff t 1 n, maskcount_one (t + n), maskcount_one t]

/-- **1-Step Discrete Derivative of `maskparity`**: stepping `t ↦ t + 1` in `maskparity t k` extracts the exact dyadic jump `carry60 (t + 2^k) 0 ⊕ carry60 t 0` along the XOR channel at position `0`. -/
theorem maskparity_step_diff (t k : Nat) :
    bxor (Rule30UOR.Scale.maskparity (t + 1) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Core.carry60 (t + twopow k) 0) (Rule30UOR.Core.carry60 t 0) :=
  maskcount_step_diff t (twopow k)

/-- The core's center column equals `rdiag t t`. -/
theorem core_center_eq_rdiag (t : Nat) : Rule30UOR.Core.center t = rdiag t t :=
  core_center_eq_rcenter t

/-- **Right-System Readout of `carry60 (s + 1) 0`**: the position-`0` carry at time `s + 1` is `(!rdiag (s + 1) (s + 1)) && rdiag s (s + 1)`. -/
theorem carry60_succ_zero_eq_rdiag (s : Nat) :
    Rule30UOR.Core.carry60 (s + 1) 0 =
      ((!rdiag (s + 1) (s + 1)) && rdiag s (s + 1)) := by
  show (!Rule30UOR.Core.cell (s + 1) 0 && Rule30UOR.Core.cell (s + 1) (LexLeanRuntime.subtract 0 (-1))) =
    ((!rdiag (s + 1) (s + 1)) && rdiag s (s + 1))
  rw [Rule30UOR.Scale.sub_neg_one, show (0 : Int) + 1 = 1 by rfl,
    show Rule30UOR.Core.cell (s + 1) 0 = rdiag (s + 1) (s + 1) from core_center_eq_rdiag (s + 1),
    show Rule30UOR.Core.cell (s + 1) 1 = rdiag s (s + 1) by
      rw [Rule30UOR.Scale.cell_eq_kit, Rule30UOR.Right.col1_readout]]

/-- **`MaskedPer T P` is Exactly `P`-Periodicity of the XOR Channel `carry60 (s + 1) 0`**: under `CenterPeriodic T P`, `Rule30UOR.Right.MaskedPer T P` holds iff `carry60 ((s + 1) + P) 0 = carry60 (s + 1) 0` for all `s ≥ T`. -/
theorem maskedPer_iff_carry60_periodic (T P : Nat) (h : Rule30UOR.Scale.CenterPeriodic T P) :
    Rule30UOR.Right.MaskedPer T P ↔
      ∀ s, T ≤ s → Rule30UOR.Core.carry60 ((s + 1) + P) 0 = Rule30UOR.Core.carry60 (s + 1) 0 := by
  constructor
  · intro hm s hs
    have hc : rdiag ((s + 1) + P) ((s + 1) + P) = rdiag (s + 1) (s + 1) := by
      rw [← core_center_eq_rdiag ((s + 1) + P), ← core_center_eq_rdiag (s + 1)]
      exact h (s + 1) (by omega)
    rw [show (s + 1) + P = (s + P) + 1 by omega] at hc ⊢
    rw [carry60_succ_zero_eq_rdiag (s + P), carry60_succ_zero_eq_rdiag s, hc]
    cases hcent : rdiag (s + 1) (s + 1)
    · simp only [Bool.not_false, Bool.true_and]
      rw [show (s + P) + 1 = s + P + 1 by omega]
      exact hm s hs hcent
    · simp only [Bool.not_true, Bool.false_and]
  · intro hcar s hs hcent
    have hcs := hcar s hs
    have hc : rdiag ((s + P) + 1) ((s + P) + 1) = rdiag (s + 1) (s + 1) := by
      rw [show (s + P) + 1 = (s + 1) + P by omega,
        ← core_center_eq_rdiag ((s + 1) + P), ← core_center_eq_rdiag (s + 1)]
      exact h (s + 1) (by omega)
    rw [show (s + 1) + P = (s + P) + 1 by omega,
      carry60_succ_zero_eq_rdiag (s + P), carry60_succ_zero_eq_rdiag s,
      hc, hcent] at hcs
    simpa [show (s + P) + 1 = s + P + 1 by omega] using hcs

/-- **Under `MaskedPer T P`, `maskcount` is `P`-Periodic from `T + 1`**: if `CenterPeriodic T P` and `MaskedPer T P` hold, then for all `t ≥ T + 1` and all `n`, `maskcount (t + P) n = maskcount t n`. -/
theorem maskcount_periodic_of_maskedPer (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P) (hm : Rule30UOR.Right.MaskedPer T P)
    (t : Nat) (ht : T + 1 ≤ t) :
    ∀ n : Nat, Rule30UOR.Scale.maskcount (t + P) n = Rule30UOR.Scale.maskcount t n
  | 0 => rfl
  | n + 1 => by
    show xor (Rule30UOR.Scale.maskcount (t + P) n) (Rule30UOR.Core.carry60 ((t + P) + n) 0) =
      xor (Rule30UOR.Scale.maskcount t n) (Rule30UOR.Core.carry60 (t + n) 0)
    rw [maskcount_periodic_of_maskedPer T P h hm t ht n]
    have hcar := (maskedPer_iff_carry60_periodic T P h).mp hm (t + n - 1) (by omega)
    have h1 : (t + n - 1) + 1 = t + n := by omega
    rw [h1] at hcar
    rw [show (t + P) + n = (t + n) + P by omega, hcar]

/-- **Under `MaskedPer T P`, `maskparity` is `P`-Periodic from `T + 1`**: if `CenterPeriodic T P` and `MaskedPer T P` hold, then for all `t ≥ T + 1` and all scales `k`, `maskparity (t + P) k = maskparity t k`. -/
theorem maskparity_periodic_of_maskedPer (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P) (hm : Rule30UOR.Right.MaskedPer T P)
    (t k : Nat) (ht : T + 1 ≤ t) :
    Rule30UOR.Scale.maskparity (t + P) k = Rule30UOR.Scale.maskparity t k :=
  maskcount_periodic_of_maskedPer T P h hm t ht (twopow k)

/-- **Equivalence of `MaskedPer T P` and `P`-Periodicity of `maskparity · 0`**: under `CenterPeriodic T P`, `MaskedPer T P` holds iff `maskparity ((s + 1) + P) 0 = maskparity (s + 1) 0` for all `s ≥ T`. -/
theorem maskedPer_iff_maskparity_zero_periodic (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P) :
    Rule30UOR.Right.MaskedPer T P ↔
      ∀ s, T ≤ s → Rule30UOR.Scale.maskparity ((s + 1) + P) 0 = Rule30UOR.Scale.maskparity (s + 1) 0 := by
  simp only [maskparity_zero]
  exact maskedPer_iff_carry60_periodic T P h

/-- **Under `CenterPeriodic T P`, Inside-the-Cone `P`-Shift of `maskparity` Equals `P`-Shift of `leftresponse`**: for `T ≤ t` and `t + P < 2^k`, the lag terms cancel between `t` and `t + P`, locking `maskparity (t + P) k ⊕ maskparity t k = leftresponse (t + P) k ⊕ leftresponse t k`. -/
theorem periodic_maskparity_shift_P_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P < twopow k) :
    bxor (Rule30UOR.Scale.maskparity (t + P) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Scale.leftresponse (t + P) k) (Rule30UOR.Scale.leftresponse t k) := by
  have ht_k : t < twopow k := by omega
  have htP_T : T ≤ t + P := by omega
  rw [Rule30UOR.Scale.periodic_mask_paper T P hP h k (t + P) htP_T htP,
    Rule30UOR.Scale.periodic_mask_paper T P hP h k t ht ht_k,
    show (t + P) + Rule30UOR.Scale.lag P k = (t + Rule30UOR.Scale.lag P k) + P by omega,
    h (t + Rule30UOR.Scale.lag P k) (by omega),
    h t ht]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (t + P) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;>
    cases Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center t <;> rfl

/-- **Under `CenterPeriodic T P`, Inside-the-Cone Dyadic Jump of `maskcount · P` Equals `P`-Shift of `leftresponse`**: for `T ≤ t` and `t + P < 2^k`, `maskcount (t + 2^k) P ⊕ maskcount t P = leftresponse (t + P) k ⊕ leftresponse t k`. -/
theorem periodic_maskcount_P_dyadic_jump_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P < twopow k) :
    bxor (Rule30UOR.Scale.maskcount (t + twopow k) P) (Rule30UOR.Scale.maskcount t P) =
      bxor (Rule30UOR.Scale.leftresponse (t + P) k) (Rule30UOR.Scale.leftresponse t k) := by
  rw [← maskparity_shift_diff t P k]
  exact periodic_maskparity_shift_P_cone T P hP h t k ht htP

/-- **Under `CenterPeriodic T P`, Inside-the-Cone Dyadic Jump of `carry60 · 0`**: for `T ≤ t` and `t + 1 < 2^k`, the dyadic jump `carry60 (t + 2^k) 0 ⊕ carry60 t 0` along the XOR channel equals the 1-step difference of `leftresponse · k` XORed with the 1-step differences of `center` at lag `2^k mod P` and lag `0`. -/
theorem periodic_carry60_dyadic_jump_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (hk : t + 1 < twopow k) :
    bxor (Rule30UOR.Core.carry60 (t + twopow k) 0) (Rule30UOR.Core.carry60 t 0) =
      bxor (bxor (Rule30UOR.Scale.leftresponse (t + 1) k) (Rule30UOR.Scale.leftresponse t k))
        (bxor (bxor (Rule30UOR.Core.center ((t + 1) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k)))
          (bxor (Rule30UOR.Core.center (t + 1)) (Rule30UOR.Core.center t))) := by
  have ht_k : t < twopow k := by omega
  have ht1_T : T ≤ t + 1 := by omega
  rw [← maskparity_step_diff t k,
    Rule30UOR.Scale.periodic_mask_paper T P hP h k (t + 1) ht1_T hk,
    Rule30UOR.Scale.periodic_mask_paper T P hP h k t ht ht_k]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (t + 1) k <;>
    cases Rule30UOR.Scale.leftresponse t k <;>
    cases Rule30UOR.Core.center ((t + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (t + 1) <;>
    cases Rule30UOR.Core.center t <;> rfl

/-- Helper: `bxor (bxor a b) (bxor c d) = bxor (bxor a c) (bxor b d)`. -/
theorem bxor_four_swap (a b c d : Bool) :
    bxor (bxor a b) (bxor c d) = bxor (bxor a c) (bxor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- **Under `CenterPeriodic T P`, Inside-the-Cone Dyadic Jump of the `P`-Periodicity Defect of `carry60 · 0`**: for `T ≤ t` and `t + P + 1 < 2^k`, all center and lag terms cancel between `t` and `t + P`, so the `P`-periodicity defect `carry60 (s + P) 0 ⊕ carry60 s 0` jumps across `2^k` purely by the second difference of `leftresponse · k`. -/
theorem periodic_carry60_defect_dyadic_jump_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P + 1 < twopow k) :
    bxor (bxor (Rule30UOR.Core.carry60 ((t + P) + twopow k) 0)
      (Rule30UOR.Core.carry60 (t + twopow k) 0))
      (bxor (Rule30UOR.Core.carry60 (t + P) 0) (Rule30UOR.Core.carry60 t 0)) =
      bxor (bxor (Rule30UOR.Scale.leftresponse ((t + P) + 1) k)
        (Rule30UOR.Scale.leftresponse (t + 1) k))
        (bxor (Rule30UOR.Scale.leftresponse (t + P) k)
          (Rule30UOR.Scale.leftresponse t k)) := by
  have h1 := maskparity_step_diff (t + P) k
  have h2 := maskparity_step_diff t k
  rw [bxor_four_swap, ← h1, ← h2, bxor_four_swap]
  have h3 := periodic_maskparity_shift_P_cone T P hP h (t + 1) k (by omega)
    (by rw [show (t + 1) + P = t + P + 1 by omega]; exact htP)
  have h4 := periodic_maskparity_shift_P_cone T P hP h t k ht (by omega)
  rw [show (t + 1) + P = (t + P) + 1 by omega] at h3
  rw [h3, h4]

/-- **Under `CenterPeriodic T P`, Outside-the-Cone `P`-Shift of Late `maskparity (d + 2^k) k`**: for `T ≤ d` and `d + P ≤ k`, the center lag terms in Theorem 9.103 (`periodic_late_maskparity_decomp`) cancel identically between `d` and `d + P`, locking `maskparity (d + P + 2^k) k ⊕ maskparity (d + 2^k) k` purely to the early `leftresponse` differences at scales `k + 1` and `k`. -/
theorem periodic_late_maskparity_shift_P (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P ≤ k) :
    bxor (Rule30UOR.Scale.maskparity ((d + P) + twopow k) k)
      (Rule30UOR.Scale.maskparity (d + twopow k) k) =
      bxor (bxor (Rule30UOR.Scale.leftresponse (d + P) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + P) k))
        (bxor (Rule30UOR.Scale.leftresponse d (k + 1))
          (Rule30UOR.Scale.leftresponse d k)) := by
  have hd_k : d ≤ k := by omega
  have hdP_T : T ≤ d + P := by omega
  rw [periodic_late_maskparity_decomp T P hP h (d + P) k hdP_T hk,
    periodic_late_maskparity_decomp T P hP h d k ht hd_k,
    show (d + P) + Rule30UOR.Scale.lag P (k + 1) = (d + Rule30UOR.Scale.lag P (k + 1)) + P by omega,
    show (d + P) + Rule30UOR.Scale.lag P k = (d + Rule30UOR.Scale.lag P k) + P by omega,
    h (d + Rule30UOR.Scale.lag P (k + 1)) (by omega),
    h (d + Rule30UOR.Scale.lag P k) (by omega)]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (d + P) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + P) k <;>
    cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d k <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;> rfl

/-- **Under `CenterPeriodic T P`, Outside-the-Cone Dyadic Jump of `carry60 · 0` Across `[d + 2^k, d + 2^(k+1)]`**: for `T ≤ d` and `d + 1 ≤ k`, differentiating Theorem 9.103 (`periodic_late_maskparity_decomp`) with respect to `d ↦ d + 1` expresses `carry60 (d + 2^(k+1)) 0 ⊕ carry60 (d + 2^k) 0` purely in terms of the inside-the-cone `leftresponse` and `center` differences at `d` and `d + 1`. -/
theorem periodic_late_carry60_dyadic_jump (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + 1 ≤ k) :
    bxor (Rule30UOR.Core.carry60 (d + twopow (k + 1)) 0)
      (Rule30UOR.Core.carry60 (d + twopow k) 0) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 1) k))
        (bxor (Rule30UOR.Scale.leftresponse d (k + 1))
          (Rule30UOR.Scale.leftresponse d k)))
        (bxor (bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)))
          (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))) := by
  have hd_k : d ≤ k := by omega
  have hd1_T : T ≤ d + 1 := by omega
  have hstep1 : d + twopow (k + 1) = (d + twopow k) + twopow k := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  have hstep2 : (d + twopow k) + 1 = (d + 1) + twopow k := by omega
  rw [hstep1, ← maskparity_step_diff (d + twopow k) k, hstep2,
    periodic_late_maskparity_decomp T P hP h (d + 1) k hd1_T hk,
    periodic_late_maskparity_decomp T P hP h d k ht hd_k]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (d + 1) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + 1) k <;>
    cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d k <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;> rfl

/-- **Under `CenterPeriodic T P`, Outside-the-Cone Late `leftresponse` Decomposition**: for `T ≤ d ≤ k`, combining `ldiag_eq_leftresponse_coboundary` with Theorem 9.103 (`periodic_late_maskparity_decomp`) expresses the late left response `leftresponse (d + 2^k) k` as `ldiag d (d + 2^k)` XORed with `maskparity (d + 2^k) k` and the center lag difference `center (d + lag P (k + 1)) ⊕ center (d + lag P k)`. -/
theorem periodic_late_leftresponse_unsettled_decomp (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) :
    Rule30UOR.Scale.leftresponse (d + twopow k) k =
      bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (bxor (ldiag d (d + twopow k))
          (Rule30UOR.Scale.maskparity (d + twopow k) k)) := by
  have hl := ldiag_eq_leftresponse_coboundary d k hk
  have hm := periodic_late_maskparity_decomp T P hP h d k ht hk
  revert hl hm
  simp only [bxor_eq_xor]
  cases ldiag d (d + twopow k) <;>
    cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d k <;>
    cases Rule30UOR.Scale.leftresponse (d + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity (d + twopow k) k <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k) <;> decide

/-- **Under `CenterPeriodic T P`, Settled Late `leftresponse` Decomposition**: for `T ≤ d ≤ k` and `SettledAt d k`, `zcenter d` equals `leftresponse (d + 2^k) k ⊕ maskparity (d + 2^k) k ⊕ center (d + lag P (k + 1)) ⊕ center (d + lag P k)`. -/
theorem periodic_zcenter_from_lag_and_late_left_mask (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) (hset : SettledAt d k) :
    zcenter d =
      bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (bxor (Rule30UOR.Scale.leftresponse (d + twopow k) k)
          (Rule30UOR.Scale.maskparity (d + twopow k) k)) := by
  rw [periodic_zcenter_from_lag_and_late_response T P hP h d k ht hk hset,
    Rule30UOR.Scale.split_paper (d + twopow k) k]

/-- **Under `CenterPeriodic T P`, Outside-the-Cone Dyadic Jump of the `P`-Periodicity Defect of `carry60 · 0`**: for `T ≤ d` and `d + P + 1 ≤ k`, all center and lag terms cancel between `d` and `d + P`, so the `P`-periodicity defect `carry60 (s + P) 0 ⊕ carry60 s 0` jumps across `[d + 2^k, d + 2^(k+1)]` purely by the second differences of `leftresponse` at scales `k + 1` and `k`. -/
theorem periodic_late_carry60_defect_dyadic_jump (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P + 1 ≤ k) :
    bxor (bxor (Rule30UOR.Core.carry60 ((d + P) + twopow (k + 1)) 0)
      (Rule30UOR.Core.carry60 (d + twopow (k + 1)) 0))
      (bxor (Rule30UOR.Core.carry60 ((d + P) + twopow k) 0)
        (Rule30UOR.Core.carry60 (d + twopow k) 0)) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 1) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 1) (k + 1)))
        (bxor (Rule30UOR.Scale.leftresponse (d + P) (k + 1))
          (Rule30UOR.Scale.leftresponse d (k + 1))))
        (bxor (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 1) k)
          (Rule30UOR.Scale.leftresponse (d + 1) k))
          (bxor (Rule30UOR.Scale.leftresponse (d + P) k)
            (Rule30UOR.Scale.leftresponse d k))) := by
  have hstep1 : (d + P) + twopow (k + 1) = ((d + P) + twopow k) + twopow k := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  have hstep2 : d + twopow (k + 1) = (d + twopow k) + twopow k := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  have h1 := maskparity_step_diff ((d + P) + twopow k) k
  have h2 := maskparity_step_diff (d + twopow k) k
  rw [← hstep1, show ((d + P) + twopow k) + 1 = ((d + P) + 1) + twopow k by omega] at h1
  rw [← hstep2, show (d + twopow k) + 1 = (d + 1) + twopow k by omega] at h2
  rw [bxor_four_swap, ← h1, ← h2, bxor_four_swap]
  have h3 := periodic_late_maskparity_shift_P T P hP h (d + 1) k (by omega)
    (by rw [show (d + 1) + P = d + P + 1 by omega]; exact hk)
  have h4 := periodic_late_maskparity_shift_P T P hP h d k ht (by omega)
  rw [show (d + 1) + P = (d + P) + 1 by omega] at h3
  rw [h3, h4]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse ((d + P) + 1) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse ((d + P) + 1) k <;>
    cases Rule30UOR.Scale.leftresponse (d + 1) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + 1) k <;>
    cases Rule30UOR.Scale.leftresponse (d + P) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + P) k <;>
    cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d k <;> rfl

/-- **Scale-0 `leftresponse` Vanishes Identically**: at scale `k = 0` (`2^0 = 1`), `leftresponse t 0 = false` for all `t`, because `carryL` vanishes at `p = 0` and `leftwin t 0` is identically `false`. -/
theorem leftresponse_zero (t : Nat) :
    Rule30UOR.Scale.leftresponse t 0 = false := by
  show xor (xor false false) (if (0 : Int) < 0 then Rule30UOR.Core.carry60 (t + 0) 0 else false) = false
  rfl

/-- **Scale-0 `response` Equals `maskparity t 0 = carry60 t 0`**: at scale `k = 0` (`2^0 = 1`), the Rule-60 window response `response t 0` equals `maskparity t 0` (`= carry60 t 0`). -/
theorem response_zero_eq_maskparity_zero (t : Nat) :
    Rule30UOR.Scale.response t 0 = Rule30UOR.Scale.maskparity t 0 := by
  rw [Rule30UOR.Scale.split_paper t 0, leftresponse_zero t]
  show bxor false (Rule30UOR.Scale.maskparity t 0) = Rule30UOR.Scale.maskparity t 0
  cases Rule30UOR.Scale.maskparity t 0 <;> rfl

/-- **Scale-0 `response` Equals `carry60 t 0`**: at scale `k = 0` (`2^0 = 1`), `response t 0 = carry60 t 0`. -/
theorem response_zero_eq_carry60 (t : Nat) :
    Rule30UOR.Scale.response t 0 = Rule30UOR.Core.carry60 t 0 := by
  rw [response_zero_eq_maskparity_zero t, maskparity_zero t]

/-- **1-Step Rule-60 Center Decomposition**: at every time `t`, `center (t + 1) = center t ⊕ cell t (-1) ⊕ carry60 t 0`. -/
theorem center_step_eq_carry60 (t : Nat) :
    Rule30UOR.Core.center (t + 1) =
      bxor (bxor (Rule30UOR.Core.center t) (Rule30UOR.Core.cell t (-1)))
        (Rule30UOR.Core.carry60 t 0) := by
  have hs := Rule30UOR.Scale.scale_center_paper t 0
  rw [show twopow 0 = 1 from rfl,
    show Rule30UOR.Scale.negpow 0 = -1 from rfl,
    response_zero_eq_carry60 t] at hs
  exact hs

/-- **Under `CenterPeriodic T P`, `P`-Periodicity of `carry60 · 0` Equals `P`-Periodicity of Column `-1`**: for `0 < P` and `T ≤ t`, `carry60 (t + P) 0 ⊕ carry60 t 0 = cell (t + P) (-1) ⊕ cell t (-1)`. Consequently, `MaskedPer T P` and `LeftPer T P` share the exact same `P`-periodicity defect at every step `t ≥ T + 1`! -/
theorem periodic_carry60_defect_eq_colm1_defect (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t : Nat) (ht : T ≤ t) :
    bxor (Rule30UOR.Core.carry60 (t + P) 0) (Rule30UOR.Core.carry60 t 0) =
      bxor (Rule30UOR.Core.cell (t + P) (-1)) (Rule30UOR.Core.cell t (-1)) := by
  have hs1 := Rule30UOR.Scale.periodic_scale_paper T P hP h 0 t ht
  have hs2 := Rule30UOR.Scale.periodic_scale_paper T P hP h 0 (t + P) (by omega)
  rw [show Rule30UOR.Scale.negpow 0 = -1 from rfl, response_zero_eq_carry60] at hs1 hs2
  rw [show (t + P) + Rule30UOR.Scale.lag P 0 = (t + Rule30UOR.Scale.lag P 0) + P by omega,
    h (t + Rule30UOR.Scale.lag P 0) (by omega),
    h t ht, ← hs1] at hs2
  revert hs2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.cell (t + P) (-1) <;>
    cases Rule30UOR.Core.carry60 (t + P) 0 <;>
    cases Rule30UOR.Core.cell t (-1) <;>
    cases Rule30UOR.Core.carry60 t 0 <;> decide

/-- **Pointwise Equivalence of `MaskedPer T P` and `LeftPer (T + 1) P` under `CenterPeriodic T P`**: because `carry60 s 0 ⊕ cell s (-1) = center (s + 1) ⊕ center s`, under `CenterPeriodic T P` (`0 < P`), `MaskedPer T P` holds iff `cell ((s + 1) + P) (-1) = cell (s + 1) (-1)` for all `s ≥ T`. -/
theorem maskedPer_iff_colm1_periodic (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P) :
    Rule30UOR.Right.MaskedPer T P ↔
      ∀ s, T ≤ s →
        Rule30UOR.Core.cell ((s + 1) + P) (-1) = Rule30UOR.Core.cell (s + 1) (-1) := by
  rw [maskedPer_iff_carry60_periodic T P h]
  constructor
  · intro hm s hs
    have hd := periodic_carry60_defect_eq_colm1_defect T P hP h (s + 1) (by omega)
    rw [hm s hs, bxor_eq_xor, Bool.xor_self] at hd
    revert hd
    simp only [bxor_eq_xor]
    cases Rule30UOR.Core.cell ((s + 1) + P) (-1) <;>
      cases Rule30UOR.Core.cell (s + 1) (-1) <;> decide
  · intro hc s hs
    have hd := periodic_carry60_defect_eq_colm1_defect T P hP h (s + 1) (by omega)
    rw [hc s hs, bxor_eq_xor, bxor_eq_xor, Bool.xor_self] at hd
    revert hd
    cases Rule30UOR.Core.carry60 ((s + 1) + P) 0 <;>
      cases Rule30UOR.Core.carry60 (s + 1) 0 <;> decide

/-- Forward implication of `maskedPer_iff_carry60_periodic` for paper-facing theorems. -/
theorem carry60_periodic_of_maskedPer (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P) (hm : Rule30UOR.Right.MaskedPer T P)
    (s : Nat) (hs : T ≤ s) :
    Rule30UOR.Core.carry60 ((s + 1) + P) 0 = Rule30UOR.Core.carry60 (s + 1) 0 :=
  (maskedPer_iff_carry60_periodic T P h).mp hm s hs

/-- Backward implication of `maskedPer_iff_carry60_periodic` for paper-facing theorems. -/
theorem maskedPer_of_carry60_periodic (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hcar : ∀ s, T ≤ s → Rule30UOR.Core.carry60 ((s + 1) + P) 0 = Rule30UOR.Core.carry60 (s + 1) 0) :
    Rule30UOR.Right.MaskedPer T P :=
  (maskedPer_iff_carry60_periodic T P h).mpr hcar

/-- Prop-valued wrapper for `periodic_zcenter_from_lag_and_late_left_mask` for paper-facing theorems. -/
theorem periodic_zcenter_from_lag_and_late_left_mask_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d ≤ k) (hset : SettledAt d k) :
    ZCenterEq d
      (bxor (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))
        (bxor (Rule30UOR.Scale.leftresponse (d + twopow k) k)
          (Rule30UOR.Scale.maskparity (d + twopow k) k))) :=
  periodic_zcenter_from_lag_and_late_left_mask T P hP h d k ht hk hset

/-- **Paper-facing 1-Step Discrete Derivative of `maskparity`**: `maskparity (t + 1) k ⊕ maskparity t k = maskparity (t + 2^k) 0 ⊕ maskparity t 0`. -/
theorem maskparity_step_diff_zero (t k : Nat) :
    bxor (Rule30UOR.Scale.maskparity (t + 1) k) (Rule30UOR.Scale.maskparity t k) =
      bxor (Rule30UOR.Scale.maskparity (t + twopow k) 0) (Rule30UOR.Scale.maskparity t 0) := by
  rw [maskparity_step_diff t k, maskparity_zero (t + twopow k), maskparity_zero t]

/-- **Paper-facing Right-System Readout of `maskparity (s + 1) 0`**: `maskparity (s + 1) 0 = (!rdiag (s + 1) (s + 1)) && rdiag s (s + 1)`. -/
theorem maskparity_succ_zero_eq_rdiag (s : Nat) :
    Rule30UOR.Scale.maskparity (s + 1) 0 =
      ((!rdiag (s + 1) (s + 1)) && rdiag s (s + 1)) := by
  rw [maskparity_zero (s + 1), carry60_succ_zero_eq_rdiag s]

/-- Prop-valued predicate for `P`-periodicity of `maskparity (s + 1) 0` from `s ≥ T`. -/
def MaskParityZeroPeriodic (T P : Nat) : Prop :=
  ∀ s, T ≤ s → Rule30UOR.Scale.maskparity ((s + 1) + P) 0 = Rule30UOR.Scale.maskparity (s + 1) 0

/-- **Paper-facing Forward Implication of `maskedPer_iff_maskparity_zero_periodic`**. -/
theorem maskparity_zero_periodic_of_maskedPer (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P) (hm : Rule30UOR.Right.MaskedPer T P) :
    MaskParityZeroPeriodic T P :=
  (maskedPer_iff_maskparity_zero_periodic T P h).mp hm

/-- **Paper-facing Backward Implication of `maskedPer_iff_maskparity_zero_periodic`**. -/
theorem maskedPer_of_maskparity_zero_periodic (T P : Nat)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (hmp : MaskParityZeroPeriodic T P) :
    Rule30UOR.Right.MaskedPer T P :=
  (maskedPer_iff_maskparity_zero_periodic T P h).mpr hmp

/-- **Paper-facing Inside-the-Cone Dyadic Jump of `maskparity · 0`**: for `T ≤ t` and `t + 1 < 2^k`, `maskparity (t + 2^k) 0 ⊕ maskparity t 0` equals the 1-step difference of `leftresponse · k` XORed with the 1-step differences of `center` at lag `2^k mod P` and lag `0`. -/
theorem periodic_maskparity_zero_dyadic_jump_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (hk : t + 1 < twopow k) :
    bxor (Rule30UOR.Scale.maskparity (t + twopow k) 0) (Rule30UOR.Scale.maskparity t 0) =
      bxor (bxor (Rule30UOR.Scale.leftresponse (t + 1) k) (Rule30UOR.Scale.leftresponse t k))
        (bxor (bxor (Rule30UOR.Core.center ((t + 1) + Rule30UOR.Scale.lag P k))
          (Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k)))
          (bxor (Rule30UOR.Core.center (t + 1)) (Rule30UOR.Core.center t))) := by
  rw [maskparity_zero (t + twopow k), maskparity_zero t]
  exact periodic_carry60_dyadic_jump_cone T P hP h t k ht hk

/-- **Paper-facing Inside-the-Cone Dyadic Jump of the `P`-Periodicity Defect of `maskparity · 0`**: for `T ≤ t` and `t + P + 1 < 2^k`, the `P`-periodicity defect `maskparity (s + P) 0 ⊕ maskparity s 0` jumps across `2^k` purely by the second difference of `leftresponse · k`. -/
theorem periodic_maskparity_zero_defect_dyadic_jump_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t k : Nat) (ht : T ≤ t) (htP : t + P + 1 < twopow k) :
    bxor (bxor (Rule30UOR.Scale.maskparity ((t + P) + twopow k) 0)
      (Rule30UOR.Scale.maskparity (t + twopow k) 0))
      (bxor (Rule30UOR.Scale.maskparity (t + P) 0) (Rule30UOR.Scale.maskparity t 0)) =
      bxor (bxor (Rule30UOR.Scale.leftresponse ((t + P) + 1) k)
        (Rule30UOR.Scale.leftresponse (t + 1) k))
        (bxor (Rule30UOR.Scale.leftresponse (t + P) k)
          (Rule30UOR.Scale.leftresponse t k)) := by
  simp only [maskparity_zero]
  exact periodic_carry60_defect_dyadic_jump_cone T P hP h t k ht htP

/-- **Paper-facing Outside-the-Cone Dyadic Jump of `maskparity · 0` Across `[d + 2^k, d + 2^(k+1)]`**. -/
theorem periodic_late_maskparity_zero_dyadic_jump (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + 1 ≤ k) :
    bxor (Rule30UOR.Scale.maskparity (d + twopow (k + 1)) 0)
      (Rule30UOR.Scale.maskparity (d + twopow k) 0) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 1) k))
        (bxor (Rule30UOR.Scale.leftresponse d (k + 1))
          (Rule30UOR.Scale.leftresponse d k)))
        (bxor (bxor (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k)))
          (bxor (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P (k + 1)))
            (Rule30UOR.Core.center (d + Rule30UOR.Scale.lag P k)))) := by
  simp only [maskparity_zero]
  exact periodic_late_carry60_dyadic_jump T P hP h d k ht hk

/-- **Paper-facing Outside-the-Cone Dyadic Jump of the `P`-Periodicity Defect of `maskparity · 0`**. -/
theorem periodic_late_maskparity_zero_defect_dyadic_jump (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d) (hk : d + P + 1 ≤ k) :
    bxor (bxor (Rule30UOR.Scale.maskparity ((d + P) + twopow (k + 1)) 0)
      (Rule30UOR.Scale.maskparity (d + twopow (k + 1)) 0))
      (bxor (Rule30UOR.Scale.maskparity ((d + P) + twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + twopow k) 0)) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 1) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 1) (k + 1)))
        (bxor (Rule30UOR.Scale.leftresponse (d + P) (k + 1))
          (Rule30UOR.Scale.leftresponse d (k + 1))))
        (bxor (bxor (Rule30UOR.Scale.leftresponse ((d + P) + 1) k)
          (Rule30UOR.Scale.leftresponse (d + 1) k))
          (bxor (Rule30UOR.Scale.leftresponse (d + P) k)
            (Rule30UOR.Scale.leftresponse d k))) := by
  simp only [maskparity_zero]
  exact periodic_late_carry60_defect_dyadic_jump T P hP h d k ht hk

/-- **Paper-facing Equality of the `P`-Periodicity Defects of `maskparity · 0` and Column `-1` (`cell · (negpow 0)`)**: for `0 < P` and `T ≤ t`, `maskparity (t + P) 0 ⊕ maskparity t 0 = cell (t + P) (negpow 0) ⊕ cell t (negpow 0)`. -/
theorem periodic_maskparity_zero_defect_eq_colm1_defect (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (t : Nat) (ht : T ≤ t) :
    bxor (Rule30UOR.Scale.maskparity (t + P) 0) (Rule30UOR.Scale.maskparity t 0) =
      bxor (Rule30UOR.Core.cell (t + P) (Rule30UOR.Scale.negpow 0))
        (Rule30UOR.Core.cell t (Rule30UOR.Scale.negpow 0)) := by
  simp only [maskparity_zero]
  exact periodic_carry60_defect_eq_colm1_defect T P hP h t ht

/-! ### Two-Half Dyadic Scale Equations: Right Threshold `J` vs. Left `ldiag` / `leftresponse` and Periodic Center -/

/-- **General Late Right-Diagonal Readout from Witt and Rule-60 Responses**: for every `r` and `k` (with no bound on `r`), `rdiag r (r + 2^k) = wittRespBool (r + 2^k) k ⊕ response (r + 2^k) k`. -/
theorem rdiag_late_eq_witt_xor_response (r k : Nat) :
    rdiag r (r + twopow k) =
      bxor (wittRespBool (r + twopow k) k) (Rule30UOR.Scale.response (r + twopow k) k) := by
  have hle : twopow k ≤ r + twopow k := by omega
  have h := wittRespBool_xor_response_ge (r + twopow k) k hle
  rw [show r + twopow k - twopow k = r by omega] at h
  exact h.symm

/-- **General Late Right-Diagonal Readout from Witt, `leftresponse`, and `maskparity`**: for every `r` and `k`, `rdiag r (r + 2^k) = wittRespBool (r + 2^k) k ⊕ (leftresponse (r + 2^k) k ⊕ maskparity (r + 2^k) k)`. -/
theorem rdiag_late_eq_witt_xor_left_mask (r k : Nat) :
    rdiag r (r + twopow k) =
      bxor (wittRespBool (r + twopow k) k)
        (bxor (Rule30UOR.Scale.leftresponse (r + twopow k) k)
          (Rule30UOR.Scale.maskparity (r + twopow k) k)) := by
  rw [rdiag_late_eq_witt_xor_response r k, Rule30UOR.Scale.split_paper (r + twopow k) k]

/-- **Universal Two-Half Witt Scale Identity**: for **every** `r` and `k` (without any cone restriction), `rdiag r (r + 2^k) ⊕ ldiag r (r + 2^k) = (center ((r + 2^k) + 2^k) ⊕ center (r + 2^k)) ⊕ wittRespBool (r + 2^k) k`. -/
theorem two_halves_witt_scale (r k : Nat) :
    bxor (rdiag r (r + twopow k)) (ldiag r (r + twopow k)) =
      bxor (bxor (Rule30UOR.Core.center ((r + twopow k) + twopow k))
        (Rule30UOR.Core.center (r + twopow k)))
        (wittRespBool (r + twopow k) k) := by
  have hr := rdiag_late_eq_witt_xor_response r k
  have hs := Rule30UOR.Scale.scale_center (r + twopow k) k
  rw [← ldiag_eq_cell_neg r (twopow k)] at hs
  unfold Rule30UOR.Scale.response at hr
  rw [bxor_eq_xor] at hr
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, hr, hs]
  cases Rule30UOR.Core.center (r + twopow k) <;>
    cases ldiag r (r + twopow k) <;>
    cases Rule30UOR.Core.window60 (r + twopow k) (twopow k) 0 <;>
    cases wittRespBool (r + twopow k) k <;> rfl

/-- **Cone-Wide Rule-60 Dyadic Coboundary (`r < 2^k`)**: for every `r < 2^k`, `ldiag r (r + 2^k)` equals the dyadic coboundary defect `response r (k + 1) ⊕ response r k ⊕ response (r + 2^k) k`. -/
theorem ldiag_eq_response_coboundary_cone (r k : Nat) (hr : r < twopow k) :
    ldiag r (r + twopow k) =
      bxor (bxor (Rule30UOR.Scale.response r (k + 1)) (Rule30UOR.Scale.response r k))
        (Rule30UOR.Scale.response (r + twopow k) k) := by
  have hr_k1 : r < twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]
    omega
  have hc1 := center_witt_scale_cone r k hr
  rw [wittRespBool_eq_response_cone r k hr] at hc1
  have hc2 := center_witt_scale_cone r (k + 1) hr_k1
  rw [wittRespBool_eq_response_cone r (k + 1) hr_k1] at hc2
  have hs := Rule30UOR.Scale.scale_center (r + twopow k) k
  rw [← ldiag_eq_cell_neg r (twopow k)] at hs
  have hstep : (r + twopow k) + twopow k = r + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep, hc2, hc1] at hs
  unfold Rule30UOR.Scale.response at *
  rw [bxor_eq_xor, bxor_eq_xor] at hs
  rw [bxor_eq_xor, bxor_eq_xor]
  revert hs
  cases Rule30UOR.Core.center r <;>
    cases Rule30UOR.Core.window60 r (twopow (k + 1)) 0 <;>
    cases Rule30UOR.Core.window60 r (twopow k) 0 <;>
    cases ldiag r (r + twopow k) <;>
    cases Rule30UOR.Core.window60 (r + twopow k) (twopow k) 0 <;> decide

/-- **Cone-Wide Pure Left-Half Response Coboundary (`r < 2^k`)**: for every `r < 2^k`, `ldiag r (r + 2^k) = leftresponse r (k + 1) ⊕ leftresponse r k ⊕ leftresponse (r + 2^k) k`. -/
theorem ldiag_eq_leftresponse_coboundary_cone (r k : Nat) (hr : r < twopow k) :
    ldiag r (r + twopow k) =
      bxor (bxor (Rule30UOR.Scale.leftresponse r (k + 1)) (Rule30UOR.Scale.leftresponse r k))
        (Rule30UOR.Scale.leftresponse (r + twopow k) k) := by
  rw [ldiag_eq_response_coboundary_cone r k hr,
    Rule30UOR.Scale.split_paper r (k + 1),
    Rule30UOR.Scale.split_paper r k,
    Rule30UOR.Scale.split_paper (r + twopow k) k]
  have hm := maskparity_coboundary r k
  revert hm
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse r (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse r k <;>
    cases Rule30UOR.Scale.leftresponse (r + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity r (k + 1) <;>
    cases Rule30UOR.Scale.maskparity r k <;>
    cases Rule30UOR.Scale.maskparity (r + twopow k) k <;> decide

/-- **Cone-Wide Two-Half Witt Dyadic Coboundary (`r < 2^k`)**: for every `r < 2^k`, `rdiag r (r + 2^k) ⊕ ldiag r (r + 2^k)` equals the dyadic coboundary defect `wittRespBool r (k + 1) ⊕ wittRespBool r k ⊕ wittRespBool (r + 2^k) k`. -/
theorem two_halves_eq_witt_coboundary_cone (r k : Nat) (hr : r < twopow k) :
    bxor (rdiag r (r + twopow k)) (ldiag r (r + twopow k)) =
      bxor (bxor (wittRespBool r (k + 1)) (wittRespBool r k))
        (wittRespBool (r + twopow k) k) := by
  have hr_k1 : r < twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]
    omega
  have hc1 := center_witt_scale_cone r k hr
  have hc2 := center_witt_scale_cone r (k + 1) hr_k1
  have h2h := two_halves_witt_scale r k
  have hstep : (r + twopow k) + twopow k = r + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep, hc2, hc1] at h2h
  rw [h2h]
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Core.center r <;>
    cases wittRespBool r (k + 1) <;>
    cases wittRespBool r k <;>
    cases wittRespBool (r + twopow k) k <;> rfl

/-- **Cone-Wide Late `maskparity` under `CenterPeriodic` (`T ≤ r < 2^k`)**: for every `r < 2^k` with `T ≤ r`, `maskparity (r + 2^k) k = (leftresponse r (k + 1) ⊕ leftresponse r k) ⊕ (center (r + lag P (k + 1)) ⊕ center (r + lag P k))`. -/
theorem periodic_maskparity_late_cone (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k : Nat) (ht : T ≤ r) (hr : r < twopow k) :
    Rule30UOR.Scale.maskparity (r + twopow k) k =
      bxor (bxor (Rule30UOR.Scale.leftresponse r (k + 1))
        (Rule30UOR.Scale.leftresponse r k))
        (bxor (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k))) := by
  have hr_k1 : r < twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]
    omega
  have hm := maskparity_coboundary r k
  have h1 := Rule30UOR.Scale.periodic_mask_paper T P hP h k r ht hr
  have h2 := Rule30UOR.Scale.periodic_mask_paper T P hP h (k + 1) r ht hr_k1
  rw [h1, h2] at hm
  revert hm
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor,
    bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.maskparity (r + twopow k) k <;>
    cases Rule30UOR.Scale.leftresponse r (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse r k <;>
    cases Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center r <;> decide

/-- **Master Two-Half Dyadic Scale Equation under `CenterPeriodic` (`T ≤ r < 2^k`)**: sets the right system `rdiag r (r + 2^k)` and the left system `ldiag r (r + 2^k)` against the Witt response `wittRespBool (r + 2^k) k` and the periodic center at lags `lag P (k + 1)` and `lag P k`. -/
theorem periodic_two_halves_scale_eq (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k : Nat) (ht : T ≤ r) (hr : r < twopow k) :
    bxor (rdiag r (r + twopow k)) (ldiag r (r + twopow k)) =
      bxor (bxor (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k)))
        (wittRespBool (r + twopow k) k) := by
  have hr_k1 : r < twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]
    omega
  rw [two_halves_eq_witt_coboundary_cone r k hr,
    periodic_witt_cone T P hP h (k + 1) r ht hr_k1,
    periodic_witt_cone T P hP h k r ht hr]
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)) <;>
    cases Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k) <;>
    cases Rule30UOR.Core.center r <;>
    cases wittRespBool (r + twopow k) k <;> rfl

/-- Boolean 4-term rearrangement `bxor a b = bxor c d → bxor a d = bxor b c`. -/
theorem bxor_swap_middle (a b c d : Bool) (h : bxor a b = bxor c d) :
    bxor a d = bxor b c := by
  revert h
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- **Master Two-Half Dyadic Scale Equation via `leftresponse` under `CenterPeriodic` (`T ≤ r < 2^k`)**: sets `rdiag r (r + 2^k) ⊕ wittRespBool (r + 2^k) k` directly equal to the left-half coboundary `(leftresponse r (k + 1) ⊕ leftresponse r k) ⊕ leftresponse (r + 2^k) k` XORed with the periodic center lag difference `center (r + lag P (k + 1)) ⊕ center (r + lag P k)`. -/
theorem periodic_rdiag_late_from_left_and_center (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k : Nat) (ht : T ≤ r) (hr : r < twopow k) :
    bxor (rdiag r (r + twopow k)) (wittRespBool (r + twopow k) k) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse r (k + 1))
        (Rule30UOR.Scale.leftresponse r k))
        (Rule30UOR.Scale.leftresponse (r + twopow k) k))
        (bxor (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k))) := by
  have h2h := periodic_two_halves_scale_eq T P hP h r k ht hr
  rw [ldiag_eq_leftresponse_coboundary_cone r k hr] at h2h
  exact bxor_swap_middle _ _ _ _ h2h

/-- **Right-System Law Below the Threshold (`r ≤ J`, `r < 2^k`) at `s = 0`**: for every `r ≤ J` with `r < 2^k`, `rdiag r (r + 2^k) = center r`. -/
theorem rdiag_below_threshold_eq_center (r k J : Nat) (hJ : IsRightThreshold k J)
    (hrJ : r ≤ J) (hr : r < twopow k) :
    rdiag r (r + twopow k) = Rule30UOR.Core.center r := by
  have h := rdiag_threshold_sub_eq_ldiag r 0 k J hJ (by omega) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at h
  have hc : ldiag r r = Rule30UOR.Core.center r := by
    have h0 := ldiag_eq_cell_neg r 0
    simp only [Nat.add_zero] at h0
    exact h0
  rw [hc] at h
  exact h

/-- **Two-Half Dyadic Scale Equation Below the Right Threshold (`r ≤ J`, `T ≤ r < 2^k`)**: below the right-period threshold `J`, the right system evaluates to `center r`, giving `center r ⊕ ldiag r (r + 2^k) = (center (r + lag P (k + 1)) ⊕ center (r + lag P k)) ⊕ wittRespBool (r + 2^k) k`. -/
theorem periodic_two_halves_below_threshold (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ r) (hrJ : r ≤ J) (hr : r < twopow k) :
    bxor (Rule30UOR.Core.center r) (ldiag r (r + twopow k)) =
      bxor (bxor (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k)))
        (wittRespBool (r + twopow k) k) := by
  rw [← rdiag_below_threshold_eq_center r k J hJ hrJ hr]
  exact periodic_two_halves_scale_eq T P hP h r k ht hr

/-- **Two-Half Dyadic Scale Equation via `leftresponse` Below the Right Threshold (`r ≤ J`, `T ≤ r < 2^k`)**: below the right-period threshold `J`, `center r ⊕ wittRespBool (r + 2^k) k` equals the `leftresponse` coboundary at `r` XORed with the periodic center lag difference. -/
theorem periodic_center_xor_witt_below_threshold (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (r k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ r) (hrJ : r ≤ J) (hr : r < twopow k) :
    bxor (Rule30UOR.Core.center r) (wittRespBool (r + twopow k) k) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse r (k + 1))
        (Rule30UOR.Scale.leftresponse r k))
        (Rule30UOR.Scale.leftresponse (r + twopow k) k))
        (bxor (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center (r + Rule30UOR.Scale.lag P k))) := by
  rw [← rdiag_below_threshold_eq_center r k J hJ hrJ hr]
  exact periodic_rdiag_late_from_left_and_center T P hP h r k ht hr

/-- **Two-Half Dyadic Scale Equation At the Right Threshold (`r = J + 1`, `T ≤ J + 1 < 2^k`)**: at the right-period threshold `J + 1`, the right system's antiperiodicity flips `rdiag (J + 1) ((J + 1) + 2^k)` to `!center (J + 1)`, giving `(!center (J + 1)) ⊕ ldiag (J + 1) ((J + 1) + 2^k) = (center ((J + 1) + lag P (k + 1)) ⊕ center ((J + 1) + lag P k)) ⊕ wittRespBool ((J + 1) + 2^k) k`. -/
theorem periodic_two_halves_at_threshold (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ J + 1) (hJlt : J + 1 < twopow k) :
    bxor (!Rule30UOR.Core.center (J + 1)) (ldiag (J + 1) ((J + 1) + twopow k)) =
      bxor (bxor (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P k)))
        (wittRespBool ((J + 1) + twopow k) k) := by
  rw [← threshold_center_antiperiod k J hJ hJlt]
  exact periodic_two_halves_scale_eq T P hP h (J + 1) k ht hJlt

/-- **Two-Half Dyadic Scale Equation via `leftresponse` At the Right Threshold (`r = J + 1`, `T ≤ J + 1 < 2^k`)**: at the right-period threshold `J + 1`, `(!center (J + 1)) ⊕ wittRespBool ((J + 1) + 2^k) k` equals the `leftresponse` coboundary at `J + 1` XORed with the periodic center lag difference. -/
theorem periodic_not_center_xor_witt_at_threshold (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ J + 1) (hJlt : J + 1 < twopow k) :
    bxor (!Rule30UOR.Core.center (J + 1)) (wittRespBool ((J + 1) + twopow k) k) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse (J + 1) (k + 1))
        (Rule30UOR.Scale.leftresponse (J + 1) k))
        (Rule30UOR.Scale.leftresponse ((J + 1) + twopow k) k))
        (bxor (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((J + 1) + Rule30UOR.Scale.lag P k))) := by
  rw [← threshold_center_antiperiod k J hJ hJlt]
  exact periodic_rdiag_late_from_left_and_center T P hP h (J + 1) k ht hJlt

/-- **Threshold-Center Coupling of `leftresponse ⊕ maskparity` to `rdiag (J + 1)`**: at time `J + 1 < 2^k`, `leftresponse (J + 1) k ⊕ maskparity (J + 1) k = !(center ((J + 1) + 2^k) ⊕ rdiag (J + 1) ((J + 1) + 2^k))`. -/
theorem threshold_center_left_mask_eq_not_rdiag (k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) :
    bxor (Rule30UOR.Scale.leftresponse (J + 1) k) (Rule30UOR.Scale.maskparity (J + 1) k) =
      !bxor (Rule30UOR.Core.center ((J + 1) + twopow k))
        (rdiag (J + 1) ((J + 1) + twopow k)) := by
  rw [← Rule30UOR.Scale.split_paper (J + 1) k,
    ← wittRespBool_eq_response_cone (J + 1) k hJlt]
  exact threshold_center_witt_response k J hJ hJlt

/-- **Triality Sector 1 Equating the Right Threshold Law (`d + 2 * s ≤ J`) and the Left Settled Law (`SettledBy d (d + s)`)**: when `d + 2 * s ≤ J` (`d + 2 * s < 2^k`) and `SettledBy d (d + s)` (`d ≤ k`), the right-diagonal spatial difference `rdiag (d + 2 * s + 2^k) (d + s + 2^k) ⊕ rdiag (d + 2 * s) (d + s + 2^k)` equals the left-diagonal spatial difference `ldiag (d + 2^k) (d + s + 2^k) ⊕ ldiag d (d + s + 2^k)`. -/
theorem sector_one_below_threshold_eq_left_settled (d s k J : Nat) (hJ : IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s ≤ J) (hds : d + 2 * s < twopow k)
    (hset : SettledBy d (d + s)) :
    bxor (rdiag ((d + 2 * s) + twopow k) ((d + s) + twopow k))
      (rdiag (d + 2 * s) ((d + s) + twopow k)) =
      bxor (ldiag (d + twopow k) ((d + s) + twopow k))
        (ldiag d ((d + s) + twopow k)) := by
  rw [← winWitt_testBit_sector_one_below_threshold (d + s) k J (d + 2 * s) hJ hdJ hds (by omega),
    winWitt_testBit_sector_one_settled d s k hk hds hset]

/-- **Triality Sector 1 Equating the Right Antiperiodic Threshold Law (`d + 2 * s = J + 1`) and the Left Settled Law (`SettledBy d (d + s)`)**: when `d + 2 * s = J + 1 < 2^k` and `SettledBy d (d + s)` (`d ≤ k`), the negated right-diagonal spatial difference `!(rdiag (J + 1 + 2^k) (d + s + 2^k) ⊕ rdiag (J + 1) (d + s + 2^k))` equals the left-diagonal spatial difference `ldiag (d + 2^k) (d + s + 2^k) ⊕ ldiag d (d + s + 2^k)`. -/
theorem sector_one_at_threshold_eq_left_settled (d s k J : Nat) (hJ : IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s = J + 1) (hJlt : J + 1 < twopow k)
    (hset : SettledBy d (d + s)) :
    (!bxor (rdiag ((J + 1) + twopow k) ((d + s) + twopow k))
      (rdiag (J + 1) ((d + s) + twopow k))) =
      bxor (ldiag (d + twopow k) ((d + s) + twopow k))
        (ldiag d ((d + s) + twopow k)) := by
  have hds : d + 2 * s < twopow k := by omega
  rw [← winWitt_testBit_sector_one_at_threshold (d + s) k J hJ hJlt (by omega),
    ← hdJ,
    winWitt_testBit_sector_one_settled d s k hk hds hset]

/-! ### Exact OR-Gate Factorization of the Right and Left Laws Across Scale `2^k` -/

/-- **Fundamental OR-XOR Gate Factorization**: for any `a1, a2, b : Bool`, `(a1 || b) ⊕ (a2 || b) = (a1 ⊕ a2) && (!b)`. -/
theorem or_xor_or_of_eq (a1 a2 b : Bool) :
    bxor (a1 || b) (a2 || b) = (bxor a1 a2 && !b) := by
  cases a1 <;> cases a2 <;> cases b <;> rfl

/-- **Universal Antiperiodic OR-Gate Cancellation**: for any `a, b : Bool`, `((!a) || b) ⊕ (a || b) = !b`, independent of `a`. -/
theorem not_or_xor_or (a b : Bool) :
    bxor ((!a) || b) (a || b) = !b := by
  cases a <;> cases b <;> rfl

/-- **Right-System `2^k`-Defect Step Law Below the Threshold (`j ≤ J`)**: for every `j ≤ J` (`IsRightThreshold k J`) and every time `t`, the 1-step time difference of `rdiag (j + 2) (t + 2^k) ⊕ rdiag (j + 2) t` equals `(rdiag (j + 1) (t + 2^k) ⊕ rdiag (j + 1) t) && (!rdiag j t)`. -/
theorem rdiag_defect_step_below_threshold (t k J j : Nat) (hJ : IsRightThreshold k J)
    (hjJ : j ≤ J) :
    bxor (bxor (rdiag (j + 2) ((t + 1) + twopow k)) (rdiag (j + 2) (t + 1)))
      (bxor (rdiag (j + 2) (t + twopow k)) (rdiag (j + 2) t)) =
      (bxor (rdiag (j + 1) (t + twopow k)) (rdiag (j + 1) t) && !rdiag j t) := by
  have hper := Rule30UOR.KitConstructive.per_mono_le hjJ hJ.1
  have hj_eq : rdiag j (t + twopow k) = rdiag j t := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact hper t
  have hs_late := Rule30UOR.Core.rdiag_step j (t + twopow k)
  have hs_early := Rule30UOR.Core.rdiag_step j t
  rw [show (t + 1) + twopow k = (t + twopow k) + 1 by omega,
    hs_late, hs_early, hj_eq, ← or_xor_or_of_eq]
  simp only [bxor_eq_xor]
  cases rdiag (j + 2) (t + twopow k) <;>
    cases rdiag (j + 2) t <;>
    cases (rdiag (j + 1) (t + twopow k) || rdiag j t) <;>
    cases (rdiag (j + 1) t || rdiag j t) <;> rfl

/-- **Universal Right-System `2^k`-Defect Step Law At the Threshold (`j = J`)**: for every `k, J` with `IsRightThreshold k J` and **every** time `t : Nat` (without any light-cone restriction), the 1-step time difference of `rdiag (J + 2) (t + 2^k) ⊕ rdiag (J + 2) t` is identically `!rdiag J t`. -/
theorem rdiag_threshold_plus_two_defect_step (t k J : Nat) (hJ : IsRightThreshold k J) :
    bxor (bxor (rdiag (J + 2) ((t + 1) + twopow k)) (rdiag (J + 2) (t + 1)))
      (bxor (rdiag (J + 2) (t + twopow k)) (rdiag (J + 2) t)) =
      !rdiag J t := by
  rw [rdiag_defect_step_below_threshold t k J J hJ (by omega)]
  have ha : rdiag (J + 1) (t + twopow k) = !rdiag (J + 1) t := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact Rule30UOR.KitConstructive.antiperiod hJ.1 hJ.2 t
  rw [ha, bxor_eq_xor]
  cases rdiag (J + 1) t <;> cases rdiag J t <;> rfl

/-- **Universal Sector-0 Step Law of `winWitt` at Bit `J + 2`**: for every `k, J` with `IsRightThreshold k J`, `J + 2 < 2^k`, and **every** time `t0 : Nat`, `(winWitt (t0 + 1) (2^k)).testBit (J + 2) ⊕ (winWitt t0 (2^k)).testBit (J + 2) = !rdiag J t0`. -/
theorem winWitt_testBit_threshold_plus_two_step_diff (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 2 < twopow k) :
    bxor ((winWitt (t0 + 1) (twopow k)).testBit (J + 2))
      ((winWitt t0 (twopow k)).testBit (J + 2)) =
      !rdiag J t0 := by
  rw [winWitt_testBit_lt_twopow (t0 + 1) k (J + 2) hJlt,
    winWitt_testBit_lt_twopow t0 k (J + 2) hJlt]
  exact rdiag_threshold_plus_two_defect_step t0 k J hJ

/-- **Universal Sector-0 Step Law of `winWitt` at Bit `J + 2` in Left-Diagonal Coordinates (`d + 2 * s = J`)**: when `d + 2 * s = J` and `J + 2 < 2^k`, `(winWitt (d + s + 1) (2^k)).testBit (J + 2) ⊕ (winWitt (d + s) (2^k)).testBit (J + 2) = !ldiag d (d + s)`. -/
theorem winWitt_testBit_threshold_plus_two_step_diff_ldiag (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hdJ : d + 2 * s = J) (hJlt : J + 2 < twopow k) :
    bxor ((winWitt ((d + s) + 1) (twopow k)).testBit (J + 2))
      ((winWitt (d + s) (twopow k)).testBit (J + 2)) =
      !ldiag d (d + s) := by
  rw [winWitt_testBit_threshold_plus_two_step_diff (d + s) k J hJ hJlt,
    ← hdJ, ← ldiag_eq_rdiag d s]

/-- **Right-Diagonal Late Readout at `r = J + 2` (`rdiag (J + 2) ((J + 2) + 2^k)`)**: transporting the `2^k`-defect of `rdiag (J + 2)` from `t = J` across the two steps `J → J + 1 → J + 2` expresses `rdiag (J + 2) ((J + 2) + 2^k)` in terms of `center (J + 2)`, the defect `rdiag (J + 2) (J + 2^k) ⊕ rdiag (J + 2) J` at time `J`, `center J`, and `rdiag J (J + 1)`. -/
theorem rdiag_threshold_plus_two_center_decomp (k J : Nat) (hJ : IsRightThreshold k J) :
    rdiag (J + 2) ((J + 2) + twopow k) =
      bxor (bxor (Rule30UOR.Core.center (J + 2))
        (bxor (rdiag (J + 2) (J + twopow k)) (rdiag (J + 2) J)))
        (bxor (Rule30UOR.Core.center J) (rdiag J (J + 1))) := by
  have hs0 := rdiag_threshold_plus_two_defect_step J k J hJ
  have hs1 := rdiag_threshold_plus_two_defect_step (J + 1) k J hJ
  rw [show (J + 1) + 1 = J + 2 by omega] at hs1
  rw [← core_center_eq_rdiag J] at hs0
  have hc2 := core_center_eq_rdiag (J + 2)
  revert hs0 hs1 hc2
  simp only [bxor_eq_xor]
  cases rdiag (J + 2) ((J + 2) + twopow k) <;>
    cases rdiag (J + 2) (J + 2) <;>
    cases Rule30UOR.Core.center (J + 2) <;>
    cases rdiag (J + 2) ((J + 1) + twopow k) <;>
    cases rdiag (J + 2) (J + 1) <;>
    cases rdiag (J + 2) (J + twopow k) <;>
    cases rdiag (J + 2) J <;>
    cases Rule30UOR.Core.center J <;>
    cases rdiag J (J + 1) <;> decide

/-- **Two-Half Dyadic Scale Equation At `r = J + 2` under `CenterPeriodic` (`T ≤ J + 2 < 2^k`)**: combines the right-threshold transport at `J + 2` with the left diagonal `ldiag (J + 2) ((J + 2) + 2^k)`, the Witt response `wittRespBool ((J + 2) + 2^k) k`, and the periodic center lag difference at `J + 2`. -/
theorem periodic_two_halves_at_threshold_plus_two (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ J + 2) (hJlt : J + 2 < twopow k) :
    bxor (bxor (bxor (Rule30UOR.Core.center (J + 2))
      (bxor (rdiag (J + 2) (J + twopow k)) (rdiag (J + 2) J)))
      (bxor (Rule30UOR.Core.center J) (rdiag J (J + 1))))
      (ldiag (J + 2) ((J + 2) + twopow k)) =
      bxor (bxor (Rule30UOR.Core.center ((J + 2) + Rule30UOR.Scale.lag P (k + 1)))
        (Rule30UOR.Core.center ((J + 2) + Rule30UOR.Scale.lag P k)))
        (wittRespBool ((J + 2) + twopow k) k) := by
  rw [← rdiag_threshold_plus_two_center_decomp k J hJ]
  exact periodic_two_halves_scale_eq T P hP h (J + 2) k ht hJlt

/-- **Left-System `2^k`-Damage Step Law Above a Settled Left Diagonal (`SettledBy d s`, `d ≤ k`)**: once left diagonal `d ≤ k` has settled by time `s`, `ldiag d` cancels from the XOR slot of `ldiag_step`, so the next-step `2^k`-damage on `d + 2` is pure OR-gate difference `(ldiag (d + 1) (s + 2^k) || ldiag (d + 2) (s + 2^k)) ⊕ (ldiag (d + 1) s || ldiag (d + 2) s)`. -/
theorem ldiag_damage_step_of_settled (d s k : Nat) (hk : d ≤ k) (hset : SettledBy d s) :
    bxor (ldiag (d + 2) ((s + 1) + twopow k)) (ldiag (d + 2) (s + 1)) =
      bxor (ldiag (d + 1) (s + twopow k) || ldiag (d + 2) (s + twopow k))
        (ldiag (d + 1) s || ldiag (d + 2) s) := by
  have hd_eq : ldiag d (s + twopow k) = ldiag d s := by
    rw [ldiag_settled_eq_E d s k hk (by unfold SettledBy at hset; omega),
      Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D d s hset]
  have hs_late := Rule30UOR.Core.ldiag_step d (s + twopow k)
  have hs_early := Rule30UOR.Core.ldiag_step d s
  rw [show (s + 1) + twopow k = (s + twopow k) + 1 by omega,
    hs_late, hs_early, hd_eq]
  simp only [bxor_eq_xor]
  cases ldiag d s <;>
    cases (ldiag (d + 1) (s + twopow k) || ldiag (d + 2) (s + twopow k)) <;>
    cases (ldiag (d + 1) s || ldiag (d + 2) s) <;> rfl

/-- **Left-System `2^k`-Damage Gating at the Settling Front (`SettledBy d s`, `SettledBy (d + 1) s`, `d + 1 ≤ k`)**: when both `d` and `d + 1` have settled by time `s`, the `2^k`-damage on `d + 2` at time `s + 1` is Multiplicatively Gated by `!ldiag (d + 1) s`: `ldiag (d + 2) ((s + 1) + 2^k) ⊕ ldiag (d + 2) (s + 1) = (ldiag (d + 2) (s + 2^k) ⊕ ldiag (d + 2) s) && (!ldiag (d + 1) s)`. -/
theorem ldiag_damage_step_of_settled_pair (d s k : Nat) (hk : d + 1 ≤ k)
    (hset0 : SettledBy d s) (hset1 : SettledBy (d + 1) s) :
    bxor (ldiag (d + 2) ((s + 1) + twopow k)) (ldiag (d + 2) (s + 1)) =
      (bxor (ldiag (d + 2) (s + twopow k)) (ldiag (d + 2) s) && !ldiag (d + 1) s) := by
  rw [ldiag_damage_step_of_settled d s k (by omega) hset0]
  have hd1_eq : ldiag (d + 1) (s + twopow k) = ldiag (d + 1) s := by
    rw [ldiag_settled_eq_E (d + 1) s k hk (by unfold SettledBy at hset1; omega),
      Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D (d + 1) s hset1]
  rw [hd1_eq]
  simp only [bxor_eq_xor]
  cases ldiag (d + 1) s <;>
    cases ldiag (d + 2) (s + twopow k) <;>
    cases ldiag (d + 2) s <;> rfl

/-- **Universal Right-System `2^k`-Defect Step Law At the Threshold in Left-Diagonal Coordinates (`d + 2 * s = J`)**: when `d + 2 * s = J`, the 1-step time difference of `rdiag (J + 2) (t + 2^k) ⊕ rdiag (J + 2) t` at `t = d + s` equals `!ldiag d (d + s)`. -/
theorem rdiag_threshold_plus_two_defect_step_ldiag (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hdJ : d + 2 * s = J) :
    bxor (bxor (rdiag (J + 2) (((d + s) + 1) + twopow k)) (rdiag (J + 2) ((d + s) + 1)))
      (bxor (rdiag (J + 2) ((d + s) + twopow k)) (rdiag (J + 2) (d + s))) =
      !ldiag d (d + s) := by
  rw [rdiag_threshold_plus_two_defect_step (d + s) k J hJ,
    ← hdJ, ← ldiag_eq_rdiag d s]

/-- **Two-Half Dyadic Scale Equation via `leftresponse` At `r = J + 2` under `CenterPeriodic` (`T ≤ J + 2 < 2^k`)**: sets `(center (J + 2) ⊕ (rdiag (J + 2) (J + 2^k) ⊕ rdiag (J + 2) J) ⊕ (center J ⊕ rdiag J (J + 1))) ⊕ wittRespBool ((J + 2) + 2^k) k` equal to the `leftresponse` coboundary at `J + 2` XORed with the periodic center lag difference. -/
theorem periodic_center_xor_witt_at_threshold_plus_two (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ J + 2) (hJlt : J + 2 < twopow k) :
    bxor (bxor (bxor (Rule30UOR.Core.center (J + 2))
      (bxor (rdiag (J + 2) (J + twopow k)) (rdiag (J + 2) J)))
      (bxor (Rule30UOR.Core.center J) (rdiag J (J + 1))))
      (wittRespBool ((J + 2) + twopow k) k) =
      bxor (bxor (bxor (Rule30UOR.Scale.leftresponse (J + 2) (k + 1))
        (Rule30UOR.Scale.leftresponse (J + 2) k))
        (Rule30UOR.Scale.leftresponse ((J + 2) + twopow k) k))
        (bxor (Rule30UOR.Core.center ((J + 2) + Rule30UOR.Scale.lag P (k + 1)))
          (Rule30UOR.Core.center ((J + 2) + Rule30UOR.Scale.lag P k))) := by
  rw [← rdiag_threshold_plus_two_center_decomp k J hJ]
  exact periodic_rdiag_late_from_left_and_center T P hP h (J + 2) k ht hJlt

/-! ### Off-Center Two-Half Triality and Coboundary Equations at Slot `r = d + 2 * s < 2^k` -/

/-- **Off-Center Two-Half Witt Dyadic Coboundary (`d + 2 * s < 2^k`)**: at any base time `t0 = d + s` and slot `r = d + 2 * s < 2^k`, `rdiag (d + 2 * s) (d + s + 2^k) ⊕ ldiag d (d + s + 2^k)` equals the 3-term Witt coboundary `((winWitt (d + s) (2^(k+1))).testBit (r + 2^(k+1)) ⊕ (winWitt (d + s) (2^k)).testBit (r + 2^k)) ⊕ (winWitt (d + s + 2^k) (2^k)).testBit (r + 2^(k+1))`. -/
theorem two_halves_off_center_witt_coboundary (d s k : Nat) (hds : d + 2 * s < twopow k) :
    bxor (rdiag (d + 2 * s) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)) =
      bxor (bxor ((winWitt (d + s) (twopow (k + 1))).testBit ((d + 2 * s) + twopow (k + 1)))
        ((winWitt (d + s) (twopow k)).testBit ((d + 2 * s) + twopow k)))
        ((winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1))) := by
  have htri := winWitt_late_testBit_triality (d + s) k (d + 2 * s)
  have h02 := winWitt_testBit_sector_zero_xor_two d s k hds
  revert htri h02
  simp only [bxor_eq_xor]
  cases rdiag (d + 2 * s) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;>
    cases (winWitt (d + s) (twopow (k + 1))).testBit ((d + 2 * s) + twopow (k + 1)) <;>
    cases (winWitt (d + s) (twopow k)).testBit (d + 2 * s) <;>
    cases (winWitt (d + s) (twopow k)).testBit ((d + 2 * s) + twopow k) <;>
    cases (winWitt (d + s) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1)) <;>
    cases (winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1)) <;> decide

/-- **Off-Center Two-Half Witt Scale Identity (`d + 2 * s < 2^k`)**: at any base time `t0 = d + s` and slot `r = d + 2 * s < 2^k`, `rdiag (d + 2 * s) (d + s + 2^k) ⊕ ldiag d (d + s + 2^k)` equals the column-`-s` scale increment `(ldiag (d + 2^(k+1)) (d + s + 2^(k+1)) ⊕ ldiag (d + 2^k) (d + s + 2^k))` XORed with `(winWitt (d + s + 2^k) (2^k)).testBit (d + 2 * s + 2^(k+1))`. -/
theorem two_halves_off_center_witt_scale (d s k : Nat) (hds : d + 2 * s < twopow k) :
    bxor (rdiag (d + 2 * s) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)) =
      bxor (bxor (ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)))
        (ldiag (d + twopow k) ((d + s) + twopow k)))
        ((winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1))) := by
  have hds_k1 : d + 2 * s < twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]
    omega
  rw [two_halves_off_center_witt_coboundary d s k hds,
    winWitt_testBit_sector_one_ldiag d s (k + 1) hds_k1,
    winWitt_testBit_sector_one_ldiag d s k hds]
  simp only [bxor_eq_xor]
  cases ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)) <;>
    cases ldiag (d + twopow k) ((d + s) + twopow k) <;>
    cases ldiag d (d + s) <;>
    cases (winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1)) <;> rfl

/-- **Vanishing of the Off-Center Witt Coboundary on Settled Left Diagonals Below the Right Threshold (`d + 2 * s ≤ J`)**: when `d + 2 * s ≤ J` (`d + 2 * s < 2^k`) and `SettledBy d (d + s)` (`d ≤ k`), the 3-term Witt coboundary at slot `r = d + 2 * s` vanishes identically. -/
theorem off_center_witt_coboundary_settled_below_threshold (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hk : d ≤ k) (hdJ : d + 2 * s ≤ J)
    (hds : d + 2 * s < twopow k) (hset : SettledBy d (d + s)) :
    bxor (bxor ((winWitt (d + s) (twopow (k + 1))).testBit ((d + 2 * s) + twopow (k + 1)))
      ((winWitt (d + s) (twopow k)).testBit ((d + 2 * s) + twopow k)))
      ((winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1))) =
      false := by
  rw [← two_halves_off_center_witt_coboundary d s k hds,
    rdiag_eq_ldiag_of_settled_below_threshold d s k J hJ hk hdJ hds hset,
    bxor_eq_xor, Bool.xor_self]

/-- **Antiperiodic Parity (`true`) of the Off-Center Witt Coboundary on Settled Left Diagonals At the Right Threshold (`d + 2 * s = J + 1`)**: when `d + 2 * s = J + 1 < 2^k` and `SettledBy d (d + s)` (`d ≤ k`), the right-threshold flip and left-settledness jointly force the 3-term Witt coboundary at slot `J + 1` to equal `true`. -/
theorem off_center_witt_coboundary_settled_at_threshold (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hk : d ≤ k) (hdJ : d + 2 * s = J + 1)
    (hJlt : J + 1 < twopow k) (hset : SettledBy d (d + s)) :
    bxor (bxor ((winWitt (d + s) (twopow (k + 1))).testBit ((J + 1) + twopow (k + 1)))
      ((winWitt (d + s) (twopow k)).testBit ((J + 1) + twopow k)))
      ((winWitt ((d + s) + twopow k) (twopow k)).testBit ((J + 1) + twopow (k + 1))) =
      true := by
  have hds : d + 2 * s < twopow k := by omega
  have hcob := two_halves_off_center_witt_coboundary d s k hds
  rw [hdJ, rdiag_eq_not_ldiag_of_settled_at_threshold d s k J hJ hk hdJ hJlt hset] at hcob
  rw [← hcob, bxor_eq_xor]
  cases ldiag d ((d + s) + twopow k) <;> rfl

/-- **Late Off-Center Witt Bit Below the Right Threshold on Settled Left Diagonals (`d + 2 * s ≤ J`)**: when `d + 2 * s ≤ J` (`d + 2 * s < 2^k`) and `SettledBy d (d + s)` (`d ≤ k`), bit `d + 2 * s + 2^(k+1)` of `winWitt (d + s + 2^k) (2^k)` equals the column-`-s` dyadic difference `ldiag (d + 2^(k+1)) (d + s + 2^(k+1)) ⊕ ldiag (d + 2^k) (d + s + 2^k)`. -/
theorem off_center_witt_scale_settled_below_threshold (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hk : d ≤ k) (hdJ : d + 2 * s ≤ J)
    (hds : d + 2 * s < twopow k) (hset : SettledBy d (d + s)) :
    (winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1)) =
      bxor (ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)))
        (ldiag (d + twopow k) ((d + s) + twopow k)) := by
  have hsc := two_halves_off_center_witt_scale d s k hds
  rw [rdiag_eq_ldiag_of_settled_below_threshold d s k J hJ hk hdJ hds hset,
    bxor_eq_xor, Bool.xor_self] at hsc
  revert hsc
  simp only [bxor_eq_xor]
  cases (winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1)) <;>
    cases ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)) <;>
    cases ldiag (d + twopow k) ((d + s) + twopow k) <;> decide

/-- **Late Off-Center Witt Bit Inversion At the Right Threshold on Settled Left Diagonals (`d + 2 * s = J + 1`)**: when `d + 2 * s = J + 1 < 2^k` and `SettledBy d (d + s)` (`d ≤ k`), bit `J + 1 + 2^(k+1)` of `winWitt (d + s + 2^k) (2^k)` is the **negation** of the column-`-s` dyadic difference `!(ldiag (d + 2^(k+1)) (d + s + 2^(k+1)) ⊕ ldiag (d + 2^k) (d + s + 2^k))`. -/
theorem off_center_witt_scale_settled_at_threshold (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hk : d ≤ k) (hdJ : d + 2 * s = J + 1)
    (hJlt : J + 1 < twopow k) (hset : SettledBy d (d + s)) :
    (winWitt ((d + s) + twopow k) (twopow k)).testBit ((J + 1) + twopow (k + 1)) =
      !bxor (ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)))
        (ldiag (d + twopow k) ((d + s) + twopow k)) := by
  have hds : d + 2 * s < twopow k := by omega
  have hsc := two_halves_off_center_witt_scale d s k hds
  rw [hdJ, rdiag_eq_not_ldiag_of_settled_at_threshold d s k J hJ hk hdJ hJlt hset] at hsc
  revert hsc
  simp only [bxor_eq_xor]
  cases ldiag d ((d + s) + twopow k) <;>
    cases (winWitt ((d + s) + twopow k) (twopow k)).testBit ((J + 1) + twopow (k + 1)) <;>
    cases ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)) <;>
    cases ldiag (d + twopow k) ((d + s) + twopow k) <;> decide

/-- Paper-facing `BitWinWittEq` wrapper for `two_halves_off_center_witt_scale`. -/
theorem two_halves_off_center_witt_scale_prop (d s k : Nat) (hds : d + 2 * s < twopow k) :
    BitWinWittEq ((d + s) + twopow k) (twopow k) ((d + 2 * s) + twopow (k + 1))
      (bxor (bxor (rdiag (d + 2 * s) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)))
        (bxor (ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)))
          (ldiag (d + twopow k) ((d + s) + twopow k)))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit]
  have hsc := two_halves_off_center_witt_scale d s k hds
  revert hsc
  simp only [bxor_eq_xor]
  cases rdiag (d + 2 * s) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;>
    cases ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)) <;>
    cases ldiag (d + twopow k) ((d + s) + twopow k) <;>
    cases (winWitt ((d + s) + twopow k) (twopow k)).testBit ((d + 2 * s) + twopow (k + 1)) <;> decide

/-- Paper-facing `BitWinWittEq` wrapper for `off_center_witt_scale_settled_below_threshold`. -/
theorem off_center_witt_scale_settled_below_threshold_prop (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hk : d ≤ k) (hdJ : d + 2 * s ≤ J)
    (hds : d + 2 * s < twopow k) (hset : SettledBy d (d + s)) :
    BitWinWittEq ((d + s) + twopow k) (twopow k) ((d + 2 * s) + twopow (k + 1))
      (bxor (ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)))
        (ldiag (d + twopow k) ((d + s) + twopow k))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    off_center_witt_scale_settled_below_threshold d s k J hJ hk hdJ hds hset]

/-- Paper-facing `BitWinWittEq` wrapper for `off_center_witt_scale_settled_at_threshold`. -/
theorem off_center_witt_scale_settled_at_threshold_prop (d s k J : Nat)
    (hJ : IsRightThreshold k J) (hk : d ≤ k) (hdJ : d + 2 * s = J + 1)
    (hJlt : J + 1 < twopow k) (hset : SettledBy d (d + s)) :
    BitWinWittEq ((d + s) + twopow k) (twopow k) ((J + 1) + twopow (k + 1))
      (!bxor (ldiag (d + twopow (k + 1)) ((d + s) + twopow (k + 1)))
        (ldiag (d + twopow k) ((d + s) + twopow k))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    off_center_witt_scale_settled_at_threshold d s k J hJ hk hdJ hJlt hset]

/-! ### Column `-1` (`s = 1`) Off-Center Scale Equations and Coupling to the XOR Channel (`maskparity · 0`) -/

/-- **Universal Dyadic Scale Jump of Column `-1` via `center` and `maskparity · 0`**: at every time `t` and scale `k`, the dyadic difference `ldiag (d + 2^(k+1)) (d + 1 + 2^(k+1)) ⊕ ldiag (d + 2^k) (d + 1 + 2^k)` on column `-1` (`t = d + 1`) equals the XOR-channel dyadic jump `maskparity (d + 1 + 2^(k+1)) 0 ⊕ maskparity (d + 1 + 2^k) 0` XORed with the center differences at `d + 1 + 2^(k+1)` and `d + 1 + 2^k`. -/
theorem colm1_dyadic_jump_eq_maskparity_zero_jump (d k : Nat) :
    bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
      (ldiag (d + twopow k) ((d + 1) + twopow k)) =
      bxor (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
        (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0))
        (bxor (bxor (Rule30UOR.Core.center (((d + 1) + twopow (k + 1)) + 1))
          (Rule30UOR.Core.center ((d + 1) + twopow (k + 1))))
          (bxor (Rule30UOR.Core.center (((d + 1) + twopow k) + 1))
            (Rule30UOR.Core.center ((d + 1) + twopow k)))) := by
  have hc1 := center_step_eq_carry60 ((d + 1) + twopow (k + 1))
  have hc2 := center_step_eq_carry60 ((d + 1) + twopow k)
  rw [← maskparity_zero ((d + 1) + twopow (k + 1))] at hc1
  rw [← maskparity_zero ((d + 1) + twopow k)] at hc2
  have hl1 : ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) =
      Rule30UOR.Core.cell ((d + 1) + twopow (k + 1)) (-1) := by
    rw [show (d + 1) + twopow (k + 1) = (d + twopow (k + 1)) + 1 by omega,
      ldiag_eq_cell_neg (d + twopow (k + 1)) 1]
    rfl
  have hl2 : ldiag (d + twopow k) ((d + 1) + twopow k) =
      Rule30UOR.Core.cell ((d + 1) + twopow k) (-1) := by
    rw [show (d + 1) + twopow k = (d + twopow k) + 1 by omega,
      ldiag_eq_cell_neg (d + twopow k) 1]
    rfl
  rw [hl1, hl2]
  revert hc1 hc2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center (((d + 1) + twopow (k + 1)) + 1) <;>
    cases Rule30UOR.Core.center ((d + 1) + twopow (k + 1)) <;>
    cases Rule30UOR.Core.cell ((d + 1) + twopow (k + 1)) (-1) <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 <;>
    cases Rule30UOR.Core.center (((d + 1) + twopow k) + 1) <;>
    cases Rule30UOR.Core.center ((d + 1) + twopow k) <;>
    cases Rule30UOR.Core.cell ((d + 1) + twopow k) (-1) <;>
    cases Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 <;> decide

/-- **Under `CenterPeriodic T P`, Dyadic Scale Jump of Column `-1` Equals `leftresponse` Second Difference**: for `T ≤ d + 1` and `d + 2 ≤ k`, the center terms in `colm1_dyadic_jump_eq_maskparity_zero_jump` and `periodic_late_maskparity_zero_dyadic_jump` cancel identically, locking the column-`-1` dyadic jump `ldiag (d + 2^(k+1)) (d + 1 + 2^(k+1)) ⊕ ldiag (d + 2^k) (d + 1 + 2^k)` purely to the early `leftresponse` differences at `d + 2` and `d + 1`. -/
theorem periodic_colm1_dyadic_jump_eq_leftresponse_diff (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) :
    bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
      (ldiag (d + twopow k) ((d + 1) + twopow k)) =
      bxor (bxor (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 2) k))
        (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k)) := by
  rw [colm1_dyadic_jump_eq_maskparity_zero_jump d k,
    periodic_late_maskparity_zero_dyadic_jump T P hP h (d + 1) k ht hk]
  have hc1 := Rule30UOR.Scale.center_mod hP h (d + 2) (twopow (k + 1)) (by omega)
  have hc2 := Rule30UOR.Scale.center_mod hP h (d + 1) (twopow (k + 1)) ht
  have hc3 := Rule30UOR.Scale.center_mod hP h (d + 2) (twopow k) (by omega)
  have hc4 := Rule30UOR.Scale.center_mod hP h (d + 1) (twopow k) ht
  rw [show ((d + 1) + twopow (k + 1)) + 1 = (d + 2) + twopow (k + 1) by omega,
    show ((d + 1) + twopow k) + 1 = (d + 2) + twopow k by omega,
    show (d + 1) + 1 = d + 2 by omega,
    hc1, hc2, hc3, hc4]
  unfold Rule30UOR.Scale.lag
  simp only [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (d + 2) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + 2) k <;>
    cases Rule30UOR.Scale.leftresponse (d + 1) (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse (d + 1) k <;>
    cases Rule30UOR.Core.center ((d + 2) + twopow (k + 1) % P) <;>
    cases Rule30UOR.Core.center ((d + 2) + twopow k % P) <;>
    cases Rule30UOR.Core.center ((d + 1) + twopow (k + 1) % P) <;>
    cases Rule30UOR.Core.center ((d + 1) + twopow k % P) <;> rfl

/-- **Exact Early `leftresponse` Formula for Late Off-Center Witt Bit Below the Right Threshold (`s = 1`, `d + 2 ≤ J`)**: under `CenterPeriodic T P`, when `T ≤ d + 1`, `d + 2 ≤ J`, and `SettledBy d (d + 1)` (`d + 2 ≤ k`), bit `d + 2 + 2^(k+1)` of the late Witt window `winWitt (d + 1 + 2^k) (2^k)` equals the early `leftresponse` second difference `(leftresponse (d + 2) (k + 1) ⊕ leftresponse (d + 2) k) ⊕ (leftresponse (d + 1) (k + 1) ⊕ leftresponse (d + 1) k)`. -/
theorem periodic_off_center_witt_below_threshold_eq_leftresponse (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hdJ : d + 2 ≤ J)
    (hset : SettledBy d (d + 1)) :
    (winWitt ((d + 1) + twopow k) (twopow k)).testBit ((d + 2) + twopow (k + 1)) =
      bxor (bxor (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 2) k))
        (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k)) := by
  have hds : d + 2 * 1 < twopow k := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self k)
  have hsc := off_center_witt_scale_settled_below_threshold d 1 k J hJ (by omega)
    (by omega) hds hset
  rw [show d + 2 * 1 = d + 2 by omega] at hsc
  rw [hsc]
  exact periodic_colm1_dyadic_jump_eq_leftresponse_diff T P hP h d k ht hk

/-- **Exact Early `leftresponse` Inversion for Late Off-Center Witt Bit At the Right Threshold (`s = 1`, `d + 2 = J + 1`)**: under `CenterPeriodic T P`, when `T ≤ d + 1`, `d + 2 = J + 1 < 2^k`, and `SettledBy d (d + 1)` (`d + 2 ≤ k`), bit `J + 1 + 2^(k+1)` of `winWitt (d + 1 + 2^k) (2^k)` is the **negation** of the early `leftresponse` second difference `!(leftresponse (d + 2) (k + 1) ⊕ leftresponse (d + 2) k ⊕ leftresponse (d + 1) (k + 1) ⊕ leftresponse (d + 1) k)`. -/
theorem periodic_off_center_witt_at_threshold_eq_not_leftresponse (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hdJ : d + 2 = J + 1)
    (hJlt : J + 1 < twopow k) (hset : SettledBy d (d + 1)) :
    (winWitt ((d + 1) + twopow k) (twopow k)).testBit ((J + 1) + twopow (k + 1)) =
      !bxor (bxor (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 2) k))
        (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k)) := by
  have hsc := off_center_witt_scale_settled_at_threshold d 1 k J hJ (by omega)
    (by omega) hJlt hset
  rw [hsc, periodic_colm1_dyadic_jump_eq_leftresponse_diff T P hP h d k ht hk]

/-- **Early-Time Evaluation of the Threshold Defect `rdiag (J + 2) (t0 + 2^k) ⊕ rdiag (J + 2) t0` Before Cone Arrival (`2 * t0 ≤ J + 1`)**: whenever `2 * t0 ≤ J + 1` (`2 * t0 < J + 2`), the early-time term `rdiag (J + 2) t0` vanishes outside the light cone, so the `2^k`-defect on `rdiag (J + 2)` equals `rdiag (J + 2) (t0 + 2^k)` directly. -/
theorem rdiag_threshold_plus_two_defect_cone (t0 k J : Nat)
    (htJ : 2 * t0 ≤ J + 1) :
    bxor (rdiag (J + 2) (t0 + twopow k)) (rdiag (J + 2) t0) =
      rdiag (J + 2) (t0 + twopow k) := by
  rw [rdiag_gt_two_mul t0 (J + 2) (by omega), bxor_eq_xor, Bool.xor_false]

/-- **2-Step Running Transport of the `rdiag (J + 2)` Defect (`t ↦ t + 2`)**: for every `t : Nat`, stepping `t ↦ t + 2` changes the `2^k`-defect `rdiag (J + 2) (t + 2^k) ⊕ rdiag (J + 2) t` by `rdiag J t ⊕ rdiag J (t + 1)`. -/
theorem rdiag_threshold_plus_two_defect_two_step (t k J : Nat) (hJ : IsRightThreshold k J) :
    bxor (bxor (rdiag (J + 2) ((t + 2) + twopow k)) (rdiag (J + 2) (t + 2)))
      (bxor (rdiag (J + 2) (t + twopow k)) (rdiag (J + 2) t)) =
      bxor (rdiag J t) (rdiag J (t + 1)) := by
  have hs0 := rdiag_threshold_plus_two_defect_step t k J hJ
  have hs1 := rdiag_threshold_plus_two_defect_step (t + 1) k J hJ
  rw [show (t + 1) + 1 = t + 2 by omega] at hs1
  revert hs0 hs1
  simp only [bxor_eq_xor]
  cases rdiag (J + 2) ((t + 2) + twopow k) <;>
    cases rdiag (J + 2) (t + 2) <;>
    cases rdiag (J + 2) ((t + 1) + twopow k) <;>
    cases rdiag (J + 2) (t + 1) <;>
    cases rdiag (J + 2) (t + twopow k) <;>
    cases rdiag (J + 2) t <;>
    cases rdiag J t <;>
    cases rdiag J (t + 1) <;> decide

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_off_center_witt_below_threshold_eq_leftresponse`. -/
theorem periodic_off_center_witt_below_threshold_eq_leftresponse_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hdJ : d + 2 ≤ J)
    (hset : SettledBy d (d + 1)) :
    BitWinWittEq ((d + 1) + twopow k) (twopow k) ((d + 2) + twopow (k + 1))
      (bxor (bxor (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 2) k))
        (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_off_center_witt_below_threshold_eq_leftresponse T P hP h d k J hJ ht hk hdJ hset]

/-- Paper-facing `BitWinWittEq` wrapper for `periodic_off_center_witt_at_threshold_eq_not_leftresponse`. -/
theorem periodic_off_center_witt_at_threshold_eq_not_leftresponse_prop (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k J : Nat) (hJ : IsRightThreshold k J)
    (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hdJ : d + 2 = J + 1)
    (hJlt : J + 1 < twopow k) (hset : SettledBy d (d + 1)) :
    BitWinWittEq ((d + 1) + twopow k) (twopow k) ((J + 1) + twopow (k + 1))
      (!bxor (bxor (Rule30UOR.Scale.leftresponse (d + 2) (k + 1))
        (Rule30UOR.Scale.leftresponse (d + 2) k))
        (bxor (Rule30UOR.Scale.leftresponse (d + 1) (k + 1))
          (Rule30UOR.Scale.leftresponse (d + 1) k))) := by
  rw [BitWinWittEq, bit_eq_bton_testBit,
    periodic_off_center_witt_at_threshold_eq_not_leftresponse T P hP h d k J hJ ht hk hdJ hJlt hset]

end Rule30UOR.Interfaces
