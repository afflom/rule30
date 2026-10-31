module

public import Rule30UOR.Interfaces.Part14

/-!
# `Rule30UOR.Interfaces`, part 15

* Batch 59: Sub-Diagonal `d` Gate Determination of the Sub-Cone `p + d ≤ k` & Pure-Drive White-Prefix Shift Laws (`kit [33]`, 9.1177–9.1191)
* Batch 60: Super-Diagonal `(u, u + (B + 1))` Trapezoid Shielding & Right-Half Diagonal Gate Laws in `rdrv` (`kit [33]`, 9.1192–9.1206)
* Batch 61: White-Drive Black Persistence (`black_stays`), Inward Black-Front Arrival (`black_reaches_boundary`), and White-Run Synchronization of `rdrv` (`kit [33]`, 9.1207–9.1221)
* Batch 62: Autonomous Sub-Diagonal Recurrence, `accum_shift` Period-Doubling, and Sub-Diagonal OR-Determination in `rdrv` (`kit [33]`, 9.1222–9.1236)
* Batch 63: Right-Edge `rdiag` / `IsRightThreshold` Super-Diagonal Readouts & `2^k`-Periodicity Transfer into `rdrv` (`kit [33]`, 9.1237–9.1251)
* Batch 64: Gate-Free Inward Light-Cone Determination (`p + k ≤ B + 1`) from `RhBandAgree` & Single-Slice Refutation of `CenterPeriodic` (`kit [33]`, 9.1252–9.1266)
* Batch 65: General Column-`p` Inward Arrival, White-Triangle Equivalence & Spatial White-Diamond Super-Diagonal Corridors in `rdrv` (`kit [33]`, 9.1267–9.1281)
* Batch 66: Main-Diagonal & Sub-Diagonal `accum_shift` Defect Laws and Unconditional `2^(k + 1 + c)`-Periodicity in `u` of `rdrv` (`kit [33]`, 9.1282–9.1296)
* Batch 67: Exact Center-Drive Replication Along Dyadic Columns (`u = v * 2^((k + 1) + c)`), Column-`1` Dyadic Lift (`u = 1 + v * 2^((k + 1) + c)`), and All-`u` Sub-Diagonal Agreement (`kit [33]`, 9.1297–9.1311)
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

/-! ### Batch 59: Sub-Diagonal `d` Gate Determination of the Sub-Cone `p + d ≤ k` & Pure-Drive White-Prefix Shift Laws (`kit [33]`, 9.1177–9.1191) -/

/-- **All-Black First Sub-Diagonal of `rdrv td 0` When `(center td, center (td + 1)) = (false, true)` (`rdrv_subdiag_one_eq_true_of_false_true`, 9.1177, `kit [33]`)**:
    for all `td, u ∈ ℕ`, if `center td = false` and `center (td + 1) = true`, then `rdrv td 0 (u + 1) u = true` for ALL `u ∈ ℕ`! -/
theorem rdrv_subdiag_one_eq_true_of_false_true (td u : Nat)
    (hc0 : Rule30UOR.Core.center td = false)
    (hc1 : Rule30UOR.Core.center (td + 1) = true) :
    rdrv td 0 (u + 1) u = true := by
  induction u with
  | zero =>
    have h0 : 0 + 1 = 1 := by omega
    rw [h0, rdrv_col0, hc1]
  | succ u ih =>
    have h1 : (u + 1) + 1 = u + 2 := by omega
    rw [h1, rdrv_white_seed_subdiag_one_step td u, ih, hc0]
    rfl

/-- **Vanishing of `rdrv td 0 k p` Above Sub-Diagonal `d` Under a Length-`d` White Drive Prefix (`rdrv_white_seed_eq_false_of_white_drive_prefix`, 9.1178)**:
    for all `td, d, k, p ∈ ℕ`, if `∀ j < d, center (td + j) = false` and `k < p + d`, then `rdrv td 0 k p = false`! -/
theorem rdrv_white_seed_eq_false_of_white_drive_prefix (td d k p : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false)
    (hkp : k < p + d) :
    rdrv td 0 k p = false := by
  induction k generalizing p with
  | zero =>
    rcases p with _ | p
    · rw [rdrv_col0]
      exact hw 0 (by omega)
    · exact rdrv_white_seed_init_eq_false td (p + 1) (by omega)
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0]
      exact hw (k + 1) (by omega)
    · rw [rdrv_step_succ td 0 k p,
          ih p (by omega), ih (p + 1) (by omega), ih (p + 2) (by omega)]
      rfl

/-- **Exact Time-Shift Law of `rdrv td 0` Under a Length-`d` White Drive Prefix (`rdrv_white_seed_shift_of_white_drive_prefix`, 9.1179, `kit [33]`)**:
    for all `td, d, k, p ∈ ℕ`, if `∀ j < d, center (td + j) = false`, then `rdrv td 0 (d + k) p = rdrv (td + d) 0 k p`! -/
theorem rdrv_white_seed_shift_of_white_drive_prefix (td d k p : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false) :
    rdrv td 0 (d + k) p = rdrv (td + d) 0 k p := by
  induction k generalizing p with
  | zero =>
    have h0 : d + 0 = d := by omega
    rw [h0]
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0, Nat.add_zero]
    · rw [rdrv_white_seed_eq_false_of_white_drive_prefix td d d (p + 1) hw (by omega),
          rdrv_white_seed_init_eq_false (td + d) (p + 1) (by omega)]
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0, Nat.add_assoc]
    · have h1 : d + (k + 1) = (d + k) + 1 := by omega
      rw [h1, rdrv_step_succ td 0 (d + k) p, rdrv_step_succ (td + d) 0 k p,
          ih p, ih (p + 1), ih (p + 2)]

/-- **Sub-Diagonal `d` Constancy of `rdrv td 0` Under a Length-`d` White Drive Prefix (`rdrv_white_seed_subdiag_eq_center_of_white_drive_prefix`, 9.1180)**:
    for all `td, d, u ∈ ℕ`, if `∀ j < d, center (td + j) = false`, then `rdrv td 0 (u + d) u = center (td + d)` for all `u`! -/
theorem rdrv_white_seed_subdiag_eq_center_of_white_drive_prefix (td d u : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false) :
    rdrv td 0 (u + d) u = Rule30UOR.Core.center (td + d) := by
  have h1 : u + d = d + u := by omega
  rw [h1, rdrv_white_seed_shift_of_white_drive_prefix td d u u hw,
      rdrv_white_seed_diag_eq_center (td + d) u]

/-- **Sub-Diagonal `d` Gate Determination of the Entire Sub-Cone `p + d ≤ k` (`rdrv_subcone_agree_of_subdiag_gate`, 9.1181, `kit [33]`)**:
    for all `td, tx2, tx, d, k, p ∈ ℕ`, if for all `1 ≤ u` with `u + d ≤ k`, `rdrv td tx2 (u + d) u = rdrv td tx (u + d) u` and (`rdrv td tx (u + d) u = false → rdrv td tx2 (u + d) (u + 1) = rdrv td tx (u + d) (u + 1)`), then for ALL `p` with `p + d ≤ k`, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_subcone_agree_of_subdiag_gate (td tx2 tx d k p : Nat)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ k →
      rdrv td tx2 (u + d) u = rdrv td tx (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ k →
      rdrv td tx (u + d) u = false →
      rdrv td tx2 (u + d) (u + 1) = rdrv td tx (u + d) (u + 1))
    (hpk : p + d ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  induction k generalizing p with
  | zero =>
    have hp0 : p = 0 := by omega
    subst hp0
    rw [rdrv_col0, rdrv_col0]
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · by_cases heq : (p + 1) + d = k + 1
      · rw [← heq]
        exact hdiag (p + 1) (by omega) (by omega)
      · have hpk' : (p + 1) + d ≤ k := by omega
        rw [rdrv_step_succ td tx2 k p, rdrv_step_succ td tx k p]
        have ih0 := ih p (fun u hu1 hu2 => hdiag u hu1 (by omega))
          (fun u hu1 hu2 => hgate u hu1 (by omega)) (by omega)
        have ih1 := ih (p + 1) (fun u hu1 hu2 => hdiag u hu1 (by omega))
          (fun u hu1 hu2 => hgate u hu1 (by omega)) hpk'
        rw [ih0, ih1]
        by_cases hlt : (p + 2) + d ≤ k
        · have ih2 := ih (p + 2) (fun u hu1 hu2 => hdiag u hu1 (by omega))
            (fun u hu1 hu2 => hgate u hu1 (by omega)) hlt
          rw [ih2]
        · have hkd : k = (p + 1) + d := by omega
          rw [hkd]
          cases hkk : rdrv td tx ((p + 1) + d) (p + 1)
          · rw [hgate (p + 1) (by omega) (by omega) hkk]
          · rw [Bool.true_or, Bool.true_or]

/-- **Total Sub-Cone Shielding `p + d ≤ k` by a Black Sub-Diagonal `d` (`rdrv_subcone_agree_of_black_subdiag`, 9.1182, `kit [33]`)**:
    for all `td, tx2, tx, d, k, p ∈ ℕ`, if `rdrv td tx2 (u + d) u = true` and `rdrv td tx (u + d) u = true` for all `1 ≤ u` with `u + d ≤ k`, then for ALL `p` with `p + d ≤ k`, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_subcone_agree_of_black_subdiag (td tx2 tx d k p : Nat)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ k → rdrv td tx2 (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ k → rdrv td tx (u + d) u = true)
    (hpk : p + d ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  refine rdrv_subcone_agree_of_subdiag_gate td tx2 tx d k p
    (fun u hu1 hu2 => by rw [hb2 u hu1 hu2, hb1 u hu1 hu2])
    (fun u hu1 hu2 hw => ?_) hpk
  rw [hb1 u hu1 hu2] at hw
  cases hw

/-- **Collapse of the Sub-Cone `p + d ≤ k` to `rdrv td 0` Under a White Prefix and Black Sub-Diagonal `d` (`rdrv_subcone_eq_white_seed_of_white_prefix_and_black_subdiag`, 9.1183)**:
    for all `td, tx, d, k, p ∈ ℕ`, if `∀ j < d, center (td + j) = false`, `center (td + d) = true`, and `∀ u, 1 ≤ u → u + d ≤ k → rdrv td tx (u + d) u = true`, then for all `p + d ≤ k`, `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_subcone_eq_white_seed_of_white_prefix_and_black_subdiag (td tx d k p : Nat)
    (hw : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = false)
    (hcd : Rule30UOR.Core.center (td + d) = true)
    (hb : ∀ u : Nat, 1 ≤ u → u + d ≤ k → rdrv td tx (u + d) u = true)
    (hpk : p + d ≤ k) :
    rdrv td tx k p = rdrv td 0 k p := by
  refine rdrv_subcone_agree_of_black_subdiag td tx 0 d k p hb (fun u _ _ => ?_) hpk
  rw [rdrv_white_seed_subdiag_eq_center_of_white_drive_prefix td d u hw, hcd]

/-- **Collapse of the Sub-Cone `p + 1 ≤ k` to `rdrv td 0` Under `(center td, center (td + 1)) = (false, true)` and a Black Sub-Diagonal `1` (`rdrv_subcone_one_eq_white_seed_of_false_true_and_black_subdiag_one`, 9.1184)**:
    for all `td, tx, k, p ∈ ℕ`, if `center td = false`, `center (td + 1) = true`, and `∀ u, 1 ≤ u → u + 1 ≤ k → rdrv td tx (u + 1) u = true`, then for all `p + 1 ≤ k`, `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_subcone_one_eq_white_seed_of_false_true_and_black_subdiag_one (td tx k p : Nat)
    (hc0 : Rule30UOR.Core.center td = false)
    (hc1 : Rule30UOR.Core.center (td + 1) = true)
    (hb : ∀ u : Nat, 1 ≤ u → u + 1 ≤ k → rdrv td tx (u + 1) u = true)
    (hpk : p + 1 ≤ k) :
    rdrv td tx k p = rdrv td 0 k p := by
  refine rdrv_subcone_agree_of_black_subdiag td tx 0 1 k p hb (fun u _ _ => ?_) hpk
  exact rdrv_subdiag_one_eq_true_of_false_true td u hc0 hc1

/-- **Derivation of `maskparity · 0` Agreement from Sub-Diagonal `d` Gate Agreement (`periodic_maskparity_zero_agree_of_subdiag_gate`, 9.1185, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, d, s ∈ ℕ` with `T ≤ t` and `1 + d ≤ s`, if the sub-diagonal `d` gate condition holds up to `s`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_subdiag_gate
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t d s : Nat) (ht : T ≤ t) (hs : 1 + d ≤ s)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ s →
      rdrv t (t + m * P) (u + d) u = rdrv t t (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ s →
      rdrv t t (u + d) u = false →
      rdrv t (t + m * P) (u + d) (u + 1) = rdrv t t (u + d) (u + 1)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_subcone_agree_of_subdiag_gate t (t + m * P) t d s 1 hdiag hgate hs

/-- **Derivation of `maskparity · 0` Agreement from a Black Sub-Diagonal `d` (`periodic_maskparity_zero_agree_of_black_subdiag`, 9.1186)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, d, s ∈ ℕ` with `T ≤ t` and `1 + d ≤ s`, if `rdrv t (t + m * P) (u + d) u = true` and `rdrv t t (u + d) u = true` for all `1 ≤ u` with `u + d ≤ s`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_black_subdiag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t d s : Nat) (ht : T ≤ t) (hs : 1 + d ≤ s)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ s → rdrv t (t + m * P) (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ s → rdrv t t (u + d) u = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_subcone_agree_of_black_subdiag t (t + m * P) t d s 1 hb2 hb1 hs

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from Sub-Diagonal `d` Gate Agreement (`not_centerPeriodic_of_subdiag_gate_at_zero_diag`, 9.1187)**:
    if `T ≤ t`, `t + (d + 1) = z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and the sub-diagonal `d` gate holds from `t` over `u + d ≤ S + (d + 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_subdiag_gate_at_zero_diag
    (T P m z p t d S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htd : t + (d + 1) = z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) →
      rdrv t (t + m * P) (u + d) u = rdrv t t (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) →
      rdrv t t (u + d) u = false →
      rdrv t (t + m * P) (u + d) (u + 1) = rdrv t t (u + d) (u + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm (by omega) hz hd hset1 hset2 hS (fun s hs => ?_) hper
  have h1 : (z + (p + 1)) + s = t + (s + (d + 1)) := by omega
  rw [h1]
  exact periodic_maskparity_zero_agree_of_subdiag_gate T P hP hper m t d (s + (d + 1)) ht (by omega)
    (fun u hu1 hu2 => hdiag u hu1 (by omega))
    (fun u hu1 hu2 => hgate u hu1 (by omega))

theorem not_centerPeriodic_of_subdiag_gate_at_zero_diag_prop
    (T P m z p t d S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htd : t + (d + 1) = z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hdiag : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) →
      rdrv t (t + m * P) (u + d) u = rdrv t t (u + d) u)
    (hgate : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) →
      rdrv t t (u + d) u = false →
      rdrv t (t + m * P) (u + d) (u + 1) = rdrv t t (u + d) (u + 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_subdiag_gate_at_zero_diag T P m z p t d S hP hm ht htd
    hz hd hset1 hset2 hS hdiag hgate

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from a Black Sub-Diagonal `d` (`not_centerPeriodic_of_black_subdiag_at_zero_diag`, 9.1188)**:
    if `T ≤ t`, `t + (d + 1) = z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and sub-diagonal `d` of `rdrv t (t + m * P)` and `rdrv t t` is black over `u + d ≤ S + (d + 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_subdiag_at_zero_diag
    (T P m z p t d S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htd : t + (d + 1) = z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) → rdrv t (t + m * P) (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) → rdrv t t (u + d) u = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_subdiag_gate_at_zero_diag T P m z p t d S hP hm ht htd hz hd hset1 hset2 hS
    (fun u hu1 hu2 => by rw [hb2 u hu1 hu2, hb1 u hu1 hu2])
    (fun u hu1 hu2 hw => ?_)
  rw [hb1 u hu1 hu2] at hw
  cases hw

theorem not_centerPeriodic_of_black_subdiag_at_zero_diag_prop
    (T P m z p t d S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htd : t + (d + 1) = z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) → rdrv t (t + m * P) (u + d) u = true)
    (hb1 : ∀ u : Nat, 1 ≤ u → u + d ≤ S + (d + 1) → rdrv t t (u + d) u = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_subdiag_at_zero_diag T P m z p t d S hP hm ht htd
    hz hd hset1 hset2 hS hb2 hb1

/-- **Black Wavefront Generation at a White `rhCenter` Cell When the Drive Flips at `d` (`rdrv_drive_wavefront_eq_true_of_first_diff_and_white_rhCenter`, 9.1189, `kit [33]`)**:
    for all `td, tx, d, p ∈ ℕ`, if `∀ j < d, center (td + j) = center (tx + j)`, `center (td + d) = !(center (tx + d))`, and `rhCenter (tx + (p + d)) p = false`, then `rdrv td tx (p + d) p = true`! -/
theorem rdrv_drive_wavefront_eq_true_of_first_diff_and_white_rhCenter (td tx d p : Nat)
    (hc : ∀ j : Nat, j < d → Rule30UOR.Core.center (td + j) = Rule30UOR.Core.center (tx + j))
    (hdiff : Rule30UOR.Core.center (td + d) = !(Rule30UOR.Core.center (tx + d)))
    (hw : rhCenter (tx + (p + d)) p = false) :
    rdrv td tx (p + d) p = true := by
  rw [rdrv_drive_wavefront_eq_rhCenter_xor td tx d p hc, hw, hdiff]
  cases Rule30UOR.Core.center (tx + d) <;> rfl

/-- **Exact Readout `rdrv td tx (p + d) p = rhCenter (tx + (p + d)) p` Under Center Prefix Agreement Up to `d` (`rdrv_drive_wavefront_eq_rhCenter_of_center_prefix_eq`, 9.1190)**:
    for all `td, tx, d, p ∈ ℕ`, if `∀ j ≤ d, center (td + j) = center (tx + j)`, then `rdrv td tx (p + d) p = rhCenter (tx + (p + d)) p`! -/
theorem rdrv_drive_wavefront_eq_rhCenter_of_center_prefix_eq (td tx d p : Nat)
    (hc : ∀ j : Nat, j ≤ d → Rule30UOR.Core.center (td + j) = Rule30UOR.Core.center (tx + j)) :
    rdrv td tx (p + d) p = rhCenter (tx + (p + d)) p := by
  rw [rdrv_drive_wavefront_eq_rhCenter_xor td tx d p (fun j hj => hc j (by omega)),
      hc d (by omega)]
  cases rhCenter (tx + (p + d)) p <;> cases Rule30UOR.Core.center (tx + d) <;> rfl

/-- **Exact Sub-Diagonal Readout of `rdrv t (t + m * P)` Under `CenterPeriodic` (`periodic_rdrv_subdiag_eq_rhCenter`, 9.1191)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, d, p ∈ ℕ` with `T ≤ t`, `rdrv t (t + m * P) (p + d) p = rhCenter ((t + m * P) + (p + d)) p`! -/
theorem periodic_rdrv_subdiag_eq_rhCenter
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t d p : Nat) (ht : T ≤ t) :
    rdrv t (t + m * P) (p + d) p = rhCenter ((t + m * P) + (p + d)) p :=
  (periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t (p + d) p ht).symm

/-! ### Batch 60: Super-Diagonal `(u, u + (B + 1))` Trapezoid Shielding & Right-Half Diagonal Gate Laws in `rdrv` (`kit [33]`, 9.1192–9.1206) -/

/-- **Expanding Trapezoid Determination `p ≤ k + (B + 1)` from `RhBandAgree tx Q 1 B` and a Super-Diagonal Gate on `(u, u + (B + 1))` (`rdrv_trapezoid_agree_of_superdiag_gate`, 9.1192, `kit [33]`)**:
    for all `td, tx, Q, B, k, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at step `0` and for all `u ≤ k`, `rhCenter ((tx + Q) + u) (u + (B + 1)) = rhCenter (tx + u) (u + (B + 1))` and (`rhCenter (tx + u) (u + (B + 1)) = false → rhCenter ((tx + Q) + u) (u + (B + 2)) = rhCenter (tx + u) (u + (B + 2))`), then for ALL `p ≤ k + (B + 1)`, `rdrv td (tx + Q) k p = rdrv td tx k p`! -/
theorem rdrv_trapezoid_agree_of_superdiag_gate (td tx Q B k p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hc1 : ∀ u : Nat, u ≤ k →
      rhCenter ((tx + Q) + u) (u + (B + 1)) = rhCenter (tx + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ k →
      rhCenter (tx + u) (u + (B + 1)) = false →
      rhCenter ((tx + Q) + u) (u + (B + 2)) = rhCenter (tx + u) (u + (B + 2)))
    (hpk : p ≤ k + (B + 1)) :
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
    · by_cases heq : p + 1 = (k + 1) + (B + 1)
      · rw [heq,
            rdrv_outside_cone_eq_rhCenter td (tx + Q) (k + 1) ((k + 1) + (B + 1)) (by omega),
            rdrv_outside_cone_eq_rhCenter td tx (k + 1) ((k + 1) + (B + 1)) (by omega)]
        exact hc1 (k + 1) (by omega)
      · have hpk' : p + 1 ≤ k + (B + 1) := by omega
        rw [rdrv_step_succ td (tx + Q) k p, rdrv_step_succ td tx k p]
        have ih0 := ih p (fun u hu => hc1 u (by omega))
          (fun u hu => hc2 u (by omega)) (by omega)
        have ih1 := ih (p + 1) (fun u hu => hc1 u (by omega))
          (fun u hu => hc2 u (by omega)) hpk'
        rw [ih0, ih1]
        by_cases hlt : p + 2 ≤ k + (B + 1)
        · have ih2 := ih (p + 2) (fun u hu => hc1 u (by omega))
            (fun u hu => hc2 u (by omega)) hlt
          rw [ih2]
        · have hp1 : p + 1 = k + (B + 1) := by omega
          have hp2 : p + 2 = k + (B + 2) := by omega
          rw [hp1, hp2,
              rdrv_outside_cone_eq_rhCenter td tx k (k + (B + 1)) (by omega),
              rdrv_outside_cone_eq_rhCenter td (tx + Q) k (k + (B + 2)) (by omega),
              rdrv_outside_cone_eq_rhCenter td tx k (k + (B + 2)) (by omega)]
          cases hkk : rhCenter (tx + k) (k + (B + 1))
          · rw [hc2 k (by omega) hkk]
          · rw [Bool.true_or, Bool.true_or]

/-- **Expanding Trapezoid Shielding `p ≤ k + (B + 1)` by a Black Super-Diagonal `(u, u + (B + 1))` (`rdrv_trapezoid_agree_of_black_superdiag`, 9.1193, `kit [33]`)**:
    for all `td, tx, Q, B, k, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at step `0` and `rhCenter ((tx + Q) + u) (u + (B + 1)) = true` and `rhCenter (tx + u) (u + (B + 1)) = true` for all `u ≤ k`, then for ALL `p ≤ k + (B + 1)`, `rdrv td (tx + Q) k p = rdrv td tx k p`! -/
theorem rdrv_trapezoid_agree_of_black_superdiag (td tx Q B k p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hb2 : ∀ u : Nat, u ≤ k → rhCenter ((tx + Q) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ k → rhCenter (tx + u) (u + (B + 1)) = true)
    (hpk : p ≤ k + (B + 1)) :
    rdrv td (tx + Q) k p = rdrv td tx k p := by
  refine rdrv_trapezoid_agree_of_superdiag_gate td tx Q B k p hband
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_) hpk
  rw [hb1 u hu] at hw
  cases hw

/-- **Exact Collapse of the Expanding Trapezoid `p ≤ k + (B + 1)` to `rdrv td 0` Under an Initial White Band and 2-Cell White Super-Diagonal Corridor (`rdrv_trapezoid_eq_white_seed_of_white_band_and_corridor`, 9.1194, `kit [33]`)**:
    for all `td, tx, B, k, p ∈ ℕ`, if `∀ i ≤ B, rhCenter tx (1 + i) = false` and `∀ u ≤ k, rhCenter (tx + u) (u + (B + 1)) = false ∧ rhCenter (tx + u) (u + (B + 2)) = false`, then for ALL `p ≤ k + (B + 1)`, `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_trapezoid_eq_white_seed_of_white_band_and_corridor (td tx B k p : Nat)
    (hwb : ∀ i : Nat, i ≤ B → rhCenter tx (1 + i) = false)
    (hwc : ∀ u : Nat, u ≤ k →
      rhCenter (tx + u) (u + (B + 1)) = false ∧ rhCenter (tx + u) (u + (B + 2)) = false)
    (hpk : p ≤ k + (B + 1)) :
    rdrv td tx k p = rdrv td 0 k p := by
  have hband : RhBandAgree 0 tx 1 B := by
    intro i hi
    rw [Nat.zero_add, hwb i hi, rhCenter_gt_eq_false 0 (1 + i) (by omega)]
  have h := rdrv_trapezoid_agree_of_superdiag_gate td 0 tx B k p hband
    (fun u hu => by
      rw [Nat.zero_add, Nat.zero_add, (hwc u hu).1,
          rhCenter_gt_eq_false u (u + (B + 1)) (by omega)])
    (fun u hu _ => by
      rw [Nat.zero_add, Nat.zero_add, (hwc u hu).2,
          rhCenter_gt_eq_false u (u + (B + 2)) (by omega)]) hpk
  rwa [Nat.zero_add] at h

/-- **Exact Collapse of `rhCenter (t + k) p` to `rdrv t 0 k p` Inside the Expanding Trapezoid `p ≤ k + (B + 1)` (`rhCenter_trapezoid_eq_white_seed_of_white_band_and_corridor`, 9.1195)**:
    for all `t, B, k, p ∈ ℕ`, if `∀ i ≤ B, rhCenter t (1 + i) = false` and `∀ u ≤ k, rhCenter (t + u) (u + (B + 1)) = false ∧ rhCenter (t + u) (u + (B + 2)) = false`, then for ALL `p ≤ k + (B + 1)`, `rhCenter (t + k) p = rdrv t 0 k p`! -/
theorem rhCenter_trapezoid_eq_white_seed_of_white_band_and_corridor (t B k p : Nat)
    (hwb : ∀ i : Nat, i ≤ B → rhCenter t (1 + i) = false)
    (hwc : ∀ u : Nat, u ≤ k →
      rhCenter (t + u) (u + (B + 1)) = false ∧ rhCenter (t + u) (u + (B + 2)) = false)
    (hpk : p ≤ k + (B + 1)) :
    rhCenter (t + k) p = rdrv t 0 k p := by
  rw [← rdrv_diag_eq_rhCenter t k p]
  exact rdrv_trapezoid_eq_white_seed_of_white_band_and_corridor t t B k p hwb hwc hpk

/-- **Derivation of `maskparity · 0` Agreement from `RhBandAgree t (m * P) 1 B` and a Super-Diagonal `(u, u + (B + 1))` Gate (`periodic_maskparity_zero_agree_of_superdiag_gate`, 9.1196, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` and the super-diagonal `B + 1` gate holds up to `s`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_superdiag_gate
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ s →
      rhCenter ((t + m * P) + u) (u + (B + 1)) = rhCenter (t + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ s →
      rhCenter (t + u) (u + (B + 1)) = false →
      rhCenter ((t + m * P) + u) (u + (B + 2)) = rhCenter (t + u) (u + (B + 2))) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_trapezoid_agree_of_superdiag_gate t t (m * P) B s 1 hband hc1 hc2 (by omega)

/-- **Derivation of `maskparity · 0` Agreement from `RhBandAgree t (m * P) 1 B` and a Black Super-Diagonal `(u, u + (B + 1))` (`periodic_maskparity_zero_agree_of_black_superdiag`, 9.1197)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` and `rhCenter ((t + m * P) + u) (u + (B + 1)) = true` and `rhCenter (t + u) (u + (B + 1)) = true` for all `u ≤ s`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_black_superdiag
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hb2 : ∀ u : Nat, u ≤ s → rhCenter ((t + m * P) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ s → rhCenter (t + u) (u + (B + 1)) = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_trapezoid_agree_of_black_superdiag t t (m * P) B s 1 hband hb2 hb1 (by omega)

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from `RhBandAgree` and a Super-Diagonal `(u, u + (B + 1))` Gate (`not_centerPeriodic_of_superdiag_gate_at_zero_diag`, 9.1198)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, `RhBandAgree (z + (p + 1)) (m * P) 1 B`, and the super-diagonal `B + 1` gate holds over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_superdiag_gate_at_zero_diag
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 1)) =
      rhCenter ((z + (p + 1)) + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((z + (p + 1)) + u) (u + (B + 1)) = false →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 2)) =
      rhCenter ((z + (p + 1)) + u) (u + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_superdiag_gate T P hP hper m (z + (p + 1)) B s ht hband
    (fun u hu => hc1 u (by omega))
    (fun u hu => hc2 u (by omega))

theorem not_centerPeriodic_of_superdiag_gate_at_zero_diag_prop
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 1)) =
      rhCenter ((z + (p + 1)) + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((z + (p + 1)) + u) (u + (B + 1)) = false →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 2)) =
      rhCenter ((z + (p + 1)) + u) (u + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_superdiag_gate_at_zero_diag T P m z p B S hP hm ht
    hz hd hset1 hset2 hS hband hc1 hc2

/-- **Zero-Diagonal Refutation of `CenterPeriodic` from `RhBandAgree` and a Black Super-Diagonal `(u, u + (B + 1))` (`not_centerPeriodic_of_black_superdiag_at_zero_diag`, 9.1199)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, `RhBandAgree (z + (p + 1)) (m * P) 1 B`, and super-diagonal `B + 1` is black over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_superdiag_at_zero_diag
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hb2 : ∀ u : Nat, u ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      rhCenter ((z + (p + 1)) + u) (u + (B + 1)) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_superdiag_gate_at_zero_diag T P m z p B S hP hm ht hz hd hset1 hset2 hS hband
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_)
  rw [hb1 u hu] at hw
  cases hw

theorem not_centerPeriodic_of_black_superdiag_at_zero_diag_prop
    (T P m z p B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hb2 : ∀ u : Nat, u ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + (B + 1)) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      rhCenter ((z + (p + 1)) + u) (u + (B + 1)) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_superdiag_at_zero_diag T P m z p B S hP hm ht
    hz hd hset1 hset2 hS hband hb2 hb1

/-- **Full-Horizon (`s ≥ 0`) Derivation of `maskparity · 0` Agreement from 2-Cell Super-Diagonal Corridor Agreement (`periodic_maskparity_zero_agree_of_corridor_gate_all`, 9.1200, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t` (including `s = 0`!), if for all `u ≤ s`, `rhCenter ((t + m * P) + u) (u + 1) = rhCenter (t + u) (u + 1)` and (`rhCenter (t + u) (u + 1) = false → rhCenter ((t + m * P) + u) (u + 2) = rhCenter (t + u) (u + 2)`), then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_corridor_gate_all
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hc1 : ∀ u : Nat, u ≤ s → rhCenter ((t + m * P) + u) (u + 1) = rhCenter (t + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ s →
      rhCenter (t + u) (u + 1) = false →
      rhCenter ((t + m * P) + u) (u + 2) = rhCenter (t + u) (u + 2)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hband : RhBandAgree t (m * P) 1 0 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    have h0 := hc1 0 (by omega)
    have ha1 : (t + m * P) + 0 = t + m * P := by omega
    have ha2 : t + 0 = t := by omega
    have ha3 : 0 + 1 = 1 + 0 := by omega
    rw [ha1, ha2, ha3] at h0
    exact h0
  exact periodic_maskparity_zero_agree_of_superdiag_gate T P hP hper m t 0 s ht hband hc1 hc2

/-- **Full-Horizon (`s ≥ 0`) Derivation of `maskparity · 0` Agreement from a Single Black First Super-Diagonal (`periodic_maskparity_zero_agree_of_black_first_superdiag_all`, 9.1201)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t` (including `s = 0`!), if `rhCenter ((t + m * P) + u) (u + 1) = true` and `rhCenter (t + u) (u + 1) = true` for all `u ≤ s`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_black_first_superdiag_all
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hb2 : ∀ u : Nat, u ≤ s → rhCenter ((t + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ s → rhCenter (t + u) (u + 1) = true) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_corridor_gate_all T P hP hper m t s ht
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_)
  rw [hb1 u hu] at hw
  cases hw

/-- **Direct Zero-Diagonal Refutation of `CenterPeriodic` at `z + (p + 1)` from the 2-Cell Super-Diagonal Corridor Gate (`not_centerPeriodic_of_corridor_gate_at_zero_diag_direct`, 9.1202)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and the 2-cell super-diagonal corridor gate holds at `z + (p + 1)` over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_corridor_gate_at_zero_diag_direct
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + 1) = rhCenter ((z + (p + 1)) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((z + (p + 1)) + u) (u + 1) = false →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + 2) = rhCenter ((z + (p + 1)) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_corridor_gate_all T P hP hper m (z + (p + 1)) s ht
    (fun u hu => hc1 u (by omega))
    (fun u hu => hc2 u (by omega))

theorem not_centerPeriodic_of_corridor_gate_at_zero_diag_direct_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + 1) = rhCenter ((z + (p + 1)) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((z + (p + 1)) + u) (u + 1) = false →
      rhCenter (((z + (p + 1)) + m * P) + u) (u + 2) = rhCenter ((z + (p + 1)) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_corridor_gate_at_zero_diag_direct T P m z p S hP hm ht
    hz hd hset1 hset2 hS hc1 hc2

/-- **Direct Zero-Diagonal Refutation of `CenterPeriodic` at `z + (p + 1)` from a Single Black First Super-Diagonal (`not_centerPeriodic_of_black_first_superdiag_at_zero_diag_direct`, 9.1203)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ S + 1`, and the first super-diagonal `(u, u + 1)` is black at `z + (p + 1)` over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_first_superdiag_at_zero_diag_direct
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S → rhCenter (((z + (p + 1)) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S → rhCenter ((z + (p + 1)) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_corridor_gate_at_zero_diag_direct T P m z p S hP hm ht hz hd hset1 hset2 hS
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_)
  rw [hb1 u hu] at hw
  cases hw

theorem not_centerPeriodic_of_black_first_superdiag_at_zero_diag_direct_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S → rhCenter (((z + (p + 1)) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S → rhCenter ((z + (p + 1)) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_first_superdiag_at_zero_diag_direct T P m z p S hP hm ht
    hz hd hset1 hset2 hS hb2 hb1

/-- **Dyadic-Window Refutation of `CenterPeriodic` from the 2-Cell Super-Diagonal Corridor Gate (`not_centerPeriodic_of_corridor_gate_sub_twopow`, 9.1204)**:
    if `0 < P`, `0 < m`, `m * P ≤ 2^k`, `T + m * P ≤ 2^k`, `2^k ≤ S + 1`, and the 2-cell super-diagonal corridor gate holds at `2^k - m * P` over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_corridor_gate_sub_twopow
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + 1) =
      rhCenter ((twopow k - m * P) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((twopow k - m * P) + u) (u + 1) = false →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + 2) =
      rhCenter ((twopow k - m * P) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_sub_twopow
    T P m k S hP hm ht hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_corridor_gate_all T P hP hper m (twopow k - m * P) s (by have := hmP; omega)
    (fun u hu => hc1 u (by omega))
    (fun u hu => hc2 u (by omega))

theorem not_centerPeriodic_of_corridor_gate_sub_twopow_prop
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + 1) =
      rhCenter ((twopow k - m * P) + u) (u + 1))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((twopow k - m * P) + u) (u + 1) = false →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + 2) =
      rhCenter ((twopow k - m * P) + u) (u + 2)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_corridor_gate_sub_twopow T P m k S hP hm hmP ht hS hc1 hc2

/-- **Dyadic-Window Refutation of `CenterPeriodic` from a Single Black First Super-Diagonal (`not_centerPeriodic_of_black_first_superdiag_sub_twopow`, 9.1205)**:
    if `0 < P`, `0 < m`, `m * P ≤ 2^k`, `T + m * P ≤ 2^k`, `2^k ≤ S + 1`, and the first super-diagonal `(u, u + 1)` is black at `2^k - m * P` over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_black_first_superdiag_sub_twopow
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      rhCenter ((twopow k - m * P) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_corridor_gate_sub_twopow T P m k S hP hm hmP ht hS
    (fun u hu => by rw [hb2 u hu, hb1 u hu])
    (fun u hu hw => ?_)
  rw [hb1 u hu] at hw
  cases hw

theorem not_centerPeriodic_of_black_first_superdiag_sub_twopow_prop
    (T P m k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hb2 : ∀ u : Nat, u ≤ S →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + 1) = true)
    (hb1 : ∀ u : Nat, u ≤ S →
      rhCenter ((twopow k - m * P) + u) (u + 1) = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_black_first_superdiag_sub_twopow T P m k S hP hm hmP ht hS hb2 hb1

/-- **Dyadic-Window Refutation of `CenterPeriodic` from `RhBandAgree` and a Super-Diagonal `(u, u + (B + 1))` Gate (`not_centerPeriodic_of_superdiag_gate_sub_twopow`, 9.1206)**:
    if `0 < P`, `0 < m`, `m * P ≤ 2^k`, `T + m * P ≤ 2^k`, `2^k ≤ S + 1`, `RhBandAgree (2^k - m * P) (m * P) 1 B`, and the super-diagonal `B + 1` gate holds over `u ≤ S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_superdiag_gate_sub_twopow
    (T P m k B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hband : RhBandAgree (twopow k - m * P) (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + (B + 1)) =
      rhCenter ((twopow k - m * P) + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((twopow k - m * P) + u) (u + (B + 1)) = false →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + (B + 2)) =
      rhCenter ((twopow k - m * P) + u) (u + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_sub_twopow
    T P m k S hP hm ht hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_superdiag_gate T P hP hper m (twopow k - m * P) B s (by have := hmP; omega) hband
    (fun u hu => hc1 u (by omega))
    (fun u hu => hc2 u (by omega))

theorem not_centerPeriodic_of_superdiag_gate_sub_twopow_prop
    (T P m k B S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hmP : m * P ≤ twopow k) (ht : T + m * P ≤ twopow k)
    (hS : twopow k ≤ S + 1)
    (hband : RhBandAgree (twopow k - m * P) (m * P) 1 B)
    (hc1 : ∀ u : Nat, u ≤ S →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + (B + 1)) =
      rhCenter ((twopow k - m * P) + u) (u + (B + 1)))
    (hc2 : ∀ u : Nat, u ≤ S →
      rhCenter ((twopow k - m * P) + u) (u + (B + 1)) = false →
      rhCenter (((twopow k - m * P) + m * P) + u) (u + (B + 2)) =
      rhCenter ((twopow k - m * P) + u) (u + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_superdiag_gate_sub_twopow T P m k B S hP hm hmP ht hS hband hc1 hc2

/-! ### Batch 61: White-Drive Black Persistence (`black_stays`), Inward Black-Front Arrival (`black_reaches_boundary`), and White-Run Synchronization of `rdrv` (`kit [33]`, 9.1207–9.1221) -/

/-- **1-Step Black Persistence Behind a Left White Cell in `rdrv` (`rdrv_black_stays_step`, 9.1207, `kit [33]`)**:
    for all `td, tx, k, p ∈ ℕ`, if `rdrv td tx k p = false` and `rdrv td tx k (p + 1) = true`, then `rdrv td tx (k + 1) (p + 1) = true`! -/
theorem rdrv_black_stays_step (td tx k p : Nat)
    (hw : rdrv td tx k p = false)
    (hb : rdrv td tx k (p + 1) = true) :
    rdrv td tx (k + 1) (p + 1) = true := by
  rw [rdrv_step_succ td tx k p, hw, hb, Bool.true_or, bxor_eq_xor]
  rfl

/-- **Multi-Step Black Persistence Behind a White Left Boundary Run in `rdrv` (`rdrv_black_stays`, 9.1208, `Rule30FiniteBlackRuns.black_stays` in `rdrv`, `kit [33]`)**:
    for all `td, tx, a, p, n, k ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < n`, `rdrv td tx a (p + 1) = true`, and `k ≤ n`, then `rdrv td tx (a + k) (p + 1) = true`! -/
theorem rdrv_black_stays (td tx a p n k : Nat)
    (hw : ∀ s : Nat, s < n → rdrv td tx (a + s) p = false)
    (hb : rdrv td tx a (p + 1) = true)
    (hk : k ≤ n) :
    rdrv td tx (a + k) (p + 1) = true := by
  induction k with
  | zero =>
    rwa [Nat.add_zero]
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 by omega]
    exact rdrv_black_stays_step td tx (a + k) p (hw k (by omega)) (ih (by omega))

/-- **Column-`1` Black Persistence Across a White Drive Run in `rdrv` (`rdrv_col_one_black_stays_of_white_drive`, 9.1209, `kit [33]`)**:
    for all `td, tx, a, r, k ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `rdrv td tx a 1 = true`, and `k ≤ r`, then `rdrv td tx (a + k) 1 = true`! -/
theorem rdrv_col_one_black_stays_of_white_drive (td tx a r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb : rdrv td tx a 1 = true)
    (hk : k ≤ r) :
    rdrv td tx (a + k) 1 = true := by
  refine rdrv_black_stays td tx a 0 r k (fun s hs => ?_) hb hk
  rw [rdrv_col0]
  exact hw s hs

/-- **Column-`1` Reset to `false` at the Black Drive End of a White Drive Run in `rdrv` (`rdrv_col_one_flip_after_white_drive`, 9.1210, `kit [33]`)**:
    for all `td, tx, a, r ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `center (td + (a + r)) = true`, and `rdrv td tx a 1 = true`, then `rdrv td tx (a + (r + 1)) 1 = false`! -/
theorem rdrv_col_one_flip_after_white_drive (td tx a r : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hbend : Rule30UOR.Core.center (td + (a + r)) = true)
    (hb : rdrv td tx a 1 = true) :
    rdrv td tx (a + (r + 1)) 1 = false := by
  have h1 := rdrv_col_one_black_stays_of_white_drive td tx a r r hw hb (by omega)
  rw [show a + (r + 1) = (a + r) + 1 by omega,
      rdrv_step_succ td tx (a + r) 0, rdrv_col0, hbend, h1, Bool.true_or, bxor_eq_xor]
  rfl

/-- **Unconditional Inward Arrival of a Black Cell Across `n` White Boundary Steps in `rdrv` (`rdrv_black_reaches_boundary`, 9.1211, `Rule30WhitePulse.black_reaches_boundary` in `rdrv`, `kit [33]`)**:
    for all `td, tx, a, p, n ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < n` and `rdrv td tx a (p + (n + 1)) = true` (with NO assumptions on the intervening cells `p + 1 .. p + n`!), then `rdrv td tx (a + n) (p + 1) = true`! -/
theorem rdrv_black_reaches_boundary (td tx a p n : Nat)
    (hw : ∀ s : Nat, s < n → rdrv td tx (a + s) p = false)
    (hb : rdrv td tx a (p + (n + 1)) = true) :
    rdrv td tx (a + n) (p + 1) = true := by
  induction n generalizing a p with
  | zero =>
    simpa using hb
  | succ n ih =>
    cases hf : rdrv td tx (a + (n + 1)) (p + 1)
    · have h1 : ∀ s : Nat, s ≤ n + 1 → rdrv td tx (a + s) (p + 1) = false := by
        intro s hs
        cases hb1 : rdrv td tx (a + s) (p + 1)
        · rfl
        · have hm := rdrv_black_stays td tx (a + s) p ((n + 1) - s) ((n + 1) - s)
            (fun k hk => by
              have hh := hw (s + k) (by omega)
              rwa [show a + (s + k) = (a + s) + k by omega] at hh)
            hb1 (by omega)
          rw [show (a + s) + ((n + 1) - s) = a + (n + 1) by omega, hf] at hm
          cases hm
      have hb' : rdrv td tx a ((p + 1) + (n + 1)) = true := by
        rw [show (p + 1) + (n + 1) = p + (n + 1 + 1) by omega]
        exact hb
      have ihn := ih a (p + 1) (fun s hs => h1 s (by omega)) hb'
      have hstep := rdrv_step_succ td tx (a + n) p
      rw [show (a + n) + 1 = a + (n + 1) by omega,
          hf, hw n (by omega), h1 n (by omega),
          show p + 2 = (p + 1) + 1 by omega, ihn,
          Bool.false_or, bxor_eq_xor] at hstep
      cases hstep
    · rfl

/-- **Inward Arrival and Persistence of a Black Cell at Column `1` During a White Drive Run (`rdrv_col_one_black_of_white_drive_and_black_cell`, 9.1212, `kit [33]`)**:
    for all `td, tx, a, n, r, k ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `rdrv td tx a (n + 1) = true`, `n ≤ k`, and `k ≤ r`, then `rdrv td tx (a + k) 1 = true`! -/
theorem rdrv_col_one_black_of_white_drive_and_black_cell (td tx a n r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb : rdrv td tx a (n + 1) = true)
    (hnk : n ≤ k) (hkr : k ≤ r) :
    rdrv td tx (a + k) 1 = true := by
  have hreach := rdrv_black_reaches_boundary td tx a 0 n
    (fun s hs => by rw [rdrv_col0]; exact hw s (by omega))
    (by simpa using hb)
  have hstay := rdrv_col_one_black_stays_of_white_drive td tx (a + n) (r - n) (k - n)
    (fun s hs => by
      rw [show (a + n) + s = a + (n + s) by omega]
      exact hw (n + s) (by omega))
    hreach (by omega)
  rwa [show (a + n) + (k - n) = a + k by omega] at hstay

/-- **Inward Arrival and Persistence at Column `1` from an Initial Black Cell `rhCenter tx (n + 1) = true` (`rdrv_col_one_black_from_init_of_white_drive`, 9.1213, `kit [33]`)**:
    for all `td, tx, n, r, k ∈ ℕ`, if `center (td + s) = false` for all `s < r`, `rhCenter tx (n + 1) = true`, `n ≤ k`, and `k ≤ r`, then `rdrv td tx k 1 = true`! -/
theorem rdrv_col_one_black_from_init_of_white_drive (td tx n r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + s) = false)
    (hb : rhCenter tx (n + 1) = true)
    (hnk : n ≤ k) (hkr : k ≤ r) :
    rdrv td tx k 1 = true := by
  have hb0 : rdrv td tx 0 (n + 1) = true := by
    rw [rdrv_init td tx (n + 1) (by omega)]
    exact hb
  have h := rdrv_col_one_black_of_white_drive_and_black_cell td tx 0 n r k
    (fun s hs => by rw [Nat.zero_add]; exact hw s hs) hb0 hnk hkr
  rwa [Nat.zero_add] at h

/-- **Unconditional Column-`1` Black Arrival from the Right-Edge Diagonal `rhCenter tx tx = true` During a White Drive Run (`rdrv_col_one_black_from_right_edge_of_white_drive`, 9.1214, `kit [33]`)**:
    for all `td, tx, r, k ∈ ℕ` with `1 ≤ tx`, if `center (td + s) = false` for all `s < r`, `tx ≤ k + 1`, and `k ≤ r`, then `rdrv td tx k 1 = true` (with NO interior black-cell hypothesis on `tx`!)! -/
theorem rdrv_col_one_black_from_right_edge_of_white_drive (td tx r k : Nat)
    (htx : 1 ≤ tx)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + s) = false)
    (htk : tx ≤ k + 1) (hkr : k ≤ r) :
    rdrv td tx k 1 = true := by
  refine rdrv_col_one_black_from_init_of_white_drive td tx (tx - 1) r k hw ?_ (by omega) hkr
  rw [show (tx - 1) + 1 = tx by omega]
  exact rhCenter_self_eq_true tx

/-- **Synchronization of Column `1` Across Two Initial States During a White Drive Run (`rdrv_col_one_agree_of_white_drive_and_black_cells`, 9.1215, `kit [33]`)**:
    for all `td, tx2, tx, a, n2, n1, r, k ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `rdrv td tx2 a (n2 + 1) = true`, `rdrv td tx a (n1 + 1) = true`, `n2 ≤ k`, `n1 ≤ k`, and `k ≤ r`, then `rdrv td tx2 (a + k) 1 = rdrv td tx (a + k) 1`! -/
theorem rdrv_col_one_agree_of_white_drive_and_black_cells (td tx2 tx a n2 n1 r k : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb2 : rdrv td tx2 a (n2 + 1) = true)
    (hb1 : rdrv td tx a (n1 + 1) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    rdrv td tx2 (a + k) 1 = rdrv td tx (a + k) 1 := by
  rw [rdrv_col_one_black_of_white_drive_and_black_cell td tx2 a n2 r k hw hb2 hn2 hkr,
      rdrv_col_one_black_of_white_drive_and_black_cell td tx a n1 r k hw hb1 hn1 hkr]

/-- **Synchronization of Column `1` One Step After a White Drive Run (`rdrv_col_one_agree_after_white_drive_and_black_cells`, 9.1216, `kit [33]`)**:
    for all `td, tx2, tx, a, n2, n1, r ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `rdrv td tx2 a (n2 + 1) = true`, `rdrv td tx a (n1 + 1) = true`, `n2 ≤ r`, and `n1 ≤ r`, then `rdrv td tx2 (a + (r + 1)) 1 = rdrv td tx (a + (r + 1)) 1`! -/
theorem rdrv_col_one_agree_after_white_drive_and_black_cells (td tx2 tx a n2 n1 r : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hb2 : rdrv td tx2 a (n2 + 1) = true)
    (hb1 : rdrv td tx a (n1 + 1) = true)
    (hn2 : n2 ≤ r) (hn1 : n1 ≤ r) :
    rdrv td tx2 (a + (r + 1)) 1 = rdrv td tx (a + (r + 1)) 1 := by
  have h2 := rdrv_col_one_black_of_white_drive_and_black_cell td tx2 a n2 r r hw hb2 hn2 (by omega)
  have h1 := rdrv_col_one_black_of_white_drive_and_black_cell td tx a n1 r r hw hb1 hn1 (by omega)
  rw [show a + (r + 1) = (a + r) + 1 by omega,
      rdrv_step_succ td tx2 (a + r) 0, rdrv_step_succ td tx (a + r) 0,
      rdrv_col0, rdrv_col0, h2, h1, Bool.true_or, Bool.true_or]

/-- **Derivation of `maskparity · 0` Agreement from a White Center Run and Black Right-Half Cells (`periodic_maskparity_zero_agree_of_white_drive_and_black_cells`, 9.1217, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, a, n2, n1, r, k ∈ ℕ` with `T ≤ t`, if `center (t + (a + s)) = false` for all `s < r`, `rdrv t (t + m * P) a (n2 + 1) = true`, `rdrv t t a (n1 + 1) = true`, `n2 ≤ k`, `n1 ≤ k`, and `k ≤ r`, then `maskparity ((t + (a + k)) + m * P) 0 = maskparity (t + (a + k)) 0`! -/
theorem periodic_maskparity_zero_agree_of_white_drive_and_black_cells
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t a n2 n1 r k : Nat) (ht : T ≤ t)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + (a + s)) = false)
    (hb2 : rdrv t (t + m * P) a (n2 + 1) = true)
    (hb1 : rdrv t t a (n1 + 1) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Scale.maskparity ((t + (a + k)) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + (a + k)) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t (a + k) ht (fun _ => ?_)
  exact rdrv_col_one_agree_of_white_drive_and_black_cells t (t + m * P) t a n2 n1 r k hw hb2 hb1 hn2 hn1 hkr

/-- **Derivation of `maskparity · 0` Agreement from an Initial White Center Run and Initial Black Right-Half Cells (`periodic_maskparity_zero_agree_from_init_of_white_drive`, 9.1218, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, n2, n1, r, k ∈ ℕ` with `T ≤ t`, if `center (t + s) = false` for all `s < r`, `rhCenter (t + m * P) (n2 + 1) = true`, `rhCenter t (n1 + 1) = true`, `n2 ≤ k`, `n1 ≤ k`, and `k ≤ r`, then `maskparity ((t + k) + m * P) 0 = maskparity (t + k) 0`! -/
theorem periodic_maskparity_zero_agree_from_init_of_white_drive
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t n2 n1 r k : Nat) (ht : T ≤ t)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (hb2 : rhCenter (t + m * P) (n2 + 1) = true)
    (hb1 : rhCenter t (n1 + 1) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    Rule30UOR.Scale.maskparity ((t + k) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + k) 0 := by
  have h := periodic_maskparity_zero_agree_of_white_drive_and_black_cells
    T P hP hper m t 0 n2 n1 r k ht
    (fun s hs => by rw [Nat.zero_add]; exact hw s hs)
    (by rw [rdrv_init t (t + m * P) (n2 + 1) (by omega)]; exact hb2)
    (by rw [rdrv_init t t (n1 + 1) (by omega)]; exact hb1)
    hn2 hn1 hkr
  rwa [Nat.zero_add] at h

/-- **White Prefix Forced by a White Column-`1` Cell During a White Drive Run (`rdrv_white_prefix_forced_of_col_one_white`, 9.1219, `Rule30WhitePulse.white_prefix_forced` in `rdrv`, `kit [33]`)**:
    for all `td, tx, a, r, q ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `rdrv td tx (a + (q - 1)) 1 = false`, `1 ≤ q`, and `q ≤ r + 1`, then `rdrv td tx a q = false`! -/
theorem rdrv_white_prefix_forced_of_col_one_white (td tx a r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (h1 : rdrv td tx (a + (q - 1)) 1 = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    rdrv td tx a q = false := by
  cases hq : rdrv td tx a q
  · rfl
  · have hb : rdrv td tx a ((q - 1) + 1) = true := by
      rwa [show (q - 1) + 1 = q by omega]
    have hc := rdrv_col_one_black_of_white_drive_and_black_cell
      td tx a (q - 1) r (q - 1) hw hb (by omega) (by omega)
    rw [h1] at hc
    cases hc

/-- **White Right-Half Cell `rhCenter t q = false` Forced by a White Column-`1` Cell During a White Center Run (`rhCenter_white_prefix_forced_of_col_one_white`, 9.1220, `kit [33]`)**:
    for all `t, r, q ∈ ℕ`, if `center (t + s) = false` for all `s < r`, `rhCenter (t + (q - 1)) 1 = false`, `1 ≤ q`, and `q ≤ r + 1`, then `rhCenter t q = false`! -/
theorem rhCenter_white_prefix_forced_of_col_one_white (t r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (h1 : rhCenter (t + (q - 1)) 1 = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    rhCenter t q = false := by
  have h0 := rdrv_white_prefix_forced_of_col_one_white t t 0 r q
    (fun s hs => by rw [Nat.zero_add]; exact hw s hs)
    (by rw [Nat.zero_add, rdrv_diag_eq_rhCenter]; exact h1)
    hq1 hqr
  rwa [rdrv_init t t q (by omega)] at h0

/-- **White Right-Half Band `[1, r + 1]` Forced by a White Center Run and White Column-`1` Run (`rhCenter_white_band_forced_of_col_one_white_run`, 9.1221, `kit [33]`)**:
    for all `t, r, q ∈ ℕ`, if `center (t + s) = false` for all `s < r`, `rhCenter (t + s) 1 = false` for all `s ≤ r`, `1 ≤ q`, and `q ≤ r + 1`, then `rhCenter t q = false`! -/
theorem rhCenter_white_band_forced_of_col_one_white_run (t r q : Nat)
    (hw : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (h1 : ∀ s : Nat, s ≤ r → rhCenter (t + s) 1 = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    rhCenter t q = false :=
  rhCenter_white_prefix_forced_of_col_one_white t r q hw (h1 (q - 1) (by omega)) hq1 hqr

/-! ### Batch 62: Autonomous Sub-Diagonal Recurrence, `accum_shift` Period-Doubling, and Sub-Diagonal OR-Determination in `rdrv` (`kit [33]`, 9.1222–9.1236) -/

/-- **Autonomous 1-Step Sub-Diagonal Recurrence in `rdrv` (`rdrv_subdiag_succ_two_step`, 9.1222, `kit [33]`)**:
    for all `td, tx, c, u ∈ ℕ`, sub-diagonal `c + 2` evolves in `u` by `rdrv td tx ((u + 1) + (c + 2)) (u + 1) = bxor (rdrv td tx (u + (c + 2)) u) (rdrv td tx ((u + 1) + (c + 1)) (u + 1) || rdrv td tx ((u + 2) + c) (u + 2))`! -/
theorem rdrv_subdiag_succ_two_step (td tx c u : Nat) :
    rdrv td tx ((u + 1) + (c + 2)) (u + 1) =
      bxor (rdrv td tx (u + (c + 2)) u)
        (rdrv td tx ((u + 1) + (c + 1)) (u + 1) || rdrv td tx ((u + 2) + c) (u + 2)) := by
  have h := rdrv_step_succ td tx (u + (c + 2)) u
  have ha1 : (u + (c + 2)) + 1 = (u + 1) + (c + 2) := by omega
  have ha2 : u + (c + 2) = (u + 1) + (c + 1) := by omega
  have ha3 : u + (c + 2) = (u + 2) + c := by omega
  rw [← ha1, h]
  congr 1
  congr 1
  · rw [ha2]
  · rw [ha3]

/-- **Autonomous Determination of Sub-Diagonal `c + 2` from OR-Agreement of Sub-Diagonals `c + 1` and `c` (`rdrv_subdiag_agree_of_prev_or_agree`, 9.1223, `kit [33]`)**:
    for all `td, tx2, tx, c, k ∈ ℕ`, if for all `u < k`, `(rdrv td tx2 ((u + 1) + (c + 1)) (u + 1) || rdrv td tx2 ((u + 2) + c) (u + 2)) = (rdrv td tx ((u + 1) + (c + 1)) (u + 1) || rdrv td tx ((u + 2) + c) (u + 2))`, then `rdrv td tx2 (k + (c + 2)) k = rdrv td tx (k + (c + 2)) k`! -/
theorem rdrv_subdiag_agree_of_prev_or_agree (td tx2 tx c k : Nat)
    (hor : ∀ u : Nat, u < k →
      (rdrv td tx2 ((u + 1) + (c + 1)) (u + 1) || rdrv td tx2 ((u + 2) + c) (u + 2)) =
      (rdrv td tx ((u + 1) + (c + 1)) (u + 1) || rdrv td tx ((u + 2) + c) (u + 2))) :
    rdrv td tx2 (k + (c + 2)) k = rdrv td tx (k + (c + 2)) k := by
  induction k with
  | zero =>
    rw [rdrv_col0, rdrv_col0]
  | succ k ih =>
    rw [rdrv_subdiag_succ_two_step td tx2 c k,
        rdrv_subdiag_succ_two_step td tx c k,
        ih (fun u hu => hor u (by omega)),
        hor k (by omega)]

/-- **Determination of Sub-Diagonal `c + 2` from Agreement of Sub-Diagonals `c + 1` and `c` (`rdrv_subdiag_agree_of_two_prev_subdiags`, 9.1224, `kit [33]`)**:
    for all `td, tx2, tx, c, k ∈ ℕ`, if `rdrv td tx2 (u + (c + 1)) u = rdrv td tx (u + (c + 1)) u` for all `u ≤ k` and `rdrv td tx2 (u + c) u = rdrv td tx (u + c) u` for all `u ≤ k + 1`, then `rdrv td tx2 (k + (c + 2)) k = rdrv td tx (k + (c + 2)) k`! -/
theorem rdrv_subdiag_agree_of_two_prev_subdiags (td tx2 tx c k : Nat)
    (hd1 : ∀ u : Nat, u ≤ k → rdrv td tx2 (u + (c + 1)) u = rdrv td tx (u + (c + 1)) u)
    (hd0 : ∀ u : Nat, u ≤ k + 1 → rdrv td tx2 (u + c) u = rdrv td tx (u + c) u) :
    rdrv td tx2 (k + (c + 2)) k = rdrv td tx (k + (c + 2)) k := by
  refine rdrv_subdiag_agree_of_prev_or_agree td tx2 tx c k (fun u hu => ?_)
  rw [hd1 (u + 1) (by omega), hd0 (u + 2) (by omega)]

/-- **Sub-Cone Determination `p + (c + 1) ≤ k` from Agreement of Two Consecutive Sub-Diagonals `c + 1` and `c` (`rdrv_subcone_agree_of_two_subdiags`, 9.1225, `kit [33]`)**:
    for all `td, tx2, tx, c, k, p ∈ ℕ`, if `rdrv td tx2 (u + (c + 1)) u = rdrv td tx (u + (c + 1)) u` and `rdrv td tx2 ((u + 1) + c) (u + 1) = rdrv td tx ((u + 1) + c) (u + 1)` for all `u ≤ k`, and `p + (c + 1) ≤ k`, then `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_subcone_agree_of_two_subdiags (td tx2 tx c k p : Nat)
    (hd1 : ∀ u : Nat, u ≤ k → rdrv td tx2 (u + (c + 1)) u = rdrv td tx (u + (c + 1)) u)
    (hd0 : ∀ u : Nat, u ≤ k →
      rdrv td tx2 ((u + 1) + c) (u + 1) = rdrv td tx ((u + 1) + c) (u + 1))
    (hpk : p + (c + 1) ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  refine rdrv_subcone_agree_of_subdiag_gate td tx2 tx (c + 1) k p
    (fun u _ hu2 => hd1 u (by omega))
    (fun u _ hu2 _ => ?_) hpk
  rw [show u + (c + 1) = (u + 1) + c by omega]
  exact hd0 u (by omega)

/-- **Exact Collapse of Sub-Diagonal `c + 2` to the Pure-Drive White Seed `rdrv td 0` (`rdrv_subdiag_eq_white_seed_of_prev_or_eq`, 9.1226, `kit [33]`)**:
    for all `td, tx, c, k ∈ ℕ`, if `(rdrv td tx ((u + 1) + (c + 1)) (u + 1) || rdrv td tx ((u + 2) + c) (u + 2)) = (rdrv td 0 ((u + 1) + (c + 1)) (u + 1) || rdrv td 0 ((u + 2) + c) (u + 2))` for all `u < k`, then `rdrv td tx (k + (c + 2)) k = rdrv td 0 (k + (c + 2)) k`! -/
theorem rdrv_subdiag_eq_white_seed_of_prev_or_eq (td tx c k : Nat)
    (hor : ∀ u : Nat, u < k →
      (rdrv td tx ((u + 1) + (c + 1)) (u + 1) || rdrv td tx ((u + 2) + c) (u + 2)) =
      (rdrv td 0 ((u + 1) + (c + 1)) (u + 1) || rdrv td 0 ((u + 2) + c) (u + 2))) :
    rdrv td tx (k + (c + 2)) k = rdrv td 0 (k + (c + 2)) k :=
  rdrv_subdiag_agree_of_prev_or_agree td tx 0 c k hor

/-- **Sub-Diagonal `H`-Shift Defect Invariance (`accum_shift`) in `rdrv` (`rdrv_subdiag_accum_shift_xor`, 9.1227, `Rule30RightPeriods.accum_shift` in `rdrv`, `kit [33]`)**:
    for all `td, tx, c, a, H, k ∈ ℕ`, if the OR of sub-diagonals `c + 1` and `c` repeats with shift `H` across `[a, a + k)`, then `bxor (rdrv td tx (((a + H) + k) + (c + 2)) ((a + H) + k)) (rdrv td tx ((a + k) + (c + 2)) (a + k)) = bxor (rdrv td tx ((a + H) + (c + 2)) (a + H)) (rdrv td tx (a + (c + 2)) a)`! -/
theorem rdrv_subdiag_accum_shift_xor (td tx c a H k : Nat)
    (hor : ∀ u : Nat, u < k →
      (rdrv td tx (((a + H) + (u + 1)) + (c + 1)) ((a + H) + (u + 1)) ||
        rdrv td tx (((a + H) + (u + 2)) + c) ((a + H) + (u + 2))) =
      (rdrv td tx ((a + (u + 1)) + (c + 1)) (a + (u + 1)) ||
        rdrv td tx ((a + (u + 2)) + c) (a + (u + 2)))) :
    bxor (rdrv td tx (((a + H) + k) + (c + 2)) ((a + H) + k))
         (rdrv td tx ((a + k) + (c + 2)) (a + k)) =
      bxor (rdrv td tx ((a + H) + (c + 2)) (a + H))
           (rdrv td tx (a + (c + 2)) a) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero]
  | succ k ih =>
    have hs1 := rdrv_subdiag_succ_two_step td tx c ((a + H) + k)
    have hs0 := rdrv_subdiag_succ_two_step td tx c (a + k)
    rw [show (a + H) + (k + 1) = ((a + H) + k) + 1 by omega,
        show a + (k + 1) = (a + k) + 1 by omega,
        hs1, hs0,
        show ((a + H) + k) + 1 = (a + H) + (k + 1) by omega,
        show ((a + H) + k) + 2 = (a + H) + (k + 2) by omega,
        show (a + k) + 1 = a + (k + 1) by omega,
        show (a + k) + 2 = a + (k + 2) by omega,
        hor k (by omega),
        ← ih (fun u hu => hor u (by omega))]
    simp only [bxor_eq_xor]
    cases rdrv td tx (((a + H) + k) + (c + 2)) ((a + H) + k) <;>
      cases rdrv td tx ((a + k) + (c + 2)) (a + k) <;>
      cases (rdrv td tx ((a + (k + 1)) + (c + 1)) (a + (k + 1)) ||
        rdrv td tx ((a + (k + 2)) + c) (a + (k + 2))) <;> rfl

/-- **Sub-Diagonal `2 * H` Period-Doubling from `H`-Periodicity of the Preceding OR Gate (`rdrv_subdiag_period_double_of_prev_or_period`, 9.1228, `kit [33]`)**:
    for all `td, tx, c, a, H, k ∈ ℕ`, if the OR of sub-diagonals `c + 1` and `c` repeats with period `H` for `u < H + k`, then sub-diagonal `c + 2` repeats with period `2 * H` at `a + k`: `rdrv td tx (((a + 2 * H) + k) + (c + 2)) ((a + 2 * H) + k) = rdrv td tx ((a + k) + (c + 2)) (a + k)`! -/
theorem rdrv_subdiag_period_double_of_prev_or_period (td tx c a H k : Nat)
    (hor : ∀ u : Nat, u < H + k →
      (rdrv td tx (((a + H) + (u + 1)) + (c + 1)) ((a + H) + (u + 1)) ||
        rdrv td tx (((a + H) + (u + 2)) + c) ((a + H) + (u + 2))) =
      (rdrv td tx ((a + (u + 1)) + (c + 1)) (a + (u + 1)) ||
        rdrv td tx ((a + (u + 2)) + c) (a + (u + 2)))) :
    rdrv td tx (((a + 2 * H) + k) + (c + 2)) ((a + 2 * H) + k) =
      rdrv td tx ((a + k) + (c + 2)) (a + k) := by
  have hx1 := rdrv_subdiag_accum_shift_xor td tx c a H k (fun u hu => hor u (by omega))
  have hx2 := rdrv_subdiag_accum_shift_xor td tx c a H (H + k) hor
  rw [show (a + H) + (H + k) = (a + 2 * H) + k by omega,
      show a + (H + k) = (a + H) + k by omega,
      ← hx1] at hx2
  revert hx2
  simp only [bxor_eq_xor]
  cases rdrv td tx (((a + 2 * H) + k) + (c + 2)) ((a + 2 * H) + k) <;>
    cases rdrv td tx (((a + H) + k) + (c + 2)) ((a + H) + k) <;>
    cases rdrv td tx ((a + k) + (c + 2)) (a + k) <;> decide

/-- **Sub-Diagonal `2 * H` Period-Doubling from `H`-Periodicity of Sub-Diagonals `c + 1` and `c` (`rdrv_subdiag_period_double_of_two_prev_periods`, 9.1229, `kit [33]`)**:
    for all `td, tx, c, a, H, k ∈ ℕ`, if sub-diagonal `c + 1` repeats with period `H` for `u ≤ H + k` and sub-diagonal `c` repeats with period `H` for `u ≤ (H + k) + 1`, then sub-diagonal `c + 2` repeats with period `2 * H` at `a + k`! -/
theorem rdrv_subdiag_period_double_of_two_prev_periods (td tx c a H k : Nat)
    (hp1 : ∀ u : Nat, u ≤ H + k →
      rdrv td tx (((a + H) + u) + (c + 1)) ((a + H) + u) =
      rdrv td tx ((a + u) + (c + 1)) (a + u))
    (hp0 : ∀ u : Nat, u ≤ (H + k) + 1 →
      rdrv td tx (((a + H) + u) + c) ((a + H) + u) =
      rdrv td tx ((a + u) + c) (a + u)) :
    rdrv td tx (((a + 2 * H) + k) + (c + 2)) ((a + 2 * H) + k) =
      rdrv td tx ((a + k) + (c + 2)) (a + k) := by
  refine rdrv_subdiag_period_double_of_prev_or_period td tx c a H k (fun u hu => ?_)
  rw [hp1 (u + 1) (by omega), hp0 (u + 2) (by omega)]

/-- **Sub-Diagonal `c + 2` Complementation Step Under a Black Preceding Sub-Diagonal `c + 1` (`rdrv_subdiag_succ_two_step_of_black_prev`, 9.1230, `kit [33]`)**:
    for all `td, tx, c, u ∈ ℕ`, if `rdrv td tx ((u + 1) + (c + 1)) (u + 1) = true`, then `rdrv td tx ((u + 1) + (c + 2)) (u + 1) = !rdrv td tx (u + (c + 2)) u`! -/
theorem rdrv_subdiag_succ_two_step_of_black_prev (td tx c u : Nat)
    (hb : rdrv td tx ((u + 1) + (c + 1)) (u + 1) = true) :
    rdrv td tx ((u + 1) + (c + 2)) (u + 1) = !rdrv td tx (u + (c + 2)) u := by
  rw [rdrv_subdiag_succ_two_step td tx c u, hb, Bool.true_or, bxor_eq_xor]
  cases rdrv td tx (u + (c + 2)) u <;> rfl

/-- **Sub-Diagonal `1` Period-`2` Invariance Under Two Consecutive Black Main-Diagonal Cells (`rdrv_subdiag_one_period_two_of_black_main_diag`, 9.1231, `kit [33]`)**:
    for all `td, tx, u ∈ ℕ`, if `rdrv td tx (u + 1) (u + 1) = true` and `rdrv td tx (u + 2) (u + 2) = true`, then `rdrv td tx ((u + 2) + 1) (u + 2) = rdrv td tx (u + 1) u`! -/
theorem rdrv_subdiag_one_period_two_of_black_main_diag (td tx u : Nat)
    (hb1 : rdrv td tx (u + 1) (u + 1) = true)
    (hb2 : rdrv td tx (u + 2) (u + 2) = true) :
    rdrv td tx ((u + 2) + 1) (u + 2) = rdrv td tx (u + 1) u := by
  have hs1 := rdrv_subdiag_one_step_of_black_main_diag td tx u hb1
  have hs2 := rdrv_subdiag_one_step_of_black_main_diag td tx (u + 1) (by
    rw [show (u + 1) + 1 = u + 2 by omega]; exact hb2)
  rw [show (u + 1) + 1 = u + 2 by omega,
      show (u + 1) + 2 = (u + 2) + 1 by omega] at hs2
  rw [hs2, hs1, Bool.not_not]

/-- **Sub-Diagonal `1` Agreement Under a Black Main Diagonal (`rdrv_subdiag_one_agree_of_black_main_diag`, 9.1232, `kit [33]`)**:
    for all `td, tx2, tx, k ∈ ℕ`, if `rdrv td tx2 (u + 1) (u + 1) = true ∧ rdrv td tx (u + 1) (u + 1) = true` for all `u < k`, then `rdrv td tx2 (k + 1) k = rdrv td tx (k + 1) k`! -/
theorem rdrv_subdiag_one_agree_of_black_main_diag (td tx2 tx k : Nat)
    (hb : ∀ u : Nat, u < k →
      rdrv td tx2 (u + 1) (u + 1) = true ∧ rdrv td tx (u + 1) (u + 1) = true) :
    rdrv td tx2 (k + 1) k = rdrv td tx (k + 1) k := by
  induction k with
  | zero =>
    rw [rdrv_col0, rdrv_col0]
  | succ k ih =>
    rw [show (k + 1) + 1 = k + 2 by omega,
        rdrv_subdiag_one_step_of_black_main_diag td tx2 k (hb k (by omega)).1,
        rdrv_subdiag_one_step_of_black_main_diag td tx k (hb k (by omega)).2,
        ih (fun u hu => hb u (by omega))]

/-- **Sub-Diagonal `2` Complementation Step Under a Black Main Diagonal (`rdrv_subdiag_two_step_of_black_main_diag`, 9.1233, `kit [33]`)**:
    for all `td, tx, u ∈ ℕ`, if `rdrv td tx (u + 2) (u + 2) = true`, then `rdrv td tx ((u + 1) + 2) (u + 1) = !rdrv td tx (u + 2) u`! -/
theorem rdrv_subdiag_two_step_of_black_main_diag (td tx u : Nat)
    (hb : rdrv td tx (u + 2) (u + 2) = true) :
    rdrv td tx ((u + 1) + 2) (u + 1) = !rdrv td tx (u + 2) u := by
  have hs := rdrv_subdiag_succ_two_step td tx 0 u
  rw [Nat.add_zero, Nat.add_zero, hb, Bool.or_true, bxor_eq_xor] at hs
  rw [hs]
  cases rdrv td tx (u + 2) u <;> rfl

/-- **Sub-Diagonal `2` Period-`2` Invariance Under Two Consecutive Black Main-Diagonal Cells (`rdrv_subdiag_two_period_two_of_black_main_diag`, 9.1234, `kit [33]`)**:
    for all `td, tx, u ∈ ℕ`, if `rdrv td tx (u + 2) (u + 2) = true` and `rdrv td tx (u + 3) (u + 3) = true`, then `rdrv td tx ((u + 2) + 2) (u + 2) = rdrv td tx (u + 2) u`! -/
theorem rdrv_subdiag_two_period_two_of_black_main_diag (td tx u : Nat)
    (hb2 : rdrv td tx (u + 2) (u + 2) = true)
    (hb3 : rdrv td tx (u + 3) (u + 3) = true) :
    rdrv td tx ((u + 2) + 2) (u + 2) = rdrv td tx (u + 2) u := by
  have hs1 := rdrv_subdiag_two_step_of_black_main_diag td tx u hb2
  have hs2 := rdrv_subdiag_two_step_of_black_main_diag td tx (u + 1) (by
    rw [show (u + 1) + 2 = u + 3 by omega]; exact hb3)
  rw [show (u + 1) + 1 = u + 2 by omega] at hs2
  rw [hs2, hs1, Bool.not_not]

/-- **Sub-Diagonal `2` Agreement Under a Black Main Diagonal (`rdrv_subdiag_two_agree_of_black_main_diag`, 9.1235, `kit [33]`)**:
    for all `td, tx2, tx, k ∈ ℕ`, if `rdrv td tx2 (u + 2) (u + 2) = true ∧ rdrv td tx (u + 2) (u + 2) = true` for all `u < k`, then `rdrv td tx2 (k + 2) k = rdrv td tx (k + 2) k`! -/
theorem rdrv_subdiag_two_agree_of_black_main_diag (td tx2 tx k : Nat)
    (hb : ∀ u : Nat, u < k →
      rdrv td tx2 (u + 2) (u + 2) = true ∧ rdrv td tx (u + 2) (u + 2) = true) :
    rdrv td tx2 (k + 2) k = rdrv td tx (k + 2) k := by
  induction k with
  | zero =>
    rw [rdrv_col0, rdrv_col0]
  | succ k ih =>
    rw [rdrv_subdiag_two_step_of_black_main_diag td tx2 k (hb k (by omega)).1,
        rdrv_subdiag_two_step_of_black_main_diag td tx k (hb k (by omega)).2,
        ih (fun u hu => hb u (by omega))]

/-- **Sub-Cone `p + 2 ≤ k` Determination from Main-Diagonal Blackness at `u ≥ 1` (`rdrv_subcone_two_agree_of_black_main_diag`, 9.1236, `kit [33]`)**:
    for all `td, tx2, tx, k, p ∈ ℕ`, if `rdrv td tx2 (u + 1) (u + 1) = true ∧ rdrv td tx (u + 1) (u + 1) = true` for all `u ≤ k` and `p + 2 ≤ k`, then `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_subcone_two_agree_of_black_main_diag (td tx2 tx k p : Nat)
    (hb : ∀ u : Nat, u ≤ k →
      rdrv td tx2 (u + 1) (u + 1) = true ∧ rdrv td tx (u + 1) (u + 1) = true)
    (hpk : p + 2 ≤ k) :
    rdrv td tx2 k p = rdrv td tx k p := by
  refine rdrv_subcone_agree_of_two_subdiags td tx2 tx 1 k p
    (fun u hu => rdrv_subdiag_two_agree_of_black_main_diag td tx2 tx u (fun v hv => by
      have h := hb (v + 1) (by omega)
      rwa [show (v + 1) + 1 = v + 2 by omega] at h))
    (fun u hu => rdrv_subdiag_one_agree_of_black_main_diag td tx2 tx (u + 1) (fun v hv =>
      hb v (by omega)))
    hpk

/-! ### Batch 63: Right-Edge `rdiag` / `IsRightThreshold` Super-Diagonal Readouts & `2^k`-Periodicity Transfer into `rdrv` (`kit [33]`, 9.1237–9.1251) -/

/-- **Exact Right-Diagonal Identification of Super-Diagonals in `rhCenter` (`rhCenter_superdiag_eq_rdiag`, 9.1237, `kit [33]`)**:
    for all `t, c, u ∈ ℕ` with `c ≤ t`, the super-diagonal cell `rhCenter (t + u) (u + c)` lies on the fixed right diagonal `t - c` (independent of `u`!): `rhCenter (t + u) (u + c) = rdiag (t - c) (t + u)`! -/
theorem rhCenter_superdiag_eq_rdiag (t c u : Nat) (hct : c ≤ t) :
    rhCenter (t + u) (u + c) = rdiag (t - c) (t + u) := by
  rw [rhCenter_eq_rdiag (t + u) (u + c) (by omega),
      show (t + u) - (u + c) = t - c by omega]

/-- **Exact Right-Diagonal Identification of Super-Diagonals in `rdrv` (`rdrv_superdiag_eq_rdiag`, 9.1238, `kit [33]`)**:
    for all `td, tx, c, u ∈ ℕ` with `1 ≤ c` and `c ≤ tx`, `rdrv td tx u (u + c) = rdiag (tx - c) (tx + u)`! -/
theorem rdrv_superdiag_eq_rdiag (td tx c u : Nat) (hc1 : 1 ≤ c) (hct : c ≤ tx) :
    rdrv td tx u (u + c) = rdiag (tx - c) (tx + u) := by
  rw [rdrv_outside_cone_eq_rhCenter td tx u (u + c) (by omega)]
  exact rhCenter_superdiag_eq_rdiag tx c u hct

/-- **Unconditional `2^k`-Periodicity in `u` of Super-Diagonals `rhCenter (t + u) (u + c)` (`rhCenter_superdiag_period_twopow`, 9.1239, `kit [33]`)**:
    for all `t, c, k, u, v ∈ ℕ` with `t - c ≤ k` (with NO `c ≤ t` bound required!), `rhCenter (t + (u + v * 2^k)) ((u + v * 2^k) + c) = rhCenter (t + u) (u + c)`! -/
theorem rhCenter_superdiag_period_twopow (t c k u v : Nat) (htc : t - c ≤ k) :
    rhCenter (t + (u + v * twopow k)) ((u + v * twopow k) + c) =
      rhCenter (t + u) (u + c) := by
  by_cases hct : c ≤ t
  · have h := rhCenter_diag_shift_twopow_eq k (t + u) (u + c) v (by omega) (by omega)
    rwa [show (t + u) + v * twopow k = t + (u + v * twopow k) by omega,
         show (u + c) + v * twopow k = (u + v * twopow k) + c by omega] at h
  · rw [rhCenter_gt_eq_false (t + (u + v * twopow k)) ((u + v * twopow k) + c) (by omega),
        rhCenter_gt_eq_false (t + u) (u + c) (by omega)]

/-- **Right-Threshold `2^k`-Periodicity in `u` of Super-Diagonals `rhCenter (t + u) (u + c)` (`rhCenter_superdiag_period_twopow_of_threshold`, 9.1240, `kit [33]`)**:
    for all `t, c, k, J, u, v ∈ ℕ` with `IsRightThreshold k J` and `t - c ≤ J` (with NO `c ≤ t` bound required!), `rhCenter (t + (u + v * 2^k)) ((u + v * 2^k) + c) = rhCenter (t + u) (u + c)`! -/
theorem rhCenter_superdiag_period_twopow_of_threshold (t c k J u v : Nat)
    (hJ : IsRightThreshold k J) (htc : t - c ≤ J) :
    rhCenter (t + (u + v * twopow k)) ((u + v * twopow k) + c) =
      rhCenter (t + u) (u + c) := by
  by_cases hct : c ≤ t
  · have h := rhCenter_diag_shift_twopow_eq_of_threshold k J (u + c) (t - c) v hJ htc
    rwa [show (u + c) + (t - c) = t + u by omega,
         show (t + u) + v * twopow k = t + (u + v * twopow k) by omega,
         show (u + c) + v * twopow k = (u + v * twopow k) + c by omega] at h
  · rw [rhCenter_gt_eq_false (t + (u + v * twopow k)) ((u + v * twopow k) + c) (by omega),
        rhCenter_gt_eq_false (t + u) (u + c) (by omega)]

/-- **Unconditional `2^k`-Periodicity in `u` of Super-Diagonals in `rdrv` (`rdrv_superdiag_period_twopow`, 9.1241, `kit [33]`)**:
    for all `td, tx, c, k, u, v ∈ ℕ` with `1 ≤ c` and `tx - c ≤ k`, `rdrv td tx (u + v * 2^k) ((u + v * 2^k) + c) = rdrv td tx u (u + c)`! -/
theorem rdrv_superdiag_period_twopow (td tx c k u v : Nat)
    (hc1 : 1 ≤ c) (htc : tx - c ≤ k) :
    rdrv td tx (u + v * twopow k) ((u + v * twopow k) + c) =
      rdrv td tx u (u + c) := by
  rw [rdrv_outside_cone_eq_rhCenter td tx (u + v * twopow k) ((u + v * twopow k) + c) (by omega),
      rdrv_outside_cone_eq_rhCenter td tx u (u + c) (by omega)]
  exact rhCenter_superdiag_period_twopow tx c k u v htc

/-- **Right-Threshold `2^k`-Periodicity in `u` of Super-Diagonals in `rdrv` (`rdrv_superdiag_period_twopow_of_threshold`, 9.1242, `kit [33]`)**:
    for all `td, tx, c, k, J, u, v ∈ ℕ` with `1 ≤ c`, `IsRightThreshold k J`, and `tx - c ≤ J`, `rdrv td tx (u + v * 2^k) ((u + v * 2^k) + c) = rdrv td tx u (u + c)`! -/
theorem rdrv_superdiag_period_twopow_of_threshold (td tx c k J u v : Nat)
    (hc1 : 1 ≤ c) (hJ : IsRightThreshold k J) (htc : tx - c ≤ J) :
    rdrv td tx (u + v * twopow k) ((u + v * twopow k) + c) =
      rdrv td tx u (u + c) := by
  rw [rdrv_outside_cone_eq_rhCenter td tx (u + v * twopow k) ((u + v * twopow k) + c) (by omega),
      rdrv_outside_cone_eq_rhCenter td tx u (u + c) (by omega)]
  exact rhCenter_superdiag_period_twopow_of_threshold tx c k J u v hJ htc

/-- **All-Time Super-Diagonal Agreement from a Single `2^k` Fundamental Period (`rhCenter_superdiag_agree_all_of_lt_twopow`, 9.1243, `kit [33]`)**:
    for all `t, Q, c, k, u ∈ ℕ` with `(t + Q) - c ≤ k`, if `rhCenter ((t + Q) + r) (r + c) = rhCenter (t + r) (r + c)` for all `r < 2^k`, then `rhCenter ((t + Q) + u) (u + c) = rhCenter (t + u) (u + c)` for ALL `u ∈ ℕ`! -/
theorem rhCenter_superdiag_agree_all_of_lt_twopow (t Q c k u : Nat)
    (htc : (t + Q) - c ≤ k)
    (h : ∀ r : Nat, r < twopow k → rhCenter ((t + Q) + r) (r + c) = rhCenter (t + r) (r + c)) :
    rhCenter ((t + Q) + u) (u + c) = rhCenter (t + u) (u + c) := by
  have hpos : 0 < twopow k := by
    rw [twopow_eq_pow k]
    exact Nat.two_pow_pos k
  have hr : u % twopow k < twopow k := Nat.mod_lt u hpos
  have heq : u % twopow k + (u / twopow k) * twopow k = u := by
    have hdiv := Nat.div_add_mod u (twopow k)
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq,
      rhCenter_superdiag_period_twopow (t + Q) c k (u % twopow k) (u / twopow k) htc,
      rhCenter_superdiag_period_twopow t c k (u % twopow k) (u / twopow k) (by omega)]
  exact h (u % twopow k) hr

/-- **All-Time Super-Diagonal Agreement Under `IsRightThreshold k J` from a Single `2^k` Fundamental Period (`rhCenter_superdiag_agree_all_of_threshold`, 9.1244, `kit [33]`)**:
    for all `t, Q, c, k, J, u ∈ ℕ` with `IsRightThreshold k J` and `(t + Q) - c ≤ J`, if `rhCenter ((t + Q) + r) (r + c) = rhCenter (t + r) (r + c)` for all `r < 2^k`, then `rhCenter ((t + Q) + u) (u + c) = rhCenter (t + u) (u + c)` for ALL `u ∈ ℕ`! -/
theorem rhCenter_superdiag_agree_all_of_threshold (t Q c k J u : Nat)
    (hJ : IsRightThreshold k J) (htc : (t + Q) - c ≤ J)
    (h : ∀ r : Nat, r < twopow k → rhCenter ((t + Q) + r) (r + c) = rhCenter (t + r) (r + c)) :
    rhCenter ((t + Q) + u) (u + c) = rhCenter (t + u) (u + c) := by
  have hpos : 0 < twopow k := by
    rw [twopow_eq_pow k]
    exact Nat.two_pow_pos k
  have hr : u % twopow k < twopow k := Nat.mod_lt u hpos
  have heq : u % twopow k + (u / twopow k) * twopow k = u := by
    have hdiv := Nat.div_add_mod u (twopow k)
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq,
      rhCenter_superdiag_period_twopow_of_threshold (t + Q) c k J (u % twopow k) (u / twopow k) hJ htc,
      rhCenter_superdiag_period_twopow_of_threshold t c k J (u % twopow k) (u / twopow k) hJ (by omega)]
  exact h (u % twopow k) hr

/-- **All-Time Conditional Super-Diagonal Gate from a Single `2^k` Fundamental Period (`rhCenter_superdiag_gate_all_of_lt_twopow`, 9.1245, `kit [33]`)**:
    for all `t, Q, c, k, u ∈ ℕ` with `(t + Q) - c ≤ k`, if `rhCenter (t + r) (r + c) = false → rhCenter ((t + Q) + r) (r + (c + 1)) = rhCenter (t + r) (r + (c + 1))` for all `r < 2^k`, then the same conditional gate holds for ALL `u ∈ ℕ`! -/
theorem rhCenter_superdiag_gate_all_of_lt_twopow (t Q c k u : Nat)
    (htc : (t + Q) - c ≤ k)
    (h : ∀ r : Nat, r < twopow k →
      rhCenter (t + r) (r + c) = false →
      rhCenter ((t + Q) + r) (r + (c + 1)) = rhCenter (t + r) (r + (c + 1)))
    (hw : rhCenter (t + u) (u + c) = false) :
    rhCenter ((t + Q) + u) (u + (c + 1)) = rhCenter (t + u) (u + (c + 1)) := by
  have hpos : 0 < twopow k := by
    rw [twopow_eq_pow k]
    exact Nat.two_pow_pos k
  have hr : u % twopow k < twopow k := Nat.mod_lt u hpos
  have heq : u % twopow k + (u / twopow k) * twopow k = u := by
    have hdiv := Nat.div_add_mod u (twopow k)
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq] at hw ⊢
  rw [rhCenter_superdiag_period_twopow t c k (u % twopow k) (u / twopow k) (by omega)] at hw
  rw [rhCenter_superdiag_period_twopow (t + Q) (c + 1) k (u % twopow k) (u / twopow k) (by omega),
      rhCenter_superdiag_period_twopow t (c + 1) k (u % twopow k) (u / twopow k) (by omega)]
  exact h (u % twopow k) hr hw

/-- **All-Time Conditional Super-Diagonal Gate Under `IsRightThreshold k J` from a Single `2^k` Fundamental Period (`rhCenter_superdiag_gate_all_of_threshold`, 9.1246, `kit [33]`)**:
    for all `t, Q, c, k, J, u ∈ ℕ` with `IsRightThreshold k J` and `(t + Q) - c ≤ J`, if `rhCenter (t + r) (r + c) = false → rhCenter ((t + Q) + r) (r + (c + 1)) = rhCenter (t + r) (r + (c + 1))` for all `r < 2^k`, then the same conditional gate holds for ALL `u ∈ ℕ`! -/
theorem rhCenter_superdiag_gate_all_of_threshold (t Q c k J u : Nat)
    (hJ : IsRightThreshold k J) (htc : (t + Q) - c ≤ J)
    (h : ∀ r : Nat, r < twopow k →
      rhCenter (t + r) (r + c) = false →
      rhCenter ((t + Q) + r) (r + (c + 1)) = rhCenter (t + r) (r + (c + 1)))
    (hw : rhCenter (t + u) (u + c) = false) :
    rhCenter ((t + Q) + u) (u + (c + 1)) = rhCenter (t + u) (u + (c + 1)) := by
  have hpos : 0 < twopow k := by
    rw [twopow_eq_pow k]
    exact Nat.two_pow_pos k
  have hr : u % twopow k < twopow k := Nat.mod_lt u hpos
  have heq : u % twopow k + (u / twopow k) * twopow k = u := by
    have hdiv := Nat.div_add_mod u (twopow k)
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq] at hw ⊢
  rw [rhCenter_superdiag_period_twopow_of_threshold t c k J (u % twopow k) (u / twopow k) hJ (by omega)] at hw
  rw [rhCenter_superdiag_period_twopow_of_threshold (t + Q) (c + 1) k J (u % twopow k) (u / twopow k) hJ (by omega),
      rhCenter_superdiag_period_twopow_of_threshold t (c + 1) k J (u % twopow k) (u / twopow k) hJ (by omega)]
  exact h (u % twopow k) hr hw

/-- **Infinite-Horizon Trapezoid Determination `p ≤ s + (B + 1)` from `RhBandAgree` and a `2^k`-Bounded Super-Diagonal Gate (`rdrv_trapezoid_agree_of_superdiag_gate_twopow`, 9.1247, `kit [33]`)**:
    for all `td, tx, Q, B, k, s, p ∈ ℕ` with `(tx + Q) - (B + 1) ≤ k`, if `RhBandAgree tx Q 1 B` and the super-diagonal `B + 1` gate holds on the single period `r < 2^k`, then for ALL `s ∈ ℕ` and ALL `p ≤ s + (B + 1)`, `rdrv td (tx + Q) s p = rdrv td tx s p`! -/
theorem rdrv_trapezoid_agree_of_superdiag_gate_twopow (td tx Q B k s p : Nat)
    (htc : (tx + Q) - (B + 1) ≤ k)
    (hband : RhBandAgree tx Q 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter ((tx + Q) + r) (r + (B + 1)) = rhCenter (tx + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter (tx + r) (r + (B + 1)) = false →
      rhCenter ((tx + Q) + r) (r + (B + 2)) = rhCenter (tx + r) (r + (B + 2)))
    (hps : p ≤ s + (B + 1)) :
    rdrv td (tx + Q) s p = rdrv td tx s p := by
  refine rdrv_trapezoid_agree_of_superdiag_gate td tx Q B s p hband
    (fun u _ => rhCenter_superdiag_agree_all_of_lt_twopow tx Q (B + 1) k u htc hc1)
    (fun u _ hw => ?_) hps
  have h := rhCenter_superdiag_gate_all_of_lt_twopow tx Q (B + 1) k u htc
    (fun r hr hwr => by
      rw [show (B + 1) + 1 = B + 2 by omega]
      exact hc2 r hr hwr) hw
  rwa [show (B + 1) + 1 = B + 2 by omega] at h

/-- **Infinite-Horizon Trapezoid Determination `p ≤ s + (B + 1)` Under `IsRightThreshold k J` from a `2^k`-Bounded Super-Diagonal Gate (`rdrv_trapezoid_agree_of_superdiag_gate_threshold`, 9.1248, `kit [33]`)**:
    for all `td, tx, Q, B, k, J, s, p ∈ ℕ` with `IsRightThreshold k J` and `(tx + Q) - (B + 1) ≤ J`, if `RhBandAgree tx Q 1 B` and the super-diagonal `B + 1` gate holds on the single period `r < 2^k`, then for ALL `s ∈ ℕ` and ALL `p ≤ s + (B + 1)`, `rdrv td (tx + Q) s p = rdrv td tx s p`! -/
theorem rdrv_trapezoid_agree_of_superdiag_gate_threshold (td tx Q B k J s p : Nat)
    (hJ : IsRightThreshold k J) (htc : (tx + Q) - (B + 1) ≤ J)
    (hband : RhBandAgree tx Q 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter ((tx + Q) + r) (r + (B + 1)) = rhCenter (tx + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter (tx + r) (r + (B + 1)) = false →
      rhCenter ((tx + Q) + r) (r + (B + 2)) = rhCenter (tx + r) (r + (B + 2)))
    (hps : p ≤ s + (B + 1)) :
    rdrv td (tx + Q) s p = rdrv td tx s p := by
  refine rdrv_trapezoid_agree_of_superdiag_gate td tx Q B s p hband
    (fun u _ => rhCenter_superdiag_agree_all_of_threshold tx Q (B + 1) k J u hJ htc hc1)
    (fun u _ hw => ?_) hps
  have h := rhCenter_superdiag_gate_all_of_threshold tx Q (B + 1) k J u hJ htc
    (fun r hr hwr => by
      rw [show (B + 1) + 1 = B + 2 by omega]
      exact hc2 r hr hwr) hw
  rwa [show (B + 1) + 1 = B + 2 by omega] at h

/-- **All-Time `maskparity · 0` Agreement from `RhBandAgree` and a `2^k`-Bounded Super-Diagonal Gate (`periodic_maskparity_zero_agree_of_superdiag_gate_twopow`, 9.1249, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, k, s ∈ ℕ` with `T ≤ t` and `(t + m * P) - (B + 1) ≤ k`, if `RhBandAgree t (m * P) 1 B` and the super-diagonal `B + 1` gate holds on `r < 2^k`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for ALL `s ∈ ℕ`! -/
theorem periodic_maskparity_zero_agree_of_superdiag_gate_twopow
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B k s : Nat) (ht : T ≤ t) (htc : (t + m * P) - (B + 1) ≤ k)
    (hband : RhBandAgree t (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter ((t + m * P) + r) (r + (B + 1)) = rhCenter (t + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter (t + r) (r + (B + 1)) = false →
      rhCenter ((t + m * P) + r) (r + (B + 2)) = rhCenter (t + r) (r + (B + 2))) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_trapezoid_agree_of_superdiag_gate_twopow t t (m * P) B k s 1 htc hband hc1 hc2 (by omega)

/-- **Horizon-Free (`r < 2^k`) Zero-Diagonal Refutation of `CenterPeriodic` from `RhBandAgree` and a Super-Diagonal Gate (`not_centerPeriodic_of_superdiag_gate_twopow_at_zero_diag`, 9.1250, `kit [33]`)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `((z + (p + 1)) + m * P) - (B + 1) ≤ k`, `RhBandAgree (z + (p + 1)) (m * P) 1 B`, and the super-diagonal `B + 1` gate holds on `r < 2^k` alone (independent of `p`!), then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_superdiag_gate_twopow_at_zero_diag
    (T P m z p B k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (htc : ((z + (p + 1)) + m * P) - (B + 1) ≤ k)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 1)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)) = false →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 2)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p (p + 3 * (m * P)) hP hm ht hz hd hset1 hset2 (by omega) (fun s _ => ?_) hper
  exact periodic_maskparity_zero_agree_of_superdiag_gate_twopow
    T P hP hper m (z + (p + 1)) B k s ht htc hband hc1 hc2

theorem not_centerPeriodic_of_superdiag_gate_twopow_at_zero_diag_prop
    (T P m z p B k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (htc : ((z + (p + 1)) + m * P) - (B + 1) ≤ k)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 1)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)) = false →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 2)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_superdiag_gate_twopow_at_zero_diag T P m z p B k hP hm ht
    hz hd hset1 hset2 htc hband hc1 hc2

/-- **Horizon-Free (`r < 2^k`) Zero-Diagonal Refutation of `CenterPeriodic` Under `IsRightThreshold k J` (`not_centerPeriodic_of_superdiag_gate_threshold_at_zero_diag`, 9.1251, `kit [33]`)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `IsRightThreshold k J`, `((z + (p + 1)) + m * P) - (B + 1) ≤ J`, `RhBandAgree (z + (p + 1)) (m * P) 1 B`, and the super-diagonal `B + 1` gate holds on `r < 2^k` alone, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_superdiag_gate_threshold_at_zero_diag
    (T P m z p B k J : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hJ : IsRightThreshold k J) (htc : ((z + (p + 1)) + m * P) - (B + 1) ≤ J)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 1)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)) = false →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 2)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p (p + 3 * (m * P)) hP hm ht hz hd hset1 hset2 (by omega) (fun s _ => ?_) hper
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m (z + (p + 1)) s ht (fun _ => ?_)
  exact rdrv_trapezoid_agree_of_superdiag_gate_threshold
    (z + (p + 1)) (z + (p + 1)) (m * P) B k J s 1 hJ htc hband hc1 hc2 (by omega)

theorem not_centerPeriodic_of_superdiag_gate_threshold_at_zero_diag_prop
    (T P m z p B k J : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hJ : IsRightThreshold k J) (htc : ((z + (p + 1)) + m * P) - (B + 1) ≤ J)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B)
    (hc1 : ∀ r : Nat, r < twopow k →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 1)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)))
    (hc2 : ∀ r : Nat, r < twopow k →
      rhCenter ((z + (p + 1)) + r) (r + (B + 1)) = false →
      rhCenter (((z + (p + 1)) + m * P) + r) (r + (B + 2)) =
      rhCenter ((z + (p + 1)) + r) (r + (B + 2))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_superdiag_gate_threshold_at_zero_diag T P m z p B k J hP hm ht
    hz hd hset1 hset2 hJ htc hband hc1 hc2

/-! ### Batch 64: Gate-Free Inward Light-Cone Determination (`p + k ≤ B + 1`) from `RhBandAgree` & Single-Slice Refutation of `CenterPeriodic` (`kit [33]`, 9.1252–9.1266) -/

/-- **Gate-Free Inward Light-Cone Determination from Step `a` (`rdrv_inward_cone_agree_from_step`, 9.1252, `kit [33]`)**:
    for all `td, tx2, tx, a, B, k, p ∈ ℕ`, if `rdrv td tx2 a q = rdrv td tx a q` for all `q ≤ B + 1` and `p + k ≤ B + 1`, then `rdrv td tx2 (a + k) p = rdrv td tx (a + k) p` — with ZERO right-boundary gates! -/
theorem rdrv_inward_cone_agree_from_step (td tx2 tx a B k p : Nat)
    (hinit : ∀ q : Nat, q ≤ B + 1 → rdrv td tx2 a q = rdrv td tx a q)
    (hpk : p + k ≤ B + 1) :
    rdrv td tx2 (a + k) p = rdrv td tx (a + k) p := by
  induction k generalizing p with
  | zero =>
    rw [Nat.add_zero]
    exact hinit p (by omega)
  | succ k ih =>
    rcases p with _ | p
    · rw [rdrv_col0, rdrv_col0]
    · rw [show a + (k + 1) = (a + k) + 1 by omega,
          rdrv_step_succ td tx2 (a + k) p,
          rdrv_step_succ td tx (a + k) p,
          ih p (by omega),
          ih (p + 1) (by omega),
          ih (p + 2) (by omega)]

/-- **Gate-Free Inward Light-Cone Determination from `k = 0` (`rdrv_inward_cone_agree_of_init_agree`, 9.1253, `kit [33]`)**:
    for all `td, tx2, tx, B, k, p ∈ ℕ`, if `rdrv td tx2 0 q = rdrv td tx 0 q` for all `q ≤ B + 1` and `p + k ≤ B + 1`, then `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_inward_cone_agree_of_init_agree (td tx2 tx B k p : Nat)
    (hinit : ∀ q : Nat, q ≤ B + 1 → rdrv td tx2 0 q = rdrv td tx 0 q)
    (hpk : p + k ≤ B + 1) :
    rdrv td tx2 k p = rdrv td tx k p := by
  have h := rdrv_inward_cone_agree_from_step td tx2 tx 0 B k p hinit hpk
  rwa [Nat.zero_add] at h

/-- **Gate-Free Inward Light-Cone Determination from `RhBandAgree tx Q 1 B` (`rdrv_inward_cone_agree_of_rhBandAgree`, 9.1254, `kit [33]`)**:
    for all `td, tx, Q, B, k, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at time `tx` and `p + k ≤ B + 1`, then `rdrv td (tx + Q) k p = rdrv td tx k p` — with ZERO temporal boundary gates! -/
theorem rdrv_inward_cone_agree_of_rhBandAgree (td tx Q B k p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hpk : p + k ≤ B + 1) :
    rdrv td (tx + Q) k p = rdrv td tx k p := by
  refine rdrv_inward_cone_agree_of_init_agree td (tx + Q) tx B k p (fun q hq => ?_) hpk
  rcases q with _ | i
  · rw [rdrv_col0, rdrv_col0]
  · rw [rdrv_init td (tx + Q) (i + 1) (by omega),
        rdrv_init td tx (i + 1) (by omega)]
    have h := hband i (by omega)
    rwa [show 1 + i = i + 1 by omega] at h

/-- **Gate-Free Column-`1` Determination from `RhBandAgree tx Q 1 B` (`rdrv_col_one_agree_of_rhBandAgree`, 9.1255, `kit [33]`)**:
    for all `td, tx, Q, B, k ∈ ℕ`, if `RhBandAgree tx Q 1 B` and `k ≤ B`, then `rdrv td (tx + Q) k 1 = rdrv td tx k 1`! -/
theorem rdrv_col_one_agree_of_rhBandAgree (td tx Q B k : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hk : k ≤ B) :
    rdrv td (tx + Q) k 1 = rdrv td tx k 1 :=
  rdrv_inward_cone_agree_of_rhBandAgree td tx Q B k 1 hband (by omega)

/-- **Gate-Free Collapse to the Pure-Drive White Seed `rdrv td 0` Inside the Inward Light Cone (`rdrv_inward_cone_eq_white_seed_of_initial_white_band`, 9.1256, `kit [33]`)**:
    for all `td, tx, B, k, p ∈ ℕ`, if `rhCenter tx (1 + i) = false` for all `i ≤ B` and `p + k ≤ B + 1`, then `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_inward_cone_eq_white_seed_of_initial_white_band (td tx B k p : Nat)
    (hw : ∀ i : Nat, i ≤ B → rhCenter tx (1 + i) = false)
    (hpk : p + k ≤ B + 1) :
    rdrv td tx k p = rdrv td 0 k p := by
  have h := rdrv_inward_cone_agree_of_rhBandAgree td 0 tx B k p
    (fun i hi => by
      rw [Nat.zero_add, hw i hi, rhCenter_gt_eq_false 0 (1 + i) (by omega)])
    hpk
  rwa [Nat.zero_add] at h

/-- **Gate-Free Collapse of `rhCenter (t + k) p` to `rdrv t 0 k p` Inside the Inward Light Cone (`rhCenter_inward_cone_eq_white_seed_of_initial_white_band`, 9.1257, `kit [33]`)**:
    for all `t, B, k, p ∈ ℕ`, if `rhCenter t (1 + i) = false` for all `i ≤ B` and `p + k ≤ B + 1`, then `rhCenter (t + k) p = rdrv t 0 k p`! -/
theorem rhCenter_inward_cone_eq_white_seed_of_initial_white_band (t B k p : Nat)
    (hw : ∀ i : Nat, i ≤ B → rhCenter t (1 + i) = false)
    (hpk : p + k ≤ B + 1) :
    rhCenter (t + k) p = rdrv t 0 k p := by
  rw [← rdrv_diag_eq_rhCenter t k p]
  exact rdrv_inward_cone_eq_white_seed_of_initial_white_band t t B k p hw hpk

/-- **Gate-Free Right-Half Inward Light-Cone Agreement Under `CenterPeriodic` (`periodic_rhCenter_inward_cone_agree_of_rhBandAgree`, 9.1258, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, s, p ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` and `p + s ≤ B + 1`, then `rhCenter ((t + s) + m * P) p = rhCenter (t + s) p`! -/
theorem periodic_rhCenter_inward_cone_agree_of_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s p : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hps : p + s ≤ B + 1) :
    rhCenter ((t + s) + m * P) p = rhCenter (t + s) p := by
  rw [show (t + s) + m * P = (t + m * P) + s by omega,
      periodic_rhCenter_shift_eq_rdrv_same_drive T P hP hper m t s p ht,
      ← rdrv_diag_eq_rhCenter t s p]
  exact rdrv_inward_cone_agree_of_rhBandAgree t t (m * P) B s p hband hps

/-- **Stepwise Contraction of `RhBandAgree` Under `CenterPeriodic` (`periodic_rhBandAgree_step_of_rhBandAgree`, 9.1259, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, s ∈ ℕ` with `T ≤ t` and `s ≤ B`, if `RhBandAgree t (m * P) 1 B`, then `RhBandAgree (t + s) (m * P) 1 (B - s)`! -/
theorem periodic_rhBandAgree_step_of_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hs : s ≤ B) :
    RhBandAgree (t + s) (m * P) 1 (B - s) := by
  intro i hi
  exact periodic_rhCenter_inward_cone_agree_of_rhBandAgree
    T P hP hper m t B s (1 + i) ht hband (by omega)

/-- **Gate-Free Column-`1` Agreement `rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1` from `RhBandAgree t (m * P) 1 B` (`periodic_rhCenter_one_agree_of_rhBandAgree`, 9.1260, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` and `s ≤ B`, then `rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1`! -/
theorem periodic_rhCenter_one_agree_of_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hs : s ≤ B) :
    rhCenter ((t + s) + m * P) 1 = rhCenter (t + s) 1 :=
  periodic_rhCenter_inward_cone_agree_of_rhBandAgree T P hP hper m t B s 1 ht hband (by omega)

/-- **Gate-Free `maskparity · 0` Agreement from Single-Slice `RhBandAgree t (m * P) 1 B` (`periodic_maskparity_zero_agree_of_rhBandAgree`, 9.1261, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 B` holds at the single time `t` and `s ≤ B`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hs : s ≤ B) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t s ht (fun _ => ?_)
  exact rdrv_col_one_agree_of_rhBandAgree t t (m * P) B s hband hs

/-- **Single-Slice Refutation of `CenterPeriodic` from `RhBandAgree` at a Doubling Zero Diagonal (`not_centerPeriodic_of_rhBandAgree_at_zero_diag_doubles`, 9.1262, `kit [33]`)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `p + 3 * (m * P) ≤ B + 1`, and `RhBandAgree (z + (p + 1)) (m * P) 1 B` holds at the single time slice `z + (p + 1)` (with NO temporal boundary gate!), then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_at_zero_diag_doubles
    (T P m z p B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hB : p + 3 * (m * P) ≤ B + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles
    T P m z p B hP hm ht hz hd hset1 hset2 hB (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree T P hP hper m (z + (p + 1)) B s ht hband hs

theorem not_centerPeriodic_of_rhBandAgree_at_zero_diag_doubles_prop
    (T P m z p B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hB : p + 3 * (m * P) ≤ B + 1)
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_at_zero_diag_doubles T P m z p B hP hm ht hz hd hset1 hset2 hB hband

/-- **Single-Slice Dyadic Refutation of `CenterPeriodic` from `RhBandAgree` (`not_centerPeriodic_of_rhBandAgree_twopow`, 9.1263, `kit [33]`)**:
    if `T ≤ t`, `t + m * P = 2^k`, `2^k ≤ B + 1`, and `RhBandAgree t (m * P) 1 B` holds at the single time slice `t`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_twopow
    (T P m t k B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hB : twopow k ≤ B + 1)
    (hband : RhBandAgree t (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k B hP hm ht htm hB (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree T P hP hper m t B s ht hband hs

/-- **Single-Slice Zero-Diagonal Pair Refutation of `CenterPeriodic` from `RhBandAgree` (`not_centerPeriodic_of_rhBandAgree_at_zero_diag_pair`, 9.1264, `kit [33]`)**:
    if `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `settle z ≤ z + 2^k`, `settle (z + m * P) ≤ (z + m * P) + 2^k`, `2^k ≤ B + 1`, and `RhBandAgree (z + 2^k) (m * P) 1 B` holds at `z + 2^k`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_at_zero_diag_pair
    (T P m z k B : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hB : twopow k ≤ B + 1)
    (hband : RhBandAgree (z + twopow k) (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags
    T P m z k B hP hz0 h2 hz1 ht hset0 hset1 hB (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree T P hP hper m (z + twopow k) B s ht hband hs

theorem not_centerPeriodic_of_rhBandAgree_at_zero_diag_pair_prop
    (T P m z k B : Nat) (hP : 0 < P) (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hB : twopow k ≤ B + 1)
    (hband : RhBandAgree (z + twopow k) (m * P) 1 B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_at_zero_diag_pair T P m z k B hP hz0 h2 hz1 ht hset0 hset1 hB hband

/-- **Shortened-Horizon Strip + Inward Light-Cone Determination (`rdrv_inward_cone_agree_of_short_boundary_gate`, 9.1265, `kit [33]`)**:
    for all `td, tx, Q, B, a, k, p ∈ ℕ`, if `RhBandAgree tx Q 1 B` holds at `0`, the conditional boundary gate at `B + 1` holds only up to step `a`, and `p + k ≤ B + 1`, then `rdrv td (tx + Q) (a + k) p = rdrv td tx (a + k) p`! -/
theorem rdrv_inward_cone_agree_of_short_boundary_gate (td tx Q B a k p : Nat)
    (hband : RhBandAgree tx Q 1 B)
    (hc2 : ∀ u : Nat, u < a →
      rdrv td tx u (B + 1) = false →
      rdrv td (tx + Q) u (B + 2) = rdrv td tx u (B + 2))
    (hpk : p + k ≤ B + 1) :
    rdrv td (tx + Q) (a + k) p = rdrv td tx (a + k) p := by
  refine rdrv_inward_cone_agree_from_step td (tx + Q) tx a B k p (fun q hq => ?_) hpk
  exact rdrv_strip_agree_of_white_boundary_col_agree td tx Q B a a q hband hc2 (by omega) hq

/-- **Shortened-Horizon `maskparity · 0` Agreement from a Conditional Boundary Gate of Length `a = S - B` (`periodic_maskparity_zero_agree_of_short_boundary_gate`, 9.1266, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, B, a, k ∈ ℕ` with `T ≤ t` and `k ≤ B`, if `RhBandAgree t (m * P) 1 B` and the conditional column `B + 1` gate holds up to step `a`, then `maskparity ((t + (a + k)) + m * P) 0 = maskparity (t + (a + k)) 0`! -/
theorem periodic_maskparity_zero_agree_of_short_boundary_gate
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t B a k : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 B)
    (hc2 : ∀ u : Nat, u < a →
      rdrv t t u (B + 1) = false →
      rdrv t (t + m * P) u (B + 2) = rdrv t t u (B + 2))
    (hk : k ≤ B) :
    Rule30UOR.Scale.maskparity ((t + (a + k)) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + (a + k)) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t (a + k) ht (fun _ => ?_)
  exact rdrv_inward_cone_agree_of_short_boundary_gate t t (m * P) B a k 1 hband hc2 (by omega)

/-! ### Batch 65: General Column-`p` Inward Arrival, White-Triangle Equivalence & Spatial White-Diamond Super-Diagonal Corridors in `rdrv` (`kit [33]`, 9.1267–9.1281) -/

/-- **General Column-`p` Inward Arrival and Persistence in `rdrv` (`rdrv_black_reaches_and_stays_boundary`, 9.1267, `kit [33]`)**:
    for all `td, tx, a, p, n, r, k ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx a (p + (n + 1)) = true`, `n ≤ k`, and `k ≤ r`, then `rdrv td tx (a + k) (p + 1) = true`! -/
theorem rdrv_black_reaches_and_stays_boundary (td tx a p n r k : Nat)
    (hw : ∀ s : Nat, s < r → rdrv td tx (a + s) p = false)
    (hb : rdrv td tx a (p + (n + 1)) = true)
    (hnk : n ≤ k) (hkr : k ≤ r) :
    rdrv td tx (a + k) (p + 1) = true := by
  have hreach := rdrv_black_reaches_boundary td tx a p n
    (fun s hs => hw s (by omega)) hb
  have hstay := rdrv_black_stays td tx (a + n) p (r - n) (k - n)
    (fun s hs => by
      rw [show (a + n) + s = a + (n + s) by omega]
      exact hw (n + s) (by omega))
    hreach (by omega)
  rwa [show (a + n) + (k - n) = a + k by omega] at hstay

/-- **Column `p + 1` Reset to `false` at the Black End of a White Run on Column `p` (`rdrv_col_succ_flip_after_white_col_and_black_cell`, 9.1268, `kit [33]`)**:
    for all `td, tx, a, p, n, r ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx (a + r) p = true`, `rdrv td tx a (p + (n + 1)) = true`, and `n ≤ r`, then `rdrv td tx (a + (r + 1)) (p + 1) = false`! -/
theorem rdrv_col_succ_flip_after_white_col_and_black_cell (td tx a p n r : Nat)
    (hw : ∀ s : Nat, s < r → rdrv td tx (a + s) p = false)
    (hbend : rdrv td tx (a + r) p = true)
    (hb : rdrv td tx a (p + (n + 1)) = true)
    (hnr : n ≤ r) :
    rdrv td tx (a + (r + 1)) (p + 1) = false := by
  have h1 := rdrv_black_reaches_and_stays_boundary td tx a p n r r hw hb hnr (by omega)
  rw [show a + (r + 1) = (a + r) + 1 by omega,
      rdrv_step_succ td tx (a + r) p, hbend, h1, Bool.true_or, bxor_eq_xor]
  rfl

/-- **Synchronization of Column `p + 1` Across Two States During a White Run on Column `p` (`rdrv_col_succ_agree_of_white_col_and_black_cells`, 9.1269, `kit [33]`)**:
    for all `td, tx2, tx, a, p, n2, n1, r, k ∈ ℕ`, if `rdrv td tx2 (a + s) p = false ∧ rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx2 a (p + (n2 + 1)) = true`, `rdrv td tx a (p + (n1 + 1)) = true`, `n2 ≤ k`, `n1 ≤ k`, and `k ≤ r`, then `rdrv td tx2 (a + k) (p + 1) = rdrv td tx (a + k) (p + 1)`! -/
theorem rdrv_col_succ_agree_of_white_col_and_black_cells (td tx2 tx a p n2 n1 r k : Nat)
    (hw : ∀ s : Nat, s < r → rdrv td tx2 (a + s) p = false ∧ rdrv td tx (a + s) p = false)
    (hb2 : rdrv td tx2 a (p + (n2 + 1)) = true)
    (hb1 : rdrv td tx a (p + (n1 + 1)) = true)
    (hn2 : n2 ≤ k) (hn1 : n1 ≤ k) (hkr : k ≤ r) :
    rdrv td tx2 (a + k) (p + 1) = rdrv td tx (a + k) (p + 1) := by
  rw [rdrv_black_reaches_and_stays_boundary td tx2 a p n2 r k (fun s hs => (hw s hs).1) hb2 hn2 hkr,
      rdrv_black_reaches_and_stays_boundary td tx a p n1 r k (fun s hs => (hw s hs).2) hb1 hn1 hkr]

/-- **Synchronization of Column `p + 1` One Step After a White Run on Column `p` (`rdrv_col_succ_agree_after_white_col_and_black_cells`, 9.1270, `kit [33]`)**:
    for all `td, tx2, tx, a, p, n2, n1, r ∈ ℕ`, if `rdrv td tx2 (a + s) p = false ∧ rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx2 (a + r) p = rdrv td tx (a + r) p`, `rdrv td tx2 a (p + (n2 + 1)) = true`, `rdrv td tx a (p + (n1 + 1)) = true`, `n2 ≤ r`, and `n1 ≤ r`, then `rdrv td tx2 (a + (r + 1)) (p + 1) = rdrv td tx (a + (r + 1)) (p + 1)`! -/
theorem rdrv_col_succ_agree_after_white_col_and_black_cells (td tx2 tx a p n2 n1 r : Nat)
    (hw : ∀ s : Nat, s < r → rdrv td tx2 (a + s) p = false ∧ rdrv td tx (a + s) p = false)
    (hend : rdrv td tx2 (a + r) p = rdrv td tx (a + r) p)
    (hb2 : rdrv td tx2 a (p + (n2 + 1)) = true)
    (hb1 : rdrv td tx a (p + (n1 + 1)) = true)
    (hn2 : n2 ≤ r) (hn1 : n1 ≤ r) :
    rdrv td tx2 (a + (r + 1)) (p + 1) = rdrv td tx (a + (r + 1)) (p + 1) := by
  have h2 := rdrv_black_reaches_and_stays_boundary td tx2 a p n2 r r (fun s hs => (hw s hs).1) hb2 hn2 (by omega)
  have h1 := rdrv_black_reaches_and_stays_boundary td tx a p n1 r r (fun s hs => (hw s hs).2) hb1 hn1 (by omega)
  rw [show a + (r + 1) = (a + r) + 1 by omega,
      rdrv_step_succ td tx2 (a + r) p, rdrv_step_succ td tx (a + r) p,
      hend, h2, h1, Bool.true_or, Bool.true_or]

/-- **White Spatial Cell `p + q` Forced by a White Column `p + 1` Cell Behind a White Column `p` (`rdrv_white_offset_forced_of_white_col`, 9.1271, `kit [33]`)**:
    for all `td, tx, a, p, r, q ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx (a + (q - 1)) (p + 1) = false`, `1 ≤ q`, and `q ≤ r + 1`, then `rdrv td tx a (p + q) = false`! -/
theorem rdrv_white_offset_forced_of_white_col (td tx a p r q : Nat)
    (hw : ∀ s : Nat, s < r → rdrv td tx (a + s) p = false)
    (h1 : rdrv td tx (a + (q - 1)) (p + 1) = false)
    (hq1 : 1 ≤ q) (hqr : q ≤ r + 1) :
    rdrv td tx a (p + q) = false := by
  cases hq : rdrv td tx a (p + q)
  · rfl
  · have hb : rdrv td tx a (p + ((q - 1) + 1)) = true := by
      rwa [show p + ((q - 1) + 1) = p + q by omega]
    have hc := rdrv_black_reaches_and_stays_boundary
      td tx a p (q - 1) r (q - 1) hw hb (by omega) (by omega)
    rw [h1] at hc
    cases hc

/-- **Outward Right-Going White Triangle Forced by a 2-Column White Run `(p, p + 1)` (`rdrv_white_triangle_forced_of_two_white_cols`, 9.1272, `kit [33]`)**:
    for all `td, tx, a, p, r, u, q ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx (a + s) (p + 1) = false` for all `s ≤ r`, `1 ≤ q`, and `u + q ≤ r + 1`, then `rdrv td tx (a + u) (p + q) = false`! -/
theorem rdrv_white_triangle_forced_of_two_white_cols (td tx a p r u q : Nat)
    (hw0 : ∀ s : Nat, s < r → rdrv td tx (a + s) p = false)
    (hw1 : ∀ s : Nat, s ≤ r → rdrv td tx (a + s) (p + 1) = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    rdrv td tx (a + u) (p + q) = false := by
  refine rdrv_white_offset_forced_of_white_col td tx (a + u) p (r - u) q
    (fun s hs => ?_) ?_ hq1 (by omega)
  · rw [show (a + u) + s = a + (u + s) by omega]
    exact hw0 (u + s) (by omega)
  · rw [show (a + u) + (q - 1) = a + (u + (q - 1)) by omega]
    exact hw1 (u + (q - 1)) (by omega)

/-- **Outward Right-Going White Triangle Forced by a White Center Run and White Column-`1` Run in `rdrv` (`rdrv_white_triangle_forced_of_white_drive_and_col_one`, 9.1273, `kit [33]`)**:
    for all `td, tx, a, r, u, q ∈ ℕ`, if `center (td + (a + s)) = false` for all `s < r`, `rdrv td tx (a + s) 1 = false` for all `s ≤ r`, `1 ≤ q`, and `u + q ≤ r + 1`, then `rdrv td tx (a + u) q = false`! -/
theorem rdrv_white_triangle_forced_of_white_drive_and_col_one (td tx a r u q : Nat)
    (hw0 : ∀ s : Nat, s < r → Rule30UOR.Core.center (td + (a + s)) = false)
    (hw1 : ∀ s : Nat, s ≤ r → rdrv td tx (a + s) 1 = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    rdrv td tx (a + u) q = false := by
  have h := rdrv_white_triangle_forced_of_two_white_cols td tx a 0 r u q
    (fun s hs => by rw [rdrv_col0]; exact hw0 s hs)
    (fun s hs => by rw [Nat.zero_add]; exact hw1 s hs)
    hq1 huq
  rwa [Nat.zero_add] at h

/-- **Outward Right-Going White Triangle in `rhCenter` Forced by a White Center Run and White Column-`1` Run (`rhCenter_white_triangle_forced_of_white_drive_and_col_one`, 9.1274, `kit [33]`)**:
    for all `t, r, u, q ∈ ℕ`, if `center (t + s) = false` for all `s < r`, `rhCenter (t + s) 1 = false` for all `s ≤ r`, `1 ≤ q`, and `u + q ≤ r + 1`, then `rhCenter (t + u) q = false`! -/
theorem rhCenter_white_triangle_forced_of_white_drive_and_col_one (t r u q : Nat)
    (hw0 : ∀ s : Nat, s < r → Rule30UOR.Core.center (t + s) = false)
    (hw1 : ∀ s : Nat, s ≤ r → rhCenter (t + s) 1 = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    rhCenter (t + u) q = false := by
  rw [← rdrv_diag_eq_rhCenter t u q]
  have h := rdrv_white_triangle_forced_of_white_drive_and_col_one t t 0 r u q
    (fun s hs => by rw [Nat.zero_add]; exact hw0 s hs)
    (fun s hs => by rw [Nat.zero_add, rdrv_diag_eq_rhCenter]; exact hw1 s hs)
    hq1 huq
  rwa [Nat.zero_add] at h

/-- **1-Step White Propagation from Three Consecutive White Cells in `rdrv` (`rdrv_white_step_of_three_white`, 9.1275, `kit [33]`)**:
    for all `td, tx, k, p ∈ ℕ`, if `rdrv td tx k p = false`, `rdrv td tx k (p + 1) = false`, and `rdrv td tx k (p + 2) = false`, then `rdrv td tx (k + 1) (p + 1) = false`! -/
theorem rdrv_white_step_of_three_white (td tx k p : Nat)
    (hw0 : rdrv td tx k p = false)
    (hw1 : rdrv td tx k (p + 1) = false)
    (hw2 : rdrv td tx k (p + 2) = false) :
    rdrv td tx (k + 1) (p + 1) = false := by
  rw [rdrv_step_succ td tx k p, hw0, hw1, hw2, Bool.false_or, bxor_eq_xor]
  rfl

/-- **Outward Right-Going White Triangle from a White Boundary Column `p` and Spatial White Interval (`rdrv_white_triangle_of_white_col_and_spatial_interval`, 9.1276, `kit [33]`)**:
    for all `td, tx, a, p, r, u, q ∈ ℕ`, if `rdrv td tx (a + s) p = false` for all `s < r`, `rdrv td tx a (p + j) = false` for all `1 ≤ j ≤ r + 1`, `1 ≤ q`, and `u + q ≤ r + 1`, then `rdrv td tx (a + u) (p + q) = false`! -/
theorem rdrv_white_triangle_of_white_col_and_spatial_interval (td tx a p r u q : Nat)
    (hw : ∀ s : Nat, s < r → rdrv td tx (a + s) p = false)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ r + 1 → rdrv td tx a (p + j) = false)
    (hq1 : 1 ≤ q) (huq : u + q ≤ r + 1) :
    rdrv td tx (a + u) (p + q) = false := by
  induction u generalizing q with
  | zero =>
    rw [Nat.add_zero]
    exact hsp q hq1 (by omega)
  | succ u ih =>
    rw [show a + (u + 1) = (a + u) + 1 by omega,
        show p + q = (p + (q - 1)) + 1 by omega]
    refine rdrv_white_step_of_three_white td tx (a + u) (p + (q - 1)) ?_ ?_ ?_
    · by_cases hq2 : q = 1
      · subst hq2
        rw [Nat.sub_self, Nat.add_zero]
        exact hw u (by omega)
      · exact ih (q - 1) (by omega) (by omega)
    · rw [show (p + (q - 1)) + 1 = p + q by omega]
      exact ih q hq1 (by omega)
    · rw [show (p + (q - 1)) + 2 = p + (q + 1) by omega]
      exact ih (q + 1) (by omega) (by omega)

/-- **Pure Spatial White-Diamond Propagation in `rdrv` (`rdrv_white_diamond_of_spatial_white_interval`, 9.1277, `kit [33]`)**:
    for all `td, tx, a, p, L, u, q ∈ ℕ`, if `rdrv td tx a (p + j) = false` for all `1 ≤ j ≤ L`, `u + 1 ≤ q`, and `u + q ≤ L`, then `rdrv td tx (a + u) (p + q) = false` (with NO assumption on column `p`!)! -/
theorem rdrv_white_diamond_of_spatial_white_interval (td tx a p L u q : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → rdrv td tx a (p + j) = false)
    (hu1 : u + 1 ≤ q) (hu2 : u + q ≤ L) :
    rdrv td tx (a + u) (p + q) = false := by
  induction u generalizing q with
  | zero =>
    rw [Nat.add_zero]
    exact hsp q (by omega) (by omega)
  | succ u ih =>
    rw [show a + (u + 1) = (a + u) + 1 by omega,
        show p + q = (p + (q - 1)) + 1 by omega]
    refine rdrv_white_step_of_three_white td tx (a + u) (p + (q - 1)) ?_ ?_ ?_
    · exact ih (q - 1) (by omega) (by omega)
    · rw [show (p + (q - 1)) + 1 = p + q by omega]
      exact ih q (by omega) (by omega)
    · rw [show (p + (q - 1)) + 2 = p + (q + 1) by omega]
      exact ih (q + 1) (by omega) (by omega)

/-- **2-Cell White Super-Diagonal Corridor Generated by a Spatial White Interval in `rdrv` (`rdrv_superdiag_white_corridor_of_spatial_white_interval`, 9.1278, `kit [33]`)**:
    for all `td, tx, a, p, L, u ∈ ℕ`, if `rdrv td tx a (p + j) = false` for all `1 ≤ j ≤ L` and `2 * u + 2 ≤ L`, then `rdrv td tx (a + u) (p + (u + 1)) = false ∧ rdrv td tx (a + u) (p + (u + 2)) = false`! -/
theorem rdrv_superdiag_white_corridor_of_spatial_white_interval (td tx a p L u : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → rdrv td tx a (p + j) = false)
    (huL : 2 * u + 2 ≤ L) :
    rdrv td tx (a + u) (p + (u + 1)) = false ∧
      rdrv td tx (a + u) (p + (u + 2)) = false := by
  refine ⟨?_, ?_⟩
  · exact rdrv_white_diamond_of_spatial_white_interval td tx a p L u (u + 1) hsp (by omega) (by omega)
  · exact rdrv_white_diamond_of_spatial_white_interval td tx a p L u (u + 2) hsp (by omega) (by omega)

/-- **Pure Spatial White-Diamond Propagation in `rhCenter` (`rhCenter_white_diamond_of_spatial_white_interval`, 9.1279, `kit [33]`)**:
    for all `t, p, L, u, q ∈ ℕ`, if `rhCenter t (p + j) = false` for all `1 ≤ j ≤ L`, `u + 1 ≤ q`, and `u + q ≤ L`, then `rhCenter (t + u) (p + q) = false`! -/
theorem rhCenter_white_diamond_of_spatial_white_interval (t p L u q : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → rhCenter t (p + j) = false)
    (hu1 : u + 1 ≤ q) (hu2 : u + q ≤ L) :
    rhCenter (t + u) (p + q) = false := by
  rw [← rdrv_diag_eq_rhCenter t u (p + q)]
  have h := rdrv_white_diamond_of_spatial_white_interval t t 0 p L u q
    (fun j hj1 hj2 => by
      rw [rdrv_init t t (p + j) (by omega)]
      exact hsp j hj1 hj2)
    hu1 hu2
  rwa [Nat.zero_add] at h

/-- **2-Cell White Super-Diagonal Corridor in `rhCenter` Generated by a Spatial White Interval (`rhCenter_superdiag_white_corridor_of_spatial_white_interval`, 9.1280, `kit [33]`)**:
    for all `t, B, L, u ∈ ℕ`, if `rhCenter t (B + j) = false` for all `1 ≤ j ≤ L` and `2 * u + 2 ≤ L`, then `rhCenter (t + u) (u + (B + 1)) = false ∧ rhCenter (t + u) (u + (B + 2)) = false`! -/
theorem rhCenter_superdiag_white_corridor_of_spatial_white_interval (t B L u : Nat)
    (hsp : ∀ j : Nat, 1 ≤ j → j ≤ L → rhCenter t (B + j) = false)
    (huL : 2 * u + 2 ≤ L) :
    rhCenter (t + u) (u + (B + 1)) = false ∧
      rhCenter (t + u) (u + (B + 2)) = false := by
  refine ⟨?_, ?_⟩
  · rw [show u + (B + 1) = B + (u + 1) by omega]
    exact rhCenter_white_diamond_of_spatial_white_interval t B L u (u + 1) hsp (by omega) (by omega)
  · rw [show u + (B + 2) = B + (u + 2) by omega]
    exact rhCenter_white_diamond_of_spatial_white_interval t B L u (u + 2) hsp (by omega) (by omega)

/-- **Expanding Trapezoid Collapse to `rdrv td 0` from a Single-Slice Wide White Band (`rdrv_trapezoid_eq_white_seed_of_wide_white_band`, 9.1281, `kit [33]`)**:
    for all `td, tx, B, k, p ∈ ℕ`, if `rhCenter tx (1 + i) = false` for all `i ≤ B + (2 * k + 2)` and `p ≤ k + (B + 1)`, then `rdrv td tx k p = rdrv td 0 k p`! -/
theorem rdrv_trapezoid_eq_white_seed_of_wide_white_band (td tx B k p : Nat)
    (hw : ∀ i : Nat, i ≤ B + (2 * k + 2) → rhCenter tx (1 + i) = false)
    (hpk : p ≤ k + (B + 1)) :
    rdrv td tx k p = rdrv td 0 k p := by
  refine rdrv_trapezoid_eq_white_seed_of_white_band_and_corridor td tx B k p
    (fun i hi => hw i (by omega))
    (fun u hu => ?_) hpk
  refine rhCenter_superdiag_white_corridor_of_spatial_white_interval tx B (2 * k + 2) u
    (fun j hj1 hj2 => ?_) (by omega)
  have h := hw (B + j - 1) (by omega)
  rwa [show 1 + (B + j - 1) = B + j by omega] at h

/-! ### Batch 66: Main-Diagonal & Sub-Diagonal `accum_shift` Defect Laws and Unconditional `2^(k + 1 + c)`-Periodicity in `u` of `rdrv` (`kit [33]`, 9.1282–9.1296) -/

/-- **1-Step Main-Diagonal Recurrence of `rdrv` Driven by Super-Diagonals `1` and `2` of `rhCenter` (`rdrv_main_diag_step_eq_rhCenter`, 9.1282, `kit [33]`)**:
    for all `td, tx, u ∈ ℕ`, `rdrv td tx (u + 1) (u + 1) = bxor (rdrv td tx u u) (rhCenter (tx + u) (u + 1) || rhCenter (tx + u) (u + 2))`! -/
theorem rdrv_main_diag_step_eq_rhCenter (td tx u : Nat) :
    rdrv td tx (u + 1) (u + 1) =
      bxor (rdrv td tx u u)
        (rhCenter (tx + u) (u + 1) || rhCenter (tx + u) (u + 2)) := by
  rw [rdrv_step_succ td tx u u,
      rdrv_outside_cone_eq_rhCenter td tx u (u + 1) (by omega),
      rdrv_outside_cone_eq_rhCenter td tx u (u + 2) (by omega)]

/-- **Main-Diagonal `H`-Shift Defect Invariance (`accum_shift`) in `rdrv` (`rdrv_main_diag_accum_shift_xor`, 9.1283, `kit [33]`)**:
    for all `td, tx, a, H, n ∈ ℕ`, if the OR of super-diagonals `1` and `2` of `rhCenter` repeats with shift `H` across `[a, a + n)`, then `bxor (rdrv td tx ((a + H) + n) ((a + H) + n)) (rdrv td tx (a + n) (a + n)) = bxor (rdrv td tx (a + H) (a + H)) (rdrv td tx a a)`! -/
theorem rdrv_main_diag_accum_shift_xor (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < n →
      (rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 1) ||
        rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 2)) =
      (rhCenter (tx + (a + u)) ((a + u) + 1) ||
        rhCenter (tx + (a + u)) ((a + u) + 2))) :
    bxor (rdrv td tx ((a + H) + n) ((a + H) + n))
         (rdrv td tx (a + n) (a + n)) =
      bxor (rdrv td tx (a + H) (a + H))
           (rdrv td tx a a) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero]
  | succ n ih =>
    rw [show (a + H) + (n + 1) = ((a + H) + n) + 1 by omega,
        show a + (n + 1) = (a + n) + 1 by omega,
        rdrv_main_diag_step_eq_rhCenter td tx ((a + H) + n),
        rdrv_main_diag_step_eq_rhCenter td tx (a + n),
        hor n (by omega),
        ← ih (fun u hu => hor u (by omega))]
    simp only [bxor_eq_xor]
    cases rdrv td tx ((a + H) + n) ((a + H) + n) <;>
      cases rdrv td tx (a + n) (a + n) <;>
      cases (rhCenter (tx + (a + n)) ((a + n) + 1) ||
        rhCenter (tx + (a + n)) ((a + n) + 2)) <;> rfl

/-- **Main-Diagonal `2 * H` Period-Doubling from `H`-Periodicity of the Super-Diagonal OR Gate (`rdrv_main_diag_period_double_of_superdiag_or_period`, 9.1284, `kit [33]`)**:
    for all `td, tx, a, H, n ∈ ℕ`, if the OR of super-diagonals `1` and `2` of `rhCenter` repeats with period `H` for `u < H + n`, then `rdrv td tx ((a + 2 * H) + n) ((a + 2 * H) + n) = rdrv td tx (a + n) (a + n)`! -/
theorem rdrv_main_diag_period_double_of_superdiag_or_period (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < H + n →
      (rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 1) ||
        rhCenter (tx + ((a + H) + u)) (((a + H) + u) + 2)) =
      (rhCenter (tx + (a + u)) ((a + u) + 1) ||
        rhCenter (tx + (a + u)) ((a + u) + 2))) :
    rdrv td tx ((a + 2 * H) + n) ((a + 2 * H) + n) =
      rdrv td tx (a + n) (a + n) := by
  have hx1 := rdrv_main_diag_accum_shift_xor td tx a H n (fun u hu => hor u (by omega))
  have hx2 := rdrv_main_diag_accum_shift_xor td tx a H (H + n) hor
  rw [show (a + H) + (H + n) = (a + 2 * H) + n by omega,
      show a + (H + n) = (a + H) + n by omega,
      ← hx1] at hx2
  revert hx2
  simp only [bxor_eq_xor]
  cases rdrv td tx ((a + 2 * H) + n) ((a + 2 * H) + n) <;>
    cases rdrv td tx ((a + H) + n) ((a + H) + n) <;>
    cases rdrv td tx (a + n) (a + n) <;> decide

/-- **Unconditional `2^(k + 1)`-Periodicity in `u` of the Main Diagonal `rdrv td tx u u` (`rdrv_main_diag_period_twopow_succ`, 9.1285, `kit [33]`)**:
    for all `td, tx, k, u ∈ ℕ` with `tx - 1 ≤ k` (and NO hypothesis on the center drive `td`!), `rdrv td tx (u + 2^(k + 1)) (u + 2^(k + 1)) = rdrv td tx u u`! -/
theorem rdrv_main_diag_period_twopow_succ (td tx k u : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx (u + twopow (k + 1)) (u + twopow (k + 1)) =
      rdrv td tx u u := by
  have h := rdrv_main_diag_period_double_of_superdiag_or_period td tx 0 (twopow k) u
    (fun w _ => by
      have h1 := rhCenter_superdiag_period_twopow tx 1 k w 1 htc
      have h2 := rhCenter_superdiag_period_twopow tx 2 k w 1 (by omega)
      rw [Nat.one_mul] at h1 h2
      rw [Nat.zero_add, Nat.zero_add,
          show twopow k + w = w + twopow k by omega,
          h1, h2])
  have h2 : (0 + 2 * twopow k) + u = u + twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rwa [h2, Nat.zero_add] at h

/-- **Right-Threshold `2^(k + 1)`-Periodicity in `u` of the Main Diagonal `rdrv td tx u u` (`rdrv_main_diag_period_twopow_succ_of_threshold`, 9.1286, `kit [33]`)**:
    for all `td, tx, k, J, u ∈ ℕ` with `IsRightThreshold k J` and `tx - 1 ≤ J`, `rdrv td tx (u + 2^(k + 1)) (u + 2^(k + 1)) = rdrv td tx u u`! -/
theorem rdrv_main_diag_period_twopow_succ_of_threshold (td tx k J u : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    rdrv td tx (u + twopow (k + 1)) (u + twopow (k + 1)) =
      rdrv td tx u u := by
  have h := rdrv_main_diag_period_double_of_superdiag_or_period td tx 0 (twopow k) u
    (fun w _ => by
      have h1 := rhCenter_superdiag_period_twopow_of_threshold tx 1 k J w 1 hJ htc
      have h2 := rhCenter_superdiag_period_twopow_of_threshold tx 2 k J w 1 hJ (by omega)
      rw [Nat.one_mul] at h1 h2
      rw [Nat.zero_add, Nat.zero_add,
          show twopow k + w = w + twopow k by omega,
          h1, h2])
  have h2 : (0 + 2 * twopow k) + u = u + twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rwa [h2, Nat.zero_add] at h

/-- **Multi-Period `v * 2^(k + 1)`-Invariance in `u` of the Main Diagonal `rdrv td tx u u` (`rdrv_main_diag_period_twopow_succ_mul`, 9.1287, `kit [33]`)**:
    for all `td, tx, k, u, v ∈ ℕ` with `tx - 1 ≤ k`, `rdrv td tx (u + v * 2^(k + 1)) (u + v * twopow (k + 1)) = rdrv td tx u u`! -/
theorem rdrv_main_diag_period_twopow_succ_mul (td tx k u v : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx (u + v * twopow (k + 1)) (u + v * twopow (k + 1)) =
      rdrv td tx u u := by
  induction v with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
  | succ v ih =>
    have hmul : u + (v + 1) * twopow (k + 1) = (u + v * twopow (k + 1)) + twopow (k + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hmul,
        rdrv_main_diag_period_twopow_succ td tx k (u + v * twopow (k + 1)) htc,
        ih]

/-- **All-Time Main-Diagonal Agreement from a Single `2^(k + 1)` Fundamental Period (`rdrv_main_diag_agree_all_of_lt_twopow_succ`, 9.1288, `kit [33]`)**:
    for all `td, tx, Q, k, u ∈ ℕ` with `(tx + Q) - 1 ≤ k`, if `rdrv td (tx + Q) r r = rdrv td tx r r` for all `r < 2^(k + 1)`, then `rdrv td (tx + Q) u u = rdrv td tx u u` for ALL `u ∈ ℕ`! -/
theorem rdrv_main_diag_agree_all_of_lt_twopow_succ (td tx Q k u : Nat)
    (htc : (tx + Q) - 1 ≤ k)
    (h : ∀ r : Nat, r < twopow (k + 1) → rdrv td (tx + Q) r r = rdrv td tx r r) :
    rdrv td (tx + Q) u u = rdrv td tx u u := by
  have hpos : 0 < twopow (k + 1) := by
    rw [twopow_eq_pow (k + 1)]
    exact Nat.two_pow_pos (k + 1)
  have hr : u % twopow (k + 1) < twopow (k + 1) := Nat.mod_lt u hpos
  have heq : u % twopow (k + 1) + (u / twopow (k + 1)) * twopow (k + 1) = u := by
    have hdiv := Nat.div_add_mod u (twopow (k + 1))
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq,
      rdrv_main_diag_period_twopow_succ_mul td (tx + Q) k (u % twopow (k + 1)) (u / twopow (k + 1)) htc,
      rdrv_main_diag_period_twopow_succ_mul td tx k (u % twopow (k + 1)) (u / twopow (k + 1)) (by omega)]
  exact h (u % twopow (k + 1)) hr

/-- **1-Step Sub-Diagonal `1` Recurrence Driven by the Main Diagonal and Super-Diagonal `1` (`rdrv_subdiag_one_step_eq_rhCenter`, 9.1289, `kit [33]`)**:
    for all `td, tx, u ∈ ℕ`, `rdrv td tx ((u + 1) + 1) (u + 1) = bxor (rdrv td tx (u + 1) u) (rdrv td tx (u + 1) (u + 1) || rhCenter (tx + (u + 1)) ((u + 1) + 1))`! -/
theorem rdrv_subdiag_one_step_eq_rhCenter (td tx u : Nat) :
    rdrv td tx ((u + 1) + 1) (u + 1) =
      bxor (rdrv td tx (u + 1) u)
        (rdrv td tx (u + 1) (u + 1) || rhCenter (tx + (u + 1)) ((u + 1) + 1)) := by
  rw [rdrv_step_succ td tx (u + 1) u,
      rdrv_outside_cone_eq_rhCenter td tx (u + 1) ((u + 1) + 1) (by omega)]

/-- **Sub-Diagonal `1` `H`-Shift Defect Invariance (`accum_shift`) in `rdrv` (`rdrv_subdiag_one_accum_shift_xor`, 9.1290, `kit [33]`)**:
    for all `td, tx, a, H, n ∈ ℕ`, if the OR of the main diagonal and super-diagonal `1` repeats with shift `H` across `[a, a + n)`, then `bxor (rdrv td tx (((a + H) + n) + 1) ((a + H) + n)) (rdrv td tx ((a + n) + 1) (a + n)) = bxor (rdrv td tx ((a + H) + 1) (a + H)) (rdrv td tx (a + 1) a)`! -/
theorem rdrv_subdiag_one_accum_shift_xor (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < n →
      (rdrv td tx ((a + H) + (u + 1)) ((a + H) + (u + 1)) ||
        rhCenter (tx + ((a + H) + (u + 1))) (((a + H) + (u + 1)) + 1)) =
      (rdrv td tx (a + (u + 1)) (a + (u + 1)) ||
        rhCenter (tx + (a + (u + 1))) ((a + (u + 1)) + 1))) :
    bxor (rdrv td tx (((a + H) + n) + 1) ((a + H) + n))
         (rdrv td tx ((a + n) + 1) (a + n)) =
      bxor (rdrv td tx ((a + H) + 1) (a + H))
           (rdrv td tx (a + 1) a) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero]
  | succ n ih =>
    rw [show (a + H) + (n + 1) = ((a + H) + n) + 1 by omega,
        show a + (n + 1) = (a + n) + 1 by omega,
        rdrv_subdiag_one_step_eq_rhCenter td tx ((a + H) + n),
        rdrv_subdiag_one_step_eq_rhCenter td tx (a + n),
        show ((a + H) + n) + 1 = (a + H) + (n + 1) by omega,
        show (a + n) + 1 = a + (n + 1) by omega,
        hor n (by omega),
        ← ih (fun u hu => hor u (by omega))]
    simp only [bxor_eq_xor]
    cases rdrv td tx (((a + H) + n) + 1) ((a + H) + n) <;>
      cases rdrv td tx ((a + n) + 1) (a + n) <;>
      cases (rdrv td tx (a + (n + 1)) (a + (n + 1)) ||
        rhCenter (tx + (a + (n + 1))) ((a + (n + 1)) + 1)) <;> rfl

/-- **Sub-Diagonal `1` `2 * H` Period-Doubling from `H`-Periodicity of the Main/Super-Diagonal OR Gate (`rdrv_subdiag_one_period_double_of_or_period`, 9.1291, `kit [33]`)**:
    for all `td, tx, a, H, n ∈ ℕ`, if the OR of the main diagonal and super-diagonal `1` repeats with period `H` for `u < H + n`, then `rdrv td tx (((a + 2 * H) + n) + 1) ((a + 2 * H) + n) = rdrv td tx ((a + n) + 1) (a + n)`! -/
theorem rdrv_subdiag_one_period_double_of_or_period (td tx a H n : Nat)
    (hor : ∀ u : Nat, u < H + n →
      (rdrv td tx ((a + H) + (u + 1)) ((a + H) + (u + 1)) ||
        rhCenter (tx + ((a + H) + (u + 1))) (((a + H) + (u + 1)) + 1)) =
      (rdrv td tx (a + (u + 1)) (a + (u + 1)) ||
        rhCenter (tx + (a + (u + 1))) ((a + (u + 1)) + 1))) :
    rdrv td tx (((a + 2 * H) + n) + 1) ((a + 2 * H) + n) =
      rdrv td tx ((a + n) + 1) (a + n) := by
  have hx1 := rdrv_subdiag_one_accum_shift_xor td tx a H n (fun u hu => hor u (by omega))
  have hx2 := rdrv_subdiag_one_accum_shift_xor td tx a H (H + n) hor
  rw [show (a + H) + (H + n) = (a + 2 * H) + n by omega,
      show a + (H + n) = (a + H) + n by omega,
      ← hx1] at hx2
  revert hx2
  simp only [bxor_eq_xor]
  cases rdrv td tx (((a + 2 * H) + n) + 1) ((a + 2 * H) + n) <;>
    cases rdrv td tx (((a + H) + n) + 1) ((a + H) + n) <;>
    cases rdrv td tx ((a + n) + 1) (a + n) <;> decide

/-- **Unconditional `2^(k + 2)`-Periodicity in `u` of Sub-Diagonal `1` (`rdrv_subdiag_one_period_twopow_succ_two`, 9.1292, `kit [33]`)**:
    for all `td, tx, k, u ∈ ℕ` with `tx - 1 ≤ k` (and NO hypothesis on the center drive `td`!), `rdrv td tx ((u + 2^(k + 2)) + 1) (u + 2^(k + 2)) = rdrv td tx (u + 1) u`! -/
theorem rdrv_subdiag_one_period_twopow_succ_two (td tx k u : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx ((u + twopow (k + 2)) + 1) (u + twopow (k + 2)) =
      rdrv td tx (u + 1) u := by
  have h := rdrv_subdiag_one_period_double_of_or_period td tx 0 (twopow (k + 1)) u
    (fun w _ => by
      have hm := rdrv_main_diag_period_twopow_succ td tx k (w + 1) htc
      have hs := rhCenter_superdiag_period_twopow tx 1 k (w + 1) 2 htc
      have h2k : 2 * twopow k = twopow (k + 1) := by rw [twopow_succ]; omega
      rw [h2k] at hs
      rw [Nat.zero_add, Nat.zero_add,
          show twopow (k + 1) + (w + 1) = (w + 1) + twopow (k + 1) by omega,
          hm, hs])
  have h2 : (0 + 2 * twopow (k + 1)) + u = u + twopow (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega, twopow_succ (k + 1)]
    omega
  rwa [h2, Nat.zero_add] at h

/-- **Right-Threshold `2^(k + 2)`-Periodicity in `u` of Sub-Diagonal `1` (`rdrv_subdiag_one_period_twopow_succ_two_of_threshold`, 9.1293, `kit [33]`)**:
    for all `td, tx, k, J, u ∈ ℕ` with `IsRightThreshold k J` and `tx - 1 ≤ J`, `rdrv td tx ((u + 2^(k + 2)) + 1) (u + 2^(k + 2)) = rdrv td tx (u + 1) u`! -/
theorem rdrv_subdiag_one_period_twopow_succ_two_of_threshold (td tx k J u : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    rdrv td tx ((u + twopow (k + 2)) + 1) (u + twopow (k + 2)) =
      rdrv td tx (u + 1) u := by
  have h := rdrv_subdiag_one_period_double_of_or_period td tx 0 (twopow (k + 1)) u
    (fun w _ => by
      have hm := rdrv_main_diag_period_twopow_succ_of_threshold td tx k J (w + 1) hJ htc
      have hs := rhCenter_superdiag_period_twopow_of_threshold tx 1 k J (w + 1) 2 hJ htc
      have h2k : 2 * twopow k = twopow (k + 1) := by rw [twopow_succ]; omega
      rw [h2k] at hs
      rw [Nat.zero_add, Nat.zero_add,
          show twopow (k + 1) + (w + 1) = (w + 1) + twopow (k + 1) by omega,
          hm, hs])
  have h2 : (0 + 2 * twopow (k + 1)) + u = u + twopow (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega, twopow_succ (k + 1)]
    omega
  rwa [h2, Nat.zero_add] at h

/-- **Universal Sub-Diagonal `2^(k + 1 + c)`-Periodicity Law in `u` for `rdrv` (`rdrv_subdiag_period_twopow_all`, 9.1294, `kit [33]`)**:
    for all `td, tx, k, c, u ∈ ℕ` with `tx - 1 ≤ k` (and NO hypothesis on the center drive `td`!), the `c`-th sub-diagonal `u ↦ rdrv td tx (u + c) u` is periodic in `u` with period `2^(k + 1 + c)`: `rdrv td tx ((u + 2^(k + 1 + c)) + c) (u + 2^(k + 1 + c)) = rdrv td tx (u + c) u`! -/
theorem rdrv_subdiag_period_twopow_all (td tx k c u : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx ((u + twopow ((k + 1) + c)) + c) (u + twopow ((k + 1) + c)) =
      rdrv td tx (u + c) u := by
  suffices hpair :
      (∀ w : Nat,
        rdrv td tx ((w + twopow ((k + 1) + c)) + c) (w + twopow ((k + 1) + c)) =
          rdrv td tx (w + c) w) ∧
      (∀ w : Nat,
        rdrv td tx ((w + twopow ((k + 1) + (c + 1))) + (c + 1)) (w + twopow ((k + 1) + (c + 1))) =
          rdrv td tx (w + (c + 1)) w) from hpair.1 u
  induction c with
  | zero =>
    refine ⟨fun w => ?_, fun w => ?_⟩
    · simp only [Nat.add_zero]
      exact rdrv_main_diag_period_twopow_succ td tx k w htc
    · rw [Nat.zero_add, show (k + 1) + 1 = k + 2 by omega]
      exact rdrv_subdiag_one_period_twopow_succ_two td tx k w htc
  | succ c ih =>
    refine ⟨ih.2, fun w => ?_⟩
    have hd := rdrv_subdiag_period_double_of_two_prev_periods
      td tx c 0 (twopow ((k + 1) + (c + 1))) w
      (fun v _ => by
        rw [Nat.zero_add, Nat.zero_add,
            show twopow ((k + 1) + (c + 1)) + v = v + twopow ((k + 1) + (c + 1)) by omega]
        exact ih.2 v)
      (fun v _ => by
        rw [Nat.zero_add, Nat.zero_add,
            show twopow ((k + 1) + (c + 1)) + v =
              (v + twopow ((k + 1) + c)) + twopow ((k + 1) + c) by
              rw [show (k + 1) + (c + 1) = ((k + 1) + c) + 1 by omega, twopow_succ]
              omega,
            ih.1 (v + twopow ((k + 1) + c)),
            ih.1 v])
    have h2 : (0 + 2 * twopow ((k + 1) + (c + 1))) + w = w + twopow ((k + 1) + (c + 1 + 1)) := by
      rw [show (k + 1) + (c + 1 + 1) = ((k + 1) + (c + 1)) + 1 by omega, twopow_succ]
      omega
    rwa [h2, Nat.zero_add] at hd

/-- **Multi-Period `v * 2^(k + 1 + c)`-Invariance in `u` of Sub-Diagonal `c` in `rdrv` (`rdrv_subdiag_period_twopow_all_mul`, 9.1295, `kit [33]`)**:
    for all `td, tx, k, c, u, v ∈ ℕ` with `tx - 1 ≤ k`, `rdrv td tx ((u + v * 2^(k + 1 + c)) + c) (u + v * 2^(k + 1 + c)) = rdrv td tx (u + c) u`! -/
theorem rdrv_subdiag_period_twopow_all_mul (td tx k c u v : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx ((u + v * twopow ((k + 1) + c)) + c) (u + v * twopow ((k + 1) + c)) =
      rdrv td tx (u + c) u := by
  induction v with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
  | succ v ih =>
    have hmul : u + (v + 1) * twopow ((k + 1) + c) =
        (u + v * twopow ((k + 1) + c)) + twopow ((k + 1) + c) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hmul,
        rdrv_subdiag_period_twopow_all td tx k c (u + v * twopow ((k + 1) + c)) htc,
        ih]

/-- **Right-Threshold Universal Sub-Diagonal `2^(k + 1 + c)`-Periodicity Law in `u` for `rdrv` (`rdrv_subdiag_period_twopow_all_of_threshold`, 9.1296, `kit [33]`)**:
    for all `td, tx, k, J, c, u ∈ ℕ` with `IsRightThreshold k J` and `tx - 1 ≤ J` (and NO hypothesis on the center drive `td`!), `rdrv td tx ((u + 2^(k + 1 + c)) + c) (u + 2^(k + 1 + c)) = rdrv td tx (u + c) u`! -/
theorem rdrv_subdiag_period_twopow_all_of_threshold (td tx k J c u : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    rdrv td tx ((u + twopow ((k + 1) + c)) + c) (u + twopow ((k + 1) + c)) =
      rdrv td tx (u + c) u := by
  suffices hpair :
      (∀ w : Nat,
        rdrv td tx ((w + twopow ((k + 1) + c)) + c) (w + twopow ((k + 1) + c)) =
          rdrv td tx (w + c) w) ∧
      (∀ w : Nat,
        rdrv td tx ((w + twopow ((k + 1) + (c + 1))) + (c + 1)) (w + twopow ((k + 1) + (c + 1))) =
          rdrv td tx (w + (c + 1)) w) from hpair.1 u
  induction c with
  | zero =>
    refine ⟨fun w => ?_, fun w => ?_⟩
    · simp only [Nat.add_zero]
      exact rdrv_main_diag_period_twopow_succ_of_threshold td tx k J w hJ htc
    · rw [Nat.zero_add, show (k + 1) + 1 = k + 2 by omega]
      exact rdrv_subdiag_one_period_twopow_succ_two_of_threshold td tx k J w hJ htc
  | succ c ih =>
    refine ⟨ih.2, fun w => ?_⟩
    have hd := rdrv_subdiag_period_double_of_two_prev_periods
      td tx c 0 (twopow ((k + 1) + (c + 1))) w
      (fun v _ => by
        rw [Nat.zero_add, Nat.zero_add,
            show twopow ((k + 1) + (c + 1)) + v = v + twopow ((k + 1) + (c + 1)) by omega]
        exact ih.2 v)
      (fun v _ => by
        rw [Nat.zero_add, Nat.zero_add,
            show twopow ((k + 1) + (c + 1)) + v =
              (v + twopow ((k + 1) + c)) + twopow ((k + 1) + c) by
              rw [show (k + 1) + (c + 1) = ((k + 1) + c) + 1 by omega, twopow_succ]
              omega,
            ih.1 (v + twopow ((k + 1) + c)),
            ih.1 v])
    have h2 : (0 + 2 * twopow ((k + 1) + (c + 1))) + w = w + twopow ((k + 1) + (c + 1 + 1)) := by
      rw [show (k + 1) + (c + 1 + 1) = ((k + 1) + (c + 1)) + 1 by omega, twopow_succ]
      omega
    rwa [h2, Nat.zero_add] at hd

/-! ### Batch 67: Exact Center-Drive Replication Along Dyadic Columns (`u = v * 2^((k + 1) + c)`), Column-`1` Dyadic Lift (`u = 1 + v * 2^((k + 1) + c)`), and All-`u` Sub-Diagonal Agreement (`kit [33]`, 9.1297–9.1311) -/

/-- **Exact Center-Drive Replication on the Main Diagonal at Multiples of `2^(k + 1)` (`rdrv_main_diag_at_twopow_succ_eq_center`, 9.1297, `kit [33]`)**:
    for all `td, tx, k, v ∈ ℕ` with `tx - 1 ≤ k`, `rdrv td tx (v * 2^(k + 1)) (v * 2^(k + 1)) = center td` — independent of `tx` and `v`! -/
theorem rdrv_main_diag_at_twopow_succ_eq_center (td tx k v : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx (v * twopow (k + 1)) (v * twopow (k + 1)) =
      Rule30UOR.Core.center td := by
  have h := rdrv_main_diag_period_twopow_succ_mul td tx k 0 v htc
  rw [Nat.zero_add, rdrv_col0, Nat.add_zero] at h
  exact h

/-- **Exact Center-Drive Replication on Sub-Diagonal `c` at Multiples of `2^((k + 1) + c)` (`rdrv_subdiag_at_twopow_all_eq_center`, 9.1298, `kit [33]`)**:
    for all `td, tx, k, c, v ∈ ℕ` with `tx - 1 ≤ k`, `rdrv td tx ((v * 2^((k + 1) + c)) + c) (v * 2^((k + 1) + c)) = center (td + c)` — independent of `tx` and `v`! -/
theorem rdrv_subdiag_at_twopow_all_eq_center (td tx k c v : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx ((v * twopow ((k + 1) + c)) + c) (v * twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (td + c) := by
  have h := rdrv_subdiag_period_twopow_all_mul td tx k c 0 v htc
  rw [Nat.zero_add, Nat.zero_add, rdrv_col0] at h
  exact h

/-- **Right-Threshold Center-Drive Replication on Sub-Diagonal `c` at `2^((k + 1) + c)` (`rdrv_subdiag_at_twopow_all_eq_center_of_threshold`, 9.1299, `kit [33]`)**:
    for all `td, tx, k, J, c ∈ ℕ` with `IsRightThreshold k J` and `tx - 1 ≤ J`, `rdrv td tx (2^((k + 1) + c) + c) (2^((k + 1) + c)) = center (td + c)`! -/
theorem rdrv_subdiag_at_twopow_all_eq_center_of_threshold (td tx k J c : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    rdrv td tx (twopow ((k + 1) + c) + c) (twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (td + c) := by
  have h := rdrv_subdiag_period_twopow_all_of_threshold td tx k J c 0 hJ htc
  rw [Nat.zero_add, Nat.zero_add, rdrv_col0] at h
  exact h

/-- **Exact Center Replication Inside `rhCenter` at Dyadic Columns `v * 2^((k + 1) + c)` (`rhCenter_subdiag_at_twopow_all_eq_center`, 9.1300, `kit [33]`)**:
    for all `t, k, c, v ∈ ℕ` with `t - 1 ≤ k`, `rhCenter (t + ((v * 2^((k + 1) + c)) + c)) (v * 2^((k + 1) + c)) = center (t + c)`! -/
theorem rhCenter_subdiag_at_twopow_all_eq_center (t k c v : Nat) (htc : t - 1 ≤ k) :
    rhCenter (t + ((v * twopow ((k + 1) + c)) + c)) (v * twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (t + c) := by
  rw [← rdrv_diag_eq_rhCenter t ((v * twopow ((k + 1) + c)) + c) (v * twopow ((k + 1) + c))]
  exact rdrv_subdiag_at_twopow_all_eq_center t t k c v htc

/-- **Right-Threshold Center Replication Inside `rhCenter` at `2^((k + 1) + c)` (`rhCenter_subdiag_at_twopow_all_eq_center_of_threshold`, 9.1301, `kit [33]`)**:
    for all `t, k, J, c ∈ ℕ` with `IsRightThreshold k J` and `t - 1 ≤ J`, `rhCenter (t + (2^((k + 1) + c) + c)) (2^((k + 1) + c)) = center (t + c)`! -/
theorem rhCenter_subdiag_at_twopow_all_eq_center_of_threshold (t k J c : Nat)
    (hJ : IsRightThreshold k J) (htc : t - 1 ≤ J) :
    rhCenter (t + (twopow ((k + 1) + c) + c)) (twopow ((k + 1) + c)) =
      Rule30UOR.Core.center (t + c) := by
  rw [← rdrv_diag_eq_rhCenter t (twopow ((k + 1) + c) + c) (twopow ((k + 1) + c))]
  exact rdrv_subdiag_at_twopow_all_eq_center_of_threshold t t k J c hJ htc

/-- **Unconditional Agreement of Two Driven Trajectories `tx2, tx` at Dyadic Sub-Diagonal Multiples `v * 2^((k + 1) + c)` (`rdrv_subdiag_at_twopow_all_agree`, 9.1302, `kit [33]`)**:
    for all `td, tx2, tx, k, c, v ∈ ℕ` with `tx2 - 1 ≤ k` and `tx - 1 ≤ k` (and NO agreement hypothesis on `tx2` and `tx`!), `rdrv td tx2 ((v * 2^((k + 1) + c)) + c) (v * 2^((k + 1) + c)) = rdrv td tx ((v * 2^((k + 1) + c)) + c) (v * 2^((k + 1) + c))`! -/
theorem rdrv_subdiag_at_twopow_all_agree (td tx2 tx k c v : Nat)
    (htc2 : tx2 - 1 ≤ k) (htc1 : tx - 1 ≤ k) :
    rdrv td tx2 ((v * twopow ((k + 1) + c)) + c) (v * twopow ((k + 1) + c)) =
      rdrv td tx ((v * twopow ((k + 1) + c)) + c) (v * twopow ((k + 1) + c)) := by
  rw [rdrv_subdiag_at_twopow_all_eq_center td tx2 k c v htc2,
      rdrv_subdiag_at_twopow_all_eq_center td tx k c v htc1]

/-- **Exact Dyadic Lift of Column `1` (`rdrv td tx (1 + c) 1`) to Column `1 + v * 2^((k + 1) + c)` (`rdrv_col_one_eq_subdiag_at_twopow_all`, 9.1303, `kit [33]`)**:
    for all `td, tx, k, c, v ∈ ℕ` with `tx - 1 ≤ k`, `rdrv td tx (1 + c) 1 = rdrv td tx ((1 + v * 2^((k + 1) + c)) + c) (1 + v * 2^((k + 1) + c))`! -/
theorem rdrv_col_one_eq_subdiag_at_twopow_all (td tx k c v : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx (1 + c) 1 =
      rdrv td tx ((1 + v * twopow ((k + 1) + c)) + c) (1 + v * twopow ((k + 1) + c)) :=
  (rdrv_subdiag_period_twopow_all_mul td tx k c 1 v htc).symm

/-- **Right-Threshold Dyadic Lift of Column `1` to Column `1 + 2^((k + 1) + c)` (`rdrv_col_one_eq_subdiag_at_twopow_all_of_threshold`, 9.1304, `kit [33]`)**:
    for all `td, tx, k, J, c ∈ ℕ` with `IsRightThreshold k J` and `tx - 1 ≤ J`, `rdrv td tx (1 + c) 1 = rdrv td tx ((1 + 2^((k + 1) + c)) + c) (1 + 2^((k + 1) + c))`! -/
theorem rdrv_col_one_eq_subdiag_at_twopow_all_of_threshold (td tx k J c : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    rdrv td tx (1 + c) 1 =
      rdrv td tx ((1 + twopow ((k + 1) + c)) + c) (1 + twopow ((k + 1) + c)) :=
  (rdrv_subdiag_period_twopow_all_of_threshold td tx k J c 1 hJ htc).symm

/-- **Exact Dyadic Lift of Column `1` in `rhCenter` (`rhCenter (t + (1 + c)) 1`) to Column `1 + v * 2^((k + 1) + c)` (`rhCenter_col_one_eq_subdiag_at_twopow_all`, 9.1305, `kit [33]`)**:
    for all `t, k, c, v ∈ ℕ` with `t - 1 ≤ k`, `rhCenter (t + (1 + c)) 1 = rhCenter (t + ((1 + v * 2^((k + 1) + c)) + c)) (1 + v * 2^((k + 1) + c))`! -/
theorem rhCenter_col_one_eq_subdiag_at_twopow_all (t k c v : Nat) (htc : t - 1 ≤ k) :
    rhCenter (t + (1 + c)) 1 =
      rhCenter (t + ((1 + v * twopow ((k + 1) + c)) + c)) (1 + v * twopow ((k + 1) + c)) := by
  rw [← rdrv_diag_eq_rhCenter t (1 + c) 1,
      ← rdrv_diag_eq_rhCenter t ((1 + v * twopow ((k + 1) + c)) + c) (1 + v * twopow ((k + 1) + c))]
  exact rdrv_col_one_eq_subdiag_at_twopow_all t t k c v htc

/-- **Right-Threshold Dyadic Lift of Column `1` in `rhCenter` to Column `1 + 2^((k + 1) + c)` (`rhCenter_col_one_eq_subdiag_at_twopow_all_of_threshold`, 9.1306, `kit [33]`)**:
    for all `t, k, J, c ∈ ℕ` with `IsRightThreshold k J` and `t - 1 ≤ J`, `rhCenter (t + (1 + c)) 1 = rhCenter (t + ((1 + 2^((k + 1) + c)) + c)) (1 + 2^((k + 1) + c))`! -/
theorem rhCenter_col_one_eq_subdiag_at_twopow_all_of_threshold (t k J c : Nat)
    (hJ : IsRightThreshold k J) (htc : t - 1 ≤ J) :
    rhCenter (t + (1 + c)) 1 =
      rhCenter (t + ((1 + twopow ((k + 1) + c)) + c)) (1 + twopow ((k + 1) + c)) := by
  rw [← rdrv_diag_eq_rhCenter t (1 + c) 1,
      ← rdrv_diag_eq_rhCenter t ((1 + twopow ((k + 1) + c)) + c) (1 + twopow ((k + 1) + c))]
  exact rdrv_col_one_eq_subdiag_at_twopow_all_of_threshold t t k J c hJ htc

/-- **Column-`1` Agreement at Step `1 + c` from Agreement at Dyadic Column `1 + v * 2^((k + 1) + c)` (`rdrv_col_one_agree_of_subdiag_twopow_agree`, 9.1307, `kit [33]`)**:
    for all `td, tx2, tx, k, c, v ∈ ℕ` with `tx2 - 1 ≤ k` and `tx - 1 ≤ k`, if `rdrv td tx2` and `rdrv td tx` agree at `((1 + v * 2^((k + 1) + c)) + c, 1 + v * 2^((k + 1) + c))`, then `rdrv td tx2 (1 + c) 1 = rdrv td tx (1 + c) 1`! -/
theorem rdrv_col_one_agree_of_subdiag_twopow_agree (td tx2 tx k c v : Nat)
    (htc2 : tx2 - 1 ≤ k) (htc1 : tx - 1 ≤ k)
    (h : rdrv td tx2 ((1 + v * twopow ((k + 1) + c)) + c) (1 + v * twopow ((k + 1) + c)) =
         rdrv td tx ((1 + v * twopow ((k + 1) + c)) + c) (1 + v * twopow ((k + 1) + c))) :
    rdrv td tx2 (1 + c) 1 = rdrv td tx (1 + c) 1 := by
  rw [rdrv_col_one_eq_subdiag_at_twopow_all td tx2 k c v htc2,
      rdrv_col_one_eq_subdiag_at_twopow_all td tx k c v htc1, h]

/-- **All-Column Agreement on Sub-Diagonal `c` from a Single `2^((k + 1) + c)` Fundamental Period (`rdrv_subdiag_agree_all_of_lt_twopow_all`, 9.1308, `kit [33]`)**:
    for all `td, tx, Q, k, c, u ∈ ℕ` with `(tx + Q) - 1 ≤ k`, if `rdrv td (tx + Q) (r + c) r = rdrv td tx (r + c) r` for all `r < 2^((k + 1) + c)`, then `rdrv td (tx + Q) (u + c) u = rdrv td tx (u + c) u` for ALL `u ∈ ℕ`! -/
theorem rdrv_subdiag_agree_all_of_lt_twopow_all (td tx Q k c u : Nat)
    (htc : (tx + Q) - 1 ≤ k)
    (h : ∀ r : Nat, r < twopow ((k + 1) + c) →
      rdrv td (tx + Q) (r + c) r = rdrv td tx (r + c) r) :
    rdrv td (tx + Q) (u + c) u = rdrv td tx (u + c) u := by
  have hpos : 0 < twopow ((k + 1) + c) := by
    rw [twopow_eq_pow ((k + 1) + c)]
    exact Nat.two_pow_pos ((k + 1) + c)
  have hr : u % twopow ((k + 1) + c) < twopow ((k + 1) + c) := Nat.mod_lt u hpos
  have heq : u % twopow ((k + 1) + c) + (u / twopow ((k + 1) + c)) * twopow ((k + 1) + c) = u := by
    have hdiv := Nat.div_add_mod u (twopow ((k + 1) + c))
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq,
      rdrv_subdiag_period_twopow_all_mul td (tx + Q) k c
        (u % twopow ((k + 1) + c)) (u / twopow ((k + 1) + c)) htc,
      rdrv_subdiag_period_twopow_all_mul td tx k c
        (u % twopow ((k + 1) + c)) (u / twopow ((k + 1) + c)) (by omega)]
  exact h (u % twopow ((k + 1) + c)) hr

/-- **Right-Threshold Multi-Period `v * 2^((k + 1) + c)`-Invariance in `u` of Sub-Diagonal `c` (`rdrv_subdiag_period_twopow_all_mul_of_threshold`, 9.1309, `kit [33]`)**:
    for all `td, tx, k, J, c, u, v ∈ ℕ` with `IsRightThreshold k J` and `tx - 1 ≤ J`, `rdrv td tx ((u + v * 2^((k + 1) + c)) + c) (u + v * 2^((k + 1) + c)) = rdrv td tx (u + c) u`! -/
theorem rdrv_subdiag_period_twopow_all_mul_of_threshold (td tx k J c u v : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) :
    rdrv td tx ((u + v * twopow ((k + 1) + c)) + c) (u + v * twopow ((k + 1) + c)) =
      rdrv td tx (u + c) u := by
  induction v with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
  | succ v ih =>
    have hmul : u + (v + 1) * twopow ((k + 1) + c) =
        (u + v * twopow ((k + 1) + c)) + twopow ((k + 1) + c) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hmul,
        rdrv_subdiag_period_twopow_all_of_threshold td tx k J c
          (u + v * twopow ((k + 1) + c)) hJ htc,
        ih]

/-- **Right-Threshold All-Column Agreement on Sub-Diagonal `c` from a Single `2^((k + 1) + c)` Fundamental Period (`rdrv_subdiag_agree_all_of_threshold`, 9.1310, `kit [33]`)**:
    for all `td, tx, Q, k, J, c, u ∈ ℕ` with `IsRightThreshold k J` and `(tx + Q) - 1 ≤ J`, if `rdrv td (tx + Q) (r + c) r = rdrv td tx (r + c) r` for all `r < 2^((k + 1) + c)`, then `rdrv td (tx + Q) (u + c) u = rdrv td tx (u + c) u` for ALL `u ∈ ℕ`! -/
theorem rdrv_subdiag_agree_all_of_threshold (td tx Q k J c u : Nat)
    (hJ : IsRightThreshold k J) (htc : (tx + Q) - 1 ≤ J)
    (h : ∀ r : Nat, r < twopow ((k + 1) + c) →
      rdrv td (tx + Q) (r + c) r = rdrv td tx (r + c) r) :
    rdrv td (tx + Q) (u + c) u = rdrv td tx (u + c) u := by
  have hpos : 0 < twopow ((k + 1) + c) := by
    rw [twopow_eq_pow ((k + 1) + c)]
    exact Nat.two_pow_pos ((k + 1) + c)
  have hr : u % twopow ((k + 1) + c) < twopow ((k + 1) + c) := Nat.mod_lt u hpos
  have heq : u % twopow ((k + 1) + c) + (u / twopow ((k + 1) + c)) * twopow ((k + 1) + c) = u := by
    have hdiv := Nat.div_add_mod u (twopow ((k + 1) + c))
    rw [Nat.mul_comm] at hdiv
    omega
  rw [← heq,
      rdrv_subdiag_period_twopow_all_mul_of_threshold td (tx + Q) k J c
        (u % twopow ((k + 1) + c)) (u / twopow ((k + 1) + c)) hJ htc,
      rdrv_subdiag_period_twopow_all_mul_of_threshold td tx k J c
        (u % twopow ((k + 1) + c)) (u / twopow ((k + 1) + c)) hJ (by omega)]
  exact h (u % twopow ((k + 1) + c)) hr

/-- **Derivation of `maskparity · 0` Agreement at `t + (1 + c)` from Dyadic Sub-Diagonal Column `1 + v * 2^((k + 1) + c)` Agreement (`periodic_maskparity_zero_agree_of_subdiag_twopow_agree`, 9.1311, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, c, v ∈ ℕ` with `T ≤ t` and `(t + m * P) - 1 ≤ k`, if `rdrv t (t + m * P)` and `rdrv t t` agree at `((1 + v * 2^((k + 1) + c)) + c, 1 + v * 2^((k + 1) + c))`, then `maskparity ((t + (1 + c)) + m * P) 0 = maskparity (t + (1 + c)) 0`! -/
theorem periodic_maskparity_zero_agree_of_subdiag_twopow_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k c v : Nat) (ht : T ≤ t) (htc : (t + m * P) - 1 ≤ k)
    (h : rdrv t (t + m * P) ((1 + v * twopow ((k + 1) + c)) + c) (1 + v * twopow ((k + 1) + c)) =
         rdrv t t ((1 + v * twopow ((k + 1) + c)) + c) (1 + v * twopow ((k + 1) + c))) :
    Rule30UOR.Scale.maskparity ((t + (1 + c)) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + (1 + c)) 0 := by
  refine periodic_maskparity_zero_agree_of_rdrv_one_agree T P hP hper m t (1 + c) ht (fun _ => ?_)
  exact rdrv_col_one_agree_of_subdiag_twopow_agree t (t + m * P) t k c v htc (by omega) h

end Rule30UOR.Interfaces
