module

public import Rule30UOR.Interfaces.Part15

/-!
# `Rule30UOR.Interfaces`, part 16

* Batch 68: Dyadic Quadrant Replication (`rdrv td tx (v * 2^((k + 1) + C) + j) (v * 2^((k + 1) + C) + q) = rdrv td tx j q`), Spatio-Temporal Self-Similarity of `rhCenter`, and Shifted-Slice `RhBandAgree` Lifting (`kit [33]`, 9.1312–9.1326)
* Batch 69: Pure-Drive White-Seed (`tx = 0`) Unconditional `2^c`-Periodicity in `u`, Dyadic Quadrant Self-Similarity of `rdrv td 0`, and Delay-Free Right-Diagonal `2^c`-Periodicity & Self-Similarity of `rhCenter` (`kit [33]`, 9.1327–9.1341)
* Batch 70: Hypothesis-Free (`2^(tx + c)`) Universal Periodicity & Dyadic Quadrant/Row Self-Similarity of `rdrv` and `rhCenter` (`kit [33]`, 9.1342–9.1356)
* Batch 71: Finite-Support Right-Half Termination (`tx < q → rdrv td tx 0 q = false`), Exterior White Cone (`tx + k < p → rdrv td tx k p = false`), All-Horizon Expansion of `RhBandAgree tx Q 1 (tx + Q)`, and Horizon-Independent Refutation of `CenterPeriodic` (`kit [33]`, 9.1357–9.1371)
* Batch 72: Left-Inversion of `rdrv` and `rhCenter` Across Dyadic Centers `U = v * 2^(t + C)`, Full Two-Sided Embedding of the Left Half `lhCenter` Inside the Right Half `rhCenter`, and Left-Side White Isolation Corridors (`kit [33]`, 9.1372–9.1386)
* Batch 73: Common-Scale Dyadic Embedding of `lhCenter`, `ldiag`, and `LhColAgree` Inside the Right Half `rhCenter` & Left-of-`v * 2^K` Refutation of `CenterPeriodic` (`kit [33]`, 9.1387–9.1401)
* Batch 74: Bilateral Interior Light-Cone Determination for `rhCenter` & Left/Right White Isolation Corridors Around `v * 2^K` (`kit [33]`, 9.1402–9.1416)
* Batch 75: Fixed-Width Active Core `[v * 2^K - (t + Q), v * 2^K + (t + Q)]` Expansion to All Bilateral Cones & Full-Row Termination of `LhColAgree` (`kit [33]`, 9.1417–9.1431)
* Batch 76: Horizon-Width Bilateral Cone Decomposition (`LhBandAgree t Q 1 S` & `RhBandAgree t Q 0 S → LhColAgree t Q 1 S`) & Two-Scale Single-Row Spatial Shift Reduction (`kit [33]`, 9.1432–9.1446)
* Batch 77: Dyadic-Multiple Period (`m = c * 2^K`) Single-Row Refutation of `CenterPeriodic` & Exact Isolated Impulse Structure of `rhCenter (u * 2^L)` and `rdrv td (u * 2^L)` (`kit [33]`, 9.1447–9.1461)
* Batch 78: Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift & Shifted-Initial-Row `rdrv td (t + u * 2^L)` Refutations of `CenterPeriodic` (`kit [33]`, 9.1462–9.1476)
* Batch 79: Anchored Left-Half Step Contraction (`periodic_lhBandAgree_one_step`, `periodic_lhColAgree_one_of_lhBandAgree_one`) & Unilateral Left-Corridor Pullbacks (`kit [33]`, 9.1477–9.1491)
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

/-! ### Batch 68: Dyadic Quadrant Replication (`rdrv td tx (v * 2^((k + 1) + C) + j) (v * 2^((k + 1) + C) + q) = rdrv td tx j q`), Spatio-Temporal Self-Similarity of `rhCenter`, and Shifted-Slice `RhBandAgree` Lifting (`kit [33]`, 9.1312–9.1326) -/

/-- **Additive-to-Multiplicative Law for `twopow` (`twopow_add_eq_mul`, 9.1312)**:
    for all `a, b ∈ ℕ`, `twopow (a + b) = twopow b * twopow a`. -/
theorem twopow_add_eq_mul (a b : Nat) :
    twopow (a + b) = twopow b * twopow a := by
  induction b with
  | zero =>
    rw [Nat.add_zero]
    change twopow a = 1 * twopow a
    omega
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega,
        twopow_succ (a + b),
        twopow_succ b,
        ih,
        ← Nat.add_mul]

/-- **Sub-Diagonal Scale Factorization for `v * 2^((k + 1) + C)` (`twopow_subdiag_scale_split`, 9.1313, `kit [33]`)**:
    for all `k, c, C, v ∈ ℕ` with `c ≤ C`, `v * 2^((k + 1) + C) = (v * 2^(C - c)) * 2^((k + 1) + c)`. -/
theorem twopow_subdiag_scale_split (k c C v : Nat) (hc : c ≤ C) :
    v * twopow ((k + 1) + C) =
      (v * twopow (C - c)) * twopow ((k + 1) + c) := by
  rw [show (k + 1) + C = ((k + 1) + c) + (C - c) by omega,
      twopow_add_eq_mul ((k + 1) + c) (C - c),
      Nat.mul_assoc]

/-- **Dyadic Quadrant Replication Theorem for `rdrv` (`rdrv_dyadic_quadrant_eq`, 9.1314, `kit [33]`)**:
    for all `td, tx, k, C, v, j, q ∈ ℕ` with `tx - 1 ≤ k` and `j ≤ q + C` (and NO hypothesis on the center drive `td`!), `rdrv td tx (v * 2^((k + 1) + C) + j) (v * 2^((k + 1) + C) + q) = rdrv td tx j q`! -/
theorem rdrv_dyadic_quadrant_eq (td tx k C v j q : Nat)
    (htc : tx - 1 ≤ k) (hjq : j ≤ q + C) :
    rdrv td tx (v * twopow ((k + 1) + C) + j) (v * twopow ((k + 1) + C) + q) =
      rdrv td tx j q := by
  by_cases hqj : q ≤ j
  · have hc : j - q ≤ C := by omega
    have hj : j = q + (j - q) := by omega
    have hU := twopow_subdiag_scale_split k (j - q) C v hc
    have h1 : v * twopow ((k + 1) + C) + j =
        (q + (v * twopow (C - (j - q))) * twopow ((k + 1) + (j - q))) + (j - q) := by
      rw [hU]
      omega
    have h2 : v * twopow ((k + 1) + C) + q =
        q + (v * twopow (C - (j - q))) * twopow ((k + 1) + (j - q)) := by
      rw [hU]
      omega
    rw [h1, h2,
        rdrv_subdiag_period_twopow_all_mul td tx k (j - q) q (v * twopow (C - (j - q))) htc,
        ← hj]
  · have hlt : j < q := by omega
    rw [rdrv_outside_cone_eq_rhCenter td tx (v * twopow ((k + 1) + C) + j)
          (v * twopow ((k + 1) + C) + q) (by omega),
        rdrv_outside_cone_eq_rhCenter td tx j q hlt]
    have hUk : v * twopow ((k + 1) + C) = (v * twopow (C + 1)) * twopow k := by
      rw [show (k + 1) + C = k + (C + 1) by omega,
          twopow_add_eq_mul k (C + 1),
          Nat.mul_assoc]
    have ht1 : tx + (v * twopow ((k + 1) + C) + j) =
        tx + (j + (v * twopow (C + 1)) * twopow k) := by
      rw [hUk]
      omega
    have ht2 : v * twopow ((k + 1) + C) + q =
        (j + (v * twopow (C + 1)) * twopow k) + (q - j) := by
      rw [hUk]
      omega
    have ht3 : q = j + (q - j) := by omega
    rw [ht1, ht2,
        rhCenter_superdiag_period_twopow tx (q - j) k j (v * twopow (C + 1)) (by omega),
        ← ht3]

/-- **Right-Threshold Dyadic Quadrant Replication Theorem for `rdrv` (`rdrv_dyadic_quadrant_eq_of_threshold`, 9.1315, `kit [33]`)**:
    for all `td, tx, k, J, C, v, j, q ∈ ℕ` with `IsRightThreshold k J`, `tx - 1 ≤ J`, and `j ≤ q + C`, `rdrv td tx (v * 2^((k + 1) + C) + j) (v * 2^((k + 1) + C) + q) = rdrv td tx j q`! -/
theorem rdrv_dyadic_quadrant_eq_of_threshold (td tx k J C v j q : Nat)
    (hJ : IsRightThreshold k J) (htc : tx - 1 ≤ J) (hjq : j ≤ q + C) :
    rdrv td tx (v * twopow ((k + 1) + C) + j) (v * twopow ((k + 1) + C) + q) =
      rdrv td tx j q := by
  by_cases hqj : q ≤ j
  · have hc : j - q ≤ C := by omega
    have hj : j = q + (j - q) := by omega
    have hU := twopow_subdiag_scale_split k (j - q) C v hc
    have h1 : v * twopow ((k + 1) + C) + j =
        (q + (v * twopow (C - (j - q))) * twopow ((k + 1) + (j - q))) + (j - q) := by
      rw [hU]
      omega
    have h2 : v * twopow ((k + 1) + C) + q =
        q + (v * twopow (C - (j - q))) * twopow ((k + 1) + (j - q)) := by
      rw [hU]
      omega
    rw [h1, h2,
        rdrv_subdiag_period_twopow_all_mul_of_threshold td tx k J (j - q) q
          (v * twopow (C - (j - q))) hJ htc,
        ← hj]
  · have hlt : j < q := by omega
    rw [rdrv_outside_cone_eq_rhCenter td tx (v * twopow ((k + 1) + C) + j)
          (v * twopow ((k + 1) + C) + q) (by omega),
        rdrv_outside_cone_eq_rhCenter td tx j q hlt]
    have hUk : v * twopow ((k + 1) + C) = (v * twopow (C + 1)) * twopow k := by
      rw [show (k + 1) + C = k + (C + 1) by omega,
          twopow_add_eq_mul k (C + 1),
          Nat.mul_assoc]
    have ht1 : tx + (v * twopow ((k + 1) + C) + j) =
        tx + (j + (v * twopow (C + 1)) * twopow k) := by
      rw [hUk]
      omega
    have ht2 : v * twopow ((k + 1) + C) + q =
        (j + (v * twopow (C + 1)) * twopow k) + (q - j) := by
      rw [hUk]
      omega
    have ht3 : q = j + (q - j) := by omega
    rw [ht1, ht2,
        rhCenter_superdiag_period_twopow_of_threshold tx (q - j) k J j (v * twopow (C + 1)) hJ (by omega),
        ← ht3]

/-- **Dyadic `C`-Step Slab Replication for `rdrv` (`rdrv_dyadic_slab_eq`, 9.1316, `kit [33]`)**:
    for all `td, tx, k, C, v, j, q ∈ ℕ` with `tx - 1 ≤ k` and `j ≤ C`, `rdrv td tx (v * 2^((k + 1) + C) + j) (v * 2^((k + 1) + C) + q) = rdrv td tx j q` for ALL columns `q ∈ ℕ`! -/
theorem rdrv_dyadic_slab_eq (td tx k C v j q : Nat)
    (htc : tx - 1 ≤ k) (hj : j ≤ C) :
    rdrv td tx (v * twopow ((k + 1) + C) + j) (v * twopow ((k + 1) + C) + q) =
      rdrv td tx j q :=
  rdrv_dyadic_quadrant_eq td tx k C v j q htc (by omega)

/-- **Dyadic Horizontal Row Replication at Step `v * 2^(k + 1)` in `rdrv` (`rdrv_dyadic_row_eq_init`, 9.1317, `kit [33]`)**:
    for all `td, tx, k, v, q ∈ ℕ` with `tx - 1 ≤ k`, `rdrv td tx (v * 2^(k + 1)) (v * 2^(k + 1) + q) = rdrv td tx 0 q` for ALL `q ∈ ℕ`! -/
theorem rdrv_dyadic_row_eq_init (td tx k v q : Nat) (htc : tx - 1 ≤ k) :
    rdrv td tx (v * twopow (k + 1)) (v * twopow (k + 1) + q) =
      rdrv td tx 0 q := by
  have h := rdrv_dyadic_slab_eq td tx k 0 v 0 q htc (by omega)
  rwa [Nat.add_zero, Nat.add_zero] at h

/-- **Spatio-Temporal Dyadic Quadrant Self-Similarity of `rhCenter` (`rhCenter_dyadic_quadrant_eq`, 9.1318, `kit [33]`)**:
    for all `t, k, C, v, j, q ∈ ℕ` with `t - 1 ≤ k` and `j ≤ q + C`, `rhCenter (t + (v * 2^((k + 1) + C) + j)) (v * 2^((k + 1) + C) + q) = rhCenter (t + j) q`! -/
theorem rhCenter_dyadic_quadrant_eq (t k C v j q : Nat)
    (htc : t - 1 ≤ k) (hjq : j ≤ q + C) :
    rhCenter (t + (v * twopow ((k + 1) + C) + j)) (v * twopow ((k + 1) + C) + q) =
      rhCenter (t + j) q := by
  rw [← rdrv_diag_eq_rhCenter t (v * twopow ((k + 1) + C) + j) (v * twopow ((k + 1) + C) + q),
      ← rdrv_diag_eq_rhCenter t j q]
  exact rdrv_dyadic_quadrant_eq t t k C v j q htc hjq

/-- **Right-Threshold Dyadic Quadrant Self-Similarity of `rhCenter` (`rhCenter_dyadic_quadrant_eq_of_threshold`, 9.1319, `kit [33]`)**:
    for all `t, k, J, C, v, j, q ∈ ℕ` with `IsRightThreshold k J`, `t - 1 ≤ J`, and `j ≤ q + C`, `rhCenter (t + (v * 2^((k + 1) + C) + j)) (v * 2^((k + 1) + C) + q) = rhCenter (t + j) q`! -/
theorem rhCenter_dyadic_quadrant_eq_of_threshold (t k J C v j q : Nat)
    (hJ : IsRightThreshold k J) (htc : t - 1 ≤ J) (hjq : j ≤ q + C) :
    rhCenter (t + (v * twopow ((k + 1) + C) + j)) (v * twopow ((k + 1) + C) + q) =
      rhCenter (t + j) q := by
  rw [← rdrv_diag_eq_rhCenter t (v * twopow ((k + 1) + C) + j) (v * twopow ((k + 1) + C) + q),
      ← rdrv_diag_eq_rhCenter t j q]
  exact rdrv_dyadic_quadrant_eq_of_threshold t t k J C v j q hJ htc hjq

/-- **Spatio-Temporal `C`-Step Slab Self-Similarity of `rhCenter` (`rhCenter_dyadic_slab_eq`, 9.1320, `kit [33]`)**:
    for all `t, k, C, v, j, q ∈ ℕ` with `t - 1 ≤ k` and `j ≤ C`, `rhCenter (t + (v * 2^((k + 1) + C) + j)) (v * 2^((k + 1) + C) + q) = rhCenter (t + j) q` for ALL `q ∈ ℕ`! -/
theorem rhCenter_dyadic_slab_eq (t k C v j q : Nat)
    (htc : t - 1 ≤ k) (hj : j ≤ C) :
    rhCenter (t + (v * twopow ((k + 1) + C) + j)) (v * twopow ((k + 1) + C) + q) =
      rhCenter (t + j) q :=
  rhCenter_dyadic_quadrant_eq t k C v j q htc (by omega)

/-- **Exact Horizontal Row Replication in `rhCenter` at Time `t + v * 2^(k + 1)` (`rhCenter_dyadic_row_eq`, 9.1321, `kit [33]`)**:
    for all `t, k, v, q ∈ ℕ` with `t - 1 ≤ k`, `rhCenter (t + v * 2^(k + 1)) (v * 2^(k + 1) + q) = rhCenter t q` for ALL `q ∈ ℕ`! -/
theorem rhCenter_dyadic_row_eq (t k v q : Nat) (htc : t - 1 ≤ k) :
    rhCenter (t + v * twopow (k + 1)) (v * twopow (k + 1) + q) =
      rhCenter t q := by
  have h := rhCenter_dyadic_slab_eq t k 0 v 0 q htc (by omega)
  rwa [Nat.add_zero, Nat.add_zero, Nat.add_zero] at h

/-- **Right-Threshold Horizontal Row Replication in `rhCenter` at Time `t + v * 2^(k + 1)` (`rhCenter_dyadic_row_eq_of_threshold`, 9.1322, `kit [33]`)**:
    for all `t, k, J, v, q ∈ ℕ` with `IsRightThreshold k J` and `t - 1 ≤ J`, `rhCenter (t + v * 2^(k + 1)) (v * 2^(k + 1) + q) = rhCenter t q` for ALL `q ∈ ℕ`! -/
theorem rhCenter_dyadic_row_eq_of_threshold (t k J v q : Nat)
    (hJ : IsRightThreshold k J) (htc : t - 1 ≤ J) :
    rhCenter (t + v * twopow (k + 1)) (v * twopow (k + 1) + q) =
      rhCenter t q := by
  have h := rhCenter_dyadic_quadrant_eq_of_threshold t k J 0 v 0 q hJ htc (by omega)
  rwa [Nat.add_zero, Nat.add_zero, Nat.add_zero] at h

/-- **Pullback of `RhBandAgree t Q a B` from Shifted Dyadic Row `t + v * 2^(k + 1)` (`rhBandAgree_of_dyadic_row_shift_agree`, 9.1323, `kit [33]`)**:
    for all `t, Q, k, v, a, B ∈ ℕ` with `(t + Q) - 1 ≤ k`, if `RhBandAgree (t + v * 2^(k + 1)) Q (v * 2^(k + 1) + a) B`, then `RhBandAgree t Q a B`! -/
theorem rhBandAgree_of_dyadic_row_shift_agree (t Q k v a B : Nat)
    (htc : (t + Q) - 1 ≤ k)
    (hband : RhBandAgree (t + v * twopow (k + 1)) Q (v * twopow (k + 1) + a) B) :
    RhBandAgree t Q a B := by
  intro i hi
  have h := hband i hi
  rw [show (t + v * twopow (k + 1)) + Q = (t + Q) + v * twopow (k + 1) by omega,
      show (v * twopow (k + 1) + a) + i = v * twopow (k + 1) + (a + i) by omega,
      rhCenter_dyadic_row_eq (t + Q) k v (a + i) htc,
      rhCenter_dyadic_row_eq t k v (a + i) (by omega)] at h
  exact h

/-- **Pushforward of `RhBandAgree t Q a B` to Shifted Dyadic Row `t + v * 2^(k + 1)` (`rhBandAgree_dyadic_row_shift_of_rhBandAgree`, 9.1324, `kit [33]`)**:
    for all `t, Q, k, v, a, B ∈ ℕ` with `(t + Q) - 1 ≤ k`, if `RhBandAgree t Q a B`, then `RhBandAgree (t + v * 2^(k + 1)) Q (v * 2^(k + 1) + a) B`! -/
theorem rhBandAgree_dyadic_row_shift_of_rhBandAgree (t Q k v a B : Nat)
    (htc : (t + Q) - 1 ≤ k)
    (hband : RhBandAgree t Q a B) :
    RhBandAgree (t + v * twopow (k + 1)) Q (v * twopow (k + 1) + a) B := by
  intro i hi
  rw [show (t + v * twopow (k + 1)) + Q = (t + Q) + v * twopow (k + 1) by omega,
      show (v * twopow (k + 1) + a) + i = v * twopow (k + 1) + (a + i) by omega,
      rhCenter_dyadic_row_eq (t + Q) k v (a + i) htc,
      rhCenter_dyadic_row_eq t k v (a + i) (by omega)]
  exact hband i hi

/-- **Gate-Free `maskparity · 0` Agreement from Shifted Dyadic Row `RhBandAgree` (`periodic_maskparity_zero_agree_of_dyadic_row_shift_agree`, 9.1325, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, v, B, s ∈ ℕ` with `T ≤ t` and `(t + m * P) - 1 ≤ k`, if `RhBandAgree (t + v * 2^(k + 1)) (m * P) (v * 2^(k + 1) + 1) B` and `s ≤ B`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_dyadic_row_shift_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k v B s : Nat) (ht : T ≤ t) (htc : (t + m * P) - 1 ≤ k)
    (hband : RhBandAgree (t + v * twopow (k + 1)) (m * P) (v * twopow (k + 1) + 1) B)
    (hs : s ≤ B) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  periodic_maskparity_zero_agree_of_rhBandAgree T P hP hper m t B s ht
    (rhBandAgree_of_dyadic_row_shift_agree t (m * P) k v 1 B htc hband) hs

/-- **Refutation of `CenterPeriodic` from Shifted Dyadic Row `RhBandAgree` at a Doubling Zero Diagonal (`not_centerPeriodic_of_dyadic_row_shift_agree_at_zero_diag_doubles`, 9.1326, `kit [33]`)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, `((z + (p + 1)) + m * P) - 1 ≤ k`, `p + 3 * (m * P) ≤ B`, and `RhBandAgree ((z + (p + 1)) + v * 2^(k + 1)) (m * P) (v * 2^(k + 1) + 1) B`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_dyadic_row_shift_agree_at_zero_diag_doubles
    (T P m z p k v B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (htc : ((z + (p + 1)) + m * P) - 1 ≤ k)
    (hB : p + 3 * (m * P) ≤ B)
    (hband : RhBandAgree ((z + (p + 1)) + v * twopow (k + 1)) (m * P) (v * twopow (k + 1) + 1) B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_at_zero_diag_doubles T P m z p B hP hm ht hz hd hset1 hset2 (by omega)
    (rhBandAgree_of_dyadic_row_shift_agree (z + (p + 1)) (m * P) k v 1 B htc hband)

theorem not_centerPeriodic_of_dyadic_row_shift_agree_at_zero_diag_doubles_prop
    (T P m z p k v B : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (htc : ((z + (p + 1)) + m * P) - 1 ≤ k)
    (hB : p + 3 * (m * P) ≤ B)
    (hband : RhBandAgree ((z + (p + 1)) + v * twopow (k + 1)) (m * P) (v * twopow (k + 1) + 1) B) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_dyadic_row_shift_agree_at_zero_diag_doubles T P m z p k v B hP hm ht hz hd
    hset1 hset2 htc hB hband

/-! ### Batch 69: Pure-Drive White-Seed (`tx = 0`) Unconditional `2^c`-Periodicity in `u`, Dyadic Quadrant Self-Similarity of `rdrv td 0`, and Delay-Free Right-Diagonal `2^c`-Periodicity & Self-Similarity of `rhCenter` (`kit [33]`, 9.1327–9.1341) -/

/-- **1-Step Sub-Diagonal `1` Recurrence in the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_subdiag_one_step_eq_center`, 9.1327, `kit [33]`)**:
    for all `td, u ∈ ℕ`, `rdrv td 0 ((u + 1) + 1) (u + 1) = bxor (rdrv td 0 (u + 1) u) (center td)`! -/
theorem rdrv_white_seed_subdiag_one_step_eq_center (td u : Nat) :
    rdrv td 0 ((u + 1) + 1) (u + 1) =
      bxor (rdrv td 0 (u + 1) u) (Rule30UOR.Core.center td) := by
  rw [rdrv_subdiag_one_step_eq_rhCenter td 0 u,
      Nat.zero_add,
      rhCenter_gt_eq_false (u + 1) ((u + 1) + 1) (by omega),
      Bool.or_false,
      rdrv_white_seed_diag_eq_center td (u + 1)]

/-- **Unconditional Period-`2` Law in `u` for Sub-Diagonal `1` of the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_subdiag_one_period_two_all`, 9.1328, `kit [33]`)**:
    for all `td, u ∈ ℕ`, `rdrv td 0 ((u + 2) + 1) (u + 2) = rdrv td 0 (u + 1) u`! -/
theorem rdrv_white_seed_subdiag_one_period_two_all (td u : Nat) :
    rdrv td 0 ((u + 2) + 1) (u + 2) =
      rdrv td 0 (u + 1) u := by
  rw [show u + 2 = (u + 1) + 1 by omega,
      rdrv_white_seed_subdiag_one_step_eq_center td (u + 1),
      rdrv_white_seed_subdiag_one_step_eq_center td u]
  simp only [bxor_eq_xor]
  cases rdrv td 0 (u + 1) u <;> cases Rule30UOR.Core.center td <;> rfl

/-- **Universal `2^c`-Periodicity in `u` of All Sub-Diagonals `c` in the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_subdiag_period_twopow_all`, 9.1329, `kit [33]`)**:
    for all `td, c, u ∈ ℕ` (with NO hypothesis on `td`!), `rdrv td 0 ((u + 2^c) + c) (u + 2^c) = rdrv td 0 (u + c) u`! -/
theorem rdrv_white_seed_subdiag_period_twopow_all (td c u : Nat) :
    rdrv td 0 ((u + twopow c) + c) (u + twopow c) =
      rdrv td 0 (u + c) u := by
  suffices hpair :
      (∀ w : Nat,
        rdrv td 0 ((w + twopow c) + c) (w + twopow c) =
          rdrv td 0 (w + c) w) ∧
      (∀ w : Nat,
        rdrv td 0 ((w + twopow (c + 1)) + (c + 1)) (w + twopow (c + 1)) =
          rdrv td 0 (w + (c + 1)) w) from hpair.1 u
  induction c with
  | zero =>
    refine ⟨fun w => ?_, fun w => ?_⟩
    · simp only [Nat.add_zero]
      rw [rdrv_white_seed_diag_eq_center td (w + twopow 0),
          rdrv_white_seed_diag_eq_center td w]
    · exact rdrv_white_seed_subdiag_one_period_two_all td w
  | succ c ih =>
    refine ⟨ih.2, fun w => ?_⟩
    have hd := rdrv_subdiag_period_double_of_two_prev_periods
      td 0 c 0 (twopow (c + 1)) w
      (fun v _ => by
        rw [Nat.zero_add, Nat.zero_add,
            show twopow (c + 1) + v = v + twopow (c + 1) by omega]
        exact ih.2 v)
      (fun v _ => by
        rw [Nat.zero_add, Nat.zero_add,
            show twopow (c + 1) + v = (v + twopow c) + twopow c by
              rw [twopow_succ c]
              omega,
            ih.1 (v + twopow c),
            ih.1 v])
    have h2 : (0 + 2 * twopow (c + 1)) + w = w + twopow (c + 1 + 1) := by
      rw [twopow_succ (c + 1)]
      omega
    rwa [h2, Nat.zero_add] at hd

/-- **Multi-Period `v * 2^c`-Invariance in `u` of Sub-Diagonal `c` in `rdrv td 0` (`rdrv_white_seed_subdiag_period_twopow_all_mul`, 9.1330, `kit [33]`)**:
    for all `td, c, u, v ∈ ℕ`, `rdrv td 0 ((u + v * 2^c) + c) (u + v * 2^c) = rdrv td 0 (u + c) u`! -/
theorem rdrv_white_seed_subdiag_period_twopow_all_mul (td c u v : Nat) :
    rdrv td 0 ((u + v * twopow c) + c) (u + v * twopow c) =
      rdrv td 0 (u + c) u := by
  induction v with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
  | succ v ih =>
    have hmul : u + (v + 1) * twopow c = (u + v * twopow c) + twopow c := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hmul,
        rdrv_white_seed_subdiag_period_twopow_all td c (u + v * twopow c),
        ih]

/-- **Exact Center-Drive Replication at `u = v * 2^c` in the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_subdiag_at_twopow_eq_center`, 9.1331, `kit [33]`)**:
    for all `td, c, v ∈ ℕ`, `rdrv td 0 (v * 2^c + c) (v * 2^c) = center (td + c)`! -/
theorem rdrv_white_seed_subdiag_at_twopow_eq_center (td c v : Nat) :
    rdrv td 0 (v * twopow c + c) (v * twopow c) =
      Rule30UOR.Core.center (td + c) := by
  have h := rdrv_white_seed_subdiag_period_twopow_all_mul td c 0 v
  rw [Nat.zero_add, Nat.zero_add, rdrv_col0] at h
  exact h

/-- **Exact Dyadic Lift of Column `1` to `1 + v * 2^c` in the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_col_one_eq_subdiag_at_twopow`, 9.1332, `kit [33]`)**:
    for all `td, c, v ∈ ℕ`, `rdrv td 0 (1 + c) 1 = rdrv td 0 ((1 + v * 2^c) + c) (1 + v * 2^c)`! -/
theorem rdrv_white_seed_col_one_eq_subdiag_at_twopow (td c v : Nat) :
    rdrv td 0 (1 + c) 1 =
      rdrv td 0 ((1 + v * twopow c) + c) (1 + v * twopow c) :=
  (rdrv_white_seed_subdiag_period_twopow_all_mul td c 1 v).symm

/-- **Unconditional Dyadic Quadrant Self-Similarity of the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_dyadic_quadrant_eq`, 9.1333, `kit [33]`)**:
    for all `td, C, v, j, q ∈ ℕ` with `j ≤ q + C`, `rdrv td 0 (v * 2^C + j) (v * 2^C + q) = rdrv td 0 j q`! -/
theorem rdrv_white_seed_dyadic_quadrant_eq (td C v j q : Nat) (hjq : j ≤ q + C) :
    rdrv td 0 (v * twopow C + j) (v * twopow C + q) =
      rdrv td 0 j q := by
  by_cases hqj : q ≤ j
  · have hc : j - q ≤ C := by omega
    have hj : j = q + (j - q) := by omega
    have hU : v * twopow C = (v * twopow (C - (j - q))) * twopow (j - q) := by
      rw [Nat.mul_assoc,
          ← twopow_add_eq_mul (j - q) (C - (j - q)),
          show (j - q) + (C - (j - q)) = C by omega]
    have h1 : v * twopow C + j =
        (q + (v * twopow (C - (j - q))) * twopow (j - q)) + (j - q) := by
      rw [hU]
      omega
    have h2 : v * twopow C + q =
        q + (v * twopow (C - (j - q))) * twopow (j - q) := by
      rw [hU]
      omega
    rw [h1, h2,
        rdrv_white_seed_subdiag_period_twopow_all_mul td (j - q) q (v * twopow (C - (j - q))),
        ← hj]
  · have hlt : j < q := by omega
    rw [rdrv_outside_cone_eq_rhCenter td 0 (v * twopow C + j) (v * twopow C + q) (by omega),
        rdrv_outside_cone_eq_rhCenter td 0 j q hlt,
        Nat.zero_add, Nat.zero_add,
        rhCenter_gt_eq_false (v * twopow C + j) (v * twopow C + q) (by omega),
        rhCenter_gt_eq_false j q hlt]

/-- **Unconditional `C`-Step Slab Self-Similarity of the Pure-Drive White Seed `rdrv td 0` (`rdrv_white_seed_dyadic_slab_eq`, 9.1334, `kit [33]`)**:
    for all `td, C, v, j, q ∈ ℕ` with `j ≤ C`, `rdrv td 0 (v * 2^C + j) (v * 2^C + q) = rdrv td 0 j q` for ALL `q ∈ ℕ`! -/
theorem rdrv_white_seed_dyadic_slab_eq (td C v j q : Nat) (hj : j ≤ C) :
    rdrv td 0 (v * twopow C + j) (v * twopow C + q) =
      rdrv td 0 j q :=
  rdrv_white_seed_dyadic_quadrant_eq td C v j q (by omega)

/-- **Delay-Free `2^c`-Periodicity of Right Diagonals in `rhCenter` (`rhCenter_subdiag_period_twopow_zero_delay`, 9.1335, `kit [33]`)**:
    for all `c, u ∈ ℕ` (starting immediately at `u = 0` with ZERO settlement delay!), `rhCenter ((u + 2^c) + c) (u + 2^c) = rhCenter (u + c) u`! -/
theorem rhCenter_subdiag_period_twopow_zero_delay (c u : Nat) :
    rhCenter ((u + twopow c) + c) (u + twopow c) =
      rhCenter (u + c) u := by
  rw [← rdrv_zero_eq_rhCenter ((u + twopow c) + c) (u + twopow c),
      ← rdrv_zero_eq_rhCenter (u + c) u]
  exact rdrv_white_seed_subdiag_period_twopow_all 0 c u

/-- **Delay-Free Multi-Period `v * 2^c`-Invariance of Right Diagonals in `rhCenter` (`rhCenter_subdiag_period_twopow_zero_delay_mul`, 9.1336, `kit [33]`)**:
    for all `c, u, v ∈ ℕ`, `rhCenter ((u + v * 2^c) + c) (u + v * 2^c) = rhCenter (u + c) u`! -/
theorem rhCenter_subdiag_period_twopow_zero_delay_mul (c u v : Nat) :
    rhCenter ((u + v * twopow c) + c) (u + v * twopow c) =
      rhCenter (u + c) u := by
  rw [← rdrv_zero_eq_rhCenter ((u + v * twopow c) + c) (u + v * twopow c),
      ← rdrv_zero_eq_rhCenter (u + c) u]
  exact rdrv_white_seed_subdiag_period_twopow_all_mul 0 c u v

/-- **Delay-Free Center Replication in `rhCenter` at `(v * 2^c + c, v * 2^c)` (`rhCenter_subdiag_at_twopow_zero_delay_eq_center`, 9.1337, `kit [33]`)**:
    for all `c, v ∈ ℕ`, `rhCenter (v * 2^c + c) (v * 2^c) = center c`! -/
theorem rhCenter_subdiag_at_twopow_zero_delay_eq_center (c v : Nat) :
    rhCenter (v * twopow c + c) (v * twopow c) =
      Rule30UOR.Core.center c := by
  rw [← rdrv_zero_eq_rhCenter (v * twopow c + c) (v * twopow c)]
  have h := rdrv_white_seed_subdiag_at_twopow_eq_center 0 c v
  rwa [Nat.zero_add] at h

/-- **Delay-Free Dyadic Lift of Column `1` (`rhCenter (1 + c) 1`) to Column `1 + v * 2^c` (`rhCenter_col_one_eq_subdiag_at_twopow_zero_delay`, 9.1338, `kit [33]`)**:
    for all `c, v ∈ ℕ`, `rhCenter (1 + c) 1 = rhCenter ((1 + v * 2^c) + c) (1 + v * 2^c)`! -/
theorem rhCenter_col_one_eq_subdiag_at_twopow_zero_delay (c v : Nat) :
    rhCenter (1 + c) 1 =
      rhCenter ((1 + v * twopow c) + c) (1 + v * twopow c) := by
  rw [← rdrv_zero_eq_rhCenter (1 + c) 1,
      ← rdrv_zero_eq_rhCenter ((1 + v * twopow c) + c) (1 + v * twopow c)]
  exact rdrv_white_seed_col_one_eq_subdiag_at_twopow 0 c v

/-- **Delay-Free Global Dyadic Quadrant Self-Similarity of `rhCenter` (`rhCenter_dyadic_quadrant_zero_delay_eq`, 9.1339, `kit [33]`)**:
    for all `C, v, j, q ∈ ℕ` with `j ≤ q + C`, `rhCenter (v * 2^C + j) (v * 2^C + q) = rhCenter j q`! -/
theorem rhCenter_dyadic_quadrant_zero_delay_eq (C v j q : Nat) (hjq : j ≤ q + C) :
    rhCenter (v * twopow C + j) (v * twopow C + q) =
      rhCenter j q := by
  rw [← rdrv_zero_eq_rhCenter (v * twopow C + j) (v * twopow C + q),
      ← rdrv_zero_eq_rhCenter j q]
  exact rdrv_white_seed_dyadic_quadrant_eq 0 C v j q hjq

/-- **Delay-Free Global `C`-Step Slab Self-Similarity of `rhCenter` (`rhCenter_dyadic_slab_zero_delay_eq`, 9.1340, `kit [33]`)**:
    for all `C, v, j, q ∈ ℕ` with `j ≤ C`, `rhCenter (v * 2^C + j) (v * 2^C + q) = rhCenter j q` for ALL `q ∈ ℕ`! -/
theorem rhCenter_dyadic_slab_zero_delay_eq (C v j q : Nat) (hj : j ≤ C) :
    rhCenter (v * twopow C + j) (v * twopow C + q) =
      rhCenter j q :=
  rhCenter_dyadic_quadrant_zero_delay_eq C v j q (by omega)

/-- **Dyadic Exterior White Corridor of `rhCenter` (`rhCenter_dyadic_triangle_white_corridor`, 9.1341, `kit [33]`)**:
    for all `C, v, j, q ∈ ℕ` with `j < q`, `rhCenter (v * 2^C + j) (v * 2^C + q) = false`! -/
theorem rhCenter_dyadic_triangle_white_corridor (C v j q : Nat) (hjq : j < q) :
    rhCenter (v * twopow C + j) (v * twopow C + q) = false := by
  rw [rhCenter_dyadic_quadrant_zero_delay_eq C v j q (by omega)]
  exact rhCenter_gt_eq_false j q hjq

/-! ### Batch 70: Hypothesis-Free (`2^(tx + c)`) Universal Periodicity & Dyadic Quadrant/Row Self-Similarity of `rdrv` and `rhCenter` (`kit [33]`, 9.1342–9.1356) -/

/-- **Hypothesis-Free `2^(tx + c)`-Periodicity in `u` of All Sub-Diagonals `c` in `rdrv` (`rdrv_subdiag_period_twopow_tx_add`, 9.1342, `kit [33]`)**:
    for ALL `td, tx, c, u ∈ ℕ` (with ZERO hypotheses!), `rdrv td tx ((u + 2^(tx + c)) + c) (u + 2^(tx + c)) = rdrv td tx (u + c) u`! -/
theorem rdrv_subdiag_period_twopow_tx_add (td tx c u : Nat) :
    rdrv td tx ((u + twopow (tx + c)) + c) (u + twopow (tx + c)) =
      rdrv td tx (u + c) u := by
  rcases tx with _ | tx
  · rw [Nat.zero_add]
    exact rdrv_white_seed_subdiag_period_twopow_all td c u
  · exact rdrv_subdiag_period_twopow_all td (tx + 1) tx c u (by omega)

/-- **Hypothesis-Free Multi-Period `v * 2^(tx + c)`-Invariance in `u` of Sub-Diagonal `c` in `rdrv` (`rdrv_subdiag_period_twopow_tx_add_mul`, 9.1343, `kit [33]`)**:
    for ALL `td, tx, c, u, v ∈ ℕ`, `rdrv td tx ((u + v * 2^(tx + c)) + c) (u + v * 2^(tx + c)) = rdrv td tx (u + c) u`! -/
theorem rdrv_subdiag_period_twopow_tx_add_mul (td tx c u v : Nat) :
    rdrv td tx ((u + v * twopow (tx + c)) + c) (u + v * twopow (tx + c)) =
      rdrv td tx (u + c) u := by
  rcases tx with _ | tx
  · rw [Nat.zero_add]
    exact rdrv_white_seed_subdiag_period_twopow_all_mul td c u v
  · exact rdrv_subdiag_period_twopow_all_mul td (tx + 1) tx c u v (by omega)

/-- **Hypothesis-Free `v * 2^tx`-Invariance in `u` of the Main Diagonal in `rdrv` (`rdrv_main_diag_period_twopow_tx`, 9.1344, `kit [33]`)**:
    for ALL `td, tx, u, v ∈ ℕ`, `rdrv td tx (u + v * 2^tx) (u + v * 2^tx) = rdrv td tx u u`! -/
theorem rdrv_main_diag_period_twopow_tx (td tx u v : Nat) :
    rdrv td tx (u + v * twopow tx) (u + v * twopow tx) =
      rdrv td tx u u := by
  have h := rdrv_subdiag_period_twopow_tx_add_mul td tx 0 u v
  rwa [Nat.add_zero, Nat.add_zero, Nat.add_zero] at h

/-- **Hypothesis-Free Center-Drive Replication on the Main Diagonal at `u = v * 2^tx` (`rdrv_main_diag_at_twopow_tx_eq_center`, 9.1345, `kit [33]`)**:
    for ALL `td, tx, v ∈ ℕ`, `rdrv td tx (v * 2^tx) (v * 2^tx) = center td`! -/
theorem rdrv_main_diag_at_twopow_tx_eq_center (td tx v : Nat) :
    rdrv td tx (v * twopow tx) (v * twopow tx) =
      Rule30UOR.Core.center td := by
  have h := rdrv_main_diag_period_twopow_tx td tx 0 v
  rw [Nat.zero_add, rdrv_col0, Nat.add_zero] at h
  exact h

/-- **Hypothesis-Free Center-Drive Replication on Sub-Diagonal `c` at `u = v * 2^(tx + c)` (`rdrv_subdiag_at_twopow_tx_add_eq_center`, 9.1346, `kit [33]`)**:
    for ALL `td, tx, c, v ∈ ℕ`, `rdrv td tx ((v * 2^(tx + c)) + c) (v * 2^(tx + c)) = center (td + c)`! -/
theorem rdrv_subdiag_at_twopow_tx_add_eq_center (td tx c v : Nat) :
    rdrv td tx ((v * twopow (tx + c)) + c) (v * twopow (tx + c)) =
      Rule30UOR.Core.center (td + c) := by
  have h := rdrv_subdiag_period_twopow_tx_add_mul td tx c 0 v
  rw [Nat.zero_add, Nat.zero_add, rdrv_col0] at h
  exact h

/-- **Hypothesis-Free Dyadic Lift of Column `1` to `1 + v * 2^(tx + c)` (`rdrv_col_one_eq_subdiag_at_twopow_tx_add`, 9.1347, `kit [33]`)**:
    for ALL `td, tx, c, v ∈ ℕ`, `rdrv td tx (1 + c) 1 = rdrv td tx ((1 + v * 2^(tx + c)) + c) (1 + v * 2^(tx + c))`! -/
theorem rdrv_col_one_eq_subdiag_at_twopow_tx_add (td tx c v : Nat) :
    rdrv td tx (1 + c) 1 =
      rdrv td tx ((1 + v * twopow (tx + c)) + c) (1 + v * twopow (tx + c)) :=
  (rdrv_subdiag_period_twopow_tx_add_mul td tx c 1 v).symm

/-- **Hypothesis-Free Dyadic Quadrant Replication (`U = v * 2^(tx + C)`) for `rdrv` (`rdrv_dyadic_quadrant_tx_add_eq`, 9.1348, `kit [33]`)**:
    for ALL `td, tx, C, v, j, q ∈ ℕ` with `j ≤ q + C`, `rdrv td tx (v * 2^(tx + C) + j) (v * 2^(tx + C) + q) = rdrv td tx j q`! -/
theorem rdrv_dyadic_quadrant_tx_add_eq (td tx C v j q : Nat) (hjq : j ≤ q + C) :
    rdrv td tx (v * twopow (tx + C) + j) (v * twopow (tx + C) + q) =
      rdrv td tx j q := by
  rcases tx with _ | tx
  · rw [Nat.zero_add]
    exact rdrv_white_seed_dyadic_quadrant_eq td C v j q hjq
  · exact rdrv_dyadic_quadrant_eq td (tx + 1) tx C v j q (by omega) hjq

/-- **Hypothesis-Free `C`-Step Slab Replication (`U = v * 2^(tx + C)`) for `rdrv` (`rdrv_dyadic_slab_tx_add_eq`, 9.1349, `kit [33]`)**:
    for ALL `td, tx, C, v, j, q ∈ ℕ` with `j ≤ C`, `rdrv td tx (v * 2^(tx + C) + j) (v * 2^(tx + C) + q) = rdrv td tx j q` for ALL `q ∈ ℕ`! -/
theorem rdrv_dyadic_slab_tx_add_eq (td tx C v j q : Nat) (hj : j ≤ C) :
    rdrv td tx (v * twopow (tx + C) + j) (v * twopow (tx + C) + q) =
      rdrv td tx j q :=
  rdrv_dyadic_quadrant_tx_add_eq td tx C v j q (by omega)

/-- **Hypothesis-Free Horizontal Row Replication at Step `v * 2^tx` in `rdrv` (`rdrv_dyadic_row_tx_eq_init`, 9.1350, `kit [33]`)**:
    for ALL `td, tx, v, q ∈ ℕ`, `rdrv td tx (v * 2^tx) (v * 2^tx + q) = rdrv td tx 0 q`! -/
theorem rdrv_dyadic_row_tx_eq_init (td tx v q : Nat) :
    rdrv td tx (v * twopow tx) (v * twopow tx + q) =
      rdrv td tx 0 q := by
  have h := rdrv_dyadic_slab_tx_add_eq td tx 0 v 0 q (by omega)
  rwa [Nat.add_zero, Nat.add_zero] at h

/-- **Hypothesis-Free Spatio-Temporal Quadrant Self-Similarity (`U = v * 2^(t + C)`) of `rhCenter` (`rhCenter_dyadic_quadrant_t_add_eq`, 9.1351, `kit [33]`)**:
    for ALL `t, C, v, j, q ∈ ℕ` with `j ≤ q + C`, `rhCenter (t + (v * 2^(t + C) + j)) (v * 2^(t + C) + q) = rhCenter (t + j) q`! -/
theorem rhCenter_dyadic_quadrant_t_add_eq (t C v j q : Nat) (hjq : j ≤ q + C) :
    rhCenter (t + (v * twopow (t + C) + j)) (v * twopow (t + C) + q) =
      rhCenter (t + j) q := by
  rw [← rdrv_diag_eq_rhCenter t (v * twopow (t + C) + j) (v * twopow (t + C) + q),
      ← rdrv_diag_eq_rhCenter t j q]
  exact rdrv_dyadic_quadrant_tx_add_eq t t C v j q hjq

/-- **Hypothesis-Free Spatio-Temporal `C`-Step Slab Self-Similarity (`U = v * 2^(t + C)`) of `rhCenter` (`rhCenter_dyadic_slab_t_add_eq`, 9.1352, `kit [33]`)**:
    for ALL `t, C, v, j, q ∈ ℕ` with `j ≤ C`, `rhCenter (t + (v * 2^(t + C) + j)) (v * 2^(t + C) + q) = rhCenter (t + j) q` for ALL `q ∈ ℕ`! -/
theorem rhCenter_dyadic_slab_t_add_eq (t C v j q : Nat) (hj : j ≤ C) :
    rhCenter (t + (v * twopow (t + C) + j)) (v * twopow (t + C) + q) =
      rhCenter (t + j) q :=
  rhCenter_dyadic_quadrant_t_add_eq t C v j q (by omega)

/-- **Hypothesis-Free Horizontal Row Self-Similarity (`U = v * 2^t`) of `rhCenter` (`rhCenter_dyadic_row_t_eq`, 9.1353, `kit [33]`)**:
    for ALL `t, v, q ∈ ℕ` (with ZERO hypotheses!), `rhCenter (t + v * 2^t) (v * 2^t + q) = rhCenter t q`! -/
theorem rhCenter_dyadic_row_t_eq (t v q : Nat) :
    rhCenter (t + v * twopow t) (v * twopow t + q) =
      rhCenter t q := by
  have h := rhCenter_dyadic_slab_t_add_eq t 0 v 0 q (by omega)
  rwa [Nat.add_zero, Nat.add_zero] at h

/-- **Common-Scale (`t ≤ K`) Horizontal Row Self-Similarity of `rhCenter` (`rhCenter_dyadic_row_scale_eq`, 9.1354, `kit [33]`)**:
    for ALL `t, K, v, q ∈ ℕ` with `t ≤ K`, `rhCenter (t + v * 2^K) (v * 2^K + q) = rhCenter t q`! -/
theorem rhCenter_dyadic_row_scale_eq (t K v q : Nat) (htK : t ≤ K) :
    rhCenter (t + v * twopow K) (v * twopow K + q) =
      rhCenter t q := by
  have hK : v * twopow K = (v * twopow (K - t)) * twopow t := by
    rw [Nat.mul_assoc,
        ← twopow_add_eq_mul t (K - t),
        show t + (K - t) = K by omega]
  rw [hK]
  exact rhCenter_dyadic_row_t_eq t (v * twopow (K - t)) q

/-- **Common-Scale (`t + Q ≤ K`) Pullback of `RhBandAgree t Q a B` from Shifted Row `t + v * 2^K` (`rhBandAgree_of_dyadic_row_scale_agree`, 9.1355, `kit [33]`)**:
    for all `t, Q, K, v, a, B ∈ ℕ` with `t + Q ≤ K`, if `RhBandAgree (t + v * 2^K) Q (v * 2^K + a) B`, then `RhBandAgree t Q a B`! -/
theorem rhBandAgree_of_dyadic_row_scale_agree (t Q K v a B : Nat)
    (htK : t + Q ≤ K)
    (hband : RhBandAgree (t + v * twopow K) Q (v * twopow K + a) B) :
    RhBandAgree t Q a B := by
  intro i hi
  have h := hband i hi
  rw [show (t + v * twopow K) + Q = (t + Q) + v * twopow K by omega,
      show (v * twopow K + a) + i = v * twopow K + (a + i) by omega,
      rhCenter_dyadic_row_scale_eq (t + Q) K v (a + i) htK,
      rhCenter_dyadic_row_scale_eq t K v (a + i) (by omega)] at h
  exact h

/-- **Common-Scale (`t + m * P ≤ K`) Gate-Free `maskparity · 0` Agreement from Shifted Row `RhBandAgree` (`periodic_maskparity_zero_agree_of_dyadic_row_scale_agree`, 9.1356, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, v, B, s ∈ ℕ` with `T ≤ t` and `t + m * P ≤ K`, if `RhBandAgree (t + v * 2^K) (m * P) (v * 2^K + 1) B` and `s ≤ B`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_dyadic_row_scale_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v B s : Nat) (ht : T ≤ t) (htK : t + m * P ≤ K)
    (hband : RhBandAgree (t + v * twopow K) (m * P) (v * twopow K + 1) B)
    (hs : s ≤ B) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  periodic_maskparity_zero_agree_of_rhBandAgree T P hP hper m t B s ht
    (rhBandAgree_of_dyadic_row_scale_agree t (m * P) K v 1 B htK hband) hs

/-! ### Batch 71: Finite-Support Right-Half Termination (`tx < q → rdrv td tx 0 q = false`), Exterior White Cone (`tx + k < p → rdrv td tx k p = false`), All-Horizon Expansion of `RhBandAgree tx Q 1 (tx + Q)`, and Horizon-Independent Refutation of `CenterPeriodic` (`kit [33]`, 9.1357–9.1371) -/

/-- **Initial Row Termination Outside the Light Cone (`rdrv_init_gt_eq_false`, 9.1357, `kit [33]`)**:
    for all `td, tx, q ∈ ℕ` with `tx < q`, `rdrv td tx 0 q = false`! -/
theorem rdrv_init_gt_eq_false (td tx q : Nat) (hq : tx < q) :
    rdrv td tx 0 q = false := by
  rw [rdrv_init td tx q (by omega)]
  exact rhCenter_gt_eq_false tx q hq

/-- **Dyadic `C`-Step Slab Exterior White Cone of `rdrv` (`rdrv_dyadic_slab_tx_gt_eq_false`, 9.1358, `kit [33]`)**:
    for all `td, tx, C, v, j, q ∈ ℕ` with `j ≤ C` and `tx + j < q`, `rdrv td tx (v * 2^(tx + C) + j) (v * 2^(tx + C) + q) = false`! -/
theorem rdrv_dyadic_slab_tx_gt_eq_false (td tx C v j q : Nat)
    (hj : j ≤ C) (hq : tx + j < q) :
    rdrv td tx (v * twopow (tx + C) + j) (v * twopow (tx + C) + q) = false := by
  rw [rdrv_dyadic_slab_tx_add_eq td tx C v j q hj]
  exact rdrv_gt_eq_false td tx j q hq

/-- **Automatic Initial-Row Agreement Outside Both Light Cones (`rdrv_init_agree_of_gt`, 9.1359, `kit [33]`)**:
    for all `td, tx2, tx, q ∈ ℕ` with `tx2 < q` and `tx < q`, `rdrv td tx2 0 q = rdrv td tx 0 q`! -/
theorem rdrv_init_agree_of_gt (td tx2 tx q : Nat)
    (hq2 : tx2 < q) (hq1 : tx < q) :
    rdrv td tx2 0 q = rdrv td tx 0 q := by
  rw [rdrv_init_gt_eq_false td tx2 q hq2,
      rdrv_init_gt_eq_false td tx q hq1]

/-- **Automatic Agreement of `rdrv` Outside Both Light Cones (`rdrv_agree_of_gt`, 9.1360, `kit [33]`)**:
    for all `td, tx2, tx, k, p ∈ ℕ` with `tx2 + k < p` and `tx + k < p`, `rdrv td tx2 k p = rdrv td tx k p`! -/
theorem rdrv_agree_of_gt (td tx2 tx k p : Nat)
    (hp2 : tx2 + k < p) (hp1 : tx + k < p) :
    rdrv td tx2 k p = rdrv td tx k p := by
  rw [rdrv_gt_eq_false td tx2 k p hp2,
      rdrv_gt_eq_false td tx k p hp1]

/-- **All-Width Expansion of Support-Width `RhBandAgree tx Q 1 (tx + Q)` (`rhBandAgree_all_of_support_agree`, 9.1361, `kit [33]`)**:
    for all `tx, Q, B ∈ ℕ`, if `RhBandAgree tx Q 1 (tx + Q)` holds on the finite support `[1, 1 + (tx + Q)]`, then `RhBandAgree tx Q 1 B` holds for EVERY width `B ∈ ℕ`! -/
theorem rhBandAgree_all_of_support_agree (tx Q B : Nat)
    (hband : RhBandAgree tx Q 1 (tx + Q)) :
    RhBandAgree tx Q 1 B := by
  intro i _
  by_cases hi : i ≤ tx + Q
  · exact hband i hi
  · rw [rhCenter_gt_eq_false (tx + Q) (1 + i) (by omega),
        rhCenter_gt_eq_false tx (1 + i) (by omega)]

/-- **All-Time All-Column Determination of `rdrv` from Support-Width `RhBandAgree tx Q 1 (tx + Q)` (`rdrv_agree_all_of_support_rhBandAgree`, 9.1362, `kit [33]`)**:
    for all `td, tx, Q, k, p ∈ ℕ`, if `RhBandAgree tx Q 1 (tx + Q)` holds at time `tx`, then `rdrv td (tx + Q) k p = rdrv td tx k p` for ALL `k, p ∈ ℕ`! -/
theorem rdrv_agree_all_of_support_rhBandAgree (td tx Q k p : Nat)
    (hband : RhBandAgree tx Q 1 (tx + Q)) :
    rdrv td (tx + Q) k p = rdrv td tx k p :=
  rdrv_inward_cone_agree_of_rhBandAgree td tx Q (p + k) k p
    (rhBandAgree_all_of_support_agree tx Q (p + k) hband) (by omega)

/-- **All-Time All-Column Agreement of `rhCenter` Under `CenterPeriodic` from Support-Width `RhBandAgree` (`periodic_rhCenter_agree_all_of_support_rhBandAgree`, 9.1363, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s, p ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 (t + m * P)` holds at time `t`, then `rhCenter ((t + s) + m * P) p = rhCenter (t + s) p` for ALL `s, p ∈ ℕ`! -/
theorem periodic_rhCenter_agree_all_of_support_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s p : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 (t + m * P)) :
    rhCenter ((t + s) + m * P) p = rhCenter (t + s) p :=
  periodic_rhCenter_inward_cone_agree_of_rhBandAgree T P hP hper m t (p + s) s p ht
    (rhBandAgree_all_of_support_agree t (m * P) (p + s) hband) (by omega)

/-- **All-Time `maskparity · 0` Agreement Under `CenterPeriodic` from Support-Width `RhBandAgree` (`periodic_maskparity_zero_agree_all_of_support_rhBandAgree`, 9.1364, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, s ∈ ℕ` with `T ≤ t`, if `RhBandAgree t (m * P) 1 (t + m * P)` holds at time `t`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for ALL `s ∈ ℕ`! -/
theorem periodic_maskparity_zero_agree_all_of_support_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t s : Nat) (ht : T ≤ t)
    (hband : RhBandAgree t (m * P) 1 (t + m * P)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  periodic_maskparity_zero_agree_of_rhBandAgree T P hP hper m t s s ht
    (rhBandAgree_all_of_support_agree t (m * P) s hband) (by omega)

/-- **Support-Width (`(z + (p + 1)) + m * P`) Single-Slice Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_doubles`, 9.1365, `kit [33]`)**:
    if `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `settle (z + 1) ≤ z + (p + 1)`, `settle ((z + 1) - m * P) ≤ z + (p + 1)`, and `RhBandAgree (z + (p + 1)) (m * P) 1 ((z + (p + 1)) + m * P)` holds at the single time `z + (p + 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_doubles
    (T P m z p : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : settle (z + 1) ≤ z + (p + 1))
    (hset2 : settle ((z + 1) - m * P) ≤ z + (p + 1))
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 ((z + (p + 1)) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_at_zero_diag_doubles T P m z p (p + 3 * (m * P))
    hP hm ht hz hd hset1 hset2 (by omega)
    (rhBandAgree_all_of_support_agree (z + (p + 1)) (m * P) (p + 3 * (m * P)) hband)

theorem not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_doubles_prop
    (T P m z p : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hband : RhBandAgree (z + (p + 1)) (m * P) 1 ((z + (p + 1)) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_doubles T P m z p hP hm ht hz hd
    hset1 hset2 hband

/-- **Support-Width (`t + m * P = 2^k`) Single-Slice Dyadic Refutation of `CenterPeriodic` (`not_centerPeriodic_of_support_rhBandAgree_twopow`, 9.1366, `kit [33]`)**:
    if `T ≤ t`, `t + m * P = 2^k`, and `RhBandAgree t (m * P) 1 (t + m * P)` holds at the single time `t`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_support_rhBandAgree_twopow
    (T P m t k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hband : RhBandAgree t (m * P) 1 (t + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_twopow T P m t k (twopow k) hP hm ht htm (by omega)
    (rhBandAgree_all_of_support_agree t (m * P) (twopow k) hband)

/-- **Support-Width Single-Slice Zero-Diagonal Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_pair`, 9.1367, `kit [33]`)**:
    if `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `settle z ≤ z + 2^k`, `settle (z + m * P) ≤ (z + m * P) + 2^k`, and `RhBandAgree (z + 2^k) (m * P) 1 ((z + 2^k) + m * P)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_pair
    (T P m z k : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : settle z ≤ z + twopow k)
    (hset1 : settle (z + m * P) ≤ (z + m * P) + twopow k)
    (hband : RhBandAgree (z + twopow k) (m * P) 1 ((z + twopow k) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_at_zero_diag_pair T P m z k (twopow k)
    hP hz0 h2 hz1 ht hset0 hset1 (by omega)
    (rhBandAgree_all_of_support_agree (z + twopow k) (m * P) (twopow k) hband)

theorem not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_pair_prop
    (T P m z k : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P) (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hband : RhBandAgree (z + twopow k) (m * P) 1 ((z + twopow k) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_support_rhBandAgree_at_zero_diag_pair T P m z k hP hz0 h2 hz1 ht
    hset0 hset1 hband

/-- **Dyadic Row White Tail of `rdrv` at Step `v * 2^tx` (`rdrv_dyadic_row_tx_gt_eq_false`, 9.1368, `kit [33]`)**:
    for all `td, tx, v, q ∈ ℕ` with `tx < q`, `rdrv td tx (v * 2^tx) (v * 2^tx + q) = false`! -/
theorem rdrv_dyadic_row_tx_gt_eq_false (td tx v q : Nat) (hq : tx < q) :
    rdrv td tx (v * twopow tx) (v * twopow tx + q) = false := by
  rw [rdrv_dyadic_row_tx_eq_init td tx v q]
  exact rdrv_init_gt_eq_false td tx q hq

/-- **Dyadic Row White Tail of `rhCenter` at Time `t + v * 2^t` (`rhCenter_dyadic_row_t_gt_eq_false`, 9.1369, `kit [33]`)**:
    for all `t, v, q ∈ ℕ` with `t < q`, `rhCenter (t + v * 2^t) (v * 2^t + q) = false`! -/
theorem rhCenter_dyadic_row_t_gt_eq_false (t v q : Nat) (hq : t < q) :
    rhCenter (t + v * twopow t) (v * twopow t + q) = false := by
  rw [rhCenter_dyadic_row_t_eq t v q]
  exact rhCenter_gt_eq_false t q hq

/-- **All-Width Pullback of `RhBandAgree t Q 1 B` from Support-Width Shifted Dyadic Row Agreement (`rhBandAgree_all_of_dyadic_row_support_agree`, 9.1370, `kit [33]`)**:
    for all `t, Q, K, v, B ∈ ℕ` with `t + Q ≤ K`, if `RhBandAgree (t + v * 2^K) Q (v * 2^K + 1) (t + Q)` holds on width `t + Q`, then `RhBandAgree t Q 1 B` holds for ALL `B ∈ ℕ`! -/
theorem rhBandAgree_all_of_dyadic_row_support_agree (t Q K v B : Nat)
    (htK : t + Q ≤ K)
    (hband : RhBandAgree (t + v * twopow K) Q (v * twopow K + 1) (t + Q)) :
    RhBandAgree t Q 1 B :=
  rhBandAgree_all_of_support_agree t Q B
    (rhBandAgree_of_dyadic_row_scale_agree t Q K v 1 (t + Q) htK hband)

/-- **All-Time `maskparity · 0` Agreement from Support-Width Shifted Dyadic Row Agreement (`periodic_maskparity_zero_agree_all_of_dyadic_row_support_agree`, 9.1371, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, v, s ∈ ℕ` with `T ≤ t` and `t + m * P ≤ K`, if `RhBandAgree (t + v * 2^K) (m * P) (v * 2^K + 1) (t + m * P)` holds on width `t + m * P`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for ALL `s ∈ ℕ`! -/
theorem periodic_maskparity_zero_agree_all_of_dyadic_row_support_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v s : Nat) (ht : T ≤ t) (htK : t + m * P ≤ K)
    (hband : RhBandAgree (t + v * twopow K) (m * P) (v * twopow K + 1) (t + m * P)) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  periodic_maskparity_zero_agree_all_of_support_rhBandAgree T P hP hper m t s ht
    (rhBandAgree_of_dyadic_row_scale_agree t (m * P) K v 1 (t + m * P) htK hband)

/-! ### Batch 72: Left-Inversion of `rdrv` and `rhCenter` Across Dyadic Centers `U = v * 2^(t + C)`, Full Two-Sided Embedding of the Left Half `lhCenter` Inside the Right Half `rhCenter`, and Left-Side White Isolation Corridors (`kit [33]`, 9.1372–9.1386) -/

/-- **Spatial Left-Inversion Law of `rdrv` (`rdrv_left_step_inv`, 9.1372, `kit [33]`)**:
    for all `td, tx, k, p ∈ ℕ`, `rdrv td tx k p = bxor (rdrv td tx (k + 1) (p + 1)) (rdrv td tx k (p + 1) || rdrv td tx k (p + 2))`! -/
theorem rdrv_left_step_inv (td tx k p : Nat) :
    rdrv td tx k p =
      bxor (rdrv td tx (k + 1) (p + 1))
        (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) := by
  rw [rdrv_step_succ td tx k p]
  simp only [bxor_eq_xor]
  cases rdrv td tx k p <;>
    cases (rdrv td tx k (p + 1) || rdrv td tx k (p + 2)) <;> rfl

/-- **Subtracted-Column Left-Inversion Law of `rdrv` (`rdrv_left_step_inv_sub`, 9.1373, `kit [33]`)**:
    for all `td, tx, k, U, d ∈ ℕ` with `d + 1 ≤ U`, `rdrv td tx k (U - (d + 1)) = bxor (rdrv td tx (k + 1) (U - d)) (rdrv td tx k (U - d) || rdrv td tx k ((U - d) + 1))`! -/
theorem rdrv_left_step_inv_sub (td tx k U d : Nat) (hdU : d + 1 ≤ U) :
    rdrv td tx k (U - (d + 1)) =
      bxor (rdrv td tx (k + 1) (U - d))
        (rdrv td tx k (U - d) || rdrv td tx k ((U - d) + 1)) := by
  have h := rdrv_left_step_inv td tx k (U - (d + 1))
  rwa [show (U - (d + 1)) + 1 = U - d by omega,
       show (U - (d + 1)) + 2 = (U - d) + 1 by omega] at h

/-- **Spatial Left-Inversion Law of `rhCenter` (`rhCenter_left_step_inv`, 9.1374, `kit [33]`)**:
    for all `t, p ∈ ℕ`, `rhCenter t p = bxor (rhCenter (t + 1) (p + 1)) (rhCenter t (p + 1) || rhCenter t (p + 2))`! -/
theorem rhCenter_left_step_inv (t p : Nat) :
    rhCenter t p =
      bxor (rhCenter (t + 1) (p + 1))
        (rhCenter t (p + 1) || rhCenter t (p + 2)) := by
  rw [← rdrv_zero_eq_rhCenter t p,
      ← rdrv_zero_eq_rhCenter (t + 1) (p + 1),
      ← rdrv_zero_eq_rhCenter t (p + 1),
      ← rdrv_zero_eq_rhCenter t (p + 2)]
  exact rdrv_left_step_inv 0 0 t p

/-- **Subtracted-Column Left-Inversion Law of `rhCenter` (`rhCenter_left_step_inv_sub`, 9.1375, `kit [33]`)**:
    for all `t, U, d ∈ ℕ` with `d + 1 ≤ U`, `rhCenter t (U - (d + 1)) = bxor (rhCenter (t + 1) (U - d)) (rhCenter t (U - d) || rhCenter t ((U - d) + 1))`! -/
theorem rhCenter_left_step_inv_sub (t U d : Nat) (hdU : d + 1 ≤ U) :
    rhCenter t (U - (d + 1)) =
      bxor (rhCenter (t + 1) (U - d))
        (rhCenter t (U - d) || rhCenter t ((U - d) + 1)) := by
  have h := rhCenter_left_step_inv t (U - (d + 1))
  rwa [show (U - (d + 1)) + 1 = U - d by omega,
       show (U - (d + 1)) + 2 = (U - d) + 1 by omega] at h

/-- **Exact Readout of Predecessor Column `v * 2^(tx + C) - 1` in `rdrv` (`rdrv_dyadic_pred_col_eq_center_xor`, 9.1376, `kit [33]`)**:
    for all `td, tx, C, v, j ∈ ℕ` with `1 ≤ v` and `j + 1 ≤ C`, `rdrv td tx (v * 2^(tx + C) + j) (v * 2^(tx + C) - 1) = bxor (center (td + (j + 1))) (center (td + j) || rdrv td tx j 1)`! -/
theorem rdrv_dyadic_pred_col_eq_center_xor (td tx C v j : Nat)
    (hv : 1 ≤ v) (hj : j + 1 ≤ C) :
    rdrv td tx (v * twopow (tx + C) + j) (v * twopow (tx + C) - 1) =
      bxor (Rule30UOR.Core.center (td + (j + 1)))
        (Rule30UOR.Core.center (td + j) || rdrv td tx j 1) := by
  have hpos : 1 ≤ twopow (tx + C) := by
    have hp : 0 < twopow (tx + C) := by
      rw [twopow_eq_pow (tx + C)]
      exact Nat.two_pow_pos (tx + C)
    omega
  have hU : 0 + 1 ≤ v * twopow (tx + C) := by
    have hm := Nat.mul_le_mul hv hpos
    omega
  have hinv := rdrv_left_step_inv_sub td tx (v * twopow (tx + C) + j) (v * twopow (tx + C)) 0 hU
  rw [Nat.sub_zero, Nat.zero_add,
      show (v * twopow (tx + C) + j) + 1 = v * twopow (tx + C) + (j + 1) by omega] at hinv
  have h01 := rdrv_dyadic_slab_tx_add_eq td tx C v (j + 1) 0 hj
  rw [show v * twopow (tx + C) + 0 = v * twopow (tx + C) by omega, rdrv_col0] at h01
  have h00 := rdrv_dyadic_slab_tx_add_eq td tx C v j 0 (by omega)
  rw [show v * twopow (tx + C) + 0 = v * twopow (tx + C) by omega, rdrv_col0] at h00
  have h11 := rdrv_dyadic_slab_tx_add_eq td tx C v j 1 (by omega)
  rw [h01, h00, h11] at hinv
  exact hinv

/-- **Exact Embedding of Left-Half Column `-1` (`lhCenter (t + j) 1`) at Right-Half Column `v * 2^(t + C) - 1` (`rhCenter_dyadic_pred_col_t_add_eq_lhCenter_one`, 9.1377, `kit [33]`)**:
    for all `t, C, v, j ∈ ℕ` with `1 ≤ v` and `j + 1 ≤ C`, `rhCenter (t + (v * 2^(t + C) + j)) (v * 2^(t + C) - 1) = lhCenter (t + j) 1`! -/
theorem rhCenter_dyadic_pred_col_t_add_eq_lhCenter_one (t C v j : Nat)
    (hv : 1 ≤ v) (hj : j + 1 ≤ C) :
    rhCenter (t + (v * twopow (t + C) + j)) (v * twopow (t + C) - 1) =
      lhCenter (t + j) 1 := by
  rw [← rdrv_diag_eq_rhCenter t (v * twopow (t + C) + j) (v * twopow (t + C) - 1),
      rdrv_dyadic_pred_col_eq_center_xor t t C v j hv hj,
      rdrv_diag_eq_rhCenter t j 1,
      show t + (j + 1) = (t + j) + 1 by omega,
      ← lhCenter_one_eq_of_center_fixed (t + j)]

/-- **Delay-Free Embedding of Left-Half Column `-1` (`lhCenter j 1`) at Right-Half Column `v * 2^C - 1` (`rhCenter_dyadic_pred_col_zero_delay_eq_lhCenter_one`, 9.1378, `kit [33]`)**:
    for all `C, v, j ∈ ℕ` with `1 ≤ v` and `j + 1 ≤ C`, `rhCenter (v * 2^C + j) (v * 2^C - 1) = lhCenter j 1`! -/
theorem rhCenter_dyadic_pred_col_zero_delay_eq_lhCenter_one (C v j : Nat)
    (hv : 1 ≤ v) (hj : j + 1 ≤ C) :
    rhCenter (v * twopow C + j) (v * twopow C - 1) =
      lhCenter j 1 := by
  have h := rhCenter_dyadic_pred_col_t_add_eq_lhCenter_one 0 C v j hv hj
  rwa [Nat.zero_add, Nat.zero_add, Nat.zero_add] at h

/-- **General Left-Inversion Propagation of `lhCenter` to the Left of Column `U` in `rhCenter` (`rhCenter_sub_eq_lhCenter_of_col_eq_center_and_one`, 9.1379, `kit [33]`)**:
    for all `t, T0, U, C, d, j ∈ ℕ` with `d ≤ U` and `j + d ≤ C`, if `rhCenter (T0 + s) U = center (t + s)` for all `s ≤ C` and `rhCenter (T0 + s) (U - 1) = lhCenter (t + s) 1` for all `s + 1 ≤ C`, then `rhCenter (T0 + j) (U - d) = lhCenter (t + j) d`! -/
theorem rhCenter_sub_eq_lhCenter_of_col_eq_center_and_one
    (t T0 U C d j : Nat)
    (hdU : d ≤ U) (hjd : j + d ≤ C)
    (h0 : ∀ s : Nat, s ≤ C → rhCenter (T0 + s) U = Rule30UOR.Core.center (t + s))
    (h1 : ∀ s : Nat, s + 1 ≤ C → rhCenter (T0 + s) (U - 1) = lhCenter (t + s) 1) :
    rhCenter (T0 + j) (U - d) = lhCenter (t + j) d := by
  suffices hpair :
      (∀ s : Nat, d ≤ U → s + d ≤ C →
        rhCenter (T0 + s) (U - d) = lhCenter (t + s) d) ∧
      (∀ s : Nat, d + 1 ≤ U → s + (d + 1) ≤ C →
        rhCenter (T0 + s) (U - (d + 1)) = lhCenter (t + s) (d + 1)) from
    hpair.1 j hdU hjd
  clear hdU hjd j
  induction d with
  | zero =>
    refine ⟨fun s _ hs => ?_, fun s _ hs => h1 s hs⟩
    rw [Nat.sub_zero, h0 s (by omega), lhCenter_zero_eq_center (t + s)]
  | succ d ih =>
    refine ⟨ih.2, fun s hd2 hs2 => ?_⟩
    have hinv := rhCenter_left_step_inv_sub (T0 + s) U (d + 1) hd2
    have hstep : (T0 + s) + 1 = T0 + (s + 1) := by omega
    have hu1 : (U - (d + 1)) + 1 = U - d := by omega
    rw [hstep, hu1,
        ih.2 (s + 1) (by omega) (by omega),
        ih.2 s (by omega) (by omega),
        ih.1 s (by omega) (by omega),
        ← show (t + s) + 1 = t + (s + 1) by omega,
        ← lhCenter_outward_step (t + s) d] at hinv
    exact hinv

/-- **Full Embedding of the Left Half `lhCenter (t + j) d` Inside the Right Half `rhCenter` to the Left of `U = v * 2^(t + C)` (`rhCenter_dyadic_sub_eq_lhCenter_t_add`, 9.1380, `kit [33]`)**:
    for all `t, C, v, d, j ∈ ℕ` with `1 ≤ v`, `d ≤ v * 2^(t + C)`, and `j + d ≤ C`, `rhCenter (t + (v * 2^(t + C) + j)) (v * 2^(t + C) - d) = lhCenter (t + j) d`! -/
theorem rhCenter_dyadic_sub_eq_lhCenter_t_add (t C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * twopow (t + C)) (hjd : j + d ≤ C) :
    rhCenter (t + (v * twopow (t + C) + j)) (v * twopow (t + C) - d) =
      lhCenter (t + j) d := by
  have h := rhCenter_sub_eq_lhCenter_of_col_eq_center_and_one
    t (t + v * twopow (t + C)) (v * twopow (t + C)) C d j hdU hjd
    (fun s hs => by
      rw [show (t + v * twopow (t + C)) + s = t + (v * twopow (t + C) + s) by omega]
      have h0 := rhCenter_dyadic_slab_t_add_eq t C v s 0 hs
      rwa [Nat.add_zero, rhCenter_zero_eq_center (t + s)] at h0)
    (fun s hs => by
      rw [show (t + v * twopow (t + C)) + s = t + (v * twopow (t + C) + s) by omega]
      exact rhCenter_dyadic_pred_col_t_add_eq_lhCenter_one t C v s hv hs)
  rwa [show (t + v * twopow (t + C)) + j = t + (v * twopow (t + C) + j) by omega] at h

/-- **Delay-Free Full Embedding of the Left Half `lhCenter j d` Inside the Right Half `rhCenter` to the Left of `U = v * 2^C` (`rhCenter_dyadic_sub_eq_lhCenter_zero_delay`, 9.1381, `kit [33]`)**:
    for all `C, v, d, j ∈ ℕ` with `1 ≤ v`, `d ≤ v * 2^C`, and `j + d ≤ C`, `rhCenter (v * 2^C + j) (v * 2^C - d) = lhCenter j d`! -/
theorem rhCenter_dyadic_sub_eq_lhCenter_zero_delay (C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * twopow C) (hjd : j + d ≤ C) :
    rhCenter (v * twopow C + j) (v * twopow C - d) =
      lhCenter j d := by
  have h := rhCenter_dyadic_sub_eq_lhCenter_t_add 0 C v d j hv
    (by rwa [Nat.zero_add]) hjd
  rwa [Nat.zero_add, Nat.zero_add, Nat.zero_add] at h

/-- **Left-Side White Isolation Corridor Around `U = v * 2^(t + C)` in `rhCenter` (`rhCenter_dyadic_left_white_corridor_t_add`, 9.1382, `kit [33]`)**:
    for all `t, C, v, d, j ∈ ℕ` with `1 ≤ v`, `d ≤ v * 2^(t + C)`, `j + d ≤ C`, and `t + j < d`, `rhCenter (t + (v * 2^(t + C) + j)) (v * 2^(t + C) - d) = false`! -/
theorem rhCenter_dyadic_left_white_corridor_t_add (t C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * twopow (t + C)) (hjd : j + d ≤ C) (htd : t + j < d) :
    rhCenter (t + (v * twopow (t + C) + j)) (v * twopow (t + C) - d) = false := by
  rw [rhCenter_dyadic_sub_eq_lhCenter_t_add t C v d j hv hdU hjd]
  exact lhCenter_gt_eq_false (t + j) d htd

/-- **Delay-Free Left-Side White Isolation Corridor Around `U = v * 2^C` in `rhCenter` (`rhCenter_dyadic_left_white_corridor_zero_delay`, 9.1383, `kit [33]`)**:
    for all `C, v, d, j ∈ ℕ` with `1 ≤ v`, `d ≤ v * 2^C`, `j + d ≤ C`, and `j < d`, `rhCenter (v * 2^C + j) (v * 2^C - d) = false`! -/
theorem rhCenter_dyadic_left_white_corridor_zero_delay (C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * twopow C) (hjd : j + d ≤ C) (hjd2 : j < d) :
    rhCenter (v * twopow C + j) (v * twopow C - d) = false := by
  rw [rhCenter_dyadic_sub_eq_lhCenter_zero_delay C v d j hv hdU hjd]
  exact lhCenter_gt_eq_false j d hjd2

/-- **Horizontal Row Left-Side White Isolation Corridor at `t + v * 2^(t + C)` (`rhCenter_dyadic_row_left_white_corridor_t_add`, 9.1384, `kit [33]`)**:
    for all `t, C, v, d ∈ ℕ` with `1 ≤ v`, `d ≤ C`, and `t < d`, `rhCenter (t + v * 2^(t + C)) (v * 2^(t + C) - d) = false`! -/
theorem rhCenter_dyadic_row_left_white_corridor_t_add (t C v d : Nat)
    (hv : 1 ≤ v) (hdC : d ≤ C) (htd : t < d) :
    rhCenter (t + v * twopow (t + C)) (v * twopow (t + C) - d) = false := by
  have hlt : t + C < twopow (t + C) := twopow_gt_self (t + C)
  have hdU : d ≤ v * twopow (t + C) := by
    have hm := Nat.mul_le_mul_right (twopow (t + C)) hv
    omega
  have h := rhCenter_dyadic_left_white_corridor_t_add t C v d 0 hv hdU (by omega) (by omega)
  rwa [Nat.add_zero] at h

/-- **Delay-Free Horizontal Row Left-Side White Isolation Corridor at `v * 2^C` (`rhCenter_dyadic_row_left_white_corridor_zero_delay`, 9.1385, `kit [33]`)**:
    for all `C, v, d ∈ ℕ` with `1 ≤ v`, `1 ≤ d`, and `d ≤ C`, `rhCenter (v * 2^C) (v * 2^C - d) = false` — at time `v * 2^C`, the `C` columns immediately to the left of `v * 2^C` are ALL WHITE (`false`)! -/
theorem rhCenter_dyadic_row_left_white_corridor_zero_delay (C v d : Nat)
    (hv : 1 ≤ v) (hd1 : 1 ≤ d) (hdC : d ≤ C) :
    rhCenter (v * twopow C) (v * twopow C - d) = false := by
  have h := rhCenter_dyadic_row_left_white_corridor_t_add 0 C v d hv hdC (by omega)
  rwa [Nat.zero_add, Nat.zero_add] at h

/-- **Direct Embedding of Left Diagonals `ldiag` Inside the Right Half `rhCenter` to the Left of `U = v * 2^(t + C)` (`rhCenter_dyadic_sub_eq_ldiag_t_add`, 9.1386, `kit [33]`)**:
    for all `t, C, v, d, j ∈ ℕ` with `1 ≤ v`, `d ≤ v * 2^(t + C)`, `j + d ≤ C`, and `d ≤ t + j`, `rhCenter (t + (v * 2^(t + C) + j)) (v * 2^(t + C) - d) = ldiag ((t + j) - d) (t + j)`! -/
theorem rhCenter_dyadic_sub_eq_ldiag_t_add (t C v d j : Nat)
    (hv : 1 ≤ v) (hdU : d ≤ v * twopow (t + C)) (hjd : j + d ≤ C) (hdt : d ≤ t + j) :
    rhCenter (t + (v * twopow (t + C) + j)) (v * twopow (t + C) - d) =
      Rule30UOR.Core.ldiag ((t + j) - d) (t + j) := by
  rw [rhCenter_dyadic_sub_eq_lhCenter_t_add t C v d j hv hdU hjd]
  exact lhCenter_eq_ldiag (t + j) d hdt

/-! ### Batch 73: Common-Scale Dyadic Embedding of `lhCenter`, `ldiag`, and `LhColAgree` Inside the Right Half `rhCenter` & Left-of-`v * 2^K` Refutation of `CenterPeriodic` (`kit [33]`, 9.1387–9.1401) -/

/-- **Automatic-Width Delay-Free Embedding of `lhCenter j d` at Right-Half Column `v * 2^K - d` (`rhCenter_dyadic_sub_eq_lhCenter_of_le`, 9.1387, `kit [33]`)**:
    for all `K, v, d, j ∈ ℕ` with `1 ≤ v` and `j + d ≤ K`, `rhCenter (v * 2^K + j) (v * 2^K - d) = lhCenter j d` (with `d ≤ v * 2^K` discharged automatically by `K < 2^K`)! -/
theorem rhCenter_dyadic_sub_eq_lhCenter_of_le (K v d j : Nat)
    (hv : 1 ≤ v) (hjd : j + d ≤ K) :
    rhCenter (v * twopow K + j) (v * twopow K - d) =
      lhCenter j d := by
  have hlt : K < twopow K := twopow_gt_self K
  have hdU : d ≤ v * twopow K := by
    have hm := Nat.mul_le_mul_right (twopow K) hv
    omega
  exact rhCenter_dyadic_sub_eq_lhCenter_zero_delay K v d j hv hdU hjd

/-- **Time-Shifted Embedding of `lhCenter (t + s) d` at Right-Half Column `v * 2^K - d` (`rhCenter_dyadic_sub_shift_eq_lhCenter`, 9.1388, `kit [33]`)**:
    for all `t, K, v, d, s ∈ ℕ` with `1 ≤ v` and `(t + s) + d ≤ K`, `rhCenter ((t + v * 2^K) + s) (v * 2^K - d) = lhCenter (t + s) d`! -/
theorem rhCenter_dyadic_sub_shift_eq_lhCenter (t K v d s : Nat)
    (hv : 1 ≤ v) (hts : (t + s) + d ≤ K) :
    rhCenter ((t + v * twopow K) + s) (v * twopow K - d) =
      lhCenter (t + s) d := by
  rw [show (t + v * twopow K) + s = v * twopow K + (t + s) by omega]
  exact rhCenter_dyadic_sub_eq_lhCenter_of_le K v d (t + s) hv hts

/-- **Period-Shifted Embedding of `lhCenter ((t + s) + Q) d` at Right-Half Column `v * 2^K - d` (`rhCenter_dyadic_sub_period_shift_eq_lhCenter`, 9.1389, `kit [33]`)**:
    for all `t, Q, K, v, d, s ∈ ℕ` with `1 ≤ v` and `((t + s) + Q) + d ≤ K`, `rhCenter (((t + v * 2^K) + s) + Q) (v * 2^K - d) = lhCenter ((t + s) + Q) d`! -/
theorem rhCenter_dyadic_sub_period_shift_eq_lhCenter (t Q K v d s : Nat)
    (hv : 1 ≤ v) (hts : ((t + s) + Q) + d ≤ K) :
    rhCenter (((t + v * twopow K) + s) + Q) (v * twopow K - d) =
      lhCenter ((t + s) + Q) d := by
  rw [show ((t + v * twopow K) + s) + Q = v * twopow K + ((t + s) + Q) by omega]
  exact rhCenter_dyadic_sub_eq_lhCenter_of_le K v d ((t + s) + Q) hv hts

/-- **Time-Shifted Embedding of Left-Half Column `-1` (`lhCenter (t + s) 1`) at Right-Half Column `v * 2^K - 1` (`rhCenter_dyadic_pred_col_shift_eq_lhCenter_one`, 9.1390, `kit [33]`)**:
    for all `t, K, v, s ∈ ℕ` with `1 ≤ v` and `(t + s) + 1 ≤ K`, `rhCenter ((t + v * 2^K) + s) (v * 2^K - 1) = lhCenter (t + s) 1`! -/
theorem rhCenter_dyadic_pred_col_shift_eq_lhCenter_one (t K v s : Nat)
    (hv : 1 ≤ v) (hts : (t + s) + 1 ≤ K) :
    rhCenter ((t + v * twopow K) + s) (v * twopow K - 1) =
      lhCenter (t + s) 1 :=
  rhCenter_dyadic_sub_shift_eq_lhCenter t K v 1 s hv hts

/-- **Pointwise Pullback of `lhCenter ((t + s) + Q) d = lhCenter (t + s) d` from Right-Half Column `v * 2^K - d` Agreement (`lhCenter_shift_agree_of_rhCenter_dyadic_sub_agree`, 9.1391, `kit [33]`)**:
    for all `t, Q, K, v, d, s ∈ ℕ` with `1 ≤ v` and `((t + s) + Q) + d ≤ K`, if `rhCenter (((t + v * 2^K) + s) + Q) (v * 2^K - d) = rhCenter ((t + v * 2^K) + s) (v * 2^K - d)`, then `lhCenter ((t + s) + Q) d = lhCenter (t + s) d`! -/
theorem lhCenter_shift_agree_of_rhCenter_dyadic_sub_agree (t Q K v d s : Nat)
    (hv : 1 ≤ v) (hts : ((t + s) + Q) + d ≤ K)
    (h : rhCenter (((t + v * twopow K) + s) + Q) (v * twopow K - d) =
         rhCenter ((t + v * twopow K) + s) (v * twopow K - d)) :
    lhCenter ((t + s) + Q) d = lhCenter (t + s) d := by
  rwa [rhCenter_dyadic_sub_period_shift_eq_lhCenter t Q K v d s hv hts,
       rhCenter_dyadic_sub_shift_eq_lhCenter t K v d s hv (by omega)] at h

/-- **Pullback of `LhColAgree t Q d S` from Right-Half Column Agreement `RhColAgree (t + v * 2^K) Q (v * 2^K - d) S` (`lhColAgree_of_rhColAgree_dyadic_sub`, 9.1392, `kit [33]`)**:
    for all `t, Q, K, v, d, S ∈ ℕ` with `1 ≤ v` and `((t + S) + Q) + d ≤ K`, if `RhColAgree (t + v * 2^K) Q (v * 2^K - d) S`, then `LhColAgree t Q d S`! -/
theorem lhColAgree_of_rhColAgree_dyadic_sub (t Q K v d S : Nat)
    (hv : 1 ≤ v) (hK : ((t + S) + Q) + d ≤ K)
    (hcol : RhColAgree (t + v * twopow K) Q (v * twopow K - d) S) :
    LhColAgree t Q d S := by
  intro s hs
  exact lhCenter_shift_agree_of_rhCenter_dyadic_sub_agree t Q K v d s hv (by omega) (hcol s hs)

/-- **Pullback of Left-Half Column-`-1` Agreement `LhColAgree t Q 1 S` from Right-Half Column `v * 2^K - 1` Agreement (`lhColAgree_one_of_rhColAgree_dyadic_pred_col`, 9.1393, `kit [33]`)**:
    for all `t, Q, K, v, S ∈ ℕ` with `1 ≤ v` and `((t + S) + Q) + 1 ≤ K`, if `RhColAgree (t + v * 2^K) Q (v * 2^K - 1) S`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_rhColAgree_dyadic_pred_col (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : ((t + S) + Q) + 1 ≤ K)
    (hcol : RhColAgree (t + v * twopow K) Q (v * twopow K - 1) S) :
    LhColAgree t Q 1 S :=
  lhColAgree_of_rhColAgree_dyadic_sub t Q K v 1 S hv hK hcol

/-- **Producing `maskparity · 0` Agreement from Right-Half Column `v * 2^K - 1` Agreement (`periodic_maskparity_zero_agree_of_rhColAgree_dyadic_pred_col`, 9.1394, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, v, S, s ∈ ℕ` with `T ≤ t`, `1 ≤ v`, `((t + S) + m * P) + 1 ≤ K`, and `s ≤ S`, if `RhColAgree (t + v * 2^K) (m * P) (v * 2^K - 1) S`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhColAgree_dyadic_pred_col
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v S s : Nat) (ht : T ≤ t) (hv : 1 ≤ v)
    (hK : ((t + S) + m * P) + 1 ≤ K)
    (hcol : RhColAgree (t + v * twopow K) (m * P) (v * twopow K - 1) S)
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlh := lhColAgree_one_of_rhColAgree_dyadic_pred_col t (m * P) K v S hv hK hcol s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlh

/-- **Refutation of `CenterPeriodic` from Right-Half Column `v * 2^K - 1` Agreement at a Doubling Zero Diagonal (`not_centerPeriodic_of_rhColAgree_dyadic_pred_col_at_zero_diag_doubles`, 9.1395, `kit [33]`)**:
    for all `T, P, m, z, p, K, v, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - m * P) (z + (p + 1))`, `p + 3 * (m * P) ≤ S + 1`, `1 ≤ v`, and `(((z + (p + 1)) + S) + m * P) + 1 ≤ K`, if `RhColAgree ((z + (p + 1)) + v * 2^K) (m * P) (v * 2^K - 1) S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhColAgree_dyadic_pred_col_at_zero_diag_doubles
    (T P m z p K v S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : (((z + (p + 1)) + S) + m * P) + 1 ≤ K)
    (hcol : RhColAgree ((z + (p + 1)) + v * twopow K) (m * P) (v * twopow K - 1) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhColAgree_dyadic_pred_col
    T P hP hper m (z + (p + 1)) K v S s ht hv hK hcol hs

/-- **Dyadic-Window Refutation of `CenterPeriodic` from Right-Half Column `v * 2^K - 1` Agreement (`not_centerPeriodic_of_rhColAgree_dyadic_pred_col_twopow`, 9.1396, `kit [33]`)**:
    for all `T, P, m, t, k, K, v, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = 2^k`, `2^k ≤ S + 1`, `1 ≤ v`, and `((t + S) + m * P) + 1 ≤ K`, if `RhColAgree (t + v * 2^K) (m * P) (v * 2^K - 1) S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhColAgree_dyadic_pred_col_twopow
    (T P m t k K v S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((t + S) + m * P) + 1 ≤ K)
    (hcol : RhColAgree (t + v * twopow K) (m * P) (v * twopow K - 1) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhColAgree_dyadic_pred_col
    T P hP hper m t K v S s ht hv hK hcol hs

/-- **Zero-Diagonal Pair Refutation of `CenterPeriodic` from Right-Half Column `v * 2^K - 1` Agreement (`not_centerPeriodic_of_rhColAgree_dyadic_pred_col_at_zero_diag_pair`, 9.1397, `kit [33]`)**:
    for all `T, P, m, z, k, K, v, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + m * P) ((z + m * P) + 2^k)`, `2^k ≤ S + 1`, `1 ≤ v`, and `(((z + 2^k) + S) + m * P) + 1 ≤ K`, if `RhColAgree ((z + 2^k) + v * 2^K) (m * P) (v * 2^K - 1) S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhColAgree_dyadic_pred_col_at_zero_diag_pair
    (T P m z k K v S : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hv : 1 ≤ v) (hK : (((z + twopow k) + S) + m * P) + 1 ≤ K)
    (hcol : RhColAgree ((z + twopow k) + v * twopow K) (m * P) (v * twopow K - 1) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhColAgree_dyadic_pred_col
    T P hP hper m (z + twopow k) K v S s ht hv hK hcol hs

/-- **Automatic-Width Delay-Free Embedding of Left Diagonals `ldiag (j - d) j` at Right-Half Column `v * 2^K - d` (`rhCenter_dyadic_sub_eq_ldiag_of_le`, 9.1398, `kit [33]`)**:
    for all `K, v, d, j ∈ ℕ` with `1 ≤ v`, `j + d ≤ K`, and `d ≤ j`, `rhCenter (v * 2^K + j) (v * 2^K - d) = ldiag (j - d) j`! -/
theorem rhCenter_dyadic_sub_eq_ldiag_of_le (K v d j : Nat)
    (hv : 1 ≤ v) (hjd : j + d ≤ K) (hdj : d ≤ j) :
    rhCenter (v * twopow K + j) (v * twopow K - d) =
      Rule30UOR.Core.ldiag (j - d) j := by
  rw [rhCenter_dyadic_sub_eq_lhCenter_of_le K v d j hv hjd]
  exact lhCenter_eq_ldiag j d hdj

/-- **Embedded Zero-Diagonal White Anti-Diagonal in the Right Half `rhCenter` (`rhCenter_dyadic_sub_zero_diag_eq_false`, 9.1399, `kit [33]`)**:
    for all `K, v, z, d ∈ ℕ` with `1 ≤ v`, `IsZeroDiag z`, `SettledBy z (z + d)`, and `(z + d) + d ≤ K`, `rhCenter (v * 2^K + (z + d)) (v * 2^K - d) = false`! -/
theorem rhCenter_dyadic_sub_zero_diag_eq_false (K v z d : Nat)
    (hv : 1 ≤ v) (hz : IsZeroDiag z) (hset : SettledBy z (z + d)) (hK : (z + d) + d ≤ K) :
    rhCenter (v * twopow K + (z + d)) (v * twopow K - d) = false := by
  rw [rhCenter_dyadic_sub_eq_ldiag_of_le K v d (z + d) hv hK (by omega),
      show (z + d) - d = z by omega]
  exact ldiag_of_zero_diag_prop z (z + d) hz hset

/-- **Embedded Post-Zero-Diagonal (`z + 2`) Black Anti-Diagonal in the Right Half `rhCenter` (`rhCenter_dyadic_sub_after_zero_diag_eq_true`, 9.1400, `kit [33]`)**:
    for all `K, v, z, d ∈ ℕ` with `1 ≤ v`, `IsZeroDiag z`, `SettledBy (z + 2) ((z + 2) + d)`, and `((z + 2) + d) + d ≤ K`, `rhCenter (v * 2^K + ((z + 2) + d)) (v * 2^K - d) = true`! -/
theorem rhCenter_dyadic_sub_after_zero_diag_eq_true (K v z d : Nat)
    (hv : 1 ≤ v) (hz : IsZeroDiag z)
    (hset : SettledBy (z + 2) ((z + 2) + d)) (hK : ((z + 2) + d) + d ≤ K) :
    rhCenter (v * twopow K + ((z + 2) + d)) (v * twopow K - d) = true := by
  rw [rhCenter_dyadic_sub_eq_ldiag_of_le K v d ((z + 2) + d) hv hK (by omega),
      show ((z + 2) + d) - d = z + 2 by omega]
  exact ldiag_after_zero_diag_prop z ((z + 2) + d) hz hset

/-- **Embedded Doubling-Diagonal (`z + 1`) `Q`-Shift Antiperiodicity in the Right Half `rhCenter` (`rhCenter_dyadic_sub_doubling_diag_antiperiodic`, 9.1401, `kit [33]`)**:
    for all `K, v, Q, z, d ∈ ℕ` with `1 ≤ v`, `IsZeroDiag z`, `DoublesAt Q z`, `SettledBy (z + 1) ((z + 1) + d)`, and `(((z + 1) + d) + Q) + (d + Q) ≤ K`, `rhCenter (v * 2^K + (((z + 1) + d) + Q)) (v * 2^K - (d + Q)) = !rhCenter (v * 2^K + ((z + 1) + d)) (v * 2^K - d)`! -/
theorem rhCenter_dyadic_sub_doubling_diag_antiperiodic (K v Q z d : Nat)
    (hv : 1 ≤ v) (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset : SettledBy (z + 1) ((z + 1) + d))
    (hK : (((z + 1) + d) + Q) + (d + Q) ≤ K) :
    rhCenter (v * twopow K + (((z + 1) + d) + Q)) (v * twopow K - (d + Q)) =
      !rhCenter (v * twopow K + ((z + 1) + d)) (v * twopow K - d) := by
  rw [rhCenter_dyadic_sub_eq_ldiag_of_le K v (d + Q) (((z + 1) + d) + Q) hv hK (by omega),
      rhCenter_dyadic_sub_eq_ldiag_of_le K v d ((z + 1) + d) hv (by omega) (by omega),
      show (((z + 1) + d) + Q) - (d + Q) = z + 1 by omega,
      show ((z + 1) + d) - d = z + 1 by omega]
  exact ldiag_settled_antiperiodic_of_doubles Q z ((z + 1) + d) hz hd hset

/-! ### Batch 74: Bilateral Interior Light-Cone Determination for `rhCenter` & Left/Right White Isolation Corridors Around `v * 2^K` (`kit [33]`, 9.1402–9.1416) -/

/-- **Interior Step Recurrence of `rhCenter` (`rhCenter_step_succ_interior`, 9.1402, `kit [33]`)**:
    for all `t, p ∈ ℕ`, `rhCenter (t + 1) (p + 1) = bxor (rhCenter t p) (rhCenter t (p + 1) || rhCenter t (p + 2))`! -/
theorem rhCenter_step_succ_interior (t p : Nat) :
    rhCenter (t + 1) (p + 1) =
      bxor (rhCenter t p) (rhCenter t (p + 1) || rhCenter t (p + 2)) := by
  rw [← rdrv_zero_eq_rhCenter (t + 1) (p + 1),
      ← rdrv_zero_eq_rhCenter t p,
      ← rdrv_zero_eq_rhCenter t (p + 1),
      ← rdrv_zero_eq_rhCenter t (p + 2)]
  exact rdrv_step_succ 0 0 t p

/-- **Single-Step Bilateral Light-Cone Contraction of `rhCenter` (`rhCenter_bilateral_cone_agree_step`, 9.1403, `kit [33]`)**:
    for all `t2, t1, a, L, i ∈ ℕ`, if `∀ q ≤ L + 2, rhCenter t2 (a + q) = rhCenter t1 (a + q)` and `i ≤ L`, then `rhCenter (t2 + 1) ((a + 1) + i) = rhCenter (t1 + 1) ((a + 1) + i)`! -/
theorem rhCenter_bilateral_cone_agree_step (t2 t1 a L i : Nat)
    (h : ∀ q : Nat, q ≤ L + 2 → rhCenter t2 (a + q) = rhCenter t1 (a + q))
    (hi : i ≤ L) :
    rhCenter (t2 + 1) ((a + 1) + i) = rhCenter (t1 + 1) ((a + 1) + i) := by
  rw [show (a + 1) + i = (a + i) + 1 by omega,
      rhCenter_step_succ_interior t2 (a + i),
      rhCenter_step_succ_interior t1 (a + i),
      show (a + i) + 1 = a + (i + 1) by omega,
      show (a + i) + 2 = a + (i + 2) by omega,
      h i (by omega),
      h (i + 1) (by omega),
      h (i + 2) (by omega)]

/-- **Bilateral Interior Light-Cone Determination Theorem for `rhCenter` (`rhCenter_bilateral_cone_agree`, 9.1404, `kit [33]`)**:
    for all `t2, t1, a, L, s, i ∈ ℕ`, if `∀ q ≤ L + 2 * s, rhCenter t2 (a + q) = rhCenter t1 (a + q)` and `i ≤ L`, then `rhCenter (t2 + s) ((a + s) + i) = rhCenter (t1 + s) ((a + s) + i)` (without any center periodicity or column-`0` hypothesis)! -/
theorem rhCenter_bilateral_cone_agree (t2 t1 a L s i : Nat)
    (h : ∀ q : Nat, q ≤ L + 2 * s → rhCenter t2 (a + q) = rhCenter t1 (a + q))
    (hi : i ≤ L) :
    rhCenter (t2 + s) ((a + s) + i) = rhCenter (t1 + s) ((a + s) + i) := by
  induction s generalizing L i with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero, Nat.add_zero]
    exact h i (by omega)
  | succ s ih =>
    have hstep := rhCenter_bilateral_cone_agree_step (t2 + s) (t1 + s) (a + s) L i
      (fun q hq => ih (L + 2) q (fun r hr => h r (by omega)) hq) hi
    rwa [show (t2 + s) + 1 = t2 + (s + 1) by omega,
         show (t1 + s) + 1 = t1 + (s + 1) by omega,
         show (a + s) + 1 = a + (s + 1) by omega] at hstep

/-- **Pointwise Bilateral Light-Cone Determination at Column `P0` (`rhCenter_bilateral_cone_point_agree`, 9.1405, `kit [33]`)**:
    for all `t2, t1, P0, s ∈ ℕ` with `s ≤ P0`, if `∀ q ≤ 2 * s, rhCenter t2 ((P0 - s) + q) = rhCenter t1 ((P0 - s) + q)`, then `rhCenter (t2 + s) P0 = rhCenter (t1 + s) P0`! -/
theorem rhCenter_bilateral_cone_point_agree (t2 t1 P0 s : Nat)
    (hs : s ≤ P0)
    (h : ∀ q : Nat, q ≤ 2 * s → rhCenter t2 ((P0 - s) + q) = rhCenter t1 ((P0 - s) + q)) :
    rhCenter (t2 + s) P0 = rhCenter (t1 + s) P0 := by
  have hc := rhCenter_bilateral_cone_agree t2 t1 (P0 - s) 0 s 0
    (fun q hq => h q (by omega)) (by omega)
  rwa [show ((P0 - s) + s) + 0 = P0 by omega] at hc

/-- **Producing `RhColAgree T0 Q P0 S` from Single-Slice Bilateral Band Agreement `RhBandAgree T0 Q (P0 - S) (2 * S)` (`rhColAgree_of_rhBandAgree_bilateral_cone`, 9.1406, `kit [33]`)**:
    for all `T0, Q, P0, S ∈ ℕ` with `S ≤ P0`, if `RhBandAgree T0 Q (P0 - S) (2 * S)`, then `RhColAgree T0 Q P0 S`! -/
theorem rhColAgree_of_rhBandAgree_bilateral_cone (T0 Q P0 S : Nat)
    (hS : S ≤ P0)
    (hband : RhBandAgree T0 Q (P0 - S) (2 * S)) :
    RhColAgree T0 Q P0 S := by
  intro s hs
  rw [show (T0 + s) + Q = (T0 + Q) + s by omega]
  refine rhCenter_bilateral_cone_point_agree (T0 + Q) T0 P0 s (by omega) (fun q hq => ?_)
  have hb := hband ((S - s) + q) (by omega)
  rwa [show (P0 - S) + ((S - s) + q) = (P0 - s) + q by omega] at hb

/-- **Pullback of `LhColAgree t Q d S` from Single-Slice Bilateral Band Agreement Around `v * 2^K - d` (`lhColAgree_of_rhBandAgree_dyadic_sub_cone`, 9.1407, `kit [33]`)**:
    for all `t, Q, K, v, d, S ∈ ℕ` with `1 ≤ v` and `((t + S) + Q) + d ≤ K`, if `RhBandAgree (t + v * 2^K) Q ((v * 2^K - d) - S) (2 * S)`, then `LhColAgree t Q d S`! -/
theorem lhColAgree_of_rhBandAgree_dyadic_sub_cone (t Q K v d S : Nat)
    (hv : 1 ≤ v) (hK : ((t + S) + Q) + d ≤ K)
    (hband : RhBandAgree (t + v * twopow K) Q ((v * twopow K - d) - S) (2 * S)) :
    LhColAgree t Q d S := by
  have hlt : K < twopow K := twopow_gt_self K
  have hS : S ≤ v * twopow K - d := by
    have hm := Nat.mul_le_mul_right (twopow K) hv
    omega
  exact lhColAgree_of_rhColAgree_dyadic_sub t Q K v d S hv hK
    (rhColAgree_of_rhBandAgree_bilateral_cone (t + v * twopow K) Q (v * twopow K - d) S hS hband)

/-- **Pullback of `LhColAgree t Q 1 S` from Single-Slice Bilateral Band Agreement Around `v * 2^K - 1` (`lhColAgree_one_of_rhBandAgree_dyadic_pred_col_cone`, 9.1408, `kit [33]`)**:
    for all `t, Q, K, v, S ∈ ℕ` with `1 ≤ v` and `((t + S) + Q) + 1 ≤ K`, if `RhBandAgree (t + v * 2^K) Q ((v * 2^K - 1) - S) (2 * S)`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_rhBandAgree_dyadic_pred_col_cone (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : ((t + S) + Q) + 1 ≤ K)
    (hband : RhBandAgree (t + v * twopow K) Q ((v * twopow K - 1) - S) (2 * S)) :
    LhColAgree t Q 1 S :=
  lhColAgree_of_rhBandAgree_dyadic_sub_cone t Q K v 1 S hv hK hband

/-- **Producing `maskparity · 0` Agreement from Single-Slice Bilateral Band Agreement Around `v * 2^K - 1` (`periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_pred_col_cone`, 9.1409, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, v, S, s ∈ ℕ` with `T ≤ t`, `1 ≤ v`, `((t + S) + m * P) + 1 ≤ K`, and `s ≤ S`, if `RhBandAgree (t + v * 2^K) (m * P) ((v * 2^K - 1) - S) (2 * S)`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_pred_col_cone
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v S s : Nat) (ht : T ≤ t) (hv : 1 ≤ v)
    (hK : ((t + S) + m * P) + 1 ≤ K)
    (hband : RhBandAgree (t + v * twopow K) (m * P) ((v * twopow K - 1) - S) (2 * S))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlh := lhColAgree_one_of_rhBandAgree_dyadic_pred_col_cone t (m * P) K v S hv hK hband s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlh

/-- **Single-Slice Bilateral Cone Refutation of `CenterPeriodic` Around `v * 2^K - 1` at a Doubling Zero Diagonal (`not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_at_zero_diag_doubles`, 9.1410, `kit [33]`)**:
    for all `T, P, m, z, p, K, v, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - m * P) (z + (p + 1))`, `p + 3 * (m * P) ≤ S + 1`, `1 ≤ v`, and `(((z + (p + 1)) + S) + m * P) + 1 ≤ K`, if `RhBandAgree ((z + (p + 1)) + v * 2^K) (m * P) ((v * 2^K - 1) - S) (2 * S)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_at_zero_diag_doubles
    (T P m z p K v S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : (((z + (p + 1)) + S) + m * P) + 1 ≤ K)
    (hband : RhBandAgree ((z + (p + 1)) + v * twopow K) (m * P) ((v * twopow K - 1) - S) (2 * S)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_pred_col_cone
    T P hP hper m (z + (p + 1)) K v S s ht hv hK hband hs

/-- **Single-Slice Bilateral Cone Dyadic-Window Refutation of `CenterPeriodic` Around `v * 2^K - 1` (`not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_twopow`, 9.1411, `kit [33]`)**:
    for all `T, P, m, t, k, K, v, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = 2^k`, `2^k ≤ S + 1`, `1 ≤ v`, and `((t + S) + m * P) + 1 ≤ K`, if `RhBandAgree (t + v * 2^K) (m * P) ((v * 2^K - 1) - S) (2 * S)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_twopow
    (T P m t k K v S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((t + S) + m * P) + 1 ≤ K)
    (hband : RhBandAgree (t + v * twopow K) (m * P) ((v * twopow K - 1) - S) (2 * S)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_pred_col_cone
    T P hP hper m t K v S s ht hv hK hband hs

/-- **Single-Slice Bilateral Cone Zero-Diagonal Pair Refutation of `CenterPeriodic` Around `v * 2^K - 1` (`not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_at_zero_diag_pair`, 9.1412, `kit [33]`)**:
    for all `T, P, m, z, k, K, v, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + m * P) ((z + m * P) + 2^k)`, `2^k ≤ S + 1`, `1 ≤ v`, and `(((z + 2^k) + S) + m * P) + 1 ≤ K`, if `RhBandAgree ((z + 2^k) + v * 2^K) (m * P) ((v * 2^K - 1) - S) (2 * S)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_at_zero_diag_pair
    (T P m z k K v S : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hv : 1 ≤ v) (hK : (((z + twopow k) + S) + m * P) + 1 ≤ K)
    (hband : RhBandAgree ((z + twopow k) + v * twopow K) (m * P) ((v * twopow K - 1) - S) (2 * S)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_pred_col_cone
    T P hP hper m (z + twopow k) K v S s ht hv hK hband hs

/-- **Common-Scale Left-Side White Corridor at Row `t + v * 2^K` (`rhCenter_dyadic_row_left_white_corridor_of_le`, 9.1413, `kit [33]`)**:
    for all `t, K, v, d ∈ ℕ` with `1 ≤ v`, `t + d ≤ K`, and `t < d`, `rhCenter (t + v * 2^K) (v * 2^K - d) = false`! -/
theorem rhCenter_dyadic_row_left_white_corridor_of_le (t K v d : Nat)
    (hv : 1 ≤ v) (htdK : t + d ≤ K) (htd : t < d) :
    rhCenter (t + v * twopow K) (v * twopow K - d) = false := by
  have h := rhCenter_dyadic_sub_shift_eq_lhCenter t K v d 0 hv (by omega)
  rw [Nat.add_zero, Nat.add_zero] at h
  rw [h]
  exact lhCenter_gt_eq_false t d htd

/-- **Automatic Agreement in the Left-Side White Corridor of `v * 2^K` (`rhCenter_dyadic_row_left_white_agree`, 9.1414, `kit [33]`)**:
    for all `t, Q, K, v, d ∈ ℕ` with `1 ≤ v`, `(t + Q) + d ≤ K`, and `t + Q < d`, `rhCenter ((t + v * 2^K) + Q) (v * 2^K - d) = rhCenter (t + v * 2^K) (v * 2^K - d)`! -/
theorem rhCenter_dyadic_row_left_white_agree (t Q K v d : Nat)
    (hv : 1 ≤ v) (hK : (t + Q) + d ≤ K) (htd : t + Q < d) :
    rhCenter ((t + v * twopow K) + Q) (v * twopow K - d) =
      rhCenter (t + v * twopow K) (v * twopow K - d) := by
  rw [show (t + v * twopow K) + Q = (t + Q) + v * twopow K by omega,
      rhCenter_dyadic_row_left_white_corridor_of_le (t + Q) K v d hv hK htd,
      rhCenter_dyadic_row_left_white_corridor_of_le t K v d hv (by omega) (by omega)]

/-- **Common-Scale Right-Side White Tail at Row `t + v * 2^K` (`rhCenter_dyadic_row_right_white_of_le`, 9.1415, `kit [33]`)**:
    for all `t, K, v, r ∈ ℕ` with `t ≤ K` and `t < r`, `rhCenter (t + v * 2^K) (v * 2^K + r) = false`! -/
theorem rhCenter_dyadic_row_right_white_of_le (t K v r : Nat)
    (htK : t ≤ K) (htr : t < r) :
    rhCenter (t + v * twopow K) (v * twopow K + r) = false := by
  rw [rhCenter_dyadic_row_scale_eq t K v r htK]
  exact rhCenter_gt_eq_false t r htr

/-- **Automatic Agreement in the Right-Side White Tail of `v * 2^K` (`rhCenter_dyadic_row_right_white_agree`, 9.1416, `kit [33]`)**:
    for all `t, Q, K, v, r ∈ ℕ` with `t + Q ≤ K` and `t + Q < r`, `rhCenter ((t + v * 2^K) + Q) (v * 2^K + r) = rhCenter (t + v * 2^K) (v * 2^K + r)`! -/
theorem rhCenter_dyadic_row_right_white_agree (t Q K v r : Nat)
    (htK : t + Q ≤ K) (htr : t + Q < r) :
    rhCenter ((t + v * twopow K) + Q) (v * twopow K + r) =
      rhCenter (t + v * twopow K) (v * twopow K + r) := by
  rw [show (t + v * twopow K) + Q = (t + Q) + v * twopow K by omega,
      rhCenter_dyadic_row_right_white_of_le (t + Q) K v r htK htr,
      rhCenter_dyadic_row_right_white_of_le t K v r (by omega) (by omega)]

/-! ### Batch 75: Fixed-Width Active Core `[v * 2^K - (t + Q), v * 2^K + (t + Q)]` Expansion to All Bilateral Cones & Full-Row Termination of `LhColAgree` (`kit [33]`, 9.1417–9.1431) -/

/-- **All-Horizon Expansion of Fixed-Width Active Core Agreement Around `v * 2^K` (`rhBandAgree_dyadic_core_expand_to_cone`, 9.1417, `kit [33]`)**:
    for all `t, Q, K, v, S ∈ ℕ` with `1 ≤ v` and `(((t + S) + Q) + (t + Q)) + 1 ≤ K`, if `RhBandAgree (t + v * 2^K) Q (v * 2^K - (t + Q)) (2 * (t + Q))` holds on the fixed-width active core `[v * 2^K - (t + Q), v * 2^K + (t + Q)]`, then `RhBandAgree (t + v * 2^K) Q ((v * 2^K - 1) - S) (2 * S)` holds across the entire bilateral cone of width `2 * S`! -/
theorem rhBandAgree_dyadic_core_expand_to_cone (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : (((t + S) + Q) + (t + Q)) + 1 ≤ K)
    (hcore : RhBandAgree (t + v * twopow K) Q ((v * twopow K) - (t + Q)) (2 * (t + Q))) :
    RhBandAgree (t + v * twopow K) Q (((v * twopow K) - 1) - S) (2 * S) := by
  intro i hi
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  by_cases hleft : (((v * twopow K) - 1) - S) + i < (v * twopow K) - (t + Q)
  · have heq : (((v * twopow K) - 1) - S) + i = (v * twopow K) - ((S + 1) - i) := by omega
    rw [heq]
    exact rhCenter_dyadic_row_left_white_agree t Q K v ((S + 1) - i) hv (by omega) (by omega)
  · by_cases hright : (v * twopow K) + (t + Q) < (((v * twopow K) - 1) - S) + i
    · have heq : (((v * twopow K) - 1) - S) + i = (v * twopow K) + ((((v * twopow K) - 1) - S) + i - (v * twopow K)) := by omega
      rw [heq]
      exact rhCenter_dyadic_row_right_white_agree t Q K v ((((v * twopow K) - 1) - S) + i - (v * twopow K)) (by omega) (by omega)
    · have heq : (((v * twopow K) - 1) - S) + i = ((v * twopow K) - (t + Q)) + ((((v * twopow K) - 1) - S) + i - ((v * twopow K) - (t + Q))) := by omega
      rw [heq]
      exact hcore ((((v * twopow K) - 1) - S) + i - ((v * twopow K) - (t + Q))) (by omega)

/-- **Pullback of `LhColAgree t Q 1 S` for Any Horizon `S` from Fixed-Width Active Core Agreement Around `v * 2^K` (`lhColAgree_one_of_rhBandAgree_dyadic_core`, 9.1418, `kit [33]`)**:
    for all `t, Q, K, v, S ∈ ℕ` with `1 ≤ v` and `(((t + S) + Q) + (t + Q)) + 1 ≤ K`, if `RhBandAgree (t + v * 2^K) Q (v * 2^K - (t + Q)) (2 * (t + Q))`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_rhBandAgree_dyadic_core (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : (((t + S) + Q) + (t + Q)) + 1 ≤ K)
    (hcore : RhBandAgree (t + v * twopow K) Q ((v * twopow K) - (t + Q)) (2 * (t + Q))) :
    LhColAgree t Q 1 S :=
  lhColAgree_one_of_rhBandAgree_dyadic_pred_col_cone t Q K v S hv (by omega)
    (rhBandAgree_dyadic_core_expand_to_cone t Q K v S hv hK hcore)

/-- **Producing `maskparity · 0` Agreement for Any Horizon `S` from Fixed-Width Active Core Agreement Around `v * 2^K` (`periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_core`, 9.1419, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, K, v, S, s ∈ ℕ` with `T ≤ t`, `1 ≤ v`, `(((t + S) + m * P) + (t + m * P)) + 1 ≤ K`, and `s ≤ S`, if `RhBandAgree (t + v * 2^K) (m * P) (v * 2^K - (t + m * P)) (2 * (t + m * P))`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rhBandAgree_dyadic_core
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v S s : Nat) (ht : T ≤ t) (hv : 1 ≤ v)
    (hK : (((t + S) + m * P) + (t + m * P)) + 1 ≤ K)
    (hcore : RhBandAgree (t + v * twopow K) (m * P) ((v * twopow K) - (t + m * P)) (2 * (t + m * P)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlh := lhColAgree_one_of_rhBandAgree_dyadic_core t (m * P) K v S hv hK hcore s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlh

/-- **Horizon-Free Fixed-Width Active Core Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_rhBandAgree_dyadic_core_at_zero_diag_doubles`, 9.1420, `kit [33]`)**:
    for all `T, P, m, z, p, K, v ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - m * P) (z + (p + 1))`, `1 ≤ v`, and `((((z + (p + 1)) + (p + 3 * (m * P))) + m * P) + ((z + (p + 1)) + m * P)) + 1 ≤ K`, if `RhBandAgree ((z + (p + 1)) + v * 2^K) (m * P) (v * 2^K - ((z + (p + 1)) + m * P)) (2 * ((z + (p + 1)) + m * P))`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_core_at_zero_diag_doubles
    (T P m z p K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hv : 1 ≤ v)
    (hK : ((((z + (p + 1)) + (p + 3 * (m * P))) + m * P) + ((z + (p + 1)) + m * P)) + 1 ≤ K)
    (hcore : RhBandAgree ((z + (p + 1)) + v * twopow K) (m * P) ((v * twopow K) - ((z + (p + 1)) + m * P)) (2 * ((z + (p + 1)) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_at_zero_diag_doubles
    T P m z p K v (p + 3 * (m * P)) hP hm ht hz hd hset1 hset2 (by omega) hv (by omega)
    (rhBandAgree_dyadic_core_expand_to_cone (z + (p + 1)) (m * P) K v (p + 3 * (m * P)) hv hK hcore)

/-- **Horizon-Free Fixed-Width Active Core Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rhBandAgree_dyadic_core_twopow`, 9.1421, `kit [33]`)**:
    for all `T, P, m, t, k, K, v ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = 2^k`, `1 ≤ v`, and `(((t + 2^k) + m * P) + (t + m * P)) + 1 ≤ K`, if `RhBandAgree (t + v * 2^K) (m * P) (v * 2^K - (t + m * P)) (2 * (t + m * P))`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_core_twopow
    (T P m t k K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hv : 1 ≤ v)
    (hK : (((t + twopow k) + m * P) + (t + m * P)) + 1 ≤ K)
    (hcore : RhBandAgree (t + v * twopow K) (m * P) ((v * twopow K) - (t + m * P)) (2 * (t + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_twopow
    T P m t k K v (twopow k) hP hm ht htm (by omega) hv (by omega)
    (rhBandAgree_dyadic_core_expand_to_cone t (m * P) K v (twopow k) hv hK hcore)

/-- **Horizon-Free Fixed-Width Active Core Zero-Diagonal Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rhBandAgree_dyadic_core_at_zero_diag_pair`, 9.1422, `kit [33]`)**:
    for all `T, P, m, z, k, K, v ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + m * P) ((z + m * P) + 2^k)`, `1 ≤ v`, and `((((z + 2^k) + 2^k) + m * P) + ((z + 2^k) + m * P)) + 1 ≤ K`, if `RhBandAgree ((z + 2^k) + v * 2^K) (m * P) (v * 2^K - ((z + 2^k) + m * P)) (2 * ((z + 2^k) + m * P))`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_core_at_zero_diag_pair
    (T P m z k K v : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hv : 1 ≤ v)
    (hK : ((((z + twopow k) + twopow k) + m * P) + ((z + twopow k) + m * P)) + 1 ≤ K)
    (hcore : RhBandAgree ((z + twopow k) + v * twopow K) (m * P) ((v * twopow K) - ((z + twopow k) + m * P)) (2 * ((z + twopow k) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_rhBandAgree_dyadic_pred_col_cone_at_zero_diag_pair
    T P m z k K v (twopow k) hP hz0 h2 hz1 ht hset0 hset1 (by omega) hv (by omega)
    (rhBandAgree_dyadic_core_expand_to_cone (z + twopow k) (m * P) K v (twopow k) hv hK hcore)

/-- **Pushforward of `LhBandAgree t Q 0 (t + Q)` to the Left Half `[v * 2^K - (t + Q), v * 2^K]` of the Active Core (`rhBandAgree_dyadic_left_half_of_lhBandAgree`, 9.1423, `kit [33]`)**:
    for all `t, Q, K, v ∈ ℕ` with `1 ≤ v` and `2 * (t + Q) ≤ K`, if `LhBandAgree t Q 0 (t + Q)`, then `RhBandAgree (t + v * 2^K) Q (v * 2^K - (t + Q)) (t + Q)`! -/
theorem rhBandAgree_dyadic_left_half_of_lhBandAgree (t Q K v : Nat)
    (hv : 1 ≤ v) (hK : 2 * (t + Q) ≤ K)
    (hlh : LhBandAgree t Q 0 (t + Q)) :
    RhBandAgree (t + v * twopow K) Q ((v * twopow K) - (t + Q)) (t + Q) := by
  intro i hi
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  have heq : ((v * twopow K) - (t + Q)) + i = (v * twopow K) - ((t + Q) - i) := by omega
  rw [heq,
      show (t + v * twopow K) + Q = ((t + v * twopow K) + 0) + Q by omega,
      rhCenter_dyadic_sub_period_shift_eq_lhCenter t Q K v ((t + Q) - i) 0 hv (by omega),
      show t + v * twopow K = (t + v * twopow K) + 0 by omega,
      rhCenter_dyadic_sub_shift_eq_lhCenter t K v ((t + Q) - i) 0 hv (by omega),
      Nat.add_zero]
  have h := hlh ((t + Q) - i) (by omega)
  rwa [Nat.zero_add] at h

/-- **Pushforward of `RhBandAgree t Q 0 (t + Q)` to the Right Half `[v * 2^K, v * 2^K + (t + Q)]` of the Active Core (`rhBandAgree_dyadic_right_half_of_rhBandAgree`, 9.1424, `kit [33]`)**:
    for all `t, Q, K, v ∈ ℕ` with `t + Q ≤ K`, if `RhBandAgree t Q 0 (t + Q)`, then `RhBandAgree (t + v * 2^K) Q (v * 2^K) (t + Q)`! -/
theorem rhBandAgree_dyadic_right_half_of_rhBandAgree (t Q K v : Nat)
    (htK : t + Q ≤ K)
    (hrh : RhBandAgree t Q 0 (t + Q)) :
    RhBandAgree (t + v * twopow K) Q (v * twopow K) (t + Q) := by
  intro i hi
  rw [show (t + v * twopow K) + Q = (t + Q) + v * twopow K by omega,
      rhCenter_dyadic_row_scale_eq (t + Q) K v i htK,
      rhCenter_dyadic_row_scale_eq t K v i (by omega)]
  have h := hrh i hi
  rwa [Nat.zero_add] at h

/-- **Assembly of Fixed-Width Active Core Agreement Around `v * 2^K` from `LhBandAgree t Q 0 (t + Q)` and `RhBandAgree t Q 0 (t + Q)` (`rhBandAgree_dyadic_core_of_lhBandAgree_and_rhBandAgree`, 9.1425, `kit [33]`)**:
    for all `t, Q, K, v ∈ ℕ` with `1 ≤ v` and `2 * (t + Q) ≤ K`, if `LhBandAgree t Q 0 (t + Q)` and `RhBandAgree t Q 0 (t + Q)`, then `RhBandAgree (t + v * 2^K) Q (v * 2^K - (t + Q)) (2 * (t + Q))`! -/
theorem rhBandAgree_dyadic_core_of_lhBandAgree_and_rhBandAgree (t Q K v : Nat)
    (hv : 1 ≤ v) (hK : 2 * (t + Q) ≤ K)
    (hlh : LhBandAgree t Q 0 (t + Q))
    (hrh : RhBandAgree t Q 0 (t + Q)) :
    RhBandAgree (t + v * twopow K) Q ((v * twopow K) - (t + Q)) (2 * (t + Q)) := by
  intro i hi
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  by_cases hle : i ≤ t + Q
  · exact rhBandAgree_dyadic_left_half_of_lhBandAgree t Q K v hv hK hlh i hle
  · have heq : ((v * twopow K) - (t + Q)) + i = (v * twopow K) + (i - (t + Q)) := by omega
    rw [heq]
    exact rhBandAgree_dyadic_right_half_of_rhBandAgree t Q K v (by omega) hrh (i - (t + Q)) (by omega)

/-- **Full-Row Termination Theorem for `LhColAgree t Q 1 S` (`lhColAgree_one_of_full_row_bandAgree`, 9.1426, `kit [33]`)**:
    for all `t, Q, S ∈ ℕ`, if `LhBandAgree t Q 0 (t + Q)` and `RhBandAgree t Q 0 (t + Q)` hold across the active support of row `t` and row `t + Q`, then `LhColAgree t Q 1 S` holds for ANY horizon `S ∈ ℕ`! -/
theorem lhColAgree_one_of_full_row_bandAgree (t Q S : Nat)
    (hlh : LhBandAgree t Q 0 (t + Q))
    (hrh : RhBandAgree t Q 0 (t + Q)) :
    LhColAgree t Q 1 S :=
  lhColAgree_one_of_rhBandAgree_dyadic_core t Q ((((t + S) + Q) + (t + Q)) + 1) 1 S
    (by omega) (by omega)
    (rhBandAgree_dyadic_core_of_lhBandAgree_and_rhBandAgree t Q ((((t + S) + Q) + (t + Q)) + 1) 1
      (by omega) (by omega) hlh hrh)

/-- **Origin Equality of `lhCenter` and `rhCenter` (`lhCenter_zero_eq_rhCenter_zero`, 9.1427, `kit [33]`)**:
    for all `t ∈ ℕ`, `lhCenter t 0 = rhCenter t 0`! -/
theorem lhCenter_zero_eq_rhCenter_zero (t : Nat) :
    lhCenter t 0 = rhCenter t 0 := by
  rw [lhCenter_zero_eq_center, rhCenter_zero_eq_center]

/-- **Extending `LhBandAgree t Q 1 B` to `LhBandAgree t Q 0 B` via `RhBandAgree t Q 0 B` (`lhBandAgree_zero_of_lhBandAgree_one_and_rhBandAgree_zero`, 9.1428, `kit [33]`)**:
    for all `t, Q, B ∈ ℕ`, if `LhBandAgree t Q 1 B` and `RhBandAgree t Q 0 B`, then `LhBandAgree t Q 0 B`! -/
theorem lhBandAgree_zero_of_lhBandAgree_one_and_rhBandAgree_zero (t Q B : Nat)
    (hlh : LhBandAgree t Q 1 B)
    (hrh : RhBandAgree t Q 0 B) :
    LhBandAgree t Q 0 B := by
  intro i hi
  rw [Nat.zero_add]
  rcases i with _ | j
  · rw [lhCenter_zero_eq_rhCenter_zero (t + Q), lhCenter_zero_eq_rhCenter_zero t]
    have h0 := hrh 0 (by omega)
    rwa [Nat.zero_add] at h0
  · rw [show j + 1 = 1 + j by omega]
    exact hlh j (by omega)

/-- **Full-Row Termination Theorem for `LhColAgree t Q 1 S` from `LhBandAgree t Q 1 (t + Q)` and `RhBandAgree t Q 0 (t + Q)` (`lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero`, 9.1429, `kit [33]`)**:
    for all `t, Q, S ∈ ℕ`, if `LhBandAgree t Q 1 (t + Q)` and `RhBandAgree t Q 0 (t + Q)`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero (t Q S : Nat)
    (hlh : LhBandAgree t Q 1 (t + Q))
    (hrh : RhBandAgree t Q 0 (t + Q)) :
    LhColAgree t Q 1 S :=
  lhColAgree_one_of_full_row_bandAgree t Q S
    (lhBandAgree_zero_of_lhBandAgree_one_and_rhBandAgree_zero t Q (t + Q) hlh hrh) hrh

/-- **Horizon-Free Refutation of `CenterPeriodic` from Single-Slice `LhBandAgree` and `RhBandAgree` at a Doubling Zero Diagonal (`not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_at_zero_diag_doubles`, 9.1430, `kit [33]`)**:
    for all `T, P, m, z, p ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, and `SettledBy ((z + 1) - m * P) (z + (p + 1))`, if `LhBandAgree (z + (p + 1)) (m * P) 1 ((z + (p + 1)) + m * P)` and `RhBandAgree (z + (p + 1)) (m * P) 0 ((z + (p + 1)) + m * P)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_at_zero_diag_doubles
    (T P m z p : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hlh : LhBandAgree (z + (p + 1)) (m * P) 1 ((z + (p + 1)) + m * P))
    (hrh : RhBandAgree (z + (p + 1)) (m * P) 0 ((z + (p + 1)) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hcol := lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero
    (z + (p + 1)) (m * P) (p + 3 * (m * P)) hlh hrh
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p (p + 3 * (m * P)) hP hm ht hz hd hset1 hset2 (by omega) (fun s hs => ?_) hper
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m ((z + (p + 1)) + s) (by omega) (hcol s hs)

/-- **Horizon-Free Dyadic-Window Refutation of `CenterPeriodic` from Single-Slice `LhBandAgree` and `RhBandAgree` (`not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_twopow`, 9.1431, `kit [33]`)**:
    for all `T, P, m, t, k ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, and `t + m * P = 2^k`, if `LhBandAgree t (m * P) 1 (t + m * P)` and `RhBandAgree t (m * P) 0 (t + m * P)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_twopow
    (T P m t k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hlh : LhBandAgree t (m * P) 1 (t + m * P))
    (hrh : RhBandAgree t (m * P) 0 (t + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hcol := lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero t (m * P) (twopow k) hlh hrh
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k (twopow k) hP hm ht htm (by omega) (fun s hs => ?_) hper
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) (hcol s hs)

/-! ### Batch 76: Horizon-Width Bilateral Cone Decomposition (`LhBandAgree t Q 1 S` & `RhBandAgree t Q 0 S → LhColAgree t Q 1 S`) & Two-Scale Single-Row Spatial Shift Reduction (`kit [33]`, 9.1432–9.1446) -/

/-- **Pushforward of Horizon-Width `LhBandAgree t Q 1 S` to the Left Cone Half `[(v * 2^K - 1) - S, v * 2^K - 1]` (`rhBandAgree_dyadic_left_cone_of_lhBandAgree`, 9.1432, `kit [33]`)**:
    for all `t, Q, K, v, S ∈ ℕ` with `1 ≤ v` and `((t + S) + Q) + 1 ≤ K`, if `LhBandAgree t Q 1 S`, then `RhBandAgree (t + v * 2^K) Q ((v * 2^K - 1) - S) S`! -/
theorem rhBandAgree_dyadic_left_cone_of_lhBandAgree (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : ((t + S) + Q) + 1 ≤ K)
    (hlh : LhBandAgree t Q 1 S) :
    RhBandAgree (t + v * twopow K) Q (((v * twopow K) - 1) - S) S := by
  intro i hi
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  have heq : (((v * twopow K) - 1) - S) + i = (v * twopow K) - (1 + (S - i)) := by omega
  rw [heq,
      show (t + v * twopow K) + Q = ((t + v * twopow K) + 0) + Q by omega,
      rhCenter_dyadic_sub_period_shift_eq_lhCenter t Q K v (1 + (S - i)) 0 hv (by omega),
      show t + v * twopow K = (t + v * twopow K) + 0 by omega,
      rhCenter_dyadic_sub_shift_eq_lhCenter t K v (1 + (S - i)) 0 hv (by omega),
      Nat.add_zero]
  exact hlh (S - i) (by omega)

/-- **Pushforward of Arbitrary-Width `RhBandAgree t Q 0 B` to the Right Cone Half `[v * 2^K, v * 2^K + B]` (`rhBandAgree_dyadic_right_cone_of_rhBandAgree`, 9.1433, `kit [33]`)**:
    for all `t, Q, K, v, B ∈ ℕ` with `t + Q ≤ K`, if `RhBandAgree t Q 0 B`, then `RhBandAgree (t + v * 2^K) Q (v * 2^K) B`! -/
theorem rhBandAgree_dyadic_right_cone_of_rhBandAgree (t Q K v B : Nat)
    (htK : t + Q ≤ K)
    (hrh : RhBandAgree t Q 0 B) :
    RhBandAgree (t + v * twopow K) Q (v * twopow K) B := by
  intro i hi
  rw [show (t + v * twopow K) + Q = (t + Q) + v * twopow K by omega,
      rhCenter_dyadic_row_scale_eq (t + Q) K v i htK,
      rhCenter_dyadic_row_scale_eq t K v i (by omega)]
  have h := hrh i hi
  rwa [Nat.zero_add] at h

/-- **Assembly of Bilateral Cone Agreement `RhBandAgree (t + v * 2^K) Q ((v * 2^K - 1) - S) (2 * S)` from Horizon-Width `LhBandAgree t Q 1 S` and `RhBandAgree t Q 0 S` (`rhBandAgree_dyadic_pred_col_cone_of_lhBandAgree_and_rhBandAgree`, 9.1434, `kit [33]`)**:
    for all `t, Q, K, v, S ∈ ℕ` with `1 ≤ v` and `((t + S) + Q) + 1 ≤ K`, if `LhBandAgree t Q 1 S` and `RhBandAgree t Q 0 S`, then `RhBandAgree (t + v * 2^K) Q ((v * 2^K - 1) - S) (2 * S)`! -/
theorem rhBandAgree_dyadic_pred_col_cone_of_lhBandAgree_and_rhBandAgree (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : ((t + S) + Q) + 1 ≤ K)
    (hlh : LhBandAgree t Q 1 S)
    (hrh : RhBandAgree t Q 0 S) :
    RhBandAgree (t + v * twopow K) Q (((v * twopow K) - 1) - S) (2 * S) := by
  intro i hi
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  by_cases hle : i ≤ S
  · exact rhBandAgree_dyadic_left_cone_of_lhBandAgree t Q K v S hv hK hlh i hle
  · have heq : (((v * twopow K) - 1) - S) + i = (v * twopow K) + (i - (S + 1)) := by omega
    rw [heq]
    exact rhBandAgree_dyadic_right_cone_of_rhBandAgree t Q K v S (by omega) hrh (i - (S + 1)) (by omega)

/-- **Drive-Free Bilateral Cone Theorem for `LhColAgree t Q 1 S` from Horizon-Width `LhBandAgree t Q 1 S` and `RhBandAgree t Q 0 S` (`lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero_cone`, 9.1435, `kit [33]`)**:
    for ALL `t, Q, S ∈ ℕ` (without any center-periodicity hypothesis!), if `LhBandAgree t Q 1 S` and `RhBandAgree t Q 0 S` hold across the interior horizon `S`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero_cone (t Q S : Nat)
    (hlh : LhBandAgree t Q 1 S)
    (hrh : RhBandAgree t Q 0 S) :
    LhColAgree t Q 1 S :=
  lhColAgree_one_of_rhBandAgree_dyadic_pred_col_cone t Q (((t + S) + Q) + 1) 1 S
    (by omega) (by omega)
    (rhBandAgree_dyadic_pred_col_cone_of_lhBandAgree_and_rhBandAgree t Q (((t + S) + Q) + 1) 1 S
      (by omega) (by omega) hlh hrh)

/-- **Producing `maskparity · 0` Agreement from Horizon-Width `LhBandAgree t (m * P) 1 S` and `RhBandAgree t (m * P) 0 S` (`periodic_maskparity_zero_agree_of_lhBandAgree_one_and_rhBandAgree_zero_cone`, 9.1436, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, S, s ∈ ℕ` with `T ≤ t` and `s ≤ S`, if `LhBandAgree t (m * P) 1 S` and `RhBandAgree t (m * P) 0 S`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_lhBandAgree_one_and_rhBandAgree_zero_cone
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t)
    (hlh : LhBandAgree t (m * P) 1 S)
    (hrh : RhBandAgree t (m * P) 0 S)
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hcol := lhColAgree_one_of_lhBandAgree_one_and_rhBandAgree_zero_cone t (m * P) S hlh hrh s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hcol

/-- **Horizon-Width Bilateral Cone Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_cone_at_zero_diag_doubles`, 9.1437, `kit [33]`)**:
    for all `T, P, m, z, p, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - m * P) (z + (p + 1))`, and `p + 3 * (m * P) ≤ S + 1`, if `LhBandAgree (z + (p + 1)) (m * P) 1 S` and `RhBandAgree (z + (p + 1)) (m * P) 0 S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_cone_at_zero_diag_doubles
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hlh : LhBandAgree (z + (p + 1)) (m * P) 1 S)
    (hrh : RhBandAgree (z + (p + 1)) (m * P) 0 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_lhBandAgree_one_and_rhBandAgree_zero_cone
    T P hP hper m (z + (p + 1)) S s ht hlh hrh hs

/-- **Horizon-Width Bilateral Cone Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_cone_twopow`, 9.1438, `kit [33]`)**:
    for all `T, P, m, t, k, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = 2^k`, and `2^k ≤ S + 1`, if `LhBandAgree t (m * P) 1 S` and `RhBandAgree t (m * P) 0 S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_cone_twopow
    (T P m t k S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hlh : LhBandAgree t (m * P) 1 S)
    (hrh : RhBandAgree t (m * P) 0 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_lhBandAgree_one_and_rhBandAgree_zero_cone
    T P hP hper m t S s ht hlh hrh hs

/-- **Horizon-Width Bilateral Cone Zero-Diagonal Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_cone_at_zero_diag_pair`, 9.1439, `kit [33]`)**:
    for all `T, P, m, z, k, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + m * P) ((z + m * P) + 2^k)`, and `2^k ≤ S + 1`, if `LhBandAgree (z + 2^k) (m * P) 1 S` and `RhBandAgree (z + 2^k) (m * P) 0 S`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_and_rhBandAgree_zero_cone_at_zero_diag_pair
    (T P m z k S : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hlh : LhBandAgree (z + twopow k) (m * P) 1 S)
    (hrh : RhBandAgree (z + twopow k) (m * P) 0 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_lhBandAgree_one_and_rhBandAgree_zero_cone
    T P hP hper m (z + twopow k) S s ht hlh hrh hs

/-- **45-Degree Dyadic Diagonal Shift Invariance `(v * 2^K ↦ (v + w) * 2^K)` on the Left of `v * 2^K` (`rhCenter_dyadic_diag_shift_left_eq`, 9.1440, `kit [33]`)**:
    for all `t, K, v, w, d ∈ ℕ` with `1 ≤ v` and `t + d ≤ K`, `rhCenter ((t + v * 2^K) + w * 2^K) (((v * 2^K) + w * 2^K) - d) = rhCenter (t + v * 2^K) ((v * 2^K) - d)`! -/
theorem rhCenter_dyadic_diag_shift_left_eq (t K v w d : Nat)
    (hv : 1 ≤ v) (htdK : t + d ≤ K) :
    rhCenter ((t + v * twopow K) + w * twopow K) (((v * twopow K) + w * twopow K) - d) =
      rhCenter (t + v * twopow K) ((v * twopow K) - d) := by
  have hvw : (v * twopow K) + w * twopow K = (v + w) * twopow K := by
    rw [Nat.add_mul]
  rw [show (t + v * twopow K) + w * twopow K = (t + (v + w) * twopow K) + 0 by
        rw [← hvw]; omega,
      hvw,
      rhCenter_dyadic_sub_shift_eq_lhCenter t K (v + w) d 0 (by omega) (by omega),
      show t + v * twopow K = (t + v * twopow K) + 0 by omega,
      rhCenter_dyadic_sub_shift_eq_lhCenter t K v d 0 hv (by omega)]

/-- **45-Degree Dyadic Diagonal Shift Invariance `(v * 2^K ↦ (v + w) * 2^K)` on the Right of `v * 2^K` (`rhCenter_dyadic_diag_shift_right_eq`, 9.1441, `kit [33]`)**:
    for all `t, K, v, w, q ∈ ℕ` with `t ≤ K`, `rhCenter ((t + v * 2^K) + w * 2^K) (((v * 2^K) + w * 2^K) + q) = rhCenter (t + v * 2^K) ((v * 2^K) + q)`! -/
theorem rhCenter_dyadic_diag_shift_right_eq (t K v w q : Nat)
    (htK : t ≤ K) :
    rhCenter ((t + v * twopow K) + w * twopow K) (((v * twopow K) + w * twopow K) + q) =
      rhCenter (t + v * twopow K) ((v * twopow K) + q) := by
  have hvw : (v * twopow K) + w * twopow K = (v + w) * twopow K := by
    rw [Nat.add_mul]
  rw [show (t + v * twopow K) + w * twopow K = t + ((v * twopow K) + w * twopow K) by omega,
      hvw,
      rhCenter_dyadic_row_scale_eq t K (v + w) q htK,
      rhCenter_dyadic_row_scale_eq t K v q htK]

/-- **45-Degree Dyadic Diagonal Shift Invariance Across Any Two-Sided Band Around `v * 2^K` (`rhCenter_dyadic_diag_shift_band_eq`, 9.1442, `kit [33]`)**:
    for all `t, K, v, w, W, i ∈ ℕ` with `1 ≤ v` and `t + W ≤ K`, `rhCenter ((t + v * 2^K) + w * 2^K) ((((v * 2^K) + w * 2^K) - W) + i) = rhCenter (t + v * 2^K) (((v * 2^K) - W) + i)`! -/
theorem rhCenter_dyadic_diag_shift_band_eq (t K v w W i : Nat)
    (hv : 1 ≤ v) (htWK : t + W ≤ K) :
    rhCenter ((t + v * twopow K) + w * twopow K) ((((v * twopow K) + w * twopow K) - W) + i) =
      rhCenter (t + v * twopow K) (((v * twopow K) - W) + i) := by
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  by_cases hle : i ≤ W
  · rw [show (((v * twopow K) + w * twopow K) - W) + i = ((v * twopow K) + w * twopow K) - (W - i) by omega,
        show ((v * twopow K) - W) + i = (v * twopow K) - (W - i) by omega]
    exact rhCenter_dyadic_diag_shift_left_eq t K v w (W - i) hv (by omega)
  · rw [show (((v * twopow K) + w * twopow K) - W) + i = ((v * twopow K) + w * twopow K) + (i - W) by omega,
        show ((v * twopow K) - W) + i = (v * twopow K) + (i - W) by omega]
    exact rhCenter_dyadic_diag_shift_right_eq t K v w (i - W) (by omega)

/-- **Reduction of Time-Shift `RhBandAgree (t + v * 2^K) (w * 2^K)` to Purely Spatial Period-Shift Agreement at a Single Row `(t + v * 2^K) + w * 2^K` (`rhBandAgree_dyadic_of_spatial_period_shift_agree`, 9.1443, `kit [33]`)**:
    for all `t, K, v, w, W, B ∈ ℕ` with `1 ≤ v` and `t + W ≤ K`, if `∀ i ≤ B, rhCenter ((t + v * 2^K) + w * 2^K) (((v * 2^K) - W) + i) = rhCenter ((t + v * 2^K) + w * 2^K) ((((v * 2^K) + w * 2^K) - W) + i)`, then `RhBandAgree (t + v * 2^K) (w * 2^K) ((v * 2^K) - W) B`! -/
theorem rhBandAgree_dyadic_of_spatial_period_shift_agree (t K v w W B : Nat)
    (hv : 1 ≤ v) (htWK : t + W ≤ K)
    (hspat : ∀ i : Nat, i ≤ B →
      rhCenter ((t + v * twopow K) + w * twopow K) (((v * twopow K) - W) + i) =
        rhCenter ((t + v * twopow K) + w * twopow K) ((((v * twopow K) + w * twopow K) - W) + i)) :
    RhBandAgree (t + v * twopow K) (w * twopow K) ((v * twopow K) - W) B := by
  intro i hi
  rw [hspat i hi]
  exact rhCenter_dyadic_diag_shift_band_eq t K v w W i hv htWK

/-- **Two-Scale Single-Row Embedding of `lhCenter t d` at Column `(u * 2^L + w * 2^K) - d` of Row `(t + u * 2^L) + w * 2^K` (`rhCenter_two_scale_row_left_eq_lhCenter`, 9.1444, `kit [33]`)**:
    for all `t, K, L, u, w, d ∈ ℕ` with `1 ≤ u`, `K ≤ L`, and `t + d ≤ K`, `rhCenter ((t + u * 2^L) + w * 2^K) (((u * 2^L) + w * 2^K) - d) = lhCenter t d`! -/
theorem rhCenter_two_scale_row_left_eq_lhCenter (t K L u w d : Nat)
    (hu : 1 ≤ u) (hKL : K ≤ L) (htdK : t + d ≤ K) :
    rhCenter ((t + u * twopow L) + w * twopow K) (((u * twopow L) + w * twopow K) - d) =
      lhCenter t d := by
  have huL : u * twopow L = (u * twopow (L - K)) * twopow K := by
    rw [Nat.mul_assoc, ← twopow_add_eq_mul K (L - K), show K + (L - K) = L by omega]
  have h1 : 1 ≤ u * twopow (L - K) := by
    have hgt : L - K < twopow (L - K) := twopow_gt_self (L - K)
    have hpos : 1 ≤ twopow (L - K) := by omega
    exact Nat.mul_le_mul hu hpos
  rw [huL,
      rhCenter_dyadic_diag_shift_left_eq t K (u * twopow (L - K)) w d h1 htdK,
      show t + (u * twopow (L - K)) * twopow K = (t + (u * twopow (L - K)) * twopow K) + 0 by omega,
      rhCenter_dyadic_sub_shift_eq_lhCenter t K (u * twopow (L - K)) d 0 h1 (by omega),
      Nat.add_zero]

/-- **Two-Scale Single-Row Embedding of `rhCenter t q` at Column `(u * 2^L + w * 2^K) + q` of Row `(t + u * 2^L) + w * 2^K` (`rhCenter_two_scale_row_right_eq_rhCenter`, 9.1445, `kit [33]`)**:
    for all `t, K, L, u, w, q ∈ ℕ` with `K ≤ L` and `t ≤ K`, `rhCenter ((t + u * 2^L) + w * 2^K) (((u * 2^L) + w * 2^K) + q) = rhCenter t q`! -/
theorem rhCenter_two_scale_row_right_eq_rhCenter (t K L u w q : Nat)
    (hKL : K ≤ L) (htK : t ≤ K) :
    rhCenter ((t + u * twopow L) + w * twopow K) (((u * twopow L) + w * twopow K) + q) =
      rhCenter t q := by
  have huL : u * twopow L = (u * twopow (L - K)) * twopow K := by
    rw [Nat.mul_assoc, ← twopow_add_eq_mul K (L - K), show K + (L - K) = L by omega]
  rw [huL,
      rhCenter_dyadic_diag_shift_right_eq t K (u * twopow (L - K)) w q htK,
      rhCenter_dyadic_row_scale_eq t K (u * twopow (L - K)) q htK]

/-- **Two-Scale Single-Row Spatial Shift Theorem for `LhColAgree t (w * 2^K) 1 S` (`lhColAgree_one_of_two_scale_single_row_spatial_agree`, 9.1446, `kit [33]`)**:
    for all `t, K, L, u, w, S ∈ ℕ` with `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + w * 2^K) + 1 ≤ L`, and `K ≤ L`, if at the single row `(t + u * 2^L) + w * 2^K` the band of width `2 * S` around `u * 2^L - 1` agrees with its spatial shift by `w * 2^K`, then `LhColAgree t (w * 2^K) 1 S`! -/
theorem lhColAgree_one_of_two_scale_single_row_spatial_agree (t K L u w S : Nat)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + w * twopow K) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ 2 * S →
      rhCenter ((t + u * twopow L) + w * twopow K) ((((u * twopow L) - 1) - S) + i) =
        rhCenter ((t + u * twopow L) + w * twopow K) (((((u * twopow L) + w * twopow K) - 1) - S) + i)) :
    LhColAgree t (w * twopow K) 1 S := by
  refine lhColAgree_one_of_rhBandAgree_dyadic_pred_col_cone t (w * twopow K) L u S hu hL ?_
  have huL : u * twopow L = (u * twopow (L - K)) * twopow K := by
    rw [Nat.mul_assoc, ← twopow_add_eq_mul K (L - K), show K + (L - K) = L by omega]
  have h1 : 1 ≤ u * twopow (L - K) := by
    have hgt : L - K < twopow (L - K) := twopow_gt_self (L - K)
    have hpos : 1 ≤ twopow (L - K) := by omega
    exact Nat.mul_le_mul hu hpos
  have hlt : K < twopow K := twopow_gt_self K
  have hm : twopow K ≤ (u * twopow (L - K)) * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) h1
    omega
  intro i hi
  rw [hspat i hi, huL,
      show ((((u * twopow (L - K)) * twopow K + w * twopow K) - 1) - S) + i =
        ((((u * twopow (L - K)) * twopow K + w * twopow K) - (S + 1)) + i) by omega,
      show ((((u * twopow (L - K)) * twopow K) - 1) - S) + i =
        ((((u * twopow (L - K)) * twopow K) - (S + 1)) + i) by omega]
  exact rhCenter_dyadic_diag_shift_band_eq t K (u * twopow (L - K)) w (S + 1) i h1 (by omega)

/-! ### Batch 77: Dyadic-Multiple Period (`m = c * 2^K`) Single-Row Refutation of `CenterPeriodic` & Exact Isolated Impulse Structure of `rhCenter (u * 2^L)` and `rdrv td (u * 2^L)` (`kit [33]`, 9.1447–9.1461) -/

/-- **Two-Scale Single-Row Spatial Shift Theorem for `LhColAgree t ((c * 2^K) * P) 1 S` (`lhColAgree_one_of_two_scale_single_row_mul_period_agree`, 9.1447, `kit [33]`)**:
    for all `t, P, K, L, u, c, S ∈ ℕ` with `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + (c * 2^K) * P) + 1 ≤ L`, and `K ≤ L`, if at the single row `(t + u * 2^L) + (c * 2^K) * P` the band of width `2 * S` around `u * 2^L - 1` agrees with its spatial shift by `(c * 2^K) * P`, then `LhColAgree t ((c * 2^K) * P) 1 S`! -/
theorem lhColAgree_one_of_two_scale_single_row_mul_period_agree (t P K L u c S : Nat)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ 2 * S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((((u * twopow L) - 1) - S) + i) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((((u * twopow L) + (c * twopow K) * P) - 1) - S) + i)) :
    LhColAgree t ((c * twopow K) * P) 1 S := by
  have heq : (c * twopow K) * P = (c * P) * twopow K := by
    rw [Nat.mul_right_comm]
  rw [heq] at hL hspat ⊢
  exact lhColAgree_one_of_two_scale_single_row_spatial_agree t K L u (c * P) S hu hK hL hKL hspat

/-- **Producing `maskparity · 0` Agreement from Two-Scale Single-Row Spatial Shift Agreement by `(c * 2^K) * P` (`periodic_maskparity_zero_agree_of_two_scale_single_row_mul_period_agree`, 9.1448, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `t, K, L, u, c, S, s ∈ ℕ` with `T ≤ t`, `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + (c * 2^K) * P) + 1 ≤ L`, `K ≤ L`, and `s ≤ S`, if at the single row `(t + u * 2^L) + (c * 2^K) * P` the band of width `2 * S` around `u * 2^L - 1` agrees with its spatial shift by `(c * 2^K) * P`, then `maskparity ((t + s) + (c * 2^K) * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_two_scale_single_row_mul_period_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (t K L u c S s : Nat) (ht : T ≤ t) (hu : 1 ≤ u)
    (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ 2 * S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((((u * twopow L) - 1) - S) + i) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((((u * twopow L) + (c * twopow K) * P) - 1) - S) + i))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + (c * twopow K) * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlh := lhColAgree_one_of_two_scale_single_row_mul_period_agree t P K L u c S hu hK hL hKL hspat s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper (c * twopow K) (t + s) (by omega) hlh

/-- **Two-Scale Single-Row Spatial Shift Refutation of `CenterPeriodic` at a Doubling Zero Diagonal for `(c * 2^K) * P` (`not_centerPeriodic_of_two_scale_single_row_at_zero_diag_doubles`, 9.1449, `kit [33]`)**:
    for all `T, P, c, z, p, K, L, u, S ∈ ℕ` with `0 < P`, `0 < c`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt ((c * 2^K) * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - (c * 2^K) * P) (z + (p + 1))`, `p + 3 * ((c * 2^K) * P) ≤ S + 1`, `1 ≤ u`, `((z + (p + 1)) + S) + 1 ≤ K`, `(((z + (p + 1)) + S) + (c * 2^K) * P) + 1 ≤ L`, and `K ≤ L`, if at the single row `((z + (p + 1)) + u * 2^L) + (c * 2^K) * P` the band of width `2 * S` around `u * 2^L - 1` agrees with its spatial shift by `(c * 2^K) * P`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_two_scale_single_row_at_zero_diag_doubles
    (T P c z p K L u S : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - (c * twopow K) * P) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : ((z + (p + 1)) + S) + 1 ≤ K)
    (hL : (((z + (p + 1)) + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ 2 * S →
      rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) ((((u * twopow L) - 1) - S) + i) =
        rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) (((((u * twopow L) + (c * twopow K) * P) - 1) - S) + i)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hm : 0 < c * twopow K := by
    have hgt : K < twopow K := twopow_gt_self K
    exact Nat.mul_pos hc (by omega)
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P (c * twopow K) z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_two_scale_single_row_mul_period_agree
    T P hP hper (z + (p + 1)) K L u c S s ht hu hK hL hKL hspat hs

/-- **Two-Scale Single-Row Spatial Shift Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_two_scale_single_row_twopow`, 9.1450, `kit [33]`)**:
    for all `T, P, c, t, k, K, L, u, S ∈ ℕ` with `0 < P`, `0 < c`, `T ≤ t`, `t + (c * 2^K) * P = 2^k`, `2^k ≤ S + 1`, `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + (c * 2^K) * P) + 1 ≤ L`, and `K ≤ L`, if at the single row `(t + u * 2^L) + (c * 2^K) * P` the band of width `2 * S` around `u * 2^L - 1` agrees with its spatial shift by `(c * 2^K) * P`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_two_scale_single_row_twopow
    (T P c t k K L u S : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ t) (htm : t + (c * twopow K) * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ 2 * S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((((u * twopow L) - 1) - S) + i) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((((u * twopow L) + (c * twopow K) * P) - 1) - S) + i)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hm : 0 < c * twopow K := by
    have hgt : K < twopow K := twopow_gt_self K
    exact Nat.mul_pos hc (by omega)
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P (c * twopow K) t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_two_scale_single_row_mul_period_agree
    T P hP hper t K L u c S s ht hu hK hL hKL hspat hs

/-- **Two-Scale Single-Row Spatial Shift Zero-Diagonal Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_two_scale_single_row_at_zero_diag_pair`, 9.1451, `kit [33]`)**:
    for all `T, P, c, z, k, K, L, u, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + (c * 2^K) * P`, `IsZeroDiag ((z + (c * 2^K) * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + (c * 2^K) * P) ((z + (c * 2^K) * P) + 2^k)`, `2^k ≤ S + 1`, `1 ≤ u`, `((z + 2^k) + S) + 1 ≤ K`, `(((z + 2^k) + S) + (c * 2^K) * P) + 1 ≤ L`, and `K ≤ L`, if at the single row `((z + 2^k) + u * 2^L) + (c * 2^K) * P` the band of width `2 * S` around `u * 2^L - 1` agrees with its spatial shift by `(c * 2^K) * P`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_two_scale_single_row_at_zero_diag_pair
    (T P c z k K L u S : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + (c * twopow K) * P)
    (hz1 : IsZeroDiag ((z + (c * twopow K) * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + (c * twopow K) * P) ((z + (c * twopow K) * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hK : ((z + twopow k) + S) + 1 ≤ K)
    (hL : (((z + twopow k) + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ 2 * S →
      rhCenter (((z + twopow k) + u * twopow L) + (c * twopow K) * P) ((((u * twopow L) - 1) - S) + i) =
        rhCenter (((z + twopow k) + u * twopow L) + (c * twopow K) * P) (((((u * twopow L) + (c * twopow K) * P) - 1) - S) + i)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P (c * twopow K) z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_two_scale_single_row_mul_period_agree
    T P hP hper (z + twopow k) K L u c S s ht hu hK hL hKL hspat hs

/-- **Exact Left White Corridor at a Pure Dyadic Row `u * 2^L` (`rhCenter_dyadic_exact_row_left_eq_false`, 9.1452, `kit [33]`)**:
    for all `L, u, d ∈ ℕ` with `1 ≤ u`, `d ≤ L`, and `0 < d`, `rhCenter (u * 2^L) (u * 2^L - d) = false`! -/
theorem rhCenter_dyadic_exact_row_left_eq_false (L u d : Nat)
    (hu : 1 ≤ u) (hdL : d ≤ L) (h0d : 0 < d) :
    rhCenter (u * twopow L) ((u * twopow L) - d) = false := by
  have h := rhCenter_dyadic_row_left_white_corridor_of_le 0 L u d hu (by omega) h0d
  rwa [Nat.zero_add] at h

/-- **Exact Black Diagonal Impulse at `(u * 2^L, u * 2^L)` (`rhCenter_dyadic_exact_row_self_eq_true`, 9.1453, `kit [33]`)**:
    for all `L, u ∈ ℕ`, `rhCenter (u * 2^L) (u * 2^L) = true`! -/
theorem rhCenter_dyadic_exact_row_self_eq_true (L u : Nat) :
    rhCenter (u * twopow L) (u * twopow L) = true :=
  rhCenter_self_eq_true (u * twopow L)

/-- **Exact Right White Tail at a Pure Dyadic Row `u * 2^L` (`rhCenter_dyadic_exact_row_right_eq_false`, 9.1454, `kit [33]`)**:
    for all `L, u, r ∈ ℕ` with `0 < r`, `rhCenter (u * 2^L) (u * 2^L + r) = false`! -/
theorem rhCenter_dyadic_exact_row_right_eq_false (L u r : Nat)
    (h0r : 0 < r) :
    rhCenter (u * twopow L) ((u * twopow L) + r) = false :=
  rhCenter_gt_eq_false (u * twopow L) ((u * twopow L) + r) (by omega)

/-- **Exact Two-Sided Band Translation Invariance Between Any Two Pure Dyadic Rows `u * 2^L` and `v * 2^L` (`rhCenter_dyadic_exact_row_translate_agree`, 9.1455, `kit [33]`)**:
    for all `L, u, v, W, i ∈ ℕ` with `1 ≤ u`, `1 ≤ v`, and `W ≤ L`, `rhCenter (v * 2^L) (((v * 2^L) - W) + i) = rhCenter (u * 2^L) (((u * 2^L) - W) + i)`! -/
theorem rhCenter_dyadic_exact_row_translate_agree (L u v W i : Nat)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hWL : W ≤ L) :
    rhCenter (v * twopow L) (((v * twopow L) - W) + i) =
      rhCenter (u * twopow L) (((u * twopow L) - W) + i) := by
  have hv1 := rhCenter_dyadic_diag_shift_band_eq 0 L 1 (v - 1) W i (by omega) (by omega)
  have hu1 := rhCenter_dyadic_diag_shift_band_eq 0 L 1 (u - 1) W i (by omega) (by omega)
  have hveq : (1 * twopow L) + (v - 1) * twopow L = v * twopow L := by
    rw [← Nat.add_mul, show 1 + (v - 1) = v by omega]
  have hueq : (1 * twopow L) + (u - 1) * twopow L = u * twopow L := by
    rw [← Nat.add_mul, show 1 + (u - 1) = u by omega]
  rw [Nat.zero_add, hveq] at hv1
  rw [Nat.zero_add, hueq] at hu1
  rw [hv1, hu1]

/-- **Multi-Step Evolved Translation Invariance Between Any Two Dyadic Multiples `u * 2^L` and `v * 2^L` (`rhCenter_dyadic_exact_row_evolve_translate_agree`, 9.1456, `kit [33]`)**:
    for all `L, u, v, W, s, i ∈ ℕ` with `1 ≤ u`, `1 ≤ v`, and `s + W ≤ L`, `rhCenter ((v * 2^L) + s) (((v * 2^L) - W) + i) = rhCenter ((u * 2^L) + s) (((u * 2^L) - W) + i)`! -/
theorem rhCenter_dyadic_exact_row_evolve_translate_agree (L u v W s i : Nat)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hsWL : s + W ≤ L) :
    rhCenter ((v * twopow L) + s) (((v * twopow L) - W) + i) =
      rhCenter ((u * twopow L) + s) (((u * twopow L) - W) + i) := by
  have hv1 := rhCenter_dyadic_diag_shift_band_eq s L 1 (v - 1) W i (by omega) hsWL
  have hu1 := rhCenter_dyadic_diag_shift_band_eq s L 1 (u - 1) W i (by omega) hsWL
  have hveq : (1 * twopow L) + (v - 1) * twopow L = v * twopow L := by
    rw [← Nat.add_mul, show 1 + (v - 1) = v by omega]
  have hueq : (1 * twopow L) + (u - 1) * twopow L = u * twopow L := by
    rw [← Nat.add_mul, show 1 + (u - 1) = u by omega]
  rw [show (s + 1 * twopow L) + (v - 1) * twopow L = ((1 * twopow L) + (v - 1) * twopow L) + s by omega, hveq] at hv1
  rw [show (s + 1 * twopow L) + (u - 1) * twopow L = ((1 * twopow L) + (u - 1) * twopow L) + s by omega, hueq] at hu1
  rw [hv1, hu1]

/-- **Pure Drive Operator `rdrv td (u * 2^L) 0` Left White Corridor (`rdrv_dyadic_exact_row_left_eq_false`, 9.1457, `kit [33]`)**:
    for all `td, L, u, d ∈ ℕ` with `1 ≤ u`, `d ≤ L`, and `0 < d`, `rdrv td (u * 2^L) 0 ((u * 2^L) - d) = false`! -/
theorem rdrv_dyadic_exact_row_left_eq_false (td L u d : Nat)
    (hu : 1 ≤ u) (hdL : d ≤ L) (h0d : 0 < d) :
    rdrv td (u * twopow L) 0 ((u * twopow L) - d) = false := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_init td (u * twopow L) ((u * twopow L) - d) (by omega)]
  exact rhCenter_dyadic_exact_row_left_eq_false L u d hu hdL h0d

/-- **Pure Drive Operator `rdrv td (u * 2^L) 0` Black Impulse at `u * 2^L` (`rdrv_dyadic_exact_row_self_eq_true`, 9.1458, `kit [33]`)**:
    for all `td, L, u ∈ ℕ` with `1 ≤ u`, `rdrv td (u * 2^L) 0 (u * 2^L) = true`! -/
theorem rdrv_dyadic_exact_row_self_eq_true (td L u : Nat)
    (hu : 1 ≤ u) :
    rdrv td (u * twopow L) 0 (u * twopow L) = true := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_init td (u * twopow L) (u * twopow L) (by omega)]
  exact rhCenter_dyadic_exact_row_self_eq_true L u

/-- **Pure Drive Operator `rdrv td (u * 2^L) 0` Right White Tail (`rdrv_dyadic_exact_row_right_eq_false`, 9.1459, `kit [33]`)**:
    for all `td, L, u, r ∈ ℕ` with `0 < r`, `rdrv td (u * 2^L) 0 ((u * 2^L) + r) = false`! -/
theorem rdrv_dyadic_exact_row_right_eq_false (td L u r : Nat)
    (h0r : 0 < r) :
    rdrv td (u * twopow L) 0 ((u * twopow L) + r) = false := by
  rw [rdrv_init td (u * twopow L) ((u * twopow L) + r) (by omega)]
  exact rhCenter_dyadic_exact_row_right_eq_false L u r h0r

/-- **Drive-Independent Evolution of `rdrv td (u * 2^L) s` to `lhCenter s d` on the Left of `u * 2^L` (`rdrv_dyadic_exact_row_shift_left_eq`, 9.1460, `kit [33]`)**:
    for all `td, L, u, d, s ∈ ℕ` with `1 ≤ u` and `s + d ≤ L`, `rdrv td (u * 2^L) s ((u * 2^L) - d) = lhCenter s d` (completely independent of the drive offset `td` at column `0`!) -/
theorem rdrv_dyadic_exact_row_shift_left_eq (td L u d s : Nat)
    (hu : 1 ≤ u) (hsdL : s + d ≤ L) :
    rdrv td (u * twopow L) s ((u * twopow L) - d) = lhCenter s d := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_outside_cone_eq_rhCenter td (u * twopow L) s ((u * twopow L) - d) (by omega)]
  exact rhCenter_dyadic_sub_eq_lhCenter_of_le L u d s hu hsdL

/-- **Drive-Independent Evolution of `rdrv td (u * 2^L) s` to `rhCenter s q` on the Right of `u * 2^L` (`rdrv_dyadic_exact_row_shift_right_eq`, 9.1461, `kit [33]`)**:
    for all `td, L, u, q, s ∈ ℕ` with `1 ≤ u` and `s ≤ L`, `rdrv td (u * 2^L) s ((u * 2^L) + q) = rhCenter s q` (completely independent of the drive offset `td` at column `0`!) -/
theorem rdrv_dyadic_exact_row_shift_right_eq (td L u q s : Nat)
    (hu : 1 ≤ u) (hsL : s ≤ L) :
    rdrv td (u * twopow L) s ((u * twopow L) + q) = rhCenter s q := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_outside_cone_eq_rhCenter td (u * twopow L) s ((u * twopow L) + q) (by omega),
      show (u * twopow L) + s = s + u * twopow L by omega]
  exact rhCenter_dyadic_row_scale_eq s L u q hsL

/-! ### Batch 78: Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift & Shifted-Initial-Row `rdrv td (t + u * 2^L)` Refutations of `CenterPeriodic` (`kit [33]`, 9.1462–9.1476) -/

/-- **Time-Shifted Drive-Independent Evolution of `rdrv td (u * 2^L) (t + s)` to `lhCenter (t + s) d` (`rdrv_dyadic_exact_row_time_shift_left_eq`, 9.1462, `kit [33]`)**:
    for all `td, t, L, u, d, s ∈ ℕ` with `1 ≤ u` and `(t + s) + d ≤ L`, `rdrv td (u * 2^L) (t + s) ((u * 2^L) - d) = lhCenter (t + s) d`! -/
theorem rdrv_dyadic_exact_row_time_shift_left_eq (td t L u d s : Nat)
    (hu : 1 ≤ u) (htsdL : (t + s) + d ≤ L) :
    rdrv td (u * twopow L) (t + s) ((u * twopow L) - d) = lhCenter (t + s) d :=
  rdrv_dyadic_exact_row_shift_left_eq td L u d (t + s) hu htsdL

/-- **Time-Shifted Drive-Independent Evolution of `rdrv td (u * 2^L) (t + s)` to `rhCenter (t + s) q` (`rdrv_dyadic_exact_row_time_shift_right_eq`, 9.1463, `kit [33]`)**:
    for all `td, t, L, u, q, s ∈ ℕ` with `1 ≤ u` and `t + s ≤ L`, `rdrv td (u * 2^L) (t + s) ((u * 2^L) + q) = rhCenter (t + s) q`! -/
theorem rdrv_dyadic_exact_row_time_shift_right_eq (td t L u q s : Nat)
    (hu : 1 ≤ u) (htsL : t + s ≤ L) :
    rdrv td (u * twopow L) (t + s) ((u * twopow L) + q) = rhCenter (t + s) q :=
  rdrv_dyadic_exact_row_shift_right_eq td L u q (t + s) hu htsL

/-- **Pullback of `LhColAgree t Q d S` from Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift Agreement (`lhColAgree_of_rdrv_dyadic_exact_row_step_agree`, 9.1464, `kit [33]`)**:
    for all `td, t, Q, L, u, d, S ∈ ℕ` with `1 ≤ u` and `((t + S) + Q) + d ≤ L`, if `∀ s ≤ S, rdrv td (u * 2^L) ((t + s) + Q) ((u * 2^L) - d) = rdrv td (u * 2^L) (t + s) ((u * 2^L) - d)`, then `LhColAgree t Q d S`! -/
theorem lhColAgree_of_rdrv_dyadic_exact_row_step_agree (td t Q L u d S : Nat)
    (hu : 1 ≤ u) (hL : ((t + S) + Q) + d ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (u * twopow L) ((t + s) + Q) ((u * twopow L) - d) =
        rdrv td (u * twopow L) (t + s) ((u * twopow L) - d)) :
    LhColAgree t Q d S := by
  intro s hs
  have h := hag s hs
  rwa [rdrv_dyadic_exact_row_shift_left_eq td L u d ((t + s) + Q) hu (by omega),
       rdrv_dyadic_exact_row_shift_left_eq td L u d (t + s) hu (by omega)] at h

/-- **Pullback of `LhColAgree t Q 1 S` from Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift Agreement at `(u * 2^L) - 1` (`lhColAgree_one_of_rdrv_dyadic_exact_row_step_agree`, 9.1465, `kit [33]`)**:
    for all `td, t, Q, L, u, S ∈ ℕ` with `1 ≤ u` and `((t + S) + Q) + 1 ≤ L`, if `∀ s ≤ S, rdrv td (u * 2^L) ((t + s) + Q) ((u * 2^L) - 1) = rdrv td (u * 2^L) (t + s) ((u * 2^L) - 1)`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_rdrv_dyadic_exact_row_step_agree (td t Q L u S : Nat)
    (hu : 1 ≤ u) (hL : ((t + S) + Q) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (u * twopow L) ((t + s) + Q) ((u * twopow L) - 1) =
        rdrv td (u * twopow L) (t + s) ((u * twopow L) - 1)) :
    LhColAgree t Q 1 S :=
  lhColAgree_of_rdrv_dyadic_exact_row_step_agree td t Q L u 1 S hu hL hag

/-- **Producing `maskparity · 0` Agreement from Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift Agreement (`periodic_maskparity_zero_agree_of_rdrv_dyadic_exact_row_step_agree`, 9.1466, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `td, m, t, L, u, S, s ∈ ℕ` with `T ≤ t`, `1 ≤ u`, `((t + S) + m * P) + 1 ≤ L`, and `s ≤ S`, if `∀ j ≤ S, rdrv td (u * 2^L) ((t + j) + m * P) ((u * 2^L) - 1) = rdrv td (u * 2^L) (t + j) ((u * 2^L) - 1)`, then `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rdrv_dyadic_exact_row_step_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td m t L u S s : Nat) (ht : T ≤ t) (hu : 1 ≤ u)
    (hL : ((t + S) + m * P) + 1 ≤ L)
    (hag : ∀ j : Nat, j ≤ S →
      rdrv td (u * twopow L) ((t + j) + m * P) ((u * twopow L) - 1) =
        rdrv td (u * twopow L) (t + j) ((u * twopow L) - 1))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlh := lhColAgree_one_of_rdrv_dyadic_exact_row_step_agree td t (m * P) L u S hu hL hag s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlh

/-- **Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_rdrv_dyadic_exact_row_step_agree_at_zero_diag_doubles`, 9.1467, `kit [33]`)**:
    for all `T, P, td, m, z, p, L, u, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - m * P) (z + (p + 1))`, `p + 3 * (m * P) ≤ S + 1`, `1 ≤ u`, and `(((z + (p + 1)) + S) + m * P) + 1 ≤ L`, if `∀ s ≤ S, rdrv td (u * 2^L) (((z + (p + 1)) + s) + m * P) ((u * 2^L) - 1) = rdrv td (u * 2^L) ((z + (p + 1)) + s) ((u * 2^L) - 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_exact_row_step_agree_at_zero_diag_doubles
    (T P td m z p L u S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hu : 1 ≤ u) (hL : (((z + (p + 1)) + S) + m * P) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (u * twopow L) (((z + (p + 1)) + s) + m * P) ((u * twopow L) - 1) =
        rdrv td (u * twopow L) ((z + (p + 1)) + s) ((u * twopow L) - 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_dyadic_exact_row_step_agree
    T P hP hper td m (z + (p + 1)) L u S s ht hu hL hag hs

/-- **Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rdrv_dyadic_exact_row_step_agree_twopow`, 9.1468, `kit [33]`)**:
    for all `T, P, td, m, t, k, L, u, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = 2^k`, `2^k ≤ S + 1`, `1 ≤ u`, and `((t + S) + m * P) + 1 ≤ L`, if `∀ s ≤ S, rdrv td (u * 2^L) ((t + s) + m * P) ((u * 2^L) - 1) = rdrv td (u * 2^L) (t + s) ((u * 2^L) - 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_exact_row_step_agree_twopow
    (T P td m t k L u S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hL : ((t + S) + m * P) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (u * twopow L) ((t + s) + m * P) ((u * twopow L) - 1) =
        rdrv td (u * twopow L) (t + s) ((u * twopow L) - 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_dyadic_exact_row_step_agree
    T P hP hper td m t L u S s ht hu hL hag hs

/-- **Same-Row, Same-Drive `rdrv td (u * 2^L)` Step-Shift Zero-Diagonal Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rdrv_dyadic_exact_row_step_agree_at_zero_diag_pair`, 9.1469, `kit [33]`)**:
    for all `T, P, td, m, z, k, L, u, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + m * P) ((z + m * P) + 2^k)`, `2^k ≤ S + 1`, `1 ≤ u`, and `(((z + 2^k) + S) + m * P) + 1 ≤ L`, if `∀ s ≤ S, rdrv td (u * 2^L) (((z + 2^k) + s) + m * P) ((u * 2^L) - 1) = rdrv td (u * 2^L) ((z + 2^k) + s) ((u * 2^L) - 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_exact_row_step_agree_at_zero_diag_pair
    (T P td m z k L u S : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hL : (((z + twopow k) + S) + m * P) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (u * twopow L) (((z + twopow k) + s) + m * P) ((u * twopow L) - 1) =
        rdrv td (u * twopow L) ((z + twopow k) + s) ((u * twopow L) - 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_dyadic_exact_row_step_agree
    T P hP hper td m (z + twopow k) L u S s ht hu hL hag hs

/-- **Restarted `rdrv td (t + u * 2^L) s` Left Evolution to `lhCenter (t + s) d` (`rdrv_dyadic_shifted_init_left_eq_lhCenter`, 9.1470, `kit [33]`)**:
    for all `td, t, L, u, d, s ∈ ℕ` with `1 ≤ u` and `(t + s) + d ≤ L`, `rdrv td (t + u * 2^L) s ((u * 2^L) - d) = lhCenter (t + s) d`! -/
theorem rdrv_dyadic_shifted_init_left_eq_lhCenter (td t L u d s : Nat)
    (hu : 1 ≤ u) (htsdL : (t + s) + d ≤ L) :
    rdrv td (t + u * twopow L) s ((u * twopow L) - d) = lhCenter (t + s) d := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_outside_cone_eq_rhCenter td (t + u * twopow L) s ((u * twopow L) - d) (by omega)]
  exact rhCenter_dyadic_sub_shift_eq_lhCenter t L u d s hu htsdL

/-- **Restarted `rdrv td (t + u * 2^L) s` Right Evolution to `rhCenter (t + s) q` (`rdrv_dyadic_shifted_init_right_eq_rhCenter`, 9.1471, `kit [33]`)**:
    for all `td, t, L, u, q, s ∈ ℕ` with `1 ≤ u` and `t + s ≤ L`, `rdrv td (t + u * 2^L) s ((u * 2^L) + q) = rhCenter (t + s) q`! -/
theorem rdrv_dyadic_shifted_init_right_eq_rhCenter (td t L u q s : Nat)
    (hu : 1 ≤ u) (htsL : t + s ≤ L) :
    rdrv td (t + u * twopow L) s ((u * twopow L) + q) = rhCenter (t + s) q := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_outside_cone_eq_rhCenter td (t + u * twopow L) s ((u * twopow L) + q) (by omega),
      show (t + u * twopow L) + s = (t + s) + u * twopow L by omega]
  exact rhCenter_dyadic_row_scale_eq (t + s) L u q htsL

/-- **Pullback of `LhColAgree t Q d S` from Shifted-Initial-Row `rdrv` Agreement at `(u * 2^L) - d` (`lhColAgree_of_rdrv_dyadic_shifted_init_agree`, 9.1472, `kit [33]`)**:
    for all `td, t, Q, L, u, d, S ∈ ℕ` with `1 ≤ u` and `((t + S) + Q) + d ≤ L`, if `∀ s ≤ S, rdrv td ((t + u * 2^L) + Q) s ((u * 2^L) - d) = rdrv td (t + u * 2^L) s ((u * 2^L) - d)`, then `LhColAgree t Q d S`! -/
theorem lhColAgree_of_rdrv_dyadic_shifted_init_agree (td t Q L u d S : Nat)
    (hu : 1 ≤ u) (hL : ((t + S) + Q) + d ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td ((t + u * twopow L) + Q) s ((u * twopow L) - d) =
        rdrv td (t + u * twopow L) s ((u * twopow L) - d)) :
    LhColAgree t Q d S := by
  intro s hs
  have h := hag s hs
  rwa [show (t + u * twopow L) + Q = (t + Q) + u * twopow L by omega,
       rdrv_dyadic_shifted_init_left_eq_lhCenter td (t + Q) L u d s hu (by omega),
       rdrv_dyadic_shifted_init_left_eq_lhCenter td t L u d s hu (by omega),
       show (t + Q) + s = (t + s) + Q by omega] at h

/-- **Pullback of `LhColAgree t Q 1 S` from Shifted-Initial-Row `rdrv` Agreement at `(u * 2^L) - 1` (`lhColAgree_one_of_rdrv_dyadic_shifted_init_agree`, 9.1473, `kit [33]`)**:
    for all `td, t, Q, L, u, S ∈ ℕ` with `1 ≤ u` and `((t + S) + Q) + 1 ≤ L`, if `∀ s ≤ S, rdrv td ((t + u * 2^L) + Q) s ((u * 2^L) - 1) = rdrv td (t + u * 2^L) s ((u * 2^L) - 1)`, then `LhColAgree t Q 1 S`! -/
theorem lhColAgree_one_of_rdrv_dyadic_shifted_init_agree (td t Q L u S : Nat)
    (hu : 1 ≤ u) (hL : ((t + S) + Q) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td ((t + u * twopow L) + Q) s ((u * twopow L) - 1) =
        rdrv td (t + u * twopow L) s ((u * twopow L) - 1)) :
    LhColAgree t Q 1 S :=
  lhColAgree_of_rdrv_dyadic_shifted_init_agree td t Q L u 1 S hu hL hag

/-- **Shifted-Initial-Row `rdrv` Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_rdrv_dyadic_shifted_init_agree_at_zero_diag_doubles`, 9.1474, `kit [33]`)**:
    for all `T, P, td, m, z, p, L, u, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ z + (p + 1)`, `IsZeroDiag z`, `DoublesAt (m * P) z`, `SettledBy (z + 1) (z + (p + 1))`, `SettledBy ((z + 1) - m * P) (z + (p + 1))`, `p + 3 * (m * P) ≤ S + 1`, `1 ≤ u`, and `(((z + (p + 1)) + S) + m * P) + 1 ≤ L`, if `∀ s ≤ S, rdrv td (((z + (p + 1)) + u * 2^L) + m * P) s ((u * 2^L) - 1) = rdrv td ((z + (p + 1)) + u * 2^L) s ((u * 2^L) - 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_shifted_init_agree_at_zero_diag_doubles
    (T P td m z p L u S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hu : 1 ≤ u) (hL : (((z + (p + 1)) + S) + m * P) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (((z + (p + 1)) + u * twopow L) + m * P) s ((u * twopow L) - 1) =
        rdrv td ((z + (p + 1)) + u * twopow L) s ((u * twopow L) - 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hcol := lhColAgree_one_of_rdrv_dyadic_shifted_init_agree td (z + (p + 1)) (m * P) L u S hu hL hag
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m ((z + (p + 1)) + s) (by omega) (hcol s hs)

/-- **Shifted-Initial-Row `rdrv` Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rdrv_dyadic_shifted_init_agree_twopow`, 9.1475, `kit [33]`)**:
    for all `T, P, td, m, t, k, L, u, S ∈ ℕ` with `0 < P`, `0 < m`, `T ≤ t`, `t + m * P = 2^k`, `2^k ≤ S + 1`, `1 ≤ u`, and `((t + S) + m * P) + 1 ≤ L`, if `∀ s ≤ S, rdrv td ((t + u * 2^L) + m * P) s ((u * 2^L) - 1) = rdrv td (t + u * 2^L) s ((u * 2^L) - 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_shifted_init_agree_twopow
    (T P td m t k L u S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ t) (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hL : ((t + S) + m * P) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td ((t + u * twopow L) + m * P) s ((u * twopow L) - 1) =
        rdrv td (t + u * twopow L) s ((u * twopow L) - 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hcol := lhColAgree_one_of_rdrv_dyadic_shifted_init_agree td t (m * P) L u S hu hL hag
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) (hcol s hs)

/-- **Shifted-Initial-Row `rdrv` Zero-Diagonal Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rdrv_dyadic_shifted_init_agree_at_zero_diag_pair`, 9.1476, `kit [33]`)**:
    for all `T, P, td, m, z, k, L, u, S ∈ ℕ` with `0 < P`, `IsZeroDiag z`, `2 ≤ z + m * P`, `IsZeroDiag ((z + m * P) - 2)`, `T ≤ z + 2^k`, `SettledBy z (z + 2^k)`, `SettledBy (z + m * P) ((z + m * P) + 2^k)`, `2^k ≤ S + 1`, `1 ≤ u`, and `(((z + 2^k) + S) + m * P) + 1 ≤ L`, if `∀ s ≤ S, rdrv td (((z + 2^k) + u * 2^L) + m * P) s ((u * 2^L) - 1) = rdrv td ((z + 2^k) + u * 2^L) s ((u * 2^L) - 1)`, then `¬ CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_shifted_init_agree_at_zero_diag_pair
    (T P td m z k L u S : Nat) (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hL : (((z + twopow k) + S) + m * P) + 1 ≤ L)
    (hag : ∀ s : Nat, s ≤ S →
      rdrv td (((z + twopow k) + u * twopow L) + m * P) s ((u * twopow L) - 1) =
        rdrv td ((z + twopow k) + u * twopow L) s ((u * twopow L) - 1)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hcol := lhColAgree_one_of_rdrv_dyadic_shifted_init_agree td (z + twopow k) (m * P) L u S hu hL hag
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m ((z + twopow k) + s) (by omega) (hcol s hs)

/-! ### Batch 79: Anchored Left-Half Step Contraction (`periodic_lhBandAgree_one_step`, `periodic_lhColAgree_one_of_lhBandAgree_one`) & Unilateral Left-Corridor Pullbacks (`kit [33]`, 9.1477–9.1491) -/

/-- **Anchored One-Step Left-Half Contraction under `CenterPeriodic` (`periodic_lhBandAgree_one_step`, 9.1477, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), `LhBandAgree t (m * P) 1 (L + 1)` implies `LhBandAgree (t + 1) (m * P) 1 L` (losing only `1` cell of width per step instead of `2`, with the inner endpoint anchored at `1`)! -/
theorem periodic_lhBandAgree_one_step
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : LhBandAgree t (m * P) 1 (L + 1)) :
    LhBandAgree (t + 1) (m * P) 1 L := by
  have h0 := periodic_lhBandAgree_zero_of_one T P hP hper m t (L + 1) ht h
  have h1 := lhBandAgree_step t (m * P) 0 L h0
  simpa using h1

/-- **Anchored Multi-Step Left-Half Contraction under `CenterPeriodic` (`periodic_lhBandAgree_one_steps`, 9.1478, `kit [33]`)**:
    by induction on `s : Nat`, under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), `LhBandAgree t (m * P) 1 (L + s)` implies `LhBandAgree (t + s) (m * P) 1 L`! -/
theorem periodic_lhBandAgree_one_steps
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L s : Nat) (ht : T ≤ t)
    (h : LhBandAgree t (m * P) 1 (L + s)) :
    LhBandAgree (t + s) (m * P) 1 L := by
  induction s generalizing t L with
  | zero =>
    simpa using h
  | succ s ih =>
    have h' : LhBandAgree t (m * P) 1 ((L + s) + 1) := by
      intro i hi
      exact h i (by omega)
    have h1 := periodic_lhBandAgree_one_step T P hP hper m t (L + s) ht h'
    have h2 := ih (t + 1) L (by omega) h1
    rwa [show (t + 1) + s = t + (s + 1) by omega] at h2

/-- **Pointwise Left Column `-1` Agreement from `LhBandAgree t (m * P) 1 S` under `CenterPeriodic` (`periodic_lhCenter_one_agree_of_lhBandAgree_one`, 9.1479, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), `LhBandAgree t (m * P) 1 S` alone implies `lhCenter ((t + s) + m * P) 1 = lhCenter (t + s) 1` for every `s ≤ S`! -/
theorem periodic_lhCenter_one_agree_of_lhBandAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t)
    (h : LhBandAgree t (m * P) 1 S)
    (hs : s ≤ S) :
    lhCenter ((t + s) + m * P) 1 = lhCenter (t + s) 1 := by
  have hsub : LhBandAgree t (m * P) 1 ((S - s) + s) := by
    intro i hi
    exact h i (by omega)
  have hstep := periodic_lhBandAgree_one_steps T P hP hper m t (S - s) s ht hsub
  have h0 := hstep 0 (by omega)
  simpa using h0

/-- **Pure Left-Half Termination of `LhColAgree` under `CenterPeriodic` (`periodic_lhColAgree_one_of_lhBandAgree_one`, 9.1480, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), `LhBandAgree t (m * P) 1 S` at a single row `t` of width `S` ALONE (with zero assumptions on the right half!) implies `LhColAgree t (m * P) 1 S`! -/
theorem periodic_lhColAgree_one_of_lhBandAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h : LhBandAgree t (m * P) 1 S) :
    LhColAgree t (m * P) 1 S := by
  intro s hs
  exact periodic_lhCenter_one_agree_of_lhBandAgree_one T P hP hper m t S s ht h hs

/-- **`maskparity · 0` Horizon Agreement from `LhBandAgree t (m * P) 1 S` under `CenterPeriodic` (`periodic_maskparity_zero_agree_of_lhBandAgree_one`, 9.1481, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), `LhBandAgree t (m * P) 1 S` implies `maskparity ((t + s) + m * P) 0 = maskparity (t + s) 0` for all `s ≤ S`! -/
theorem periodic_maskparity_zero_agree_of_lhBandAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S s : Nat) (ht : T ≤ t)
    (h : LhBandAgree t (m * P) 1 S)
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + m * P) 0 = Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlcol := periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m t S ht h s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper m (t + s) (by omega) hlcol

/-- **Doubling-Zero-Diagonal Refutation of `CenterPeriodic` from `LhBandAgree · 1 S` Alone (`not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles`, 9.1482, `kit [33]`)**:
    if `IsZeroDiag z` and `DoublesAt (m * P) z` hold with `p + 3 * (m * P) ≤ S + 1`, then `LhBandAgree (z + (p + 1)) (m * P) 1 S` alone refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    (T P m z p S : Nat)
    (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h : LhBandAgree (z + (p + 1)) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P m z p S hP hm ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper m (z + (p + 1)) S s ht h hs

/-- **Dyadic-Window (`t + m * P = 2^k`) Refutation of `CenterPeriodic` from `LhBandAgree · 1 S` Alone (`not_centerPeriodic_of_lhBandAgree_one_twopow`, 9.1483, `kit [33]`)**:
    when `t + m * P = 2^k` and `2^k ≤ S + 1`, `LhBandAgree t (m * P) 1 S` alone refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_twopow
    (T P m t k S : Nat)
    (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (h : LhBandAgree t (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P m t k S hP hm ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper m t S s ht h hs

/-- **Zero-Diagonal-Pair Refutation of `CenterPeriodic` from `LhBandAgree · 1 S` Alone (`not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_pair`, 9.1484, `kit [33]`)**:
    for a zero-diagonal pair `(z, (z + m * P) - 2)` with `2^k ≤ S + 1`, `LhBandAgree (z + 2^k) (m * P) 1 S` alone refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_pair
    (T P m z k S : Nat)
    (hP : 0 < P)
    (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (h : LhBandAgree (z + twopow k) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper m (z + twopow k) S s ht h hs

/-- **Pullback of `LhBandAgree t Q 1 S` from `rhCenter` Agreement on the Left Corridor `[v * 2^K - (S + 1), v * 2^K - 1]` (`lhBandAgree_one_of_rhCenter_dyadic_left_corridor_agree`, 9.1485, `kit [33]`)**:
    for `1 ≤ v` and `(t + Q) + (S + 1) ≤ K`, agreement of `rhCenter` between rows `t + v * 2^K` and `(t + v * 2^K) + Q` on the left corridor `v * 2^K - (1 + i)` (`i ≤ S`) implies `LhBandAgree t Q 1 S`! -/
theorem lhBandAgree_one_of_rhCenter_dyadic_left_corridor_agree
    (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : (t + Q) + (S + 1) ≤ K)
    (hag : ∀ i : Nat, i ≤ S →
      rhCenter ((t + v * twopow K) + Q) (v * twopow K - (1 + i)) =
      rhCenter (t + v * twopow K) (v * twopow K - (1 + i))) :
    LhBandAgree t Q 1 S := by
  intro i hi
  have h1 := rhCenter_dyadic_sub_shift_eq_lhCenter (t + Q) K v (1 + i) 0 hv (by omega)
  have h2 := rhCenter_dyadic_sub_shift_eq_lhCenter t K v (1 + i) 0 hv (by omega)
  simp only [Nat.add_zero] at h1 h2
  rw [show (t + Q) + v * twopow K = (t + v * twopow K) + Q by omega] at h1
  rw [← h1, ← h2]
  exact hag i hi

/-- **Pullback of `LhBandAgree t Q 1 S` from `RhBandAgree (t + v * 2^K) Q (v * 2^K - (S + 1)) S` (`lhBandAgree_one_of_rhBandAgree_dyadic_left_corridor`, 9.1486, `kit [33]`)**:
    for `1 ≤ v` and `(t + Q) + (S + 1) ≤ K`, `RhBandAgree (t + v * 2^K) Q (v * 2^K - (S + 1)) S` (width `S`, purely to the left of `v * 2^K`) implies `LhBandAgree t Q 1 S`! -/
theorem lhBandAgree_one_of_rhBandAgree_dyadic_left_corridor
    (t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : (t + Q) + (S + 1) ≤ K)
    (hrh : RhBandAgree (t + v * twopow K) Q (v * twopow K - (S + 1)) S) :
    LhBandAgree t Q 1 S := by
  apply lhBandAgree_one_of_rhCenter_dyadic_left_corridor_agree t Q K v S hv hK
  intro i hi
  have hlt := twopow_gt_self K
  have hmul : twopow K ≤ v * twopow K := by
    have h := Nat.mul_le_mul_right (twopow K) hv
    omega
  have heq := hrh (S - i) (by omega)
  rwa [show (v * twopow K - (S + 1)) + (S - i) = v * twopow K - (1 + i) by omega] at heq

/-- **Derivation of `LhColAgree t (m * P) 1 S` from `RhBandAgree` on the Left Corridor `[v * 2^K - (S + 1), v * 2^K - 1]` under `CenterPeriodic` (`periodic_lhColAgree_one_of_rhBandAgree_dyadic_left_corridor`, 9.1487, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), for `1 ≤ v` and `(t + m * P) + (S + 1) ≤ K`, `RhBandAgree (t + v * 2^K) (m * P) (v * 2^K - (S + 1)) S` (width `S`, purely on the left of `v * 2^K`) implies `LhColAgree t (m * P) 1 S`! -/
theorem periodic_lhColAgree_one_of_rhBandAgree_dyadic_left_corridor
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t K v S : Nat) (ht : T ≤ t)
    (hv : 1 ≤ v) (hK : (t + m * P) + (S + 1) ≤ K)
    (hrh : RhBandAgree (t + v * twopow K) (m * P) (v * twopow K - (S + 1)) S) :
    LhColAgree t (m * P) 1 S := by
  have hlh := lhBandAgree_one_of_rhBandAgree_dyadic_left_corridor t (m * P) K v S hv hK hrh
  exact periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m t S ht hlh

/-- **Doubling-Zero-Diagonal Refutation of `CenterPeriodic` from Left-Corridor `RhBandAgree` (`not_centerPeriodic_of_rhBandAgree_dyadic_left_corridor_at_zero_diag_doubles`, 9.1488, `kit [33]`)**:
    if `IsZeroDiag z` and `DoublesAt (m * P) z` hold with `p + 3 * (m * P) ≤ S + 1`, then `RhBandAgree ((z + (p + 1)) + v * 2^K) (m * P) (v * 2^K - (S + 1)) S` (width `S`, purely to the left of `v * 2^K`) refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_left_corridor_at_zero_diag_doubles
    (T P m z p K v S : Nat)
    (hP : 0 < P) (hm : 0 < m) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z)
    (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + (p + 1)) + m * P) + (S + 1) ≤ K)
    (hrh : RhBandAgree ((z + (p + 1)) + v * twopow K) (m * P) (v * twopow K - (S + 1)) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hlh := lhBandAgree_one_of_rhBandAgree_dyadic_left_corridor (z + (p + 1)) (m * P) K v S hv hK hrh
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hset2 hS hlh

/-- **Dyadic-Window (`t + m * P = 2^k`) Refutation of `CenterPeriodic` from Left-Corridor `RhBandAgree` (`not_centerPeriodic_of_rhBandAgree_dyadic_left_corridor_twopow`, 9.1489, `kit [33]`)**:
    when `t + m * P = 2^k` and `2^k ≤ S + 1`, `RhBandAgree (t + v * 2^K) (m * P) (v * 2^K - (S + 1)) S` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_left_corridor_twopow
    (T P m t k K v S : Nat)
    (hP : 0 < P) (hm : 0 < m) (ht : T ≤ t)
    (htm : t + m * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hv : 1 ≤ v) (hK : (t + m * P) + (S + 1) ≤ K)
    (hrh : RhBandAgree (t + v * twopow K) (m * P) (v * twopow K - (S + 1)) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hlh := lhBandAgree_one_of_rhBandAgree_dyadic_left_corridor t (m * P) K v S hv hK hrh
  exact not_centerPeriodic_of_lhBandAgree_one_twopow T P m t k S hP hm ht htm hS hlh

/-- **Zero-Diagonal-Pair Refutation of `CenterPeriodic` from Left-Corridor `RhBandAgree` (`not_centerPeriodic_of_rhBandAgree_dyadic_left_corridor_at_zero_diag_pair`, 9.1490, `kit [33]`)**:
    for a zero-diagonal pair `(z, (z + m * P) - 2)` with `2^k ≤ S + 1`, `RhBandAgree ((z + 2^k) + v * 2^K) (m * P) (v * 2^K - (S + 1)) S` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rhBandAgree_dyadic_left_corridor_at_zero_diag_pair
    (T P m z k K v S : Nat)
    (hP : 0 < P)
    (hz0 : IsZeroDiag z)
    (h2 : 2 ≤ z + m * P)
    (hz1 : IsZeroDiag ((z + m * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + m * P) ((z + m * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + twopow k) + m * P) + (S + 1) ≤ K)
    (hrh : RhBandAgree ((z + twopow k) + v * twopow K) (m * P) (v * twopow K - (S + 1)) S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hlh := lhBandAgree_one_of_rhBandAgree_dyadic_left_corridor (z + twopow k) (m * P) K v S hv hK hrh
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_pair
    T P m z k S hP hz0 h2 hz1 ht hset0 hset1 hS hlh

/-- **Pullback of `LhBandAgree t Q 1 S` from `rdrv td (v * 2^K)` Left-Corridor Agreement (`lhBandAgree_one_of_rdrv_dyadic_exact_row_left_corridor_agree`, 9.1491, `kit [33]`)**:
    for `1 ≤ v` and `(t + Q) + (S + 1) ≤ K`, agreement of `rdrv td (v * 2^K) (t + Q)` and `rdrv td (v * 2^K) t` on the left corridor `v * 2^K - (1 + i)` (`i ≤ S`) implies `LhBandAgree t Q 1 S`! -/
theorem lhBandAgree_one_of_rdrv_dyadic_exact_row_left_corridor_agree
    (td t Q K v S : Nat)
    (hv : 1 ≤ v) (hK : (t + Q) + (S + 1) ≤ K)
    (hag : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) (t + Q) (v * twopow K - (1 + i)) =
      rdrv td (v * twopow K) t (v * twopow K - (1 + i))) :
    LhBandAgree t Q 1 S := by
  intro i hi
  have h1 := rdrv_dyadic_exact_row_shift_left_eq td K v (1 + i) (t + Q) hv (by omega)
  have h2 := rdrv_dyadic_exact_row_shift_left_eq td K v (1 + i) t hv (by omega)
  rw [← h1, ← h2]
  exact hag i hi

end Rule30UOR.Interfaces
