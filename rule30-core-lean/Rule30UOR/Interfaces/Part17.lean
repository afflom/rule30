module

public import Rule30UOR.Interfaces.Part16

/-!
# `Rule30UOR.Interfaces`, part 17

* Batch 80: Unilateral Left-Corridor Two-Scale Single-Row Spatial Shift Reduction & Pure-Drive `rdrv td (u * 2^L)` Left-Corridor Refutations of `CenterPeriodic` (`kit [33]`, 9.1492–9.1506)
* Batch 81: Unconditional Dyadic-Multiple Diagonal-Shift Periodicity & Direct Left-Half Single-Row Spatial Shift Reduction at t = z + 1 (9.1507–9.1521)
* Batch 82: General-p Prefix/Tail Decomposition at Doubling Zero Diagonals & Single-Scale Dyadic Embedding of Single-Row Left-Half Spatial Agreement in rhCenter and rdrv (9.1522–9.1536)
* Batch 83: Late-Scale (t + 2^k, p + 2^k) Diagonal-Shift Periodicity & Scale-Independent Tail Horizon 3mP Refutations (9.1537–9.1551)
* Batch 84: Monotone Settlement Bound (`settleBound` / `SettledUpTo`), Settlement-Hypothesis-Free Prefix/Tail Reductions, and Single-Row Prefix+Tail Refutations of `CenterPeriodic` (9.1552–9.1566)
* Batch 85: Single-Time Left-Band Refutation at Doubling Zero Diagonals, Unconditional Single-Row Spatial Non-Periodicity, and Signed Single-Row Characterizations on `z + 1`, `z + 2`, `z + 3` (9.1567–9.1581)
* Batch 86: Audit Theorems — Unsatisfiability of the Left-Band Engine Hypotheses and Exact Equivalence of the Engine Input with Problem 1 (9.1582–9.1587)
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

/-! ### Batch 80: Unilateral Left-Corridor Two-Scale Single-Row Spatial Shift Reduction & Pure-Drive `rdrv td (u * 2^L)` Left-Corridor Refutations of `CenterPeriodic` (`kit [33]`, 9.1492–9.1506) -/

/-- **Two-Scale Single-Row Left-Corridor Spatial Shift Theorem for `LhBandAgree t (w * 2^K) 1 S` (`lhBandAgree_one_of_two_scale_single_row_left_corridor_spatial_agree`, 9.1492, `kit [33]`)**:
    for all `t, K, L, u, w, S ∈ ℕ` with `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + w * 2^K) + 1 ≤ L`, and `K ≤ L`, if at the SINGLE row `(t + u * 2^L) + w * 2^K` the left corridor `[u * 2^L - (S + 1), u * 2^L - 1]` of width `S` agrees with its spatial shift by `w * 2^K`, then `LhBandAgree t (w * 2^K) 1 S`! -/
theorem lhBandAgree_one_of_two_scale_single_row_left_corridor_spatial_agree
    (t K L u w S : Nat)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + w * twopow K) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter ((t + u * twopow L) + w * twopow K) ((u * twopow L) - (1 + i)) =
        rhCenter ((t + u * twopow L) + w * twopow K) (((u * twopow L) + w * twopow K) - (1 + i))) :
    LhBandAgree t (w * twopow K) 1 S := by
  intro i hi
  have h1 := rhCenter_dyadic_sub_shift_eq_lhCenter (t + w * twopow K) L u (1 + i) 0 hu (by omega)
  simp only [Nat.add_zero] at h1
  rw [show (t + w * twopow K) + u * twopow L = (t + u * twopow L) + w * twopow K by omega] at h1
  have h2 := rhCenter_two_scale_row_left_eq_lhCenter t K L u w (1 + i) hu hKL (by omega)
  rw [← h1, ← h2]
  exact hspat i hi

/-- **Dyadic-Multiple Period (`(c * 2^K) * P`) Single-Row Left-Corridor Spatial Shift Theorem for `LhBandAgree t ((c * 2^K) * P) 1 S` (`lhBandAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree`, 9.1493, `kit [33]`)**:
    for all `t, P, c, K, L, u, S ∈ ℕ` with `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + (c * 2^K) * P) + 1 ≤ L`, and `K ≤ L`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at the single row `(t + u * 2^L) + (c * 2^K) * P` implies `LhBandAgree t ((c * 2^K) * P) 1 S`! -/
theorem lhBandAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (t P c K L u S : Nat)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    LhBandAgree t ((c * twopow K) * P) 1 S := by
  have hmul : (c * twopow K) * P = (c * P) * twopow K := Nat.mul_right_comm c (twopow K) P
  rw [hmul] at hL hspat ⊢
  exact lhBandAgree_one_of_two_scale_single_row_left_corridor_spatial_agree
    t K L u (c * P) S hu hK hL hKL hspat

/-- **Derivation of `LhColAgree t ((c * 2^K) * P) 1 S` from Single-Row Left-Corridor Spatial Shift Agreement under `CenterPeriodic` (`periodic_lhColAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree`, 9.1494, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), spatial shift agreement by `(c * 2^K) * P` ONLY on the left corridor `[u * 2^L - (S + 1), u * 2^L - 1]` of width `S` at the single row `(t + u * 2^L) + (c * 2^K) * P` implies `LhColAgree t ((c * 2^K) * P) 1 S`! -/
theorem periodic_lhColAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (c t K L u S : Nat) (ht : T ≤ t)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    LhColAgree t ((c * twopow K) * P) 1 S := by
  have hlh := lhBandAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    t P c K L u S hu hK hL hKL hspat
  exact periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper (c * twopow K) t S ht hlh

/-- **Producing `maskparity · 0` Agreement from Single-Row Left-Corridor Spatial Shift Agreement under `CenterPeriodic` (`periodic_maskparity_zero_agree_of_dyadic_mul_period_single_row_left_corridor_spatial_agree`, 9.1495, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), for `s ≤ S`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at the single row `(t + u * 2^L) + (c * 2^K) * P` implies `maskparity ((t + s) + (c * 2^K) * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (c t K L u S s : Nat) (ht : T ≤ t)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + (c * twopow K) * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlcol := periodic_lhColAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    T P hP hper c t K L u S ht hu hK hL hKL hspat s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper (c * twopow K) (t + s) (by omega) hlcol

/-- **Single-Row Left-Corridor Spatial Shift Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_doubles`, 9.1496, `kit [33]`)**:
    spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at the single row `((z + (p + 1)) + u * 2^L) + (c * 2^K) * P` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_doubles
    (T P c z p K L u S : Nat)
    (hP : 0 < P) (hc : 0 < c) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - (c * twopow K) * P) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : ((z + (p + 1)) + S) + 1 ≤ K)
    (hL : (((z + (p + 1)) + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hgt : K < twopow K := twopow_gt_self K
  have hpos : 0 < c * twopow K := Nat.mul_pos hc (by omega)
  have hlh := lhBandAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (z + (p + 1)) P c K L u S hu hK hL hKL hspat
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P (c * twopow K) z p S hP hpos ht hz hd hset1 hset2 hS hlh

/-- **Single-Row Left-Corridor Spatial Shift Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_dyadic_mul_period_single_row_left_corridor_spatial_agree_twopow`, 9.1497, `kit [33]`)**:
    when `t + (c * 2^K) * P = 2^k` and `2^k ≤ S + 1`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at the single row `(t + u * 2^L) + (c * 2^K) * P` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_dyadic_mul_period_single_row_left_corridor_spatial_agree_twopow
    (T P c t k K L u S : Nat)
    (hP : 0 < P) (hc : 0 < c) (ht : T ≤ t)
    (htm : t + (c * twopow K) * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter ((t + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rhCenter ((t + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hgt : K < twopow K := twopow_gt_self K
  have hpos : 0 < c * twopow K := Nat.mul_pos hc (by omega)
  have hlh := lhBandAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    t P c K L u S hu hK hL hKL hspat
  exact not_centerPeriodic_of_lhBandAgree_one_twopow
    T P (c * twopow K) t k S hP hpos ht htm hS hlh

/-- **Single-Row Left-Corridor Spatial Shift Zero-Diagonal-Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_pair`, 9.1498, `kit [33]`)**:
    for a zero-diagonal pair `(z, (z + (c * 2^K) * P) - 2)` with `2^k ≤ S + 1`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at the single row `((z + 2^k) + u * 2^L) + (c * 2^K) * P` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_pair
    (T P c z k K L u S : Nat)
    (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + (c * twopow K) * P)
    (hz1 : IsZeroDiag ((z + (c * twopow K) * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + (c * twopow K) * P) ((z + (c * twopow K) * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hK : ((z + twopow k) + S) + 1 ≤ K)
    (hL : (((z + twopow k) + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + twopow k) + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rhCenter (((z + twopow k) + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hlh := lhBandAgree_one_of_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (z + twopow k) P c K L u S hu hK hL hKL hspat
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_pair
    T P (c * twopow K) z k S hP hz0 h2 hz1 ht hset0 hset1 hS hlh

/-- **Two-Scale `rdrv td (u * 2^L)` Embedding of `lhCenter t d` at Column `(u * 2^L + w * 2^K) - d` of Step `t + w * 2^K` (`rdrv_two_scale_row_left_eq_lhCenter`, 9.1499, `kit [33]`)**:
    for all `td, t, K, L, u, w, d ∈ ℕ` with `1 ≤ u`, `K ≤ L`, `t + d ≤ K`, and `(t + w * 2^K) + d ≤ L`, `rdrv td (u * 2^L) (t + w * 2^K) ((u * 2^L + w * 2^K) - d) = lhCenter t d`! -/
theorem rdrv_two_scale_row_left_eq_lhCenter
    (td t K L u w d : Nat)
    (hu : 1 ≤ u) (hKL : K ≤ L)
    (htdK : t + d ≤ K) (htwdL : (t + w * twopow K) + d ≤ L) :
    rdrv td (u * twopow L) (t + w * twopow K) (((u * twopow L) + w * twopow K) - d) =
      lhCenter t d := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_outside_cone_eq_rhCenter td (u * twopow L) (t + w * twopow K)
        (((u * twopow L) + w * twopow K) - d) (by omega),
      show (u * twopow L) + (t + w * twopow K) = (t + u * twopow L) + w * twopow K by omega]
  exact rhCenter_two_scale_row_left_eq_lhCenter t K L u w d hu hKL htdK

/-- **Two-Scale `rdrv td (u * 2^L)` Embedding of `rhCenter t q` at Column `(u * 2^L + w * 2^K) + q` of Step `t + w * 2^K` (`rdrv_two_scale_row_right_eq_rhCenter`, 9.1500, `kit [33]`)**:
    for all `td, t, K, L, u, w, q ∈ ℕ` with `1 ≤ u`, `K ≤ L`, `t ≤ K`, and `t + w * 2^K ≤ L`, `rdrv td (u * 2^L) (t + w * 2^K) ((u * 2^L + w * 2^K) + q) = rhCenter t q`! -/
theorem rdrv_two_scale_row_right_eq_rhCenter
    (td t K L u w q : Nat)
    (hu : 1 ≤ u) (hKL : K ≤ L)
    (htK : t ≤ K) (htwL : t + w * twopow K ≤ L) :
    rdrv td (u * twopow L) (t + w * twopow K) (((u * twopow L) + w * twopow K) + q) =
      rhCenter t q := by
  have hlt : L < twopow L := twopow_gt_self L
  have hm : twopow L ≤ u * twopow L := by
    have h := Nat.mul_le_mul_right (twopow L) hu
    omega
  rw [rdrv_outside_cone_eq_rhCenter td (u * twopow L) (t + w * twopow K)
        (((u * twopow L) + w * twopow K) + q) (by omega),
      show (u * twopow L) + (t + w * twopow K) = (t + u * twopow L) + w * twopow K by omega]
  exact rhCenter_two_scale_row_right_eq_rhCenter t K L u w q hKL htK

/-- **Two-Scale Single-Step `rdrv td (u * 2^L)` Left-Corridor Spatial Shift Theorem for `LhBandAgree t (w * 2^K) 1 S` (`lhBandAgree_one_of_rdrv_two_scale_single_row_left_corridor_spatial_agree`, 9.1501, `kit [33]`)**:
    for all `td, t, K, L, u, w, S ∈ ℕ` with `1 ≤ u`, `(t + S) + 1 ≤ K`, `((t + S) + w * 2^K) + 1 ≤ L`, and `K ≤ L`, if at step `t + w * 2^K` of `rdrv td (u * 2^L)` the left corridor of width `S` agrees with its spatial shift by `w * 2^K`, then `LhBandAgree t (w * 2^K) 1 S`! -/
theorem lhBandAgree_one_of_rdrv_two_scale_single_row_left_corridor_spatial_agree
    (td t K L u w S : Nat)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + w * twopow K) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) (t + w * twopow K) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) (t + w * twopow K) (((u * twopow L) + w * twopow K) - (1 + i))) :
    LhBandAgree t (w * twopow K) 1 S := by
  intro i hi
  have h1 := rdrv_dyadic_exact_row_shift_left_eq td L u (1 + i) (t + w * twopow K) hu (by omega)
  have h2 := rdrv_two_scale_row_left_eq_lhCenter td t K L u w (1 + i) hu hKL (by omega) (by omega)
  rw [← h1, ← h2]
  exact hspat i hi

/-- **Derivation of `LhColAgree t ((c * 2^K) * P) 1 S` from Single-Step `rdrv td (u * 2^L)` Left-Corridor Spatial Shift Agreement under `CenterPeriodic` (`periodic_lhColAgree_one_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree`, 9.1502, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at step `t + (c * 2^K) * P` of `rdrv td (u * 2^L)` implies `LhColAgree t ((c * 2^K) * P) 1 S`! -/
theorem periodic_lhColAgree_one_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td c t K L u S : Nat) (ht : T ≤ t)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) (t + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) (t + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    LhColAgree t ((c * twopow K) * P) 1 S := by
  have hmul : (c * twopow K) * P = (c * P) * twopow K := Nat.mul_right_comm c (twopow K) P
  have hL' : ((t + S) + (c * P) * twopow K) + 1 ≤ L := by rwa [← hmul]
  have hspat' : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) (t + (c * P) * twopow K) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) (t + (c * P) * twopow K) (((u * twopow L) + (c * P) * twopow K) - (1 + i)) := by
    intro i hi
    simpa [hmul] using hspat i hi
  have hlh : LhBandAgree t ((c * twopow K) * P) 1 S := by
    rw [hmul]
    exact lhBandAgree_one_of_rdrv_two_scale_single_row_left_corridor_spatial_agree
      td t K L u (c * P) S hu hK hL' hKL hspat'
  exact periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper (c * twopow K) t S ht hlh

/-- **Producing `maskparity · 0` Agreement from Single-Step `rdrv td (u * 2^L)` Left-Corridor Spatial Shift Agreement under `CenterPeriodic` (`periodic_maskparity_zero_agree_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree`, 9.1503, `kit [33]`)**:
    under `CenterPeriodic T P` (`0 < P`, `T ≤ t`), for `s ≤ S`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at step `t + (c * 2^K) * P` of `rdrv td (u * 2^L)` implies `maskparity ((t + s) + (c * 2^K) * P) 0 = maskparity (t + s) 0`! -/
theorem periodic_maskparity_zero_agree_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td c t K L u S s : Nat) (ht : T ≤ t)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) (t + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) (t + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + (c * twopow K) * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  have hlcol := periodic_lhColAgree_one_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree
    T P hP hper td c t K L u S ht hu hK hL hKL hspat s hs
  exact periodic_maskparity_zero_eq_of_lhCenter_one_eq T P hP hper (c * twopow K) (t + s) (by omega) hlcol

/-- **Single-Step `rdrv td (u * 2^L)` Left-Corridor Spatial Shift Refutation of `CenterPeriodic` at a Doubling Zero Diagonal (`not_centerPeriodic_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_doubles`, 9.1504, `kit [33]`)**:
    spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at step `(z + (p + 1)) + (c * 2^K) * P` of `rdrv td (u * 2^L)` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_doubles
    (T P td c z p K L u S : Nat)
    (hP : 0 < P) (hc : 0 < c) (ht : T ≤ z + (p + 1))
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - (c * twopow K) * P) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : ((z + (p + 1)) + S) + 1 ≤ K)
    (hL : (((z + (p + 1)) + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) ((z + (p + 1)) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) ((z + (p + 1)) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hgt : K < twopow K := twopow_gt_self K
  have hpos : 0 < c * twopow K := Nat.mul_pos hc (by omega)
  refine not_centerPeriodic_of_maskparity_zero_agree_at_zero_diag_doubles_prop
    T P (c * twopow K) z p S hP hpos ht hz hd hset1 hset2 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree
    T P hP hper td c (z + (p + 1)) K L u S s ht hu hK hL hKL hspat hs

/-- **Single-Step `rdrv td (u * 2^L)` Left-Corridor Spatial Shift Dyadic-Window Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree_twopow`, 9.1505, `kit [33]`)**:
    when `t + (c * 2^K) * P = 2^k` and `2^k ≤ S + 1`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at step `t + (c * 2^K) * P` of `rdrv td (u * 2^L)` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree_twopow
    (T P td c t k K L u S : Nat)
    (hP : 0 < P) (hc : 0 < c) (ht : T ≤ t)
    (htm : t + (c * twopow K) * P = twopow k)
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hK : (t + S) + 1 ≤ K)
    (hL : ((t + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) (t + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) (t + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  have hgt : K < twopow K := twopow_gt_self K
  have hpos : 0 < c * twopow K := Nat.mul_pos hc (by omega)
  refine not_centerPeriodic_of_maskparity_zero_agree_at_twopow
    T P (c * twopow K) t k S hP hpos ht htm hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree
    T P hP hper td c t K L u S s ht hu hK hL hKL hspat hs

/-- **Single-Step `rdrv td (u * 2^L)` Left-Corridor Spatial Shift Zero-Diagonal-Pair Refutation of `CenterPeriodic` (`not_centerPeriodic_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_pair`, 9.1506, `kit [33]`)**:
    for a zero-diagonal pair `(z, (z + (c * 2^K) * P) - 2)` with `2^k ≤ S + 1`, spatial shift agreement by `(c * 2^K) * P` on the left corridor of width `S` at step `(z + 2^k) + (c * 2^K) * P` of `rdrv td (u * 2^L)` refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree_at_zero_diag_pair
    (T P td c z k K L u S : Nat)
    (hP : 0 < P)
    (hz0 : IsZeroDiag z) (h2 : 2 ≤ z + (c * twopow K) * P)
    (hz1 : IsZeroDiag ((z + (c * twopow K) * P) - 2))
    (ht : T ≤ z + twopow k)
    (hset0 : SettledBy z (z + twopow k))
    (hset1 : SettledBy (z + (c * twopow K) * P) ((z + (c * twopow K) * P) + twopow k))
    (hS : twopow k ≤ S + 1)
    (hu : 1 ≤ u) (hK : ((z + twopow k) + S) + 1 ≤ K)
    (hL : (((z + twopow k) + S) + (c * twopow K) * P) + 1 ≤ L) (hKL : K ≤ L)
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (u * twopow L) ((z + twopow k) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
        rdrv td (u * twopow L) ((z + twopow k) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hper
  refine not_centerPeriodic_of_maskparity_zero_agree_of_two_zero_diags_prop
    T P (c * twopow K) z k S hP hz0 h2 hz1 ht hset0 hset1 hS (fun s hs => ?_) hper
  exact periodic_maskparity_zero_agree_of_rdrv_dyadic_mul_period_single_row_left_corridor_spatial_agree
    T P hP hper td c (z + twopow k) K L u S s ht hu hK hL hKL hspat hs

/-! ### Batch 81: Unconditional Dyadic-Multiple Diagonal-Shift Periodicity & Direct Left-Half Single-Row Spatial Shift Reduction at t = z + 1 (9.1507–9.1521) -/

/-- **9.1507**: Common dyadic-multiple `w * 2^e`-periodicity of every settled left diagonal `d ≤ e`. -/
theorem ldiag_settled_mul_twopow_periodic_le
    (e w d t : Nat) (hde : d ≤ e) (hset : settle d ≤ t) :
    ldiag d (t + w * twopow e) = ldiag d t := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hw : t + (w + 1) * twopow e = (t + w * twopow e) + twopow e := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hw, ldiag_settled_twopow_periodic_le e d (t + w * twopow e) hde (by omega), ih]

theorem ldiag_settled_mul_twopow_periodic_le_prop
    (e w d t : Nat) (hde : d ≤ e) (hset : SettledBy d t) :
    ldiag d (t + w * twopow e) = ldiag d t :=
  ldiag_settled_mul_twopow_periodic_le e w d t hde hset

/-- **9.1508**: Unconditional diagonal-shift `w * 2^e`-periodicity of `lhCenter` for all `t - p ≤ e` and `settle (t - p) ≤ t` (with no `p ≤ t` bound required!). -/
theorem lhCenter_diag_shift_mul_twopow_periodic_le
    (e w t p : Nat) (hde : t - p ≤ e) (hset : settle (t - p) ≤ t) :
    lhCenter (t + w * twopow e) (p + w * twopow e) = lhCenter t p := by
  by_cases hpt : p ≤ t
  · rw [lhCenter_eq_ldiag (t + w * twopow e) (p + w * twopow e) (by omega),
        lhCenter_eq_ldiag t p hpt,
        show (t + w * twopow e) - (p + w * twopow e) = t - p by omega]
    exact ldiag_settled_mul_twopow_periodic_le e w (t - p) t hde hset
  · rw [lhCenter_gt_eq_false (t + w * twopow e) (p + w * twopow e) (by omega),
        lhCenter_gt_eq_false t p (by omega)]

theorem lhCenter_diag_shift_mul_twopow_periodic_le_prop
    (e w t p : Nat) (hde : t - p ≤ e) (hset : SettledBy (t - p) t) :
    lhCenter (t + w * twopow e) (p + w * twopow e) = lhCenter t p :=
  lhCenter_diag_shift_mul_twopow_periodic_le e w t p hde hset

/-- **9.1509**: Single-row spatial shift agreement by `w * 2^e` at row `t + w * 2^e` implies temporal shift agreement `lhCenter (t + w * 2^e) p = lhCenter t p`. -/
theorem lhCenter_eq_shifted_row_of_mul_twopow_and_spatial_agree
    (e w t p : Nat) (hde : t - p ≤ e) (hset : settle (t - p) ≤ t)
    (hspat : lhCenter (t + w * twopow e) p = lhCenter (t + w * twopow e) (p + w * twopow e)) :
    lhCenter (t + w * twopow e) p = lhCenter t p := by
  rw [hspat]
  exact lhCenter_diag_shift_mul_twopow_periodic_le e w t p hde hset

theorem lhCenter_eq_shifted_row_of_mul_twopow_and_spatial_agree_prop
    (e w t p : Nat) (hde : t - p ≤ e) (hset : SettledBy (t - p) t)
    (hspat : lhCenter (t + w * twopow e) p = lhCenter (t + w * twopow e) (p + w * twopow e)) :
    lhCenter (t + w * twopow e) p = lhCenter t p :=
  lhCenter_eq_shifted_row_of_mul_twopow_and_spatial_agree e w t p hde hset hspat

/-- **9.1510**: `LhBandAgree t (w * 2^e) p0 L` from purely spatial shift agreement by `w * 2^e` inside the single left-half row `t + w * 2^e`. -/
theorem lhBandAgree_of_single_lh_row_mul_twopow_spatial_agree
    (e w t p0 L : Nat) (hde : t - p0 ≤ e)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (t + w * twopow e) (p0 + i) = lhCenter (t + w * twopow e) ((p0 + i) + w * twopow e)) :
    LhBandAgree t (w * twopow e) p0 L := by
  intro i hi
  exact lhCenter_eq_shifted_row_of_mul_twopow_and_spatial_agree
    e w t (p0 + i) (by omega) (hset i hi) (hspat i hi)

theorem lhBandAgree_of_single_lh_row_mul_twopow_spatial_agree_prop
    (e w t p0 L : Nat) (hde : t - p0 ≤ e)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (t + w * twopow e) (p0 + i) = lhCenter (t + w * twopow e) ((p0 + i) + w * twopow e)) :
    LhBandAgree t (w * twopow e) p0 L :=
  lhBandAgree_of_single_lh_row_mul_twopow_spatial_agree e w t p0 L hde hset hspat

/-- **9.1511**: `LhBandAgree t (w * 2^e) 1 S` from purely spatial shift agreement by `w * 2^e` inside the single left-half row `t + w * 2^e` on `[1, 1 + S]`. -/
theorem lhBandAgree_one_of_single_lh_row_mul_twopow_spatial_agree
    (e w t S : Nat) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + w * twopow e) (1 + i) = lhCenter (t + w * twopow e) ((1 + i) + w * twopow e)) :
    LhBandAgree t (w * twopow e) 1 S :=
  lhBandAgree_of_single_lh_row_mul_twopow_spatial_agree e w t 1 S hde hset hspat

theorem lhBandAgree_one_of_single_lh_row_mul_twopow_spatial_agree_prop
    (e w t S : Nat) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + w * twopow e) (1 + i) = lhCenter (t + w * twopow e) ((1 + i) + w * twopow e)) :
    LhBandAgree t (w * twopow e) 1 S :=
  lhBandAgree_one_of_single_lh_row_mul_twopow_spatial_agree e w t S hde hset hspat

/-- **9.1512**: Dyadic-multiple period `Q = (c * 2^e) * P` specialization of `9.1511`. -/
theorem lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree
    (e c P t S : Nat) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) = lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    LhBandAgree t ((c * twopow e) * P) 1 S := by
  have hmul : (c * twopow e) * P = (c * P) * twopow e := by
    rw [Nat.mul_assoc, Nat.mul_comm (twopow e) P, ← Nat.mul_assoc]
  rw [hmul] at hspat ⊢
  exact lhBandAgree_one_of_single_lh_row_mul_twopow_spatial_agree e (c * P) t S hde hset hspat

theorem lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree_prop
    (e c P t S : Nat) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) = lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    LhBandAgree t ((c * twopow e) * P) 1 S :=
  lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree e c P t S hde hset hspat

/-- **9.1513**: Under `CenterPeriodic T P`, spatial shift agreement by `(c * 2^e) * P` inside the single left-half row `t + (c * 2^e) * P` on `[1, 1 + S]` implies `LhColAgree t ((c * 2^e) * P) 1 S`. -/
theorem periodic_lhColAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (c e t S : Nat) (ht : T ≤ t) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) = lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    LhColAgree t ((c * twopow e) * P) 1 S := by
  refine periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper (c * twopow e) t S ht ?_
  exact lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree e c P t S hde hset hspat

theorem periodic_lhColAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (c e t S : Nat) (ht : T ≤ t) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) = lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    LhColAgree t ((c * twopow e) * P) 1 S :=
  periodic_lhColAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree T P hP hper c e t S ht hde hset hspat

/-- **9.1514**: Under `CenterPeriodic T P`, spatial shift agreement by `(c * 2^e) * P` inside the single left-half row `t + (c * 2^e) * P` on `[1, 1 + S]` implies `maskparity · 0` agreement over `[t, t + S]`. -/
theorem periodic_maskparity_zero_agree_of_single_lh_row_dyadic_mul_period_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (c e t S s : Nat) (ht : T ≤ t) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) = lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + (c * twopow e) * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 := by
  refine periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper (c * twopow e) t S s ht ?_ hs
  exact lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree e c P t S hde hset hspat

theorem periodic_maskparity_zero_agree_of_single_lh_row_dyadic_mul_period_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (c e t S s : Nat) (ht : T ≤ t) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) = lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity ((t + s) + (c * twopow e) * P) 0 =
      Rule30UOR.Scale.maskparity (t + s) 0 :=
  periodic_maskparity_zero_agree_of_single_lh_row_dyadic_mul_period_spatial_agree
    T P hP hper c e t S s ht hde hset hspat hs

/-- **9.1515**: Single-row left-half spatial shift agreement by `(c * 2^e) * P` at a doubling zero diagonal refutes `CenterPeriodic T P`. -/
theorem not_centerPeriodic_of_single_lh_row_dyadic_mul_period_spatial_agree_at_zero_diag_doubles
    (T P c z p e S : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow e) * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - (c * twopow e) * P) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow e) * P) ≤ S + 1)
    (hde : (z + (p + 1)) - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + (p + 1)) + (c * twopow e) * P) (1 + i) =
      lhCenter ((z + (p + 1)) + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hgt : e < twopow e := twopow_gt_self e
  have hm : 0 < c * twopow e := Nat.mul_pos hc (by omega)
  refine not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P (c * twopow e) z p S hP hm ht hz hd hset1 hset2 hS ?_
  exact lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree
    e c P (z + (p + 1)) S hde hset hspat

theorem not_centerPeriodic_of_single_lh_row_dyadic_mul_period_spatial_agree_at_zero_diag_doubles_prop
    (T P c z p e S : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow e) * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - (c * twopow e) * P) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow e) * P) ≤ S + 1)
    (hde : (z + (p + 1)) - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + (p + 1)) + (c * twopow e) * P) (1 + i) =
      lhCenter ((z + (p + 1)) + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_single_lh_row_dyadic_mul_period_spatial_agree_at_zero_diag_doubles
    T P c z p e S hP hc ht hz hd hset1 hset2 hS hde hset hspat

/-- **9.1516**: Single-row left-half spatial shift agreement by `(c * 2^e) * P` at `t + (c * 2^e) * P = 2^k` refutes `CenterPeriodic T P`. -/
theorem not_centerPeriodic_of_single_lh_row_dyadic_mul_period_spatial_agree_twopow
    (T P c t k e S : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ t) (htm : t + (c * twopow e) * P = twopow k)
    (hS : twopow k ≤ S + 1) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) =
      lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hgt : e < twopow e := twopow_gt_self e
  have hm : 0 < c * twopow e := Nat.mul_pos hc (by omega)
  refine not_centerPeriodic_of_lhBandAgree_one_twopow T P (c * twopow e) t k S hP hm ht htm hS ?_
  exact lhBandAgree_one_of_single_lh_row_dyadic_mul_period_spatial_agree e c P t S hde hset hspat

theorem not_centerPeriodic_of_single_lh_row_dyadic_mul_period_spatial_agree_twopow_prop
    (T P c t k e S : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ t) (htm : t + (c * twopow e) * P = twopow k)
    (hS : twopow k ≤ S + 1) (hde : t - 1 ≤ e)
    (hset : ∀ i : Nat, i ≤ S → SettledBy (t - (1 + i)) t)
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (t + (c * twopow e) * P) (1 + i) =
      lhCenter (t + (c * twopow e) * P) ((1 + i) + (c * twopow e) * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_single_lh_row_dyadic_mul_period_spatial_agree_twopow
    T P c t k e S hP hc ht htm hS hde hset hspat

/-- **9.1517**: For ANY shift `Q` and doubling point `z` (`DoublesAt Q z`) with `t - p0 ≤ z` (no dyadic factor `2^e` in `Q` required!), spatial `Q`-periodicity inside the single left-half row `t + Q` on `[p0, p0 + L]` implies `LhBandAgree t Q p0 L`. -/
theorem lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree
    (Q z t p0 L : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (t + Q) (p0 + i) = lhCenter (t + Q) ((p0 + i) + Q)) :
    LhBandAgree t Q p0 L := by
  intro i hi
  rw [hspat i hi]
  exact lhCenter_diag_shift_periodic_of_doubles_le Q z t (p0 + i) hd (by omega) (hset i hi)

theorem lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree_prop
    (Q z t p0 L : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (t + Q) (p0 + i) = lhCenter (t + Q) ((p0 + i) + Q)) :
    LhBandAgree t Q p0 L :=
  lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree Q z t p0 L hd hdz hset hspat

/-- **9.1518**: At `t = z + 1` (one step past a doubling point `z` where `DoublesAt Q z` holds), EVERY cell `(z + 1, 1 + i)` in `[1, 1 + S]` satisfies `(z + 1) - (1 + i) = z - i ≤ z`, so spatial `Q`-periodicity inside the single left-half row `(z + 1) + Q` on `[1, 1 + S]` implies `LhBandAgree (z + 1) Q 1 S` for ANY `Q`! -/
theorem lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    (Q z S : Nat) (hd : DoublesAt Q z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + Q) (1 + i) = lhCenter ((z + 1) + Q) ((1 + i) + Q)) :
    LhBandAgree (z + 1) Q 1 S :=
  lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree Q z (z + 1) 1 S hd (by omega) hset hspat

theorem lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree_prop
    (Q z S : Nat) (hd : DoublesAt Q z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + Q) (1 + i) = lhCenter ((z + 1) + Q) ((1 + i) + Q)) :
    LhBandAgree (z + 1) Q 1 S :=
  lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree Q z S hd hset hspat

/-- **9.1519**: Under `CenterPeriodic T P` (`T ≤ z + 1`) and `DoublesAt (m * P) z` (available for EVERY `m` by `9.898`!), spatial `(m * P)`-periodicity of the single left-half row `(z + 1) + m * P` on `[1, 1 + S]` implies `LhColAgree (z + 1) (m * P) 1 S`. -/
theorem periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + m * P) (1 + i) = lhCenter ((z + 1) + m * P) ((1 + i) + m * P)) :
    LhColAgree (z + 1) (m * P) 1 S := by
  refine periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m (z + 1) S ht ?_
  exact lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree (m * P) z S hd hset hspat

theorem periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + m * P) (1 + i) = lhCenter ((z + 1) + m * P) ((1 + i) + m * P)) :
    LhColAgree (z + 1) (m * P) 1 S :=
  periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    T P hP hper m z S ht hd hset hspat

/-- **9.1520**: Under `CenterPeriodic T P` (`T ≤ z + 1`) and `DoublesAt (m * P) z`, spatial `(m * P)`-periodicity of the single left-half row `(z + 1) + m * P` on `[1, 1 + S]` implies `maskparity · 0` agreement over `[z + 1, (z + 1) + S]`. -/
theorem periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S s : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + m * P) (1 + i) = lhCenter ((z + 1) + m * P) ((1 + i) + m * P))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity (((z + 1) + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity ((z + 1) + s) 0 := by
  refine periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper m (z + 1) S s ht ?_ hs
  exact lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree (m * P) z S hd hset hspat

theorem periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S s : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + m * P) (1 + i) = lhCenter ((z + 1) + m * P) ((1 + i) + m * P))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity (((z + 1) + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity ((z + 1) + s) 0 :=
  periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    T P hP hper m z S s ht hd hset hspat hs

/-- **9.1521**: At `t = z + 1` (`p = 0`), spatial `(m * P)`-periodicity of the single left-half row `(z + 1) + m * P` across `[1, 1 + S]` (`3 * (m * P) ≤ S + 1`) refutes `CenterPeriodic T P` for ANY `m > 0`! -/
theorem not_centerPeriodic_of_single_lh_row_spatial_agree_at_zero_diag_succ_doubles
    (T P m z S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + 1) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - m * P) (z + 1))
    (hS : 3 * (m * P) ≤ S + 1)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + m * P) (1 + i) = lhCenter ((z + 1) + m * P) ((1 + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hband := lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree (m * P) z S hd hset hspat
  have h0 : z + (0 + 1) = z + 1 := rfl
  have hS0 : 0 + 3 * (m * P) ≤ S + 1 := by omega
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P m z 0 S hP hm (by simpa [h0] using ht) hz hd
    (by simpa [h0] using hset1) (by simpa [h0] using hset2) hS0
    (by simpa [h0] using hband)

theorem not_centerPeriodic_of_single_lh_row_spatial_agree_at_zero_diag_succ_doubles_prop
    (T P m z S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + 1) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - m * P) (z + 1))
    (hS : 3 * (m * P) ≤ S + 1)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + m * P) (1 + i) = lhCenter ((z + 1) + m * P) ((1 + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_single_lh_row_spatial_agree_at_zero_diag_succ_doubles
    T P m z S hP hm ht hz hd hset1 hset2 hS hset hspat

/-! ### Batch 82: General-p Prefix/Tail Decomposition at Doubling Zero Diagonals & Single-Scale Dyadic Embedding of Single-Row Left-Half Spatial Agreement in rhCenter and rdrv (9.1522–9.1536) -/

/-- **9.1522**: At `t = z + (p + 1)` with `DoublesAt Q z`, `LhBandAgree (z + (p + 1)) Q 1 S` splits into the `p`-cell prefix `i < p` above `z` and the single-row spatial tail `p ≤ i ≤ S` at or below `z`. -/
theorem lhBandAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail
    (Q z p S : Nat) (hd : DoublesAt Q z)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + Q) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (hset : ∀ i : Nat, p ≤ i → i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + Q) (1 + i) = lhCenter ((z + (p + 1)) + Q) ((1 + i) + Q)) :
    LhBandAgree (z + (p + 1)) Q 1 S := by
  intro i hi
  by_cases hip : i < p
  · exact hpref i hip
  · have hpi : p ≤ i := by omega
    rw [htail i hpi hi]
    exact lhCenter_diag_shift_periodic_of_doubles_le Q z (z + (p + 1)) (1 + i) hd (by omega) (hset i hpi hi)

theorem lhBandAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail_prop
    (Q z p S : Nat) (hd : DoublesAt Q z)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + Q) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (hset : ∀ i : Nat, p ≤ i → i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + Q) (1 + i) = lhCenter ((z + (p + 1)) + Q) ((1 + i) + Q)) :
    LhBandAgree (z + (p + 1)) Q 1 S :=
  lhBandAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail Q z p S hd hpref hset htail

/-- **9.1523**: Under `CenterPeriodic T P` (`T ≤ z + (p + 1)`) and `DoublesAt (m * P) z`, the `p`-cell prefix + single-row tail hypotheses imply `LhColAgree (z + (p + 1)) (m * P) 1 S`. -/
theorem periodic_lhColAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z p S : Nat) (ht : T ≤ z + (p + 1)) (hd : DoublesAt (m * P) z)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (hset : ∀ i : Nat, p ≤ i → i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter ((z + (p + 1)) + m * P) ((1 + i) + m * P)) :
    LhColAgree (z + (p + 1)) (m * P) 1 S := by
  refine periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m (z + (p + 1)) S ht ?_
  exact lhBandAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail (m * P) z p S hd hpref hset htail

theorem periodic_lhColAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z p S : Nat) (ht : T ≤ z + (p + 1)) (hd : DoublesAt (m * P) z)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (hset : ∀ i : Nat, p ≤ i → i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter ((z + (p + 1)) + m * P) ((1 + i) + m * P)) :
    LhColAgree (z + (p + 1)) (m * P) 1 S :=
  periodic_lhColAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail
    T P hP hper m z p S ht hd hpref hset htail

/-- **9.1524**: The `p`-cell prefix + single-row tail spatial agreement at `t = z + (p + 1)` refutes `CenterPeriodic T P`. -/
theorem not_centerPeriodic_of_doubles_prefix_and_single_lh_row_tail_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (hset : ∀ i : Nat, p ≤ i → i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter ((z + (p + 1)) + m * P) ((1 + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P m z p S hP hm ht hz hd hset1 hset2 hS ?_
  exact lhBandAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail (m * P) z p S hd hpref hset htail

theorem not_centerPeriodic_of_doubles_prefix_and_single_lh_row_tail_at_zero_diag_prop
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (hset : ∀ i : Nat, p ≤ i → i ≤ S → SettledBy ((z + (p + 1)) - (1 + i)) (z + (p + 1)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter ((z + (p + 1)) + m * P) ((1 + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_doubles_prefix_and_single_lh_row_tail_at_zero_diag
    T P m z p S hP hm ht hz hd hset1 hset2 hS hpref hset htail

/-- **9.1525**: At a SINGLE dyadic scale `K` (`(t + Q) + (d + Q) ≤ K`), leftward `Q`-shift agreement inside the single right-half row `(t + Q) + v * 2^K` transfers directly to `lhCenter (t + Q) d = lhCenter (t + Q) (d + Q)`. -/
theorem rhCenter_dyadic_left_shift_pair_eq_lhCenter_pair
    (t Q K v d : Nat) (hv : 1 ≤ v) (hK : (t + Q) + (d + Q) ≤ K)
    (hrh : rhCenter ((t + Q) + v * twopow K) ((v * twopow K) - d) =
           rhCenter ((t + Q) + v * twopow K) ((v * twopow K) - (d + Q))) :
    lhCenter (t + Q) d = lhCenter (t + Q) (d + Q) := by
  have h1 := rhCenter_dyadic_sub_shift_eq_lhCenter (t + Q) K v d 0 hv (by omega)
  have h2 := rhCenter_dyadic_sub_shift_eq_lhCenter (t + Q) K v (d + Q) 0 hv hK
  simp only [Nat.add_zero] at h1 h2
  rw [← h1, ← h2]
  exact hrh

/-- **9.1526**: Single-scale (`K`) single-row `rhCenter ((t + Q) + v * 2^K)` leftward `Q`-shift agreement implies `LhBandAgree t Q p0 L` for ANY `Q` with `DoublesAt Q z` and `t - p0 ≤ z`. -/
theorem lhBandAgree_of_doubles_le_and_single_rh_row_dyadic_left_spatial_agree
    (Q z t p0 L K v : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hv : 1 ≤ v) (hK : (t + Q) + ((p0 + L) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((t + Q) + v * twopow K) ((v * twopow K) - (p0 + i)) =
      rhCenter ((t + Q) + v * twopow K) ((v * twopow K) - ((p0 + i) + Q))) :
    LhBandAgree t Q p0 L := by
  refine lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree Q z t p0 L hd hdz hset (fun i hi => ?_)
  exact rhCenter_dyadic_left_shift_pair_eq_lhCenter_pair t Q K v (p0 + i) hv (by omega) (hspat i hi)

theorem lhBandAgree_of_doubles_le_and_single_rh_row_dyadic_left_spatial_agree_prop
    (Q z t p0 L K v : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hv : 1 ≤ v) (hK : (t + Q) + ((p0 + L) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((t + Q) + v * twopow K) ((v * twopow K) - (p0 + i)) =
      rhCenter ((t + Q) + v * twopow K) ((v * twopow K) - ((p0 + i) + Q))) :
    LhBandAgree t Q p0 L :=
  lhBandAgree_of_doubles_le_and_single_rh_row_dyadic_left_spatial_agree Q z t p0 L K v hd hdz hv hK hset hspat

/-- **9.1527**: At `t = z + 1` (`p = 0`), single-scale (`K`) single-row `rhCenter (((z + 1) + Q) + v * 2^K)` leftward `Q`-shift agreement on `[1, 1 + S]` implies `LhBandAgree (z + 1) Q 1 S` for ANY `Q` with `DoublesAt Q z`. -/
theorem lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    (Q z S K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : ((z + 1) + Q) + ((1 + S) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + Q) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + Q) + v * twopow K) ((v * twopow K) - ((1 + i) + Q))) :
    LhBandAgree (z + 1) Q 1 S :=
  lhBandAgree_of_doubles_le_and_single_rh_row_dyadic_left_spatial_agree
    Q z (z + 1) 1 S K v hd (by omega) hv hK hset hspat

theorem lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree_prop
    (Q z S K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : ((z + 1) + Q) + ((1 + S) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + Q) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + Q) + v * twopow K) ((v * twopow K) - ((1 + i) + Q))) :
    LhBandAgree (z + 1) Q 1 S :=
  lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    Q z S K v hd hv hK hset hspat

/-- **9.1528**: Under `CenterPeriodic T P` (`T ≤ z + 1`) and `DoublesAt (m * P) z`, single-scale (`K`) single-row `rhCenter (((z + 1) + m * P) + v * 2^K)` leftward `(m * P)`-shift agreement on `[1, 1 + S]` implies `LhColAgree (z + 1) (m * P) 1 S` for ANY `m`! -/
theorem periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S K v : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P))) :
    LhColAgree (z + 1) (m * P) 1 S := by
  refine periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m (z + 1) S ht ?_
  exact lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    (m * P) z S K v hd hv hK hset hspat

theorem periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S K v : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P))) :
    LhColAgree (z + 1) (m * P) 1 S :=
  periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    T P hP hper m z S K v ht hd hv hK hset hspat

/-- **9.1529**: Under `CenterPeriodic T P` (`T ≤ z + 1`) and `DoublesAt (m * P) z`, single-scale (`K`) single-row `rhCenter (((z + 1) + m * P) + v * 2^K)` leftward `(m * P)`-shift agreement on `[1, 1 + S]` implies `maskparity · 0` agreement over `[z + 1, (z + 1) + S]`. -/
theorem periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S K v s : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity (((z + 1) + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity ((z + 1) + s) 0 := by
  refine periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper m (z + 1) S s ht ?_ hs
  exact lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    (m * P) z S K v hd hv hK hset hspat

theorem periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z S K v s : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity (((z + 1) + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity ((z + 1) + s) 0 :=
  periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    T P hP hper m z S K v s ht hd hv hK hset hspat hs

/-- **9.1530**: Single-scale (`K`), arbitrary-`m` (`0 < m`), single-row `rhCenter (((z + 1) + m * P) + v * 2^K)` leftward `(m * P)`-shift agreement on `[1, 1 + S]` (`3 * (m * P) ≤ S + 1`) refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_single_rh_row_dyadic_left_spatial_agree_at_zero_diag_succ_doubles
    (T P m z S K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + 1) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - m * P) (z + 1))
    (hS : 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_single_lh_row_spatial_agree_at_zero_diag_succ_doubles
    T P m z S hP hm ht hz hd hset1 hset2 hS hset (fun i hi => ?_)
  exact rhCenter_dyadic_left_shift_pair_eq_lhCenter_pair (z + 1) (m * P) K v (1 + i) hv (by omega) (hspat i hi)

theorem not_centerPeriodic_of_single_rh_row_dyadic_left_spatial_agree_at_zero_diag_succ_doubles_prop
    (T P m z S K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + 1) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - m * P) (z + 1))
    (hS : 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + 1) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_single_rh_row_dyadic_left_spatial_agree_at_zero_diag_succ_doubles
    T P m z S K v hP hm ht hz hd hset1 hset2 hS hv hK hset hspat

/-- **9.1531**: At a SINGLE dyadic scale `K` (`(t + Q) + (d + Q) ≤ K`), leftward `Q`-shift agreement inside the single driven row `rdrv td (v * 2^K) (t + Q)` transfers directly to `lhCenter (t + Q) d = lhCenter (t + Q) (d + Q)`. -/
theorem rdrv_dyadic_left_shift_pair_eq_lhCenter_pair
    (td t Q K v d : Nat) (hv : 1 ≤ v) (hK : (t + Q) + (d + Q) ≤ K)
    (hrdrv : rdrv td (v * twopow K) (t + Q) ((v * twopow K) - d) =
             rdrv td (v * twopow K) (t + Q) ((v * twopow K) - (d + Q))) :
    lhCenter (t + Q) d = lhCenter (t + Q) (d + Q) := by
  have h1 := rdrv_dyadic_exact_row_shift_left_eq td K v d (t + Q) hv (by omega)
  have h2 := rdrv_dyadic_exact_row_shift_left_eq td K v (d + Q) (t + Q) hv hK
  rw [← h1, ← h2]
  exact hrdrv

/-- **9.1532**: Single-scale (`K`) single-step `rdrv td (v * 2^K) (t + Q)` leftward `Q`-shift agreement implies `LhBandAgree t Q p0 L` for ANY `Q` with `DoublesAt Q z` and `t - p0 ≤ z`. -/
theorem lhBandAgree_of_doubles_le_and_single_rdrv_row_dyadic_left_spatial_agree
    (td Q z t p0 L K v : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hv : 1 ≤ v) (hK : (t + Q) + ((p0 + L) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      rdrv td (v * twopow K) (t + Q) ((v * twopow K) - (p0 + i)) =
      rdrv td (v * twopow K) (t + Q) ((v * twopow K) - ((p0 + i) + Q))) :
    LhBandAgree t Q p0 L := by
  refine lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree Q z t p0 L hd hdz hset (fun i hi => ?_)
  exact rdrv_dyadic_left_shift_pair_eq_lhCenter_pair td t Q K v (p0 + i) hv (by omega) (hspat i hi)

theorem lhBandAgree_of_doubles_le_and_single_rdrv_row_dyadic_left_spatial_agree_prop
    (td Q z t p0 L K v : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hv : 1 ≤ v) (hK : (t + Q) + ((p0 + L) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) t)
    (hspat : ∀ i : Nat, i ≤ L →
      rdrv td (v * twopow K) (t + Q) ((v * twopow K) - (p0 + i)) =
      rdrv td (v * twopow K) (t + Q) ((v * twopow K) - ((p0 + i) + Q))) :
    LhBandAgree t Q p0 L :=
  lhBandAgree_of_doubles_le_and_single_rdrv_row_dyadic_left_spatial_agree td Q z t p0 L K v hd hdz hv hK hset hspat

/-- **9.1533**: At `t = z + 1` (`p = 0`), single-scale (`K`) single-step `rdrv td (v * 2^K) ((z + 1) + Q)` leftward `Q`-shift agreement on `[1, 1 + S]` implies `LhBandAgree (z + 1) Q 1 S` for ANY `Q` with `DoublesAt Q z`. -/
theorem lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    (td Q z S K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : ((z + 1) + Q) + ((1 + S) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + Q) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + Q) ((v * twopow K) - ((1 + i) + Q))) :
    LhBandAgree (z + 1) Q 1 S :=
  lhBandAgree_of_doubles_le_and_single_rdrv_row_dyadic_left_spatial_agree
    td Q z (z + 1) 1 S K v hd (by omega) hv hK hset hspat

theorem lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree_prop
    (td Q z S K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : ((z + 1) + Q) + ((1 + S) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + Q) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + Q) ((v * twopow K) - ((1 + i) + Q))) :
    LhBandAgree (z + 1) Q 1 S :=
  lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    td Q z S K v hd hv hK hset hspat

/-- **9.1534**: Under `CenterPeriodic T P` (`T ≤ z + 1`) and `DoublesAt (m * P) z`, single-scale (`K`) single-step `rdrv td (v * 2^K) ((z + 1) + m * P)` leftward `(m * P)`-shift agreement on `[1, 1 + S]` implies `LhColAgree (z + 1) (m * P) 1 S` for ANY `m`! -/
theorem periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td m z S K v : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - ((1 + i) + m * P))) :
    LhColAgree (z + 1) (m * P) 1 S := by
  refine periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m (z + 1) S ht ?_
  exact lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    td (m * P) z S K v hd hv hK hset hspat

theorem periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td m z S K v : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - ((1 + i) + m * P))) :
    LhColAgree (z + 1) (m * P) 1 S :=
  periodic_lhColAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    T P hP hper td m z S K v ht hd hv hK hset hspat

/-- **9.1535**: Under `CenterPeriodic T P` (`T ≤ z + 1`) and `DoublesAt (m * P) z`, single-scale (`K`) single-step `rdrv td (v * 2^K) ((z + 1) + m * P)` leftward `(m * P)`-shift agreement on `[1, 1 + S]` implies `maskparity · 0` agreement over `[z + 1, (z + 1) + S]`. -/
theorem periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td m z S K v s : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - ((1 + i) + m * P)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity (((z + 1) + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity ((z + 1) + s) 0 := by
  refine periodic_maskparity_zero_agree_of_lhBandAgree_one T P hP hper m (z + 1) S s ht ?_ hs
  exact lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    td (m * P) z S K v hd hv hK hset hspat

theorem periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (td m z S K v s : Nat) (ht : T ≤ z + 1) (hd : DoublesAt (m * P) z)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - ((1 + i) + m * P)))
    (hs : s ≤ S) :
    Rule30UOR.Scale.maskparity (((z + 1) + s) + m * P) 0 =
      Rule30UOR.Scale.maskparity ((z + 1) + s) 0 :=
  periodic_maskparity_zero_agree_at_zero_diag_succ_of_doubles_and_single_rdrv_row_dyadic_left_spatial_agree
    T P hP hper td m z S K v s ht hd hv hK hset hspat hs

/-- **9.1536**: Single-scale (`K`), arbitrary-`m` (`0 < m`), single-step `rdrv td (v * 2^K) ((z + 1) + m * P)` leftward `(m * P)`-shift agreement on `[1, 1 + S]` (`3 * (m * P) ≤ S + 1`) refutes `CenterPeriodic T P`! -/
theorem not_centerPeriodic_of_single_rdrv_row_dyadic_left_spatial_agree_at_zero_diag_succ_doubles
    (T P td m z S K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + 1) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - m * P) (z + 1))
    (hS : 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - ((1 + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_single_lh_row_spatial_agree_at_zero_diag_succ_doubles
    T P m z S hP hm ht hz hd hset1 hset2 hS hset (fun i hi => ?_)
  exact rdrv_dyadic_left_shift_pair_eq_lhCenter_pair td (z + 1) (m * P) K v (1 + i) hv (by omega) (hspat i hi)

theorem not_centerPeriodic_of_single_rdrv_row_dyadic_left_spatial_agree_at_zero_diag_succ_doubles_prop
    (T P td m z S K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + 1) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - m * P) (z + 1))
    (hS : 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + 1) + m * P) + ((1 + S) + m * P) ≤ K)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + 1) + m * P) ((v * twopow K) - ((1 + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_single_rdrv_row_dyadic_left_spatial_agree_at_zero_diag_succ_doubles
    T P td m z S K v hP hm ht hz hd hset1 hset2 hS hv hK hset hspat

/-! ### Batch 83: Late-Scale (t + 2^k, p + 2^k) Diagonal-Shift Periodicity & Scale-Independent Tail Horizon 3mP Refutations (9.1537–9.1551) -/

/-- **9.1537**: Late-scale `(t + 2^k, p + 2^k)` diagonal-shift `Q`-periodicity of `lhCenter` below a doubling point `z`, requiring ONLY late settlement `SettledBy (t - p) (t + 2^k)`! -/
theorem lhCenter_late_scale_diag_shift_periodic_of_doubles_le
    (Q z t p k : Nat) (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : SettledBy (t - p) (t + twopow k)) :
    lhCenter ((t + Q) + twopow k) ((p + Q) + twopow k) = lhCenter (t + twopow k) (p + twopow k) := by
  have ht : (t + Q) + twopow k = (t + twopow k) + Q := by omega
  have hp : (p + Q) + twopow k = (p + twopow k) + Q := by omega
  have hsub : (t + twopow k) - (p + twopow k) = t - p := by omega
  rw [ht, hp]
  exact lhCenter_diag_shift_periodic_of_doubles_le Q z (t + twopow k) (p + twopow k)
    hd (by omega) (by simpa [SettledBy, hsub] using hset)

theorem lhCenter_late_scale_diag_shift_periodic_of_doubles_le_prop
    (Q z t p k : Nat) (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : SettledBy (t - p) (t + twopow k)) :
    lhCenter ((t + Q) + twopow k) ((p + Q) + twopow k) = lhCenter (t + twopow k) (p + twopow k) :=
  lhCenter_late_scale_diag_shift_periodic_of_doubles_le Q z t p k hd hdz hset

/-- **9.1538**: Late-scale `(t + 2^k, p + 2^k)` diagonal-shift `w * 2^e`-periodicity of `lhCenter` for `t - p ≤ e`, requiring ONLY late settlement `SettledBy (t - p) (t + 2^k)`! -/
theorem lhCenter_late_scale_diag_shift_mul_twopow_periodic_le
    (e w t p k : Nat) (hde : t - p ≤ e)
    (hset : SettledBy (t - p) (t + twopow k)) :
    lhCenter ((t + w * twopow e) + twopow k) ((p + w * twopow e) + twopow k) =
      lhCenter (t + twopow k) (p + twopow k) := by
  have ht : (t + w * twopow e) + twopow k = (t + twopow k) + w * twopow e := by omega
  have hp : (p + w * twopow e) + twopow k = (p + twopow k) + w * twopow e := by omega
  have hsub : (t + twopow k) - (p + twopow k) = t - p := by omega
  rw [ht, hp]
  exact lhCenter_diag_shift_mul_twopow_periodic_le e w (t + twopow k) (p + twopow k)
    (by omega) (by simpa [SettledBy, hsub] using hset)

theorem lhCenter_late_scale_diag_shift_mul_twopow_periodic_le_prop
    (e w t p k : Nat) (hde : t - p ≤ e)
    (hset : SettledBy (t - p) (t + twopow k)) :
    lhCenter ((t + w * twopow e) + twopow k) ((p + w * twopow e) + twopow k) =
      lhCenter (t + twopow k) (p + twopow k) :=
  lhCenter_late_scale_diag_shift_mul_twopow_periodic_le e w t p k hde hset

/-- **9.1539**: Spatial `Q`-periodicity at `(p + 2^k)` inside the single late row `(t + Q) + 2^k` implies temporal `Q`-periodicity `lhCenter ((t + Q) + 2^k) (p + 2^k) = lhCenter (t + 2^k) (p + 2^k)`, requiring ONLY late settlement `SettledBy (t - p) (t + 2^k)`! -/
theorem lhCenter_late_scale_eq_of_doubles_le_and_spatial_agree
    (Q z t p k : Nat) (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : SettledBy (t - p) (t + twopow k))
    (hspat : lhCenter ((t + Q) + twopow k) (p + twopow k) =
             lhCenter ((t + Q) + twopow k) ((p + Q) + twopow k)) :
    lhCenter ((t + Q) + twopow k) (p + twopow k) = lhCenter (t + twopow k) (p + twopow k) := by
  rw [hspat]
  exact lhCenter_late_scale_diag_shift_periodic_of_doubles_le Q z t p k hd hdz hset

theorem lhCenter_late_scale_eq_of_doubles_le_and_spatial_agree_prop
    (Q z t p k : Nat) (hd : DoublesAt Q z) (hdz : t - p ≤ z)
    (hset : SettledBy (t - p) (t + twopow k))
    (hspat : lhCenter ((t + Q) + twopow k) (p + twopow k) =
             lhCenter ((t + Q) + twopow k) ((p + Q) + twopow k)) :
    lhCenter ((t + Q) + twopow k) (p + twopow k) = lhCenter (t + twopow k) (p + twopow k) :=
  lhCenter_late_scale_eq_of_doubles_le_and_spatial_agree Q z t p k hd hdz hset hspat

/-- **9.1540**: `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` from single-row spatial `Q`-periodicity on `[p0 + 2^k, p0 + 2^k + L]` at `(t + Q) + 2^k`, requiring ONLY late settlement `SettledBy (t - (p0 + i)) (t + 2^k)`. -/
theorem lhBandAgree_late_scale_of_doubles_le_and_single_lh_row_spatial_agree
    (Q z t p0 L k : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) (t + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter ((t + Q) + twopow k) ((p0 + twopow k) + i) =
      lhCenter ((t + Q) + twopow k) (((p0 + twopow k) + i) + Q)) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  intro i hi
  have ht : (t + twopow k) + Q = (t + Q) + twopow k := by omega
  have hp1 : (p0 + twopow k) + i = (p0 + i) + twopow k := by omega
  have hp2 : ((p0 + twopow k) + i) + Q = ((p0 + i) + Q) + twopow k := by omega
  have hsp : lhCenter ((t + Q) + twopow k) ((p0 + i) + twopow k) =
      lhCenter ((t + Q) + twopow k) (((p0 + i) + Q) + twopow k) := by
    have h0 := hspat i hi
    rwa [hp2, hp1] at h0
  rw [ht, hp1]
  exact lhCenter_late_scale_eq_of_doubles_le_and_spatial_agree
    Q z t (p0 + i) k hd (by omega) (hset i hi) hsp

theorem lhBandAgree_late_scale_of_doubles_le_and_single_lh_row_spatial_agree_prop
    (Q z t p0 L k : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z)
    (hset : ∀ i : Nat, i ≤ L → SettledBy (t - (p0 + i)) (t + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter ((t + Q) + twopow k) ((p0 + twopow k) + i) =
      lhCenter ((t + Q) + twopow k) (((p0 + twopow k) + i) + Q)) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L :=
  lhBandAgree_late_scale_of_doubles_le_and_single_lh_row_spatial_agree Q z t p0 L k hd hdz hset hspat

/-- **9.1541**: At `t = z + 1` (`p0 = 1`), single-row spatial `Q`-periodicity on `[1 + 2^k, 1 + 2^k + S]` at `((z + 1) + Q) + 2^k` implies `LhBandAgree ((z + 1) + 2^k) Q (1 + 2^k) S`, requiring ONLY late settlement at `(z + 1) + 2^k`! -/
theorem lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    (Q z S k : Nat) (hd : DoublesAt Q z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (((z + 1) + Q) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + Q) + twopow k) (((1 + twopow k) + i) + Q)) :
    LhBandAgree ((z + 1) + twopow k) Q (1 + twopow k) S :=
  lhBandAgree_late_scale_of_doubles_le_and_single_lh_row_spatial_agree
    Q z (z + 1) 1 S k hd (by omega) hset hspat

theorem lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree_prop
    (Q z S k : Nat) (hd : DoublesAt Q z)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter (((z + 1) + Q) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + Q) + twopow k) (((1 + twopow k) + i) + Q)) :
    LhBandAgree ((z + 1) + twopow k) Q (1 + twopow k) S :=
  lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree Q z S k hd hset hspat

/-- **9.1542**: Band concatenation for `LhBandAgree`: `LhBandAgree t Q p0 A` and `LhBandAgree t Q (p0 + A) B` imply `LhBandAgree t Q p0 (A + B)`. -/
theorem lhBandAgree_append_of_split
    (t Q p0 A B : Nat)
    (hA : LhBandAgree t Q p0 A) (hB : LhBandAgree t Q (p0 + A) B) :
    LhBandAgree t Q p0 (A + B) := by
  intro i hi
  by_cases hiA : i ≤ A
  · exact hA i hiA
  · have hBi := hB (i - A) (by omega)
    simpa [show (p0 + A) + (i - A) = p0 + i by omega] using hBi

/-- **9.1543**: Combining a prefix `i < P0` with a shifted band `LhBandAgree t Q (1 + P0) L` yields `LhBandAgree t Q 1 (P0 + L)`. -/
theorem lhBandAgree_one_of_prefix_and_shifted_band
    (t Q P0 L : Nat)
    (hpref : ∀ i : Nat, i < P0 → lhCenter (t + Q) (1 + i) = lhCenter t (1 + i))
    (hband : LhBandAgree t Q (1 + P0) L) :
    LhBandAgree t Q 1 (P0 + L) := by
  intro i hi
  by_cases hiP : i < P0
  · exact hpref i hiP
  · have hb := hband (i - P0) (by omega)
    simpa [show (1 + P0) + (i - P0) = 1 + i by omega] using hb

/-- **9.1544**: At `t = (z + 1) + 2^k`, combining the `2^k`-prefix `i < 2^k` with single-row spatial `Q`-periodicity on the outer strip `[1 + 2^k, 1 + 2^k + L]` yields `LhBandAgree ((z + 1) + 2^k) Q 1 (2^k + L)`. -/
theorem lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail
    (Q z L k : Nat) (hd : DoublesAt Q z)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + Q) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + Q) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + Q) + twopow k) (((1 + twopow k) + i) + Q)) :
    LhBandAgree ((z + 1) + twopow k) Q 1 (twopow k + L) := by
  refine lhBandAgree_one_of_prefix_and_shifted_band ((z + 1) + twopow k) Q (twopow k) L hpref ?_
  exact lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    Q z L k hd hset hspat

theorem lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail_prop
    (Q z L k : Nat) (hd : DoublesAt Q z)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + Q) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + Q) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + Q) + twopow k) (((1 + twopow k) + i) + Q)) :
    LhBandAgree ((z + 1) + twopow k) Q 1 (twopow k + L) :=
  lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail Q z L k hd hpref hset hspat

/-- **9.1545**: Under `CenterPeriodic T P` (`T ≤ (z + 1) + 2^k`) and `DoublesAt (m * P) z`, the `2^k`-prefix + late single-row tail of width `L` implies `LhColAgree ((z + 1) + 2^k) (m * P) 1 (2^k + L)`. -/
theorem periodic_lhColAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z L k : Nat) (ht : T ≤ (z + 1) + twopow k) (hd : DoublesAt (m * P) z)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + m * P) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + m * P) + twopow k) (((1 + twopow k) + i) + m * P)) :
    LhColAgree ((z + 1) + twopow k) (m * P) 1 (twopow k + L) := by
  refine periodic_lhColAgree_one_of_lhBandAgree_one T P hP hper m ((z + 1) + twopow k) (twopow k + L) ht ?_
  exact lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail
    (m * P) z L k hd hpref hset hspat

theorem periodic_lhColAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m z L k : Nat) (ht : T ≤ (z + 1) + twopow k) (hd : DoublesAt (m * P) z)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + m * P) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + m * P) + twopow k) (((1 + twopow k) + i) + m * P)) :
    LhColAgree ((z + 1) + twopow k) (m * P) 1 (twopow k + L) :=
  periodic_lhColAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail
    T P hP hper m z L k ht hd hpref hset hspat

/-- **9.1546**: Scale-independent tail width `3 * (m * P) ≤ L + 1` at `t = (z + 1) + 2^k`: because `p = 2^k` cancels out of `p + 3 * (m * P) ≤ (2^k + L) + 1`, the single-row tail width `L` is `3 * (m * P) - 1` (independent of `k` and `z`!) and requires ONLY late settlement at `(z + 1) + 2^k`! -/
theorem not_centerPeriodic_of_late_scale_doubles_prefix_and_single_lh_row_tail
    (T P m z L k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + m * P) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + m * P) + twopow k) (((1 + twopow k) + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hband := lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail
    (m * P) z L k hd hpref hset hspat
  have hzp : z + (twopow k + 1) = (z + 1) + twopow k := by omega
  have hS : twopow k + 3 * (m * P) ≤ (twopow k + L) + 1 := by omega
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P m z (twopow k) (twopow k + L) hP hm (by simpa [hzp] using ht) hz hd
    (by simpa [hzp] using hset1) (by simpa [hzp] using hset2) hS
    (by simpa [hzp] using hband)

theorem not_centerPeriodic_of_late_scale_doubles_prefix_and_single_lh_row_tail_prop
    (T P m z L k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + m * P) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + m * P) + twopow k) (((1 + twopow k) + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_late_scale_doubles_prefix_and_single_lh_row_tail
    T P m z L k hP hm ht hz hd hset1 hset2 hL hpref hset hspat

/-- **9.1547**: Embedding the late-scale single-row tail `((z + 1) + Q) + 2^k` into `rhCenter` at scale `K` yields `LhBandAgree ((z + 1) + 2^k) Q (1 + 2^k) L`, requiring ONLY late settlement at `(z + 1) + 2^k`. -/
theorem lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    (Q z L k K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : (((z + 1) + Q) + twopow k) + (((1 + twopow k) + L) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - ((1 + twopow k) + i)) =
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - (((1 + twopow k) + i) + Q))) :
    LhBandAgree ((z + 1) + twopow k) Q (1 + twopow k) L := by
  refine lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    Q z L k hd hset (fun i hi => ?_)
  have ht : ((z + 1) + Q) + twopow k = ((z + 1) + twopow k) + Q := by omega
  rw [ht]
  exact rhCenter_dyadic_left_shift_pair_eq_lhCenter_pair
    ((z + 1) + twopow k) Q K v ((1 + twopow k) + i) hv (by omega)
    (by simpa [ht] using hspat i hi)

theorem lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree_prop
    (Q z L k K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : (((z + 1) + Q) + twopow k) + (((1 + twopow k) + L) + Q) ≤ K)
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - ((1 + twopow k) + i)) =
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - (((1 + twopow k) + i) + Q))) :
    LhBandAgree ((z + 1) + twopow k) Q (1 + twopow k) L :=
  lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    Q z L k K v hd hv hK hset hspat

/-- **9.1548**: Combining the `2^k`-prefix with the `rhCenter`-embedded late single-row tail yields `LhBandAgree ((z + 1) + 2^k) Q 1 (2^k + L)`. -/
theorem lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rh_row_tail
    (Q z L k K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : (((z + 1) + Q) + twopow k) + (((1 + twopow k) + L) + Q) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + Q) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - ((1 + twopow k) + i)) =
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - (((1 + twopow k) + i) + Q))) :
    LhBandAgree ((z + 1) + twopow k) Q 1 (twopow k + L) := by
  refine lhBandAgree_one_of_prefix_and_shifted_band ((z + 1) + twopow k) Q (twopow k) L hpref ?_
  exact lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_rh_row_dyadic_left_spatial_agree
    Q z L k K v hd hv hK hset hspat

theorem lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rh_row_tail_prop
    (Q z L k K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : (((z + 1) + Q) + twopow k) + (((1 + twopow k) + L) + Q) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + Q) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - ((1 + twopow k) + i)) =
      rhCenter ((((z + 1) + Q) + twopow k) + v * twopow K) ((v * twopow K) - (((1 + twopow k) + i) + Q))) :
    LhBandAgree ((z + 1) + twopow k) Q 1 (twopow k + L) :=
  lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rh_row_tail
    Q z L k K v hd hv hK hpref hset hspat

/-- **9.1549**: Refutation of `CenterPeriodic T P` from the `2^k`-prefix and the `rhCenter`-embedded late single-row tail of scale-independent width `3 * (m * P) ≤ L + 1`! -/
theorem not_centerPeriodic_of_late_scale_doubles_prefix_and_single_rh_row_tail
    (T P m z L k K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1) (hv : 1 ≤ v)
    (hK : (((z + 1) + m * P) + twopow k) + (((1 + twopow k) + L) + m * P) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((((z + 1) + m * P) + twopow k) + v * twopow K) ((v * twopow K) - ((1 + twopow k) + i)) =
      rhCenter ((((z + 1) + m * P) + twopow k) + v * twopow K) ((v * twopow K) - (((1 + twopow k) + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hband := lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rh_row_tail
    (m * P) z L k K v hd hv hK hpref hset hspat
  have hzp : z + (twopow k + 1) = (z + 1) + twopow k := by omega
  have hS : twopow k + 3 * (m * P) ≤ (twopow k + L) + 1 := by omega
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P m z (twopow k) (twopow k + L) hP hm (by simpa [hzp] using ht) hz hd
    (by simpa [hzp] using hset1) (by simpa [hzp] using hset2) hS
    (by simpa [hzp] using hband)

theorem not_centerPeriodic_of_late_scale_doubles_prefix_and_single_rh_row_tail_prop
    (T P m z L k K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1) (hv : 1 ≤ v)
    (hK : (((z + 1) + m * P) + twopow k) + (((1 + twopow k) + L) + m * P) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rhCenter ((((z + 1) + m * P) + twopow k) + v * twopow K) ((v * twopow K) - ((1 + twopow k) + i)) =
      rhCenter ((((z + 1) + m * P) + twopow k) + v * twopow K) ((v * twopow K) - (((1 + twopow k) + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_late_scale_doubles_prefix_and_single_rh_row_tail
    T P m z L k K v hP hm ht hz hd hset1 hset2 hL hv hK hpref hset hspat

/-- **9.1550**: Combining the `2^k`-prefix with the `rdrv`-embedded late single-row tail yields `LhBandAgree ((z + 1) + 2^k) Q 1 (2^k + L)`. -/
theorem lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rdrv_row_tail
    (td Q z L k K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : (((z + 1) + Q) + twopow k) + (((1 + twopow k) + L) + Q) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + Q) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rdrv td (v * twopow K) (((z + 1) + Q) + twopow k) ((v * twopow K) - ((1 + twopow k) + i)) =
      rdrv td (v * twopow K) (((z + 1) + Q) + twopow k) ((v * twopow K) - (((1 + twopow k) + i) + Q))) :
    LhBandAgree ((z + 1) + twopow k) Q 1 (twopow k + L) := by
  refine lhBandAgree_one_of_prefix_and_shifted_band ((z + 1) + twopow k) Q (twopow k) L hpref ?_
  refine lhBandAgree_late_scale_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree
    Q z L k hd hset (fun i hi => ?_)
  have ht : ((z + 1) + Q) + twopow k = ((z + 1) + twopow k) + Q := by omega
  rw [ht]
  exact rdrv_dyadic_left_shift_pair_eq_lhCenter_pair
    td ((z + 1) + twopow k) Q K v ((1 + twopow k) + i) hv (by omega)
    (by simpa [ht] using hspat i hi)

theorem lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rdrv_row_tail_prop
    (td Q z L k K v : Nat) (hd : DoublesAt Q z) (hv : 1 ≤ v)
    (hK : (((z + 1) + Q) + twopow k) + (((1 + twopow k) + L) + Q) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + Q) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rdrv td (v * twopow K) (((z + 1) + Q) + twopow k) ((v * twopow K) - ((1 + twopow k) + i)) =
      rdrv td (v * twopow K) (((z + 1) + Q) + twopow k) ((v * twopow K) - (((1 + twopow k) + i) + Q))) :
    LhBandAgree ((z + 1) + twopow k) Q 1 (twopow k + L) :=
  lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rdrv_row_tail
    td Q z L k K v hd hv hK hpref hset hspat

/-- **9.1551**: Refutation of `CenterPeriodic T P` from the `2^k`-prefix and the `rdrv`-embedded late single-row tail of scale-independent width `3 * (m * P) ≤ L + 1`! -/
theorem not_centerPeriodic_of_late_scale_doubles_prefix_and_single_rdrv_row_tail
    (T P td m z L k K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1) (hv : 1 ≤ v)
    (hK : (((z + 1) + m * P) + twopow k) + (((1 + twopow k) + L) + m * P) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rdrv td (v * twopow K) (((z + 1) + m * P) + twopow k) ((v * twopow K) - ((1 + twopow k) + i)) =
      rdrv td (v * twopow K) (((z + 1) + m * P) + twopow k) ((v * twopow K) - (((1 + twopow k) + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hband := lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_rdrv_row_tail
    td (m * P) z L k K v hd hv hK hpref hset hspat
  have hzp : z + (twopow k + 1) = (z + 1) + twopow k := by omega
  have hS : twopow k + 3 * (m * P) ≤ (twopow k + L) + 1 := by omega
  exact not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
    T P m z (twopow k) (twopow k + L) hP hm (by simpa [hzp] using ht) hz hd
    (by simpa [hzp] using hset1) (by simpa [hzp] using hset2) hS
    (by simpa [hzp] using hband)

theorem not_centerPeriodic_of_late_scale_doubles_prefix_and_single_rdrv_row_tail_prop
    (T P td m z L k K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1) (hv : 1 ≤ v)
    (hK : (((z + 1) + m * P) + twopow k) + (((1 + twopow k) + L) + m * P) ≤ K)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      rdrv td (v * twopow K) (((z + 1) + m * P) + twopow k) ((v * twopow K) - ((1 + twopow k) + i)) =
      rdrv td (v * twopow K) (((z + 1) + m * P) + twopow k) ((v * twopow K) - (((1 + twopow k) + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_late_scale_doubles_prefix_and_single_rdrv_row_tail
    T P td m z L k K v hP hm ht hz hd hset1 hset2 hL hv hK hpref hset hspat

/-! ### Batch 84: Monotone Settlement Bound (`settleBound` / `SettledUpTo`), Settlement-Hypothesis-Free Prefix/Tail Reductions, and Single-Row Prefix+Tail Refutations of `CenterPeriodic` (9.1552–9.1566) -/

/-- Monotone settling bound `settleBound d := Rule30UOR.Intent.bound d`, dominating `settle j` for all `j ≤ d`. -/
noncomputable def settleBound (d : Nat) : Nat := Rule30UOR.Intent.bound d

/-- Uniform prefix settlement proposition `SettledUpTo D t : Prop := settleBound D ≤ t`, dominating `SettledBy d t` for all `d ≤ D`. -/
def SettledUpTo (D t : Nat) : Prop := settleBound D ≤ t

/-- **9.1552**: Uniform settlement of every diagonal `d ≤ D` once `SettledUpTo D t` (`settleBound D ≤ t`). -/
theorem settledBy_of_le_and_settleBound_le
    (D d t : Nat) (hdD : d ≤ D) (hbt : SettledUpTo D t) :
    SettledBy d t :=
  Nat.le_trans (Rule30UOR.Intent.settle_le_bound d)
    (Nat.le_trans (Rule30UOR.Intent.bound_mono d D hdD) hbt)

/-- **9.1553**: Settled `ldiag` periodicity below a doubling point `z` from `SettledUpTo z t`, with zero individual `SettledBy` hypotheses. -/
theorem ldiag_settled_periodic_of_doubles_le_settleBound
    (Q z d t : Nat) (hd : DoublesAt Q z) (hdz : d ≤ z) (hbt : SettledUpTo z t) :
    ldiag d (t + Q) = ldiag d t :=
  ldiag_settled_periodic_of_doubles_le Q z d t hd hdz
    (settledBy_of_le_and_settleBound_le z d t hdz hbt)

/-- **9.1554**: Diagonal-shift `Q`-periodicity of `lhCenter` below a doubling point `z` from `SettledUpTo z t`. -/
theorem lhCenter_diag_shift_periodic_of_doubles_le_settleBound
    (Q z t p : Nat) (hd : DoublesAt Q z) (hdz : t - p ≤ z) (hbt : SettledUpTo z t) :
    lhCenter (t + Q) (p + Q) = lhCenter t p :=
  lhCenter_diag_shift_periodic_of_doubles_le Q z t p hd hdz
    (settledBy_of_le_and_settleBound_le z (t - p) t hdz hbt)

/-- **9.1555**: Diagonal-shift `w * 2^e`-periodicity of `lhCenter` for `t - p ≤ e` from `SettledUpTo e t`. -/
theorem lhCenter_diag_shift_mul_twopow_periodic_le_settleBound
    (e w t p : Nat) (hde : t - p ≤ e) (hbt : SettledUpTo e t) :
    lhCenter (t + w * twopow e) (p + w * twopow e) = lhCenter t p :=
  lhCenter_diag_shift_mul_twopow_periodic_le e w t p hde
    (settledBy_of_le_and_settleBound_le e (t - p) t hde hbt)

/-- **9.1556**: `LhBandAgree t Q p0 L` from single-row spatial `Q`-periodicity and `SettledUpTo z t` (zero `SettledBy` hypotheses!). -/
theorem lhBandAgree_of_doubles_le_settleBound_and_single_lh_row_spatial_agree
    (Q z t p0 L : Nat) (hd : DoublesAt Q z) (hdz : t - p0 ≤ z) (hbt : SettledUpTo z t)
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (t + Q) (p0 + i) = lhCenter (t + Q) ((p0 + i) + Q)) :
    LhBandAgree t Q p0 L :=
  lhBandAgree_of_doubles_le_and_single_lh_row_spatial_agree Q z t p0 L hd hdz
    (fun i _ => settledBy_of_le_and_settleBound_le z (t - (p0 + i)) t (by omega) hbt)
    hspat

/-- **9.1557**: Prefix + single-row tail theorem for `LhBandAgree (z + (p + 1)) Q 1 S` under `SettledUpTo (z + 1) (z + (p + 1))` (zero `SettledBy` hypotheses!). -/
theorem lhBandAgree_one_at_zero_diag_of_doubles_settleBound_prefix_and_single_lh_row_tail
    (Q z p S : Nat) (hd : DoublesAt Q z) (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + Q) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + Q) (1 + i) = lhCenter ((z + (p + 1)) + Q) ((1 + i) + Q)) :
    LhBandAgree (z + (p + 1)) Q 1 S :=
  lhBandAgree_one_at_zero_diag_of_doubles_prefix_and_single_lh_row_tail Q z p S hd hpref
    (fun i hpi _ => settledBy_of_le_and_settleBound_le (z + 1) ((z + (p + 1)) - (1 + i)) (z + (p + 1)) (by omega) hbt)
    htail

/-- **9.1558**: Zero-diagonal refutation of `CenterPeriodic T P` from `LhBandAgree (z + (p + 1)) (m * P) 1 S` under `SettledUpTo (z + 1) (z + (p + 1))` (zero `SettledBy` hypotheses!). -/
theorem not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles_settleBound
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hband : LhBandAgree (z + (p + 1)) (m * P) 1 S) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles T P m z p S hP hm ht hz hd
    (settledBy_of_le_and_settleBound_le (z + 1) (z + 1) (z + (p + 1)) (by omega) hbt)
    (settledBy_of_le_and_settleBound_le (z + 1) ((z + 1) - m * P) (z + (p + 1)) (by omega) hbt)
    hS hband

/-- **9.1559**: Refutation of `CenterPeriodic T P` from the `p`-cell prefix and single-row tail spatial agreement under `SettledUpTo (z + 1) (z + (p + 1))` (zero `SettledBy` hypotheses!). -/
theorem not_centerPeriodic_of_doubles_settleBound_prefix_and_single_lh_row_tail_at_zero_diag
    (T P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter ((z + (p + 1)) + m * P) ((1 + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles_settleBound
    T P m z p S hP hm ht hz hd hbt hS
    (lhBandAgree_one_at_zero_diag_of_doubles_settleBound_prefix_and_single_lh_row_tail
      (m * P) z p S hd hbt hpref htail)

/-- **9.1560**: Refutation of `CenterPeriodic T P` with the tail embedded in a single right-half row `rhCenter (((z + (p + 1)) + m * P) + v * 2^K)` under `SettledUpTo (z + 1) (z + (p + 1))`. -/
theorem not_centerPeriodic_of_doubles_settleBound_prefix_and_single_rh_row_tail_at_zero_diag
    (T P m z p S K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + (p + 1)) + m * P) + ((1 + S) + m * P) ≤ K)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      rhCenter (((z + (p + 1)) + m * P) + v * twopow K) ((v * twopow K) - (1 + i)) =
      rhCenter (((z + (p + 1)) + m * P) + v * twopow K) ((v * twopow K) - ((1 + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_doubles_settleBound_prefix_and_single_lh_row_tail_at_zero_diag
    T P m z p S hP hm ht hz hd hbt hS hpref (fun i hpi hi => ?_)
  exact rhCenter_dyadic_left_shift_pair_eq_lhCenter_pair
    (z + (p + 1)) (m * P) K v (1 + i) hv (by omega) (htail i hpi hi)

/-- **9.1561**: Refutation of `CenterPeriodic T P` with the tail embedded in a single step `(z + (p + 1)) + m * P` of `rdrv td (v * 2^K)` under `SettledUpTo (z + 1) (z + (p + 1))`. -/
theorem not_centerPeriodic_of_doubles_settleBound_prefix_and_single_rdrv_row_tail_at_zero_diag
    (T P td m z p S K v : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hv : 1 ≤ v) (hK : ((z + (p + 1)) + m * P) + ((1 + S) + m * P) ≤ K)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      rdrv td (v * twopow K) ((z + (p + 1)) + m * P) ((v * twopow K) - (1 + i)) =
      rdrv td (v * twopow K) ((z + (p + 1)) + m * P) ((v * twopow K) - ((1 + i) + m * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  refine not_centerPeriodic_of_doubles_settleBound_prefix_and_single_lh_row_tail_at_zero_diag
    T P m z p S hP hm ht hz hd hbt hS hpref (fun i hpi hi => ?_)
  exact rdrv_dyadic_left_shift_pair_eq_lhCenter_pair
    td (z + (p + 1)) (m * P) K v (1 + i) hv (by omega) (htail i hpi hi)

/-- **9.1562**: Single-row `rhCenter (((z + (p + 1)) + u * 2^L) + w * 2^K)` prefix (`i < p`, requiring ONLY `(z + (p + 1)) + p ≤ K`!) + tail (`p ≤ i ≤ S`) theorem for `LhBandAgree (z + (p + 1)) (w * 2^K) 1 S`! -/
theorem lhBandAgree_one_at_zero_diag_of_two_scale_single_rh_row_prefix_and_tail_settleBound
    (z p S K L u w : Nat) (hd : DoublesAt (w * twopow K) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hu : 1 ≤ u) (hK : (z + (p + 1)) + p ≤ K)
    (hL : ((z + (p + 1)) + w * twopow K) + ((1 + S) + w * twopow K) ≤ L) (hKL : K ≤ L)
    (hpref : ∀ i : Nat, i < p →
      rhCenter (((z + (p + 1)) + u * twopow L) + w * twopow K) ((u * twopow L) - (1 + i)) =
      rhCenter (((z + (p + 1)) + u * twopow L) + w * twopow K) (((u * twopow L) + w * twopow K) - (1 + i)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      rhCenter (((z + (p + 1)) + u * twopow L) + w * twopow K) ((u * twopow L) - (1 + i)) =
      rhCenter (((z + (p + 1)) + u * twopow L) + w * twopow K) ((u * twopow L) - ((1 + i) + w * twopow K))) :
    LhBandAgree (z + (p + 1)) (w * twopow K) 1 S := by
  intro i hi
  by_cases hip : i < p
  · have h1 := rhCenter_dyadic_sub_shift_eq_lhCenter
      ((z + (p + 1)) + w * twopow K) L u (1 + i) 0 hu (by omega)
    simp only [Nat.add_zero] at h1
    rw [show ((z + (p + 1)) + w * twopow K) + u * twopow L =
      ((z + (p + 1)) + u * twopow L) + w * twopow K by omega] at h1
    have h2 := rhCenter_two_scale_row_left_eq_lhCenter
      (z + (p + 1)) K L u w (1 + i) hu hKL (by omega)
    rw [← h1, ← h2]
    exact hpref i hip
  · have hpi : p ≤ i := by omega
    have hrow : ((z + (p + 1)) + w * twopow K) + u * twopow L =
        ((z + (p + 1)) + u * twopow L) + w * twopow K := by omega
    have hpair := rhCenter_dyadic_left_shift_pair_eq_lhCenter_pair
      (z + (p + 1)) (w * twopow K) L u (1 + i) hu (by omega)
      (by simpa [hrow] using htail i hpi hi)
    rw [hpair]
    exact lhCenter_diag_shift_periodic_of_doubles_le (w * twopow K) z (z + (p + 1)) (1 + i) hd (by omega)
      (settledBy_of_le_and_settleBound_le (z + 1) ((z + (p + 1)) - (1 + i)) (z + (p + 1)) (by omega) hbt)

/-- **9.1563**: Single-row `rhCenter` prefix + tail refutation of `CenterPeriodic T P` with `(z + (p + 1)) + p ≤ K` (completely independent of `S` and `2^K`!) and zero `SettledBy` hypotheses! -/
theorem not_centerPeriodic_of_two_scale_single_rh_row_prefix_and_tail_settleBound
    (T P c z p S K L u : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : (z + (p + 1)) + p ≤ K)
    (hL : ((z + (p + 1)) + (c * twopow K) * P) + ((1 + S) + (c * twopow K) * P) ≤ L) (hKL : K ≤ L)
    (hpref : ∀ i : Nat, i < p →
      rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
      rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
      rhCenter (((z + (p + 1)) + u * twopow L) + (c * twopow K) * P) ((u * twopow L) - ((1 + i) + (c * twopow K) * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hgt : K < twopow K := twopow_gt_self K
  have hm : 0 < c * twopow K := Nat.mul_pos hc (by omega)
  have hmul : (c * twopow K) * P = (c * P) * twopow K := Nat.mul_right_comm c (twopow K) P
  refine not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles_settleBound
    T P (c * twopow K) z p S hP hm ht hz hd hbt hS ?_
  rw [hmul] at hd hL hpref htail ⊢
  exact lhBandAgree_one_at_zero_diag_of_two_scale_single_rh_row_prefix_and_tail_settleBound
    z p S K L u (c * P) hd hbt hu hK hL hKL hpref htail

/-- **9.1564**: Single-step `rdrv td (u * 2^L) ((z + (p + 1)) + w * 2^K)` prefix (`i < p`, requiring ONLY `(z + (p + 1)) + p ≤ K`!) + tail (`p ≤ i ≤ S`) theorem for `LhBandAgree (z + (p + 1)) (w * 2^K) 1 S`! -/
theorem lhBandAgree_one_at_zero_diag_of_two_scale_single_rdrv_row_prefix_and_tail_settleBound
    (td z p S K L u w : Nat) (hd : DoublesAt (w * twopow K) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hu : 1 ≤ u) (hK : (z + (p + 1)) + p ≤ K)
    (hL : ((z + (p + 1)) + w * twopow K) + ((1 + S) + w * twopow K) ≤ L) (hKL : K ≤ L)
    (hpref : ∀ i : Nat, i < p →
      rdrv td (u * twopow L) ((z + (p + 1)) + w * twopow K) ((u * twopow L) - (1 + i)) =
      rdrv td (u * twopow L) ((z + (p + 1)) + w * twopow K) (((u * twopow L) + w * twopow K) - (1 + i)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      rdrv td (u * twopow L) ((z + (p + 1)) + w * twopow K) ((u * twopow L) - (1 + i)) =
      rdrv td (u * twopow L) ((z + (p + 1)) + w * twopow K) ((u * twopow L) - ((1 + i) + w * twopow K))) :
    LhBandAgree (z + (p + 1)) (w * twopow K) 1 S := by
  intro i hi
  by_cases hip : i < p
  · have h1 := rdrv_dyadic_exact_row_shift_left_eq
      td L u (1 + i) ((z + (p + 1)) + w * twopow K) hu (by omega)
    have h2 := rdrv_two_scale_row_left_eq_lhCenter
      td (z + (p + 1)) K L u w (1 + i) hu hKL (by omega) (by omega)
    rw [← h1, ← h2]
    exact hpref i hip
  · have hpi : p ≤ i := by omega
    have hpair := rdrv_dyadic_left_shift_pair_eq_lhCenter_pair
      td (z + (p + 1)) (w * twopow K) L u (1 + i) hu (by omega) (htail i hpi hi)
    rw [hpair]
    exact lhCenter_diag_shift_periodic_of_doubles_le (w * twopow K) z (z + (p + 1)) (1 + i) hd (by omega)
      (settledBy_of_le_and_settleBound_le (z + 1) ((z + (p + 1)) - (1 + i)) (z + (p + 1)) (by omega) hbt)

/-- **9.1565**: Single-step `rdrv td (u * 2^L)` prefix + tail refutation of `CenterPeriodic T P` with `(z + (p + 1)) + p ≤ K` (completely independent of `S` and `2^K`!) and zero `SettledBy` hypotheses! -/
theorem not_centerPeriodic_of_two_scale_single_rdrv_row_prefix_and_tail_settleBound
    (T P td c z p S K L u : Nat) (hP : 0 < P) (hc : 0 < c)
    (ht : T ≤ z + (p + 1)) (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : (z + (p + 1)) + p ≤ K)
    (hL : ((z + (p + 1)) + (c * twopow K) * P) + ((1 + S) + (c * twopow K) * P) ≤ L) (hKL : K ≤ L)
    (hpref : ∀ i : Nat, i < p →
      rdrv td (u * twopow L) ((z + (p + 1)) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
      rdrv td (u * twopow L) ((z + (p + 1)) + (c * twopow K) * P) (((u * twopow L) + (c * twopow K) * P) - (1 + i)))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      rdrv td (u * twopow L) ((z + (p + 1)) + (c * twopow K) * P) ((u * twopow L) - (1 + i)) =
      rdrv td (u * twopow L) ((z + (p + 1)) + (c * twopow K) * P) ((u * twopow L) - ((1 + i) + (c * twopow K) * P))) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  have hgt : K < twopow K := twopow_gt_self K
  have hm : 0 < c * twopow K := Nat.mul_pos hc (by omega)
  have hmul : (c * twopow K) * P = (c * P) * twopow K := Nat.mul_right_comm c (twopow K) P
  refine not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles_settleBound
    T P (c * twopow K) z p S hP hm ht hz hd hbt hS ?_
  rw [hmul] at hd hL hpref htail ⊢
  exact lhBandAgree_one_at_zero_diag_of_two_scale_single_rdrv_row_prefix_and_tail_settleBound
    td z p S K L u (c * P) hd hbt hu hK hL hKL hpref htail

/-- **9.1566**: Late-scale `t = (z + 1) + 2^k` refutation of `CenterPeriodic T P` under `SettledUpTo (z + 1) ((z + 1) + 2^k)` (which ALWAYS holds for large `k`!), with scale-independent tail width `3 * (m * P) ≤ L + 1` and zero `SettledBy` hypotheses! -/
theorem not_centerPeriodic_of_late_scale_doubles_settleBound_prefix_and_single_lh_row_tail
    (T P m z L k : Nat) (hP : 0 < P) (hm : 0 < m)
    (ht : T ≤ (z + 1) + twopow k) (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hbt : SettledUpTo (z + 1) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + m * P) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + m * P) + twopow k) (((1 + twopow k) + i) + m * P)) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_late_scale_doubles_prefix_and_single_lh_row_tail
    T P m z L k hP hm ht hz hd
    (settledBy_of_le_and_settleBound_le (z + 1) (z + 1) ((z + 1) + twopow k) (by omega) hbt)
    (settledBy_of_le_and_settleBound_le (z + 1) ((z + 1) - m * P) ((z + 1) + twopow k) (by omega) hbt)
    hL hpref
    (fun i _ => settledBy_of_le_and_settleBound_le (z + 1) ((z + 1) - (1 + i)) ((z + 1) + twopow k) (by omega) hbt)
    hspat

/-! ### Batch 85: Single-Time Left-Band Refutation at Doubling Zero Diagonals, Unconditional Single-Row Spatial Non-Periodicity, and Signed Single-Row Characterizations on `z + 1`, `z + 2`, `z + 3` (9.1567–9.1581) -/

/-- **9.1567**: `SettledUpTo` is antitone in the diagonal bound: `D ≤ D'` and `SettledUpTo D' t` give `SettledUpTo D t`. -/
theorem settledUpTo_mono (D D' t : Nat) (hD : D ≤ D') (h : SettledUpTo D' t) :
    SettledUpTo D t :=
  Nat.le_trans (Rule30UOR.Intent.bound_mono D D' hD) h

/-- **9.1568**: For every diagonal bound `D` there is a time `t` with `SettledUpTo D t`. -/
theorem exists_settledUpTo (D : Nat) : ∃ t : Nat, SettledUpTo D t :=
  ⟨settleBound D, Nat.le_refl _⟩

/-- **9.1569**: Single-time refutation of `LhBandAgree t Q p0 L` at a doubling zero diagonal
    `z = t - (p + 1)` for every shift `Q ≥ 1`, whenever `p0 ≤ p + Q` and `(p + Q) + 2 * Q ≤ p0 + L`.
    No periodicity hypothesis and no second time slice: the band at time `t` propagates to
    `t + Q` by `lhBandAgree_steps`, contradicting `9.904`. -/
theorem not_lhBandAgree_of_doubles_single (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hset1 : SettledBy ((t - (p + 1)) + 1) t)
    (hsetQ : SettledBy (t - (p + Q)) t)
    (hp0 : p0 ≤ p + Q) (hL : (p + Q) + 2 * Q ≤ p0 + L) :
    ¬ LhBandAgree t Q p0 L := by
  intro hband
  have hL' : LhBandAgree t Q p0 ((L - 2 * Q) + 2 * Q) := by
    intro i hi
    exact hband i (by omega)
  have h1 := lhBandAgree_steps t Q p0 (L - 2 * Q) Q hL'
  exact not_lhBandAgree_step_Q_of_doubles Q t p p0 L (p0 + Q) (L - 2 * Q) hQ hz hd hset1 hsetQ
    hp0 (by omega) (by omega) (by omega) hband h1

/-- **9.1570**: `9.1569` with both settlement hypotheses replaced by `SettledUpTo ((t - (p + 1)) + 1) t`. -/
theorem not_lhBandAgree_of_doubles_settledUpTo (Q t p p0 L : Nat)
    (hQ : 1 ≤ Q)
    (hz : IsZeroDiag (t - (p + 1))) (hd : DoublesAt Q (t - (p + 1)))
    (hbt : SettledUpTo ((t - (p + 1)) + 1) t)
    (hp0 : p0 ≤ p + Q) (hL : (p + Q) + 2 * Q ≤ p0 + L) :
    ¬ LhBandAgree t Q p0 L :=
  not_lhBandAgree_of_doubles_single Q t p p0 L hQ hz hd
    (settledBy_of_le_and_settleBound_le ((t - (p + 1)) + 1) ((t - (p + 1)) + 1) t (Nat.le_refl _) hbt)
    (settledBy_of_le_and_settleBound_le ((t - (p + 1)) + 1) (t - (p + Q)) t (by omega) hbt)
    hp0 hL

/-- **9.1571**: Column-`1` specialization: at `t = z + (p + 1)` with `IsZeroDiag z`, `DoublesAt Q z`,
    `1 ≤ Q`, `SettledUpTo (z + 1) (z + (p + 1))` and `p + 3 * Q ≤ S + 1`, `¬ LhBandAgree (z + (p + 1)) Q 1 S`.
    This is exactly the band (with exactly the horizon) consumed by the zero-diagonal engines `9.905`ff,
    so those engines refute it with no use of `CenterPeriodic`. -/
theorem not_lhBandAgree_one_at_zero_diag_of_doubles_settledUpTo (Q z p S : Nat)
    (hQ : 1 ≤ Q) (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * Q ≤ S + 1) :
    ¬ LhBandAgree (z + (p + 1)) Q 1 S :=
  not_lhBandAgree_of_doubles_settledUpTo Q (z + (p + 1)) p 1 S hQ
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rw [show (z + (p + 1)) - (p + 1) = z by omega]; exact hbt)
    (by omega) (by omega)

/-- **9.1572**: Unconditional single-row spatial non-periodicity: at a doubling zero diagonal `z`
    (`IsZeroDiag z`, `DoublesAt Q z`, `1 ≤ Q`) and `SettledUpTo (z + 1) (z + (p + 1))`, row
    `(z + (p + 1)) + Q` of the left half has a cell `(p + Q) + i` (`i ≤ 2 * Q`) whose `Q`-shift disagrees. -/
theorem exists_lh_row_spatial_disagree_of_doubles_settledUpTo (Q z p : Nat)
    (hQ : 1 ≤ Q) (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1))) :
    ∃ i : Nat, i ≤ 2 * Q ∧
      lhCenter ((z + (p + 1)) + Q) ((p + Q) + i) =
        !lhCenter ((z + (p + 1)) + Q) (((p + Q) + i) + Q) := by
  refine Decidable.byContradiction (fun hne => ?_)
  have hspat : ∀ i : Nat, i ≤ 2 * Q →
      lhCenter ((z + (p + 1)) + Q) ((p + Q) + i) =
        lhCenter ((z + (p + 1)) + Q) (((p + Q) + i) + Q) := by
    intro i hi
    cases ha : lhCenter ((z + (p + 1)) + Q) ((p + Q) + i) <;>
      cases hb : lhCenter ((z + (p + 1)) + Q) (((p + Q) + i) + Q)
    · rfl
    · exact (hne ⟨i, hi, by rw [ha, hb]; rfl⟩).elim
    · exact (hne ⟨i, hi, by rw [ha, hb]; rfl⟩).elim
    · rfl
  have hband := lhBandAgree_of_doubles_le_settleBound_and_single_lh_row_spatial_agree
    Q z (z + (p + 1)) (p + Q) (2 * Q) hd (by omega)
    (settledUpTo_mono z (z + 1) (z + (p + 1)) (by omega) hbt) hspat
  exact not_lhBandAgree_of_doubles_settledUpTo Q (z + (p + 1)) p (p + Q) (2 * Q) hQ
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rw [show (z + (p + 1)) - (p + 1) = z by omega]; exact hbt)
    (Nat.le_refl _) (by omega) hband

/-- **9.1573**: For every shift `Q ≥ 1` and every time bound `N`, some row `r ≥ N` of the left half
    has a cell whose spatial `Q`-shift disagrees, inside a window of `2 * Q + 1` cells. -/
theorem exists_lh_row_spatial_disagree_ge (Q N : Nat) (hQ : 1 ≤ Q) :
    ∃ r : Nat, ∃ c : Nat, ∃ i : Nat, N ≤ r ∧ i ≤ 2 * Q ∧
      lhCenter r (c + i) = !lhCenter r ((c + i) + Q) := by
  obtain ⟨z, hz, hd⟩ := Rule30UOR.CompilePoints.doubling_points Q (by omega)
  obtain ⟨t0, ht0⟩ := exists_settledUpTo (z + 1)
  have h0 : settleBound (z + 1) ≤ t0 := ht0
  obtain ⟨i, hi, hdis⟩ := exists_lh_row_spatial_disagree_of_doubles_settledUpTo Q z (t0 + N) hQ hz hd
    (Nat.le_trans h0 (by omega))
  exact ⟨(z + ((t0 + N) + 1)) + Q, (t0 + N) + Q, i, by omega, hi, hdis⟩

/-- **9.1574**: If the diagonal shift by `Q` flips the cell `(t, x)`, then vertical `Q`-agreement at
    column `x` is equivalent to single-row spatial `Q`-antiagreement in row `t + Q`. -/
theorem lhCenter_shift_agree_iff_spatial_antiagree_of_diag_flip (Q t x : Nat)
    (h : lhCenter (t + Q) (x + Q) = !lhCenter t x) :
    lhCenter (t + Q) x = lhCenter t x ↔
      lhCenter (t + Q) x = !lhCenter (t + Q) (x + Q) := by
  rw [h, Bool.not_not]

/-- **9.1575**: If the diagonal shift by `Q` preserves the cell `(t, x)`, then vertical `Q`-agreement at
    column `x` is equivalent to single-row spatial `Q`-agreement in row `t + Q`. -/
theorem lhCenter_shift_agree_iff_spatial_agree_of_diag_eq (Q t x : Nat)
    (h : lhCenter (t + Q) (x + Q) = lhCenter t x) :
    lhCenter (t + Q) x = lhCenter t x ↔
      lhCenter (t + Q) x = lhCenter (t + Q) (x + Q) := by
  rw [h]

/-- **9.1576**: Signed single-row characterization on the doubling diagonal `z + 1`. -/
theorem lhCenter_shift_agree_iff_spatial_antiagree_on_doubling_diag (Q z c : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) ((z + 1) + c)) :
    lhCenter (((z + 1) + c) + Q) c = lhCenter ((z + 1) + c) c ↔
      lhCenter (((z + 1) + c) + Q) c = !lhCenter (((z + 1) + c) + Q) (c + Q) :=
  lhCenter_shift_agree_iff_spatial_antiagree_of_diag_flip Q ((z + 1) + c) c
    (lhCenter_diag_shift_antiperiodic_at_t_of_doubles Q ((z + 1) + c) c
      (by rwa [show ((z + 1) + c) - (c + 1) = z by omega])
      (by rwa [show ((z + 1) + c) - (c + 1) = z by omega])
      (by
        rw [show ((z + 1) + c) - (c + 1) = z by omega]
        exact settledBy_of_le_and_settleBound_le (z + 1) (z + 1) ((z + 1) + c) (Nat.le_refl _) hbt))

/-- **9.1577**: Signed single-row characterization on the post-zero black diagonal `z + 2`. -/
theorem lhCenter_shift_agree_iff_spatial_agree_on_black_diag (Q z c : Nat)
    (hz : IsZeroDiag z)
    (hbt : SettledUpTo (z + 2) ((z + 2) + c)) :
    lhCenter (((z + 2) + c) + Q) c = lhCenter ((z + 2) + c) c ↔
      lhCenter (((z + 2) + c) + Q) c = lhCenter (((z + 2) + c) + Q) (c + Q) := by
  have hs0 : settle (z + 2) ≤ (z + 2) + c :=
    settledBy_of_le_and_settleBound_le (z + 2) (z + 2) ((z + 2) + c) (Nat.le_refl _) hbt
  have hs1 : settle (z + 2) ≤ ((z + 2) + c) + Q := by omega
  refine lhCenter_shift_agree_iff_spatial_agree_of_diag_eq Q ((z + 2) + c) c ?_
  rw [lhCenter_eq_ldiag (((z + 2) + c) + Q) (c + Q) (by omega),
    lhCenter_eq_ldiag ((z + 2) + c) c (by omega),
    show (((z + 2) + c) + Q) - (c + Q) = z + 2 by omega,
    show ((z + 2) + c) - c = z + 2 by omega,
    ldiag_after_zero_diag z (((z + 2) + c) + Q) hz hs1,
    ldiag_after_zero_diag z ((z + 2) + c) hz hs0]

/-- **9.1578**: Signed single-row characterization on the post-black reset diagonal `z + 3`. -/
theorem lhCenter_shift_agree_iff_spatial_antiagree_on_reset_diag (Q z c : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 3) ((z + 3) + c)) :
    lhCenter (((z + 3) + c) + Q) c = lhCenter ((z + 3) + c) c ↔
      lhCenter (((z + 3) + c) + Q) c = !lhCenter (((z + 3) + c) + Q) (c + Q) := by
  have hs0 : settle (z + 3) ≤ (z + 3) + c :=
    settledBy_of_le_and_settleBound_le (z + 3) (z + 3) ((z + 3) + c) (Nat.le_refl _) hbt
  refine lhCenter_shift_agree_iff_spatial_antiagree_of_diag_flip Q ((z + 3) + c) c ?_
  rw [lhCenter_eq_ldiag (((z + 3) + c) + Q) (c + Q) (by omega),
    lhCenter_eq_ldiag ((z + 3) + c) c (by omega),
    show (((z + 3) + c) + Q) - (c + Q) = z + 3 by omega,
    show ((z + 3) + c) - c = z + 3 by omega]
  exact ldiag_settled_reset_antiperiodic_of_doubles Q z ((z + 3) + c) hz hd hs0

/-- **9.1579**: Signed single-row characterization below a doubling point: on every diagonal `t - c ≤ z`. -/
theorem lhCenter_shift_agree_iff_spatial_agree_below_doubling (Q z t c : Nat)
    (hd : DoublesAt Q z) (hdz : t - c ≤ z) (hbt : SettledUpTo z t) :
    lhCenter (t + Q) c = lhCenter t c ↔
      lhCenter (t + Q) c = lhCenter (t + Q) (c + Q) :=
  lhCenter_shift_agree_iff_spatial_agree_of_diag_eq Q t c
    (lhCenter_diag_shift_periodic_of_doubles_le_settleBound Q z t c hd hdz hbt)

/-- **9.1580**: Doubled diagonal-shift periodicity through `z + 3`: for `c ≤ t`, `t - c ≤ z + 3`,
    `lhCenter (t + (Q + Q)) (c + (Q + Q)) = lhCenter t c`. -/
theorem lhCenter_diag_shift_two_mul_periodic_le_add_three_of_doubles (Q z t c : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hct : c ≤ t) (hdz : t - c ≤ z + 3) (hbt : SettledUpTo (z + 3) t) :
    lhCenter (t + (Q + Q)) (c + (Q + Q)) = lhCenter t c := by
  rw [lhCenter_eq_ldiag (t + (Q + Q)) (c + (Q + Q)) (by omega),
    lhCenter_eq_ldiag t c hct,
    show (t + (Q + Q)) - (c + (Q + Q)) = t - c by omega]
  exact ldiag_settled_two_mul_periodic_le_add_three_of_doubles Q z (t - c) t hz hd hdz
    (settledBy_of_le_and_settleBound_le (z + 3) (t - c) t hdz hbt)

/-- **9.1581**: `LhBandAgree t (Q + Q) p0 L` from single-row spatial `(Q + Q)`-agreement of row
    `t + (Q + Q)` on `[p0, p0 + L]`, whenever the window lies in `t - (p0 + i) ≤ z + 3` with `p0 + L ≤ t`. -/
theorem lhBandAgree_two_mul_of_doubles_and_single_lh_row_spatial_agree (Q z t p0 L : Nat)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hdz : t - p0 ≤ z + 3) (hpL : p0 + L ≤ t) (hbt : SettledUpTo (z + 3) t)
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (t + (Q + Q)) (p0 + i) = lhCenter (t + (Q + Q)) ((p0 + i) + (Q + Q))) :
    LhBandAgree t (Q + Q) p0 L := by
  intro i hi
  rw [hspat i hi]
  exact lhCenter_diag_shift_two_mul_periodic_le_add_three_of_doubles Q z t (p0 + i) hz hd
    (by omega) (by omega) hbt

/-! ### Batch 86: Audit Theorems — Unsatisfiability of the Left-Band Engine Hypotheses and Exact Equivalence of the Engine Input with Problem 1 (9.1582–9.1587) -/

/-- **9.1582 (audit)**: The hypothesis bundle of `not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles`
    (everything except `CenterPeriodic` and `T ≤ z + (p + 1)`) is unsatisfiable. That engine's conclusion
    therefore follows from `False`; its `CenterPeriodic` hypothesis carries no information. -/
theorem lhBandAgree_engine_hypotheses_unsat (P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) (z + (p + 1)))
    (hset2 : SettledBy ((z + 1) - m * P) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (h : LhBandAgree (z + (p + 1)) (m * P) 1 S) : False := by
  have hmP : 0 < m * P := Nat.mul_pos hm hP
  exact not_lhBandAgree_of_doubles_single (m * P) (z + (p + 1)) p 1 S (by omega)
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
    (by rw [show (z + (p + 1)) - (p + 1) = z by omega]; exact hset1)
    (by rw [show (z + (p + 1)) - (p + m * P) = (z + 1) - m * P by omega]; exact hset2)
    (by omega) (by omega) h

/-- **9.1583 (audit)**: The hypothesis bundle of the prefix/tail refutation `9.1559` (minus `CenterPeriodic`
    and the time bound) is unsatisfiable. -/
theorem prefix_tail_engine_hypotheses_unsat (P m z p S : Nat) (hP : 0 < P) (hm : 0 < m)
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * (m * P) ≤ S + 1)
    (hpref : ∀ i : Nat, i < p →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter (z + (p + 1)) (1 + i))
    (htail : ∀ i : Nat, p ≤ i → i ≤ S →
      lhCenter ((z + (p + 1)) + m * P) (1 + i) = lhCenter ((z + (p + 1)) + m * P) ((1 + i) + m * P)) :
    False := by
  have hmP : 0 < m * P := Nat.mul_pos hm hP
  exact not_lhBandAgree_one_at_zero_diag_of_doubles_settledUpTo (m * P) z p S (by omega) hz hd hbt hS
    (lhBandAgree_one_at_zero_diag_of_doubles_settleBound_prefix_and_single_lh_row_tail
      (m * P) z p S hd hbt hpref htail)

/-- **9.1584 (audit)**: The hypothesis bundle of the late-scale refutation
    `not_centerPeriodic_of_late_scale_doubles_prefix_and_single_lh_row_tail` (minus `CenterPeriodic`
    and the time bound) is unsatisfiable. -/
theorem late_scale_engine_hypotheses_unsat (P m z L k : Nat) (hP : 0 < P) (hm : 0 < m)
    (hz : IsZeroDiag z) (hd : DoublesAt (m * P) z)
    (hset1 : SettledBy (z + 1) ((z + 1) + twopow k))
    (hset2 : SettledBy ((z + 1) - m * P) ((z + 1) + twopow k))
    (hL : 3 * (m * P) ≤ L + 1)
    (hpref : ∀ i : Nat, i < twopow k →
      lhCenter (((z + 1) + twopow k) + m * P) (1 + i) = lhCenter ((z + 1) + twopow k) (1 + i))
    (hset : ∀ i : Nat, i ≤ L → SettledBy ((z + 1) - (1 + i)) ((z + 1) + twopow k))
    (hspat : ∀ i : Nat, i ≤ L →
      lhCenter (((z + 1) + m * P) + twopow k) ((1 + twopow k) + i) =
      lhCenter (((z + 1) + m * P) + twopow k) (((1 + twopow k) + i) + m * P)) :
    False := by
  have hmP : 0 < m * P := Nat.mul_pos hm hP
  have hband := lhBandAgree_one_late_scale_at_zero_diag_succ_of_doubles_prefix_and_single_lh_row_tail
    (m * P) z L k hd hpref hset hspat
  exact not_lhBandAgree_of_doubles_single (m * P) ((z + 1) + twopow k) (twopow k) 1 (twopow k + L)
    (by omega)
    (by rwa [show ((z + 1) + twopow k) - (twopow k + 1) = z by omega])
    (by rwa [show ((z + 1) + twopow k) - (twopow k + 1) = z by omega])
    (by rw [show ((z + 1) + twopow k) - (twopow k + 1) = z by omega]; exact hset1)
    (by rw [show ((z + 1) + twopow k) - (twopow k + m * P) = (z + 1) - m * P by omega]; exact hset2)
    (by omega) (by omega) hband

/-- **9.1585 (audit)**: The hypothesis bundle of the single-row refutation at `t = z + 1` (Batch 81)
    is unsatisfiable whenever `3 * Q ≤ S + 1`. -/
theorem single_row_zero_diag_succ_engine_hypotheses_unsat (Q z S : Nat) (hQ : 1 ≤ Q)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hset1 : SettledBy (z + 1) (z + 1))
    (hset2 : SettledBy ((z + 1) - Q) (z + 1))
    (hS : 3 * Q ≤ S + 1)
    (hset : ∀ i : Nat, i ≤ S → SettledBy ((z + 1) - (1 + i)) (z + 1))
    (hspat : ∀ i : Nat, i ≤ S →
      lhCenter ((z + 1) + Q) (1 + i) = lhCenter ((z + 1) + Q) ((1 + i) + Q)) :
    False :=
  not_lhBandAgree_of_doubles_single Q (z + 1) 0 1 S hQ
    (by rwa [show (z + 1) - (0 + 1) = z by omega])
    (by rwa [show (z + 1) - (0 + 1) = z by omega])
    (by rw [show (z + 1) - (0 + 1) = z by omega]; exact hset1)
    (by rw [show (z + 1) - (0 + Q) = (z + 1) - Q by omega]; exact hset2)
    (by omega) (by omega)
    (lhBandAgree_one_at_zero_diag_succ_of_doubles_and_single_lh_row_spatial_agree Q z S hd hset hspat)

/-- **9.1586 (audit)**: Period by period, the engine input — "a `P`-periodic center yields column-`1`
    agreement on a window after a doubling zero diagonal" — is equivalent to excluding period `P`. -/
theorem engine_input_iff_not_centerPeriodic (T P : Nat) (hP : 0 < P) :
    (Rule30UOR.Scale.CenterPeriodic T P →
      ∃ m z p S : Nat, 0 < m ∧ T ≤ z + (p + 1) ∧ IsZeroDiag z ∧ DoublesAt (m * P) z ∧
        SettledBy (z + 1) (z + (p + 1)) ∧ SettledBy ((z + 1) - m * P) (z + (p + 1)) ∧
        p + 3 * (m * P) ≤ S + 1 ∧ RhColAgree (z + (p + 1)) (m * P) 1 S) ↔
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  constructor
  · intro h hc
    obtain ⟨m, z, p, S, hm, ht, hz, hd, hs1, hs2, hS, hrc⟩ := h hc
    exact not_periodic_rhColAgree_one_of_doubles T P hP hc m (z + (p + 1)) p S hm ht
      (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
      (by rwa [show (z + (p + 1)) - (p + 1) = z by omega])
      (by rw [show (z + (p + 1)) - (p + 1) = z by omega]; exact hs1)
      (by rw [show (z + (p + 1)) - (p + m * P) = (z + 1) - m * P by omega]; exact hs2)
      hS hrc
  · intro hn hc
    exact absurd hc hn

/-- **9.1587 (audit)**: Problem 1 is equivalent to the engine input holding for every period. The
    missing step of the zero-diagonal program is therefore Problem 1 itself, not a weaker lemma. -/
theorem problem1_iff_engine_input :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔
      ∀ T P : Nat, 0 < P → Rule30UOR.Scale.CenterPeriodic T P →
        ∃ m z p S : Nat, 0 < m ∧ T ≤ z + (p + 1) ∧ IsZeroDiag z ∧ DoublesAt (m * P) z ∧
          SettledBy (z + 1) (z + (p + 1)) ∧ SettledBy ((z + 1) - m * P) (z + (p + 1)) ∧
          p + 3 * (m * P) ≤ S + 1 ∧ RhColAgree (z + (p + 1)) (m * P) 1 S := by
  rw [Rule30UOR.Scale.problem1_iff]
  constructor
  · intro h T P hP
    exact (engine_input_iff_not_centerPeriodic T P hP).mpr (h T P hP)
  · intro h T P hP
    exact (engine_input_iff_not_centerPeriodic T P hP).mp (h T P hP)

end Rule30UOR.Interfaces
