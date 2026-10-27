module

public import Rule30Equivalents.Holonomic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Problem 1 ⟺ the generating series of the center column is not D-finite

A power series `F` over `ℚ` is *D-finite* (differentiably finite) when it satisfies a linear
differential equation `∑_{i ≤ r} q_i(X) · F^{(i)} = 0` with polynomial coefficients `q_i ∈ ℚ[X]`,
not all zero. Equivalently, the coefficients `q_i` may be rational functions: clear the
denominators.

* `coeff_D`: the coefficient of `X^n` in `F^{(i)}` is `F_{n+i} · (n + 1)(n + 2)⋯(n + i)`.
* `dFinite_of_eventuallyPeriodic`: an eventually periodic `b` has a rational generating series
  `G / H` (`LinearRelations.exists_mul_eq_of_eventuallyPeriodic`), which solves
  `H G · F' − (G' H − G H') · F = 0`.
* `eventuallyPeriodic_of_dFinite`: conversely, let `i₀` be the largest order with `q_{i₀} ≠ 0` and
  `K` a bound on the degrees of the `q_i`. Coefficient `t + K` of the equation is
  `∑_i ∑_{m ≤ K} q_{i, K-m} · (t + m + 1)⋯(t + m + i) · b(t + m + i) = 0`, a polynomial in `t`
  once the window `b(t), …, b(t + K + r)` is fixed. A window that recurs makes that polynomial
  vanish at infinitely many `t`, so it is `0`; its coefficient of `t^{i₀}` is
  `∑_{m ≤ K} q_{i₀, K-m} · b(t + i₀ + m)`. That is a constant-coefficient relation, not all zero, and
  `LinearRelations.eventuallyPeriodic_of_relation'` gives eventual periodicity.
* `problem1_iff_not_dFinite`.

This is Stanley's equivalence of D-finite series and P-recursive sequences, specialized to bit
sequences, where both are equivalent to eventual periodicity (`Holonomic`).

Sources: R. P. Stanley, *Differentiably finite power series*, European J. Combin. 1 (1980)
175–188; A. J. van der Poorten and I. E. Shparlinski, *On linear recurrence sequences with
polynomial coefficients*, Glasgow Math. J. 38 (1996) 147–155.
-/

@[expose] public section

namespace Rule30Equivalents.DFinite

open Ruliology.CellularAutomata Polynomial LinearRelations

/-- The `i`-th derivative of a power series over `ℚ`. -/
noncomputable def D (i : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (⇑(PowerSeries.derivative (R := ℚ)))^[i] f

/-- **Coefficients of the `i`-th derivative**: `[X^n] F^{(i)} = F_{n+i} · (n + 1)⋯(n + i)`. -/
theorem coeff_D (f : PowerSeries ℚ) : ∀ (i n : ℕ),
    PowerSeries.coeff n (D i f) = PowerSeries.coeff (n + i) f * ((n + 1).ascFactorial i : ℚ)
  | 0, n => by simp [D]
  | i + 1, n => by
    show PowerSeries.coeff n (D i (PowerSeries.derivative (R := ℚ) f)) = _
    rw [coeff_D _ i n, PowerSeries.coeff_derivative, Nat.ascFactorial_succ,
      show n + i + 1 = n + (i + 1) by omega]
    push_cast
    ring

/-- For `K` at least the degree of `q`, coefficient `t + K` of `q · φ`. -/
theorem coeff_coe_mul_add {q : ℚ[X]} {K : ℕ} (hK : q.natDegree ≤ K) (φ : PowerSeries ℚ)
    (t : ℕ) :
    PowerSeries.coeff (t + K) ((q : PowerSeries ℚ) * φ) =
      ∑ m ∈ Finset.range (K + 1), q.coeff (K - m) * PowerSeries.coeff (t + m) φ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (q : PowerSeries ℚ) * PowerSeries.coeff j φ),
    show (t + K).succ = (K + 1) + t by omega, Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range t, PowerSeries.coeff (K + 1 + x) (q : PowerSeries ℚ) *
      PowerSeries.coeff (t + K - (K + 1 + x)) φ = 0 :=
    Finset.sum_eq_zero fun x _ => by
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rw [hz, add_zero, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Polynomial.coeff_coe, show K + 1 - 1 - m = K - m by omega,
    show t + K - (K - m) = t + m by omega]

/-- `b`'s generating series over `ℚ` is **D-finite**: it satisfies a linear differential equation
with polynomial coefficients, not all zero. -/
def IsDFinite (b : ℕ → Bool) : Prop :=
  ∃ (r : ℕ) (q : Fin (r + 1) → ℚ[X]), (∃ i, q i ≠ 0) ∧
    ∑ i : Fin (r + 1), (q i : PowerSeries ℚ) * D i (series ℚ b) = 0

/-- **Eventually periodic ⟹ D-finite.** The generating series is `G / H`, and it solves
`H G · F' − (G' H − G H') · F = 0`. -/
theorem dFinite_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) : IsDFinite b := by
  obtain ⟨P, Q, hQ0, hQF⟩ := exists_mul_eq_of_eventuallyPeriodic (K := ℚ) h
  have hQ : Q ≠ 0 := fun h0 => hQ0 (by rw [h0, Polynomial.coeff_zero])
  by_cases hP : P = 0
  · -- the series is zero
    have hF : series ℚ b = 0 := by
      rw [hP, Polynomial.coe_zero] at hQF
      rcases mul_eq_zero.1 hQF with h1 | h1
      · exact absurd (Polynomial.coe_eq_zero_iff.1 h1) hQ
      · exact h1
    refine ⟨0, fun _ => 1, ⟨0, one_ne_zero⟩, ?_⟩
    simp [D, hF]
  · refine ⟨1, ![-(derivative P * Q - P * derivative Q), P * Q], ⟨1, by simp [hP, hQ]⟩, ?_⟩
    have hd := congrArg (PowerSeries.derivative (R := ℚ)) hQF
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, PowerSeries.derivative_coe,
      PowerSeries.derivative_coe] at hd
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [D, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
      Function.iterate_zero, id_eq, zero_add, Function.iterate_one, add_zero, Polynomial.coe_mul,
      Polynomial.coe_sub, Polynomial.coe_neg]
    linear_combination (P : PowerSeries ℚ) * hd - ((derivative P : ℚ[X]) : PowerSeries ℚ) * hQF

/-- **D-finite ⟹ eventually periodic.** -/
theorem eventuallyPeriodic_of_dFinite {b : ℕ → Bool} (h : IsDFinite b) : EventuallyPeriodic b := by
  classical
  obtain ⟨r, q, hq, hsum⟩ := h
  -- the top order with a nonzero coefficient
  let S := Finset.univ.filter fun i : Fin (r + 1) => q i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hq
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  set i₀ := S.max' hS with hi₀def
  have hi₀ : q i₀ ≠ 0 := (Finset.mem_filter.1 (S.max'_mem hS)).2
  have htop : ∀ i, i₀ < i → q i = 0 := fun i hi => by
    by_contra hne
    exact absurd (S.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)) (not_le.2 hi)
  -- a common degree bound
  set K := Finset.univ.sup fun i => (q i).natDegree with hKdef
  have hK : ∀ i, (q i).natDegree ≤ K := fun i =>
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ i)
  -- coefficient `t + K` of the equation
  have hrel : ∀ t, ∑ i : Fin (r + 1), ∑ m ∈ Finset.range (K + 1),
      (q i).coeff (K - m) * (toK ℚ b (t + m + i) * ((t + m + 1).ascFactorial i : ℚ)) = 0 := by
    intro t
    have := congrArg (PowerSeries.coeff (t + K)) hsum
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_coe_mul_add (hK i)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_D, coeff_series]
  -- windows of length `K + r + 1` recur from some point on
  let W : ℕ → (Fin (K + r + 1) → Bool) := fun t j => b (t + j)
  obtain ⟨N', -, hrec⟩ := Holonomic.eventually_recurrent W 0
  -- the coefficient of `t ^ i₀` gives a constant-coefficient relation
  have hconst : ∀ n, N' ≤ n →
      ∑ m ∈ Finset.range (K + 1), (q i₀).coeff (K - m) * toK ℚ b (n + i₀ + m) = 0 := by
    intro n hn
    let Pn : ℚ[X] := ∑ i : Fin (r + 1), ∑ m ∈ Finset.range (K + 1),
      C ((q i).coeff (K - m) * toK ℚ b (n + m + i)) *
        (ascPochhammer ℚ (i : ℕ)).comp (X + C ((m : ℚ) + 1))
    have hroot : ∀ t, W t = W n → Pn.IsRoot (t : ℚ) := by
      intro t hW
      simp only [IsRoot, Pn, eval_finsetSum, eval_mul, eval_C, eval_comp, eval_add, eval_X]
      rw [← hrel t]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      have hb : b (n + m + i) = b (t + m + i) := by
        have := congrFun hW ⟨m + i, by omega⟩
        simp only [W] at this
        rw [show n + m + i = n + (m + i) by omega, show t + m + i = t + (m + i) by omega]
        exact this.symm
      have hasc : (ascPochhammer ℚ (i : ℕ)).eval ((t : ℚ) + ((m : ℚ) + 1)) =
          ((t + m + 1).ascFactorial i : ℚ) := by
        rw [← ascPochhammer_nat_eq_ascFactorial, ascPochhammer_eval_cast]
        push_cast
        ring_nf
      rw [hasc, toK, toK, hb]
      ring
    have hinf : Set.Infinite {x : ℚ | Pn.IsRoot x} := by
      refine Set.infinite_of_not_bddAbove fun ⟨a, ha⟩ => ?_
      obtain ⟨m, hm, hWm⟩ := hrec n hn (⌈a⌉.toNat + 1)
      have hle := ha (hroot m hWm)
      have h1 : (⌈a⌉.toNat : ℚ) + 1 ≤ m := by exact_mod_cast hm
      have h2 : a ≤ (⌈a⌉.toNat : ℚ) := by
        have := Int.le_ceil a
        have h3 : ((⌈a⌉ : ℤ) : ℚ) ≤ ((⌈a⌉.toNat : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
        push_cast at h3
        linarith
      linarith
    have hPn := Polynomial.eq_zero_of_infinite_isRoot Pn hinf
    have hcoeff := congrArg (fun P : ℚ[X] => P.coeff (i₀ : ℕ)) hPn
    simp only [Pn, finsetSum_coeff, coeff_C_mul, coeff_zero] at hcoeff
    rw [Finset.sum_eq_single i₀ (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)]
      at hcoeff
    · rw [← hcoeff]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hmon : ((ascPochhammer ℚ (i₀ : ℕ)).comp (X + C ((m : ℚ) + 1))).coeff (i₀ : ℕ) = 1 := by
        have hM := (monic_ascPochhammer ℚ (i₀ : ℕ)).comp_X_add_C ((m : ℚ) + 1)
        have hdeg : ((ascPochhammer ℚ (i₀ : ℕ)).comp (X + C ((m : ℚ) + 1))).natDegree = i₀ := by
          rw [natDegree_comp, ascPochhammer_natDegree, natDegree_X_add_C, Nat.mul_one]
        have := hM.coeff_natDegree
        rwa [hdeg] at this
      rw [hmon, mul_one, show n + m + (i₀ : ℕ) = n + i₀ + m by omega]
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine Finset.sum_eq_zero fun m _ => ?_
        have hdeg : ((ascPochhammer ℚ (i : ℕ)).comp (X + C ((m : ℚ) + 1))).natDegree = i := by
          rw [natDegree_comp, ascPochhammer_natDegree, natDegree_X_add_C, Nat.mul_one]
        rw [coeff_eq_zero_of_natDegree_lt (p := (ascPochhammer ℚ (i : ℕ)).comp (X + C ((m : ℚ) + 1)))
          (n := (i₀ : ℕ)) (by rw [hdeg]; exact hlt), mul_zero]
      · refine Finset.sum_eq_zero fun m _ => ?_
        rw [htop i hgt, Polynomial.coeff_zero, zero_mul, zero_mul]
  -- the relation has a nonzero coefficient: the leading one of `q i₀`
  have hdeg₀ := hK i₀
  refine eventuallyPeriodic_of_relation' (K := ℚ) (a := fun m => (q i₀).coeff (K - m))
    (N := K + 1) (T := N' + i₀) ⟨K - (q i₀).natDegree, by omega, ?_⟩ (fun t ht => ?_)
  · show (q i₀).coeff (K - (K - (q i₀).natDegree)) ≠ 0
    rw [show K - (K - (q i₀).natDegree) = (q i₀).natDegree by omega]
    exact leadingCoeff_ne_zero.2 hi₀
  · have := hconst (t - i₀) (by omega)
    rwa [show t - (i₀ : ℕ) + (i₀ : ℕ) = t by omega] at this

/-- **A bit sequence is eventually periodic iff its generating series is D-finite.** -/
theorem eventuallyPeriodic_iff_dFinite (b : ℕ → Bool) : EventuallyPeriodic b ↔ IsDFinite b :=
  ⟨dFinite_of_eventuallyPeriodic, eventuallyPeriodic_of_dFinite⟩

/-- **Problem 1 ⟺ `∑ c(t) Xᵗ` is not D-finite over `ℚ(X)`**: no
linear differential equation with polynomial coefficients, not all zero, holds for it. -/
theorem problem1_iff_not_dFinite : Rule30Prize.Problem1 ↔
    ¬ ∃ (r : ℕ) (q : Fin (r + 1) → ℚ[X]), (∃ i, q i ≠ 0) ∧
      ∑ i : Fin (r + 1), (q i : PowerSeries ℚ) * (⇑(PowerSeries.derivative (R := ℚ)))^[i]
        (PowerSeries.mk fun t => if Rule30Prize.center t then 1 else 0) = 0 :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_dFinite c))

end Rule30Equivalents.DFinite
