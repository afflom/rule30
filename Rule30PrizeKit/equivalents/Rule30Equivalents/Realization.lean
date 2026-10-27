module

public import Rule30Equivalents.BinaryIrrational
public import Ruliology.CellularAutomata.Rule30Realization
public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Analysis.Real.Cardinality

/-!
# The inverse problem, other columns, and `Real.ofDigits`

* `problem1_iff_realization`: **Problem 1 as an inverse problem.** Keep the right half of the initial
  row white. Rule 30 is affine in its left cell, so every column `u : ℕ → Bool` is the centre
  column of exactly one such row, `Rule30Realization.conf seed u`. Problem 1 says that no
  eventually periodic column is realized by the single seed.
* `problem1_or_column`, `problem1_iff_column_iff_both`: **why other columns are not equivalent
  forms.** By Jen's theorem at most one column of the pattern is eventually periodic, so for every
  column `j ≠ 0`, Problem 1 or "column `j` is not eventually periodic" holds. Hence a proof that
  Problem 1 is *equivalent* to the same question for column `j` would prove both statements
  outright: no such equivalence can be proved without solving the problem.
* `problem1_iff_irrational_ofDigits`: Problem 1 in Mathlib's `Real.ofDigits` vocabulary, in every
  base `b ≥ 2`, through `BinaryIrrational.problem1_iff_irrational_base`.
* `problem1_iff_irrational_cantorFunction`: the same with Mathlib's `Cardinal.cantorFunction` at
  `1/b`, which is `b` times the base-`b` value.
-/

@[expose] public section

namespace Rule30Equivalents.Realization

open Ruliology.CellularAutomata

/-! ### The inverse problem -/

open Rule30Realization in
/-- **Problem 1 as an inverse problem.** With the right half white, every column `u` is realized by
exactly one row `conf seed u`; Problem 1 says that no eventually periodic `u` is realized by the
single seed. -/
theorem problem1_iff_realization :
    Rule30Prize.Problem1 ↔ ∀ u : ℕ → Bool, EventuallyPeriodic u → conf seed u ≠ seed := by
  constructor
  · intro h u hu he
    apply h
    have : c = u := by
      funext t
      have h1 := (realize seed u).2 t
      rw [he, evol_seed] at h1
      exact h1
    have h' : Rule30Prize.center = u := this
    rw [h']; exact hu
  · intro h hc
    have hs : conf seed c = seed := by
      symm
      refine unique (fun p hp => ((realize seed c).1 p hp).symm) (fun t => ?_)
      rw [evol_seed, (realize seed c).2 t]; rfl
    exact h c hc hs

/-! ### Other columns -/

/-- Jen's theorem: Problem 1 holds, or column `j ≠ 0` is not eventually periodic. -/
theorem problem1_or_column (j : ℤ) (hj : j ≠ 0) :
    Rule30Prize.Problem1 ∨ ¬ EventuallyPeriodic (fun t => Rule30Jen.cell t j) := by
  by_cases h : Rule30Prize.Problem1
  · exact Or.inl h
  · refine Or.inr fun hjp => ?_
    have hc : EventuallyPeriodic c := Classical.byContradiction h
    exact Rule30Jen.jen 0 j (Ne.symm hj) ⟨hc, hjp⟩

/-- An equivalence between Problem 1 and the same question for column `j ≠ 0` would prove both. -/
theorem problem1_iff_column_iff_both (j : ℤ) (hj : j ≠ 0) :
    (Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => Rule30Jen.cell t j)) ↔
      (Rule30Prize.Problem1 ∧ ¬ EventuallyPeriodic (fun t => Rule30Jen.cell t j)) := by
  constructor
  · intro e
    rcases problem1_or_column j hj with a | b
    · exact ⟨a, e.1 a⟩
    · exact ⟨e.2 b, b⟩
  · rintro ⟨a, b⟩
    exact ⟨fun _ => b, fun _ => a⟩

/-! ### `Real.ofDigits` -/

theorem ofDigits_eq (b : ℕ) [NeZero b] (hb : 2 ≤ b) :
    Real.ofDigits (b := b) (fun t => if c t then 1 else 0) =
      ∑' t, (if c t then (1 : ℝ) else 0) / (b : ℝ) ^ (t + 1) := by
  unfold Real.ofDigits Real.ofDigitsTerm
  congr 1
  funext t
  have h1 : 1 % b = 1 := Nat.one_mod_eq_one.mpr (by omega)
  cases hc : c t
  · simp [hc]
  · simp [hc, h1, div_eq_mul_inv]

/-- **Problem 1 in Mathlib's `Real.ofDigits` vocabulary**, in every base `b ≥ 2`. -/
theorem problem1_iff_irrational_ofDigits (b : ℕ) [NeZero b] (hb : 2 ≤ b) :
    Rule30Prize.Problem1 ↔ Irrational (Real.ofDigits (b := b) fun t => if c t then 1 else 0) := by
  rw [ofDigits_eq b hb]
  exact BinaryIrrational.problem1_iff_irrational_base hb

/-! ### The Cantor function -/

theorem cantorFunction_eq (b : ℕ) (hb : 2 ≤ b) :
    Cardinal.cantorFunction (1 / (b : ℝ)) c =
      (b : ℝ) * ∑' t, (if c t then (1 : ℝ) else 0) / (b : ℝ) ^ (t + 1) := by
  unfold Cardinal.cantorFunction
  rw [← tsum_mul_left]
  congr 1
  funext t
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  unfold Cardinal.cantorFunctionAux
  rcases Bool.eq_false_or_eq_true (c t) with h | h
  · rw [h]
    simp only [Bool.cond_true, ite_true, one_div, inv_pow]
    rw [pow_succ]
    field_simp
  · rw [h]; simp

/-- **Problem 1 in the vocabulary of the Cantor function**: `Cardinal.cantorFunction (1/b) c`, the
number `∑ c(t) b^-t`, is irrational, for every base `b ≥ 2`. -/
theorem problem1_iff_irrational_cantorFunction (b : ℕ) (hb : 2 ≤ b) : Rule30Prize.Problem1 ↔
    Irrational (Cardinal.cantorFunction (1 / (b : ℝ)) Rule30Prize.center) := by
  rw [cantorFunction_eq b hb, irrational_natCast_mul_iff, BinaryIrrational.problem1_iff_irrational_base hb]
  exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

end Rule30Equivalents.Realization
