module

public import Rule30Equivalents.PisotNumbers
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.ComputeDegree
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
# Problem 1 in the Pisot base `1 + √2`

Read the center column as the digits of `x_β = ∑ c(t) β^-(t+1)` with `β = 1 + √2`, the Pisot number
whose conjugate is `1 - √2`.

* `problem1_iff_not_mem_Q_sqrt_two`: Problem 1 holds iff `x_β` is not of the form
  `a + b √2` with `a, b` rational, that is, `x_β ∉ ℚ(√2)`.
* In general, `eventuallyPeriodic_iff_mem_qsqrt2`: a `Bool` sequence is eventually periodic iff its
  value in base `1 + √2` lies in `ℚ(√2)`.

This is the case `β = 1 + √2` of `PisotNumbers.eventuallyPeriodic_iff_mem_adjoin`: `1 + √2` is a
root of `X² - 2X - 1`, whose other root `1 - √2` has absolute value `√2 - 1 < 1` (`isPisot_β`), and
`ℚ(1 + √2)` is the field `ℚ(√2)` of the numbers `a + b √2` (`mem_adjoin_iff`).
-/

@[expose] public section

namespace Rule30Equivalents.PisotBase

open Ruliology.CellularAutomata Polynomial

/-- The base `β = 1 + √2`. -/
noncomputable abbrev β : ℝ := 1 + Real.sqrt 2

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_gt : (1.4 : ℝ) < Real.sqrt 2 := by
  rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt2_lt : Real.sqrt 2 < 1.5 := by
  rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem two_lt_β : (2 : ℝ) < β := by have := sqrt2_gt; simp only [β]; linarith

/-! ### `1 + √2` is a Pisot number -/

theorem aeval_β : aeval β (X ^ 2 - 2 * X - 1 : ℤ[X]) = 0 := by
  simp only [map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
  linear_combination sqrt2_sq

theorem isPisot_β : PisotNumbers.IsPisot β := by
  have hm : (X ^ 2 - 2 * X - 1 : ℤ[X]).Monic := by monicity!
  have hint : IsIntegral ℤ β := ⟨_, hm, by rw [← aeval_def]; exact aeval_β⟩
  refine ⟨hint, by linarith [two_lt_β], fun z hz hne => ?_⟩
  -- `z` is a root of `X² - 2X - 1`, so `z = 1 - √2`
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint aeval_β
  have hz2 : z ^ 2 - 2 * z - 1 = 0 := by
    have := congrArg (aeval z) hr
    rw [map_mul, hz, zero_mul] at this
    simp only [map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat] at this
    exact this
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast sqrt2_sq
  have hprod : (z - ((β : ℝ) : ℂ)) * (z - ((1 - Real.sqrt 2 : ℝ) : ℂ)) = 0 := by
    push_cast
    linear_combination hz2 - hs
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · rw [sub_eq_zero.1 h, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_pos (by linarith [sqrt2_gt])]
    linarith [sqrt2_lt]

/-! ### The field `ℚ(√2)` -/

/-- `ℚ(√2)` as a subfield of `ℝ`: the numbers `a + b √2` with `a, b` rational. -/
noncomputable def qsqrt2 : Subfield ℝ where
  carrier := {x | ∃ a b : ℚ, x = a + b * Real.sqrt 2}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c + 2 * b * d, a * d + b * c, ?_⟩
    push_cast
    linear_combination (b : ℝ) * d * sqrt2_sq
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases h : (a : ℝ) + b * Real.sqrt 2 = 0
    · rw [h, inv_zero]; exact ⟨0, 0, by simp⟩
    · have hprod : ((a : ℝ) + b * Real.sqrt 2) * ((a : ℝ) - b * Real.sqrt 2) =
          ((a ^ 2 - 2 * b ^ 2 : ℚ) : ℝ) := by
        push_cast; linear_combination -(b : ℝ) ^ 2 * sqrt2_sq
      have hy : (a : ℝ) - b * Real.sqrt 2 ≠ 0 := by
        intro h'
        by_cases hb : b = 0
        · subst hb; simp at h h'; exact h h'
        · apply irrational_sqrt_two
          refine ⟨a / b, ?_⟩
          have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
          push_cast
          field_simp
          linarith
      refine ⟨a / (a ^ 2 - 2 * b ^ 2), -b / (a ^ 2 - 2 * b ^ 2), ?_⟩
      rw [show ((a / (a ^ 2 - 2 * b ^ 2) : ℚ) : ℝ) + ((-b / (a ^ 2 - 2 * b ^ 2) : ℚ) : ℝ) *
          Real.sqrt 2 = ((a : ℝ) - b * Real.sqrt 2) / ((a ^ 2 - 2 * b ^ 2 : ℚ) : ℝ) by
        push_cast; ring, ← hprod]
      field_simp

theorem mem_qsqrt2 {x : ℝ} : x ∈ qsqrt2 ↔ ∃ a b : ℚ, x = a + b * Real.sqrt 2 := Iff.rfl

theorem β_mem : β ∈ qsqrt2 := ⟨1, 1, by simp⟩

/-- `ℚ(1 + √2) = ℚ(√2)`. -/
theorem mem_adjoin_iff {x : ℝ} : x ∈ IntermediateField.adjoin ℚ ({β} : Set ℝ) ↔ x ∈ qsqrt2 := by
  constructor
  · intro hx
    have hle : IntermediateField.adjoin ℚ ({β} : Set ℝ) ≤
        qsqrt2.toIntermediateField fun q => ⟨q, 0, by simp⟩ :=
      IntermediateField.adjoin_simple_le_iff.2 β_mem
    exact hle hx
  · rintro ⟨a, b, rfl⟩
    set K := IntermediateField.adjoin ℚ ({β} : Set ℝ)
    have hβ : β ∈ K := IntermediateField.mem_adjoin_simple_self ℚ β
    have ha : (a : ℝ) ∈ K := by simp
    have hb : (b : ℝ) ∈ K := by simp
    rw [show (a : ℝ) + b * Real.sqrt 2 = a + b * (β - 1) by simp only [β]; ring]
    exact K.add_mem ha (K.mul_mem hb (K.sub_mem hβ K.one_mem))

/-- **A digit sequence is eventually periodic iff its value in base `1 + √2` lies in `ℚ(√2)`.** -/
theorem eventuallyPeriodic_iff_mem_qsqrt2 (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ BinaryIrrational.value β b ∈ qsqrt2 := by
  rw [PisotNumbers.eventuallyPeriodic_iff_mem_adjoin isPisot_β two_lt_β, mem_adjoin_iff]

/-- **Problem 1 ⟺ `x_β ∉ ℚ(√2)` for `β = 1 + √2`**. -/
theorem problem1_iff_not_mem_Q_sqrt_two : Rule30Prize.Problem1 ↔
    ¬ ∃ a b : ℚ, ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / (1 + Real.sqrt 2) ^ (t + 1) =
      a + b * Real.sqrt 2 :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_mem_qsqrt2 c))

end Rule30Equivalents.PisotBase
