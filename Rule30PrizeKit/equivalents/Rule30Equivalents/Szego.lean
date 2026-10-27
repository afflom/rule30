module

public import Rule30Equivalents.SzegoContour
public import Rule30Equivalents.ApproximateRecurrence
public import Rule30Equivalents.NaturalBoundary
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Szegő's theorem for 0/1 sequences: Problem 1 as a natural boundary

Let `f(z) = Σ b(t) zᵗ` for a sequence `b` of `0`s and `1`s. If `b` is eventually periodic, `f` is
rational and continues across the unit circle (`NaturalBoundary.exists_continuation`). Szegő's
theorem is the converse: a continuation of `f` across any arc of the circle makes `b` eventually
periodic.

* `eventuallyPeriodic_of_continuation`: rotating the arc to `1`, the coefficients
  `a(n) = b(n) z₀ⁿ` satisfy, by `SzegoContour.exists_approx_recurrence`, `‖Σⱼ wⱼ a(n + j)‖ < 1/2`
  for a monic `W` and every `n`. Then `Q(X) = W(z₀X)/z₀ᵈ` is monic with `‖(Q(σ) b)(n)‖ < 1/2`, and
  `ApproximateRecurrence.eventuallyPeriodic_iff_approx_recurrence` concludes.
* `eventuallyPeriodic_iff_continuation`: both directions.
* `problem1_iff_natural_boundary`: the center column is not eventually periodic iff its
  generating function continues analytically across no arc of the unit circle.

Sources: G. Szegő, *Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten*,
Sitzungsber. Preuss. Akad. Wiss. (1922) 88–91; P. Dienes, *The Taylor series*, Dover (1957),
chapter X; P. Borwein, T. Erdélyi and F. Littmann, *Polynomials with coefficients from a finite
set*, Trans. Amer. Math. Soc. 360 (2008) 5145–5154, section 3.
-/

@[expose] public section

namespace Rule30Equivalents.Szego

open Ruliology.CellularAutomata Complex Polynomial Metric NaturalBoundary ApproximateRecurrence

/-- **Szegő's theorem** for 0/1 sequences: if `Σ b(t) zᵗ` continues analytically across an arc of
the unit circle, then `b` is eventually periodic. -/
theorem eventuallyPeriodic_of_continuation {b : ℕ → Bool} {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {r : ℝ}
    (hr : 0 < r) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball z₀ r))
    (hgf : ∀ z ∈ ball z₀ r, ‖z‖ < 1 → g z = genFun b z) : EventuallyPeriodic b := by
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    simp at hz₀
  -- rotate the arc to `1`
  set a : ℕ → ℂ := fun n => coef b n * z₀ ^ n with hadef
  have ha : ∀ n, ‖a n‖ ≤ 1 := fun n => by
    rw [hadef, norm_mul, norm_pow, hz₀, one_pow, mul_one, coef]
    split_ifs <;> simp
  have hmem : ∀ z ∈ ball (1 : ℂ) r, z₀ * z ∈ ball z₀ r := fun z hz => by
    rw [mem_ball, dist_eq] at hz ⊢
    rw [show z₀ * z - z₀ = z₀ * (z - 1) by ring, norm_mul, hz₀, one_mul]
    exact hz
  have hg' : DifferentiableOn ℂ (fun z => g (z₀ * z)) (ball 1 r) := fun z hz =>
    ((hg _ (hmem z hz)).differentiableAt.comp z
      (differentiableAt_id.const_mul z₀)).differentiableWithinAt
  have hgf' : ∀ z ∈ ball (1 : ℂ) r, ‖z‖ < 1 → g (z₀ * z) = ∑' n, a n * z ^ n := fun z hz hz1 => by
    rw [hgf _ (hmem z hz) (by rw [norm_mul, hz₀, one_mul]; exact hz1), genFun]
    refine tsum_congr fun n => ?_
    rw [hadef, mul_pow]
    ring
  obtain ⟨W, hWm, hW⟩ := SzegoContour.exists_approx_recurrence ha hr hg' hgf'
    (by norm_num : (0 : ℝ) < 1 / 2)
  -- normalize `W(z₀ X)` to a monic polynomial
  set d := W.natDegree with hd
  set Q : ℂ[X] := C (z₀ ^ d)⁻¹ * W.comp (C z₀ * X) with hQdef
  have hCX : (C z₀ * X).natDegree = 1 := natDegree_C_mul_X z₀ hz0
  have hQdeg : Q.natDegree = d := by
    rw [hQdef, natDegree_C_mul (inv_ne_zero (pow_ne_zero _ hz0)), natDegree_comp, hCX, mul_one]
  have hQm : Q.Monic := by
    rw [Monic, hQdef, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.2
      (inv_ne_zero (pow_ne_zero _ hz0))), leadingCoeff_comp (by rw [hCX]; exact one_ne_zero),
      hWm.leadingCoeff, one_mul, leadingCoeff_C_mul_X, ← hd, inv_mul_cancel₀ (pow_ne_zero _ hz0)]
  refine (eventuallyPeriodic_iff_approx_recurrence (𝕜 := ℂ) b).2 ⟨Q, hQm, 0, fun n _ => ?_⟩
  have happly : apply Q b n =
      (z₀ ^ (d + n))⁻¹ * ∑ j ∈ Finset.range (d + 1), a (n + j) * W.coeff j := by
    rw [apply, hQdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcb : bit ℂ (b (n + j)) = coef b (n + j) := by
      rw [bit, coef]
    rw [hQdef, coeff_C_mul, comp_C_mul_X_coeff, hcb, hadef]
    field_simp
    ring
  rw [happly, norm_mul, norm_inv, norm_pow, hz₀, one_pow, inv_one, one_mul]
  exact hW n

/-- **Szegő's theorem** for 0/1 sequences, both directions: `b` is eventually periodic iff
`Σ b(t) zᵗ` continues analytically across some arc of the unit circle. -/
theorem eventuallyPeriodic_iff_continuation (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ z₀ : ℂ, ‖z₀‖ = 1 ∧ ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball z₀ r) ∧ ∀ z ∈ ball z₀ r, ‖z‖ < 1 → g z = genFun b z :=
  ⟨exists_continuation, fun ⟨_, hz₀, _, hr, _, hg, hgf⟩ =>
    eventuallyPeriodic_of_continuation hz₀ hr hg hgf⟩

/-- **Problem 1, natural boundary**: the center column is not eventually periodic iff its
generating function `Σ c(t) zᵗ` continues analytically across no arc of the unit circle. -/
theorem problem1_iff_natural_boundary : Rule30Prize.Problem1 ↔
    ∀ z₀ : ℂ, ‖z₀‖ = 1 → ∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball z₀ r) ∧ ∀ z ∈ ball z₀ r, ‖z‖ < 1 → g z = genFun c z :=
  ⟨fun h _ hz₀ _ hr ⟨_, hg, hgf⟩ => h (eventuallyPeriodic_of_continuation hz₀ hr hg hgf),
    problem1_of_natural_boundary⟩

end Rule30Equivalents.Szego
