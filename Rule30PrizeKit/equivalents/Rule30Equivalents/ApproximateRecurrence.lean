module

public import Rule30Equivalents.WordsAutomata
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Normed.Field.Basic
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
# Approximate linear recurrences

Over a normed field `𝕜`, such as `ℂ`, `ℝ` or `ℚ_[p]`, a monic polynomial
`Q = X^q + γ_{q-1} X^{q-1} + ⋯ + γ₀` acts on a sequence `b` of `0`s and `1`s by
`(Q(σ) b)(n) = b(n + q) + Σ_{j < q} γⱼ b(n + j)`.

* `eventuallyPeriodic_iff_approx_recurrence`: `b` is eventually periodic iff for some monic `Q`
  the values `(Q(σ) b)(n)` stay within `1/2` of `0` from some `n` on. If `b` has period `P` from
  time `T`, then `X^P - 1` kills it from `T` on. Conversely, two candidates `0` and `1` for
  `b(n + q)` give values `1` apart, so at most one of them lies within `1/2` of
  `-Σ γⱼ b(n + j)`: each letter is a function of the `q` letters before it, a feedback shift
  register (`WordsAutomata.eventuallyPeriodic_iff_feedback`).
* `problem1_iff_no_approx_recurrence`: so Problem 1 holds iff, for every monic `Q` over `𝕜`, the
  center column has `‖(Q(σ) c)(n)‖ ≥ 1/2` for infinitely many `n`;
  `problem1_iff_not_tendsto_zero`: iff no monic `Q` has `(Q(σ) c)(n) → 0`.

This is the last step of Szegő's theorem on power series with finitely many distinct coefficients:
an analytic continuation of `Σ c(t) zᵗ` across an arc of the unit circle yields, for every
`ε > 0`, a monic `Q` over `ℂ` with `‖(Q(σ) c)(n)‖ < ε` for all `n`.

Sources: G. Szegő, *Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten*,
Sitzungsber. Preuss. Akad. Wiss. (1922) 88–91; P. Dienes, *The Taylor series*, Dover (1957),
chapter X; P. Borwein, T. Erdélyi and F. Littmann, *Polynomials with coefficients from a finite
set*, Trans. Amer. Math. Soc. 360 (2008) 5145–5154, section 3.
-/

@[expose] public section

namespace Rule30Equivalents.ApproximateRecurrence

open Ruliology.CellularAutomata Polynomial Filter Topology

variable {𝕜 : Type*} [NormedField 𝕜]

/-- A letter as `1` (black) or `0` (white) in `𝕜`. -/
def bit (𝕜 : Type*) [NormedField 𝕜] (b : Bool) : 𝕜 := if b then 1 else 0

@[simp] theorem bit_true : bit 𝕜 true = 1 := by simp [bit]

@[simp] theorem bit_false : bit 𝕜 false = 0 := by simp [bit]

/-- `(Q(σ) b)(n) = Σⱼ Q.coeff j · b(n + j)`, a linear recurrence applied to `b` at time `n`. -/
noncomputable def apply (Q : 𝕜[X]) (b : ℕ → Bool) (n : ℕ) : 𝕜 :=
  ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * bit 𝕜 (b (n + j))

/-- For monic `Q` of degree `q`, `(Q(σ) b)(n) = b(n + q) + Σ_{j < q} γⱼ b(n + j)`. -/
theorem apply_of_monic {Q : 𝕜[X]} (hQ : Q.Monic) (b : ℕ → Bool) (n : ℕ) :
    apply Q b n = bit 𝕜 (b (n + Q.natDegree)) +
      ∑ j : Fin Q.natDegree, Q.coeff j * bit 𝕜 (b (n + j)) := by
  rw [apply, Finset.sum_range_succ, hQ.coeff_natDegree, one_mul, add_comm,
    Fin.sum_univ_eq_sum_range (fun j => Q.coeff j * bit 𝕜 (b (n + j)))]

/-- `X^P - 1` kills a sequence of period `P`. -/
theorem apply_X_pow_sub_one {P : ℕ} (hP : 0 < P) (b : ℕ → Bool) (n : ℕ) :
    apply (X ^ P - C (1 : 𝕜)) b n = bit 𝕜 (b (n + P)) - bit 𝕜 (b n) := by
  rw [apply, natDegree_X_pow_sub_C, Finset.sum_range_succ, Finset.sum_eq_single 0]
  · simp [coeff_X_pow, coeff_one, hP.ne, hP.ne']
    ring
  · intro j hj hj0
    have hjP : j ≠ P := (Finset.mem_range.1 hj).ne
    simp [coeff_X_pow, coeff_one, hjP, hj0]
  · intro h
    exact absurd (Finset.mem_range.2 hP) h

/-- **Approximate linear recurrences**: `b` is eventually periodic iff some monic polynomial `Q`
over a normed field keeps `(Q(σ) b)(n)` within `1/2` of `0` from some time on. -/
theorem eventuallyPeriodic_iff_approx_recurrence (b : ℕ → Bool) :
    EventuallyPeriodic b ↔
      ∃ Q : 𝕜[X], Q.Monic ∧ ∃ N, ∀ n, N ≤ n → ‖apply Q b n‖ < 1 / 2 := by
  constructor
  · rintro ⟨T, P, hP, hper⟩
    refine ⟨X ^ P - C 1, monic_X_pow_sub_C 1 hP.ne', T, fun n hn => ?_⟩
    rw [apply_X_pow_sub_one hP, hper n hn, sub_self, norm_zero]
    norm_num
  · rintro ⟨Q, hQ, N, hN⟩
    refine (WordsAutomata.eventuallyPeriodic_iff_feedback b).2
      ⟨Q.natDegree, fun w => decide (‖1 + ∑ j : Fin Q.natDegree, Q.coeff j * bit 𝕜 (w j)‖ < 1 / 2),
        N, fun t ht => ?_⟩
    have h := hN t ht
    rw [apply_of_monic hQ] at h
    set x := ∑ j : Fin Q.natDegree, Q.coeff j * bit 𝕜 (b (t + j))
    cases hb : b (t + Q.natDegree)
    · rw [hb, bit_false, zero_add] at h
      have h1 : 1 / 2 < ‖1 + x‖ := by
        have := norm_sub_norm_le (1 : 𝕜) (-x)
        rw [norm_one, norm_neg, sub_neg_eq_add] at this
        linarith
      exact (decide_eq_false (not_lt.2 h1.le)).symm
    · rw [hb, bit_true] at h
      exact (decide_eq_true h).symm

/-- **Problem 1, approximate recurrences**: for every monic `Q` over a normed field `𝕜`, the
center column has `‖(Q(σ) c)(n)‖ ≥ 1/2` for infinitely many `n`. Over `ℂ` this is the form that
Szegő's theorem reaches. -/
theorem problem1_iff_no_approx_recurrence (𝕜 : Type*) [NormedField 𝕜] :
    Rule30Prize.Problem1 ↔
      ∀ Q : 𝕜[X], Q.Monic → ∀ N, ∃ n, N ≤ n ∧ 1 / 2 ≤ ‖apply Q c n‖ := by
  refine (eventuallyPeriodic_iff_approx_recurrence (𝕜 := 𝕜) c).not.trans ?_
  constructor
  · intro h Q hQ N
    by_contra hne
    push Not at hne
    exact h ⟨Q, hQ, N, hne⟩
  · rintro h ⟨Q, hQ, N, hN⟩
    obtain ⟨n, hn, hge⟩ := h Q hQ N
    exact absurd (hN n hn) (not_lt.2 hge)

/-- **Asymptotic linear recurrences**: `b` is eventually periodic iff some monic polynomial `Q`
over a normed field has `(Q(σ) b)(n) → 0`. -/
theorem eventuallyPeriodic_iff_tendsto_zero (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ Q : 𝕜[X], Q.Monic ∧ Tendsto (apply Q b) atTop (𝓝 0) := by
  constructor
  · rintro ⟨T, P, hP, hper⟩
    refine ⟨X ^ P - C 1, monic_X_pow_sub_C 1 hP.ne', tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop T] with n hn
    rw [apply_X_pow_sub_one hP, hper n hn, sub_self]
  · rintro ⟨Q, hQ, hlim⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hlim.eventually (Metric.ball_mem_nhds (0 : 𝕜) (by norm_num : (0 : ℝ) < 1 / 2)))
    refine (eventuallyPeriodic_iff_approx_recurrence b).2 ⟨Q, hQ, N, fun n hn => ?_⟩
    have := hN n hn
    rwa [dist_zero_right] at this

/-- **Problem 1, asymptotic recurrences**: no monic `Q` over a normed field has
`(Q(σ) c)(n) → 0`. -/
theorem problem1_iff_not_tendsto_zero (𝕜 : Type*) [NormedField 𝕜] :
    Rule30Prize.Problem1 ↔
      ∀ Q : 𝕜[X], Q.Monic → ¬ Tendsto (apply Q c) atTop (𝓝 0) := by
  refine (eventuallyPeriodic_iff_tendsto_zero (𝕜 := 𝕜) c).not.trans ?_
  constructor
  · intro h Q hQ hlim
    exact h ⟨Q, hQ, hlim⟩
  · rintro h ⟨Q, hQ, hlim⟩
    exact h Q hQ hlim

end Rule30Equivalents.ApproximateRecurrence
