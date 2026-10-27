module

public import Rule30Equivalents.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Natural boundary: the sufficient direction

Let `f(z) = ∑ c(t) zᵗ` on the unit disk. Problem 1 is equivalent to `f` having
the unit circle as a natural boundary: no analytic continuation across any arc. The hard direction
is Szegő's theorem (or Pólya–Carlson). This file proves the easy one.

* `mul_genFun_eq`: if `b` is eventually periodic with period `P` from time `T`, then on the unit
  disk `(1 − z^P) f(z)` is the polynomial `∑_{t < T + P} (bₜ − b_{t−P}) zᵗ`.
* `exists_continuation`: so `f` continues analytically across the circle at `z₀ = e^{iπ/P}`, where
  `1 − z₀^P = 2 ≠ 0`, as the rational function `Q(z) / (1 − z^P)`.
* `problem1_of_natural_boundary`.

Sources: G. Szegő, *Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten*, Sitzungsber.
Preuss. Akad. Wiss. (1922) 88–91; F. Carlson, *Über Potenzreihen mit ganzzahligen Koeffizienten*,
Math. Z. 9 (1921) 1–13.
-/

@[expose] public section

namespace Rule30Equivalents.NaturalBoundary

open Ruliology.CellularAutomata Complex Finset Real

/-- The coefficients of the generating function of `b`. -/
noncomputable def coef (b : ℕ → Bool) (t : ℕ) : ℂ := if b t then 1 else 0

/-- The generating function `∑ b(t) zᵗ`, on the unit disk. -/
noncomputable def genFun (b : ℕ → Bool) (z : ℂ) : ℂ := ∑' t, coef b t * z ^ t

theorem summable_coef (b : ℕ → Bool) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun t => coef b t * z ^ t := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun t => ?_
  rw [norm_mul, norm_pow]
  refine mul_le_of_le_one_left (by positivity) ?_
  unfold coef
  split_ifs <;> simp

/-- An eventually periodic sequence has a rational generating function: `(1 − z^P) f(z)` is a
polynomial on the unit disk. -/
theorem mul_genFun_eq {b : ℕ → Bool} {T P : ℕ} (hTP : ∀ t, T ≤ t → b (t + P) = b t) {z : ℂ}
    (hz : ‖z‖ < 1) : (1 - z ^ P) * genFun b z =
      ∑ t ∈ range (T + P), (coef b t - if P ≤ t then coef b (t - P) else 0) * z ^ t := by
  have hs := summable_coef b hz
  set g : ℕ → ℂ := fun t => (if P ≤ t then coef b (t - P) else 0) * z ^ t
  have hg : ∀ t, g (t + P) = z ^ P * (coef b t * z ^ t) := fun t => by
    simp only [g, ite_eq_left (Nat.le_add_left P t), Nat.add_sub_cancel, pow_add]
    ring
  have hgs : Summable g := by
    refine (summable_nat_add_iff P).1 ?_
    simp only [hg]
    exact hs.mul_left _
  have hgsum : ∑' t, g t = z ^ P * genFun b z := by
    rw [← hgs.sum_add_tsum_nat_add P, Finset.sum_eq_zero fun t ht => by
      simp [g, show ¬ P ≤ t by simpa using ht], zero_add]
    simp only [hg]
    rw [tsum_mul_left, genFun]
  rw [sub_mul, one_mul, ← hgsum, genFun, ← hs.tsum_sub hgs]
  rw [tsum_eq_sum (s := range (T + P)) fun t ht => ?_]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [g]
    ring
  · have ht' : T + P ≤ t := by simpa using ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + P := ⟨t - P, by omega⟩
    simp only [g, ite_eq_left (Nat.le_add_left P s), Nat.add_sub_cancel, coef, hTP s (by omega)]
    ring

/-- **An eventually periodic sequence has a generating function that continues analytically
across the unit circle.** -/
theorem exists_continuation {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ z₀ : ℂ, ‖z₀‖ = 1 ∧ ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball z₀ r) ∧ ∀ z ∈ Metric.ball z₀ r, ‖z‖ < 1 → g z = genFun b z := by
  obtain ⟨T, P, hP, hTP⟩ := h
  set Q : ℂ → ℂ := fun z =>
    ∑ t ∈ range (T + P), (coef b t - if P ≤ t then coef b (t - P) else 0) * z ^ t
  set z₀ : ℂ := exp ((π / P : ℝ) * I)
  have hz₀ : ‖z₀‖ = 1 := norm_exp_ofReal_mul_I _
  have hP' : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hz₀P : z₀ ^ P = -1 := by
    rw [← Complex.exp_nat_mul, show (P : ℂ) * ((π / P : ℝ) * I) = π * I by
      push_cast
      field_simp]
    exact Complex.exp_pi_mul_I
  set U : Set ℂ := {z | 1 - z ^ P ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hz₀U : z₀ ∈ U := by
    show 1 - z₀ ^ P ≠ 0
    rw [hz₀P]
    norm_num
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀U
  refine ⟨z₀, hz₀, r, hr, fun z => Q z / (1 - z ^ P), ?_, fun z hz hz1 => ?_⟩
  · have hd : DifferentiableOn ℂ (fun z => Q z / (1 - z ^ P)) U :=
      DifferentiableOn.div (by fun_prop) (by fun_prop) fun z hz => hz
    exact (hd.analyticOnNhd hU).mono hball
  · have hne : 1 - z ^ P ≠ 0 := hball hz
    rw [div_eq_iff hne, mul_comm, mul_genFun_eq hTP hz1]

/-- **A sufficient condition**: if the generating function of the center column
continues analytically across no arc of the unit circle, Problem 1 holds. The converse is Szegő's
theorem, which is not proved here. -/
theorem problem1_of_natural_boundary
    (h : ∀ z₀ : ℂ, ‖z₀‖ = 1 → ∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball z₀ r) ∧ ∀ z ∈ Metric.ball z₀ r, ‖z‖ < 1 → g z = genFun c z) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨z₀, hz₀, r, hr, hg⟩ := exists_continuation hep
  exact h z₀ hz₀ r hr hg

end Rule30Equivalents.NaturalBoundary
