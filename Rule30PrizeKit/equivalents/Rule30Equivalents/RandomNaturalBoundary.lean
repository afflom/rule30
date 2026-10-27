module

public import Rule30Equivalents.NaturalBoundary
public import Rule30Equivalents.Fluctuations
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound
public import Mathlib.Probability.Independence.Integration

/-!
# The natural boundary of a random generating function

For a sequence of fair coins `v`, the generating function `f(z) = ∑ v(k) zᵏ` of the black cells
(`NaturalBoundary.genFun`) has the unit circle as a natural boundary almost surely
(`ae_circleIsNaturalBoundary`): no analytic function on a disk around a point of the circle agrees
with `f` inside the unit disk. The same holds for the center column of almost every configuration
(`ae_circleIsNaturalBoundary_trace`). For the center column of the single seed this would prove
Problem 1 (`problem1_of_circleIsNaturalBoundary`).

The proof combines the Paley–Zygmund inequality with Kolmogorov's zero-one law. Write
`spin(b) = ±1` for a coin, so that `2 f(z) - 1/(1 - z) = ∑ spin(v(k)) zᵏ`.

* `moments_partialSum`, `integral_rademacher_sq`, `integral_rademacher_pow_four_le`: a weighted
  sum `X = ∑ a(k) spin(v(k))` of independent signs has `E X² = ∑ a(k)²` and `E X⁴ ≤ 3 (E X²)²`.
* `le_measureReal_lt_sq`: so (Paley–Zygmund) `X² > E X² / 4` with probability at least `1/6`.
* `ae_unbounded`: for a sequence of weights whose sums of squares are unbounded, the sums `Xⱼ` are
  unbounded with probability at least `1/6` (`measure_unbounded_ne_zero`); the event does not
  depend on finitely many coins (`unbounded_iff_tail`), so by Kolmogorov's zero-one law it is
  almost sure.
* `rademacher_radialWeight`: along the radius to `w`, the real part of `2 f(t w) - 1/(1 - t w)` is
  such a sum, with weights `tᵏ Re(wᵏ)`. For `w = e^{iπ(2p+1)/(N+1)}` (`dir`) these weights square
  to at least `1/(1 - t^(2N+2))` (`le_tsum_radialWeight_sq`), which is unbounded as `t → 1`.
* `circleIsNaturalBoundary_of_unbounded`: these points are dense in the circle
  (`exists_dir_mem_ball`), and an analytic continuation across the circle at `w ≠ 1` would make
  `2 f(t w) - 1/(1 - t w)` converge as `t → 1` (`tendsto_rademacher_of_continuation`).

Sources: H. Steinhaus, *Über die Wahrscheinlichkeit dafür, daß der Konvergenzkreis einer
Potenzreihe ihre natürliche Grenze ist*, Math. Z. 31 (1930) 408–416; R. E. A. C. Paley and
A. Zygmund, *On some series of functions (3)*, Proc. Cambridge Philos. Soc. 28 (1932) 190–205;
J.-P. Kahane, *Some random series of functions*, 2nd ed., Cambridge University Press (1985).
-/

@[expose] public section

namespace Rule30Equivalents.RandomNaturalBoundary

open MeasureTheory ProbabilityTheory Filter Topology Genericity RandomConfigurations
  NaturalBoundary Fluctuations

/-- The unit circle is a natural boundary of the generating function of `b`: no analytic function
on a disk around a point of the circle agrees with it inside the unit disk. -/
def CircleIsNaturalBoundary (b : ℕ → Bool) : Prop :=
  ∀ z₀ : ℂ, ‖z₀‖ = 1 → ∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g (Metric.ball z₀ r) ∧ ∀ z ∈ Metric.ball z₀ r, ‖z‖ < 1 → g z = genFun b z

/-! ### Weighted sums of signs -/

/-- A coin as a sign: black `1`, white `-1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]

theorem abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> norm_num [spin]

theorem measurable_spin : Measurable spin := Measurable.of_discrete

theorem integral_spin_apply (k : ℕ) : ∫ v, spin (v k) ∂(coins ℕ) = 0 := by
  rw [← integral_map (measurable_pi_apply k).aemeasurable measurable_spin.aestronglyMeasurable,
    coins_map_eval, integral_fintype Integrable.of_finite]
  simp [spin, measureReal_def, coin_singleton]

/-- The weighted sum `∑_{k < n} a(k) spin(v(k))` of the first `n` coins. -/
noncomputable def partialSum (a : ℕ → ℝ) (v : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, spin (v k) * a k

theorem measurable_partialSum (a : ℕ → ℝ) (n : ℕ) :
    Measurable fun v : ℕ → Bool => partialSum a v n :=
  Finset.measurable_sum _ fun k _ => (measurable_spin.comp (measurable_pi_apply k)).mul_const _

theorem abs_partialSum_le (a : ℕ → ℝ) (v : ℕ → Bool) (n : ℕ) :
    |partialSum a v n| ≤ ∑ k ∈ Finset.range n, |a k| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [abs_mul, abs_spin, one_mul]

/-- The first `n` coins are independent of the coin `n`. -/
theorem indepFun_partialSum (a : ℕ → ℝ) (n : ℕ) :
    IndepFun (fun v : ℕ → Bool => partialSum a v n) (fun v => spin (v n) * a n) (coins ℕ) := by
  have hind : iIndepFun (fun k (v : ℕ → Bool) => spin (v k) * a k) (coins ℕ) :=
    iIndepFun_infinitePi (X := fun k b => spin b * a k) fun k => measurable_spin.mul_const _
  have h := hind.indepFun_finsetSum_of_notMem
    (fun k => (measurable_spin.comp (measurable_pi_apply k)).mul_const _)
    (s := Finset.range n) (i := n) (by simp)
  convert h using 1
  ext v
  simp [partialSum, Finset.sum_apply]

/-- **The second and fourth moments of a weighted sum of signs**: `E S² = ∑ a(k)²` and
`E S⁴ ≤ 3 (∑ a(k)²)²`. Adding an independent term `a spin` adds `a²` to the second moment and
`6 a² E S² + a⁴` to the fourth, since the odd moments of `spin` vanish. -/
theorem moments_partialSum (a : ℕ → ℝ) (n : ℕ) :
    ∫ v, partialSum a v n ^ 2 ∂(coins ℕ) = ∑ k ∈ Finset.range n, a k ^ 2 ∧
      ∫ v, partialSum a v n ^ 4 ∂(coins ℕ) ≤ 3 * (∑ k ∈ Finset.range n, a k ^ 2) ^ 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    set S : (ℕ → Bool) → ℝ := fun v => partialSum a v n with hS
    set f : (ℕ → Bool) → ℝ := fun v => spin (v n) * a n with hf
    have hsucc : ∀ v, partialSum a v (n + 1) = S v + f v := fun v => Finset.sum_range_succ _ _
    have hSm : Measurable S := measurable_partialSum a n
    have hfm : Measurable f := (measurable_spin.comp (measurable_pi_apply n)).mul_const _
    have hf2 : ∀ v, f v ^ 2 = a n ^ 2 := fun v => by rw [hf, mul_pow, spin_sq, one_mul]
    have hf0 : ∫ v, f v ∂(coins ℕ) = 0 := by
      rw [hf, integral_mul_const, integral_spin_apply, zero_mul]
    have hcross : ∀ p : ℕ, ∫ v, S v ^ p * f v ∂(coins ℕ) = 0 := fun p => by
      have h : IndepFun (fun v => S v ^ p) f (coins ℕ) :=
        (indepFun_partialSum a n).comp (measurable_id.pow_const p) measurable_id
      rw [h.integral_fun_mul_eq_mul_integral (hSm.pow_const p).aestronglyMeasurable
        hfm.aestronglyMeasurable, hf0, mul_zero]
    set M := ∑ k ∈ Finset.range n, |a k|
    have hM : ∀ v, |S v| ≤ M := fun v => abs_partialSum_le a v n
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun k _ => abs_nonneg _
    have hfa : ∀ v, |f v| = |a n| := fun v => by rw [hf, abs_mul, abs_spin, one_mul]
    have hint : ∀ p q : ℕ, Integrable (fun v => S v ^ p * f v ^ q) (coins ℕ) := fun p q =>
      Integrable.of_bound ((hSm.pow_const p).mul (hfm.pow_const q)).aestronglyMeasurable
        (M ^ p * |a n| ^ q) (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, hfa]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM v) p)
            (by positivity))
    have hintS : ∀ p, Integrable (fun v => S v ^ p) (coins ℕ) := fun p => by
      simpa using hint p 0
    have hintSf : ∀ p, Integrable (fun v => S v ^ p * f v) (coins ℕ) := fun p => by
      simpa using hint p 1
    obtain ⟨ih2, ih4⟩ := ih
    constructor
    · have e2 : (fun v => partialSum a v (n + 1) ^ 2) =
          fun v => S v ^ 2 + 2 * (S v ^ 1 * f v) + a n ^ 2 := funext fun v => by
        rw [hsucc]
        linear_combination hf2 v
      have h1 : Integrable (fun v => S v ^ 2 + 2 * (S v ^ 1 * f v)) (coins ℕ) :=
        (hintS 2).add ((hintSf 1).const_mul 2)
      rw [e2, integral_add h1 (integrable_const _), integral_add (hintS 2) ((hintSf 1).const_mul 2),
        integral_const_mul, hcross 1, integral_const, ih2, Finset.sum_range_succ]
      simp
    · have e4 : (fun v => partialSum a v (n + 1) ^ 4) =
          fun v => S v ^ 4 + 4 * (S v ^ 3 * f v) + 6 * a n ^ 2 * S v ^ 2 +
            4 * a n ^ 2 * (S v ^ 1 * f v) + a n ^ 4 := funext fun v => by
        rw [hsucc]
        linear_combination (6 * S v ^ 2 + 4 * S v * f v + f v ^ 2 + a n ^ 2) * hf2 v
      have h1 : Integrable (fun v => S v ^ 4 + 4 * (S v ^ 3 * f v)) (coins ℕ) :=
        (hintS 4).add ((hintSf 3).const_mul 4)
      have h2 : Integrable (fun v => S v ^ 4 + 4 * (S v ^ 3 * f v) + 6 * a n ^ 2 * S v ^ 2)
          (coins ℕ) :=
        h1.add ((hintS 2).const_mul (6 * a n ^ 2))
      have h3 : Integrable (fun v => S v ^ 4 + 4 * (S v ^ 3 * f v) + 6 * a n ^ 2 * S v ^ 2 +
          4 * a n ^ 2 * (S v ^ 1 * f v)) (coins ℕ) :=
        h2.add ((hintSf 1).const_mul (4 * a n ^ 2))
      rw [e4, integral_add h3 (integrable_const _), integral_add h2 ((hintSf 1).const_mul _),
        integral_add h1 ((hintS 2).const_mul _), integral_add (hintS 4) ((hintSf 3).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hcross 3, hcross 1, ih2,
        integral_const, Finset.sum_range_succ]
      simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
      have hσ : 0 ≤ ∑ k ∈ Finset.range n, a k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
      nlinarith [sq_nonneg (a n ^ 2), mul_nonneg hσ (sq_nonneg (a n))]

/-- The weighted sum `∑ a(k) spin(v(k))` of all the coins. -/
noncomputable def rademacher (a : ℕ → ℝ) (v : ℕ → Bool) : ℝ := ∑' k, spin (v k) * a k

variable {a : ℕ → ℝ}

theorem summable_spin_mul (ha : Summable a) (v : ℕ → Bool) :
    Summable fun k => spin (v k) * a k :=
  Summable.of_norm_bounded ha.abs fun k => by rw [Real.norm_eq_abs, abs_mul, abs_spin, one_mul]

theorem tendsto_partialSum (ha : Summable a) (v : ℕ → Bool) :
    Tendsto (partialSum a v) atTop (𝓝 (rademacher a v)) :=
  (summable_spin_mul ha v).hasSum.tendsto_sum_nat

theorem measurable_rademacher (ha : Summable a) : Measurable (rademacher a) :=
  measurable_of_tendsto_metrizable (measurable_partialSum a)
    (tendsto_pi_nhds.2 fun v => tendsto_partialSum ha v)

theorem abs_partialSum_le_tsum (ha : Summable a) (v : ℕ → Bool) (n : ℕ) :
    |partialSum a v n| ≤ ∑' k, |a k| :=
  (abs_partialSum_le a v n).trans (ha.abs.sum_le_tsum _ fun _ _ => abs_nonneg _)

theorem abs_rademacher_le (ha : Summable a) (v : ℕ → Bool) : |rademacher a v| ≤ ∑' k, |a k| :=
  le_of_tendsto ((continuous_abs.tendsto _).comp (tendsto_partialSum ha v))
    (Eventually.of_forall fun n => abs_partialSum_le_tsum ha v n)

/-- The moments of `partialSum` converge to those of `rademacher`, by dominated convergence. -/
theorem tendsto_integral_partialSum_pow (ha : Summable a) (p : ℕ) :
    Tendsto (fun n => ∫ v, partialSum a v n ^ p ∂(coins ℕ)) atTop
      (𝓝 (∫ v, rademacher a v ^ p ∂(coins ℕ))) :=
  tendsto_integral_of_dominated_convergence (fun _ => (∑' k, |a k|) ^ p)
    (fun n => ((measurable_partialSum a n).pow_const p).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_partialSum_le_tsum ha v n) p)
    (Eventually.of_forall fun v => (tendsto_partialSum ha v).pow p)

theorem integral_rademacher_sq (ha : Summable a) (ha2 : Summable fun k => a k ^ 2) :
    ∫ v, rademacher a v ^ 2 ∂(coins ℕ) = ∑' k, a k ^ 2 :=
  tendsto_nhds_unique (tendsto_integral_partialSum_pow ha 2)
    (by simpa only [fun n => (moments_partialSum a n).1] using ha2.hasSum.tendsto_sum_nat)

theorem integral_rademacher_pow_four_le (ha : Summable a) (ha2 : Summable fun k => a k ^ 2) :
    ∫ v, rademacher a v ^ 4 ∂(coins ℕ) ≤ 3 * (∑' k, a k ^ 2) ^ 2 :=
  le_of_tendsto_of_tendsto' (tendsto_integral_partialSum_pow ha 4)
    ((ha2.hasSum.tendsto_sum_nat.pow 2).const_mul 3) fun n => (moments_partialSum a n).2

/-- **The Paley–Zygmund inequality**: a bounded random variable with `E X² = s > 0` and
`E X⁴ ≤ 3 s²` has `X² > s/4` with probability at least `1/6`. Pointwise,
`X² ≤ s/4 + X⁴/(12 s) + 3 s 1_{X² > s/4}`; integrate. -/
theorem le_measureReal_lt_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {C : ℝ} (hC : ∀ ω, |X ω| ≤ C)
    {s : ℝ} (hs : 0 < s) (h2 : ∫ ω, X ω ^ 2 ∂μ = s) (h4 : ∫ ω, X ω ^ 4 ∂μ ≤ 3 * s ^ 2) :
    1 / 6 ≤ μ.real {ω | s / 4 < X ω ^ 2} := by
  set A := {ω | s / 4 < X ω ^ 2}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hX.pow_const 2)
  have hint : ∀ p : ℕ, Integrable (fun ω => X ω ^ p) μ := fun p =>
    Integrable.of_bound (hX.pow_const p).aestronglyMeasurable (C ^ p)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) p)
  have h12 : 0 < 12 * s := by positivity
  have hpt : ∀ ω, X ω ^ 2 ≤ s / 4 + X ω ^ 4 / (12 * s) + 3 * s * A.indicator 1 ω := fun ω => by
    have h4' : 0 ≤ X ω ^ 4 / (12 * s) := by positivity
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have key : X ω ^ 2 ≤ X ω ^ 4 / (12 * s) + 3 * s := by
        rw [div_add' _ _ _ h12.ne', le_div_iff₀ h12]
        nlinarith [sq_nonneg (X ω ^ 2 - 6 * s)]
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have : X ω ^ 2 ≤ s / 4 := not_lt.1 hω
      linarith
  have hg1 : Integrable (fun ω => s / 4 + X ω ^ 4 / (12 * s)) μ :=
    (integrable_const _).add ((hint 4).div_const _)
  have hg2 : Integrable (fun ω => 3 * s * A.indicator 1 ω) μ :=
    ((integrable_const 1).indicator hA).const_mul _
  have hmono := integral_mono (hint 2)
    (show Integrable (fun ω => s / 4 + X ω ^ 4 / (12 * s) + 3 * s * A.indicator 1 ω) μ from
      hg1.add hg2) hpt
  rw [integral_add hg1 hg2, integral_add (integrable_const _) ((hint 4).div_const _),
    integral_const, integral_div, integral_const_mul, integral_indicator_one hA, h2] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have h4s : (∫ ω, X ω ^ 4 ∂μ) / (12 * s) ≤ s / 4 := by
    rw [div_le_iff₀ h12]
    nlinarith
  nlinarith

/-! ### Unboundedness and the zero-one law -/

/-- `|f(j)|` is unbounded as `j → ∞`, written with countably many quantifiers. -/
def Unbounded (f : ℕ → ℝ) : Prop := ∀ n : ℕ, ∃ j ≥ n, (n : ℝ) < |f j|

theorem Unbounded.of_abs_sub_le {f g : ℕ → ℝ} (h : Unbounded f) {B : ℝ}
    (hB : ∀ j, |f j - g j| ≤ B) : Unbounded g := fun n => by
  obtain ⟨j, hj, hf⟩ := h (n + ⌈B⌉₊)
  refine ⟨j, (Nat.le_add_right n _).trans hj, ?_⟩
  have h1 := hB j
  have h2 := abs_sub_abs_le_abs_sub (f j) (g j)
  have h3 := Nat.le_ceil B
  push_cast at hf
  linarith

theorem not_unbounded_of_tendsto {f : ℕ → ℝ} {L : ℝ} (h : Tendsto f atTop (𝓝 L)) :
    ¬ Unbounded f := fun hu => by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (h.eventually (Metric.ball_mem_nhds L one_pos))
  obtain ⟨j, hj, hlt⟩ := hu (max J ⌈|L| + 1⌉₊)
  have h1 := hJ j ((le_max_left _ _).trans hj)
  rw [Real.dist_eq] at h1
  have h2 := abs_sub_abs_le_abs_sub (f j) L
  have h3 : |L| + 1 ≤ ((max J ⌈|L| + 1⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  linarith

/-- The weighted sum of the coins from `m` on. -/
noncomputable def tailRademacher (a : ℕ → ℝ) (m : ℕ) (v : ℕ → Bool) : ℝ :=
  ∑' k, spin (v (k + m)) * a (k + m)

theorem rademacher_eq_add (ha : Summable a) (v : ℕ → Bool) (m : ℕ) :
    rademacher a v = partialSum a v m + tailRademacher a m v :=
  ((summable_spin_mul ha v).sum_add_tsum_nat_add m).symm

/-- With weights at most `1`, the coins below `m` move the sum by at most `m`, so unboundedness
does not depend on them. -/
theorem unbounded_iff_tail {a : ℕ → ℕ → ℝ} (ha : ∀ j, Summable (a j))
    (ha1 : ∀ j k, |a j k| ≤ 1) (v : ℕ → Bool) (m : ℕ) :
    (Unbounded fun j => rademacher (a j) v) ↔ Unbounded fun j => tailRademacher (a j) m v := by
  have hB : ∀ j, |rademacher (a j) v - tailRademacher (a j) m v| ≤ m := fun j => by
    rw [rademacher_eq_add (ha j) v m, add_sub_cancel_right]
    refine (abs_partialSum_le _ v m).trans ?_
    simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.range m) => ha1 j k
  exact ⟨fun h => h.of_abs_sub_le hB,
    fun h => h.of_abs_sub_le (B := m) fun j => by rw [abs_sub_comm]; exact hB j⟩

/-- The sum of the coins from `m` on is measurable for the coins from `m` on. -/
theorem measurableSet_unbounded_tail {a : ℕ → ℕ → ℝ} (ha : ∀ j, Summable (a j)) (m : ℕ) :
    MeasurableSet[⨆ i ≥ m, coinAlg i]
      {v | Unbounded fun j => tailRademacher (a j) m v} := by
  let : MeasurableSpace (ℕ → Bool) := ⨆ i ≥ m, coinAlg i
  have hk : ∀ k, Measurable fun v : ℕ → Bool => v (k + m) := fun k =>
    Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ≥ m) => coinAlg i) (k + m)
      (Nat.le_add_left m k))
  have hmeas : ∀ j, Measurable (tailRademacher (a j) m) := fun j =>
    measurable_of_tendsto_metrizable
      (fun N => Finset.measurable_sum (Finset.range N) fun k _ =>
        (measurable_spin.comp (hk k)).mul_const (a j (k + m)))
      (tendsto_pi_nhds.2 fun v =>
        ((summable_nat_add_iff m).2 (summable_spin_mul (ha j) v)).hasSum.tendsto_sum_nat)
  have hset : {v : ℕ → Bool | Unbounded fun j => tailRademacher (a j) m v} =
      ⋂ n : ℕ, ⋃ j : ℕ, ⋃ (_ : j ≥ n), {v | (n : ℝ) < |tailRademacher (a j) m v|} := by
    ext v
    simp [Unbounded]
  rw [hset]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const (hmeas j).abs

theorem measurableSet_limsup_unbounded {a : ℕ → ℕ → ℝ} (ha : ∀ j, Summable (a j))
    (ha1 : ∀ j k, |a j k| ≤ 1) :
    MeasurableSet[limsup coinAlg atTop] {v | Unbounded fun j => rademacher (a j) v} := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro m
  rw [show {v : ℕ → Bool | Unbounded fun j => rademacher (a j) v} =
    {v | Unbounded fun j => tailRademacher (a j) m v} from
      Set.ext fun v => unbounded_iff_tail ha ha1 v m]
  exact measurableSet_unbounded_tail ha m

theorem measurableSet_unbounded {a : ℕ → ℕ → ℝ} (ha : ∀ j, Summable (a j)) :
    MeasurableSet {v : ℕ → Bool | Unbounded fun j => rademacher (a j) v} := by
  have hset : {v : ℕ → Bool | Unbounded fun j => rademacher (a j) v} =
      ⋂ n : ℕ, ⋃ j : ℕ, ⋃ (_ : j ≥ n), {v | (n : ℝ) < |rademacher (a j) v|} := by
    ext v
    simp [Unbounded]
  rw [hset]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const (measurable_rademacher (ha j)).abs

theorem summable_sq_of_abs_le_one (ha : Summable a) (ha1 : ∀ k, |a k| ≤ 1) :
    Summable fun k => a k ^ 2 :=
  Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => by
      rw [← sq_abs]
      exact pow_le_of_le_one (abs_nonneg _) (ha1 k) two_ne_zero) ha.abs

/-- **Unbounded sums have positive probability**: if the sums of squares of the weights are
unbounded, then for each `n` some `j ≥ n` has `Xⱼ² > n²` with probability at least `1/6`
(Paley–Zygmund), and so does the decreasing limit. -/
theorem measure_unbounded_ne_zero {a : ℕ → ℕ → ℝ} (ha : ∀ j, Summable (a j))
    (ha1 : ∀ j k, |a j k| ≤ 1) (hσ : ∀ n : ℕ, ∃ j ≥ n, 4 * (n : ℝ) ^ 2 < ∑' k, a j k ^ 2) :
    coins ℕ {v | Unbounded fun j => rademacher (a j) v} ≠ 0 := by
  let B : ℕ → Set (ℕ → Bool) := fun n => ⋃ j ≥ n, {v | (n : ℝ) < |rademacher (a j) v|}
  have hB : ∀ n, ENNReal.ofReal (1 / 6) ≤ coins ℕ (B n) := fun n => by
    obtain ⟨j, hj, hσj⟩ := hσ n
    have ha2 := summable_sq_of_abs_le_one (ha j) (ha1 j)
    have hs : 0 < ∑' k, a j k ^ 2 := lt_of_le_of_lt (by positivity) hσj
    have hpz := le_measureReal_lt_sq (μ := coins ℕ) (measurable_rademacher (ha j))
      (abs_rademacher_le (ha j)) hs (integral_rademacher_sq (ha j) ha2)
      (integral_rademacher_pow_four_le (ha j) ha2)
    refine (ENNReal.ofReal_le_ofReal hpz).trans ?_
    rw [ofReal_measureReal]
    refine measure_mono fun v hv => Set.mem_iUnion₂.2 ⟨j, hj, ?_⟩
    have hv' : (n : ℝ) ^ 2 < rademacher (a j) v ^ 2 := by
      have : (∑' k, a j k ^ 2) / 4 < rademacher (a j) v ^ 2 := hv
      linarith
    have := sq_lt_sq.1 hv'
    rwa [abs_of_nonneg (Nat.cast_nonneg n)] at this
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const (measurable_rademacher (ha j)).abs
  have hanti : Antitone B := fun n m h v hv => by
    simp only [B, Set.mem_iUnion] at hv ⊢
    obtain ⟨j, hj, hv⟩ := hv
    have hv' : (m : ℝ) < |rademacher (a j) v| := hv
    exact ⟨j, h.trans hj, show (n : ℝ) < _ from lt_of_le_of_lt (by exact_mod_cast h) hv'⟩
  have hc : ENNReal.ofReal (1 / 6) ≤ coins ℕ (⋂ n, B n) :=
    ge_of_tendsto (tendsto_measure_iInter_atTop (fun n => (hBm n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩) (Eventually.of_forall hB)
  have hsub : (⋂ n, B n) ⊆ {v | Unbounded fun j => rademacher (a j) v} := fun v hv n => by
    simp only [B, Set.mem_iInter, Set.mem_iUnion] at hv
    obtain ⟨j, hj, hv⟩ := hv n
    exact ⟨j, hj, hv⟩
  intro h0
  have := hc.trans ((measure_mono hsub).trans h0.le)
  simp at this

/-- **Weighted sums of signs whose sums of squares are unbounded are almost surely unbounded.** -/
theorem ae_unbounded {a : ℕ → ℕ → ℝ} (ha : ∀ j, Summable (a j)) (ha1 : ∀ j k, |a j k| ≤ 1)
    (hσ : ∀ n : ℕ, ∃ j ≥ n, 4 * (n : ℝ) ^ 2 < ∑' k, a j k ^ 2) :
    ∀ᵐ v ∂(coins ℕ), Unbounded fun j => rademacher (a j) v := by
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop coinAlg_le iIndep_coinAlg
      (measurableSet_limsup_unbounded ha ha1) with h | h
  · exact absurd h (measure_unbounded_ne_zero ha ha1 hσ)
  · exact ae_iff.2 ((prob_compl_eq_zero_iff (measurableSet_unbounded ha)).2 h)

/-! ### Along a radius -/

/-- The weight `tᵏ Re(wᵏ)` of the coin `k` in the real part of `∑ spin(v(k)) (t w)ᵏ`. -/
noncomputable def radialWeight (w : ℂ) (t : ℝ) (k : ℕ) : ℝ := t ^ k * (w ^ k).re

variable {w : ℂ} {t : ℝ}

theorem abs_radialWeight_le (hw : ‖w‖ = 1) (ht0 : 0 ≤ t) (k : ℕ) :
    |radialWeight w t k| ≤ t ^ k := by
  rw [radialWeight, abs_mul, abs_of_nonneg (pow_nonneg ht0 k)]
  refine mul_le_of_le_one_right (pow_nonneg ht0 k) ?_
  calc |(w ^ k).re| ≤ ‖w ^ k‖ := Complex.abs_re_le_norm _
    _ = 1 := by rw [norm_pow, hw, one_pow]

theorem summable_radialWeight (hw : ‖w‖ = 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (radialWeight w t) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one ht0 ht1) fun k =>
    (Real.norm_eq_abs _).trans_le (abs_radialWeight_le hw ht0 k)

theorem abs_radialWeight_le_one (hw : ‖w‖ = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) :
    |radialWeight w t k| ≤ 1 :=
  (abs_radialWeight_le hw ht0 k).trans (pow_le_one₀ ht0 ht1)

/-- **Along the radius to `w`**, `∑ tᵏ Re(wᵏ) spin(v(k))` is the real part of
`2 f(t w) - 1/(1 - t w)`. -/
theorem rademacher_radialWeight (hw : ‖w‖ = 1) (ht0 : 0 ≤ t) (ht1 : t < 1) (v : ℕ → Bool) :
    rademacher (radialWeight w t) v = (2 * genFun v (t * w) - (1 - t * w)⁻¹).re := by
  have hz : ‖(t : ℂ) * w‖ < 1 := by
    rwa [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]
  have hs1 := summable_coef v hz
  have hs2 : Summable fun k => ((t : ℂ) * w) ^ k :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hz) fun k => by
      rw [norm_pow]
  have key : 2 * genFun v (t * w) - (1 - t * w)⁻¹ =
      ∑' k, (spin (v k) : ℂ) * ((t : ℂ) * w) ^ k := by
    rw [genFun, ← tsum_geometric_of_norm_lt_one hz, ← tsum_mul_left,
      ← (hs1.mul_left 2).tsum_sub hs2]
    congr 1
    ext k
    unfold coef spin
    split_ifs <;> push_cast <;> ring
  have hs3 : Summable fun k => (spin (v k) : ℂ) * ((t : ℂ) * w) ^ k := by
    refine ((hs1.mul_left 2).sub hs2).congr fun k => ?_
    unfold coef spin
    split_ifs <;> push_cast <;> ring
  rw [key, Complex.re_tsum hs3, rademacher]
  congr 1
  ext k
  rw [radialWeight, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- The radii `1 - 1/(j + 1)`. -/
noncomputable def radius (j : ℕ) : ℝ := 1 - 1 / ((j : ℝ) + 1)

theorem radius_nonneg (j : ℕ) : 0 ≤ radius j := by
  rw [radius, sub_nonneg, div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem radius_lt_one (j : ℕ) : radius j < 1 := by
  rw [radius]
  linarith [(by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))]

theorem tendsto_radius : Tendsto radius atTop (𝓝 1) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
  rw [sub_zero] at h
  exact h

/-! ### Directions -/

/-- The point `e^{iπ(2p+1)/(N+1)}` of the unit circle, a root of `z^(N+1) = -1`. -/
noncomputable def dir (p : ℤ) (N : ℕ) : ℂ :=
  Complex.exp (↑(Real.pi * (2 * p + 1) / (N + 1)) * Complex.I)

theorem norm_dir (p : ℤ) (N : ℕ) : ‖dir p N‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem dir_pow (p : ℤ) (N : ℕ) : dir p N ^ (N + 1) = -1 := by
  rw [dir, ← Complex.exp_nat_mul]
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have : ((N + 1 : ℕ) : ℂ) * (↑(Real.pi * (2 * p + 1) / (N + 1)) * Complex.I) =
      ↑Real.pi * Complex.I + p * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem dir_ne_one (p : ℤ) (N : ℕ) : dir p N ≠ 1 := fun h => by
  have := dir_pow p N
  rw [h, one_pow] at this
  norm_num at this

/-- At the multiples of `N + 1` the weights toward `dir p N` are `± t^((N+1) i)`, so the sum of
their squares is at least `1/(1 - t^(2N+2))`. -/
theorem le_tsum_radialWeight_sq (p : ℤ) (N : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t ^ (2 * (N + 1)))⁻¹ ≤ ∑' k, radialWeight (dir p N) t k ^ 2 := by
  have hsum : Summable fun k => radialWeight (dir p N) t k ^ 2 :=
    summable_sq_of_abs_le_one (summable_radialWeight (norm_dir p N) ht0 ht1)
      (abs_radialWeight_le_one (norm_dir p N) ht0 ht1.le)
  have hinj : Function.Injective fun i : ℕ => (N + 1) * i := fun i j h =>
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos N) h
  refine le_trans (le_of_eq ?_) (tsum_comp_le_tsum_of_inj hsum (fun k => sq_nonneg _) hinj)
  rw [← tsum_geometric_of_lt_one (by positivity) (pow_lt_one₀ ht0 ht1 (by omega))]
  congr 1
  ext i
  have hre : ((-1 : ℂ) ^ i).re ^ 2 = 1 := by
    rcases neg_one_pow_eq_or ℂ i with h | h <;> simp [h]
  simp only [Function.comp, radialWeight]
  rw [pow_mul (dir p N) (N + 1) i, dir_pow, mul_pow, hre, mul_one, ← pow_mul, ← pow_mul]
  congr 1
  ring

/-- Toward `dir p N` the sums of squares along the radii `radius j` are unbounded. -/
theorem exists_lt_tsum_radialWeight_sq (p : ℤ) (N : ℕ) (n : ℕ) :
    ∃ j ≥ n, 4 * (n : ℝ) ^ 2 < ∑' k, radialWeight (dir p N) (radius j) k ^ 2 := by
  refine ⟨8 * (N + 1) * n ^ 2 + n, Nat.le_add_left n _, lt_of_lt_of_le ?_
    (le_tsum_radialWeight_sq p N (radius_nonneg _) (radius_lt_one _))⟩
  set j := 8 * (N + 1) * n ^ 2 + n with hj
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hj1]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- Bernoulli: `radius j ^ M ≥ 1 - M / (j + 1)`
  have hb := one_add_mul_le_pow (a := -(1 / ((j : ℝ) + 1))) (by linarith) (2 * (N + 1))
  rw [show (1 : ℝ) + -(1 / ((j : ℝ) + 1)) = radius j by rw [radius]; ring] at hb
  have hpos : 0 < 1 - radius j ^ (2 * (N + 1)) :=
    sub_pos.2 (pow_lt_one₀ (radius_nonneg j) (radius_lt_one j) (by omega))
  have hle : 1 - radius j ^ (2 * (N + 1)) ≤ ((2 * (N + 1) : ℕ) : ℝ) / ((j : ℝ) + 1) := by
    have : ((2 * (N + 1) : ℕ) : ℝ) * -(1 / ((j : ℝ) + 1)) =
        -(((2 * (N + 1) : ℕ) : ℝ) / ((j : ℝ) + 1)) := by ring
    linarith
  refine lt_of_lt_of_le ?_ (inv_anti₀ hpos hle)
  rw [inv_div, lt_div_iff₀ (by positivity)]
  have hjn : (j : ℝ) = 8 * ((N : ℝ) + 1) * n ^ 2 + n := by
    rw [hj]
    push_cast
    ring
  rw [hjn]
  push_cast
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ### Analytic continuation -/

/-- **An analytic continuation across the circle at `w ≠ 1` makes `2 f(t w) - 1/(1 - t w)`
converge** as `t → 1` along the radii `radius j`. -/
theorem tendsto_rademacher_of_continuation {v : ℕ → Bool} {z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball z₀ r))
    (hgf : ∀ z ∈ Metric.ball z₀ r, ‖z‖ < 1 → g z = genFun v z)
    (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (hwb : w ∈ Metric.ball z₀ r) :
    Tendsto (fun j => rademacher (radialWeight w (radius j)) v) atTop
      (𝓝 ((2 * g w - (1 - w)⁻¹).re)) := by
  have htend : Tendsto (fun j => (radius j : ℂ) * w) atTop (𝓝 w) := by
    simpa using ((Complex.continuous_ofReal.tendsto 1).comp tendsto_radius).mul_const w
  have hcont : ContinuousAt (fun z => (2 * g z - (1 - z)⁻¹).re) w :=
    Complex.continuous_re.continuousAt.comp
      ((continuousAt_const.mul (hg w hwb).continuousAt).sub
        ((continuousAt_const.sub continuousAt_id).inv₀ (sub_ne_zero.2 (Ne.symm hw1))))
  refine (hcont.tendsto.comp htend).congr' ?_
  filter_upwards [htend.eventually (Metric.isOpen_ball.mem_nhds hwb)] with j hj
  have hn : ‖(radius j : ℂ) * w‖ < 1 := by
    rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_of_nonneg (radius_nonneg j)]
    exact radius_lt_one j
  simp only [Function.comp_apply]
  rw [rademacher_radialWeight hw (radius_nonneg j) (radius_lt_one j), hgf _ hj hn]

/-- **The points `dir p N` are dense in the unit circle.** -/
theorem exists_dir_mem_ball {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {r : ℝ} (hr : 0 < r) :
    ∃ (p : ℤ) (N : ℕ), dir p N ∈ Metric.ball z₀ r := by
  have hcont : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by fun_prop
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuous_iff.1 hcont (Complex.arg z₀) r hr
  have hz : Complex.exp (Complex.arg z₀ * Complex.I) = z₀ := by
    have h := Complex.norm_mul_exp_arg_mul_I z₀
    rwa [hz₀, Complex.ofReal_one, one_mul] at h
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hδ Real.pi_pos)
  set y : ℝ := (Complex.arg z₀ * (N + 1) / Real.pi - 1) / 2 with hy
  refine ⟨round y, N, ?_⟩
  rw [Metric.mem_ball, ← hz, dir]
  refine hδr _ ?_
  rw [Real.dist_eq]
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hπ := Real.pi_pos
  have heq : Real.pi * (2 * ((round y : ℤ) : ℝ) + 1) / (N + 1) - Complex.arg z₀ =
      -(2 * Real.pi / (N + 1)) * (y - round y) := by
    rw [hy]
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_of_pos (by positivity)]
  calc 2 * Real.pi / (N + 1) * |y - round y| ≤ 2 * Real.pi / (N + 1) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round y) (by positivity)
    _ = Real.pi * (1 / (N + 1)) := by ring
    _ < Real.pi * (δ / Real.pi) := mul_lt_mul_of_pos_left hN hπ
    _ = δ := by field_simp

/-! ### Almost every sequence -/

/-- If, toward every `dir p N`, the real parts of `2 f(t w) - 1/(1 - t w)` are unbounded as
`t → 1`, the unit circle is a natural boundary. -/
theorem circleIsNaturalBoundary_of_unbounded {v : ℕ → Bool}
    (h : ∀ (p : ℤ) (N : ℕ), Unbounded fun j => rademacher (radialWeight (dir p N) (radius j)) v) :
    CircleIsNaturalBoundary v := by
  rintro z₀ hz₀ r hr ⟨g, hg, hgf⟩
  obtain ⟨p, N, hb⟩ := exists_dir_mem_ball hz₀ hr
  exact not_unbounded_of_tendsto
    (tendsto_rademacher_of_continuation hg hgf (norm_dir p N) (dir_ne_one p N) hb) (h p N)

/-- **The generating function of almost every sequence of fair coins has the unit circle as a
natural boundary.** -/
theorem ae_circleIsNaturalBoundary : ∀ᵐ v ∂(coins ℕ), CircleIsNaturalBoundary v := by
  have h : ∀ (p : ℤ) (N : ℕ), ∀ᵐ v ∂(coins ℕ),
      Unbounded fun j => rademacher (radialWeight (dir p N) (radius j)) v := fun p N =>
    ae_unbounded
      (fun j => summable_radialWeight (norm_dir p N) (radius_nonneg j) (radius_lt_one j))
      (fun j k => abs_radialWeight_le_one (norm_dir p N) (radius_nonneg j) (radius_lt_one j).le k)
      (exists_lt_tsum_radialWeight_sq p N)
  filter_upwards [ae_all_iff.2 fun p => ae_all_iff.2 (h p)] with v hv
  exact circleIsNaturalBoundary_of_unbounded hv

/-- **The generating function of the center column of almost every configuration has the unit
circle as a natural boundary.** -/
theorem ae_circleIsNaturalBoundary_trace :
    ∀ᵐ x ∂(coins ℤ), CircleIsNaturalBoundary (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_circleIsNaturalBoundary

/-- For the center column of the single seed, the natural boundary would prove Problem 1. -/
theorem problem1_of_circleIsNaturalBoundary (h : CircleIsNaturalBoundary c) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_natural_boundary h

end Rule30Equivalents.RandomNaturalBoundary
