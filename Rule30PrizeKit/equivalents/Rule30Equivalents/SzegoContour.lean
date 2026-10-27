module

public import Rule30Equivalents.SzegoPolynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr

/-!
# Szegő's contour: approximate recurrences from a continuation

Let `f(z) = Σ aₙ zⁿ` have coefficients `‖aₙ‖ ≤ 1`, and let `Tₙ(z) = Σₘ a(n + m) zᵐ` be its
tails (`tail`). For a polynomial `W = Σ wⱼ Xʲ`, the combination `Σⱼ wⱼ a(n + j)` is a contour
integral of `Tₙ(z) W(1/z)/z` (`circleIntegral_tail_mul`): on a circle of radius `ρ < 1` around `0`
the monomials `zᵏ` integrate to `2πi` for `k = -1` and to `0` otherwise
(`circleIntegral_zpow`, `circleIntegral_partial_mul`), and the tail beyond `N` contributes
`O(ρᴺ)`.

If `f` continues analytically to a disk around `1`, as `g`, the tails continue as
`(g(z) - Σ_{j<n} aⱼ zʲ)/zⁿ` (`contTail`), and Cauchy's theorem on an annular sector
(`sector_integral_eq`) moves the arc `|arg z| ≤ τ` of the circle out to a radius `R > 1`.
Outside the unit circle the continued tails are at most `‖g(z)‖ + (‖z‖ - 1)⁻¹`
(`norm_contTail_le`), and the factor `(1/z - e^{iτ})(1/z - e^{-iτ})` cancels that growth where
the contour crosses the circle (`norm_contTail_mul_le`). With `W` the monic polynomial of
`SzegoPolynomial.exists_notch_poly` times `(X - e^{iτ})(X - e^{-iτ})`, every piece of the contour
is at most a constant times `qᴰ` with `q < 1`. So (`exists_approx_recurrence`, Szegő's analytic
step) for every `ε > 0` some monic `W` has `‖Σⱼ wⱼ a(n + j)‖ < ε` for every `n`.

Sources: G. Szegő, *Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten*,
Sitzungsber. Preuss. Akad. Wiss. (1922) 88–91; P. Dienes, *The Taylor series*, Dover (1957),
chapter X; P. Borwein, T. Erdélyi and F. Littmann, *Polynomials with coefficients from a finite
set*, Trans. Amer. Math. Soc. 360 (2008) 5145–5154, section 3.
-/

@[expose] public section

namespace Rule30Equivalents.SzegoContour

open Complex Polynomial MeasureTheory Filter Topology Metric
open scoped Interval

/-- `∮ zᵏ` over a circle around `0` is `2πi` for `k = -1` and `0` otherwise. -/
theorem circleIntegral_zpow (k : ℤ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ z in C(0, ρ), z ^ k) = if k = -1 then 2 * Real.pi * I else 0 := by
  split_ifs with hk
  · subst hk
    have h := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := 0) (R := ρ)
      (mem_ball_self hρ)
    simpa [zpow_neg_one] using h
  · simpa using circleIntegral.integral_sub_zpow_of_ne hk (0 : ℂ) 0 ρ

/-- **Pairing a polynomial with `W(1/z)/z`**: `∮ (Σ_{m<N} bₘ zᵐ) W(1/z)/z = 2πi Σⱼ bⱼ wⱼ`, the sum
over `j ≤ deg W` with `j < N`. -/
theorem circleIntegral_partial_mul (b : ℕ → ℂ) (N : ℕ) (W : ℂ[X]) {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ z in C(0, ρ), (∑ m ∈ Finset.range N, b m * z ^ m) * (W.eval z⁻¹ * z⁻¹)) =
      2 * Real.pi * I * ∑ j ∈ Finset.range (W.natDegree + 1),
        (if j < N then b j else 0) * W.coeff j := by
  -- the integrand as a double sum of monomials
  have hcongr : Set.EqOn (fun z => (∑ m ∈ Finset.range N, b m * z ^ m) * (W.eval z⁻¹ * z⁻¹))
      (fun z => ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range (W.natDegree + 1),
        b m * W.coeff j * z ^ ((m : ℤ) - j - 1)) (sphere 0 ρ) := fun z hz => by
    have hz0 : z ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz; linarith
    simp only
    rw [eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((m : ℤ) - j - 1) = (m : ℤ) - ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ hz0,
      zpow_natCast, zpow_natCast, div_eq_mul_inv, ← inv_pow, pow_succ]
    ring
  have hcont : ∀ (m j : ℕ), ContinuousOn
      (fun z => b m * W.coeff j * z ^ ((m : ℤ) - j - 1)) (sphere 0 ρ) := fun m j =>
    continuousOn_const.mul (continuousOn_id.zpow₀ _ fun z hz =>
      Or.inl (ne_zero_of_mem_sphere hρ.ne' ⟨z, hz⟩))
  have hint : ∀ (m j : ℕ), CircleIntegrable
      (fun z => b m * W.coeff j * z ^ ((m : ℤ) - j - 1)) 0 ρ := fun m j =>
    (hcont m j).circleIntegrable hρ.le
  rw [circleIntegral.integral_congr hρ.le hcongr,
    circleIntegral.integral_fun_sum fun m _ => ?_]
  · simp_rw [circleIntegral.integral_fun_sum fun j _ => hint _ j, circleIntegral.integral_const_mul,
      circleIntegral_zpow _ hρ]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ m : ℕ, ((m : ℤ) - j - 1 = -1 ↔ m = j) := fun m => by omega
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    split_ifs <;> ring
  · -- each `m`-term is integrable
    exact (continuousOn_finsetSum _ fun j _ => hcont m j).circleIntegrable hρ.le

/-! ### Tails -/

/-- The tails `Tₙ(z) = Σₘ a(n + m) zᵐ` of `Σ aₙ zⁿ`. -/
noncomputable def tail (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ := ∑' m, a (n + m) * z ^ m

variable {a : ℕ → ℂ}

theorem norm_term_le (ha : ∀ n, ‖a n‖ ≤ 1) (n m : ℕ) (z : ℂ) : ‖a (n + m) * z ^ m‖ ≤ ‖z‖ ^ m := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (ha _)

theorem summable_tail (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun m => a (n + m) * z ^ m :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun m =>
    norm_term_le ha n m z

theorem norm_tail_le (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖tail a n z‖ ≤ (1 - ‖z‖)⁻¹ := by
  have hs := summable_geometric_of_lt_one (norm_nonneg z) hz
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => norm_term_le ha n m z) hs)).trans ?_
  rw [← tsum_geometric_of_lt_one (norm_nonneg z) hz]
  exact Summable.tsum_le_tsum (fun m => norm_term_le ha n m z)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => norm_term_le ha n m z) hs) hs

/-- `Tₙ(z) = Σ_{m<N} a(n + m) zᵐ + zᴺ T_{n+N}(z)`. -/
theorem tail_eq_add (ha : ∀ n, ‖a n‖ ≤ 1) (n N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    tail a n z = (∑ m ∈ Finset.range N, a (n + m) * z ^ m) + z ^ N * tail a (n + N) z := by
  rw [tail, ← (summable_tail ha n hz).sum_add_tsum_nat_add N, tail, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun m => ?_
  rw [pow_add, show n + (m + N) = n + N + m by ring]
  ring

theorem continuousOn_tail (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ContinuousOn (tail a n) (closedBall 0 ρ) :=
  continuousOn_tsum (fun m => by fun_prop) (summable_geometric_of_lt_one hρ0 hρ1)
    fun m z hz => (norm_term_le ha n m z).trans
      (pow_le_pow_left₀ (norm_nonneg z) (mem_closedBall_zero_iff.1 hz) m)

/-- `W(1/z)/z`, continuous away from `0`. -/
theorem continuousOn_eval_inv_mul (W : ℂ[X]) {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (fun z : ℂ => W.eval z⁻¹ * z⁻¹) (sphere 0 ρ) := by
  have h0 : ∀ z ∈ sphere (0 : ℂ) ρ, z ≠ 0 := fun z hz => ne_zero_of_mem_sphere hρ.ne' ⟨z, hz⟩
  exact (W.continuous.comp_continuousOn (continuousOn_inv₀.mono fun z hz => h0 z hz)).mul
    (continuousOn_inv₀.mono fun z hz => h0 z hz)

/-- **The coefficient identity**: `∮_{|z|=ρ} Tₙ(z) W(1/z)/z = 2πi Σⱼ a(n + j) wⱼ`. -/
theorem circleIntegral_tail_mul (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) (W : ℂ[X]) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    (∮ z in C(0, ρ), tail a n z * (W.eval z⁻¹ * z⁻¹)) =
      2 * Real.pi * I * ∑ j ∈ Finset.range (W.natDegree + 1), a (n + j) * W.coeff j := by
  set E := 2 * Real.pi * I * ∑ j ∈ Finset.range (W.natDegree + 1), a (n + j) * W.coeff j
  -- a bound for `W(1/z)/z` on the circle
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ sphere (0 : ℂ) ρ, ‖W.eval z⁻¹ * z⁻¹‖ ≤ B :=
    (isCompact_sphere 0 ρ).exists_bound_of_continuousOn (continuousOn_eval_inv_mul W hρ0)
  have hsph : ∀ z ∈ sphere (0 : ℂ) ρ, ‖z‖ = ρ := fun z hz => mem_sphere_zero_iff_norm.1 hz
  have hcL := continuousOn_eval_inv_mul W hρ0
  have hct : ∀ m, ContinuousOn (tail a m) (sphere 0 ρ) := fun m =>
    (continuousOn_tail ha m hρ0.le hρ1).mono sphere_subset_closedBall
  have key : ∀ N, W.natDegree + 1 ≤ N →
      ‖(∮ z in C(0, ρ), tail a n z * (W.eval z⁻¹ * z⁻¹)) - E‖ ≤
        2 * Real.pi * ρ * (ρ ^ N * (1 - ρ)⁻¹ * B) := fun N hN => by
    have h1 : CircleIntegrable (fun z => (∑ m ∈ Finset.range N, a (n + m) * z ^ m) *
        (W.eval z⁻¹ * z⁻¹)) 0 ρ :=
      ((continuousOn_finsetSum _ fun m _ => by fun_prop).mul hcL).circleIntegrable hρ0.le
    have h2 : CircleIntegrable (fun z => z ^ N * tail a (n + N) z * (W.eval z⁻¹ * z⁻¹)) 0 ρ :=
      (((continuousOn_pow N).mul (hct (n + N))).mul hcL).circleIntegrable hρ0.le
    have hsplit : (∮ z in C(0, ρ), tail a n z * (W.eval z⁻¹ * z⁻¹)) =
        (∮ z in C(0, ρ), (∑ m ∈ Finset.range N, a (n + m) * z ^ m) * (W.eval z⁻¹ * z⁻¹)) +
          ∮ z in C(0, ρ), z ^ N * tail a (n + N) z * (W.eval z⁻¹ * z⁻¹) := by
      rw [← circleIntegral.integral_add h1 h2]
      refine circleIntegral.integral_congr hρ0.le fun z hz => ?_
      rw [tail_eq_add ha n N (by rw [hsph z hz]; exact hρ1)]
      ring
    rw [hsplit, circleIntegral_partial_mul (fun m => a (n + m)) N W hρ0]
    have hif : ∑ j ∈ Finset.range (W.natDegree + 1), (if j < N then a (n + j) else 0) *
        W.coeff j = ∑ j ∈ Finset.range (W.natDegree + 1), a (n + j) * W.coeff j :=
      Finset.sum_congr rfl fun j hj => by
        rw [ite_eq_left (lt_of_lt_of_le (Finset.mem_range.1 hj) hN)]
    rw [hif, add_sub_cancel_left]
    refine circleIntegral.norm_integral_le_of_norm_le_const hρ0.le fun z hz => ?_
    rw [norm_mul, norm_mul, norm_pow, hsph z hz]
    gcongr
    · exact (norm_tail_le ha _ (by rw [hsph z hz]; exact hρ1)).trans_eq (by rw [hsph z hz])
    · exact hB z hz
  -- the remainder is at most a constant times `ρᴺ` for all large `N`
  have hlim : Tendsto (fun N => 2 * Real.pi * ρ * (ρ ^ N * (1 - ρ)⁻¹ * B)) atTop (𝓝 0) := by
    have := (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const
      (1 - ρ)⁻¹).mul_const B).const_mul (2 * Real.pi * ρ)
    simpa using this
  have hle : ‖(∮ z in C(0, ρ), tail a n z * (W.eval z⁻¹ * z⁻¹)) - E‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨W.natDegree + 1, key⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-! ### Arcs and Cauchy's theorem on an annular sector -/

/-- The integrand of a circle integral at angle `θ`: `F(ρ e^{iθ}) · iρe^{iθ}`. -/
noncomputable def arcIntegrand (F : ℂ → ℂ) (ρ θ : ℝ) : ℂ :=
  F (ρ * exp (θ * I)) * (ρ * exp (θ * I) * I)

theorem continuous_arcIntegrand {F : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hF : ContinuousOn F (sphere 0 ρ)) : Continuous (arcIntegrand F ρ) := by
  have hc : Continuous fun θ : ℝ => (ρ : ℂ) * exp (θ * I) := by fun_prop
  have hmem : ∀ θ : ℝ, (ρ : ℂ) * exp (θ * I) ∈ sphere (0 : ℂ) ρ := fun θ => by
    rw [← circleMap_zero]
    exact circleMap_mem_sphere 0 hρ θ
  unfold arcIntegrand
  exact (hF.comp_continuous hc hmem).mul (hc.mul continuous_const)

/-- **The circle as two arcs**: `∮_{|z|=ρ} F = ∫_{-τ}^{τ} + ∫_{τ}^{2π-τ}` of the arc integrand. -/
theorem circleIntegral_eq_arcs {F : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hF : ContinuousOn F (sphere 0 ρ)) (τ : ℝ) :
    (∮ z in C(0, ρ), F z) =
      (∫ θ in -τ..τ, arcIntegrand F ρ θ) + ∫ θ in τ..2 * Real.pi - τ, arcIntegrand F ρ θ := by
  have hg : (∮ z in C(0, ρ), F z) = ∫ θ in (0 : ℝ)..0 + 2 * Real.pi, arcIntegrand F ρ θ := by
    rw [zero_add, circleIntegral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, arcIntegrand]
    ring
  have hper : Function.Periodic (arcIntegrand F ρ) (2 * Real.pi) := fun θ => by
    simp only [arcIntegrand, ← circleMap_zero, periodic_circleMap 0 ρ θ]
  have hc := continuous_arcIntegrand hρ hF
  rw [hg, hper.intervalIntegral_add_eq 0 (-τ),
    ← intervalIntegral.integral_add_adjacent_intervals (b := τ) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  congr 2
  ring

/-- **Cauchy's theorem on an annular sector** `{eˢ : s ∈ [log ρ, log R] × [-τ, τ]}`, from the
rectangle in logarithmic coordinates: the inner arc equals the outer arc plus the radial segment
at `-τ` minus the one at `τ`. -/
theorem sector_integral_eq {F : ℂ → ℂ} {ρ R τ : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hF : DifferentiableOn ℂ (fun s => F (exp s) * exp s)
      (Set.uIcc (Real.log ρ) (Real.log R) ×ℂ Set.uIcc (-τ) τ)) :
    (∫ θ in -τ..τ, arcIntegrand F ρ θ) =
      (∫ θ in -τ..τ, arcIntegrand F R θ) +
      (∫ x in Real.log ρ..Real.log R, F (exp x * exp (-τ * I)) * (exp x * exp (-τ * I))) -
      (∫ x in Real.log ρ..Real.log R, F (exp x * exp (τ * I)) * (exp x * exp (τ * I))) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun s => F (exp s) * exp s) (Real.log ρ + (-τ : ℝ) * I) (Real.log R + τ * I) (by
      simpa using hF)
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add] at h
  have hexp : ∀ (r : ℝ), 0 < r → ∀ θ : ℝ, exp ((Real.log r : ℂ) + θ * I) = r * exp (θ * I) :=
    fun r hr θ => by rw [exp_add, ← ofReal_exp, Real.exp_log hr]
  have hside : ∀ (r : ℝ), 0 < r → I * (∫ y in -τ..τ, F (exp ((Real.log r : ℂ) + y * I)) *
      exp ((Real.log r : ℂ) + y * I)) = ∫ θ in -τ..τ, arcIntegrand F r θ := fun r hr => by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hexp r hr θ, arcIntegrand]
    ring
  have hrad : ∀ y : ℝ, (∫ x in Real.log ρ..Real.log R, F (exp ((x : ℂ) + y * I)) *
      exp ((x : ℂ) + y * I)) = ∫ x in Real.log ρ..Real.log R,
        F (exp x * exp (y * I)) * (exp x * exp (y * I)) := fun y => by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [exp_add]
  rw [hrad, hrad, smul_eq_mul, smul_eq_mul] at h
  rw [← hside ρ hρ, ← hside R hR]
  push_cast at h ⊢
  linear_combination (-1 : ℂ) * h

/-! ### The continued tails -/

/-- The tail continued through `g`: `(g(z) - Σ_{j<n} aⱼ zʲ)/zⁿ`. -/
noncomputable def contTail (a : ℕ → ℂ) (g : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (g z - ∑ j ∈ Finset.range n, a j * z ^ j) / z ^ n

/-- Where `g` is the series, the continued tail is the tail. -/
theorem contTail_eq_tail (ha : ∀ n, ‖a n‖ ≤ 1) {g : ℂ → ℂ} (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) (hg : g z = ∑' j, a j * z ^ j) : contTail a g n z = tail a n z := by
  have hs : Summable fun j => a j * z ^ j := by
    simpa using summable_tail ha 0 hz
  rw [contTail, hg, ← hs.sum_add_tsum_nat_add n, add_sub_cancel_left, tail,
    div_eq_iff (pow_ne_zero n hz0), ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  rw [add_comm m n, pow_add]
  ring

/-- Outside the unit circle, `‖contTail‖ ≤ ‖g(z)‖ + (‖z‖ - 1)⁻¹`. -/
theorem norm_contTail_le (ha : ∀ n, ‖a n‖ ≤ 1) (g : ℂ → ℂ) (n : ℕ) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖contTail a g n z‖ ≤ ‖g z‖ + (‖z‖ - 1)⁻¹ := by
  set t := ‖z‖ with ht
  have ht0 : 0 < t := by linarith
  have htn : 1 ≤ t ^ n := one_le_pow₀ hz.le
  rw [contTail, norm_div, norm_pow, ← ht, div_le_iff₀ (by positivity)]
  have hsum : ‖∑ j ∈ Finset.range n, a j * z ^ j‖ ≤ (t ^ n - 1) / (t - 1) := by
    refine (norm_sum_le _ _).trans ?_
    rw [← geom_sum_eq (by linarith : t ≠ 1)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_pow, ← ht]
    exact mul_le_of_le_one_left (by positivity) (ha j)
  have h1 : (t ^ n - 1) / (t - 1) ≤ (t - 1)⁻¹ * t ^ n := by
    rw [div_le_iff₀ (by linarith)]
    have : (t - 1)⁻¹ * t ^ n * (t - 1) = t ^ n := by field_simp
    linarith
  calc ‖g z - ∑ j ∈ Finset.range n, a j * z ^ j‖ ≤ ‖g z‖ + (t ^ n - 1) / (t - 1) :=
        (norm_sub_le _ _).trans (by linarith)
    _ ≤ ‖g z‖ * t ^ n + (t - 1)⁻¹ * t ^ n := by nlinarith [norm_nonneg (g z)]
    _ = (‖g z‖ + (t - 1)⁻¹) * t ^ n := by ring

/-- Near the unit circle the continued tail grows at most like `|‖z‖ - 1|⁻¹`, which the factor
`|‖z‖⁻¹ - 1|` cancels. -/
theorem norm_contTail_mul_le (ha : ∀ n, ‖a n‖ ≤ 1) {g : ℂ → ℂ} (n : ℕ) {z : ℂ} {M : ℝ}
    (hM : ‖g z‖ ≤ M) (hz : 1 / 2 ≤ ‖z‖) (hg : ‖z‖ < 1 → g z = ∑' j, a j * z ^ j) :
    ‖contTail a g n z‖ * |‖z‖⁻¹ - 1| ≤ M + 2 := by
  set t := ‖z‖ with ht
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have ht0 : 0 < t := by linarith
  have hti : t⁻¹ ≤ 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  rcases lt_trichotomy t 1 with h | h | h
  · have hge : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).2 h.le
    rw [contTail_eq_tail ha n h (norm_pos_iff.1 ht0) (hg h), abs_of_nonneg (by linarith)]
    have h1 : ‖tail a n z‖ ≤ (1 - t)⁻¹ := norm_tail_le ha n h
    have h2 : (1 - t)⁻¹ * (t⁻¹ - 1) = t⁻¹ := by
      have : 1 - t ≠ 0 := by linarith
      field_simp
    calc ‖tail a n z‖ * (t⁻¹ - 1) ≤ (1 - t)⁻¹ * (t⁻¹ - 1) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = t⁻¹ := h2
      _ ≤ M + 2 := by linarith
  · rw [h, inv_one, sub_self, abs_zero, mul_zero]
    linarith
  · have hle : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h.le
    rw [abs_of_nonpos (by linarith)]
    have h1 : ‖contTail a g n z‖ ≤ ‖g z‖ + (t - 1)⁻¹ := norm_contTail_le ha g n h
    have h2 : (t - 1)⁻¹ * -(t⁻¹ - 1) = t⁻¹ := by
      have : t - 1 ≠ 0 := by linarith
      field_simp
      ring
    calc ‖contTail a g n z‖ * -(t⁻¹ - 1) ≤ (M + (t - 1)⁻¹) * -(t⁻¹ - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = M * (1 - t⁻¹) + t⁻¹ := by rw [add_mul, h2]; ring
      _ ≤ M + 2 := by nlinarith [mul_nonneg hM0 hti0.le]

/-- On the arc `τ ≤ θ ≤ 2π - τ`, `cos θ ≤ cos τ`. -/
theorem cos_le_cos_of_mem_arc {τ θ : ℝ} (hτ0 : 0 ≤ τ) (h1 : τ ≤ θ)
    (h2 : θ ≤ 2 * Real.pi - τ) : Real.cos θ ≤ Real.cos τ := by
  rcases le_total θ Real.pi with hθ | hθ
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hτ0 hθ h1
  · rw [← Real.cos_two_pi_sub θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hτ0 (by linarith) (by linarith)

/-- `exp (x + y i) = eˣ e^{iy}`, with `‖e^{iy}‖ = 1`. -/
theorem exp_re_add_im (w : ℂ) : exp w = (Real.exp w.re : ℂ) * exp (w.im * I) := by
  conv_lhs => rw [← re_add_im w]
  rw [exp_add, ← ofReal_exp]

/-! ### Szegő's analytic step -/

/-- **Szegő's analytic step**: if `f(z) = Σ aₙ zⁿ` with `‖aₙ‖ ≤ 1` continues analytically to a disk
around `1`, then for every `ε > 0` some monic `W = Σ wⱼ Xʲ` has `‖Σⱼ a(n + j) wⱼ‖ < ε` for every
`n`. The combination is `(2πi)⁻¹ ∮ Tₙ(z) W(1/z)/z` over a circle of radius `ρ < 1`
(`circleIntegral_tail_mul`); across the arc `|arg z| ≤ τ` the circle is pushed out to radius
`R > 1` (`sector_integral_eq`), where the continued tails are bounded. With `W` the polynomial of
`SzegoPolynomial.exists_notch_poly` times `(w - e^{iτ})(w - e^{-iτ})`, whose last factors vanish
where the contour crosses the unit circle, the integrand is at most a constant times `qᴰ`. -/
theorem exists_approx_recurrence (ha : ∀ n, ‖a n‖ ≤ 1) {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 1 r))
    (hgf : ∀ z ∈ ball (1 : ℂ) r, ‖z‖ < 1 → g z = ∑' n, a n * z ^ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : ℂ[X], W.Monic ∧
      ∀ n, ‖∑ j ∈ Finset.range (W.natDegree + 1), a (n + j) * W.coeff j‖ < ε := by
  -- the geometry: an annular sector `ρ ≤ |z| ≤ R`, `|arg z| ≤ τ` inside `ball 1 r`
  set s := min r 1 / 4 with hsdef
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 / 4 := by have := min_le_right r 1; rw [hsdef]; linarith
  have hsr : 2 * s < r := by have := min_le_left r 1; rw [hsdef]; linarith
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  have hτ1 : s < Real.pi / 2 := by linarith
  obtain ⟨ρ₁, ρ₂, q, hρ₁0, hρ₁h, hρ₁1, hρ₂1, hρ₂3, hq0, hq1, hP⟩ :=
    SzegoPolynomial.exists_notch_poly hs0 hτ1 (ρ₀ := 1 / (1 + s)) (ρ₃ := 1 / (1 - s))
      (by rw [div_lt_one (by linarith)]; linarith) (by rw [lt_div_iff₀ (by linarith)]; linarith)
  set ρ := ρ₂⁻¹ with hρdef
  set R := ρ₁⁻¹ with hRdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ hρ₂1
  have hρs : 1 - s ≤ ρ := by
    rw [hρdef, le_inv_comm₀ (by linarith) (by linarith)]
    calc ρ₂ ≤ 1 / (1 - s) := hρ₂3
      _ = (1 - s)⁻¹ := one_div _
  have hR1 : 1 < R := (one_lt_inv₀ (by linarith)).2 hρ₁1
  have hRs : R ≤ 1 + s := by
    rw [hRdef, inv_le_comm₀ (by linarith) (by linarith)]
    calc (1 + s)⁻¹ = 1 / (1 + s) := (one_div _).symm
      _ ≤ ρ₁ := hρ₁0
  have hρ34 : 3 / 4 ≤ ρ := by linarith
  set Rect := Set.uIcc (Real.log ρ) (Real.log R) ×ℂ Set.uIcc (-s) s with hRectdef
  have hRect : ∀ w ∈ Rect, exp w ∈ ball (1 : ℂ) r ∧ ρ ≤ Real.exp w.re ∧ Real.exp w.re ≤ R := by
    intro w hw
    rw [hRectdef, Complex.mem_reProdIm] at hw
    obtain ⟨hx, hy⟩ := hw
    have hlog : Real.log ρ ≤ Real.log R := Real.log_le_log hρ0 (by linarith)
    rw [Set.uIcc_of_le hlog] at hx
    rw [Set.uIcc_of_le (by linarith)] at hy
    have he1 : ρ ≤ Real.exp w.re := by
      rw [← Real.exp_log hρ0]; exact Real.exp_le_exp.2 hx.1
    have he2 : Real.exp w.re ≤ R := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < R)]; exact Real.exp_le_exp.2 hx.2
    refine ⟨?_, he1, he2⟩
    rw [mem_ball, dist_eq, exp_re_add_im]
    have hu : ‖exp (w.im * I)‖ = 1 := norm_exp_ofReal_mul_I _
    have hu1 : ‖exp (w.im * I) - 1‖ ≤ s := by
      rw [mul_comm]
      refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := w.im)).trans ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1, hy.2]
    have hex : |Real.exp w.re - 1| ≤ s := by
      rw [abs_le]
      constructor <;> linarith
    have e : (Real.exp w.re : ℂ) * exp (w.im * I) - 1 =
        ((Real.exp w.re : ℂ) - 1) * exp (w.im * I) + (exp (w.im * I) - 1) := by ring
    rw [e]
    calc ‖((Real.exp w.re : ℂ) - 1) * exp (w.im * I) + (exp (w.im * I) - 1)‖
        ≤ ‖((Real.exp w.re : ℂ) - 1) * exp (w.im * I)‖ + ‖exp (w.im * I) - 1‖ := norm_add_le _ _
      _ = |Real.exp w.re - 1| + ‖exp (w.im * I) - 1‖ := by
          rw [norm_mul, hu, mul_one, ← ofReal_one, ← ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
      _ < r := by linarith
  -- a bound for `g` on the sector
  have hRectc : IsCompact (exp '' Rect) :=
    (isCompact_uIcc.reProdIm isCompact_uIcc).image continuous_exp
  have himg : exp '' Rect ⊆ ball (1 : ℂ) r := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hRect w hw).1
  obtain ⟨Mg, hMg⟩ := hRectc.exists_bound_of_continuousOn (hg.continuousOn.mono himg)
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg (exp (Real.log R : ℂ)) ⟨_, by
    rw [hRectdef, Complex.mem_reProdIm]
    simp only [ofReal_re, ofReal_im]
    exact ⟨Set.right_mem_uIcc, by rw [Set.uIcc_of_le (by linarith)]; constructor <;> linarith⟩,
    rfl⟩)
  -- the constants
  set L := |Real.log R - Real.log ρ| with hL
  set C : ℝ := (2 * Real.pi * (18 * (1 - ρ)⁻¹) + 2 * s * (18 * (Mg + (R - 1)⁻¹)) +
    2 * (L * (6 * (Mg + 2)))) / (2 * Real.pi) with hCdef
  have hC0 : 0 ≤ C := by
    have : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith)
    have : 0 ≤ (R - 1)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < C + 1)) hq1
  obtain ⟨P, hPm, hP1, hP2⟩ := hP D
  set e₁ := exp (s * I) with he₁
  set e₂ := exp (-s * I) with he₂
  refine ⟨P * (X - Polynomial.C e₁) * (X - Polynomial.C e₂),
    (hPm.mul (monic_X_sub_C e₁)).mul (monic_X_sub_C e₂), fun n => ?_⟩
  set W := P * (X - Polynomial.C e₁) * (X - Polynomial.C e₂) with hWdef
  have hWeval : ∀ w, W.eval w = P.eval w * (w - e₁) * (w - e₂) := fun w => by
    simp [hWdef]
  have hne1 : ‖e₁‖ = 1 := by rw [he₁]; exact norm_exp_ofReal_mul_I s
  have hne2 : ‖e₂‖ = 1 := by
    rw [he₂, show (-s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  -- `W(w)` on the reflected contour
  have hfac : ∀ w : ℂ, ‖w‖ ≤ 2 → ‖(w - e₁) * (w - e₂)‖ ≤ 9 := fun w hw => by
    rw [norm_mul]
    have h1 : ‖w - e₁‖ ≤ 3 := (norm_sub_le _ _).trans (by rw [hne1]; linarith)
    have h2 : ‖w - e₂‖ ≤ 3 := (norm_sub_le _ _).trans (by rw [hne2]; linarith)
    nlinarith [norm_nonneg (w - e₁), norm_nonneg (w - e₂)]
  -- the factor `(w - e₁)(w - e₂)` vanishes where the contour crosses the unit circle
  have hfac' : ∀ (t : ℝ) (v : ℂ), 3 / 4 ≤ t → (v = e₁ ∨ v = e₂) →
      ‖((t⁻¹ : ℝ) * v - e₁) * ((t⁻¹ : ℝ) * v - e₂)‖ ≤ |t⁻¹ - 1| * 3 := fun t v ht hv => by
    have ht0 : 0 < t := by linarith
    have hti : t⁻¹ ≤ 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
    have hnv : ‖v‖ = 1 := by rcases hv with rfl | rfl <;> assumption
    have hw : ‖((t⁻¹ : ℝ) : ℂ) * v‖ ≤ 2 := by
      rw [norm_mul, hnv, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact hti
    have hother : ∀ e : ℂ, ‖e‖ = 1 → ‖((t⁻¹ : ℝ) : ℂ) * v - e‖ ≤ 3 := fun e he =>
      (norm_sub_le _ _).trans (by rw [he]; linarith)
    have hsame : ‖((t⁻¹ : ℝ) : ℂ) * v - v‖ = |t⁻¹ - 1| := by
      rw [show ((t⁻¹ : ℝ) : ℂ) * v - v = ((t⁻¹ - 1 : ℝ) : ℂ) * v by push_cast; ring, norm_mul, hnv,
        mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul]
    rcases hv with rfl | rfl
    · rw [hsame]
      exact mul_le_mul_of_nonneg_left (hother e₂ hne2) (abs_nonneg _)
    · rw [hsame, mul_comm]
      exact mul_le_mul_of_nonneg_left (hother _ hne1) (abs_nonneg _)
  -- the integrands
  set Lf : ℂ → ℂ := fun z => W.eval z⁻¹ * z⁻¹ with hLf
  set F : ℂ → ℂ := fun z => tail a n z * Lf z with hFdef
  set G : ℂ → ℂ := fun z => contTail a g n z * Lf z with hGdef
  have hFc : ContinuousOn F (sphere 0 ρ) :=
    ((continuousOn_tail ha n hρ0.le hρ1).mono sphere_subset_closedBall).mul
      (continuousOn_eval_inv_mul W hρ0)
  have hexpRect : ∀ x θ : ℝ, x ∈ Set.uIcc (Real.log ρ) (Real.log R) → θ ∈ Set.uIcc (-s) s →
      exp (x + θ * I) ∈ ball (1 : ℂ) r ∧ ρ ≤ Real.exp x ∧ Real.exp x ≤ R := fun x θ hx hθ => by
    have := hRect (x + θ * I) (by
      rw [hRectdef, Complex.mem_reProdIm]
      simpa using ⟨hx, hθ⟩)
    simpa using this
  have hGdiff : DifferentiableOn ℂ (fun w => G (exp w) * exp w)
      (Set.uIcc (Real.log ρ) (Real.log R) ×ℂ Set.uIcc (-s) s) := fun w hw => by
    have hball := (hRect w hw).1
    have he0 : exp w ≠ 0 := exp_ne_zero w
    have hgd : DifferentiableAt ℂ g (exp w) := hg.differentiableAt (isOpen_ball.mem_nhds hball)
    have hexpd : DifferentiableAt ℂ exp w := differentiableAt_exp
    have h1 : DifferentiableAt ℂ (fun w => g (exp w)) w := hgd.comp w hexpd
    have h2 : DifferentiableAt ℂ (fun w => ∑ j ∈ Finset.range n, a j * exp w ^ j) w :=
      DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul (hexpd.pow j)
    have h3 : DifferentiableAt ℂ (fun w => exp w ^ n) w := hexpd.pow n
    have h4 : DifferentiableAt ℂ (fun w => W.eval (exp w)⁻¹) w :=
      W.differentiableAt.comp w (hexpd.inv he0)
    have hd : DifferentiableAt ℂ (fun w => G (exp w) * exp w) w :=
      (((h1.sub h2).div h3 (pow_ne_zero n he0)).mul (h4.mul (hexpd.inv he0))).mul hexpd
    exact hd.differentiableWithinAt
  -- `2πi Eₙ` as the contour integral
  have hE : 2 * Real.pi * I * ∑ j ∈ Finset.range (W.natDegree + 1), a (n + j) * W.coeff j =
      ((∫ θ in -s..s, arcIntegrand G R θ) +
        (∫ x in Real.log ρ..Real.log R, G (exp x * exp (-s * I)) * (exp x * exp (-s * I))) -
        (∫ x in Real.log ρ..Real.log R, G (exp x * exp (s * I)) * (exp x * exp (s * I)))) +
      ∫ θ in s..2 * Real.pi - s, arcIntegrand F ρ θ := by
    rw [← circleIntegral_tail_mul ha n W hρ0 hρ1]
    rw [show (∮ z in C(0, ρ), tail a n z * (W.eval z⁻¹ * z⁻¹)) = ∮ z in C(0, ρ), F z from rfl,
      circleIntegral_eq_arcs hρ0.le hFc s]
    have hFG : (∫ θ in -s..s, arcIntegrand F ρ θ) = ∫ θ in -s..s, arcIntegrand G ρ θ := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      have hz := hexpRect (Real.log ρ) θ Set.left_mem_uIcc hθ
      have hzeq : exp ((Real.log ρ : ℂ) + θ * I) = ρ * exp (θ * I) := by
        rw [exp_add, ← ofReal_exp, Real.exp_log hρ0]
      rw [hzeq] at hz
      have hnz : ‖(ρ : ℂ) * exp (θ * I)‖ = ρ := by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hρ0.le]
      have hz0 : (ρ : ℂ) * exp (θ * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hρ0.ne') (exp_ne_zero _)
      simp only [arcIntegrand, hFdef, hGdef]
      rw [contTail_eq_tail ha n (by rw [hnz]; exact hρ1) hz0 (hgf _ hz.1 (by rw [hnz]; exact hρ1))]
    rw [hFG, sector_integral_eq hρ0 (by linarith) hGdiff]
  -- points of the contour in polar form
  have hpolar : ∀ u φ : ℝ, 0 < u → ‖(u : ℂ) * exp (φ * I)‖ = u := fun u φ hu => by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hu.le]
  have hpolar_re : ∀ u φ : ℝ, ((u : ℂ) * exp (φ * I)).re = u * Real.cos φ := fun u φ => by
    rw [re_ofReal_mul, exp_ofReal_mul_I_re]
  have hpolar_inv : ∀ u φ : ℝ,
      ((u : ℂ) * exp (φ * I))⁻¹ = ((u⁻¹ : ℝ) : ℂ) * exp (((-φ : ℝ) : ℂ) * I) := fun u φ => by
    rw [mul_inv, ofReal_inv, ofReal_neg, neg_mul, exp_neg]
  have hpolar0 : ∀ u φ : ℝ, 0 < u → (u : ℂ) * exp (φ * I) ≠ 0 := fun u φ hu =>
    mul_ne_zero (by exact_mod_cast hu.ne') (exp_ne_zero _)
  have hρinv : ρ⁻¹ = ρ₂ := by rw [hρdef, inv_inv]
  have hRinv : R⁻¹ = ρ₁ := by rw [hRdef, inv_inv]
  have hR0 : 0 < R := by linarith
  have hρ₂2 : ρ₂ ≤ 2 := by rw [← hρinv, inv_le_comm₀ hρ0 (by norm_num)]; linarith
  have hq : 0 ≤ q ^ D := pow_nonneg hq0.le D
  -- the integrands in terms of `W(1/z)`
  have hLz : ∀ (K : ℂ → ℂ) (z : ℂ), z ≠ 0 → ‖K z * Lf z * z‖ = ‖K z‖ * ‖W.eval z⁻¹‖ :=
    fun K z hz => by
      rw [show K z * Lf z * z = K z * W.eval z⁻¹ * (z⁻¹ * z) by simp only [hLf]; ring,
        inv_mul_cancel₀ hz, mul_one, norm_mul]
  have hArc : ∀ (K : ℂ → ℂ) (u θ : ℝ), 0 < u →
      ‖arcIntegrand (fun z => K z * Lf z) u θ‖ =
        ‖K (u * exp (θ * I))‖ * ‖W.eval (u * exp (θ * I))⁻¹‖ := fun K u θ hu => by
    have e : arcIntegrand (fun z => K z * Lf z) u θ =
        K (u * exp (θ * I)) * Lf (u * exp (θ * I)) * (u * exp (θ * I)) * I := by
      simp only [arcIntegrand]; ring
    rw [e, norm_mul _ I, norm_I, mul_one, hLz K _ (hpolar0 u θ hu)]
  have hWw : ∀ w : ℂ, ‖w‖ ≤ 2 → ‖P.eval w‖ ≤ 2 * q ^ D → ‖W.eval w‖ ≤ 18 * q ^ D :=
    fun w hw hPw => by
      rw [hWeval, mul_assoc, norm_mul]
      calc ‖P.eval w‖ * ‖(w - e₁) * (w - e₂)‖ ≤ 2 * q ^ D * 9 :=
            mul_le_mul hPw (hfac w hw) (norm_nonneg _) (by positivity)
        _ = 18 * q ^ D := by ring
  -- the sector lies in the disk of continuation
  have hsect : ∀ u θ : ℝ, ρ ≤ u → u ≤ R → -s ≤ θ → θ ≤ s →
      ‖g (u * exp (θ * I))‖ ≤ Mg ∧ (u : ℂ) * exp (θ * I) ∈ ball (1 : ℂ) r := by
    intro u θ hu1 hu2 hθ1 hθ2
    have hu0 : 0 < u := by linarith
    have hlog : Real.log ρ ≤ Real.log R := Real.log_le_log hρ0 (by linarith)
    have hx : Real.log u ∈ Set.uIcc (Real.log ρ) (Real.log R) := by
      rw [Set.uIcc_of_le hlog]
      exact ⟨Real.log_le_log hρ0 hu1, Real.log_le_log hu0 hu2⟩
    have hθ : θ ∈ Set.uIcc (-s) s := by
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨hθ1, hθ2⟩
    have hmem : ((Real.log u : ℂ) + θ * I) ∈ Rect := by
      rw [hRectdef, Complex.mem_reProdIm]
      simpa using ⟨hx, hθ⟩
    have he : exp ((Real.log u : ℂ) + θ * I) = u * exp (θ * I) := by
      rw [exp_add, ← ofReal_exp, Real.exp_log hu0]
    rw [← he]
    exact ⟨hMg _ ⟨_, hmem, rfl⟩, (hRect _ hmem).1⟩
  -- the big inner arc `|z| = ρ`, `τ ≤ arg z ≤ 2π - τ`
  have hbig : ∀ θ ∈ Ι s (2 * Real.pi - s), ‖arcIntegrand F ρ θ‖ ≤ 18 * (1 - ρ)⁻¹ * q ^ D := by
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith)] at hθ
    have hz1 : ‖(ρ : ℂ) * exp (θ * I)‖ < 1 := by rw [hpolar ρ θ hρ0]; exact hρ1
    set w := ((ρ : ℂ) * exp (θ * I))⁻¹ with hwdef
    have hw : w = ((ρ⁻¹ : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := hpolar_inv ρ θ
    have hwn : ‖w‖ = ρ₂ := by rw [hw, hpolar _ _ (by positivity), hρinv]
    have hwre : w.re ≤ ‖w‖ * Real.cos s := by
      rw [hwn, hw, hpolar_re, hρinv, Real.cos_neg]
      exact mul_le_mul_of_nonneg_left (cos_le_cos_of_mem_arc hs0.le hθ.1.le hθ.2) (by linarith)
    have hWw' := hWw w (by rw [hwn]; exact hρ₂2) (hP2 w (by rw [hwn]; linarith) hwn.le hwre)
    calc ‖arcIntegrand F ρ θ‖ = ‖tail a n (ρ * exp (θ * I))‖ * ‖W.eval w‖ :=
          hArc (tail a n) ρ θ hρ0
      _ ≤ (1 - ρ)⁻¹ * (18 * q ^ D) := by
          refine mul_le_mul ?_ hWw' (norm_nonneg _) (inv_nonneg.2 (by linarith))
          have := norm_tail_le ha n hz1
          rwa [hpolar ρ θ hρ0] at this
      _ = 18 * (1 - ρ)⁻¹ * q ^ D := by ring
  -- the outer arc `|z| = R`, `|arg z| ≤ τ`
  have hout : ∀ θ ∈ Ι (-s) s, ‖arcIntegrand G R θ‖ ≤ 18 * (Mg + (R - 1)⁻¹) * q ^ D := by
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith)] at hθ
    have hz1 : 1 < ‖(R : ℂ) * exp (θ * I)‖ := by rw [hpolar R θ hR0]; exact hR1
    have hgz := (hsect R θ (by linarith) le_rfl hθ.1.le hθ.2).1
    set w := ((R : ℂ) * exp (θ * I))⁻¹ with hwdef
    have hw : w = ((R⁻¹ : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := hpolar_inv R θ
    have hwn : ‖w‖ = ρ₁ := by rw [hw, hpolar _ _ (by positivity), hRinv]
    have hWw' := hWw w (by rw [hwn]; linarith) (hP1 w hwn)
    calc ‖arcIntegrand G R θ‖ = ‖contTail a g n (R * exp (θ * I))‖ * ‖W.eval w‖ :=
          hArc _ R θ hR0
      _ ≤ (Mg + (R - 1)⁻¹) * (18 * q ^ D) := by
          refine mul_le_mul ?_ hWw' (norm_nonneg _) (add_nonneg hMg0 (inv_nonneg.2 (by linarith)))
          have := norm_contTail_le ha g n hz1
          rw [hpolar R θ hR0] at this
          linarith
      _ = 18 * (Mg + (R - 1)⁻¹) * q ^ D := by ring
  -- the radial segments `arg z = ±τ`, where the factor `(w - e₁)(w - e₂)` vanishes on the circle
  have hradb : ∀ θ : ℝ, (θ = s ∨ θ = -s) → ∀ x ∈ Ι (Real.log ρ) (Real.log R),
      ‖G (exp x * exp (θ * I)) * (exp x * exp (θ * I))‖ ≤ 6 * (Mg + 2) * q ^ D := by
    intro θ hθ x hx
    rw [Set.uIoc_of_le (Real.log_le_log hρ0 (by linarith))] at hx
    set u := Real.exp x with hu
    have hu0 : 0 < u := Real.exp_pos x
    have hu1 : ρ ≤ u := by
      rw [hu, ← Real.exp_log hρ0]; exact Real.exp_le_exp.2 hx.1.le
    have hu2 : u ≤ R := by
      rw [hu, ← Real.exp_log hR0]; exact Real.exp_le_exp.2 hx.2
    rw [← ofReal_exp, ← hu]
    have hθs : -s ≤ θ ∧ θ ≤ s := by
      rcases hθ with rfl | rfl <;> constructor <;> linarith
    obtain ⟨hgz, hzb⟩ := hsect u θ hu1 hu2 hθs.1 hθs.2
    have hzn : ‖(u : ℂ) * exp (θ * I)‖ = u := hpolar u θ hu0
    set w := ((u : ℂ) * exp (θ * I))⁻¹ with hwdef
    have hw : w = ((u⁻¹ : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := hpolar_inv u θ
    have hwn : ‖w‖ = u⁻¹ := by rw [hw, hpolar _ _ (by positivity)]
    have hwre : w.re ≤ ‖w‖ * Real.cos s := by
      rw [hwn, hw, hpolar_re, Real.cos_neg]
      rcases hθ with rfl | rfl
      · exact le_rfl
      · rw [Real.cos_neg]
    have hPw : ‖P.eval w‖ ≤ 2 * q ^ D := hP2 w
      (by rw [hwn, ← hRinv]; exact inv_anti₀ hu0 hu2)
      (by rw [hwn, ← hρinv]; exact inv_anti₀ hρ0 hu1) hwre
    have hv : exp (((-θ : ℝ) : ℂ) * I) = e₁ ∨ exp (((-θ : ℝ) : ℂ) * I) = e₂ := by
      rcases hθ with rfl | rfl
      · right; rw [he₂, ofReal_neg]
      · left; rw [he₁, neg_neg]
    have hf := hfac' u _ (by linarith) hv
    rw [← hw] at hf
    have hct := norm_contTail_mul_le ha n hgz (by rw [hzn]; linarith) (fun h => hgf _ hzb h)
    rw [hzn] at hct
    calc ‖G (u * exp (θ * I)) * (u * exp (θ * I))‖ =
          ‖contTail a g n (u * exp (θ * I))‖ * ‖W.eval w‖ := hLz _ _ (hpolar0 u θ hu0)
      _ = ‖contTail a g n (u * exp (θ * I))‖ * (‖P.eval w‖ * ‖(w - e₁) * (w - e₂)‖) := by
          rw [hWeval, mul_assoc, norm_mul]
      _ ≤ ‖contTail a g n (u * exp (θ * I))‖ * (2 * q ^ D * (|u⁻¹ - 1| * 3)) := by
          gcongr
      _ = (‖contTail a g n (u * exp (θ * I))‖ * |u⁻¹ - 1|) * (6 * q ^ D) := by ring
      _ ≤ (Mg + 2) * (6 * q ^ D) := by gcongr
      _ = 6 * (Mg + 2) * q ^ D := by ring
  -- adding up
  have hint1 := intervalIntegral.norm_integral_le_of_norm_le_const hbig
  have hint2 := intervalIntegral.norm_integral_le_of_norm_le_const hout
  have hint3 := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => G (exp x * exp (-s * I)) * (exp x * exp (-s * I))) (fun x hx => by
      have := hradb (-s) (Or.inr rfl) x hx
      rwa [ofReal_neg] at this)
  have hint4 := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => G (exp x * exp (s * I)) * (exp x * exp (s * I))) (hradb s (Or.inl rfl))
  have hlen1 : |2 * Real.pi - s - s| ≤ 2 * Real.pi := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hlen2 : |s - -s| = 2 * s := by rw [abs_of_nonneg (by linarith)]; ring
  rw [hlen2] at hint2
  have hint1' := hint1.trans (mul_le_mul_of_nonneg_left hlen1
    (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 (by linarith))) hq))
  have htri : ∀ A B C' D' : ℂ, ‖A + B - C' + D'‖ ≤ ‖A‖ + ‖B‖ + ‖C'‖ + ‖D'‖ := fun A B C' D' =>
    calc ‖A + B - C' + D'‖ ≤ ‖A + B - C'‖ + ‖D'‖ := norm_add_le _ _
      _ ≤ ‖A + B‖ + ‖C'‖ + ‖D'‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖A‖ + ‖B‖ + ‖C'‖ + ‖D'‖ := by gcongr; exact norm_add_le _ _
  set E := ∑ j ∈ Finset.range (W.natDegree + 1), a (n + j) * W.coeff j with hEdef
  have h2pi : ‖(2 * Real.pi * I : ℂ) * E‖ = 2 * Real.pi * ‖E‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  have hCe : 2 * Real.pi * (C * q ^ D) = (2 * Real.pi * (18 * (1 - ρ)⁻¹) +
      2 * s * (18 * (Mg + (R - 1)⁻¹)) + 2 * (L * (6 * (Mg + 2)))) * q ^ D := by
    rw [hCdef]; field_simp
  have hmain : 2 * Real.pi * ‖E‖ ≤ 2 * Real.pi * (C * q ^ D) := by
    rw [← h2pi, hE, hCe]
    refine (htri _ _ _ _).trans ?_
    linarith only [hint1', hint2, hint3, hint4]
  have hEC : ‖E‖ ≤ C * q ^ D := le_of_mul_le_mul_left hmain (by positivity)
  have hCq : (C + 1) * q ^ D < ε := (lt_div_iff₀' (by linarith)).1 hD
  calc ‖E‖ ≤ C * q ^ D := hEC
    _ ≤ (C + 1) * q ^ D := mul_le_mul_of_nonneg_right (by linarith) hq
    _ < ε := hCq

end Rule30Equivalents.SzegoContour
