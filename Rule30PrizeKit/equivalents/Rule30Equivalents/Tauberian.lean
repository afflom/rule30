module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The Hardy–Littlewood–Karamata Tauberian theorem

For a sequence `a` of nonnegative reals,

  `(1 - x) ∑ aₙ xⁿ → L` as `x → 1⁻`  implies  `(a₀ + ⋯ + a_{N-1}) / N → L`

(`tendsto_cesaro_of_tendsto_abel`, Hardy and Littlewood 1914). The proof is Karamata's (1930).
Write `Λₓ(φ) = (1 - x) ∑ aₙ xⁿ φ(xⁿ)` (`abelMean`).

* `tendsto_abelMean_pow`: `Λₓ(tᵏ) → L / (k + 1) = L ∫₀¹ tᵏ dt`, since `Λₓ(tᵏ)` is the Abel mean at
  `x^(k+1)` times `(1 - x) / (1 - x^(k+1))`.
* `tendsto_abelMean_poly`, `tendsto_abelMean_of_continuousOn`: `Λₓ(φ) → L ∫₀¹ φ` for polynomials by
  linearity, and for continuous `φ` by the Weierstrass approximation theorem.
* `tendsto_cesaro_of_tendsto_abel`: at `x = e^(-1/N)` the indicator of `[e⁻¹, 1]` picks out
  `a₀, …, a_N`. Continuous ramps squeeze it from both sides (here `aₙ ≥ 0` is used), with integrals
  against `dt / t` close to `∫_{e⁻¹}^1 dt / t = 1`, and `N (1 - e^(-1/N)) → 1`.

The converse, the Abelian direction, holds for bounded sequences (`tendsto_abel_of_tendsto_cesaro`).
-/

@[expose] public section

namespace Rule30Equivalents.Tauberian

open Filter Topology Polynomial

/-- The Abel mean of `a` with the weight `φ`: `(1 - x) ∑ aₙ xⁿ φ(xⁿ)`. -/
noncomputable def abelMean (a : ℕ → ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - x) * ∑' n, a n * x ^ n * φ (x ^ n)

variable {a : ℕ → ℝ} {L : ℝ}

theorem eventually_mem_Ioo : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsLT one_pos

theorem exists_bound {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Icc 0 1)) :
    ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ t| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  exact ⟨B, fun t ht => by simpa [Real.norm_eq_abs] using hB t ht⟩

theorem summable_weighted (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun n => a n * x ^ n)
    {φ : ℝ → ℝ} {B : ℝ} (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ t| ≤ B) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) : Summable fun n => a n * x ^ n * φ (x ^ n) := by
  refine Summable.of_norm_bounded ((hs x hx0 hx1).mul_left B) fun n => ?_
  have hxn : x ^ n ∈ Set.Icc (0 : ℝ) 1 := ⟨pow_nonneg hx0 n, pow_le_one₀ hx0 hx1.le⟩
  have h0 : 0 ≤ a n * x ^ n := mul_nonneg (ha n) (pow_nonneg hx0 n)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _ hxn) h0

/-- **Powers.** `Λₓ(tᵏ) → L / (k + 1)`. -/
theorem tendsto_abelMean_pow (h : Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 L))
    (k : ℕ) : Tendsto (abelMean a fun t => t ^ k) (𝓝[<] 1) (𝓝 (L / (k + 1))) := by
  have hy : Tendsto (fun x : ℝ => x ^ (k + 1)) (𝓝[<] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_pow (k + 1)).tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 1))
      rwa [one_pow] at this
    · filter_upwards [eventually_mem_Ioo] with x hx
      exact pow_lt_one₀ hx.1.le hx.2 (by omega)
  have hG : Tendsto (fun x : ℝ => ∑ i ∈ Finset.range (k + 1), x ^ i) (𝓝[<] 1)
      (𝓝 ((k : ℝ) + 1)) := by
    have hc : Continuous fun x : ℝ => ∑ i ∈ Finset.range (k + 1), x ^ i := by fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  refine ((h.comp hy).div hG (by positivity)).congr' ?_
  filter_upwards [eventually_mem_Ioo] with x hx
  have hgeom : 1 - x ^ (k + 1) = (1 - x) * ∑ i ∈ Finset.range (k + 1), x ^ i := by
    have := geom_sum_mul x (k + 1)
    linarith
  have hpos : 0 < ∑ i ∈ Finset.range (k + 1), x ^ i :=
    Finset.sum_pos (fun i _ => pow_pos hx.1 i) ⟨0, by simp⟩
  have hne := hpos.ne'
  have hterm : ∀ n, a n * x ^ n * (x ^ n) ^ k = a n * (x ^ (k + 1)) ^ n := fun n => by
    rw [mul_assoc, ← pow_succ', ← pow_mul, ← pow_mul, mul_comm n (k + 1)]
  simp only [Pi.div_apply, Function.comp_def, abelMean, hterm, hgeom]
  field_simp

/-- **Polynomials.** `Λₓ(P) → L ∫₀¹ P`. -/
theorem tendsto_abelMean_poly (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun n => a n * x ^ n)
    (h : Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 L)) (P : ℝ[X]) :
    Tendsto (abelMean a fun t => P.eval t) (𝓝[<] 1) (𝓝 (L * ∫ t in (0 : ℝ)..1, P.eval t)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Bp, hBp⟩ := exists_bound (φ := fun t => p.eval t) p.continuous.continuousOn
    obtain ⟨Bq, hBq⟩ := exists_bound (φ := fun t => q.eval t) q.continuous.continuousOn
    have e : (fun x => abelMean a (fun t => p.eval t) x + abelMean a (fun t => q.eval t) x)
        =ᶠ[𝓝[<] 1] abelMean a fun t => (p + q).eval t := by
      filter_upwards [eventually_mem_Ioo] with x hx
      simp only [abelMean, eval_add, mul_add]
      rw [← mul_add, ← (summable_weighted ha hs hBp hx.1.le hx.2).tsum_add
        (summable_weighted ha hs hBq hx.1.le hx.2)]
    have hint : ∫ t in (0 : ℝ)..1, (p + q).eval t =
        (∫ t in (0 : ℝ)..1, p.eval t) + ∫ t in (0 : ℝ)..1, q.eval t := by
      simp only [eval_add]
      exact intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
        (q.continuous.intervalIntegrable _ _)
    rw [hint, mul_add]
    exact (hp.add hq).congr' e
  | monomial n c =>
    have e : (fun x => c * abelMean a (fun t => t ^ n) x)
        =ᶠ[𝓝[<] 1] abelMean a fun t => (monomial n c).eval t := by
      filter_upwards [eventually_mem_Ioo] with x hx
      simp only [abelMean, eval_monomial]
      rw [show (fun m => a m * x ^ m * (c * (x ^ m) ^ n)) =
          fun m => c * (a m * x ^ m * (x ^ m) ^ n) from funext fun m => by ring, tsum_mul_left]
      ring
    have hint : ∫ t in (0 : ℝ)..1, (monomial n c).eval t = c * (1 / (n + 1)) := by
      simp only [eval_monomial]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp
    rw [hint, show L * (c * (1 / ((n : ℝ) + 1))) = c * (L / (n + 1)) by ring]
    exact ((tendsto_abelMean_pow h n).const_mul c).congr' e

/-- **Continuous weights.** `Λₓ(φ) → L ∫₀¹ φ` for `φ` continuous on `[0, 1]`. -/
theorem tendsto_abelMean_of_continuousOn (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun n => a n * x ^ n)
    (h : Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 L)) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc 0 1)) :
    Tendsto (abelMean a φ) (𝓝[<] 1) (𝓝 (L * ∫ t in (0 : ℝ)..1, φ t)) := by
  obtain ⟨Bφ, hBφ⟩ := exists_bound hφ
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := ε / (2 * |L| + 3) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 φ hφ η hη0
  obtain ⟨BP, hBP⟩ := exists_bound (φ := fun t => P.eval t) P.continuous.continuousOn
  have hPlim := tendsto_abelMean_poly ha hs h P
  -- the integrals are close
  have hint : |(∫ t in (0 : ℝ)..1, φ t) - ∫ t in (0 : ℝ)..1, P.eval t| ≤ η := by
    rw [← intervalIntegral.integral_sub (hφ.intervalIntegrable_of_Icc zero_le_one)
      (P.continuous.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := η)
      (f := fun t => φ t - P.eval t) fun t ht => by
        rw [Set.uIoc_of_le zero_le_one] at ht
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hP t ⟨ht.1.le, ht.2⟩).le
    simpa using this
  filter_upwards [Metric.tendsto_nhds.1 hPlim η hη0, h.eventually (gt_mem_nhds (lt_add_one L)),
    eventually_mem_Ioo] with x h1 h2 hx
  have hx1 : 0 < 1 - x := sub_pos.2 hx.2
  have hsφ := summable_weighted ha hs hBφ hx.1.le hx.2
  have hsP := summable_weighted ha hs hBP hx.1.le hx.2
  have hsa := hs x hx.1.le hx.2
  -- the Abel means are close
  have hsum : |∑' n, (a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n))| ≤
      η * ∑' n, a n * x ^ n := by
    have hb : ∀ n, |a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n)| ≤
        η * (a n * x ^ n) := fun n => by
      have h0 : 0 ≤ a n * x ^ n := mul_nonneg (ha n) (pow_nonneg hx.1.le n)
      rw [← mul_sub, abs_mul, abs_of_nonneg h0, mul_comm]
      have hxn : x ^ n ∈ Set.Icc (0 : ℝ) 1 := ⟨pow_nonneg hx.1.le n, pow_le_one₀ hx.1.le hx.2.le⟩
      exact mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact (hP _ hxn).le) h0
    have hsabs : Summable fun n => |a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n)| :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hb (hsa.mul_left η)
    calc |∑' n, (a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n))|
        ≤ ∑' n, |a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n)| := by
          exact norm_tsum_le_tsum_norm
            (f := fun n => a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n)) hsabs
      _ ≤ ∑' n, η * (a n * x ^ n) := hsabs.tsum_le_tsum hb (hsa.mul_left η)
      _ = η * ∑' n, a n * x ^ n := tsum_mul_left
  have hdiff : |abelMean a φ x - abelMean a (fun t => P.eval t) x| ≤
      η * ((1 - x) * ∑' n, a n * x ^ n) := by
    simp only [abelMean]
    rw [← mul_sub, ← hsφ.tsum_sub hsP, abs_mul, abs_of_pos hx1]
    calc (1 - x) * |∑' n, (a n * x ^ n * φ (x ^ n) - a n * x ^ n * P.eval (x ^ n))|
        ≤ (1 - x) * (η * ∑' n, a n * x ^ n) := mul_le_mul_of_nonneg_left hsum hx1.le
      _ = η * ((1 - x) * ∑' n, a n * x ^ n) := by ring
  have h0 : 0 ≤ (1 - x) * ∑' n, a n * x ^ n :=
    mul_nonneg hx1.le (tsum_nonneg fun n => mul_nonneg (ha n) (pow_nonneg hx.1.le n))
  rw [Real.dist_eq] at h1 ⊢
  have hL : |L * (∫ t in (0 : ℝ)..1, P.eval t) - L * ∫ t in (0 : ℝ)..1, φ t| ≤ |L| * η := by
    rw [← mul_sub, abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hint (abs_nonneg L)
  have hηL : η * (2 * |L| + 3) = ε := by
    rw [hη]; field_simp
  calc |abelMean a φ x - L * ∫ t in (0 : ℝ)..1, φ t|
      ≤ |abelMean a φ x - abelMean a (fun t => P.eval t) x| +
        |abelMean a (fun t => P.eval t) x - L * ∫ t in (0 : ℝ)..1, P.eval t| +
        |L * (∫ t in (0 : ℝ)..1, P.eval t) - L * ∫ t in (0 : ℝ)..1, φ t| := by
        have := abs_sub_le (abelMean a φ x) (abelMean a (fun t => P.eval t) x)
          (L * ∫ t in (0 : ℝ)..1, φ t)
        have := abs_sub_le (abelMean a (fun t => P.eval t) x) (L * ∫ t in (0 : ℝ)..1, P.eval t)
          (L * ∫ t in (0 : ℝ)..1, φ t)
        linarith
    _ < ε := by
        have := mul_le_mul_of_nonneg_left h2.le hη0.le
        have hLabs := le_abs_self L
        nlinarith [abs_nonneg L]

/-! ### Squeezing the indicator -/

/-- A continuous function vanishing left of `r > 0`, divided by `t`, is continuous. -/
theorem continuous_div_id {ψ : ℝ → ℝ} (hψ : Continuous ψ) {r : ℝ} (hr : 0 < r)
    (h0 : ∀ t < r, ψ t = 0) : Continuous fun t => ψ t / t := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t < r
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [h0 s hs, zero_div]
  · push Not at ht
    exact hψ.continuousAt.div continuousAt_id (hr.trans_le ht).ne'

/-- The ramp below the indicator of `[e⁻¹, ∞)`: `0` up to `e⁻¹`, `1` from `e⁻¹ + δ` on. -/
noncomputable def rampLo (δ t : ℝ) : ℝ := max 0 (min 1 ((t - Real.exp (-1)) / δ))

/-- The ramp above the indicator of `[e⁻¹, ∞)`: `0` up to `e⁻¹ - δ`, `1` from `e⁻¹` on. -/
noncomputable def rampHi (δ t : ℝ) : ℝ := max 0 (min 1 ((t - Real.exp (-1) + δ) / δ))

theorem continuous_rampLo (δ : ℝ) : Continuous (rampLo δ) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const δ))

theorem continuous_rampHi (δ : ℝ) : Continuous (rampHi δ) :=
  continuous_const.max (continuous_const.min
    (((continuous_id.sub continuous_const).add continuous_const).div_const δ))

theorem rampLo_nonneg (δ t : ℝ) : 0 ≤ rampLo δ t := le_max_left _ _

theorem rampHi_le_one (δ t : ℝ) : rampHi δ t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem rampLo_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    rampLo δ t ≤ if Real.exp (-1) ≤ t then 1 else 0 := by
  unfold rampLo
  split_ifs with ht
  · exact max_le zero_le_one (min_le_left _ _)
  · refine max_le le_rfl ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg ?_ hδ.le))
    linarith

theorem le_rampHi {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (if Real.exp (-1) ≤ t then 1 else 0) ≤ rampHi δ t := by
  unfold rampHi
  split_ifs with ht
  · refine le_max_of_le_right (le_min le_rfl ?_)
    rw [le_div_iff₀ hδ]
    linarith
  · exact le_max_left _ _

theorem rampLo_eq_zero {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t < Real.exp (-1)) : rampLo δ t = 0 :=
  le_antisymm ((rampLo_le hδ t).trans (by rw [ite_eq_right (not_le.2 ht)])) (rampLo_nonneg δ t)

theorem rampLo_eq_one {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : Real.exp (-1) + δ ≤ t) :
    rampLo δ t = 1 := by
  unfold rampLo
  rw [min_eq_left ((le_div_iff₀ hδ).2 (by linarith)), max_eq_right zero_le_one]

theorem rampHi_eq_zero {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ≤ Real.exp (-1) - δ) :
    rampHi δ t = 0 := by
  unfold rampHi
  refine max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg ?_ hδ.le))
  linarith

theorem integral_rampLo_ge {δ : ℝ} (hδ : 0 < δ) (h1 : Real.exp (-1) + δ ≤ 1) :
    -Real.log (Real.exp (-1) + δ) ≤ ∫ t in (0 : ℝ)..1, rampLo δ t / t := by
  have hc : 0 < Real.exp (-1) := Real.exp_pos _
  have hcont : Continuous fun t => rampLo δ t / t :=
    continuous_div_id (continuous_rampLo δ) hc fun t ht => rampLo_eq_zero hδ ht
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.exp (-1) + δ)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h2 : ∫ t in (Real.exp (-1) + δ)..1, rampLo δ t / t =
      ∫ t in (Real.exp (-1) + δ)..1, t⁻¹ := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le h1] at ht
    simp only [rampLo_eq_one hδ ht.1, one_div]
  have h3 : 0 ≤ ∫ t in (0 : ℝ)..(Real.exp (-1) + δ), rampLo δ t / t :=
    intervalIntegral.integral_nonneg (by positivity) fun t ht =>
      div_nonneg (rampLo_nonneg _ _) ht.1
  rw [h2, integral_inv_of_pos (by positivity) one_pos, one_div, Real.log_inv]
  linarith

theorem integral_rampHi_le {δ : ℝ} (hδ : 0 < δ) (hδc : δ < Real.exp (-1)) :
    ∫ t in (0 : ℝ)..1, rampHi δ t / t ≤ -Real.log (Real.exp (-1) - δ) := by
  have hc1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hr : 0 < Real.exp (-1) - δ := by linarith
  have hcont : Continuous fun t => rampHi δ t / t :=
    continuous_div_id (continuous_rampHi δ) hr fun t ht => rampHi_eq_zero hδ ht.le
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.exp (-1) - δ)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..(Real.exp (-1) - δ), rampHi δ t / t = 0 := by
    have : ∫ t in (0 : ℝ)..(Real.exp (-1) - δ), rampHi δ t / t =
        ∫ t in (0 : ℝ)..(Real.exp (-1) - δ), (0 : ℝ) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le hr.le] at ht
        simp [rampHi_eq_zero hδ ht.2]
    rw [this, intervalIntegral.integral_zero]
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume (Real.exp (-1) - δ) 1 :=
    (continuousOn_inv₀.mono fun t ht => by
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact (hr.trans_le ht.1).ne').intervalIntegrable
  have h2 : ∫ t in (Real.exp (-1) - δ)..1, rampHi δ t / t ≤ ∫ t in (Real.exp (-1) - δ)..1, t⁻¹ :=
    intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _) hinv
      fun t ht => by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_nonneg.2 (hr.le.trans ht.1)) (rampHi_le_one _ _)
  rw [integral_inv_of_pos hr one_pos, one_div, Real.log_inv] at h2
  linarith

/-- **The Hardy–Littlewood–Karamata Tauberian theorem.** If `aₙ ≥ 0` and the Abel means
`(1 - x) ∑ aₙ xⁿ` tend to `L` as `x → 1⁻`, the Cesàro means `(a₀ + ⋯ + a_{N-1}) / N` tend to
`L`. -/
theorem tendsto_cesaro_of_tendsto_abel (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun n => a n * x ^ n)
    (h : Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 L) := by
  set c := Real.exp (-1) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hlogc : Real.log c = -1 := Real.log_exp _
  have hL : 0 ≤ L := ge_of_tendsto h (by
    filter_upwards [eventually_mem_Ioo] with x hx
    exact mul_nonneg (sub_pos.2 hx.2).le
      (tsum_nonneg fun n => mul_nonneg (ha n) (pow_nonneg hx.1.le n)))
  -- the points `x_N = e^(-1/N)`
  set x : ℕ → ℝ := fun N => Real.exp (-1 / N) with hx
  have hx0 : ∀ N, 0 < x N := fun N => Real.exp_pos _
  have hx1 : ∀ N, 0 < N → x N < 1 := fun N hN => Real.exp_lt_one_iff.2
    (div_neg_of_neg_of_pos (by norm_num) (by exact_mod_cast hN))
  have hxlim : Tendsto x atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Real.continuous_exp.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (-1 : ℝ))
      simpa [Function.comp_def] using this
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact hx1 N hN
  have hind : ∀ N, 0 < N → ∀ n : ℕ, (c ≤ x N ^ n ↔ n ≤ N) := fun N hN n => by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [hx, hc, ← Real.exp_nat_mul, Real.exp_le_exp, mul_div_assoc', le_div_iff₀ hN']
    constructor
    · intro h'
      have : (n : ℝ) ≤ N := by linarith
      exact_mod_cast this
    · intro h'
      have : (n : ℝ) ≤ N := by exact_mod_cast h'
      linarith
  -- the partial sums `S N = a₀ + ⋯ + a_N`
  set S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range (N + 1), a n with hS
  have hsand : ∀ δ, 0 < δ → δ < c → ∀ N, 0 < N →
      abelMean a (fun t => rampLo δ t / t) (x N) ≤ (1 - x N) * S N ∧
      (1 - x N) * S N ≤ abelMean a (fun t => rampHi δ t / t) (x N) := by
    intro δ hδ hδc N hN
    have h1x : 0 ≤ 1 - x N := (sub_pos.2 (hx1 N hN)).le
    have hxn : ∀ n, x N ^ n ≠ 0 := fun n => (pow_pos (hx0 N) n).ne'
    have hcl : Continuous fun t => rampLo δ t / t :=
      continuous_div_id (continuous_rampLo δ) hc0 fun t ht => rampLo_eq_zero hδ ht
    have hch : Continuous fun t => rampHi δ t / t :=
      continuous_div_id (continuous_rampHi δ) (by linarith) fun t ht => rampHi_eq_zero hδ ht.le
    obtain ⟨Bl, hBl⟩ := exists_bound hcl.continuousOn
    obtain ⟨Bh, hBh⟩ := exists_bound hch.continuousOn
    have hlo : (fun n => a n * x N ^ n * (rampLo δ (x N ^ n) / x N ^ n)) =
        fun n => a n * rampLo δ (x N ^ n) := funext fun n => by field_simp [hxn n]
    have hhi : (fun n => a n * x N ^ n * (rampHi δ (x N ^ n) / x N ^ n)) =
        fun n => a n * rampHi δ (x N ^ n) := funext fun n => by field_simp [hxn n]
    have hsl : Summable fun n => a n * rampLo δ (x N ^ n) := by
      rw [← hlo]; exact summable_weighted ha hs hBl (hx0 N).le (hx1 N hN)
    have hsh : Summable fun n => a n * rampHi δ (x N ^ n) := by
      rw [← hhi]; exact summable_weighted ha hs hBh (hx0 N).le (hx1 N hN)
    have hsi : Summable fun n => a n * (if c ≤ x N ^ n then 1 else 0) := by
      refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
      rw [ite_eq_right (fun h' => hn (Finset.mem_range_succ_iff.2 ((hind N hN n).1 h'))), mul_zero]
    have hsum : ∑' n, a n * (if c ≤ x N ^ n then 1 else 0) = S N := by
      rw [tsum_eq_sum (s := Finset.range (N + 1))]
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [ite_eq_left ((hind N hN n).2 (Finset.mem_range_succ_iff.1 hn)), mul_one]
      · intro n hn
        rw [ite_eq_right (fun h' => hn (Finset.mem_range_succ_iff.2 ((hind N hN n).1 h'))),
            mul_zero]
    simp only [abelMean]
    rw [hlo, hhi, ← hsum]
    constructor
    · exact mul_le_mul_of_nonneg_left (hsl.tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_left (rampLo_le hδ _) (ha n)) hsi) h1x
    · exact mul_le_mul_of_nonneg_left (hsi.tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_left (le_rampHi hδ _) (ha n)) hsh) h1x
  -- `(1 - x_N) S_N → L`
  have hu : Tendsto (fun N => (1 - x N) * S N) atTop (𝓝 L) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      have hcont : ContinuousAt (fun δ : ℝ => L * -Real.log (c + δ)) 0 :=
        continuousAt_const.mul ((continuousAt_const.add continuousAt_id).log
          (by simp)).neg
      have hlim : Tendsto (fun δ : ℝ => L * -Real.log (c + δ)) (𝓝[>] 0) (𝓝 L) := by
        simpa [hlogc] using hcont.tendsto.mono_left nhdsWithin_le_nhds
      obtain ⟨δ, hbδ, hδ⟩ := ((hlim.eventually (lt_mem_nhds hb)).and
        (Ioo_mem_nhdsGT (show (0 : ℝ) < min c (1 - c) by
          exact lt_min hc0 (by linarith)))).exists
      have hδc : δ < c := hδ.2.trans_le (min_le_left _ _)
      have hδ1 : c + δ ≤ 1 := by linarith [hδ.2.trans_le (min_le_right _ _)]
      have hgt : b < L * ∫ t in (0 : ℝ)..1, rampLo δ t / t :=
        hbδ.trans_le (mul_le_mul_of_nonneg_left (integral_rampLo_ge hδ.1 hδ1) hL)
      have hlimlo := (tendsto_abelMean_of_continuousOn ha hs h (continuous_div_id
        (continuous_rampLo δ) hc0 fun t ht => rampLo_eq_zero hδ.1 ht).continuousOn).comp hxlim
      filter_upwards [hlimlo.eventually (lt_mem_nhds hgt), eventually_gt_atTop 0] with N h1 hN
      exact h1.trans_le (hsand δ hδ.1 hδc N hN).1
    · intro b hb
      have hcont : ContinuousAt (fun δ : ℝ => L * -Real.log (c - δ)) 0 :=
        continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).log
          (by simp)).neg
      have hlim : Tendsto (fun δ : ℝ => L * -Real.log (c - δ)) (𝓝[>] 0) (𝓝 L) := by
        simpa [hlogc] using hcont.tendsto.mono_left nhdsWithin_le_nhds
      obtain ⟨δ, hbδ, hδ⟩ := ((hlim.eventually (gt_mem_nhds hb)).and
        (Ioo_mem_nhdsGT hc0)).exists
      have hlt : L * ∫ t in (0 : ℝ)..1, rampHi δ t / t < b :=
        (mul_le_mul_of_nonneg_left (integral_rampHi_le hδ.1 hδ.2) hL).trans_lt hbδ
      have hlimhi := (tendsto_abelMean_of_continuousOn ha hs h (continuous_div_id
        (continuous_rampHi δ) (by linarith [hδ.2]) fun t ht =>
          rampHi_eq_zero hδ.1 ht.le).continuousOn).comp hxlim
      filter_upwards [hlimhi.eventually (gt_mem_nhds hlt), eventually_gt_atTop 0] with N h1 hN
      exact (hsand δ hδ.1 hδ.2 N hN).2.trans_lt h1
  -- `N (1 - x_N) → 1`
  have hv : Tendsto (fun N : ℕ => (N : ℝ) * (1 - x N)) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_natCast_div_add_atTop (1 : ℝ))
      tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : 1 + 1 / (N : ℝ) ≤ Real.exp (1 / N) := by
        have := Real.add_one_le_exp (1 / (N : ℝ)); linarith
      have h2 : x N = (Real.exp (1 / N))⁻¹ := by
        simp only [hx]
        rw [← Real.exp_neg, neg_div]
      have h3 : x N ≤ (N : ℝ) / (N + 1) := by
        rw [h2]
        calc (Real.exp (1 / N))⁻¹ ≤ (1 + 1 / (N : ℝ))⁻¹ := inv_anti₀ (by positivity) h1
          _ = (N : ℝ) / (N + 1) := by field_simp
      calc (N : ℝ) / (N + 1) = N * (1 - N / (N + 1)) := by field_simp; ring
        _ ≤ N * (1 - x N) := mul_le_mul_of_nonneg_left (by linarith) hN'.le
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : 1 + (-1 / (N : ℝ)) ≤ x N := by
        have := Real.add_one_le_exp (-1 / (N : ℝ)); rw [hx]; linarith
      calc (N : ℝ) * (1 - x N) ≤ N * (1 / N) :=
            mul_le_mul_of_nonneg_left (by rw [neg_div] at h1; linarith) hN'.le
        _ = 1 := mul_one_div_cancel hN'.ne'
  -- `S_N / N → L`
  have hSN : Tendsto (fun N : ℕ => S N / N) atTop (𝓝 L) := by
    have := hu.div hv one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 : 1 - x N ≠ 0 := (sub_pos.2 (hx1 N hN)).ne'
    have h2 : (N : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp
  rw [← tendsto_add_atTop_iff_nat 1]
  have := hSN.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h2 : (N : ℝ) ≠ 0 := by positivity
  have h3 : (N : ℝ) + 1 ≠ 0 := by positivity
  simp only [hS]
  push_cast
  field_simp

/-! ### The Abelian direction -/

/-- **The Abelian direction.** For a bounded sequence, if the Cesàro means tend to `L`, so do the
Abel means. -/
theorem tendsto_abel_of_tendsto_cesaro {B : ℝ} (hB : ∀ n, |a n| ≤ B)
    (h : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 L)) :
    Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 L) := by
  set S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range (N + 1), a n with hS
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hSB : ∀ N, |S N| ≤ B * (N + 1) := fun N => by
    calc |S N| ≤ ∑ n ∈ Finset.range (N + 1), |a n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range (N + 1), B := Finset.sum_le_sum fun n _ => hB n
      _ = B * (N + 1) := by simp [mul_comm]
  -- summability for `0 ≤ x < 1`
  have hsN : ∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun N : ℕ => ((N : ℝ) + 1) * x ^ N := by
    intro x hx0 hx1
    have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
    have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hxn).summable
    have h2 := summable_geometric_of_lt_one hx0 hx1
    simpa [add_mul] using h1.add h2
  -- the Abel mean minus `L` is `(1 - x)² ∑ (S N - L (N + 1)) x^N`
  have key : ∀ x : ℝ, 0 ≤ x → x < 1 → (1 - x) * ∑' n, a n * x ^ n - L =
      (1 - x) ^ 2 * ∑' N : ℕ, (S N - L * (N + 1)) * x ^ N := by
    intro x hx0 hx1
    have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
    have hg : Summable fun n : ℕ => ‖x ^ n‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg x) hxn
    have hf : Summable fun n => ‖a n * x ^ n‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hB n) (norm_nonneg _))
        (hg.mul_left B)
    have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
    have hterm : ∀ N, ∑ k ∈ Finset.range (N + 1), a k * x ^ k * x ^ (N - k) = S N * x ^ N :=
      fun N => by
        rw [hS, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_range_succ_iff.1 hk)]
    simp only [hterm] at hcauchy
    rw [tsum_geometric_of_lt_one hx0 hx1] at hcauchy
    have hsum1 : Summable fun N : ℕ => S N * x ^ N :=
      Summable.of_norm_bounded ((hsN x hx0 hx1).mul_left B) fun N => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 N), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hSB N) (pow_nonneg hx0 N)
    have hgeo2 : ∑' N : ℕ, ((N : ℝ) + 1) * x ^ N = ((1 - x) ^ 2)⁻¹ := by
      have h1 := tsum_coe_mul_geometric_of_norm_lt_one hxn
      have h2 := tsum_geometric_of_lt_one hx0 hx1
      have hs1 := (hasSum_coe_mul_geometric_of_norm_lt_one hxn).summable
      have hs2 := summable_geometric_of_lt_one hx0 hx1
      rw [show (fun N : ℕ => ((N : ℝ) + 1) * x ^ N) = fun N : ℕ => (N : ℝ) * x ^ N + x ^ N from
        funext fun N => by ring, hs1.tsum_add hs2, h1, h2]
      have : 1 - x ≠ 0 := by linarith
      field_simp
      ring
    rw [show (fun N : ℕ => (S N - L * (N + 1)) * x ^ N) =
        fun N => S N * x ^ N - L * (((N : ℝ) + 1) * x ^ N) from funext fun N => by ring,
      hsum1.tsum_sub ((hsN x hx0 hx1).mul_left L), tsum_mul_left, hgeo2, ← hcauchy]
    have : 1 - x ≠ 0 := by linarith
    field_simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 ((tendsto_add_atTop_iff_nat 1).2 h) (ε / 2)
    (by positivity)
  set K := (B + |L|) * N₀ with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ N : ℕ, |S N - L * (N + 1)| ≤ K + ε / 2 * (N + 1) := by
    intro N
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    by_cases hN : N₀ ≤ N
    · have h1 := hN₀ N hN
      rw [Real.dist_eq] at h1
      have e : S N - L * (N + 1) =
          ((N : ℝ) + 1) * ((∑ n ∈ Finset.range (N + 1), a n) / ((N + 1 : ℕ) : ℝ) - L) := by
        simp only [hS]
        push_cast
        field_simp
      rw [e, abs_mul, abs_of_pos hpos]
      have := mul_le_mul_of_nonneg_left h1.le hpos.le
      nlinarith
    · push Not at hN
      have hN' : (N : ℝ) + 1 ≤ N₀ := by exact_mod_cast hN
      calc |S N - L * (N + 1)| ≤ |S N| + |L * (N + 1)| := abs_sub _ _
        _ ≤ B * (N + 1) + |L| * (N + 1) := by
            rw [abs_mul, abs_of_pos hpos]
            linarith [hSB N]
        _ = (B + |L|) * (N + 1) := by ring
        _ ≤ (B + |L|) * N₀ := mul_le_mul_of_nonneg_left hN' (by positivity)
        _ ≤ K + ε / 2 * (N + 1) := by
            have : 0 ≤ ε / 2 * ((N : ℝ) + 1) := by positivity
            linarith
  have hsmall : ∀ᶠ x in 𝓝[<] (1 : ℝ), (1 - x) * K < ε / 2 := by
    have : Tendsto (fun x : ℝ => (1 - x) * K) (𝓝[<] 1) (𝓝 0) := by
      have := ((continuous_const.sub continuous_id).mul continuous_const).tendsto (1 : ℝ)
        (f := fun x : ℝ => (1 - x) * K)
      simpa using this.mono_left nhdsWithin_le_nhds
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [eventually_mem_Ioo, hsmall] with x hx hxK
  have hx0 := hx.1.le
  have hx1 := hx.2
  have h1x : 0 < 1 - x := sub_pos.2 hx1
  rw [Real.dist_eq, key x hx0 hx1, abs_mul, abs_of_pos (pow_pos h1x 2)]
  have hgeo : ∑' N : ℕ, x ^ N = (1 - x)⁻¹ := tsum_geometric_of_lt_one hx0 hx1
  have hsg := summable_geometric_of_lt_one hx0 hx1
  have hsb : Summable fun N : ℕ => (K + ε / 2 * (N + 1)) * x ^ N := by
    have := (hsg.mul_left K).add ((hsN x hx0 hx1).mul_left (ε / 2))
    refine this.congr fun N => by ring
  have hT : |∑' N : ℕ, (S N - L * (N + 1)) * x ^ N| ≤
      K * (1 - x)⁻¹ + ε / 2 * ((1 - x) ^ 2)⁻¹ := by
    have hb : ∀ N : ℕ, |(S N - L * (N + 1)) * x ^ N| ≤ (K + ε / 2 * (N + 1)) * x ^ N :=
      fun N => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 N)]
        exact mul_le_mul_of_nonneg_right (hbound N) (pow_nonneg hx0 N)
    have hsabs : Summable fun N : ℕ => |(S N - L * (N + 1)) * x ^ N| :=
      Summable.of_nonneg_of_le (fun N => abs_nonneg _) hb hsb
    have hgeo2 : ∑' N : ℕ, ((N : ℝ) + 1) * x ^ N = ((1 - x) ^ 2)⁻¹ := by
      have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
      have h1 := tsum_coe_mul_geometric_of_norm_lt_one hxn
      have hs1 := (hasSum_coe_mul_geometric_of_norm_lt_one hxn).summable
      rw [show (fun N : ℕ => ((N : ℝ) + 1) * x ^ N) = fun N : ℕ => (N : ℝ) * x ^ N + x ^ N from
        funext fun N => by ring, hs1.tsum_add hsg, h1, hgeo]
      have : 1 - x ≠ 0 := h1x.ne'
      field_simp
      ring
    calc |∑' N : ℕ, (S N - L * (N + 1)) * x ^ N|
        ≤ ∑' N : ℕ, |(S N - L * (N + 1)) * x ^ N| :=
          norm_tsum_le_tsum_norm (f := fun N : ℕ => (S N - L * (N + 1)) * x ^ N) hsabs
      _ ≤ ∑' N : ℕ, (K + ε / 2 * (N + 1)) * x ^ N := hsabs.tsum_le_tsum hb hsb
      _ = K * ∑' N : ℕ, x ^ N + ε / 2 * ∑' N : ℕ, ((N : ℝ) + 1) * x ^ N := by
          rw [← tsum_mul_left, ← tsum_mul_left, ← (hsg.mul_left K).tsum_add
            ((hsN x hx0 hx1).mul_left (ε / 2))]
          exact tsum_congr fun N => by ring
      _ = K * (1 - x)⁻¹ + ε / 2 * ((1 - x) ^ 2)⁻¹ := by rw [hgeo, hgeo2]
  calc (1 - x) ^ 2 * |∑' N : ℕ, (S N - L * (N + 1)) * x ^ N|
      ≤ (1 - x) ^ 2 * (K * (1 - x)⁻¹ + ε / 2 * ((1 - x) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (1 - x) * K + ε / 2 := by
        have : 1 - x ≠ 0 := h1x.ne'
        field_simp
    _ < ε := by linarith

end Rule30Equivalents.Tauberian
