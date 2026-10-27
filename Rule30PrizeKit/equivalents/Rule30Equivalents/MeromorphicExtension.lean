module

public import Rule30Equivalents.LinearRelations
public import Rule30Equivalents.NaturalBoundary
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# No meromorphic extension beyond the unit disk

Let `f(z) = ∑ c(t) zᵗ` on the unit disk. **Problem 1 holds iff `f`
extends meromorphically to no disk `‖z‖ < R` with `R > 1`**: there is no nonzero polynomial `Q`
for which `Q · f` extends holomorphically to such a disk (`problem1_iff_no_meromorphic_extension`).

This is the easy case of Szegő's theorem, after Fatou and Borel. The proof works for every bit
sequence `b` (`eventuallyPeriodic_of_meromorphicExtension`):

* the coefficients `β n` of `Q · ∑ b(t) Xᵗ` take finitely many values, one for each window
  `b(n - D), …, b(n)`, `D = deg Q` (`coeff_mul_series`, `finite_range_coeff`);
* on the unit disk `Q(z) f(z) = ∑ β n zⁿ` (Cauchy product, `eval_mul_genFun`), so the
  holomorphic extension `G` has Taylor coefficients `β n` at `0`;
* Cauchy's estimate on the circle of radius `ρ ∈ (1, R)` gives `‖β n‖ ≤ K ρ⁻ⁿ → 0`;
* a sequence with finitely many values that tends to `0` is eventually `0`. Then
  `Q · ∑ b(t) Xᵗ` is a polynomial, and `b` is eventually periodic
  (`LinearRelations.eventuallyPeriodic_of_mul_eq`).

Conversely, an eventually periodic `b` with period `P` gives `(1 - z^P) f(z)`, a polynomial
(`NaturalBoundary.mul_genFun_eq`).

The same holds with Mathlib's `MeromorphicOn` (`problem1_iff_no_meromorphicOn`): a function
meromorphic on a disk of radius `R > 1` has, on the closed disk of radius `(1 + R)/2`, finitely many
poles, which a polynomial clears (`hasMeromorphicExtension_of_meromorphicOn`).

Sources: P. Fatou, *Séries trigonométriques et séries de Taylor*, Acta Math. 30 (1906) 335–400;
G. Szegő, *Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten*, Sitzungsber. Preuss.
Akad. Wiss. (1922) 88–91.
-/

@[expose] public section

namespace Rule30Equivalents.MeromorphicExtension

open Ruliology.CellularAutomata Filter Topology Polynomial NaturalBoundary LinearRelations
open scoped NNReal

/-- `f = ∑ b(t) zᵗ` extends meromorphically to the disk of radius `R`: for some nonzero polynomial
`Q`, the function `Q · f` on the unit disk extends holomorphically to `‖z‖ < R`. -/
def HasMeromorphicExtension (b : ℕ → Bool) (R : ℝ) : Prop :=
  ∃ Q : ℂ[X], Q ≠ 0 ∧ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball 0 R) ∧
    ∀ z : ℂ, ‖z‖ < 1 → G z = Q.eval z * genFun b z

/-- The coefficients of `Q · ∑ b(t) Xᵗ` are read off a window of `b` of length `deg Q + 1`. -/
theorem coeff_mul_series (Q : ℂ[X]) (b : ℕ → Bool) (n : ℕ) :
    PowerSeries.coeff n ((Q : PowerSeries ℂ) * series ℂ b) =
      ∑ k : Fin (Q.natDegree + 1), Q.coeff k * (if (k : ℕ) ≤ n ∧ b (n - k) then 1 else 0) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (Q : PowerSeries ℂ) * PowerSeries.coeff j (series ℂ b)),
    Fin.sum_univ_eq_sum_range (fun k => Q.coeff k * (if k ≤ n ∧ b (n - k) then 1 else 0))]
  set g : ℕ → ℂ := fun k => Q.coeff k * (if k ≤ n ∧ b (n - k) then 1 else 0)
  have h1 : ∑ k ∈ Finset.range n.succ,
      PowerSeries.coeff k (Q : PowerSeries ℂ) * PowerSeries.coeff (n - k) (series ℂ b) =
      ∑ k ∈ Finset.range n.succ, g k := Finset.sum_congr rfl fun k hk => by
    rw [Finset.mem_range] at hk
    simp only [g, Polynomial.coeff_coe, coeff_series, toK]
    by_cases hb : b (n - k) <;> simp [hb, show k ≤ n by omega]
  rw [h1]
  have hg : ∀ k, n < k ∨ Q.natDegree < k → g k = 0 := fun k hk => by
    rcases hk with hk | hk
    · simp [g, show ¬ k ≤ n by omega]
    · simp [g, Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  rw [Finset.sum_subset (Finset.range_subset_range.2 (show n.succ ≤ n + Q.natDegree + 2 by omega))
      fun k _ hk => hg k (Or.inl (by simpa using hk))]
  exact (Finset.sum_subset (Finset.range_subset_range.2
    (show Q.natDegree + 1 ≤ n + Q.natDegree + 2 by omega))
    fun k _ hk => hg k (Or.inr (by simpa using hk))).symm

/-- The coefficients of `Q · ∑ b(t) Xᵗ` take finitely many values. -/
theorem finite_range_coeff (Q : ℂ[X]) (b : ℕ → Bool) :
    (Set.range fun n => PowerSeries.coeff n ((Q : PowerSeries ℂ) * series ℂ b)).Finite := by
  refine (Set.finite_range fun ε : Fin (Q.natDegree + 1) → Bool =>
    ∑ k : Fin (Q.natDegree + 1), Q.coeff (k : ℕ) * (if ε k then (1 : ℂ) else 0)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨fun k => decide ((k : ℕ) ≤ n ∧ b (n - k) = true), ?_⟩
  dsimp only
  rw [coeff_mul_series]
  simp only [decide_eq_true_eq]

/-- On the unit disk, `Q(z) f(z)` is the power series of `Q · ∑ b(t) Xᵗ`. -/
theorem eval_mul_genFun (Q : ℂ[X]) (b : ℕ → Bool) {z : ℂ} (hz : ‖z‖ < 1) :
    Q.eval z * genFun b z =
      ∑' n, PowerSeries.coeff n ((Q : PowerSeries ℂ) * series ℂ b) * z ^ n := by
  have hQ : Q.eval z = ∑' i, Q.coeff i * z ^ i := by
    rw [eval_eq_sum_range, tsum_eq_sum (s := Finset.range (Q.natDegree + 1)) fun i hi => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hi), zero_mul]]
  have hf : Summable fun i => ‖Q.coeff i * z ^ i‖ :=
    summable_of_ne_finset_zero (s := Finset.range (Q.natDegree + 1)) fun i hi => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hi), zero_mul, norm_zero]
  have hg : Summable fun t => ‖coef b t * z ^ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
      (summable_geometric_of_lt_one (norm_nonneg z) hz)
    rw [norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ?_
    unfold coef
    split_ifs <;> simp
  rw [hQ, genFun, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [Polynomial.coeff_coe, coeff_series, ← hkl, pow_add]
  simp only [coef, toK]
  ring

/-- A sequence with finitely many values that tends to `0` is eventually `0`. -/
theorem eventually_eq_zero {u : ℕ → ℂ} (hfin : (Set.range u).Finite)
    (hu : Tendsto u atTop (𝓝 0)) : ∀ᶠ n in atTop, u n = 0 := by
  have hcl : IsClosed (Set.range u \ {0}) := (hfin.sdiff).isClosed
  have hmem : (Set.range u \ {0})ᶜ ∈ 𝓝 (0 : ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hu hmem] with n hn
  by_contra hne
  exact hn ⟨⟨n, rfl⟩, hne⟩

/-- **Fatou–Szegő for a disk.** If `∑ b(t) zᵗ` extends meromorphically to a disk of radius
`R > 1`, then `b` is eventually periodic. -/
theorem eventuallyPeriodic_of_meromorphicExtension {b : ℕ → Bool} {R : ℝ} (hR : 1 < R)
    (h : HasMeromorphicExtension b R) : EventuallyPeriodic b := by
  obtain ⟨Q, hQ, G, hG, hGQ⟩ := h
  set β : ℕ → ℂ := fun n => PowerSeries.coeff n ((Q : PowerSeries ℂ) * series ℂ b)
  have hfin : (Set.range β).Finite := finite_range_coeff Q b
  -- `β` is bounded, so its power series converges on the unit disk
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hfin.isBounded
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ β
  have hrad : ((1 : ℝ≥0) : ENNReal) ≤ p.radius := p.le_radius_of_bound C fun n => by
    rw [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
    simpa using hC ⟨n, rfl⟩
  have hps : HasFPowerSeriesAt G p 0 := by
    refine (p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by simp) hrad)).hasFPowerSeriesAt.congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    rw [mem_ball_zero_iff] at hz
    rw [hGQ z hz, eval_mul_genFun Q b hz, FormalMultilinearSeries.sum]
    exact tsum_congr fun n => by
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  -- Cauchy's estimate on the circle of radius `ρ ∈ (1, R)`
  set ρ : ℝ≥0 := ⟨(1 + R) / 2, by linarith⟩
  have hρ1 : (1 : ℝ) < ρ := show (1 : ℝ) < (1 + R) / 2 by linarith
  have hρR : (ρ : ℝ) < R := show (1 + R) / 2 < R by linarith
  have hd : DifferentiableOn ℂ G (Metric.closedBall 0 ρ) :=
    hG.mono (Metric.closedBall_subset_ball hρR)
  have hcp := (hd.hasFPowerSeriesOnBall (show (0 : ℝ≥0) < ρ by
    exact_mod_cast (zero_lt_one.trans hρ1))).hasFPowerSeriesAt.eq_formalMultilinearSeries hps
  set K := (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0)..2 * Real.pi, ‖G (circleMap 0 ρ θ)‖
  have hbound : ∀ n, ‖β n‖ ≤ K * |(ρ : ℝ)|⁻¹ ^ n := fun n => by
    have := norm_cauchyPowerSeries_le G 0 ρ n
    rwa [hcp, FormalMultilinearSeries.ofScalars_norm] at this
  have hlim : Tendsto β atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    rw [← mul_zero K]
    refine Tendsto.const_mul K (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_)
    rw [abs_of_pos (zero_lt_one.trans hρ1)]
    exact inv_lt_one_of_one_lt₀ hρ1
  -- so `β` is eventually `0`, and `Q · ∑ b(t) Xᵗ` is a polynomial
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_eq_zero hfin hlim)
  refine eventuallyPeriodic_of_mul_eq (K := ℂ) (P := PowerSeries.trunc N
    ((Q : PowerSeries ℂ) * series ℂ b)) hQ (PowerSeries.ext fun n => ?_)
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact hN n (by omega)

/-- An eventually periodic sequence has a generating function that extends meromorphically to
every disk: `(1 - z^P) f(z)` is a polynomial. -/
theorem hasMeromorphicExtension_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b)
    (R : ℝ) : HasMeromorphicExtension b R := by
  obtain ⟨T, P, hP, hTP⟩ := h
  refine ⟨1 - X ^ P, fun h0 => ?_, fun z => ∑ t ∈ Finset.range (T + P),
    (coef b t - if P ≤ t then coef b (t - P) else 0) * z ^ t, ?_, fun z hz => ?_⟩
  · have := congrArg (Polynomial.coeff · 0) h0
    simp only [coeff_sub, coeff_one_zero, coeff_X_pow, coeff_zero] at this
    rw [ite_eq_right (by omega)] at this
    norm_num at this
  · exact Differentiable.differentiableOn (by fun_prop)
  · rw [eval_sub, eval_one, eval_pow, eval_X, mul_genFun_eq hTP hz]

/-- **Meromorphic in Mathlib's sense.** If `∑ b(t) zᵗ` agrees on the unit disk with a function `g`
that is meromorphic on a disk of radius `R > 1`, then a polynomial clears its poles in the smaller
disk of radius `(1 + R) / 2`: at each point `x` of the closed disk, `(z - x)ⁿ g(z)` is analytic on
a ball around `x`, finitely many of these balls cover the closed disk, and `Q = ∏ (X - x)ⁿ`. -/
theorem hasMeromorphicExtension_of_meromorphicOn {b : ℕ → Bool} {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : MeromorphicOn g (Metric.ball 0 R)) (hgb : ∀ z : ℂ, ‖z‖ < 1 → g z = genFun b z) :
    HasMeromorphicExtension b ((1 + R) / 2) := by
  classical
  set ρ := (1 + R) / 2
  have hloc : ∀ x ∈ Metric.closedBall (0 : ℂ) ρ, ∃ n : ℕ, ∃ r > 0,
      AnalyticOnNhd ℂ (fun z => (z - x) ^ n * g z) (Metric.ball x r) := by
    intro x hx
    obtain ⟨n, hn⟩ := hg x (Metric.closedBall_subset_ball (by simp only [ρ]; linarith) hx)
    obtain ⟨r, hr, han⟩ := hn.exists_ball_analyticOnNhd
    exact ⟨n, r, hr, by simpa only [smul_eq_mul] using han⟩
  choose! n r hr han using hloc
  obtain ⟨t, hts, hcover⟩ := (isCompact_closedBall (0 : ℂ) ρ).elim_nhds_subcover
    (fun x => Metric.ball x (r x)) (fun x hx => Metric.ball_mem_nhds x (hr x hx))
  set Q : ℂ[X] := ∏ x ∈ t, (X - C x) ^ n x
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x)
  refine ⟨Q, hQ, fun z => Q.eval z * g z, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 (hcover (Metric.ball_subset_closedBall hz))
    have hQfac : Q = (∏ y ∈ t.erase x, (X - C y) ^ n y) * (X - C x) ^ n x :=
      (Finset.prod_erase_mul t _ hxt).symm
    have hfac : (fun w => Q.eval w * g w) =
        fun w => (∏ y ∈ t.erase x, (X - C y) ^ n y).eval w * ((w - x) ^ n x * g w) := by
      funext w
      rw [hQfac, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      ring
    have hanz : AnalyticAt ℂ (fun w => Q.eval w * g w) z := by
      rw [hfac]
      exact ((Polynomial.differentiable _).analyticAt z).mul (han x (hts x hxt) z hzx)
    exact hanz.differentiableAt.differentiableWithinAt
  · show Q.eval z * g z = Q.eval z * genFun b z
    rw [hgb z hz]

/-- An eventually periodic sequence has a generating function that agrees on the unit disk with a
rational function, meromorphic on all of `ℂ`. -/
theorem exists_meromorphicOn_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ g : ℂ → ℂ, MeromorphicOn g Set.univ ∧ ∀ z : ℂ, ‖z‖ < 1 → g z = genFun b z := by
  obtain ⟨T, P, hP, hTP⟩ := h
  refine ⟨fun z => (∑ t ∈ Finset.range (T + P),
    (coef b t - if P ≤ t then coef b (t - P) else 0) * z ^ t) / (1 - z ^ P),
    fun x _ => ?_, fun z hz => ?_⟩
  · exact ((Differentiable.analyticAt (by fun_prop) x).meromorphicAt).fun_div
      ((Differentiable.analyticAt (by fun_prop) x).meromorphicAt)
  · have hne : 1 - z ^ P ≠ 0 := by
      intro h0
      have h1 : ‖z ^ P‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg z) hz hP.ne'
      rw [← sub_eq_zero.1 h0, norm_one] at h1
      exact lt_irrefl _ h1
    show _ / _ = _
    rw [div_eq_iff hne, mul_comm, mul_genFun_eq hTP hz]

/-- **No meromorphic extension, with Mathlib's `MeromorphicOn`.** Problem 1 holds iff the
generating function of the center column agrees on the unit disk with no function that is
meromorphic on a disk of radius `R > 1`. -/
theorem problem1_iff_no_meromorphicOn : Rule30Prize.Problem1 ↔
    ∀ R : ℝ, 1 < R → ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (Metric.ball 0 R) ∧
      ∀ z : ℂ, ‖z‖ < 1 → g z = genFun c z := by
  refine ⟨fun h1 R hR ⟨g, hg, hgb⟩ => h1 (eventuallyPeriodic_of_meromorphicExtension
    (show 1 < (1 + R) / 2 by linarith) (hasMeromorphicExtension_of_meromorphicOn hR hg hgb)),
    fun h hep => ?_⟩
  obtain ⟨g, hg, hgb⟩ := exists_meromorphicOn_of_eventuallyPeriodic hep
  exact h 2 one_lt_two ⟨g, fun x _ => hg x (Set.mem_univ x), hgb⟩

/-- **No meromorphic extension.** Problem 1 holds iff the generating function of the center
column extends meromorphically to no disk of radius `R > 1`. -/
theorem problem1_iff_no_meromorphic_extension : Rule30Prize.Problem1 ↔
    ∀ R : ℝ, 1 < R → ¬ HasMeromorphicExtension c R :=
  ⟨fun h1 _ hR hm => h1 (eventuallyPeriodic_of_meromorphicExtension hR hm),
    fun h hep => h 2 one_lt_two (hasMeromorphicExtension_of_eventuallyPeriodic hep 2)⟩

end Rule30Equivalents.MeromorphicExtension
