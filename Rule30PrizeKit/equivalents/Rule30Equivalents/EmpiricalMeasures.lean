module

public import Rule30Equivalents.Mixing
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
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
# Problem 2 through empirical measures

The empirical measure of a bit sequence `b` over the times
`0, …, N` is `μ_N = (δ_b + δ_{σb} + ⋯ + δ_{σᴺb}) / (N + 1)` on `{0,1}^ℕ` (`empirical`), a point of
the compact space of probability measures (Mathlib's Prokhorov theorem). Its mass on the cylinder
`[1] = {v | v 0 = 1}` is the proportion of `1`s among `b 0, …, b N` (`empirical_one`).

* `continuous_mass_one`: `ν ↦ ν [1]` is continuous, since `[1]` is clopen (portmanteau).
* `tendsto_comp_iff_forall_mapClusterPt`: in a compact space, `g(u N) → L` for a continuous `g`
  iff `g x = L` at every cluster point `x` of `(u N)`.
* `halfDensity_iff_mapClusterPt`, `problem2_iff_mapClusterPt`: **Problem 2 holds iff every limit
  point of the empirical measures of the center column gives the cylinder `[1]` mass `1/2`.**
* `problem1_of_nonatomic_mapClusterPt`: if some limit point has no atoms, Problem 1 holds; for an
  eventually periodic sequence every empirical measure, hence every limit point, is carried by
  finitely many shifts (`not_eventuallyPeriodic_of_nonatomic`).
* `map_shift_of_mapClusterPt`: **Krylov–Bogolyubov**, every such limit point is shift-invariant.
  The function `μ ↦ ∫ f ∘ σ dμ - ∫ f dμ` is continuous and equals
  `(f(σᴺ⁺¹b) - f(b)) / (N + 1)` at the `N`-th empirical measure (`integral_empiricalOf`).
* `isNormal_iff_tendsto_empirical`: **a bit sequence is normal iff its empirical measures converge
  weakly to the fair-coin measure** (normal sequences are the generic points of the fair coin).
  Cylinders are clopen (portmanteau) and form a π-system of arbitrarily small neighbourhoods
  (Mathlib's `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`). With Borel's theorem,
  the trace of almost every configuration is generic (`ae_tendsto_empirical_trace`).
-/

@[expose] public section

namespace Rule30Equivalents.EmpiricalMeasures

open MeasureTheory Filter Topology Finset Ruliology.CellularAutomata BoundedContinuousFunction

/-- The cylinder of sequences starting with `1`. -/
def one : Set (ℕ → Bool) := {v | v 0 = true}

theorem isClopen_one : IsClopen one :=
  (isClopen_discrete {true}).preimage (continuous_apply (A := fun _ : ℕ => Bool) 0)

theorem measurableSet_one : MeasurableSet one :=
  (measurableSet_singleton true).preimage (measurable_pi_apply 0)

/-- The empirical measure of the points `u 0, …, u N` of a measurable space. -/
noncomputable def empiricalOf {X : Type*} [MeasurableSpace X] (u : ℕ → X) (N : ℕ) :
    ProbabilityMeasure X :=
  ⟨((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (u n), by
    constructor
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [measure_univ, sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact ENNReal.inv_mul_cancel (by simp) (by simp)⟩

/-- The mass of a measurable set `s` is the proportion of the times `i ≤ N` with `u i ∈ s`. -/
theorem empiricalOf_apply {X : Type*} [MeasurableSpace X] (u : ℕ → X) (N : ℕ) {s : Set X}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    ((empiricalOf u N) s : ℝ) = (#{i ∈ range (N + 1) | u i ∈ s} : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  have hμ : (empiricalOf u N : Measure X) s =
      ((N : ENNReal) + 1)⁻¹ * (#{i ∈ range (N + 1) | u i ∈ s} : ENNReal) := by
    show (((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (u n)) s = _
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul, ← sum_boole]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [Measure.dirac_apply' _ hs, Set.indicator_apply]
    simp only [Pi.one_apply]
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal, hμ, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_inv_mul]
  push_cast
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp

/-- The empirical measure of `b` over the times `0, …, N`: of the shifts `b, σb, …, σᴺb`. -/
noncomputable def empirical (b : ℕ → Bool) (N : ℕ) : ProbabilityMeasure (ℕ → Bool) :=
  empiricalOf (fun n => ShiftOrbit.shift^[n] b) N

theorem empirical_apply (b : ℕ → Bool) (N : ℕ) {s : Set (ℕ → Bool)} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) :
    ((empirical b N) s : ℝ) =
      (#{i ∈ range (N + 1) | ShiftOrbit.shift^[i] b ∈ s} : ℝ) / ((N + 1 : ℕ) : ℝ) :=
  empiricalOf_apply _ N hs

/-- **The mass of `[1]` is the proportion of `1`s** among `b 0, …, b N`. -/
theorem empirical_one (b : ℕ → Bool) (N : ℕ) :
    ((empirical b N) one : ℝ) =
      (((List.range (N + 1)).filter b).length : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  classical
  rw [empirical_apply b N measurableSet_one, ProblemTwo.count_eq_sum, sum_boole]
  congr 3
  refine filter_congr fun i _ => ?_
  simp [one, ShiftOrbit.shift_iterate]

/-- `ν ↦ ν [1]` is continuous: `[1]` is clopen, so its frontier is null (portmanteau). -/
theorem continuous_mass_one :
    Continuous fun ν : ProbabilityMeasure (ℕ → Bool) => (ν one : ℝ) := by
  refine continuous_iff_continuousAt.2 fun ν => ?_
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto (μs := id)
    (L := 𝓝 ν) tendsto_id (E := one) (by rw [isClopen_one.frontier_eq]; simp)
  exact (NNReal.continuous_coe.tendsto _).comp h

/-- **Limits through cluster points**: in a compact space, `g(u N) → L` for a continuous `g` iff
`g x = L` at every cluster point `x` of `(u N)`. -/
theorem tendsto_comp_iff_forall_mapClusterPt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {u : ℕ → X} {g : X → ℝ} (hg : Continuous g) {L : ℝ} :
    Tendsto (g ∘ u) atTop (𝓝 L) ↔ ∀ x, MapClusterPt x atTop u → g x = L := by
  constructor
  · intro h x hx
    have hgx : ClusterPt (g x) (map (g ∘ u) atTop) :=
      ClusterPt.map hx hg.continuousAt (tendsto_map'_iff.2 tendsto_map)
    have hL : ClusterPt (g x) (𝓝 L) := hgx.mono h
    by_contra hne
    exact hL.ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))
  · intro h
    by_contra hne
    rw [Metric.tendsto_atTop] at hne
    push Not at hne
    obtain ⟨ε, hε, hfreq⟩ := hne
    let S : Set ℕ := {n | ε ≤ dist ((g ∘ u) n) L}
    have hfr : ∃ᶠ n in atTop, n ∈ S := Filter.frequently_atTop.2 hfreq
    have : NeBot (atTop ⊓ 𝓟 S) := Filter.frequently_iff_neBot.1 hfr
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_clusterPt (f := map u (atTop ⊓ 𝓟 S))
      (le_principal_iff.2 univ_mem)
    have hgx := h x (hx.mono (map_mono inf_le_left))
    have hcl : ClusterPt (g x) (map (g ∘ u) (atTop ⊓ 𝓟 S)) :=
      ClusterPt.map hx hg.continuousAt (tendsto_map'_iff.2 tendsto_map)
    have hsub : map (g ∘ u) (atTop ⊓ 𝓟 S) ≤ 𝓟 {y | ε ≤ dist y L} := by
      rw [le_principal_iff, Filter.mem_map]
      exact mem_inf_of_right (mem_principal_self S)
    have hmem : g x ∈ closure {y | ε ≤ dist y L} := mem_closure_iff_clusterPt.2 (hcl.mono hsub)
    have hS : IsClosed {y : ℝ | ε ≤ dist y L} :=
      isClosed_le continuous_const (continuous_id.dist continuous_const)
    rw [hS.closure_eq, Set.mem_ofPred_eq, hgx, dist_self] at hmem
    linarith

/-- **Density `1/2` through empirical measures**, for every bit sequence: every limit point of
the empirical measures gives the cylinder `[1]` mass `1/2`. -/
theorem halfDensity_iff_mapClusterPt (b : ℕ → Bool) : Symmetry.HalfDensity b ↔
    ∀ ν : ProbabilityMeasure (ℕ → Bool), MapClusterPt ν atTop (empirical b) →
      (ν one : ℝ) = 1 / 2 := by
  rw [← tendsto_comp_iff_forall_mapClusterPt continuous_mass_one,
    ProblemTwo.halfDensity_iff_tendsto, ← tendsto_add_atTop_iff_nat 1]
  refine tendsto_congr fun N => ?_
  simp only [Function.comp, empirical_one]

/-- **Problem 2 through empirical measures**: Problem 2 holds iff every limit point of the
empirical measures of the center column gives the cylinder `[1]` mass `1/2`. -/
theorem problem2_iff_mapClusterPt : Rule30Prize.Problem2 ↔
    ∀ ν : ProbabilityMeasure (ℕ → Bool), MapClusterPt ν atTop (empirical c) →
      (ν one : ℝ) = 1 / 2 :=
  halfDensity_iff_mapClusterPt c

/-! ### Krylov–Bogolyubov -/

/-- The integral of a bounded continuous function against an empirical measure is its average
along the points. -/
theorem integral_empiricalOf {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [TopologicalSpace X] [OpensMeasurableSpace X] (u : ℕ → X) (N : ℕ) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(empiricalOf u N : Measure X) = (∑ n ∈ range (N + 1), f (u n)) / (N + 1) := by
  show ∫ x, f x ∂(((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (u n)) = _
  rw [integral_smul_measure, integral_finsetSum_measure fun n _ => f.integrable _]
  simp only [integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
    ENNReal.toReal_one, inv_mul_eq_div]

/-- **Krylov–Bogolyubov**: every limit point of the empirical measures of a bit sequence is
invariant under the shift. -/
theorem map_shift_of_mapClusterPt {b : ℕ → Bool} {ν : ProbabilityMeasure (ℕ → Bool)}
    (hν : MapClusterPt ν atTop (empirical b)) :
    (ν : Measure (ℕ → Bool)).map ShiftOrbit.shift = ν := by
  have hσ := WordsAutomata.continuous_shift
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hint : ∀ g : (ℕ → Bool) →ᵇ ℝ,
      Continuous fun μ : ProbabilityMeasure (ℕ → Bool) => ∫ x, g x ∂(μ : Measure (ℕ → Bool)) :=
    fun g => continuous_iff_continuousAt.2 fun μ =>
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id) g
  let fσ : (ℕ → Bool) →ᵇ ℝ := f.compContinuous ⟨ShiftOrbit.shift, hσ⟩
  -- `Φ μ = ∫ f ∘ σ dμ - ∫ f dμ` is continuous and tends to `0` along the empirical measures
  let Φ : ProbabilityMeasure (ℕ → Bool) → ℝ := fun μ =>
    ∫ x, fσ x ∂(μ : Measure (ℕ → Bool)) - ∫ x, f x ∂(μ : Measure (ℕ → Bool))
  have hΦ : Continuous Φ := (hint fσ).sub (hint f)
  have hcomp : ∀ N : ℕ, Φ (empirical b N) =
      (f (ShiftOrbit.shift^[N + 1] b) - f b) / ((N : ℝ) + 1) := by
    intro N
    simp only [Φ, empirical]
    rw [integral_empiricalOf, integral_empiricalOf, ← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    have hterm : ∀ n, fσ (ShiftOrbit.shift^[n] b) - f (ShiftOrbit.shift^[n] b) =
        f (ShiftOrbit.shift^[n + 1] b) - f (ShiftOrbit.shift^[n] b) := fun n => by
      simp only [fσ, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
        Function.iterate_succ_apply']
    rw [Finset.sum_congr rfl fun n _ => hterm n,
      Finset.sum_range_sub (fun n => f (ShiftOrbit.shift^[n] b)), Function.iterate_zero_apply]
  have hlim : Tendsto (Φ ∘ empirical b) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N : ℕ => 2 * ‖f‖ / ((N : ℝ) + 1)) (fun N => ?_) ?_
    · simp only [Function.comp, hcomp, norm_div]
      have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [Real.norm_of_nonneg hN.le]
      refine div_le_div_of_nonneg_right ?_ hN.le
      calc ‖f (ShiftOrbit.shift^[N + 1] b) - f b‖ ≤ ‖f (ShiftOrbit.shift^[N + 1] b)‖ + ‖f b‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
    · exact tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h0 := (tendsto_comp_iff_forall_mapClusterPt hΦ).1 hlim ν hν
  have h0' : ∫ x, f (ShiftOrbit.shift x) ∂(ν : Measure (ℕ → Bool)) -
      ∫ x, f x ∂(ν : Measure (ℕ → Bool)) = 0 := by
    simpa [Φ, fσ] using h0
  rw [integral_map hσ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact sub_eq_zero.1 h0'

/-! ### A sufficient condition for Problem 1 -/

/-- **Eventually periodic sequences have atomic limits**: if some limit point of the empirical
measures of `b` has no atoms, `b` is not eventually periodic. For an eventually periodic `b`
every shift `σⁿ b` is among the finitely many `σᵐ b`, `m < T + P`, so every empirical measure is
carried by that finite set, and so is every limit point (portmanteau for closed sets). -/
theorem not_eventuallyPeriodic_of_nonatomic {b : ℕ → Bool} {ν : ProbabilityMeasure (ℕ → Bool)}
    (hν : MapClusterPt ν atTop (empirical b)) (hna : ∀ x, (ν : Measure (ℕ → Bool)) {x} = 0) :
    ¬ EventuallyPeriodic b := by
  classical
  rintro ⟨T, P, hP, hper⟩
  let F : Finset (ℕ → Bool) := (range (T + P)).image fun n => ShiftOrbit.shift^[n] b
  have hmem : ∀ n, ShiftOrbit.shift^[n] b ∈ F := fun n => by
    obtain ⟨m, hm, hmt⟩ := ShiftOrbit.exists_lt_shift_eq hP hper n
    refine Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, ?_⟩
    rw [ShiftOrbit.shift_iterate, ShiftOrbit.shift_iterate]
    exact funext fun t => (hmt t).symm
  -- every empirical measure is carried by `F`
  have hμF : ∀ N, (empirical b N : Measure (ℕ → Bool)) (F : Set (ℕ → Bool)) = 1 := by
    intro N
    show (((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1),
      Measure.dirac (ShiftOrbit.shift^[n] b)) (F : Set (ℕ → Bool)) = 1
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    simp only [Measure.dirac_apply_of_mem (Finset.mem_coe.2 (hmem _)), sum_const, card_range,
      nsmul_eq_mul, mul_one]
    push_cast
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  -- so is `ν`
  have : NeBot (comap (empirical b) (𝓝 ν) ⊓ atTop) := neBot_inf_comap_iff_map'.2 hν.neBot
  have hlim : Tendsto (empirical b) (comap (empirical b) (𝓝 ν) ⊓ atTop) (𝓝 ν) :=
    tendsto_comap.mono_left inf_le_left
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
    (F := (F : Set (ℕ → Bool))) F.finite_toSet.isClosed
  simp only [hμF, limsup_const] at hle
  -- but a finite set of measure `1` has an atom
  rw [← sum_measure_singleton, sum_eq_zero fun x _ => hna x] at hle
  exact absurd hle (by simp)

/-- **Problem 1 from a non-atomic limit**: if some limit point of the empirical measures of the
center column has no atoms (for instance a fair-coin limit), Problem 1 holds. -/
theorem problem1_of_nonatomic_mapClusterPt {ν : ProbabilityMeasure (ℕ → Bool)}
    (hν : MapClusterPt ν atTop (empirical c)) (hna : ∀ x, (ν : Measure (ℕ → Bool)) {x} = 0) :
    Rule30Prize.Problem1 :=
  not_eventuallyPeriodic_of_nonatomic hν hna

/-! ### Normal sequences are the generic points of the fair coin -/

/-- The cylinder of sequences starting with the word `w`. -/
def cyl {n : ℕ} (w : Fin n → Bool) : Set (ℕ → Bool) := {v | ∀ j : Fin n, v j = w j}

theorem isClopen_cyl {n : ℕ} (w : Fin n → Bool) : IsClopen (cyl w) := by
  have : cyl w = ⋂ j : Fin n, (fun v : ℕ → Bool => v j) ⁻¹' {w j} := by
    ext v
    simp [cyl]
  rw [this]
  exact isClopen_iInter_of_finite fun j =>
    (isClopen_discrete {w j}).preimage (continuous_apply (A := fun _ : ℕ => Bool) j)

theorem measurableSet_cyl {n : ℕ} (w : Fin n → Bool) : MeasurableSet (cyl w) :=
  (isClopen_cyl w).isClosed.measurableSet

theorem coinsPM_cyl {n : ℕ} (w : Fin n → Bool) :
    (RandomConfigurations.coinsPM ℕ (cyl w) : ℝ) = (2 : ℝ)⁻¹ ^ n := by
  have hset : cyl w = Set.pi (Finset.range n : Set ℕ)
      (fun j => {if h : j < n then w ⟨j, h⟩ else false}) := by
    ext v
    simp only [cyl, Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      Set.mem_singleton_iff]
    constructor
    · intro h j hj
      rw [dite_eq_left hj]
      exact h ⟨j, hj⟩
    · intro h j
      have := h j j.2
      rwa [dite_eq_left j.2] at this
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal]
  show (RandomConfigurations.coins ℕ (cyl w)).toReal = _
  rw [hset, RandomConfigurations.coins_pi, Finset.prod_congr rfl fun j _ =>
    RandomConfigurations.coin_singleton _, Finset.prod_const, Finset.card_range,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- **Normal sequences are the generic points of the fair-coin measure**: a bit sequence is normal
iff its empirical measures converge weakly to the fair-coin measure on `{0,1}^ℕ`. Cylinders are
clopen (portmanteau), and they form a π-system of arbitrarily small neighbourhoods (Mathlib's
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`). -/
theorem isNormal_iff_tendsto_empirical (b : ℕ → Bool) :
    StrongerStatements.IsNormal b ↔
      Tendsto (empirical b) atTop (𝓝 (RandomConfigurations.coinsPM ℕ)) := by
  have hfreq : ∀ {n : ℕ} (w : Fin n → Bool) (N : ℕ), ((empirical b N) (cyl w) : ℝ) =
      (#{i ∈ range (N + 1) | ∀ j : Fin n, b (i + j) = w j} : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    intro n w N
    classical
    rw [empirical_apply b N (measurableSet_cyl w)]
    congr 3
    refine filter_congr fun i _ => ?_
    simp only [cyl, Set.mem_ofPred_eq, ShiftOrbit.shift_iterate]
  have hnorm : StrongerStatements.IsNormal b ↔ ∀ n (w : Fin n → Bool),
      Tendsto (fun N => ((empirical b N) (cyl w) : ℝ)) atTop (𝓝 ((2 : ℝ)⁻¹ ^ n)) := by
    refine forall_congr' fun n => forall_congr' fun w => ?_
    rw [← tendsto_add_atTop_iff_nat 1]
    exact tendsto_congr fun N => (hfreq w N).symm
  rw [hnorm]
  constructor
  · intro h
    refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
      (S := {s | ∃ n, ∃ w : Fin n → Bool, s = cyl w}) ?_ ?_ ?_ ?_
    · rintro s ⟨n, w, rfl⟩ t ⟨m, w', rfl⟩ ⟨v, hv1, hv2⟩
      rcases le_total n m with hnm | hmn
      · refine ⟨m, w', Set.ext fun u => ⟨fun hu => hu.2, fun hu => ⟨fun j => ?_, hu⟩⟩⟩
        have h1 := hu ⟨j, by omega⟩
        have h2 := hv2 ⟨j, by omega⟩
        have h3 := hv1 j
        dsimp only at h1 h2 h3
        rw [h1, ← h2, h3]
      · refine ⟨n, w, Set.ext fun u => ⟨fun hu => hu.1, fun hu => ⟨hu, fun j => ?_⟩⟩⟩
        have h1 := hu ⟨j, by omega⟩
        have h2 := hv1 ⟨j, by omega⟩
        have h3 := hv2 j
        dsimp only at h1 h2 h3
        rw [h1, ← h2, h3]
    · rintro s ⟨n, w, rfl⟩
      exact measurableSet_cyl w
    · intro u hu x hx
      obtain ⟨L, hL⟩ := Genericity.exists_prefix_subset (hu.mem_nhds hx)
      refine ⟨cyl fun j : Fin L => x j, ⟨L, _, rfl⟩,
        (isClopen_cyl _).isOpen.mem_nhds fun j => rfl, fun v hv => hL fun t ht => ?_⟩
      exact hv ⟨t, ht⟩
    · rintro s ⟨n, w, rfl⟩
      have h' := h n w
      rw [← coinsPM_cyl w] at h'
      exact NNReal.tendsto_coe.1 h'
  · intro h n w
    have h' := (NNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h (isClopen_cyl w))
    rw [coinsPM_cyl] at h'
    exact h'

/-- **Almost every trace is generic for the fair coin**: for almost every configuration, the
empirical measures of its center trace converge weakly to the fair-coin measure. -/
theorem ae_tendsto_empirical_trace :
    ∀ᵐ x ∂(RandomConfigurations.coins ℤ),
      Tendsto (empirical (Genericity.trace x)) atTop (𝓝 (RandomConfigurations.coinsPM ℕ)) :=
  RandomConfigurations.ae_isNormal_trace.mono fun _ h =>
    (isNormal_iff_tendsto_empirical _).1 h

end Rule30Equivalents.EmpiricalMeasures
