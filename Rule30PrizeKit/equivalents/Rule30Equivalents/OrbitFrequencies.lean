module

public import Rule30Equivalents.EmpiricalMeasures
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
# Pattern frequencies along rule 30 orbits

A pointwise ergodic theorem for rule 30 and local
patterns, proved from independence alone. Mathlib has no pointwise ergodic theorem, but it has
Etemadi's strong law of large numbers, which needs only pairwise independence.

* `indepFun_indicator`, `map_indicator_eq`: indicators of independent events are independent
  random variables, and indicators of events of equal probability have the same law.
* `measure_inter_window_time`: the window `I` of row `s` and of row `t` are independent when some
  `m` separates them, `m ≤ i - s` and `i - t < m` on `I` (independence beyond the light cone,
  `Mixing.measure_inter_window`).
* `ae_tendsto_residue`: along a residue class `r + kg` of times with `g` larger than the width of
  `I`, these events are pairwise independent with probability `2^-|I|`, so the strong law applies.
* `ae_orbit_frequency`: averaging the residue classes
  (`RandomConfigurations.tendsto_average_of_residues`), **for almost every configuration, every
  pattern on every window `[-n, n]` appears in the rows of the space-time diagram with frequency
  `2^-(2n+1)`.**
* `ae_orbit_frequency_progression`: the same along every arithmetic progression `a + Ps` of times,
  by splitting it into `2n + 1` sub-progressions of step `(2n + 1) P`. Wolfram asks whether the
  right halves `y_{Pk+r}` of the rows of the seed are equidistributed; at the level of
  digits, this is the answer for almost every configuration.
* `ae_tendsto_orbit_empirical`: so **almost every configuration is generic** for the fair-coin
  measure under rule 30: the empirical measures of its orbit converge weakly to it (the window
  patterns form a π-system of small neighbourhoods,
  `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`).
-/

@[expose] public section

namespace Rule30Equivalents.OrbitFrequencies

open MeasureTheory ProbabilityTheory Filter Topology Finset Ruliology.CellularAutomata
  Rule30Realization Genericity RandomConfigurations Mixing

/-- Indicators of two independent events are independent random variables. -/
theorem indepFun_indicator {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (h : μ (E ∩ F) = μ E * μ F) :
    IndepFun (E.indicator (1 : Ω → ℝ)) (F.indicator (1 : Ω → ℝ)) μ := by
  have hind := (IndepSet_iff_Indep E F μ).1 ((indepSet_iff_measure_inter_eq_mul hE hF μ).2 h)
  have hle : ∀ G : Set Ω, MeasurableSpace.comap (G.indicator (1 : Ω → ℝ)) inferInstance ≤
      MeasurableSpace.generateFrom {G} := fun G => by
    let : MeasurableSpace Ω := MeasurableSpace.generateFrom {G}
    exact Measurable.comap_le (measurable_one.indicator
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton G)))
  rw [IndepFun_iff_Indep]
  exact (indep_of_indep_of_le_left (indep_of_indep_of_le_left hind (hle E)).symm (hle F)).symm

/-- Indicators of events of equal probability have the same law. -/
theorem map_indicator_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) (h : μ E = μ F) :
    μ.map (E.indicator (1 : Ω → ℝ)) = μ.map (F.indicator (1 : Ω → ℝ)) := by
  classical
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_one.indicator hE) hA,
    Measure.map_apply (measurable_one.indicator hF) hA,
    show (1 : Ω → ℝ) = fun _ => 1 from rfl, Set.indicator_const_preimage_eq_union,
    Set.indicator_const_preimage_eq_union]
  split_ifs <;> simp [prob_compl_eq_one_sub hE, prob_compl_eq_one_sub hF, h]

/-- **Two rows far apart in time are independent on a window**. -/
theorem measure_inter_window_time {I : Finset ℤ} {w : ℤ → Bool} {s t : ℕ} {m : ℤ}
    (hs : ∀ i ∈ I, m ≤ i - s) (ht : ∀ i ∈ I, i - t < m) :
    coins ℤ ({x | ∀ i ∈ I, evol x s i = w i} ∩ {x | ∀ i ∈ I, evol x t i = w i}) =
      coins ℤ {x | ∀ i ∈ I, evol x s i = w i} * coins ℤ {x | ∀ i ∈ I, evol x t i = w i} := by
  have hAm : ∀ x p, p < m → (Function.update x p (!x p) ∈ {x : ℤ → Bool | ∀ i ∈ I,
      evol x s i = w i} ↔ x ∈ {x : ℤ → Bool | ∀ i ∈ I, evol x s i = w i}) := by
    intro x p hp
    simp only [Set.mem_ofPred_eq]
    refine forall₂_congr fun i hi => ?_
    rw [AlgebraicDegree.evol_update_of_far (Or.inl (by have := hs i hi; omega))]
  rw [measure_inter_window (measurableSet_window s I w) hAm t w I ht, measure_window t I w]

/-- **The strong law along one residue class of times.** -/
theorem ae_tendsto_residue (I : Finset ℤ) (w : ℤ → Bool) (g r : ℕ)
    (hsep : ∀ j k : ℕ, j < k → ∃ m : ℤ, (∀ i ∈ I, m ≤ i - (r + j * g : ℕ)) ∧
      ∀ i ∈ I, i - (r + k * g : ℕ) < m) :
    ∀ᵐ x ∂(coins ℤ), Tendsto (fun K : ℕ => (∑ k ∈ range K,
      ({y | ∀ i ∈ I, evol y (r + k * g) i = w i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / K) atTop
        (𝓝 ((2 : ℝ)⁻¹ ^ I.card)) := by
  let E : ℕ → Set (ℤ → Bool) := fun k => {y | ∀ i ∈ I, evol y (r + k * g) i = w i}
  let Y : ℕ → (ℤ → Bool) → ℝ := fun k => (E k).indicator 1
  have hE : ∀ k, MeasurableSet (E k) := fun k => measurableSet_window _ I w
  have hμE : ∀ k, coins ℤ (E k) = 2⁻¹ ^ I.card := fun k => measure_window _ I w
  have hind : Pairwise fun j k => IndepFun (Y j) (Y k) (coins ℤ) := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · obtain ⟨m, hm1, hm2⟩ := hsep j k h
      exact indepFun_indicator (hE j) (hE k) (measure_inter_window_time hm1 hm2)
    · obtain ⟨m, hm1, hm2⟩ := hsep k j h
      exact (indepFun_indicator (hE k) (hE j) (measure_inter_window_time hm1 hm2)).symm
  have hident : ∀ k, IdentDistrib (Y k) (Y 0) (coins ℤ) (coins ℤ) := fun k =>
    ⟨(measurable_one.indicator (hE k)).aemeasurable,
      (measurable_one.indicator (hE 0)).aemeasurable,
      map_indicator_eq (hE k) (hE 0) ((hμE k).trans (hμE 0).symm)⟩
  have hint : Integrable (Y 0) (coins ℤ) := (integrable_const 1).indicator (hE 0)
  have hmean : (coins ℤ)[Y 0] = (2 : ℝ)⁻¹ ^ I.card := by
    rw [integral_indicator_one (hE 0), measureReal_def, hμE 0, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  filter_upwards [strong_law_ae Y hint hind hident] with x hx
  rw [hmean] at hx
  refine hx.congr fun K => ?_
  rw [smul_eq_mul, inv_mul_eq_div]

/-- **Pattern frequencies along every progression of times**: for almost every configuration `x`,
every pattern `v` on every window `[-n, n]` appears in the rows `a, a + P, a + 2P, …` of the
space-time diagram of `x` with frequency `2^-(2n+1)`. Split the progression into `2n + 1`
sub-progressions of step `(2n + 1) P`, along which the events are pairwise independent. Wolfram
asks whether the right halves `y_{Pk+r}` of the rows of the single seed are equidistributed;
at the level of digits, this answers it for almost every configuration. -/
theorem ae_orbit_frequency_progression :
    ∀ᵐ x ∂(coins ℤ), ∀ (P a n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool), 0 < P →
      Tendsto (fun T : ℕ => (∑ s ∈ range T, ({y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n,
        evol y (a + P * s) i = extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / T) atTop
          (𝓝 ((2 : ℝ)⁻¹ ^ (2 * n + 1))) := by
  refine ae_all_iff.2 fun P => ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
    ae_all_iff.2 fun v => ?_
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · exact Eventually.of_forall fun x h => absurd h (lt_irrefl 0)
  have hcard : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  have hG : 2 * n + 1 ≤ (2 * n + 1) * P := Nat.le_mul_of_pos_right _ hP
  have hres : ∀ᵐ x ∂(coins ℤ), ∀ r : Fin (2 * n + 1), Tendsto (fun K : ℕ => (∑ k ∈ range K,
      ({y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, evol y ((a + P * r) + k * ((2 * n + 1) * P)) i =
        extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / K) atTop
          (𝓝 ((2 : ℝ)⁻¹ ^ (Finset.Icc (-(n : ℤ)) n).card)) := by
    refine ae_all_iff.2 fun r => ae_tendsto_residue _ _ ((2 * n + 1) * P) (a + P * r)
      fun j k hjk => ?_
    refine ⟨-(n : ℤ) - ((a + P * r) + j * ((2 * n + 1) * P) : ℕ), fun i hi => ?_,
      fun i hi => ?_⟩
    · have := (Finset.mem_Icc.1 hi).1
      omega
    · have hi2 := (Finset.mem_Icc.1 hi).2
      have hkj : (j + 1) * ((2 * n + 1) * P) ≤ k * ((2 * n + 1) * P) :=
        Nat.mul_le_mul_right _ hjk
      have hkj' : ((j * ((2 * n + 1) * P) : ℕ) : ℤ) + ((2 * n + 1) * P : ℕ) ≤
          ((k * ((2 * n + 1) * P) : ℕ) : ℤ) := by
        rw [add_mul, one_mul] at hkj
        exact_mod_cast hkj
      have hG' : ((2 * n + 1 : ℕ) : ℤ) ≤ (((2 * n + 1) * P : ℕ) : ℤ) := by exact_mod_cast hG
      push_cast at hkj' hG' ⊢
      omega
  filter_upwards [hres] with x hx hP'
  rw [← hcard]
  refine tendsto_average_of_residues (m := 2 * n + 1) (Nat.succ_pos _)
    (a := fun s => {y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, evol y (a + P * s) i =
      extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x)
    (fun i => by simp only [Set.indicator]; split_ifs <;> norm_num)
    (fun i => by simp only [Set.indicator]; split_ifs <;> norm_num) fun r hr => ?_
  refine (hx ⟨r, hr⟩).congr fun K => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  show _ = {y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, evol y (a + P * (r + k * (2 * n + 1))) i =
      extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x
  rw [show a + P * (r + k * (2 * n + 1)) = (a + P * r) + k * ((2 * n + 1) * P) by ring]

/-- **Pattern frequencies along almost every orbit** (a pointwise ergodic theorem for local
patterns): for almost every configuration `x`, every pattern `v` on every window `[-n, n]`
appears in the rows of the space-time diagram of `x` with frequency `2^-(2n+1)`. -/
theorem ae_orbit_frequency :
    ∀ᵐ x ∂(coins ℤ), ∀ (n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool),
      Tendsto (fun T : ℕ => (∑ t ∈ range T, ({y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n,
        evol y t i = extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / T) atTop
          (𝓝 ((2 : ℝ)⁻¹ ^ (2 * n + 1))) := by
  filter_upwards [ae_orbit_frequency_progression] with x hx n v
  have := hx 1 0 n v one_pos
  simp only [zero_add, one_mul] at this
  exact this

/-! ### Generic points -/

/-- The configurations that show the pattern `v` on the window `[-n, n]`. -/
def windowSet (n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool) : Set (ℤ → Bool) :=
  {y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, y i = extend v i}

theorem coinsPM_windowSet (n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool) :
    (coinsPM ℤ (windowSet n v) : ℝ) = (2 : ℝ)⁻¹ ^ (2 * n + 1) := by
  have hcard : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal]
  show (coins ℤ {y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, evol y 0 i = extend v i}).toReal = _
  rw [measure_window, hcard, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- **Almost every configuration is generic** for the fair-coin measure under rule 30: the
empirical measures `(δ_x + δ_{Fx} + ⋯ + δ_{F^T x}) / (T + 1)` of its orbit converge weakly to the
fair-coin measure. -/
theorem ae_tendsto_orbit_empirical :
    ∀ᵐ x ∂(coins ℤ), Tendsto (fun T => EmpiricalMeasures.empiricalOf (fun t => evol x t) T)
      atTop (𝓝 (coinsPM ℤ)) := by
  filter_upwards [ae_orbit_frequency] with x hx
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (S := {s | ∃ n v, s = windowSet n v}) ?_ ?_ ?_ ?_
  · rintro s ⟨n, v, rfl⟩ t ⟨n', v', rfl⟩ ⟨z, hz1, hz2⟩
    rcases le_total n n' with h | h
    · refine ⟨n', v', Set.ext fun u => ⟨fun hu => hu.2, fun hu => ⟨fun i hi => ?_, hu⟩⟩⟩
      have hi' : i ∈ Finset.Icc (-(n' : ℤ)) n' := by
        rw [Finset.mem_Icc] at hi ⊢
        omega
      rw [hu i hi', ← hz2 i hi', hz1 i hi]
    · refine ⟨n, v, Set.ext fun u => ⟨fun hu => hu.1, fun hu => ⟨hu, fun i hi => ?_⟩⟩⟩
      have hi' : i ∈ Finset.Icc (-(n : ℤ)) n := by
        rw [Finset.mem_Icc] at hi ⊢
        omega
      rw [hu i hi', ← hz1 i hi', hz2 i hi]
  · rintro s ⟨n, v, rfl⟩
    exact measurableSet_window 0 _ _
  · intro u hu y hy
    obtain ⟨n, hn⟩ := exists_window_subset (hu.mem_nhds hy)
    refine ⟨windowSet n ((Finset.Icc (-(n : ℤ)) n).restrict y), ⟨n, _, rfl⟩,
      (isOpen_window 0 _ _).mem_nhds fun i hi => by simp [Mixing.extend, hi]; rfl,
      fun z hz => hn fun p hp1 hp2 => ?_⟩
    have := hz p (Finset.mem_Icc.2 ⟨hp1, hp2⟩)
    simpa [Mixing.extend, Finset.mem_Icc.2 ⟨hp1, hp2⟩] using this
  · rintro s ⟨n, v, rfl⟩
    have h := hx n v
    rw [← tendsto_add_atTop_iff_nat 1] at h
    rw [← coinsPM_windowSet n v] at h
    refine NNReal.tendsto_coe.1 (h.congr fun T => ?_)
    classical
    have hW : MeasurableSet (windowSet n v) := measurableSet_window 0 _ _
    rw [EmpiricalMeasures.empiricalOf_apply _ T hW, ← sum_boole]
    congr 1

end Rule30Equivalents.OrbitFrequencies
