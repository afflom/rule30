module

public import Rule30Equivalents.Genericity
public import Rule30Equivalents.ProblemTwo
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound
public import Mathlib.Analysis.PSeries

/-!
# Random configurations

The measure-theoretic counterpart of `Genericity`. Start rule 30 from independent fair coins on
`ℤ` (`coins ℤ`, the uniform Bernoulli product measure).

* `measurePreserving_trace`: the center trace `x ↦ (evol x t 0)ₜ` pushes `coins ℤ` to `coins ℕ`,
  so the trace of a random configuration is a sequence of independent fair coins. Flipping the coin
  at `-(n+1)` preserves the measure (`map_flip`), fixes the trace up to time `n` and flips it at
  time `n + 1` (left-permutivity), so it halves the prefix event (`two_mul_measure_flip`) and
  every prefix of length `n + 1` has probability `2^-(n+1)` (`measure_prefix`); cylinders over
  initial segments then determine the measure. The same halving gives `measure_triangular`: if
  flipping the coin at `p j` flips the event `g j` and no earlier one, the events `g 0, …, g (m-1)`
  take any given values with probability `2^-m`, over any index set.
* `ae_isNormal`: **Borel's normal number theorem** for fair coins. For a word `u` of length `m`
  and a residue `r`, the blocks `v(r + k m), …, v(r + k m + m - 1)` are independent fair words
  (`map_blocks`, by reindexing and currying the product measure), so by the strong law of large
  numbers `u` occurs with frequency `2⁻ᵐ` along the residue class `r`
  (`ae_tendsto_residue_frequency`); averaging over the `m` classes gives frequency `2⁻ᵐ`
  (`tendsto_average_of_residues`).
* `trace_evol_one`: the trace intertwines rule 30 with the shift, so with `measurePreserving_trace`
  the one-sided Bernoulli shift is a factor of rule 30.
* `tendstoInDistribution_count_trace`: **the central limit theorem** for the trace (Mathlib's
  `tendstoInDistribution_inv_sqrt_mul_sum_sub`): `(black cells among the first n - n/2) / √n`
  converges in distribution to the normal law with variance `1/4`.
* `measureReal_abs_count_trace_ge_le`: **Hoeffding's inequality** for the trace (Mathlib's
  `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`): among the first `n` cells, at least
  `n/2 + n δ` or at most `n/2 - n δ` black ones has probability at most `2 exp(-2 n δ²)`. With
  Borel–Cantelli, `ae_eventually_abs_count_trace_lt`: for almost every configuration the count is
  within `√(n log n)` of `n/2` for all large `n`.
* `ae_isNormal_trace_glue`: **the right half does not matter**. The same holds for the map
  `x ↦ glue R x` that keeps the cells `p ≤ 0` of `x` and puts a fixed right half `R` beside them
  (white, say, as for the single seed): the prefix argument only flips cells left of `1`
  (`FlipsLeft`, `measure_prefix_of_flipsLeft`, `measurePreserving_trace_of_flipsLeft`). The
  argument works for every map adapted to the left coins (`Adapted`,
  `measure_inter_prefix_of_adapted`) and inside any event about the right half
  (`measure_inter_prefix_of_flipsLeft`), so
  `indepFun_trace_rightHalf`: **the trace is independent of the cells `x_1, x_2, …`**.
* `traceRightHalf`: **the configuration space is the product of the center column and the right
  half**: `x ↦ ((F^t(x)_0)ₜ, (x_n)_{n ≥ 1})` is a homeomorphism `{0,1}^ℤ ≃ {0,1}^ℕ × {0,1}^ℕ`, since
  rule 30 is affine in its left cell (`bijective_trace_rightHalf`), and it carries `coins ℤ` to the
  product of fair-coin measures (`measurePreserving_traceRightHalf`).
* `ae_isNormal_trace`: for almost every configuration the trace is normal; hence it has density
  `1/2` (`ae_halfDensity_trace`), is disjunctive (`ae_disjunctive_trace`) and is not eventually
  periodic (`ae_not_eventuallyPeriodic_trace`). The configurations whose trace has density `1/2`
  form a meager set (`Genericity.isMeagre_halfDensity_trace`) of full measure
  (`isMeagre_and_ae_halfDensity_trace`).

So the analogues of Problems 1 and 2 hold for almost every initial configuration. The single black
cell is one configuration, a null set, so neither statement says anything about `c` itself. The
configurations with an eventually periodic trace are dense, meager and null
(`dense_isMeagre_null_eventuallyPeriodic_trace`).
-/

@[expose] public section

namespace Rule30Equivalents.RandomConfigurations

open MeasureTheory ProbabilityTheory Filter Topology Ruliology.CellularAutomata Rule30Realization
  Genericity

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := Measure.uniformOfFinset Finset.univ

instance : IsProbabilityMeasure coin :=
  ⟨by simp [coin, Measure.uniformOfFinset, ENNReal.inv_two_add_inv_two]⟩

theorem coin_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  simp [coin]

/-- Independent fair coins indexed by `ι`. -/
noncomputable abbrev coins (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι => coin

/-- The fair-coin measure as a point of the space of probability measures. -/
noncomputable def coinsPM (ι : Type*) : ProbabilityMeasure (ι → Bool) := ⟨coins ι, inferInstance⟩

theorem coins_map_eval {ι : Type*} (i : ι) : (coins ι).map (fun x => x i) = coin :=
  Measure.infinitePi_map_eval _ i

theorem coins_map_restrict {ι : Type*} (I : Finset ι) :
    (coins ι).map I.restrict = Measure.pi fun _ : I => coin :=
  Measure.infinitePi_map_restrict _

theorem coins_pi {ι : Type*} (s : Finset ι) (t : ι → Set Bool) :
    coins ι (Set.pi s t) = ∏ i ∈ s, coin (t i) :=
  Measure.infinitePi_pi _ fun _ _ => MeasurableSet.of_discrete

/-- **The fair-coin measure has no atoms**: a sequence lies in the cylinder of its prefix of
length `n + 1`, of probability `2^-(n+1)`. -/
theorem coins_singleton (v : ℕ → Bool) : coins ℕ {v} = 0 := by
  have hle : ∀ n : ℕ, coins ℕ {v} ≤ 2⁻¹ ^ (n + 1) := fun n => by
    calc coins ℕ {v} ≤ coins ℕ (Set.pi (Finset.range (n + 1) : Set ℕ) fun t => {v t}) :=
          measure_mono fun u hu => by
            rw [Set.mem_singleton_iff] at hu
            subst hu
            exact fun t _ => rfl
      _ = 2⁻¹ ^ (n + 1) := by
          rw [coins_pi, Finset.prod_congr rfl fun t _ => coin_singleton (v t), Finset.prod_const,
            Finset.card_range]
  have hlim : Tendsto (fun n : ℕ => (2⁻¹ : ENNReal) ^ (n + 1)) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).comp (tendsto_add_atTop_nat 1)
  exact le_antisymm (ge_of_tendsto' hlim hle) zero_le

instance : NullSingletonClass (coins ℕ) := ⟨coins_singleton⟩

theorem measurable_evol (t : ℕ) (p : ℤ) : Measurable fun x : ℤ → Bool => evol x t p :=
  (continuous_evol t p).measurable

theorem measurable_trace : Measurable trace := continuous_trace.measurable

/-- Flipping the coin at `j`, coordinatewise. -/
theorem flip_eq {ι : Type*} [DecidableEq ι] (j : ι) :
    (fun x : ι → Bool => Function.update x j (!x j)) =
      fun x i => (if i = j then (fun b : Bool => !b) else id) (x i) := by
  funext x i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem measurable_flip {ι : Type*} [DecidableEq ι] (j : ι) :
    Measurable fun x : ι → Bool => Function.update x j (!x j) := by
  rw [flip_eq]
  exact Measurable.of_eval fun i => Measurable.of_discrete.comp (measurable_pi_apply i)

/-- Flipping one coin preserves the fair-coin measure. -/
theorem map_flip {ι : Type*} [DecidableEq ι] (j : ι) :
    (coins ι).map (fun x => Function.update x j (!x j)) = coins ι := by
  rw [flip_eq, coins, Measure.infinitePi_map_pi _ fun i => Measurable.of_discrete]
  refine congrArg Measure.infinitePi (funext fun i => ?_)
  split_ifs
  · refine Measure.ext_iff_singleton.2 fun b => ?_
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton b),
      show (fun b : Bool => !b) ⁻¹' {b} = {!b} by ext a; cases a <;> cases b <;> simp,
      coin_singleton, coin_singleton]
  · exact Measure.map_id

/-- `G` commutes with flipping any cell `p ≤ 0`: the identity does, and so does replacing the right
half by a fixed one (`glue`). -/
def FlipsLeft (G : (ℤ → Bool) → (ℤ → Bool)) : Prop :=
  ∀ x (p : ℤ), p ≤ 0 → G (Function.update x p (!x p)) = Function.update (G x) p (!G x p)

theorem flipsLeft_id : FlipsLeft id := fun _ _ _ => rfl

theorem measurableSet_prefix {G : (ℤ → Bool) → (ℤ → Bool)} (hG : Measurable G) (w : ℕ → Bool)
    (n : ℕ) : MeasurableSet {x : ℤ → Bool | ∀ t ≤ n, trace (G x) t = w t} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
    ((measurable_evol t 0).comp hG) (measurableSet_singleton (w t))

/-- **Flip halving**: if flipping the coin at `j` preserves `A` and flips `f` on `A`, then `f`
takes each value on half of `A`. -/
theorem two_mul_measure_flip {ι : Type*} [DecidableEq ι] {A : Set (ι → Bool)}
    (hA : MeasurableSet A) {f : (ι → Bool) → Bool} (hf : Measurable f) (j : ι)
    (hAj : ∀ x, Function.update x j (!x j) ∈ A ↔ x ∈ A)
    (hfj : ∀ x ∈ A, f (Function.update x j (!x j)) = !f x) (b : Bool) :
    2 * coins ι (A ∩ {x | f x = b}) = coins ι A := by
  have hB : ∀ b, MeasurableSet (A ∩ {x | f x = b}) := fun b =>
    hA.inter (hf (measurableSet_singleton b))
  have hφ : ∀ b, (fun x => Function.update x j (!x j)) ⁻¹' (A ∩ {x | f x = b}) =
      A ∩ {x | f x = !b} := by
    intro b
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, hAj]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      rw [← h, hfj x hx, Bool.not_not]
    · rintro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      rw [hfj x hx, h, Bool.not_not]
  have heq : coins ι (A ∩ {x | f x = b}) = coins ι (A ∩ {x | f x = !b}) := by
    rw [← hφ b, ← Measure.map_apply (measurable_flip j) (hB b), map_flip]
  have hsum : coins ι (A ∩ {x | f x = b}) + coins ι (A ∩ {x | f x = !b}) = coins ι A := by
    rw [← measure_union _ (hB _)]
    · congr 1
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      cases f x <;> cases b <;> simp
    · rw [Set.disjoint_left]
      rintro x ⟨-, h1⟩ ⟨-, h2⟩
      simp only [Set.mem_ofPred_eq] at h1 h2
      rw [h1] at h2
      cases b <;> simp at h2
  rw [two_mul]
  nth_rewrite 2 [heq]
  exact hsum

theorem eq_mul_inv_of_two_mul {X Y : ENNReal} (h : 2 * X = Y) : X = Y * 2⁻¹ := by
  rw [← h, mul_comm 2 X, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

/-- A Boolean function of the first `N` coins is measurable. -/
theorem measurable_of_forall_lt {g : (ℕ → Bool) → Bool} (N : ℕ)
    (hg : ∀ v w, (∀ i < N, v i = w i) → g v = g w) : Measurable g := by
  have e : g = (fun r : Finset.range N → Bool =>
      g fun i => if h : i ∈ Finset.range N then r ⟨i, h⟩ else false) ∘
        (Finset.range N).restrict := by
    funext v
    exact hg _ _ fun i hi => by simp [Finset.mem_range.2 hi]
  rw [e]
  exact (measurable_of_finite _).comp (Finset.measurable_restrict _)

/-- **Triangular events.** If flipping the coin at `p j` flips the event `g j` and changes no event
`g i` with `i < j`, then `g 0, …, g (m - 1)` take the values `β 0, …, β (m - 1)` with
probability `2^-m`. -/
theorem measure_triangular {ι : Type*} [DecidableEq ι] (g : ℕ → (ι → Bool) → Bool)
    (hg : ∀ j, Measurable (g j)) (p : ℕ → ι)
    (hflip : ∀ j v, g j (Function.update v (p j) (!v (p j))) = !g j v)
    (hfix : ∀ j v, ∀ i < j, g i (Function.update v (p j) (!v (p j))) = g i v) (β : ℕ → Bool) :
    ∀ m, coins ι {v | ∀ j < m, g j v = β j} = 2⁻¹ ^ m
  | 0 => by simp
  | m + 1 => by
    set E := {v : ι → Bool | ∀ j < m, g j v = β j} with hEdef
    have hE : MeasurableSet E := by
      simp only [hEdef, Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        hg j (measurableSet_singleton _)
    have hinv : ∀ v, Function.update v (p m) (!v (p m)) ∈ E ↔ v ∈ E := fun v => by
      simp only [hEdef, Set.mem_ofPred_eq]
      exact forall₂_congr fun j hj => by rw [hfix m v j hj]
    have h := two_mul_measure_flip hE (hg m) (p m) hinv (fun v _ => hflip m v) (β m)
    have hset : {v : ι → Bool | ∀ j < m + 1, g j v = β j} = E ∩ {v | g m v = β m} := by
      ext v
      simp only [hEdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hv
        exact ⟨fun j hj => hv j (by omega), hv m (by omega)⟩
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_or_ge j m with h' | h'
        · exact h1 j h'
        · obtain rfl : j = m := by omega
          exact h2
    rw [hset, eq_mul_inv_of_two_mul h, measure_triangular g hg p hflip hfix β m, pow_succ]

/-- A map `g` to `{0,1}^ℕ` is **adapted to the left coins** if flipping the coin at `-n` flips
`g x n` and fixes `g x t` for `t < n`. The center trace is one (`adapted_trace_of_flipsLeft`, by
left-permutivity and the light cone), and so is everything computed from the trace causally with
the new bit entering by `xor` (`BoundedRemainder.adapted_errors`). -/
def Adapted (g : (ℤ → Bool) → ℕ → Bool) : Prop :=
  ∀ x (n : ℕ), g (Function.update x (-(n : ℤ)) (!x (-(n : ℤ)))) n = !g x n ∧
    ∀ t < n, g (Function.update x (-(n : ℤ)) (!x (-(n : ℤ)))) t = g x t

/-- **Every prefix of an adapted map has probability `2^-(n+1)`, also inside an event that ignores
the left half**: `μ(A ∩ {g x starts with w}) = μ(A) 2^-(n+1)`. Flipping the coin at `-(n+1)`
preserves the measure and `A`, fixes `g x` up to time `n` and flips it at time `n + 1`. -/
theorem measure_inter_prefix_of_adapted {g : (ℤ → Bool) → ℕ → Bool}
    (hg : ∀ t, Measurable fun x => g x t) (hadapt : Adapted g) {A : Set (ℤ → Bool)}
    (hA : MeasurableSet A) (hAm : ∀ x (p : ℤ), p ≤ 0 → (Function.update x p (!x p) ∈ A ↔ x ∈ A))
    (w : ℕ → Bool) :
    ∀ n : ℕ, coins ℤ (A ∩ {x | ∀ t ≤ n, g x t = w t}) = coins ℤ A * 2⁻¹ ^ (n + 1)
  | 0 => by
    have hset : A ∩ {x : ℤ → Bool | ∀ t ≤ 0, g x t = w t} = A ∩ {x | g x 0 = w 0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine and_congr_right fun _ => ⟨fun h => h 0 le_rfl, fun h t ht => ?_⟩
      obtain rfl : t = 0 := by omega
      exact h
    have h : 2 * coins ℤ (A ∩ {x | g x 0 = w 0}) = coins ℤ A :=
      two_mul_measure_flip hA (hg 0) 0 (fun x => hAm x 0 le_rfl)
        (fun x _ => by simpa using (hadapt x 0).1) (w 0)
    rw [hset, eq_mul_inv_of_two_mul h, zero_add, pow_one]
  | n + 1 => by
    set E := A ∩ {x : ℤ → Bool | ∀ t ≤ n, g x t = w t} with hEdef
    have hEm : MeasurableSet E := by
      refine hA.inter ?_
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
        hg t (measurableSet_singleton (w t))
    -- the prefix up to time `n` and `A` do not see the coin at `-(n+1)`
    have hinv : ∀ x, Function.update x (-((n + 1 : ℕ) : ℤ)) (!x (-((n + 1 : ℕ) : ℤ))) ∈ E ↔
        x ∈ E := by
      intro x
      simp only [hEdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hAm x _ (by omega)]
      refine and_congr_right fun _ => forall_congr' fun t => imp_congr_right fun ht => ?_
      rw [(hadapt x (n + 1)).2 t (by omega)]
    have h : 2 * coins ℤ (E ∩ {x | g x (n + 1) = w (n + 1)}) = coins ℤ E :=
      two_mul_measure_flip hEm (hg (n + 1)) _ hinv (fun x _ => (hadapt x (n + 1)).1) (w (n + 1))
    have htarget : A ∩ {x : ℤ → Bool | ∀ t ≤ n + 1, g x t = w t} =
        E ∩ {x | g x (n + 1) = w (n + 1)} := by
      ext x
      simp only [hEdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨⟨hx, fun t ht => h t (by omega)⟩, h (n + 1) le_rfl⟩
      · rintro ⟨⟨hx, h1⟩, h2⟩
        refine ⟨hx, fun t ht => ?_⟩
        rcases Nat.lt_or_ge t (n + 1) with h' | h'
        · exact h1 t (by omega)
        · obtain rfl : t = n + 1 := by omega
          exact h2
    rw [htarget, eq_mul_inv_of_two_mul h, hEdef,
      measure_inter_prefix_of_adapted hg hadapt hA hAm w n, mul_assoc, ← pow_succ]

/-- Every prefix of an adapted map has probability `2^-(n+1)`. -/
theorem measure_prefix_of_adapted {g : (ℤ → Bool) → ℕ → Bool}
    (hg : ∀ t, Measurable fun x => g x t) (hadapt : Adapted g) (w : ℕ → Bool) (n : ℕ) :
    coins ℤ {x | ∀ t ≤ n, g x t = w t} = 2⁻¹ ^ (n + 1) := by
  have h := measure_inter_prefix_of_adapted hg hadapt MeasurableSet.univ
    (fun _ _ _ => Iff.rfl) w n
  rwa [Set.univ_inter, measure_univ, one_mul] at h

/-- The trace of `G x` is adapted, for `G` commuting with the flips of the cells `p ≤ 0`: flipping
the coin at `-n` flips the center at time `n` (left-permutivity) and nothing before it (the light
cone). -/
theorem adapted_trace_of_flipsLeft {G : (ℤ → Bool) → (ℤ → Bool)} (hflip : FlipsLeft G) :
    Adapted fun x t => trace (G x) t := fun x n => by
  dsimp only
  rw [hflip x (-(n : ℤ)) (by omega)]
  refine ⟨evol_flip (G x) n, fun t ht => ?_⟩
  exact AlgebraicDegree.evol_congr t 0 fun k hk1 _ => by rw [Function.update_of_ne (by omega)]

/-- **Every prefix of the trace has probability `2^-(n+1)`, also inside an event that ignores the
left half**, for `G` commuting with the flips of the cells `p ≤ 0`. -/
theorem measure_inter_prefix_of_flipsLeft {G : (ℤ → Bool) → (ℤ → Bool)} (hG : Measurable G)
    (hflip : FlipsLeft G) {A : Set (ℤ → Bool)} (hA : MeasurableSet A)
    (hAm : ∀ x (p : ℤ), p ≤ 0 → (Function.update x p (!x p) ∈ A ↔ x ∈ A)) (w : ℕ → Bool)
    (n : ℕ) :
    coins ℤ (A ∩ {x | ∀ t ≤ n, trace (G x) t = w t}) = coins ℤ A * 2⁻¹ ^ (n + 1) :=
  measure_inter_prefix_of_adapted (fun t => (measurable_evol t 0).comp hG)
    (adapted_trace_of_flipsLeft hflip) hA hAm w n

/-- **Every prefix of the trace has probability `2^-(n+1)`**, for the configuration `G x` with `G`
commuting with the flips of the cells `p ≤ 0`. -/
theorem measure_prefix_of_flipsLeft {G : (ℤ → Bool) → (ℤ → Bool)} (hG : Measurable G)
    (hflip : FlipsLeft G) (w : ℕ → Bool) (n : ℕ) :
    coins ℤ {x | ∀ t ≤ n, trace (G x) t = w t} = 2⁻¹ ^ (n + 1) := by
  have h := measure_inter_prefix_of_flipsLeft hG hflip MeasurableSet.univ
    (fun _ _ _ => Iff.rfl) w n
  rwa [Set.univ_inter, measure_univ, one_mul] at h

/-- **Every prefix of the trace has probability `2^-(n+1)`.** -/
theorem measure_prefix (w : ℕ → Bool) (n : ℕ) :
    coins ℤ {x | ∀ t ≤ n, trace x t = w t} = 2⁻¹ ^ (n + 1) :=
  measure_prefix_of_flipsLeft measurable_id flipsLeft_id w n

/-- A measurable map to `{0,1}^ℕ` whose prefix events all have probability `2^-(n+1)` under a
probability measure `ρ` carries `ρ` to `coins ℕ`: cylinders over initial segments determine the
measure. -/
theorem measurePreserving_of_measure_prefix {ρ : Measure (ℤ → Bool)} [IsProbabilityMeasure ρ]
    {g : (ℤ → Bool) → (ℕ → Bool)} (hg : Measurable g)
    (hpre : ∀ (w : ℕ → Bool) (n : ℕ), ρ {x | ∀ t ≤ n, g x t = w t} = 2⁻¹ ^ (n + 1)) :
    MeasurePreserving g ρ (coins ℕ) := by
  refine ⟨hg, ?_⟩
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs => ?_) (by rw [measure_univ, measure_univ])
  rw [measurableCylinders_nat] at hs
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hs
  obtain ⟨a, S, hS, rfl⟩ := hs
  rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _) hS,
    ← Measure.map_apply (Finset.measurable_restrict _) hS, coins_map_restrict,
    Measure.map_map (Finset.measurable_restrict _) hg]
  congr 1
  refine Measure.ext_iff_singleton.2 fun v => ?_
  rw [Measure.map_apply ((Finset.measurable_restrict _).comp hg) (measurableSet_singleton v),
    Measure.pi_singleton]
  -- the event is a prefix
  let w : ℕ → Bool := fun t => if h : t ≤ a then v ⟨t, Finset.mem_Iic.2 h⟩ else false
  have hset : ((Finset.Iic a).restrict ∘ g) ⁻¹' {v} = {x | ∀ t ≤ a, g x t = w t} := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro h t ht
      simp only [w, dite_eq_left ht]
      rw [← h]
      rfl
    · intro h
      funext i
      have := h i.1 (Finset.mem_Iic.1 i.2)
      simp only [w, dite_eq_left (Finset.mem_Iic.1 i.2)] at this
      exact this
  rw [hset, hpre, Finset.prod_congr rfl fun i _ => coin_singleton (v i), Finset.prod_const,
    Finset.card_univ, Fintype.card_coe, Nat.card_Iic]

/-- The center trace of `G x` is a fair-coin sequence, for `G` commuting with the flips left
of `1`. -/
theorem measurePreserving_trace_of_flipsLeft {G : (ℤ → Bool) → (ℤ → Bool)} (hG : Measurable G)
    (hflip : FlipsLeft G) : MeasurePreserving (fun x => trace (G x)) (coins ℤ) (coins ℕ) :=
  measurePreserving_of_measure_prefix (measurable_trace.comp hG)
    (measure_prefix_of_flipsLeft hG hflip)

/-- **The trace of a random configuration is a random sequence**: the trace map pushes the
fair-coin measure on `{0,1}^ℤ` to the fair-coin measure on `{0,1}^ℕ`. -/
theorem measurePreserving_trace : MeasurePreserving trace (coins ℤ) (coins ℕ) :=
  measurePreserving_trace_of_flipsLeft measurable_id flipsLeft_id

/-- The right half `x_1, x_2, …` of a configuration. -/
def rightHalf (x : ℤ → Bool) : ℕ → Bool := fun n => x (n + 1)

theorem continuous_rightHalf : Continuous rightHalf := continuous_pi fun _ => continuous_apply _

theorem measurable_rightHalf : Measurable rightHalf := continuous_rightHalf.measurable

/-- **The center trace is independent of the right half**: for a fair-coin configuration `x`, the
trace `(F^t(x)_0)ₜ` is independent of the cells `x_1, x_2, …`. Conditioned on any event `A` about
those cells, the trace is still a fair-coin sequence (`measure_inter_prefix_of_flipsLeft`). -/
theorem indepFun_trace_rightHalf : IndepFun trace rightHalf (coins ℤ) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  set A := rightHalf ⁻¹' t with hAdef
  have hA : MeasurableSet A := measurable_rightHalf ht
  have hAm : ∀ x (p : ℤ), p ≤ 0 → (Function.update x p (!x p) ∈ A ↔ x ∈ A) := by
    intro x p hp
    simp only [hAdef, Set.mem_preimage]
    rw [show rightHalf (Function.update x p (!x p)) = rightHalf x from
      funext fun n => Function.update_of_ne (by omega) _ _]
  have h2 : coins ℤ (trace ⁻¹' s) = coins ℕ s :=
    measurePreserving_trace.measure_preimage hs.nullMeasurableSet
  rcases eq_or_ne (coins ℤ A) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact measure_mono_null Set.inter_subset_right h0
  · have := cond_isProbabilityMeasure (μ := coins ℤ) h0
    -- conditioned on `A`, the trace is a fair-coin sequence
    have hcond : MeasurePreserving trace ((coins ℤ)[|A]) (coins ℕ) := by
      refine measurePreserving_of_measure_prefix measurable_trace fun w n => ?_
      have hpre := measure_inter_prefix_of_flipsLeft measurable_id flipsLeft_id hA hAm w n
      simp only [id] at hpre
      rw [cond_apply hA, hpre, ← mul_assoc, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _),
        one_mul]
    have h1 := hcond.measure_preimage hs.nullMeasurableSet
    rw [cond_apply hA] at h1
    calc coins ℤ (trace ⁻¹' s ∩ A)
        = coins ℤ A * ((coins ℤ A)⁻¹ * coins ℤ (A ∩ trace ⁻¹' s)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul,
            Set.inter_comm]
      _ = coins ℤ (trace ⁻¹' s) * coins ℤ A := by rw [h1, h2, mul_comm]

/-! ### Coordinates: the center column and the right half -/

theorem measurePreserving_rightHalf : MeasurePreserving rightHalf (coins ℤ) (coins ℕ) := by
  refine measurePreserving_of_measure_prefix measurable_rightHalf fun w n => ?_
  let S : Finset ℤ := (Finset.range (n + 1)).image fun t : ℕ => (t : ℤ) + 1
  have hset : {x : ℤ → Bool | ∀ t ≤ n, rightHalf x t = w t} =
      Set.pi (S : Set ℤ) fun p => {w (p - 1).toNat} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, S, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio, rightHalf, Set.mem_singleton_iff]
    constructor
    · rintro h p ⟨t, ht, rfl⟩
      rw [show ((t : ℤ) + 1 - 1).toNat = t by omega]
      exact h t (by omega)
    · intro h t ht
      have := h ((t : ℤ) + 1) ⟨t, by omega, rfl⟩
      rwa [show ((t : ℤ) + 1 - 1).toNat = t by omega] at this
  have hcard : S.card = n + 1 := by
    rw [Finset.card_image_of_injective _ fun a b h => by simpa using h, Finset.card_range]
  rw [hset, coins_pi, Finset.prod_congr rfl fun p _ => coin_singleton _, Finset.prod_const, hcard]

/-- A configuration is determined by its center column and its right half, and every pair occurs:
rule 30 is affine in its left cell (`Rule30Realization.realize`, `Rule30Realization.unique`). -/
theorem bijective_trace_rightHalf :
    Function.Bijective fun x : ℤ → Bool => (trace x, rightHalf x) := by
  constructor
  · intro x x' h
    simp only [Prod.mk.injEq] at h
    refine Rule30Realization.unique (fun p hp => ?_) fun t => congrFun h.1 t
    have := congrFun h.2 (p - 1).toNat
    simp only [rightHalf] at this
    rwa [show ((p - 1).toNat : ℤ) + 1 = p by omega] at this
  · rintro ⟨u, r⟩
    refine ⟨Rule30Realization.conf (fun p => r (p - 1).toNat) u, ?_⟩
    have h := Rule30Realization.realize (fun p => r (p - 1).toNat) u
    refine Prod.ext (funext fun t => h.2 t) (funext fun n => ?_)
    show Rule30Realization.conf _ u ((n : ℤ) + 1) = r n
    rw [h.1 _ (by omega)]
    simp

/-- **The configuration space is the product of the center column and the right half**: the map
`x ↦ ((F^t(x)_0)ₜ, (x_n)_{n ≥ 1})` is a homeomorphism `{0,1}^ℤ ≃ {0,1}^ℕ × {0,1}^ℕ` (a continuous
bijection of compact Hausdorff spaces). -/
noncomputable def traceRightHalf : (ℤ → Bool) ≃ₜ (ℕ → Bool) × (ℕ → Bool) :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bijective_trace_rightHalf)
    (continuous_trace.prodMk continuous_rightHalf)

theorem traceRightHalf_apply (x : ℤ → Bool) : traceRightHalf x = (trace x, rightHalf x) := rfl

/-- **In these coordinates the fair-coin measure is the product of fair-coin measures**: the center
column and the right half of a random configuration are independent fair-coin sequences
(`indepFun_trace_rightHalf`, `measurePreserving_trace`, `measurePreserving_rightHalf`). -/
theorem measurePreserving_traceRightHalf :
    MeasurePreserving traceRightHalf (coins ℤ) ((coins ℕ).prod (coins ℕ)) := by
  refine ⟨traceRightHalf.continuous.measurable, ?_⟩
  have h := (indepFun_iff_map_prod_eq_prod_map_map measurable_trace.aemeasurable
    measurable_rightHalf.aemeasurable).1 indepFun_trace_rightHalf
  rw [measurePreserving_trace.map_eq, measurePreserving_rightHalf.map_eq] at h
  exact h

/-- **The Bernoulli shift is a factor of rule 30**: the trace intertwines rule 30 with the shift,
`trace (F x) = σ (trace x)`, and it carries `coins ℤ` to `coins ℕ` (`measurePreserving_trace`). -/
theorem trace_evol_one (x : ℤ → Bool) : trace (evol x 1) = fun t => trace x (t + 1) := by
  funext t
  show evol (fun p => evol x 1 p) t 0 = evol x (t + 1) 0
  rw [Rule30ZeroBoundaryBarriers.evol_restart, Nat.add_comm]

/-! ### Normality almost surely (Borel) -/

/-- Summing over `[0, m q)` by residues modulo `m`. -/
theorem sum_range_mul (a : ℕ → ℝ) (m q : ℕ) :
    ∑ i ∈ Finset.range (m * q), a i =
      ∑ r ∈ Finset.range m, ∑ k ∈ Finset.range q, a (r + k * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [mul_add_one, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_range_succ, Nat.add_comm (m * q) r, Nat.mul_comm m q]

/-- **Averages from residue classes**: a `[0, 1]`-valued sequence whose averages along every
residue class modulo `m` tend to `L` has averages tending to `L`. -/
theorem tendsto_average_of_residues {a : ℕ → ℝ} {m : ℕ} (hm : 0 < m) {L : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (h : ∀ r < m, Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, a (r + k * m)) / K) atTop
      (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, a i) / N) atTop (𝓝 L) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : Tendsto (fun N : ℕ => N / m) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * m, fun N hN => (Nat.le_div_iff_mul_le hm).2 hN⟩
  -- the averages over `[0, m q)`
  have hA : Tendsto (fun q : ℕ => (∑ i ∈ Finset.range (m * q), a i) / (m * q : ℕ)) atTop
      (𝓝 L) := by
    have hsum := (tendsto_finsetSum (Finset.range m) fun r hr =>
      h r (Finset.mem_range.1 hr)).const_mul (m : ℝ)⁻¹
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hm'.ne', one_mul] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with q hq1
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq1
    rw [sum_range_mul, Finset.sum_div, Finset.mul_sum, Nat.cast_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  -- `m ⌊N / m⌋ / N → 1`
  have hB : Tendsto (fun N : ℕ => ((m * (N / m) : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hlow : Tendsto (fun N : ℕ => 1 - (m : ℝ) / N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : N ≤ m * (N / m) + m := by
        have := Nat.div_add_mod N m
        have := Nat.mod_lt N hm
        omega
      have h2 : (N : ℝ) ≤ ((m * (N / m) : ℕ) : ℝ) + m := by exact_mod_cast h1
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN', one_mul]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_one hN']
      exact_mod_cast Nat.mul_div_le N m
  -- the remainder over `[m ⌊N / m⌋, N)`
  have hsplit : ∀ N, ∑ i ∈ Finset.range N, a i = ∑ i ∈ Finset.range (m * (N / m)), a i +
      ∑ x ∈ Finset.range (N % m), a (m * (N / m) + x) := fun N => by
    rw [← Finset.sum_range_add, Nat.div_add_mod]
  have hC : Tendsto (fun N : ℕ => ((∑ i ∈ Finset.range N, a i) -
      ∑ i ∈ Finset.range (m * (N / m)), a i) / N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)) (Eventually.of_forall fun N => ?_)
      (Eventually.of_forall fun N => ?_)
    · rw [hsplit, add_sub_cancel_left]
      exact div_nonneg (Finset.sum_nonneg fun x _ => ha0 _) (Nat.cast_nonneg _)
    · rw [hsplit, add_sub_cancel_left]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      calc ∑ x ∈ Finset.range (N % m), a (m * (N / m) + x)
          ≤ ∑ x ∈ Finset.range (N % m), (1 : ℝ) := Finset.sum_le_sum fun x _ => ha1 _
        _ ≤ m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          exact_mod_cast (Nat.mod_lt N hm).le
  have hlim := ((hA.comp hq).mul hB).add hC
  rw [mul_one, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop m] with N hN
  have hq1 : 0 < N / m := Nat.div_pos hN hm
  have hmq : (0 : ℝ) < ((m * (N / m) : ℕ) : ℝ) := by positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hm hN
  simp only [Function.comp]
  field_simp
  ring

/-- **Disjoint windows are independent**: if the windows `n k, …, n k + m k - 1` are pairwise
disjoint, the words `v(n k), …, v(n k + m k - 1)` of a fair-coin sequence are independent fair
words (reindex the product measure, then curry it). -/
theorem map_windows {m n : ℕ → ℕ}
    (hinj : Function.Injective fun p : (k : ℕ) × Fin (m k) => n p.1 + p.2) :
    (coins ℕ).map (fun v k (j : Fin (m k)) => v (n k + j)) =
      Measure.infinitePi fun k => coins (Fin (m k)) := by
  have h1 : (coins ℕ).map (fun v (p : (k : ℕ) × Fin (m k)) => v (n p.1 + p.2)) =
      Measure.infinitePi fun _ : (k : ℕ) × Fin (m k) => coin :=
    Measure.map_infinitePi_infinitePi_of_inj hinj
  have h2 := Measure.infinitePi_map_piCurry (X := fun (k : ℕ) (_ : Fin (m k)) => Bool)
    fun _ _ => coin
  rw [← h2, ← h1, Measure.map_map (MeasurableEquiv.piCurry _).measurable (by fun_prop)]
  rfl

/-- The blocks `v(r + k m), …, v(r + k m + m - 1)`, `k = 0, 1, …`, of a fair-coin sequence are
independent fair words. -/
theorem map_blocks {m : ℕ} (hm : 0 < m) (r : ℕ) :
    (coins ℕ).map (fun v k (j : Fin m) => v (r + k * m + j)) =
      Measure.infinitePi fun _ : ℕ => coins (Fin m) := by
  refine map_windows (m := fun _ => m) (n := fun k => r + k * m) ?_
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  have h' : (j : ℕ) + k * m = j' + k' * m := by simp only at h; omega
  have hj : (j : ℕ) = j' := by
    have := congrArg (· % m) h'
    simpa only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt j'.2]
      using this
  have hk : k = k' := by
    have := congrArg (· / m) h'
    simpa only [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.2, Nat.div_eq_of_lt j'.2,
      zero_add] using this
  subst hk
  rw [Fin.ext hj]

/-- **Borel's theorem for one word along one residue class**: the strong law of large numbers
for the independent blocks. -/
theorem ae_tendsto_block_frequency {m : ℕ} (u : Fin m → Bool) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => coins (Fin m)),
      Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, if ω k = u then (1 : ℝ) else 0) / K) atTop
        (𝓝 ((2 : ℝ)⁻¹ ^ m)) := by
  let ρ : Measure (ℕ → Fin m → Bool) := Measure.infinitePi fun _ : ℕ => coins (Fin m)
  let g : (Fin m → Bool) → ℝ := fun b => if b = u then 1 else 0
  let X : ℕ → (ℕ → Fin m → Bool) → ℝ := fun k ω => g (ω k)
  have hg : Measurable g := Measurable.of_discrete
  have hX : ∀ k, Measurable (X k) := fun k => hg.comp (measurable_pi_apply k)
  have hmap : ∀ k, ρ.map (X k) = (coins (Fin m)).map g := fun k => by
    rw [show X k = g ∘ fun ω => ω k from rfl, ← Measure.map_map hg (measurable_pi_apply k),
      Measure.infinitePi_map_eval]
  have hind : iIndepFun X ρ := iIndepFun_infinitePi (X := fun _ => g) fun _ => hg
  have hident : ∀ k, IdentDistrib (X k) (X 0) ρ ρ := fun k =>
    ⟨(hX k).aemeasurable, (hX 0).aemeasurable, by rw [hmap, hmap]⟩
  have hint : Integrable (X 0) ρ := by
    have : Integrable g (ρ.map fun ω => ω 0) := by
      rw [Measure.infinitePi_map_eval]
      exact Integrable.of_finite
    exact this.comp_measurable (measurable_pi_apply 0)
  have hmean : ρ[X 0] = (2 : ℝ)⁻¹ ^ m := by
    show ∫ ω, g (ω 0) ∂ρ = _
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_fintype Integrable.of_finite]
    simp [g, measureReal_def, coin_singleton]
  filter_upwards [strong_law_ae X hint (fun i j hij => hind.indepFun hij) hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun K => ?_
  rw [smul_eq_mul, inv_mul_eq_div]

/-- The same, read in the fair-coin sequence: along the residue class `r` modulo `m`, the word
`u` occurs with frequency `2⁻ᵐ`. -/
theorem ae_tendsto_residue_frequency {m : ℕ} (hm : 0 < m) (u : Fin m → Bool) (r : ℕ) :
    ∀ᵐ v ∂(coins ℕ), Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K,
      if ∀ j : Fin m, v (r + k * m + j) = u j then (1 : ℝ) else 0) / K) atTop
        (𝓝 ((2 : ℝ)⁻¹ ^ m)) := by
  have hmp : MeasurePreserving (fun v k (j : Fin m) => v (r + k * m + j)) (coins ℕ)
      (Measure.infinitePi fun _ : ℕ => coins (Fin m)) := ⟨by fun_prop, map_blocks hm r⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (ae_tendsto_block_frequency u)] with v hv
  refine hv.congr fun K => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [funext_iff]

/-- **Borel's normal number theorem** for fair coins: almost every fair-coin sequence is
normal. -/
theorem ae_isNormal : ∀ᵐ v ∂(coins ℕ), StrongerStatements.IsNormal v := by
  unfold StrongerStatements.IsNormal
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun w => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the empty word occurs everywhere
    refine Eventually.of_forall fun v => ?_
    rw [pow_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Finset.filter_true_of_mem fun i _ j => j.elim0, Finset.card_range,
      div_self (Nat.cast_ne_zero.2 (by omega))]
  · filter_upwards [ae_all_iff.2 fun r : Fin n => ae_tendsto_residue_frequency hn w r]
      with v hv
    have := tendsto_average_of_residues hn
      (a := fun i => if ∀ j : Fin n, v (i + j) = w j then (1 : ℝ) else 0)
      (fun i => by split_ifs <;> norm_num)
      (fun i => by split_ifs <;> norm_num)
      fun r hr => hv ⟨r, hr⟩
    refine this.congr fun N => ?_
    rw [Finset.sum_boole]

/-- **Normal traces almost surely**: for almost every configuration, the rule 30 trace is
normal. -/
theorem ae_isNormal_trace : ∀ᵐ x ∂(coins ℤ), StrongerStatements.IsNormal (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_isNormal

/-! ### Fluctuations: the central limit theorem -/

/-- Black as `1`, white as `0`. -/
def black (b : Bool) : ℝ := if b then 1 else 0

theorem measurable_black : Measurable black := Measurable.of_discrete

theorem integral_black : ∫ b, black b ∂coin = 1 / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp [black, measureReal_def, coin_singleton]

theorem variance_black : Var[black; coin] = 1 / 4 := by
  rw [variance_eq_integral measurable_black.aemeasurable, integral_black,
    integral_fintype Integrable.of_finite]
  simp [black, measureReal_def, coin_singleton]
  norm_num

theorem measurable_centeredSum (n : ℕ) :
    Measurable fun v : ℕ → Bool => (√n)⁻¹ * (∑ k ∈ Finset.range n, black (v k) - n * (1 / 2)) :=
  ((Finset.measurable_sum _ fun k _ => measurable_black.comp (measurable_pi_apply k)).sub
    measurable_const).const_mul _

/-- **The central limit theorem for fair coins**: `(black cells among the first n - n/2) / √n`
converges in distribution to the normal law with variance `1/4`. -/
theorem tendstoInDistribution_count :
    TendstoInDistribution
      (fun (n : ℕ) (v : ℕ → Bool) => (√n)⁻¹ * (∑ k ∈ Finset.range n, black (v k) - n * (1 / 2)))
      atTop id (fun _ => coins ℕ) (gaussianReal 0 (1 / 4)) := by
  let X : ℕ → (ℕ → Bool) → ℝ := fun k v => black (v k)
  have hX : ∀ k, Measurable (X k) := fun k => measurable_black.comp (measurable_pi_apply k)
  have hmap : ∀ k, (coins ℕ).map (X k) = coin.map black := fun k => by
    rw [show X k = black ∘ fun v => v k from rfl,
      ← Measure.map_map measurable_black (measurable_pi_apply k), coins_map_eval]
  have hind : iIndepFun X (coins ℕ) :=
    iIndepFun_infinitePi (X := fun _ => black) fun _ => measurable_black
  have hident : ∀ k, IdentDistrib (X k) (X 0) (coins ℕ) (coins ℕ) := fun k =>
    ⟨(hX k).aemeasurable, (hX 0).aemeasurable, by rw [hmap, hmap]⟩
  have hL2 : MemLp (X 0) 2 (coins ℕ) :=
    memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun v => by
      simp only [X, black, Set.mem_Icc]
      split_ifs <;> norm_num) (hX 0).aestronglyMeasurable 2
  have hmean : (coins ℕ)[X 0] = 1 / 2 := by
    show ∫ v, black (v 0) ∂(coins ℕ) = 1 / 2
    rw [← integral_map (measurable_pi_apply 0).aemeasurable
      measurable_black.aestronglyMeasurable, coins_map_eval, integral_black]
  have hvar : Var[X 0; coins ℕ] = 1 / 4 := by
    rw [show X 0 = black ∘ fun v : ℕ → Bool => v 0 from rfl,
      ← variance_map measurable_black.aemeasurable (measurable_pi_apply 0).aemeasurable,
      coins_map_eval, variance_black]
  have hY : HasLaw id (gaussianReal 0 (Var[X 0; coins ℕ]).toNNReal) (gaussianReal 0 (1 / 4)) := by
    rw [hvar, show ((1 / 4 : ℝ)).toNNReal = 1 / 4 by
      rw [Real.toNNReal_div (by norm_num)]
      norm_num]
    exact HasLaw.id
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hY hL2 hind hident
  rw [hmean] at h
  exact h

/-- **Fluctuations of the density for a random configuration**: the number of black cells among
the first `n` cells of the center trace is `n/2 + √n · Z / 2` in the limit, with `Z` standard
normal: `(count - n/2) / √n` converges in distribution to the normal law with variance `1/4`.
For the single seed, Wolfram's `10⁹` bits show `500,025,038` black cells, `1.6` such standard
deviations above `n/2`. -/
theorem tendstoInDistribution_count_trace :
    TendstoInDistribution
      (fun (n : ℕ) (x : ℤ → Bool) =>
        (√n)⁻¹ * (∑ k ∈ Finset.range n, black (trace x k) - n * (1 / 2)))
      atTop id (fun _ => coins ℤ) (gaussianReal 0 (1 / 4)) := by
  have h := tendstoInDistribution_count
  refine ⟨fun n => ((measurable_centeredSum n).comp measurable_trace).aemeasurable,
    h.aemeasurable_limit, h.tendsto.congr fun n => ?_⟩
  apply Subtype.ext
  show (coins ℕ).map _ = (coins ℤ).map _
  rw [← measurePreserving_trace.map_eq, Measure.map_map (measurable_centeredSum n)
    measurable_trace]
  rfl

/-! ### Large deviations: Hoeffding's inequality -/

/-- A centered fair coin `black b - 1/2` is sub-Gaussian with parameter `1/4` (Hoeffding's
lemma). -/
theorem hasSubgaussianMGF_black (k : ℕ) :
    HasSubgaussianMGF (fun v : ℕ → Bool => black (v k) - 1 / 2) (1 / 4) (coins ℕ) := by
  have hm : AEMeasurable (fun v : ℕ → Bool => black (v k)) (coins ℕ) :=
    (measurable_black.comp (measurable_pi_apply k)).aemeasurable
  have hb : ∀ᵐ v ∂(coins ℕ), black (v k) ∈ Set.Icc (0 : ℝ) 1 := Eventually.of_forall fun v => by
    simp only [black, Set.mem_Icc]
    split_ifs <;> norm_num
  have hmean : (coins ℕ)[fun v : ℕ → Bool => black (v k)] = 1 / 2 := by
    rw [← integral_map (measurable_pi_apply k).aemeasurable
      measurable_black.aestronglyMeasurable, coins_map_eval, integral_black]
  have h := hasSubgaussianMGF_of_mem_Icc hm hb
  rw [hmean] at h
  convert h using 1
  rw [sub_zero, nnnorm_one]
  norm_num

/-- **Hoeffding's inequality for fair coins**: among the first `n` coins, the probability of at
least `n/2 + ε` black ones is at most `exp(-2ε²/n)`. -/
theorem measureReal_sum_ge_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (coins ℕ).real {v | ε ≤ ∑ k ∈ Finset.range n, (black (v k) - 1 / 2)} ≤
      Real.exp (-2 * ε ^ 2 / n) := by
  have hind : iIndepFun (fun k (v : ℕ → Bool) => black (v k) - 1 / 2) (coins ℕ) :=
    iIndepFun_infinitePi (X := fun _ b => black b - 1 / 2) fun _ =>
      measurable_black.sub measurable_const
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (c := 1 / 4) (n := n)
    (fun k _ => hasSubgaussianMGF_black k) hε
  refine h.trans_eq (congrArg Real.exp ?_)
  push_cast
  ring

/-- The same bound for at most `n/2 - ε` black coins. -/
theorem measureReal_sum_le_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (coins ℕ).real {v | ε ≤ ∑ k ∈ Finset.range n, (1 / 2 - black (v k))} ≤
      Real.exp (-2 * ε ^ 2 / n) := by
  have hind : iIndepFun (fun k (v : ℕ → Bool) => 1 / 2 - black (v k)) (coins ℕ) :=
    iIndepFun_infinitePi (X := fun _ b => 1 / 2 - black b) fun _ =>
      measurable_const.sub measurable_black
  have hsub : ∀ k < n, HasSubgaussianMGF (fun v : ℕ → Bool => 1 / 2 - black (v k)) (1 / 4)
      (coins ℕ) := fun k _ =>
    (hasSubgaussianMGF_black k).neg.congr (Eventually.of_forall fun v => by simp)
  have h :=
    HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (c := 1 / 4) (n := n) hsub hε
  refine h.trans_eq (congrArg Real.exp ?_)
  push_cast
  ring

/-- **Large deviations of the density for a random configuration** (Hoeffding's inequality): the
probability that the number of black cells among the first `n` cells of the center trace is off
from `n/2` by at least `n δ` is at most `2 exp(-2 n δ²)`. So the exceptional configurations of
each length are exponentially rare. -/
theorem measureReal_abs_count_trace_ge_le (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (coins ℤ).real {x | n * δ ≤ |∑ k ∈ Finset.range n, black (trace x k) - n / 2|} ≤
      2 * Real.exp (-2 * n * δ ^ 2) := by
  have hε : (0 : ℝ) ≤ n * δ := mul_nonneg n.cast_nonneg hδ
  have hexp : Real.exp (-2 * (n * δ) ^ 2 / n) = Real.exp (-2 * n * δ ^ 2) := by
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      simp
    · congr 1
      field_simp
  let S : Set (ℕ → Bool) := {v | n * δ ≤ |∑ k ∈ Finset.range n, black (v k) - n / 2|}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const
      (((Finset.measurable_sum _ fun k _ => measurable_black.comp (measurable_pi_apply k)).sub
        measurable_const).abs)
  have hsplit : S ⊆ {v | n * δ ≤ ∑ k ∈ Finset.range n, (black (v k) - 1 / 2)} ∪
      {v | n * δ ≤ ∑ k ∈ Finset.range n, (1 / 2 - black (v k))} := by
    intro v hv
    have e1 : ∑ k ∈ Finset.range n, (black (v k) - 1 / 2) =
        ∑ k ∈ Finset.range n, black (v k) - n / 2 := by
      rw [Finset.sum_sub_distrib]
      simp [div_eq_mul_inv]
    have e2 : ∑ k ∈ Finset.range n, (1 / 2 - black (v k)) =
        -(∑ k ∈ Finset.range n, black (v k) - n / 2) := by
      rw [Finset.sum_sub_distrib]
      simp [div_eq_mul_inv]
    simp only [Set.mem_union, Set.mem_ofPred_eq, e1, e2]
    exact (le_abs'.1 hv).symm.imp_right fun h => le_neg_of_le_neg h
  calc (coins ℤ).real {x | n * δ ≤ |∑ k ∈ Finset.range n, black (trace x k) - n / 2|}
      = (coins ℕ).real S := measurePreserving_trace.measureReal_preimage hS.nullMeasurableSet
    _ ≤ (coins ℕ).real {v | n * δ ≤ ∑ k ∈ Finset.range n, (black (v k) - 1 / 2)} +
        (coins ℕ).real {v | n * δ ≤ ∑ k ∈ Finset.range n, (1 / 2 - black (v k))} :=
      (measureReal_mono hsplit).trans (measureReal_union_le _ _)
    _ ≤ Real.exp (-2 * (n * δ) ^ 2 / n) + Real.exp (-2 * (n * δ) ^ 2 / n) :=
      add_le_add (measureReal_sum_ge_le n hε) (measureReal_sum_le_le n hε)
    _ = 2 * Real.exp (-2 * n * δ ^ 2) := by rw [hexp, two_mul]

/-- **The rate of convergence of the density**: for almost every configuration, the number of
black cells among the first `n` cells of the center trace is within `√(n log n)` of `n/2` for all
large `n`. At `n ≥ 1` the opposite has probability at most `2/n²`
(`measureReal_abs_count_trace_ge_le` with `δ = √(n log n)/n`), and these are summable
(Borel–Cantelli). -/
theorem ae_eventually_abs_count_trace_lt :
    ∀ᵐ x ∂(coins ℤ), ∀ᶠ n : ℕ in atTop,
      |∑ k ∈ Finset.range n, black (trace x k) - n / 2| < √(n * Real.log n) := by
  let s : ℕ → Set (ℤ → Bool) := fun n =>
    {x | √(n * Real.log n) ≤ |∑ k ∈ Finset.range n, black (trace x k) - n / 2|}
  have hreal : ∀ n : ℕ, (coins ℤ).real (s n) ≤ 8 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      refine measureReal_le_one.trans ?_
      norm_num
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn'
    have hnl : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn0.le hlog
    have hδ : 0 ≤ √(n * Real.log n) / n := div_nonneg (Real.sqrt_nonneg _) hn0.le
    have h := measureReal_abs_count_trace_ge_le n hδ
    rw [mul_div_cancel₀ _ hn0.ne'] at h
    have hexp : Real.exp (-2 * n * (√(n * Real.log n) / n) ^ 2) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [div_pow, Real.sq_sqrt hnl, show -2 * (n : ℝ) * (n * Real.log n / n ^ 2) =
        -Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; field_simp; ring, Real.exp_neg,
        Real.exp_log (by positivity)]
    rw [hexp] at h
    refine h.trans ?_
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum : ∑' n, coins ℤ (s n) ≠ ⊤ := by
    have hsumm : Summable fun n : ℕ => 8 / ((n : ℝ) + 1) ^ 2 := by
      have := ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left 8
      refine this.congr fun n => ?_
      push_cast
      ring
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, 8 / ((n : ℝ) + 1) ^ 2)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hreal n)
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with n hn
  simpa [s, not_le] using hn

/-! ### The right half does not matter -/

/-- The configuration that agrees with `x` at the cells `p ≤ 0` and with `R` right of `0`. -/
def glue (R x : ℤ → Bool) (p : ℤ) : Bool := if p ≤ 0 then x p else R p

theorem measurable_glue (R : ℤ → Bool) : Measurable (glue R) :=
  Measurable.of_eval fun p => by
    by_cases hp : p ≤ 0
    · simp only [glue, ite_eq_left hp]
      exact measurable_pi_apply p
    · simp only [glue, ite_eq_right hp]
      exact measurable_const

theorem flipsLeft_glue (R : ℤ → Bool) : FlipsLeft (glue R) := by
  intro x p hp
  funext q
  by_cases hq : q = p
  · subst hq
    simp [glue, hp]
  · by_cases hq0 : q ≤ 0
    · simp [glue, hq0, Function.update_of_ne hq]
    · simp [glue, hq0, Function.update_of_ne hq]

/-- **The right half does not matter**: for every right half `R` (all white, say, as for the
single seed), a fair-coin left half gives a fair-coin center trace, which is normal almost
surely. -/
theorem ae_isNormal_trace_glue (R : ℤ → Bool) :
    ∀ᵐ x ∂(coins ℤ), StrongerStatements.IsNormal (trace (glue R x)) :=
  (measurePreserving_trace_of_flipsLeft (measurable_glue R)
    (flipsLeft_glue R)).quasiMeasurePreserving.ae ae_isNormal

/-! ### Consequences: category versus measure -/

/-- For almost every configuration, the trace has density `1/2`. -/
theorem ae_halfDensity_trace : ∀ᵐ x ∂(coins ℤ), Symmetry.HalfDensity (trace x) :=
  ae_isNormal_trace.mono fun _ h => ProblemTwo.halfDensity_of_isNormal h

/-- For almost every configuration, the trace is disjunctive. -/
theorem ae_disjunctive_trace : ∀ᵐ x ∂(coins ℤ), Disjunctive (trace x) :=
  ae_isNormal_trace.mono fun _ h => StrongerStatements.disjunctive_of_isNormal h

/-- For almost every configuration, the trace is not eventually periodic. -/
theorem ae_not_eventuallyPeriodic_trace :
    ∀ᵐ x ∂(coins ℤ), ¬ EventuallyPeriodic (trace x) :=
  ae_isNormal_trace.mono fun _ h =>
    StrongerStatements.not_eventuallyPeriodic_of_disjunctive
      (StrongerStatements.disjunctive_of_isNormal h)

/-- **Meager but of full measure**: the configurations whose trace has density `1/2` (a fortiori
those with a normal trace) form a meager set of full measure. -/
theorem isMeagre_and_ae_halfDensity_trace :
    IsMeagre {x : ℤ → Bool | Symmetry.HalfDensity (trace x)} ∧
      ∀ᵐ x ∂(coins ℤ), Symmetry.HalfDensity (trace x) :=
  ⟨isMeagre_halfDensity_trace, ae_halfDensity_trace⟩

/-- **Eventually periodic traces are dense, meager and null**: every nonempty open set contains a
configuration whose trace is eventually periodic (keep a window, then make the trace eventually
white, `Genericity.exists_extend`), yet these configurations form a meager set of measure zero. -/
theorem dense_isMeagre_null_eventuallyPeriodic_trace :
    Dense {x : ℤ → Bool | EventuallyPeriodic (trace x)} ∧
      IsMeagre {x : ℤ → Bool | EventuallyPeriodic (trace x)} ∧
        coins ℤ {x : ℤ → Bool | EventuallyPeriodic (trace x)} = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dense_iff_inter_open]
    rintro U hU ⟨x, hx⟩
    obtain ⟨n, hn⟩ := exists_window_subset (hU.mem_nhds hx)
    obtain ⟨y, hy, hyw⟩ := exists_extend x n (fun t => if t ≤ n then trace x t else false)
      fun t ht => by simp [ht]
    refine ⟨y, hn fun p hp1 _ => hy p hp1, ?_⟩
    show EventuallyPeriodic (trace y)
    rw [hyw]
    exact ⟨n + 1, 1, one_pos, fun t ht => by
      simp [show ¬ (t + 1 ≤ n) by omega, show ¬ (t ≤ n) by omega]⟩
  · show {x : ℤ → Bool | EventuallyPeriodic (trace x)}ᶜ ∈ residual (ℤ → Bool)
    exact Filter.mem_of_superset residual_disjunctive_trace fun x hx =>
      StrongerStatements.not_eventuallyPeriodic_of_disjunctive hx
  · have h := ae_iff.1 ae_not_eventuallyPeriodic_trace
    simpa only [not_not] using h

end Rule30Equivalents.RandomConfigurations
