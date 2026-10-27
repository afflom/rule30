module

public import Rule30Equivalents.Mixing
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
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
# Rule 30 is an automorphism of the fair-coin measure, modulo null sets

Rule 30 `F` is not one-to-one (`Genericity.not_injective_evol_one`),
but almost every configuration has exactly one preimage (`Mixing.ae_existsUnique_preimage`). So `F`
is invertible modulo null sets:

* `exists_measurePreserving_inverse`: **there is a measurable map `G` with `G (F x) = x` and
  `F (G y) = y` for almost every `x` and `y`, and `G` preserves the fair-coin measure.** `F` is
  one-to-one on a measurable set `S` of full measure (`Mixing.exists_injOn_ae`, shrunk to a
  measurable set), so by the Lusin–Souslin theorem (Mathlib's `ContinuousOn.measurableEmbedding`)
  it is a measurable embedding there; `G` inverts it on `F(S)`, which has full measure because `F`
  preserves the measure. Then `G_* μ = G_* F_* μ = (G ∘ F)_* μ = μ`
  (`measurePreserving_of_ae_leftInverse`).
* `measurePreserving_twoSidedTrace`: **the two-sided center column of a random configuration,
  with rule 30 forward and its inverse `G` backward in time, is a two-sided sequence of independent
  fair coins** (`twoSidedTrace`). From time `-m` on it is the center column of `G^m x`
  (`twoSidedTrace_eq`), which is a fair-coin sequence because `G^m` preserves the measure.
* `ae_twoSidedTrace_evol_one`: it intertwines rule 30 with the shift, so the two-sided Bernoulli
  shift is a factor of rule 30 as an automorphism of the fair-coin measure, extending
  `RandomConfigurations.trace_evol_one` from the one-sided shift.
-/

@[expose] public section

namespace Rule30Equivalents.Invertibility

open MeasureTheory Filter Topology Ruliology.CellularAutomata Rule30Realization RandomConfigurations
  Mixing

/-- `{0,1}^ℤ` is a Polish space: separable, and completely metrizable as a countable product of
discrete spaces. -/
instance : PolishSpace (ℤ → Bool) := {}

theorem continuous_evol_one : Continuous fun x : ℤ → Bool => evol x 1 :=
  continuous_pi fun p => Genericity.continuous_evol 1 p

/-- A measurable left inverse of rule 30, almost everywhere, preserves the fair-coin measure:
`G_* μ = G_* F_* μ = (G ∘ F)_* μ = μ`. -/
theorem measurePreserving_of_ae_leftInverse {G : (ℤ → Bool) → (ℤ → Bool)} (hG : Measurable G)
    (hGF : ∀ᵐ x ∂(coins ℤ), G (evol x 1) = x) : MeasurePreserving G (coins ℤ) (coins ℤ) := by
  refine ⟨hG, ?_⟩
  have hF := measurePreserving_evol 1
  calc (coins ℤ).map G = ((coins ℤ).map fun x => evol x 1).map G := by rw [hF.map_eq]
    _ = (coins ℤ).map (G ∘ fun x => evol x 1) := Measure.map_map hG hF.measurable
    _ = (coins ℤ).map id := Measure.map_congr hGF
    _ = coins ℤ := Measure.map_id

/-- **Rule 30 is an automorphism of the fair-coin measure modulo null sets**: it has a
measure-preserving inverse `G`, with `G (F x) = x` and `F (G y) = y` almost everywhere. -/
theorem exists_measurePreserving_inverse :
    ∃ G : (ℤ → Bool) → (ℤ → Bool), MeasurePreserving G (coins ℤ) (coins ℤ) ∧
      (∀ᵐ x ∂(coins ℤ), G (evol x 1) = x) ∧ ∀ᵐ y ∂(coins ℤ), evol (G y) 1 = y := by
  obtain ⟨E, hE, hinj⟩ := exists_injOn_ae
  -- a measurable set of full measure inside `E`
  set S := (toMeasurable (coins ℤ) Eᶜ)ᶜ with hSdef
  have hS : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSc : coins ℤ Sᶜ = 0 := by rw [hSdef, compl_compl, measure_toMeasurable]; exact hE
  have hSE : S ⊆ E := fun x hx => by
    by_contra h
    exact hx (subset_toMeasurable _ _ h)
  have hemb : MeasurableEmbedding (S.domRestrict fun x : ℤ → Bool => evol x 1) :=
    continuous_evol_one.continuousOn.measurableEmbedding hS (hinj.mono hSE)
  -- invert rule 30 on `F(S)`, and do nothing elsewhere
  let G : (ℤ → Bool) → (ℤ → Bool) :=
    Function.extend (S.domRestrict fun x : ℤ → Bool => evol x 1) Subtype.val id
  have hGF : ∀ x ∈ S, G (evol x 1) = x := fun x hx =>
    hemb.injective.extend_apply Subtype.val id ⟨x, hx⟩
  have hG : Measurable G := hemb.measurable_extend measurable_subtype_coe measurable_id
  have hleft : ∀ᵐ x ∂(coins ℤ), G (evol x 1) = x := by
    have hmem : ∀ᵐ x ∂(coins ℤ), x ∈ S := mem_ae_iff.2 hSc
    filter_upwards [hmem] with x hx using hGF x hx
  refine ⟨G, measurePreserving_of_ae_leftInverse hG hleft, hleft, ?_⟩
  -- `F(S)` has full measure, since `F` preserves the measure
  have hFS : MeasurableSet ((fun x : ℤ → Bool => evol x 1) '' S) := by
    have := hemb.measurableSet_range
    rwa [Set.range_domRestrict] at this
  have hpre : coins ℤ ((fun x : ℤ → Bool => evol x 1) ⁻¹' ((fun x : ℤ → Bool => evol x 1) '' S))ᶜ
      = 0 := measure_mono_null (Set.compl_subset_compl.2 (Set.subset_preimage_image _ S)) hSc
  have hfull : coins ℤ ((fun x : ℤ → Bool => evol x 1) '' S)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hFS, ← (measurePreserving_evol 1).measure_preimage
      hFS.nullMeasurableSet, ← prob_compl_eq_one_sub (hFS.preimage (measurable_evol_all 1)), hpre]
  have hmem : ∀ᵐ y ∂(coins ℤ), y ∈ (fun x : ℤ → Bool => evol x 1) '' S := mem_ae_iff.2 hfull
  filter_upwards [hmem] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [hGF x hx]

/-! ### The two-sided center column -/

/-- The almost-everywhere inverse of rule 30 (`exists_measurePreserving_inverse`). -/
noncomputable def inv : (ℤ → Bool) → (ℤ → Bool) :=
  Classical.choose exists_measurePreserving_inverse

theorem measurePreserving_inv : MeasurePreserving inv (coins ℤ) (coins ℤ) :=
  (Classical.choose_spec exists_measurePreserving_inverse).1

theorem ae_inv_evol_one : ∀ᵐ x ∂(coins ℤ), inv (evol x 1) = x :=
  (Classical.choose_spec exists_measurePreserving_inverse).2.1

theorem ae_evol_one_inv : ∀ᵐ y ∂(coins ℤ), evol (inv y) 1 = y :=
  (Classical.choose_spec exists_measurePreserving_inverse).2.2

/-- For almost every `x`, rule 30 undoes every step of the backward orbit `G^n x`. -/
theorem ae_evol_one_inv_iterate :
    ∀ᵐ x ∂(coins ℤ), ∀ n : ℕ, evol (inv^[n + 1] x) 1 = inv^[n] x := by
  refine ae_all_iff.2 fun n => ?_
  filter_upwards [(measurePreserving_inv.iterate n).quasiMeasurePreserving.ae ae_evol_one_inv]
    with x hx
  rw [Function.iterate_succ_apply']
  exact hx

theorem evol_add_eq (y : ℤ → Bool) (a b : ℕ) : evol y (a + b) = evol (evol y a) b :=
  funext fun p => (Rule30ZeroBoundaryBarriers.evol_restart y a b p).symm

/-- Along the backward orbit, `F^k (G^m x) = G^(m - k) x` for `k ≤ m`. -/
theorem evol_inv_iterate {x : ℤ → Bool} (hx : ∀ n : ℕ, evol (inv^[n + 1] x) 1 = inv^[n] x)
    (m : ℕ) : ∀ k ≤ m, evol (inv^[m] x) k = inv^[m - k] x := by
  intro k
  induction k with
  | zero => intro _; funext p; rfl
  | succ k ih =>
    intro hk
    obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - k - 1, by omega⟩
    rw [evol_add_eq, ih (by omega), hj, hx j, show m - (k + 1) = j by omega]

/-- … and `F^k (G^m x) = F^(k - m) x` for `k ≥ m`. -/
theorem evol_inv_iterate_ge {x : ℤ → Bool} (hx : ∀ n : ℕ, evol (inv^[n + 1] x) 1 = inv^[n] x)
    (m k : ℕ) (hk : m ≤ k) : evol (inv^[m] x) k = evol x (k - m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [evol_add_eq, evol_inv_iterate hx m m le_rfl, Nat.sub_self, Function.iterate_zero_apply,
    Nat.add_sub_cancel_left]

/-- The center cell of `x` at every time `t ∈ ℤ`: forward with rule 30, backward with its
almost-everywhere inverse. -/
noncomputable def twoSidedTrace (x : ℤ → Bool) (t : ℤ) : Bool :=
  if 0 ≤ t then evol x t.toNat 0 else inv^[(-t).toNat] x 0

/-- From time `-m` on, the two-sided center column of `x` is the center column of `G^m x`. -/
theorem twoSidedTrace_eq {x : ℤ → Bool} (hx : ∀ n : ℕ, evol (inv^[n + 1] x) 1 = inv^[n] x)
    (m : ℕ) {t : ℤ} (ht : -(m : ℤ) ≤ t) :
    twoSidedTrace x t = Genericity.trace (inv^[m] x) (t + m).toNat := by
  unfold twoSidedTrace Genericity.trace
  split_ifs with h
  · rw [evol_inv_iterate_ge hx m ((t + m).toNat) (by omega),
      show (t + m).toNat - m = t.toNat by omega]
  · rw [evol_inv_iterate hx m ((t + m).toNat) (by omega),
      show m - (t + m).toNat = (-t).toNat by omega]

theorem measurable_twoSidedTrace : Measurable twoSidedTrace := by
  refine Measurable.of_eval fun t => ?_
  unfold twoSidedTrace
  split_ifs
  · exact measurable_evol t.toNat 0
  · exact (measurable_pi_apply 0).comp (measurePreserving_inv.measurable.iterate _)

/-- **The two-sided center column of a random configuration is a two-sided sequence of fair
coins**: with rule 30 forward and its inverse backward, the center cells at all times `t ∈ ℤ` are
independent fair coins. A window of times from `-m` on is a window of the one-sided center column
of `G^m x` (`twoSidedTrace_eq`), and `G^m` preserves the measure. -/
theorem measurePreserving_twoSidedTrace :
    MeasurePreserving twoSidedTrace (coins ℤ) (coins ℤ) := by
  refine ⟨measurable_twoSidedTrace, Measure.eq_infinitePi _ fun s t ht => ?_⟩
  -- shift the times in `s` into `ℕ`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ i ∈ s, -(m : ℤ) ≤ i := ⟨s.sup fun i => (-i).toNat, fun i hi => by
    have : (-i).toNat ≤ s.sup fun i => (-i).toNat := Finset.le_sup (f := fun i => (-i).toNat) hi
    omega⟩
  let φ : ℤ → ℕ := fun i => (i + m).toNat
  have hφ : ∀ i ∈ s, ((φ i : ℕ) : ℤ) - m = i := fun i hi => by
    have := hm i hi
    simp only [φ]
    omega
  have hinj : Set.InjOn φ s := fun i hi j hj h => by
    have h1 := hφ i hi
    have h2 := hφ j hj
    rw [h] at h1
    rw [← h1, h2]
  have hset : {v : ℕ → Bool | ∀ i ∈ s, v (φ i) ∈ t i} =
      Set.pi ↑(s.image φ) fun k : ℕ => t ((k : ℤ) - m) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro h k ⟨i, hi, rfl⟩
      rw [hφ i hi]
      exact h i hi
    · intro h i hi
      have := h (φ i) ⟨i, hi, rfl⟩
      rwa [hφ i hi] at this
  have hT : MeasurableSet {v : ℕ → Bool | ∀ i ∈ s, v (φ i) ∈ t i} := by
    rw [hset]
    exact MeasurableSet.pi (Finset.countable_toSet _) fun k _ => ht _
  have hpi : MeasurableSet (Set.pi (s : Set ℤ) t) :=
    MeasurableSet.pi (Finset.countable_toSet _) fun i _ => ht i
  -- almost surely the event is about the center column of `G^m x`
  have hae : twoSidedTrace ⁻¹' Set.pi s t =ᵐ[coins ℤ]
      (inv^[m]) ⁻¹' (Genericity.trace ⁻¹' {v : ℕ → Bool | ∀ i ∈ s, v (φ i) ∈ t i}) := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [ae_evol_one_inv_iterate] with x hx
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_ofPred_eq]
    exact forall₂_congr fun i hi => by rw [twoSidedTrace_eq hx m (hm i hi)]
  rw [Measure.map_apply measurable_twoSidedTrace hpi, measure_congr hae,
    (measurePreserving_inv.iterate m).measure_preimage
      (hT.preimage measurable_trace).nullMeasurableSet,
    measurePreserving_trace.measure_preimage hT.nullMeasurableSet, hset, coins_pi,
    Finset.prod_image hinj]
  exact Finset.prod_congr rfl fun i hi => by rw [hφ i hi]

/-- **The two-sided Bernoulli shift is a factor of rule 30**: almost surely the two-sided center
column of `F x` is that of `x` shifted by one. -/
theorem ae_twoSidedTrace_evol_one :
    ∀ᵐ x ∂(coins ℤ), twoSidedTrace (evol x 1) = fun t => twoSidedTrace x (t + 1) := by
  filter_upwards [ae_inv_evol_one] with x hx
  funext t
  unfold twoSidedTrace
  by_cases h : 0 ≤ t
  · rw [ite_eq_left h, ite_eq_left (by omega), ← evol_add_eq,
      show 1 + t.toNat = (t + 1).toNat by omega]
  · obtain ⟨n, hn⟩ : ∃ n, (-t).toNat = n + 1 := ⟨(-t).toNat - 1, by omega⟩
    rw [ite_eq_right h, hn, Function.iterate_succ_apply, hx]
    by_cases h' : 0 ≤ t + 1
    · rw [ite_eq_left h', show n = 0 by omega, show (t + 1).toNat = 0 by omega]
      rfl
    · rw [ite_eq_right h', show (-(t + 1)).toNat = n by omega]

end Rule30Equivalents.Invertibility
