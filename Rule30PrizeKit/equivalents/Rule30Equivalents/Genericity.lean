module

public import Rule30Equivalents.AlgebraicDegree
public import Rule30Equivalents.Symmetry
public import Rule30Equivalents.LimitPoints
public import Mathlib.Topology.Baire.BaireMeasurable
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
# Generic configurations

Let `trace x = (t ↦ cell (t, 0))` be the center column of rule 30 from
a configuration `x : ℤ → Bool`.

* `continuous_trace`, `isOpenMap_trace`, `surjective_trace`: the trace map is continuous, open and
  onto. By left-permutivity, flipping the cell `-m` flips the center at time `m` and changes nothing
  before (`evol_flip`), so every continuation of a trace prefix is realized by changing only cells
  left of the prefix's light cone (`exists_extend`).
* `residual_disjunctive`, `isMeagre_halfDensity`: in `{0,1}^ℕ` the disjunctive sequences (every
  word occurs) form a comeager set, and the sequences with density `1/2` a meager one.
* So the configurations with a disjunctive trace form a comeager set
  (`residual_disjunctive_trace`), and those whose trace has density `1/2`, the property of Prize
  Problem 2, a meager set (`isMeagre_halfDensity_trace`).

The single black cell is one point of the meager, countable set of finite configurations, so
neither statement says anything about the center column `c` itself.

Rule 30 itself is onto (`surjective_evol_one`: on each window a preimage is solved from right to
left, and compactness gives a global one) and not one-to-one (`not_injective_evol_one`).

The trace carries the omega-limit set of the single black cell under rule 30 onto the
omega-limit set `ω(c)` of the center column under the shift (`image_trace_omegaLimit_seed`, from
`image_omegaLimit_eq` for continuous semiconjugacies of compact spaces), so **Problem 1 holds iff
the trace of the seed's omega-limit set is infinite**
(`problem1_iff_trace_omegaLimit_seed_infinite`), iff some configuration in it has a center
column that is not periodic (`problem1_iff_exists_omegaLimit_seed_not_periodic`). The
omega-limit set itself is infinite (`infinite_omegaLimit_seed`, from Kopra's limit points of the
right halves of the rows), so Problem 1 is about its trace, not its size. The same holds for every
configuration with a leftmost black cell (`infinite_omegaLimit`).
-/

@[expose] public section

namespace Rule30Equivalents.Genericity

open Ruliology.CellularAutomata Rule30Realization Topology Filter Set

/-- The center column of rule 30 from the configuration `x`. -/
def trace (x : ℤ → Bool) : ℕ → Bool := fun t => evol x t 0

theorem continuous_evol : ∀ (t : ℕ) (p : ℤ), Continuous fun x : ℤ → Bool => evol x t p
  | 0, p => continuous_apply p
  | t + 1, p => by
    have h := (continuous_evol t (p - 1)).prodMk ((continuous_evol t p).prodMk
      (continuous_evol t (p + 1)))
    exact (continuous_of_discreteTopology
      (f := fun q : Bool × Bool × Bool => xor q.1 (q.2.1 || q.2.2))).comp h

theorem continuous_trace : Continuous trace := continuous_pi fun t => continuous_evol t 0

/-- Flipping the cell `p - t` flips the cell `(t, p)` (left-permutivity). -/
theorem evol_flip_at (x : ℤ → Bool) (t : ℕ) (p : ℤ) :
    evol (Function.update x (p - t) (!x (p - t))) t p = !evol x t p := by
  have h := AlgebraicDegree.evol_update_left x t p
  cases hx : x (p - t)
  · rw [Bool.not_false, h, Function.update_eq_self_iff.2 hx.symm]
  · have e : Function.update x (p - t) true = x := Function.update_eq_self_iff.2 hx.symm
    rw [e] at h
    rw [Bool.not_true, h, Bool.not_not]

/-- **Left-permutivity**: flipping the cell `-m` flips the center at time `m`. -/
theorem evol_flip (x : ℤ → Bool) (m : ℕ) :
    evol (Function.update x (-(m : ℤ)) (!x (-(m : ℤ)))) m 0 = !evol x m 0 := by
  simpa using evol_flip_at x m 0

/-- **Every continuation of a trace prefix is realized**, by changing only the cells left of
`-n`. -/
theorem exists_extend (x : ℤ → Bool) (n : ℕ) (w : ℕ → Bool) (hw : ∀ t ≤ n, w t = trace x t) :
    ∃ y : ℤ → Bool, (∀ p, -(n : ℤ) ≤ p → y p = x p) ∧ trace y = w := by
  classical
  -- step `k` fixes the time `n + k + 1`, flipping the cell `-(n + k + 1)` if needed
  let step : ℕ → (ℤ → Bool) → (ℤ → Bool) := fun k y =>
    if evol y (n + k + 1) 0 = w (n + k + 1) then y
    else Function.update y (-((n + k + 1 : ℕ) : ℤ)) (!y (-((n + k + 1 : ℕ) : ℤ)))
  let cfg : ℕ → (ℤ → Bool) := fun k => Nat.rec x (fun k y => step k y) k
  have cfg_succ : ∀ k, cfg (k + 1) = step k (cfg k) := fun _ => rfl
  -- later steps only change cells further left
  have hstable : ∀ k k', k ≤ k' → ∀ p, -((n + k : ℕ) : ℤ) ≤ p → cfg k' p = cfg k p := by
    intro k k' hkk' p hp
    induction k', hkk' using Nat.le_induction with
    | base => rfl
    | succ k' hk' ih =>
      rw [cfg_succ]
      simp only [step]
      split_ifs
      · exact ih
      · rw [Function.update_of_ne (by push_cast at hp ⊢; omega)]
        exact ih
  -- the trace of `cfg k` is `w` up to time `n + k`
  have htrace : ∀ k, ∀ t ≤ n + k, evol (cfg k) t 0 = w t := by
    intro k
    induction k with
    | zero => intro t ht; exact (hw t (by omega)).symm
    | succ k ih =>
      intro t ht
      rcases Nat.lt_or_ge t (n + k + 1) with h | h
      · rw [AlgebraicDegree.evol_congr t 0 (y := cfg k) fun j hj1 hj2 =>
          hstable k (k + 1) (Nat.le_succ k) j (by push_cast; omega), ih t (by omega)]
      · obtain rfl : t = n + k + 1 := by omega
        rw [cfg_succ]
        simp only [step]
        split_ifs with hc
        · exact hc
        · have := evol_flip (cfg k) (n + k + 1)
          rw [this]
          cases hcfg : evol (cfg k) (n + k + 1) 0 <;> cases hww : w (n + k + 1) <;> simp_all
  -- the limit configuration
  let y : ℤ → Bool := fun p => if -(n : ℤ) ≤ p then x p else cfg ((-p).toNat - n) p
  have hy : ∀ k, ∀ p, -((n + k : ℕ) : ℤ) ≤ p → y p = cfg k p := by
    intro k p hp
    simp only [y]
    split_ifs with h
    · exact (hstable 0 k (Nat.zero_le k) p (by push_cast; omega)).symm
    · have hk : (-p).toNat - n ≤ k := by omega
      exact (hstable _ k hk p (by push_cast; omega)).symm
  refine ⟨y, fun p hp => by simp only [y, ite_eq_left hp], funext fun t => ?_⟩
  show evol y t 0 = w t
  rw [AlgebraicDegree.evol_congr t 0 (y := cfg t) fun j hj1 hj2 => hy t j (by push_cast; omega),
    htrace t t (by omega)]

theorem surjective_trace : Function.Surjective trace := fun w => by
  obtain ⟨y, -, hy⟩ := exists_extend (fun p => if p = 0 then w 0 else false) 0 w fun t ht => by
    obtain rfl : t = 0 := by omega
    simp [trace, evol]
  exact ⟨y, hy⟩

/-- A neighbourhood of a configuration contains a cylinder over a window `[-n, n]`. -/
theorem exists_window_subset {x : ℤ → Bool} {U : Set (ℤ → Bool)} (hU : U ∈ 𝓝 x) :
    ∃ n : ℕ, {y | ∀ p, -(n : ℤ) ≤ p → p ≤ n → y p = x p} ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIt⟩ := hU
  obtain ⟨n, hn⟩ := (hI.image Int.natAbs).bddAbove
  refine ⟨n, fun y hy => hIt fun i hi => ?_⟩
  have hin : i.natAbs ≤ n := hn ⟨i, hi, rfl⟩
  rw [hy i (by omega) (by omega)]
  exact mem_of_mem_nhds (ht i)

/-- A cylinder over a prefix is a neighbourhood of a sequence. -/
theorem prefix_mem_nhds (v : ℕ → Bool) (n : ℕ) : {u : ℕ → Bool | ∀ t ≤ n, u t = v t} ∈ 𝓝 v := by
  have h : ∀ t, ∀ᶠ u in 𝓝 v, u t = v t := fun t =>
    (continuous_apply t).continuousAt ((isOpen_discrete {v t}).mem_nhds rfl)
  have hfin : (Set.Iic n).Finite := Set.finite_Iic n
  exact (hfin.eventually_all.2 fun t _ => h t).mono fun u hu t ht => hu t ht

/-- **The trace map is open**: the image of a window cylinder is the cylinder of its trace
prefix. -/
theorem isOpenMap_trace : IsOpenMap trace := by
  rw [isOpenMap_iff_nhds_le]
  intro x V hV
  obtain ⟨n, hn⟩ := exists_window_subset (Filter.mem_map.1 hV)
  refine Filter.mem_of_superset (prefix_mem_nhds (trace x) n) fun v hv => ?_
  obtain ⟨y, hyx, hyv⟩ := exists_extend x n v hv
  have : y ∈ trace ⁻¹' V := hn fun p hp _ => hyx p hp
  rwa [Set.mem_preimage, hyv] at this

/-! ### Comeager and meager sets of sequences -/

/-- Every finite word occurs in `v`. -/
def Disjunctive (v : ℕ → Bool) : Prop := ∀ n (w : Fin n → Bool), ∃ i, ∀ j : Fin n, v (i + j) = w j

/-- A neighbourhood of a sequence contains a cylinder over a prefix. -/
theorem exists_prefix_subset {v : ℕ → Bool} {U : Set (ℕ → Bool)} (hU : U ∈ 𝓝 v) :
    ∃ L : ℕ, {u | ∀ t < L, u t = v t} ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIt⟩ := hU
  obtain ⟨L, hL⟩ := hI.bddAbove
  refine ⟨L + 1, fun u hu => hIt fun i hi => ?_⟩
  rw [hu i (by have := hL hi; omega)]
  exact mem_of_mem_nhds (ht i)

/-- A single sequence is nowhere dense in `{0,1}^ℕ`: every neighborhood contains another one. -/
theorem isNowhereDense_singleton (v : ℕ → Bool) : IsNowhereDense ({v} : Set (ℕ → Bool)) := by
  have : (𝓝[≠] v).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
    intro U hU
    obtain ⟨L, hL⟩ := exists_prefix_subset hU
    refine ⟨Function.update v L (!v L), hL fun t ht => ?_, ?_⟩
    · exact Function.update_of_ne (by omega) _ _
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      have := congrFun he L
      simp at this
  rw [isClosed_singleton.isNowhereDense_iff, interior_singleton]

/-- **Disjunctive sequences are generic**: they form a comeager set. -/
theorem residual_disjunctive : {v : ℕ → Bool | Disjunctive v} ∈ residual (ℕ → Bool) := by
  have h : {v : ℕ → Bool | Disjunctive v} =
      ⋂ p : (Σ n, Fin n → Bool), {v | ∃ i, ∀ j : Fin p.1, v (i + j) = p.2 j} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Disjunctive, Sigma.forall]
  rw [h]
  refine countable_iInter_mem.2 fun p => residual_of_dense_open ?_ ?_
  · rw [Set.ofPred_exists]
    refine isOpen_iUnion fun i => ?_
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      (isOpen_discrete ({p.2 j} : Set Bool)).preimage
        (continuous_apply (A := fun _ : ℕ => Bool) (i + (j : ℕ)))
  · rw [dense_iff_inter_open]
    rintro U hU ⟨v, hv⟩
    obtain ⟨L, hL⟩ := exists_prefix_subset (hU.mem_nhds hv)
    -- copy the prefix of `v`, then the word
    refine ⟨fun t => if t < L then v t else if h : t - L < p.1 then p.2 ⟨t - L, h⟩ else false,
      hL fun t ht => by simp only [ite_eq_left ht], L, fun j => ?_⟩
    simp only [show ¬ (L + (j : ℕ) < L) by omega, ite_false, show L + (j : ℕ) - L = j by omega,
      dite_eq_left j.isLt]

/-- The number of `true` values of `v` before `n`. -/
def count (v : ℕ → Bool) (n : ℕ) : ℕ := ((List.range n).filter v).length

theorem count_succ (v : ℕ → Bool) (n : ℕ) :
    count v (n + 1) = count v n + if v n then 1 else 0 := by
  unfold count
  rw [List.range_succ, List.filter_append, List.length_append]
  cases hv : v n <;> simp [hv]

theorem count_congr {u v : ℕ → Bool} {n : ℕ} (h : ∀ t < n, u t = v t) : count u n = count v n := by
  unfold count
  congr 1
  exact List.filter_congr fun t ht => h t (List.mem_range.1 ht)

theorem le_count {v : ℕ → Bool} {L : ℕ} (h : ∀ t, L ≤ t → v t = true) : ∀ n, n - L ≤ count v n
  | 0 => by simp
  | n + 1 => by
    rw [count_succ]
    have := le_count h n
    by_cases hn : L ≤ n
    · rw [h n hn, ite_eq_left rfl]
      omega
    · omega

/-- **Sequences with density `1/2` are rare**: they form a meager set. Sequences with a frequency of
ones at least `2/3` infinitely often are generic, and none of them has density `1/2`. -/
theorem isMeagre_halfDensity : IsMeagre {v : ℕ → Bool | Symmetry.HalfDensity v} := by
  have hA : (⋂ N : ℕ, ⋃ n : ℕ, {v : ℕ → Bool | N < n ∧ 2 * n ≤ 3 * count v n}) ∈
      residual (ℕ → Bool) := by
    refine countable_iInter_mem.2 fun N => residual_of_dense_open ?_ ?_
    · refine isOpen_iUnion fun n => ?_
      -- the condition reads only the first `n` letters
      rw [isOpen_iff_mem_nhds]
      intro v hv
      refine Filter.mem_of_superset (prefix_mem_nhds v n) fun u hu => ?_
      rw [Set.mem_ofPred_eq, count_congr fun t ht => hu t ht.le]
      exact hv
    · rw [dense_iff_inter_open]
      rintro U hU ⟨v, hv⟩
      obtain ⟨L, hL⟩ := exists_prefix_subset (hU.mem_nhds hv)
      -- copy the prefix of `v`, then only ones
      refine ⟨fun t => if t < L then v t else true, hL fun t ht => by simp only [ite_eq_left ht],
          ?_⟩
      refine Set.mem_iUnion.2 ⟨3 * (L + N + 1), by omega, ?_⟩
      have := le_count (v := fun t => if t < L then v t else true) (L := L)
        (fun t ht => by simp only [show ¬ t < L by omega, ite_false]) (3 * (L + N + 1))
      omega
  refine Filter.mem_of_superset hA fun v hv hhalf => ?_
  simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq] at hv
  obtain ⟨N, hN⟩ := hhalf 10 (by norm_num)
  obtain ⟨n, hNn, hn⟩ := hv N
  have h1 := hN n hNn.le
  unfold count at hn
  omega

/-- **Configurations with a disjunctive trace are generic.** -/
theorem residual_disjunctive_trace :
    {x : ℤ → Bool | Disjunctive (trace x)} ∈ residual (ℤ → Bool) :=
  tendsto_residual_of_isOpenMap continuous_trace isOpenMap_trace residual_disjunctive

/-- **Configurations whose trace has density `1/2` are rare.** -/
theorem isMeagre_halfDensity_trace :
    IsMeagre {x : ℤ → Bool | Symmetry.HalfDensity (trace x)} :=
  isMeagre_halfDensity.preimage_of_isOpenMap continuous_trace isOpenMap_trace

/-! ### Rule 30 is onto, not one-to-one -/

/-- A preimage of `y` on the window `[-n, n]`, solved from right to left:
`k ↦ (x(n+1-k), x(n+2-k))`, with white cells right of `n`. -/
def preimPair (y : ℤ → Bool) (n : ℕ) : ℕ → Bool × Bool
  | 0 => (false, false)
  | k + 1 => (xor (y ((n : ℤ) + 1 - k)) ((preimPair y n k).1 || (preimPair y n k).2),
      (preimPair y n k).1)

/-- The configuration of `preimPair`. -/
def preimWin (y : ℤ → Bool) (n : ℕ) (p : ℤ) : Bool :=
  if p ≤ (n : ℤ) + 1 then (preimPair y n ((n : ℤ) + 1 - p).toNat).1 else false

theorem preimWin_eq (y : ℤ → Bool) (n : ℕ) (k : ℕ) :
    preimWin y n ((n : ℤ) + 1 - k) = (preimPair y n k).1 := by
  unfold preimWin
  rw [ite_eq_left (by omega), show ((n : ℤ) + 1 - ((n : ℤ) + 1 - k)).toNat = k by omega]

theorem preimWin_succ (y : ℤ → Bool) (n : ℕ) (k : ℕ) :
    preimWin y n ((n : ℤ) + 1 - (k + 1 : ℕ) + 1) = (preimPair y n (k + 1)).2 := by
  rw [show ((n : ℤ) + 1 - (k + 1 : ℕ) + 1) = (n : ℤ) + 1 - k by push_cast; ring, preimWin_eq]
  rfl

/-- `preimWin y n` is a preimage of `y` at every cell `p ≤ n`. -/
theorem evol_preimWin (y : ℤ → Bool) (n : ℕ) (p : ℤ) (hp : p ≤ n) :
    evol (preimWin y n) 1 p = y p := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p = (n : ℤ) + 1 - (k + 1 : ℕ) := ⟨(n - p).toNat, by omega⟩
  have e0 : preimWin y n p = (preimPair y n (k + 1)).1 := by rw [hk, preimWin_eq]
  have e1 : preimWin y n (p + 1) = (preimPair y n (k + 1)).2 := by rw [hk, preimWin_succ]
  have e2 : preimWin y n (p - 1) = (preimPair y n (k + 2)).1 := by
    rw [hk, show (n : ℤ) + 1 - (k + 1 : ℕ) - 1 = (n : ℤ) + 1 - (k + 2 : ℕ) by push_cast; ring,
      preimWin_eq]
  show xor (preimWin y n (p - 1)) (preimWin y n p || preimWin y n (p + 1)) = y p
  rw [e0, e1, e2]
  simp only [preimPair]
  rw [show (n : ℤ) + 1 - ((k + 1 : ℕ) : ℤ) = p by omega]
  cases y p <;> cases (preimPair y n k).1 <;> cases (preimPair y n k).2 <;> simp

/-- **Rule 30 is onto**: every configuration has a preimage. On each window `[-n, n]` a preimage
is solved from right to left (left-permutivity), and compactness of `{0,1}^ℤ` gives a global one. -/
theorem surjective_evol_one : Function.Surjective fun x : ℤ → Bool => evol x 1 := by
  intro y
  let F : ℕ → Set (ℤ → Bool) := fun n => {x | ∀ p, -(n : ℤ) ≤ p → p ≤ n → evol x 1 p = y p}
  have hclosed : ∀ n, IsClosed (F n) := fun n => by
    simp only [F, Set.ofPred_forall]
    refine isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact (isClosed_discrete {y p}).preimage (continuous_evol 1 p)
  have hne : ∀ n, (F n).Nonempty := fun n => ⟨preimWin y n, fun p _ hp => evol_preimWin y n p hp⟩
  have hmono : ∀ n, F (n + 1) ⊆ F n := fun n x hx p _ _ => hx p (by omega) (by omega)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne
    (hclosed 0).isCompact hclosed
  refine ⟨x, funext fun p => ?_⟩
  exact (Set.mem_iInter.1 hx p.natAbs) p (by omega) (by omega)

/-- **Rule 30 is not one-to-one**: the all-black configuration and the all-white one both turn
all white. -/
theorem not_injective_evol_one : ¬ Function.Injective fun x : ℤ → Bool => evol x 1 := by
  intro h
  have := congrFun (@h (fun _ => true) (fun _ => false) (funext fun p => rfl)) 0
  exact absurd this (by decide)

/-! ### The omega-limit set of the seed -/

/-- A continuous map `π` from a compact space carries the omega-limit set of a point onto the set
of cluster points of the images of its orbit. A cluster point `z` of the images comes from a
limit point of the orbit along the finer filter on which the images tend to `z`. -/
theorem image_omegaLimit_eq_mapClusterPt {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {π : X → Y} (hπ : Continuous π) (ϕ : ℕ → X → X) (x : X) :
    π '' omegaLimit atTop ϕ {x} = {z | MapClusterPt z atTop fun t => π (ϕ t x)} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    exact hy.continuousAt_comp hπ.continuousAt
  · intro hz
    -- the times at which the images approach `z`
    set G := atTop ⊓ comap (fun t => π (ϕ t x)) (𝓝 z) with hG
    have : NeBot G := by
      rw [hG, inf_comm]
      exact neBot_inf_comap_iff_map'.2 hz.neBot
    obtain ⟨y, -, hy⟩ := isCompact_univ.exists_clusterPt (f := map (fun t => ϕ t x) G)
      (le_principal_iff.2 univ_mem)
    refine ⟨y, (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ x y).2
      (hy.mono (map_mono inf_le_left)), ?_⟩
    -- `π y` is a cluster point of a filter that converges to `z`
    have h1 : ClusterPt (π y) (map (fun t => π (ϕ t x)) G) := by
      have := hy.map hπ.continuousAt (tendsto_map)
      rwa [map_map] at this
    have h2 : map (fun t => π (ϕ t x)) G ≤ 𝓝 z := by
      rw [hG, map_le_iff_le_comap]
      exact inf_le_right
    exact eq_of_nhds_neBot (h1.neBot.mono (inf_le_inf_left _ h2))

/-- A continuous semiconjugacy `π` from a compact space carries the omega-limit set of a point onto
the omega-limit set of its image. -/
theorem image_omegaLimit_eq {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {π : X → Y} (hπ : Continuous π) {ϕ : ℕ → X → X}
    {ψ : ℕ → Y → Y} (hsemi : ∀ t x, π (ϕ t x) = ψ t (π x)) (x : X) :
    π '' omegaLimit atTop ϕ {x} = omegaLimit atTop ψ {π x} := by
  rw [image_omegaLimit_eq_mapClusterPt hπ ϕ x]
  ext z
  rw [mem_omegaLimit_singleton_iff_mapClusterPt]
  simp only [mem_ofPred_eq, hsemi]

/-- **The omega-limit set of the center column is the trace of that of the seed**: `ω_σ(c)` is
the image under the center trace of the omega-limit set of the single black cell under rule 30. -/
theorem image_trace_omegaLimit_seed :
    trace '' omegaLimit atTop (fun (n : ℕ) (x : ℤ → Bool) => evol x n) {seed} =
      omegaLimit atTop (fun (n : ℕ) (b : ℕ → Bool) => fun t => b (n + t)) {c} := by
  have hc : trace seed = c := funext fun t => by
    show evol seed t 0 = Rule30Prize.center t
    rw [evol_seed]
    rfl
  rw [← hc]
  refine image_omegaLimit_eq continuous_trace (fun n x => funext fun t => ?_) seed
  show evol (evol x n) t 0 = evol x (n + t) 0
  exact Rule30ZeroBoundaryBarriers.evol_restart x n t 0

/-- **Problem 1 through the omega-limit set of the seed**: Problem 1 holds iff the center trace of
the omega-limit set of the single black cell under rule 30 is infinite. -/
theorem problem1_iff_trace_omegaLimit_seed_infinite : Rule30Prize.Problem1 ↔
    (trace '' omegaLimit atTop (fun (n : ℕ) (x : ℤ → Bool) => evol x n) {seed}).Infinite := by
  rw [image_trace_omegaLimit_seed]
  exact WordsAutomata.problem1_iff_omegaLimit_infinite

/-- **Problem 1 through a limit configuration of the seed**: Problem 1 holds iff some
configuration in the omega-limit set of the single black cell under rule 30 has a center column
that is not periodic. -/
theorem problem1_iff_exists_omegaLimit_seed_not_periodic : Rule30Prize.Problem1 ↔
    ∃ y ∈ omegaLimit atTop (fun (n : ℕ) (x : ℤ → Bool) => evol x n) {seed},
      trace y ∉ Function.periodicPts ShiftOrbit.shift := by
  rw [WordsAutomata.problem1_iff_omegaLimit_not_periodic, ← image_trace_omegaLimit_seed]
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, hz⟩
    exact ⟨y, hy, hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨trace y, ⟨y, hy, rfl⟩, hz⟩

/-- **The omega-limit set of every configuration with a leftmost black cell is infinite**: its
right halves are the limit points of the right halves of the rows
(`image_omegaLimit_eq_mapClusterPt`), and there are infinitely many of those (Kopra,
`LimitPoints.infinite_limitPoints_evol`). -/
theorem infinite_omegaLimit {x : ℤ → Bool} {lo : ℤ} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) :
    (omegaLimit atTop (fun (n : ℕ) (y : ℤ → Bool) => evol y n) {x}).Infinite := by
  have hR : Continuous fun (y : ℤ → Bool) (p : ℕ) => y p :=
    continuous_pi fun p => continuous_apply _
  have h := image_omegaLimit_eq_mapClusterPt hR (fun (n : ℕ) (y : ℤ → Bool) => evol y n) x
  have hhalf : {z : ℕ → Bool | MapClusterPt z atTop fun t => fun p : ℕ => evol x t p} =
      LimitPoints.limitPoints (evol x) := rfl
  rw [hhalf] at h
  exact Set.Infinite.of_image _ (h ▸ LimitPoints.infinite_limitPoints_evol hlo hzero)

/-- **The omega-limit set of the seed is infinite** (`infinite_omegaLimit`). Problem 1 asks whether
its center trace is infinite too (`problem1_iff_trace_omegaLimit_seed_infinite`). -/
theorem infinite_omegaLimit_seed :
    (omegaLimit atTop (fun (n : ℕ) (x : ℤ → Bool) => evol x n) {seed}).Infinite :=
  infinite_omegaLimit (lo := 0) (by simp [seed]) fun p hp => by simp [seed]; omega

end Rule30Equivalents.Genericity
