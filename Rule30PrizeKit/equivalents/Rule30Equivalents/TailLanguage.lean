module

public import Rule30Equivalents.WordsAutomata
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# The tail language: no flat step, no Rauzy cycle

`WordsAutomata.tailFactors b n` is the set of words of length `n` that occur in `b` infinitely
often, the tail language `L∞(b)`; write `p∞(n)` for its size.

* `eventually_factors_eq_tailFactors`: past some time, the windows of a given length that occur
  in `b` are exactly the words of `L∞(b)`.
* `eventuallyPeriodic_iff_tail_flat`: `b` is eventually periodic iff `p∞` has a flat step,
  `p∞(m + 1) ≤ p∞(m)` for some `m`. A flat step is a flat step of the factor complexity of a tail
  of `b`, so Morse–Hedlund applies (`ShiftOrbit.eventuallyPeriodic_of_ncard_factors_succ_le`).
* `problem1_iff_tail_strictMono`: Problem 1 holds iff `p∞` is strictly
  increasing.
* `tailSubshift b`: the two-sided subshift with language `L∞(b)`, the sequences `ℤ → Bool` all of
  whose windows occur in `b` infinitely often. `exists_mem_tailSubshift`: every word of `L∞(b)` is
  a window of one of its points, a cluster point of shifts of `b` in the compact space `ℤ → Bool`.
  `infinite_tailSubshift_iff`: the subshift is infinite iff `b` is not eventually periodic. If `b`
  has period `P` from some time on, every point has period `P`. Otherwise `p∞(n) > n` for every
  `n`, and distinct words of `L∞(b)` extend to distinct points.
* `problem1_iff_tailSubshift_infinite`.

The Rauzy graph `Γ_m` of `L∞(c)` has the words of `L∞(c)` of length `m` as vertices and one edge
`u → v` for each word of `L∞(c)` of length `m + 1` with prefix `u` and suffix `v`. Every vertex has
an outgoing edge and `Γ_m` is strongly connected, so `Γ_m` is a single cycle exactly when it has as
many edges as vertices, `p∞(m + 1) = p∞(m)`. So `problem1_iff_tail_strictMono` says that no Rauzy
graph of the tail language of the center column is a single cycle. The graphs themselves are not
formalized here.

Sources: G. Rauzy, *Suites à termes dans un alphabet fini*, Sém. Théorie des Nombres de Bordeaux
(1983); J. Cassaigne and F. Nicolas, *Factor complexity*, in Combinatorics, Automata and Number
Theory (2010).
-/

@[expose] public section

namespace Rule30Equivalents.TailLanguage

open Ruliology.CellularAutomata WordsAutomata

/-- **Past some time, the windows of length `n` are exactly the tail factors.** -/
theorem eventually_factors_eq_tailFactors (b : ℕ → Bool) (n : ℕ) :
    ∃ N, ∀ M, N ≤ M → ShiftOrbit.factors (fun t => b (M + t)) n = tailFactors b n := by
  have hev : ∀ u : Fin n → Bool, ∀ᶠ i in Filter.atTop,
      (fun j : Fin n => b (i + j)) = u → u ∈ tailFactors b n := by
    intro u
    by_cases hu : u ∈ tailFactors b n
    · exact Filter.Eventually.of_forall fun _ _ => hu
    · have hu' : ¬ ∃ᶠ i in Filter.atTop, (fun j : Fin n => b (i + j)) = u := hu
      exact (Filter.not_frequently.1 hu').mono fun i hi he => absurd he hi
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hev)
  refine ⟨N, fun M hM => Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨i, rfl⟩
    have := hN (M + i) (by omega) _ rfl
    simpa only [Nat.add_assoc] using this
  · intro w hw
    obtain ⟨i, hi, hiw⟩ := Filter.frequently_atTop.1 hw M
    refine ⟨i - M, ?_⟩
    rw [← hiw]
    funext j
    simp only
    congr 1
    omega

/-- The empty word occurs at every position. -/
theorem ncard_tailFactors_zero (b : ℕ → Bool) : (tailFactors b 0).ncard = 1 := by
  have : tailFactors b 0 = Set.univ := by
    ext w
    simp only [Set.mem_univ, iff_true]
    exact Filter.Frequently.of_forall fun i => funext fun j => j.elim0
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, pow_zero]

/-- **`b` is eventually periodic iff its tail complexity has a flat step.** -/
theorem eventuallyPeriodic_iff_tail_flat (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ m, (tailFactors b (m + 1)).ncard ≤ (tailFactors b m).ncard := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (eventuallyPeriodic_iff_exists_ncard_tailFactors_le b).1 h
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ k, k + 1 ≤ (tailFactors b k).ncard := by
      intro k
      induction k with
      | zero => rw [ncard_tailFactors_zero]
      | succ k ih => have := hcon k; omega
    have := hgrow n
    omega
  · rintro ⟨m, hm⟩
    obtain ⟨N₁, h₁⟩ := eventually_factors_eq_tailFactors b m
    obtain ⟨N₂, h₂⟩ := eventually_factors_eq_tailFactors b (m + 1)
    apply eventuallyPeriodic_of_tail (max N₁ N₂)
    apply ShiftOrbit.eventuallyPeriodic_of_ncard_factors_succ_le (n := m)
    rw [h₁ _ (le_max_left _ _), h₂ _ (le_max_right _ _)]
    exact hm

/-- **Problem 1 ⟺ the tail complexity of the center column is strictly increasing**:
no Rauzy graph of its tail language is a single cycle. -/
theorem problem1_iff_tail_strictMono :
    Rule30Prize.Problem1 ↔ ∀ m, (tailFactors c m).ncard < (tailFactors c (m + 1)).ncard := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_tail_flat]
  push Not
  rfl

/-! ### The subshift form -/

/-- The two-sided subshift with language `L∞(b)`: the sequences `ℤ → Bool` all of whose windows
occur in `b` infinitely often. -/
def tailSubshift (b : ℕ → Bool) : Set (ℤ → Bool) :=
  {x | ∀ (m : ℤ) (n : ℕ), (fun j : Fin n => x (m + ((j : ℕ) : ℤ))) ∈ tailFactors b n}

theorem continuous_window (m : ℤ) (n : ℕ) :
    Continuous fun x : ℤ → Bool => fun j : Fin n => x (m + ((j : ℕ) : ℤ)) :=
  continuous_pi fun j => continuous_apply (m + ((j : ℕ) : ℤ))

/-- **Every word that occurs in `b` infinitely often is a window of a point of the subshift.** The
point is a cluster point, in the compact space `ℤ → Bool`, of the shifts of `b` that put an
occurrence of the word at `0`. -/
theorem exists_mem_tailSubshift {b : ℕ → Bool} {n : ℕ} {w : Fin n → Bool}
    (hw : w ∈ tailFactors b n) : ∃ x ∈ tailSubshift b, ∀ j : Fin n, x ((j : ℕ) : ℤ) = w j := by
  have hocc : ∀ k : ℕ, ∃ i, k ≤ i ∧ (fun j : Fin n => b (i + j)) = w :=
    fun k => Filter.frequently_atTop.1 hw k
  choose i hik hiw using hocc
  -- the shift of `b` that puts the `k`-th chosen occurrence at `0`, padded with white
  let y : ℕ → ℤ → Bool := fun k m =>
    if 0 ≤ (i k : ℤ) + m then b ((i k : ℤ) + m).toNat else false
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_clusterPt (f := Filter.map y Filter.atTop)
    (Filter.le_principal_iff.2 Filter.univ_mem)
  -- every window of `x` is the same window of `y k` for frequently many `k`
  have key : ∀ (m : ℤ) (L : ℕ), ∃ᶠ k in Filter.atTop,
      (fun j : Fin L => y k (m + ((j : ℕ) : ℤ))) = fun j : Fin L => x (m + ((j : ℕ) : ℤ)) := by
    intro m L
    have hopen : IsOpen ((fun z : ℤ → Bool => fun j : Fin L => z (m + ((j : ℕ) : ℤ))) ⁻¹'
        {fun j : Fin L => x (m + ((j : ℕ) : ℤ))}) :=
      (isOpen_discrete _).preimage (continuous_window m L)
    exact mapClusterPt_iff_frequently.1 hx _ (hopen.mem_nhds rfl)
  refine ⟨x, fun m L => ?_, fun j => ?_⟩
  · show ∃ᶠ p in Filter.atTop,
      (fun j : Fin L => b (p + j)) = fun j : Fin L => x (m + ((j : ℕ) : ℤ))
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨k, hk, hkw⟩ := Filter.frequently_atTop.1 (key m L) (N + (-m).toNat)
    have hi := hik k
    refine ⟨((i k : ℤ) + m).toNat, by omega, ?_⟩
    rw [← hkw]
    funext j
    show b (((i k : ℤ) + m).toNat + j) =
      if 0 ≤ (i k : ℤ) + (m + ((j : ℕ) : ℤ)) then b ((i k : ℤ) + (m + ((j : ℕ) : ℤ))).toNat
      else false
    rw [ite_eq_left (by omega)]
    congr 1
    omega
  · obtain ⟨k, hkw⟩ := (key 0 n).exists
    have h1 : y k (0 + ((j : ℕ) : ℤ)) = x (0 + ((j : ℕ) : ℤ)) := congrFun hkw j
    have h2 : b (i k + j) = w j := congrFun (hiw k) j
    rw [Int.zero_add] at h1
    rw [← h1, ← h2]
    show (if 0 ≤ (i k : ℤ) + ((j : ℕ) : ℤ) then b ((i k : ℤ) + ((j : ℕ) : ℤ)).toNat else false) =
      b (i k + j)
    rw [ite_eq_left (by omega)]
    congr 1

/-- A sequence `ℤ → Bool` with period `P` repeats after every multiple of `P`. -/
theorem int_periodic {x : ℤ → Bool} {P : ℤ} (h : ∀ m, x (m + P) = x m) (q : ℤ) :
    ∀ m, x (P * q + m) = x m := by
  refine Int.induction_on q (fun m => by simp) (fun i ih m => ?_) (fun i ih m => ?_)
  · rw [show P * ((i : ℤ) + 1) + m = (P * i + m) + P by ring, h, ih]
  · rw [← h (P * (-(i : ℤ) - 1) + m),
      show P * (-(i : ℤ) - 1) + m + P = P * (-(i : ℤ)) + m by ring, ih]

/-- **The subshift of the tail language is infinite iff `b` is not eventually periodic.** -/
theorem infinite_tailSubshift_iff (b : ℕ → Bool) :
    (tailSubshift b).Infinite ↔ ¬ EventuallyPeriodic b := by
  constructor
  · rintro hinf ⟨T, P, hP, hper⟩
    apply hinf
    -- every point of the subshift has period `P`
    have hpx : ∀ x ∈ tailSubshift b, ∀ m : ℤ, x (m + (P : ℤ)) = x m := by
      intro x hx m
      obtain ⟨i, hi, hiw⟩ := Filter.frequently_atTop.1 (hx m (P + 1)) T
      have e0 : b i = x m := by simpa using congrFun hiw ⟨0, by omega⟩
      have eP : b (i + P) = x (m + (P : ℤ)) := by simpa using congrFun hiw ⟨P, by omega⟩
      rw [← eP, hper i hi, e0]
    -- so it is determined by its cells at `0, …, P - 1`
    refine Set.Finite.of_injOn (f := fun x : ℤ → Bool => fun j : Fin P => x ((j : ℕ) : ℤ))
      (t := Set.univ) (Set.mapsTo_univ _ _) ?_ Set.finite_univ
    intro x hx x' hx' hxx'
    funext m
    have hPpos : (0 : ℤ) < P := by omega
    have hr0 := Int.emod_nonneg m (ne_of_gt hPpos)
    have hrP := Int.emod_lt_of_pos m hPpos
    have e := congrFun hxx' ⟨(m % (P : ℤ)).toNat, by omega⟩
    simp only at e
    rw [show (((m % (P : ℤ)).toNat : ℕ) : ℤ) = m % (P : ℤ) by omega] at e
    rw [← Int.mul_ediv_add_emod m (P : ℤ), int_periodic (hpx x hx) (m / (P : ℤ)),
      int_periodic (hpx x' hx') (m / (P : ℤ))]
    exact e
  · intro hne hfin
    rw [eventuallyPeriodic_iff_exists_ncard_tailFactors_le] at hne
    push Not at hne
    obtain ⟨K, hK⟩ : ∃ K, (tailSubshift b).ncard = K := ⟨_, rfl⟩
    have hlt := hne K
    classical
    -- extend each word of length `K` of the tail language to a point of the subshift
    let f : (Fin K → Bool) → (ℤ → Bool) := fun w =>
      if h : w ∈ tailFactors b K then Classical.choose (exists_mem_tailSubshift h)
      else fun _ => false
    have hf : ∀ w (h : w ∈ tailFactors b K),
        f w ∈ tailSubshift b ∧ ∀ j : Fin K, f w ((j : ℕ) : ℤ) = w j := by
      intro w h
      have := Classical.choose_spec (exists_mem_tailSubshift h)
      simp only [f, dite_eq_left h]
      exact this
    have hinj : Set.InjOn f (tailFactors b K) := by
      intro w hw w' hw' hww'
      funext j
      rw [← (hf w hw).2 j, ← (hf w' hw').2 j, hww']
    have hle := Set.ncard_le_ncard_of_injOn f (fun w hw => (hf w hw).1) hinj hfin
    omega

/-- **Problem 1 ⟺ the subshift of the tail language of the center column is infinite**. -/
theorem problem1_iff_tailSubshift_infinite :
    Rule30Prize.Problem1 ↔ (tailSubshift c).Infinite := by
  rw [infinite_tailSubshift_iff]
  exact problem1_iff_not_eventuallyPeriodic

end Rule30Equivalents.TailLanguage
