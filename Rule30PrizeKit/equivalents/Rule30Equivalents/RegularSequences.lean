module

public import Rule30Equivalents.Cobham
public import Rule30Equivalents.LinearRelations
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# k-regular sequences

In the vocabulary of Allouche and Shallit (1992), a sequence is `k`-regular
over a field `K` if the `K`-span of its `k`-kernel `{n ↦ f(kᵉ n + r) : r < kᵉ}` is
finite-dimensional (`IsRegularSeq`). Regular sequences generalize automatic ones to infinitely
many values; for a sequence with values in `{0, 1}` the two notions agree
(`isRegularSeq_iff_isAutomatic`).

* A finite-dimensional space of sequences is determined by finitely many coordinates
  (`exists_eq_zero_of_vanish`): the subspaces of vectors vanishing below `N` decrease with `N`, so
  their dimensions stabilize, and from then on the subspace is the intersection of all of them,
  which is `0`.
* So two kernel elements of a `k`-regular `f` that agree below `N` are equal: their difference
  lies in the span and vanishes below `N`. The kernel embeds into `{0, 1}^N` and is finite.

With Cobham's theorem, **Problem 1 holds iff the center column is not both `2`-regular and
`3`-regular**, over any field (`problem1_iff_not_regularSeq_two_three`).

Source: J.-P. Allouche and J. Shallit, *The ring of k-regular sequences*, Theoret. Comput. Sci. 98
(1992) 163–197, where `k`-regular sequences are defined over a ring, and a `k`-regular sequence
with finitely many values is shown to be `k`-automatic.
-/

@[expose] public section

namespace Rule30Equivalents.RegularSequences

open Ruliology.CellularAutomata Automatic LinearRelations Module

variable {K : Type*} [Field K]

/-- The vectors of `V` that vanish below `N`. -/
def vanishBelow (V : Submodule K (ℕ → K)) (N : ℕ) : Submodule K (ℕ → K) where
  carrier := {v | v ∈ V ∧ ∀ n < N, v n = 0}
  add_mem' := fun ha hb => ⟨V.add_mem ha.1 hb.1, fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
  zero_mem' := ⟨V.zero_mem, fun _ _ => rfl⟩
  smul_mem' := fun c _ hv => ⟨V.smul_mem c hv.1, fun n hn => by simp [hv.2 n hn]⟩

/-- **A finite-dimensional space of sequences is determined by finitely many coordinates.** -/
theorem exists_eq_zero_of_vanish (V : Submodule K (ℕ → K)) [FiniteDimensional K V] :
    ∃ N, ∀ v ∈ V, (∀ n < N, v n = 0) → v = 0 := by
  classical
  have : ∀ N, FiniteDimensional K (vanishBelow V N) := fun N =>
    Submodule.finiteDimensional_of_le fun _ hv => hv.1
  -- an `N` of least dimension
  have hex : ∃ m, ∃ N, finrank K (vanishBelow V N) = m := ⟨_, 0, rfl⟩
  obtain ⟨N, hNm⟩ := Nat.find_spec hex
  have hmin : ∀ M, finrank K (vanishBelow V N) ≤ finrank K (vanishBelow V M) := fun M => by
    rw [hNm]
    exact Nat.find_min' hex ⟨M, rfl⟩
  refine ⟨N, fun v hv h0 => funext fun m => ?_⟩
  have hle : vanishBelow V (max N (m + 1)) ≤ vanishBelow V N :=
    fun w hw => ⟨hw.1, fun n hn => hw.2 n (by omega)⟩
  have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _)
  have hvM : v ∈ vanishBelow V (max N (m + 1)) := by
    rw [heq]
    exact ⟨hv, h0⟩
  exact hvM.2 m (by omega)

/-- `f` is `k`-regular over `K` (Allouche–Shallit): the `K`-span of its `k`-kernel, read in `K`,
is finite-dimensional. -/
def IsRegularSeq (K : Type*) [Field K] (k : ℕ) (f : ℕ → Bool) : Prop :=
  FiniteDimensional K (Submodule.span K (toK K '' kernel k f))

/-- **A `0/1` sequence is `k`-regular iff it is `k`-automatic**, over any field. -/
theorem isRegularSeq_iff_isAutomatic (k : ℕ) (f : ℕ → Bool) :
    IsRegularSeq K k f ↔ IsAutomatic k f := by
  constructor
  · intro h
    have : FiniteDimensional K (Submodule.span K (toK K '' kernel k f)) := h
    obtain ⟨N, hN⟩ := exists_eq_zero_of_vanish (Submodule.span K (toK K '' kernel k f))
    -- the kernel embeds into `Fin N → Bool`
    have hinj : Function.Injective fun g : kernel k f => fun i : Fin N => g.1 i := by
      intro g g' hgg'
      have hsub : toK K g.1 - toK K g'.1 = 0 := hN _
        (Submodule.sub_mem _ (Submodule.subset_span ⟨g.1, g.2, rfl⟩)
          (Submodule.subset_span ⟨g'.1, g'.2, rfl⟩))
        (fun n hn => by
          have := congrFun hgg' ⟨n, hn⟩
          rw [Pi.sub_apply, sub_eq_zero, toK_eq_toK_iff]
          exact this)
      apply Subtype.ext
      funext n
      have := congrFun hsub n
      rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, toK_eq_toK_iff] at this
    exact Set.finite_coe_iff.1 (Finite.of_injective _ hinj)
  · intro h
    exact FiniteDimensional.span_of_finite K (h.image _)

/-- **Not `k`-regular.** If the center column is not `k`-regular over some field, for some
`k ≥ 2`, Problem 1 holds. -/
theorem problem1_of_not_regularSeq (K : Type*) [Field K] {k : ℕ} (hk : 2 ≤ k)
    (h : ¬ IsRegularSeq K k c) : Rule30Prize.Problem1 :=
  problem1_of_not_automatic hk ((isRegularSeq_iff_isAutomatic k c).not.1 h)

/-- **`k`-regular sequences.** Over any field, Problem 1 holds iff the center column is not both
`2`-regular and `3`-regular. -/
theorem problem1_iff_not_regularSeq_two_three (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ¬ (IsRegularSeq K 2 c ∧ IsRegularSeq K 3 c) := by
  rw [isRegularSeq_iff_isAutomatic, isRegularSeq_iff_isAutomatic]
  exact Cobham.problem1_iff_not_two_three_automatic

end Rule30Equivalents.RegularSequences
