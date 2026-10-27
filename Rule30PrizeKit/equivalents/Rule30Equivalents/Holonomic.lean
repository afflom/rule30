module

public import Rule30Equivalents.LinearRelations
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Field
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
# Problem 1 ⟺ the center column is not P-recursive

A sequence is *P-recursive* (holonomic) when it satisfies, from some point on, a linear recurrence
whose coefficients are polynomials in the index, not all zero:
`∑_{i ≤ d} p_i(n) · b(n + i) = 0` for `n ≥ N`.

* `eventuallyPeriodic_iff_pRecursive`: a `Bool` sequence is P-recursive iff it is eventually
  periodic.
* `problem1_iff_not_pRecursive`: Problem 1 holds iff the center column is not
  P-recursive.

**Proof.** An eventual period gives the recurrence `b(n + P) - b(n) = 0`. Conversely
(`exists_const_relation`), let `D` be the largest degree of a nonzero `p_i` and `q_i` the
coefficient of `n^D` in `p_i`. Past some point every window `(b(n), …, b(n + d))` occurs
infinitely often (`eventually_recurrent`, as there are finitely many windows). For a window `a`
that occurs infinitely often, the integer polynomial `∑ a_i p_i` has infinitely many roots, so it
is `0`, and in particular `∑ q_i a_i = 0`. So `∑ q_i b(n + i) = 0` from that point on: a
recurrence with constant coefficients, not all zero, which `LinearRelations` turns into eventual
periodicity (`eventuallyPeriodic_of_const_relation`).

This is the elementary half of the classical picture: a P-recursive sequence with finitely many
values has a rational generating function (van der Poorten and Shparlinski 1996), and P-recursive
is equivalent to D-finite (Stanley 1980), so Problem 1 also says that `∑ c(t) Xᵗ` is not D-finite.
The D-finite form is proved in `DFinite`.

Sources: A. J. van der Poorten and I. E. Shparlinski, *On linear recurrence sequences with
polynomial coefficients*, Glasgow Math. J. 38 (1996) 147–155; R. P. Stanley, *Differentiably
finite power series*, European J. Combin. 1 (1980) 175–188.
-/

@[expose] public section

namespace Rule30Equivalents.Holonomic

open Ruliology.CellularAutomata Polynomial

/-- `b` read as integers. -/
def z (b : ℕ → Bool) (n : ℕ) : ℤ := if b n then 1 else 0

/-- `b` satisfies, from `N` on, a recurrence with polynomial coefficients that are not all zero. -/
def PRecursive (b : ℕ → Bool) : Prop :=
  ∃ (d N : ℕ) (p : Fin (d + 1) → ℤ[X]), (∃ i, p i ≠ 0) ∧
    ∀ n, N ≤ n → ∑ i : Fin (d + 1), (p i).eval (n : ℤ) * (if b (n + i) then 1 else 0) = 0

/-! ### Eventually periodic ⟹ P-recursive -/

theorem pRecursive_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    PRecursive b := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨P, T, fun i => if (i : ℕ) = 0 then C (-1) else if (i : ℕ) = P then C 1 else 0,
    ⟨Fin.last P, by simp [hP.ne']⟩, fun n hn => ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i => (if i = 0 then C (-1) else if i = P then C 1 else 0 :
    ℤ[X]).eval (n : ℤ) * (if b (n + i) then 1 else 0)) (P + 1), Finset.sum_range_succ,
    Finset.sum_eq_single 0 (fun i hi h0 => by
      rw [Finset.mem_range] at hi
      simp [h0, show i ≠ P by omega]) (fun h => absurd (Finset.mem_range.2 hP) h)]
  simp only [ite_eq_right hP.ne', Nat.add_zero]
  rw [hper n hn]
  cases b n <;> simp

/-! ### Constant coefficients ⟹ eventually periodic -/

theorem eventuallyPeriodic_of_const_relation {b : ℕ → Bool} {d N : ℕ} (q : ℕ → ℤ)
    (hq : ∃ i ≤ d, q i ≠ 0)
    (h : ∀ n, N ≤ n → ∑ i ∈ Finset.range (d + 1), q i * z b (n + i) = 0) :
    EventuallyPeriodic b := by
  classical
  let S := (Finset.range (d + 1)).filter fun i => q i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hqi⟩ := hq
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hqi⟩⟩
  let j := S.max' hS
  have hjS : j ∈ S := S.max'_mem hS
  have hjd : j ≤ d := by have := (Finset.mem_filter.1 hjS).1; rw [Finset.mem_range] at this; omega
  have hqj : q j ≠ 0 := (Finset.mem_filter.1 hjS).2
  have hzero : ∀ i, j < i → i ≤ d → q i = 0 := by
    intro i hji hid
    by_contra hne
    have : i ≤ j := S.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hne⟩)
    omega
  -- the relation, solved for the top term
  have hsolve : ∀ n, N ≤ n →
      q j * z b (n + j) = -∑ i ∈ Finset.range j, q i * z b (n + i) := by
    intro n hn
    have e := h n hn
    rw [← Finset.sum_range_add_sum_Ico _ (show j + 1 ≤ d + 1 by omega),
      Finset.sum_eq_zero (s := Finset.Ico (j + 1) (d + 1)) (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [hzero i (by omega) (by omega), zero_mul]),
      Finset.sum_range_succ] at e
    linarith
  refine (LinearRelations.eventuallyPeriodic_iff_exists_eventually_isSolution (K := ℚ) b).2
    ⟨⟨j, fun i => -(q i : ℚ) / q j⟩, Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩⟩
  have hqj' : (q j : ℚ) ≠ 0 := by exact_mod_cast hqj
  have hz : ∀ m, LinearRelations.toK ℚ b m = (z b m : ℚ) := fun m => by
    unfold LinearRelations.toK z; split_ifs <;> simp
  show LinearRelations.toK ℚ b (n + j) = ∑ i : Fin j, -(q i : ℚ) / q j * LinearRelations.toK ℚ b (n + i)
  rw [Fin.sum_univ_eq_sum_range (fun i => -(q i : ℚ) / q j * LinearRelations.toK ℚ b (n + i)) j]
  simp only [hz]
  have e : (q j : ℚ) * (z b (n + j) : ℚ) = -∑ i ∈ Finset.range j, (q i : ℚ) * (z b (n + i) : ℚ) := by
    exact_mod_cast hsolve n hn
  have hsum : ∑ i ∈ Finset.range j, -(q i : ℚ) / q j * (z b (n + i) : ℚ) =
      (-∑ i ∈ Finset.range j, (q i : ℚ) * (z b (n + i) : ℚ)) / q j := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, ← e]
  field_simp

/-! ### P-recursive ⟹ constant coefficients -/

/-- Past some point, every value of a sequence in a finite type occurs again later. -/
theorem eventually_recurrent {α : Type*} [Finite α] (W : ℕ → α) (N : ℕ) :
    ∃ N', N ≤ N' ∧ ∀ n, N' ≤ n → ∀ M, ∃ m, M ≤ m ∧ W m = W n := by
  classical
  have : ∀ a : α, ∃ B : ℕ, (∀ M, ∃ m, M ≤ m ∧ W m = a) ∨ (∀ m, B ≤ m → W m ≠ a) := by
    intro a
    by_cases h : ∀ M, ∃ m, M ≤ m ∧ W m = a
    · exact ⟨0, Or.inl h⟩
    · push Not at h
      obtain ⟨B, hB⟩ := h
      exact ⟨B, Or.inr hB⟩
  choose B hB using this
  have := Fintype.ofFinite α
  refine ⟨N + Finset.univ.sup B, by omega, fun n hn M => ?_⟩
  rcases hB (W n) with h | h
  · exact h M
  · exact absurd rfl (h n (le_trans (Finset.le_sup (Finset.mem_univ (W n))) (by omega)))

theorem exists_const_relation {b : ℕ → Bool} (h : PRecursive b) :
    ∃ (d N : ℕ) (q : ℕ → ℤ), (∃ i ≤ d, q i ≠ 0) ∧
      ∀ n, N ≤ n → ∑ i ∈ Finset.range (d + 1), q i * z b (n + i) = 0 := by
  classical
  obtain ⟨d, N, p, ⟨i0, hi0⟩, hrel⟩ := h
  let S := Finset.univ.filter fun i => p i ≠ 0
  have hS : S.Nonempty := ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0⟩⟩
  obtain ⟨i1, hi1S, hi1D⟩ := Finset.exists_mem_eq_sup' hS fun i => (p i).natDegree
  set D := S.sup' hS fun i => (p i).natDegree
  let q : ℕ → ℤ := fun n => if hn : n < d + 1 then (p ⟨n, hn⟩).coeff D else 0
  have hq1 : q i1 ≠ 0 := by
    simp only [q, dite_eq_left i1.isLt]
    rw [hi1D, ← Polynomial.leadingCoeff]
    exact leadingCoeff_ne_zero.2 (Finset.mem_filter.1 hi1S).2
  let W : ℕ → (Fin (d + 1) → Bool) := fun n i => b (n + i)
  obtain ⟨N', hNN', hrec⟩ := eventually_recurrent W N
  refine ⟨d, N', q, ⟨i1, by omega, hq1⟩, fun n hn => ?_⟩
  -- the polynomial of the window at `n` vanishes at every later occurrence of the window
  let Pa : ℤ[X] := ∑ i : Fin (d + 1), p i * C (if b (n + i) then 1 else 0)
  have hroot : ∀ m, N ≤ m → W m = W n → Pa.IsRoot (m : ℤ) := by
    intro m hm hW
    simp only [IsRoot, Pa, eval_finsetSum, eval_mul, eval_C]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (hrel m hm)
    rw [show b (n + i) = b (m + i) from (congrFun hW i).symm]
  have hinf : Set.Infinite {x : ℤ | Pa.IsRoot x} := by
    refine Set.infinite_of_not_bddAbove fun ⟨a, ha⟩ => ?_
    obtain ⟨m, hm, hWm⟩ := hrec n hn (max N (a.toNat + 1))
    have := ha (hroot m (le_trans (le_max_left _ _) hm) hWm)
    omega
  have hPa := Polynomial.eq_zero_of_infinite_isRoot Pa hinf
  have hcoeff := congrArg (fun P : ℤ[X] => P.coeff D) hPa
  simp only [Pa, finsetSum_coeff, coeff_mul_C, coeff_zero] at hcoeff
  rw [← hcoeff, ← Fin.sum_univ_eq_sum_range (fun i => q i * z b (n + i)) (d + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [q, dite_eq_left i.isLt, z]

/-! ### The equivalence -/

/-- **A `Bool` sequence is P-recursive iff it is eventually periodic.** -/
theorem eventuallyPeriodic_iff_pRecursive (b : ℕ → Bool) : EventuallyPeriodic b ↔ PRecursive b := by
  refine ⟨pRecursive_of_eventuallyPeriodic, fun h => ?_⟩
  obtain ⟨d, N, q, hq, hrel⟩ := exists_const_relation h
  exact eventuallyPeriodic_of_const_relation q hq hrel

/-- **Problem 1 ⟺ the center column satisfies no recurrence with polynomial coefficients**. -/
theorem problem1_iff_not_pRecursive : Rule30Prize.Problem1 ↔
    ¬ ∃ (d N : ℕ) (p : Fin (d + 1) → Polynomial ℤ), (∃ i, p i ≠ 0) ∧
      ∀ n, N ≤ n → ∑ i : Fin (d + 1),
        (p i).eval (n : ℤ) * (if Rule30Prize.center (n + i) then 1 else 0) = 0 :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_pRecursive c))

end Rule30Equivalents.Holonomic
