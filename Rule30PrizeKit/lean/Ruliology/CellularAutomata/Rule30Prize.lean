module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# The Rule 30 Prize problems: statements, and the constant case of Problem 1

Wolfram, *Announcing the Rule 30 Prizes* (2019):
<https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/>

    Problem 1: Does the center column always remain non-periodic?
    Problem 2: Does each color of cell occur on average equally often in the center column?
    Problem 3: Does computing the nth cell of the center column require at least O(n)
               computational effort?

All three are open.

* `Problem1`, `Problem2`: the first two problems as statements about `cell` from `Rule30Jen`.
  They match `Rule30.centerColumn_not_eventually_periodic` and
  `Rule30.centerColumn_frequency_half` in google-deepmind/formal-conjectures
  (`FormalConjectures/Other/Rule30.lean`), whose `state t i` is `cell t i`. Problem 3 needs a
  model of computation and is not stated here.
* `no_column_eventually_constant`: **no column is eventually constant**. This settles the period-1
  case of Problem 1, for every column and every transient. If a column is eventually black, the
  column to its left is eventually white. If it is eventually white, the column to its right can
  only turn from white to black, so it is eventually constant. Either way two adjacent columns are
  eventually periodic, which Jen's theorem (`Rule30Jen.not_adjacent`) rules out.
* `center_not_eventually_constant`: the center column in particular.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Prize

open Rule30Jen

/-- The center column: the color of the cell at position `0` at time `t`. -/
def center (t : Nat) : Bool := cell t 0

/-- **Problem 1**: the center column is not eventually periodic. -/
def Problem1 : Prop := ¬ EventuallyPeriodic center

/-- The number of black cells among `center 0, …, center (n - 1)`. -/
def blackCount (n : Nat) : Nat := ((List.range n).filter center).length

/-- **Problem 2**: black cells have density `1/2` in the center column, stated with integers:
for every `k > 0`, eventually `k · |2 · blackCount n − n| ≤ n`. -/
def Problem2 : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCount n : Int) - n).natAbs ≤ n

/-- An eventually constant sequence is eventually periodic. -/
theorem eventuallyPeriodic_of_const {f : Nat → Bool} {T : Nat} {b : Bool}
    (h : ∀ t, T ≤ t → f t = b) : EventuallyPeriodic f :=
  ⟨T, 1, Nat.one_pos, fun t ht => (h (t + 1) (by omega)).trans (h t ht).symm⟩

/-- A sequence that can only turn from white to black is eventually constant. -/
theorem eventually_const_of_mono {f : Nat → Bool} {T : Nat}
    (h : ∀ t, T ≤ t → f t = true → f (t + 1) = true) : ∃ T' b, ∀ t, T' ≤ t → f t = b := by
  by_cases hx : ∃ t, T ≤ t ∧ f t = true
  · obtain ⟨t₀, ht₀, hf⟩ := hx
    have hk : ∀ k, f (t₀ + k) = true := by
      intro k
      induction k with
      | zero => exact hf
      | succ k ih => exact h (t₀ + k) (by omega) ih
    refine ⟨t₀, true, fun t ht => ?_⟩
    have := hk (t - t₀)
    rwa [show t₀ + (t - t₀) = t by omega] at this
  · refine ⟨T, false, fun t ht => ?_⟩
    cases hft : f t
    · rfl
    · exact absurd ⟨t, ht, hft⟩ hx

/-- **No column of rule 30 is eventually constant.** -/
theorem no_column_eventually_constant (i : Int) : ¬ ∃ T b, ∀ t, T ≤ t → cell t i = b := by
  rintro ⟨T, b, h⟩
  cases b
  · -- column `i` is eventually white: column `i + 1` can only turn black
    have hmono : ∀ t, T ≤ t → cell t (i + 1) = true → cell (t + 1) (i + 1) = true := by
      intro t ht h1
      show rule (cell t (i + 1 - 1)) (cell t (i + 1)) (cell t (i + 1 + 1)) = true
      rw [show i + 1 - 1 = i by omega, h t ht, h1]
      rfl
    obtain ⟨T', b', h'⟩ := eventually_const_of_mono hmono
    exact not_adjacent i (eventuallyPeriodic_of_const h) (eventuallyPeriodic_of_const h')
  · -- column `i` is eventually black: column `i - 1` is eventually white
    have hleft : ∀ t, T ≤ t → cell t (i - 1) = false := by
      intro t ht
      have e := h (t + 1) (by omega)
      have hc : cell (t + 1) i = rule (cell t (i - 1)) (cell t i) (cell t (i + 1)) := rfl
      rw [hc, h t ht] at e
      revert e
      cases cell t (i - 1) <;> simp [rule]
    refine not_adjacent (i - 1) (eventuallyPeriodic_of_const hleft) ?_
    rw [show i - 1 + 1 = i by omega]
    exact eventuallyPeriodic_of_const h

/-- **The center column is not eventually constant**: Problem 1 for period `1`. -/
theorem center_not_eventually_constant : ¬ ∃ T b, ∀ t, T ≤ t → center t = b :=
  no_column_eventually_constant 0

/-- The same, in the shape of Problem 1: no transient `N` after which the center column has
period `1`. -/
theorem center_not_eventually_period_one : ¬ ∃ N, ∀ t, N ≤ t → center (t + 1) = center t := by
  rintro ⟨N, h⟩
  have hk : ∀ k, center (N + k) = center N := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, h (N + k) (by omega), ih]
  refine center_not_eventually_constant ⟨N, center N, fun t ht => ?_⟩
  have := hk (t - N)
  rwa [show N + (t - N) = t by omega] at this

end Rule30Prize
end Ruliology.CellularAutomata
