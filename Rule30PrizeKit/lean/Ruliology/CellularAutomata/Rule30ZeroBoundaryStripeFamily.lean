module

public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles0
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles1
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles2

/-!
# The stripe-prefix family `S[1..m] · v · 0^∞`, `|v| ≤ 3`: death within `31` steps of arrival

For every `m` and every word `v = b₀ b₁ b₂` (a shorter word is the same row padded with white), the
start `row3 m b₀ b₁ b₂` (the stripe at depths `1, …, m`, then `v`, then white) has its first
deviation from the stripe at some depth `d ≤ m + 5`, and depth `1` is white at some even time
`≤ d - 1 + 31`. The proof is `family_of_class` (front window, `Rule30ZeroBoundaryStripeFront`) with
one of eight kernel-checked periodic window orbits per class `(m mod 2, v)`
(`Rule30Certificates.ZeroBoundaryStripeCycles0` – `ZeroBoundaryStripeCycles2`). The theorems live
in the namespace `Rule30ZeroBoundaryStripeFront`.

* `stripe_prefix_family`: the word given as three Booleans.
* `stripe_prefix_family_list`: the word given as a list `v` with `|v| ≤ 3` (`rowV`).

Only tails `|v| ≤ 3` are kernel-checked; the bound `31` after arrival is attained (computation).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeFront

open Rule30ZeroBoundaryStripeFront.StripeCycles0
open Rule30ZeroBoundaryStripeFront.StripeCycles1
open Rule30ZeroBoundaryStripeFront.StripeCycles2
open Rule30ZeroBoundary

theorem cycle_congr {K S W0 W0' p0 p0' lam : Nat} (h1 : W0 = W0') (h2 : p0 = p0')
    (h : Cycle K S W0' p0' lam) : Cycle K S W0 p0 lam := by subst h1 h2; exact h

/-- **The stripe-prefix family dies.** For every `m` and `b₀ b₁ b₂`, the first deviation `d` of
`S[1..m] · b₀ b₁ b₂ · 0^∞` from the stripe satisfies `d ≤ m + 5`, and depth `1` is white at some even
time `t ≤ d - 1 + 31`. -/
theorem stripe_prefix_family (m : Nat) (b0 b1 b2 : Bool) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 5 ∧ (∀ k, 1 ≤ k → k < d → row3 m b0 b1 b2 k = stripe k) ∧
      row3 m b0 b1 b2 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row3 m b0 b1 b2) t 1 = false := by
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;> cases b0 <;> cases b1 <;> cases b2
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 1 4096 false false false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_0_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 1 65536 false false true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_4_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 1 16384 false true false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_2_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 1 4096 false true true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_6_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 3 4096 true false false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_0_1)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 5 4096 true false true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_0_1)
    exact ⟨m + 5, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 2 4096 true true false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_1_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 0 2 16384 true true true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_3_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 2 4096 false false false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_0_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 2 16384 false false true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_2_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 4 4096 false true false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_0_1)
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 3 4096 false true true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_1_0)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 1 4096 true false false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_1_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 1 65536 true false true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_5_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 1 16384 true true false hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_3_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family_of_class m 1 1 16384 true true true hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_7_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩

/-- The same for a word given as a list of length `≤ 3`. -/
def rowV (m : Nat) (v : List Bool) (k : Nat) : Bool := if k ≤ m then stripe k else v.getD (k - m - 1) false

theorem rowV_eq (m : Nat) (v : List Bool) (hv : v.length ≤ 3) :
    rowV m v = row3 m (v.getD 0 false) (v.getD 1 false) (v.getD 2 false) := by
  funext k
  unfold rowV row3 vget
  by_cases hk : k ≤ m
  · simp [hk]
  · simp only [hk, ite_false]
    rcases (show k - m - 1 = 0 ∨ k - m - 1 = 1 ∨ k - m - 1 = 2 ∨ 3 ≤ k - m - 1 by omega) with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl

/-- **Stripe-prefix family, list form.** For every `m` and every word `v` with `|v| ≤ 3`, the start
`S[1..m] · v · 0^∞` deviates from the stripe first at some depth `d ≤ m + 5` and has a white cell
at depth `1` at some even time `≤ d - 1 + 31`. -/
theorem stripe_prefix_family_list (m : Nat) (v : List Bool) (hv : v.length ≤ 3) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 5 ∧ (∀ k, 1 ≤ k → k < d → rowV m v k = stripe k) ∧ rowV m v d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (rowV m v) t 1 = false := by
  rw [rowV_eq m v hv]
  exact stripe_prefix_family m _ _ _

end Rule30ZeroBoundaryStripeFront
end Ruliology.CellularAutomata
