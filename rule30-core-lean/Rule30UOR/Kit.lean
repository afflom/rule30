module

public import Rule30UOR.Core
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# The LexLean left system and the kit's diagonals (Lean 4.32.1 host for the paper)

`ldiag_eq_D`: the closed left system of the LexLean core is the kit's left-diagonal array.
`ldiag_periodic`: every left diagonal is eventually periodic, with period a power of two. Read as
digits, this is the 2-adic continuity of the leading part of the rows: digit `j` from the top of
row `t` depends only on `t` modulo `2^j` once `t` is large.
-/

@[expose] public section

namespace Rule30UOR.Kit

open Ruliology.CellularAutomata

theorem ldiag_eq_D : ∀ t j, Rule30UOR.Core.ldiag j t = Rule30Diagonals.D j t := by
  intro t
  induction t with
  | zero =>
    intro j
    rcases j with _ | j
    · rfl
    · show false = Rule30Jen.cell 0 (((j + 1 : Nat) : Int) - ((0 : Nat) : Int))
      simp only [Rule30Jen.cell]; exact (decide_eq_false (by omega)).symm
  | succ t ih =>
    intro j
    rcases j with _ | _ | k
    · exact (Rule30Diagonals.D_zero (t + 1)).symm
    · exact (Rule30Diagonals.D_one t).symm
    · rw [Rule30UOR.Core.ldiag_step, ih k, ih (k + 1), ih (k + 2), Rule30Diagonals.D_step]
      simp only [Rule30UOR.Core.bxor]; cases Rule30Diagonals.D k t <;> simp

/-- Every left diagonal is eventually periodic with period `2^j`. -/
theorem ldiag_periodic (j : Nat) :
    ∃ T, ∀ t, T ≤ t → Rule30UOR.Core.ldiag j (t + 2 ^ j) = Rule30UOR.Core.ldiag j t := by
  obtain ⟨T, hT⟩ := Rule30Diagonals.D_periodic j
  exact ⟨T, fun t ht => by rw [ldiag_eq_D, ldiag_eq_D]; exact hT t ht⟩

end Rule30UOR.Kit

namespace Rule30UOR.Kit

/-- The same, with the period as a witness. -/
theorem ldiag_eventually_periodic (j : Nat) :
    ∃ P, 0 < P ∧ ∃ T, ∀ t, T ≤ t → Rule30UOR.Core.ldiag j (t + P) = Rule30UOR.Core.ldiag j t := by
  obtain ⟨T, hT⟩ := ldiag_periodic j
  exact ⟨2 ^ j, Nat.two_pow_pos j, T, hT⟩

end Rule30UOR.Kit
