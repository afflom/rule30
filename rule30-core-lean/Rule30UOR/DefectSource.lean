module

public import Rule30UOR.TemporalDefect
public import Rule30UOR.Collision

/-!
# The temporal defect is a Rule 30 history with collision sources

`TemporalDefect.defect Q t p = cell (t+Q) p XOR cell t p` compares two time-shifted rows of the
single-seed orbit. `Collision.collision Q t p` is the adjacent determinant of those two rows.
This file proves the exact law connecting them:

  `defect Q (t+1) p = rule (defect Q t (p-1)) (defect Q t p) (defect Q t (p+1)) XOR collision Q t p`.

So the defect field is an ordinary Rule 30 history except at collision sites, which act as
sources. Nothing is linearized and no periodicity is assumed.

It also records an audit result. Under center agreement at two consecutive times, the defect
column `-2` is the first difference of column `-1` (`defect_neg_two_of_agree`). But this
identity carries no information beyond the center: the unconditional identity
`left_triple_eq_center_pair` shows that the corresponding single-column quantity equals
`center t && center (t+1)`. Constraints that go beyond the center must come from deeper
columns or from the global edge data, not from the center-adjacent layer.
-/

@[expose] public section

namespace Rule30UOR.DefectSource

open Ruliology.CellularAutomata Rule30Jen Rule30Prize
open Rule30UOR.TemporalDefect Rule30UOR.Collision

/-- The adjacent determinant written with the earlier row and the defect. -/
theorem collision_eq_defect (Q t : Nat) (p : Int) :
    collision Q t p =
      xor (cell t p && defect Q t (p + 1)) (cell t (p + 1) && defect Q t p) := by
  simp only [collision, defect, difference]
  cases cell t p <;> cases cell t (p + 1) <;> cases cell (t + Q) p <;>
    cases cell (t + Q) (p + 1) <;> rfl

/-- **Source law.** The temporal defect evolves by Rule 30 itself, with the collision as an
additive source. Exact, with every nonlinear term retained. -/
theorem defect_source_law (Q t : Nat) (p : Int) :
    defect Q (t + 1) p =
      xor (rule (defect Q t (p - 1)) (defect Q t p) (defect Q t (p + 1))) (collision Q t p) := by
  rw [defect_step, collision_eq_defect]
  unfold rule
  cases defect Q t (p - 1) <;> cases defect Q t p <;> cases defect Q t (p + 1) <;>
    cases cell t p <;> cases cell t (p + 1) <;> rfl

/-- Away from collisions the defect is an exact Rule 30 history. -/
theorem defect_rule_of_no_collision (Q t : Nat) (p : Int) (h : collision Q t p = false) :
    defect Q (t + 1) p = rule (defect Q t (p - 1)) (defect Q t p) (defect Q t (p + 1)) := by
  rw [defect_source_law, h, Bool.xor_false]

/-- With the center in agreement at time `t`, the center collision is `center t && defect Q t 1`. -/
theorem collision_center_of_agree (Q t : Nat) (h0 : defect Q t 0 = false) :
    collision Q t 0 = (center t && defect Q t 1) := by
  rw [collision_eq_defect]
  simp only [show (0 : Int) + 1 = 1 by omega, h0, Bool.and_false, Bool.xor_false]
  rfl

/-- With the center in agreement at times `t` and `t + 1`, there is no collision at column `-1`. -/
theorem collision_neg_one_of_agree (Q t : Nat)
    (h0 : defect Q t 0 = false) (h1 : defect Q (t + 1) 0 = false) :
    collision Q t (-1) = false := by
  have hm := neighbor_matching Q t 0 h0 h1
  rw [show (0 : Int) - 1 = -1 by omega, show (0 : Int) + 1 = 1 by omega] at hm
  rw [collision_eq_defect]
  simp only [show (-1 : Int) + 1 = 0 by omega, h0, Bool.and_false, Bool.false_xor]
  rw [hm]
  cases cell t 0 <;> simp

/-- With the center in agreement at times `t` and `t + 1`, defect column `-2` is the first
difference of defect column `-1`. -/
theorem defect_neg_two_of_agree (Q t : Nat)
    (h0 : defect Q t 0 = false) (h1 : defect Q (t + 1) 0 = false) :
    defect Q t (-2) = xor (defect Q (t + 1) (-1)) (defect Q t (-1)) := by
  have hs := defect_source_law Q t (-1)
  rw [collision_neg_one_of_agree Q t h0 h1, show (-1 : Int) - 1 = -2 by omega,
    show (-1 : Int) + 1 = 0 by omega, h0] at hs
  rw [hs]
  unfold rule
  cases defect Q t (-2) <;> cases defect Q t (-1) <;> rfl

/-- Unconditional single-column form of the left layer: it is `center t && !cell t (-1)`. -/
theorem left_triple_eq (t : Nat) :
    xor (xor (cell t (-2)) (cell (t + 1) (-1))) (cell t (-1)) =
      (center t && !cell t (-1)) := by
  have hstep : cell (t + 1) (-1) = rule (cell t (-2)) (cell t (-1)) (cell t 0) := rfl
  rw [hstep]
  unfold rule center
  cases cell t (-2) <;> cases cell t (-1) <;> cases cell t 0 <;> rfl

/-- **Audit.** The left layer carries only `center t && center (t+1)`: the identity
`defect_neg_two_of_agree` adds no constraint beyond the center column itself. -/
theorem left_triple_eq_center_pair (t : Nat) :
    xor (xor (cell t (-2)) (cell (t + 1) (-1))) (cell t (-1)) =
      (center t && center (t + 1)) := by
  rw [left_triple_eq]
  cases h : center t
  · rfl
  · have hb := Rule30MaskedJen.left_of_black t 0 h
    rw [show (0 : Int) - 1 = -1 by omega] at hb
    rw [hb]
    unfold center
    cases cell (t + 1) 0 <;> rfl

end Rule30UOR.DefectSource
