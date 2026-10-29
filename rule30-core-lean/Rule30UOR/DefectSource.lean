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

/-- The exact difference of the two OR gates. This is where an incoming defect
can be flipped; it retains both backgrounds. -/
def gateDifference (Q t : Nat) (p : Int) : Bool :=
  xor (cell (t + Q) p || cell (t + Q) (p + 1)) (cell t p || cell t (p + 1))

def leftGateDifference (Q t k : Nat) : Bool := gateDifference Q t (-(k : Int))

/-- Gate codes 1..6 are X0, 0X, XX, Y0, 0Y, YY. They encode an OR-gate
mismatch, which may create or erase a defect depending on the incoming bit. -/
def gateCase : Bool → Bool → Bool → Bool → Nat
  | true, false, false, false => 1
  | false, false, true, false => 2
  | true, false, true, false => 3
  | false, true, false, false => 4
  | false, false, false, true => 5
  | false, true, false, true => 6
  | _, _, _, _ => 0

def gateCode (Q t k : Nat) : Nat :=
  gateCase (cell t (-(k : Int))) (cell (t + Q) (-(k : Int)))
    (cell t (-(k : Int) + 1)) (cell (t + Q) (-(k : Int) + 1))

def ErasureEvent (Q t k : Nat) : Prop :=
  leftDefect Q t (k + 1) = true ∧ leftDefect Q (t + 1) k = false ∧
    gateCode Q t k ≠ 0 ∧ collisionCode Q t k = 0 ∧
    (leftColour Q (t + 1) k = 0 ∨ leftColour Q (t + 1) k = 3)

theorem gate_code_nonzero (Q t k : Nat) :
    gateCode Q t k ≠ 0 ↔ leftGateDifference Q t k = true := by
  unfold gateCode leftGateDifference gateDifference
  cases cell t (-(k : Int)) <;> cases cell (t + Q) (-(k : Int)) <;>
    cases cell t (-(k : Int) + 1) <;> cases cell (t + Q) (-(k : Int) + 1) <;> decide

theorem gate_code_bound (Q t k : Nat) : gateCode Q t k ≤ 6 := by
  unfold gateCode
  cases cell t (-(k : Int)) <;> cases cell (t + Q) (-(k : Int)) <;>
    cases cell t (-(k : Int) + 1) <;> cases cell (t + Q) (-(k : Int) + 1) <;> decide

private theorem gate_case_table : ∀ a b c d : Bool,
    (gateCase a b c d = 1 ↔ colourCode a b = 1 ∧ colourCode c d = 0) ∧
    (gateCase a b c d = 2 ↔ colourCode a b = 0 ∧ colourCode c d = 1) ∧
    (gateCase a b c d = 3 ↔ colourCode a b = 1 ∧ colourCode c d = 1) ∧
    (gateCase a b c d = 4 ↔ colourCode a b = 2 ∧ colourCode c d = 0) ∧
    (gateCase a b c d = 5 ↔ colourCode a b = 0 ∧ colourCode c d = 2) ∧
    (gateCase a b c d = 6 ↔ colourCode a b = 2 ∧ colourCode c d = 2) := by
  unfold gateCase colourCode
  decide +kernel

theorem gate_code_colours (Q t k : Nat) (hk : 0 < k) :
    (gateCode Q t k = 1 ↔ leftColour Q t k = 1 ∧ leftColour Q t (k - 1) = 0) ∧
    (gateCode Q t k = 2 ↔ leftColour Q t k = 0 ∧ leftColour Q t (k - 1) = 1) ∧
    (gateCode Q t k = 3 ↔ leftColour Q t k = 1 ∧ leftColour Q t (k - 1) = 1) ∧
    (gateCode Q t k = 4 ↔ leftColour Q t k = 2 ∧ leftColour Q t (k - 1) = 0) ∧
    (gateCode Q t k = 5 ↔ leftColour Q t k = 0 ∧ leftColour Q t (k - 1) = 2) ∧
    (gateCode Q t k = 6 ↔ leftColour Q t k = 2 ∧ leftColour Q t (k - 1) = 2) := by
  simpa only [gateCode, leftColour, leftCell,
    show -((k - 1 : Nat) : Int) = -(k : Int) + 1 by omega] using
    gate_case_table (cell t (-(k : Int))) (cell (t + Q) (-(k : Int)))
      (cell t (-(k : Int) + 1)) (cell (t + Q) (-(k : Int) + 1))

theorem defect_step_gate (Q t : Nat) (p : Int) :
    defect Q (t + 1) p = xor (defect Q t (p - 1)) (gateDifference Q t p) := by
  unfold defect difference gateDifference
  dsimp only
  rw [show t + 1 + Q = (t + Q) + 1 by omega]
  change xor (rule (cell (t + Q) (p - 1)) (cell (t + Q) p) (cell (t + Q) (p + 1)))
    (rule (cell t (p - 1)) (cell t p) (cell t (p + 1))) = _
  unfold rule
  cases cell t (p - 1) <;> cases cell (t + Q) (p - 1) <;>
    cases cell t p <;> cases cell (t + Q) p <;>
    cases cell t (p + 1) <;> cases cell (t + Q) (p + 1) <;> rfl

theorem left_defect_step_gate (Q t k : Nat) :
    leftDefect Q (t + 1) k = xor (leftDefect Q t (k + 1)) (leftGateDifference Q t k) := by
  simpa only [leftDefect, leftGateDifference,
    show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] using defect_step_gate Q t (-(k : Int))

theorem gate_difference_iff_flip (Q t k : Nat) :
    (leftDefect Q (t + 1) k = !leftDefect Q t (k + 1)) ↔ leftGateDifference Q t k = true := by
  rw [left_defect_step_gate]
  cases leftDefect Q t (k + 1) <;> cases leftGateDifference Q t k <;> decide

/-- Every nonzero collision has matching OR gates. It is transparent to the
incoming left defect at its own site. -/
theorem collision_gate_agreement (Q t : Nat) (p : Int)
    (hc : collision Q t p = true) : gateDifference Q t p = false := by
  unfold collision at hc
  unfold gateDifference
  cases ha : cell t p <;> cases hb : cell (t + Q) p <;>
    cases hc1 : cell t (p + 1) <;> cases hd : cell (t + Q) (p + 1) <;> simp_all

theorem collision_transmits_left (Q t k : Nat) (hc : collisionCode Q t k ≠ 0) :
    leftDefect Q (t + 1) k = leftDefect Q t (k + 1) := by
  have hs : collision Q t (-(k : Int)) = true := by
    simpa only [collisionBit] using (collision_code_nonzero Q t k).1 hc
  simp only [leftDefect, defect_step_gate, collision_gate_agreement Q t (-(k : Int)) hs,
    Bool.xor_false, show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega]

theorem collision_gates_agree_at_depth (Q t k : Nat) (hc : collisionCode Q t k ≠ 0) :
    leftGateDifference Q t k = false := by
  unfold leftGateDifference
  apply collision_gate_agreement
  simpa only [collisionBit] using (collision_code_nonzero Q t k).1 hc

/-- All six oriented cases, retaining the outside right bit where it is needed.
The common-black right endpoint (cases 3 and 5) forces an advance. -/
theorem collision_right_transport_table (Q t k : Nat) (hk : 2 ≤ k) :
    (collisionCode Q t k = 1 → leftDefect Q (t + 1) (k - 1) = leftCell t (k - 2)) ∧
    (collisionCode Q t k = 2 → leftDefect Q (t + 1) (k - 1) = leftCell (t + Q) (k - 2)) ∧
    (collisionCode Q t k = 3 → leftDefect Q (t + 1) (k - 1) = true) ∧
    (collisionCode Q t k = 4 → leftDefect Q (t + 1) (k - 1) = !leftCell (t + Q) (k - 2)) ∧
    (collisionCode Q t k = 5 → leftDefect Q (t + 1) (k - 1) = true) ∧
    (collisionCode Q t k = 6 → leftDefect Q (t + 1) (k - 1) = !leftCell t (k - 2)) := by
  simp only [leftDefect, leftCell,
    show -((k - 1 : Nat) : Int) = -(k : Int) + 1 by omega,
    show -((k - 2 : Nat) : Int) = -(k : Int) + 2 by omega,
    defect_step_gate]
  unfold gateDifference defect difference collisionCode
  dsimp only
  simp only [show -(k : Int) + 1 + 1 = -(k : Int) + 2 by omega]
  cases ha : cell t (-(k : Int)) <;> cases hb : cell (t + Q) (-(k : Int)) <;>
    cases hc : cell t (-(k : Int) + 1) <;> cases hd : cell (t + Q) (-(k : Int) + 1) <;>
    cases he : cell t (-(k : Int) + 2) <;> cases hf : cell (t + Q) (-(k : Int) + 2) <;>
    simp_all [colourCase]

/-- Crossing a shared black right endpoint reverses the unit orientation. -/
theorem advancing_right_colour_table (Q t k : Nat) (hk : 0 < k) :
    (collisionCode Q t k = 3 → leftColour Q (t + 1) (k - 1) = 2) ∧
    (collisionCode Q t k = 5 → leftColour Q (t + 1) (k - 1) = 1) := by
  have step : ∀ (u : Nat) (x : Int),
      cell (u + 1) x = rule (cell u (x - 1)) (cell u x) (cell u (x + 1)) := by
    intro u x
    rfl
  simp only [leftColour, leftCell,
    show -((k - 1 : Nat) : Int) = -(k : Int) + 1 by omega,
    show t + 1 + Q = (t + Q) + 1 by omega, step,
    show -(k : Int) + 1 - 1 = -(k : Int) by omega]
  unfold collisionCode
  cases ha : cell t (-(k : Int)) <;> cases hb : cell (t + Q) (-(k : Int)) <;>
    cases hc : cell t (-(k : Int) + 1) <;> cases hd : cell (t + Q) (-(k : Int) + 1) <;>
    simp_all [colourCase, colourCode, rule]

/-- A selected unit/black collision forces the defect one site right, irrespective
of the outside cells. -/
theorem advancing_collision_step (Q t : Nat) (p : Int)
    (hc : AdvancingCollision Q t p) : defect Q (t + 1) (p + 1) = true := by
  rcases hc with ⟨hd, ha, hb⟩
  rw [defect_step_gate]
  simp only [show p + 1 - 1 = p by omega]
  unfold gateDifference defect difference
  rw [ha, hb]
  cases h1 : cell t p <;> cases h2 : cell (t + Q) p <;> simp_all

/-- Cancellation of a true incoming defect requires a mismatching OR gate. -/
theorem incoming_defect_erased_iff (Q t k : Nat) (hd : leftDefect Q t (k + 1) = true) :
    leftDefect Q (t + 1) k = false ↔ leftGateDifference Q t k = true := by
  have he := defect_step_gate Q t (-(k : Int))
  change defect Q t (-((k + 1 : Nat) : Int)) = true at hd
  rw [show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega, hd] at he
  change defect Q (t + 1) (-(k : Int)) = false ↔ gateDifference Q t (-(k : Int)) = true
  rw [he]
  cases gateDifference Q t (-(k : Int)) <;> decide

theorem erasure_has_no_collision (Q t k : Nat)
    (hd : leftDefect Q t (k + 1) = true) (he : leftDefect Q (t + 1) k = false) :
    collisionCode Q t k = 0 := by
  by_cases hc : collisionCode Q t k = 0
  · exact hc
  · have ht := collision_transmits_left Q t k hc
    rw [hd, he] at ht
    contradiction

theorem erasure_event_of_step (Q t k : Nat)
    (hd : leftDefect Q t (k + 1) = true) (he : leftDefect Q (t + 1) k = false) :
    ErasureEvent Q t k := by
  refine ⟨hd, he, ?_, erasure_has_no_collision Q t k hd he, (left_defect_false_colours Q (t + 1) k).1 he⟩
  exact (gate_code_nonzero Q t k).2 ((incoming_defect_erased_iff Q t k hd).1 he)

/-- The erased pair is black exactly when the active OR gate and incoming unit
have opposite orientations. -/
theorem erasure_black_phase_iff (Q t k : Nat) (he : ErasureEvent Q t k) :
    leftColour Q (t + 1) k = 3 ↔
      (gateCode Q t k ≤ 3 ∧ leftColour Q t (k + 1) = 2) ∨
      (4 ≤ gateCode Q t k ∧ leftColour Q t (k + 1) = 1) := by
  rcases he with ⟨hin, hout, hgate, hcollision, hcolour⟩
  have step : ∀ (u : Nat) (x : Int),
      cell (u + 1) x = rule (cell u (x - 1)) (cell u x) (cell u (x + 1)) := by
    intro u x
    rfl
  simp only [leftDefect, defect, difference] at hin
  simp only [show -((k + 1 : Nat) : Int) = -(k : Int) - 1 by omega] at hin
  simp only [leftColour, leftCell,
    show -((k + 1 : Nat) : Int) = -(k : Int) - 1 by omega,
    show t + 1 + Q = (t + Q) + 1 by omega, step]
  unfold gateCode at hgate ⊢
  cases ha : cell t (-(k : Int) - 1) <;> cases hb : cell (t + Q) (-(k : Int) - 1) <;>
    cases hc : cell t (-(k : Int)) <;> cases hd : cell (t + Q) (-(k : Int)) <;>
    cases he : cell t (-(k : Int) + 1) <;> cases hf : cell (t + Q) (-(k : Int) + 1) <;>
    simp_all [gateCase, colourCode, rule]

/-- A black common reset cannot occur outside the earlier seed's cone. -/
theorem erasure_outside_seed_cone_white (Q t k : Nat) (hk : t + 1 < k)
    (he : ErasureEvent Q t k) : leftColour Q (t + 1) k = 0 := by
  have ho := left_colours_outside_seed_cone Q (t + 1) k hk
  have hp := he.2.2.2.2
  rcases ho with h0 | h2
  · exact h0
  · rcases hp with h0 | h3
    · exact h0
    · omega

/-- The actual seed also permits an erasure immediately, at a site with no collision.
This finite reduction rules out a blanket no-erasure seed invariant. -/
theorem seed_gate_erasure :
    leftDefect 3 0 3 = true ∧ leftDefect 3 1 2 = false ∧ leftGateDifference 3 0 2 = true := by
  decide +kernel

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
