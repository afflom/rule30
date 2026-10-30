module

public import Rule30UOR.Interfaces
public import Rule30UOR.TemporalDefect
public import Rule30UOR.DefectSource

/-!
# The temporal difference as an exact seeded Witt evolution

At time `t`, physical alignment of rows separated by `Q` requires shifting the earlier row
by `Q` bits. Without this shift, a bitwise XOR compares diagonal coordinates, not columns.

The pair recursion retains the background and the full nonlinear cross-carry. Its initial
state is fixed by the single seed. The center readout gives an exact Problem 1 equivalence;
the required unbounded sequence of nonzero center readouts remains unproved.
-/

@[expose] public section

namespace Rule30UOR.WittDefect

open Rule30UOR.Core (phi row)
open Rule30UOR.Interfaces (crossCarry)
open Rule30UOR.TemporalDefect
open Ruliology.CellularAutomata Rule30Jen Rule30Prize

/-- The full nonlinear row map commutes with bit shifts. -/
theorem phi_shl (y Q : Nat) : phi (y <<< Q) = phi y <<< Q := by
  change (y <<< Q) ^^^ (((y <<< Q) <<< 1) ||| ((y <<< Q) <<< 2)) =
    (y ^^^ ((y <<< 1) ||| (y <<< 2))) <<< Q
  simp only [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_or_distrib,
    ← Nat.shiftLeft_add]
  rw [Nat.add_comm Q 1, Nat.add_comm Q 2]

/-- Earlier row aligned with the later row's physical coordinates. -/
def background (Q t : Nat) : Nat := row t <<< Q

/-- Physical-column temporal difference in the later row's bit coordinates. -/
def alignedDefect (Q t : Nat) : Nat := row (t + Q) ^^^ background Q t

/-- Exact damage update, including the bilinear interaction with the background. -/
def defectStep (b d : Nat) : Nat := phi d ^^^ (crossCarry b d <<< 1)

theorem defectStep_eq (b d : Nat) :
    defectStep b d = phi (b ^^^ d) ^^^ phi b := by
  rw [Rule30UOR.Interfaces.phi_xor]
  unfold defectStep
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases (phi b).testBit i <;> cases (phi d).testBit i <;>
    cases (crossCarry b d <<< 1).testBit i <;> rfl

theorem background_step (Q t : Nat) : background Q (t + 1) = phi (background Q t) := by
  exact (phi_shl (row t) Q).symm

theorem reconstruct (Q t : Nat) : background Q t ^^^ alignedDefect Q t = row (t + Q) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [alignedDefect, Nat.testBit_xor]
  cases (background Q t).testBit i <;> cases (row (t + Q)).testBit i <;> rfl

theorem alignedDefect_step (Q t : Nat) :
    alignedDefect Q (t + 1) = defectStep (background Q t) (alignedDefect Q t) := by
  rw [defectStep_eq, reconstruct]
  unfold alignedDefect
  rw [background_step, show t + 1 + Q = (t + Q) + 1 by omega]
  rfl

/-- An autonomous recursion with no external driver or unspecified phase choices. -/
def pairOrbit (Q : Nat) : Nat → Nat × Nat
  | 0 => (1 <<< Q, row Q ^^^ (1 <<< Q))
  | t + 1 => let bd := pairOrbit Q t; (phi bd.1, defectStep bd.1 bd.2)

theorem pairOrbit_eq (Q : Nat) : ∀ t, pairOrbit Q t = (background Q t, alignedDefect Q t)
  | 0 => by simp [pairOrbit, background, alignedDefect, row]
  | t + 1 => by rw [pairOrbit, pairOrbit_eq Q t, background_step, alignedDefect_step]

/-- Bit `j + Q` compares the same physical column `t - j` in both rows. -/
theorem alignedDefect_readout (Q t j : Nat) :
    (alignedDefect Q t).testBit (j + Q) = defect Q t ((t : Int) - (j : Int)) := by
  simp only [alignedDefect, background, Nat.testBit_xor, Nat.testBit_shiftLeft]
  simp only [Nat.le_add_left, decide_true, Nat.add_sub_cancel, Bool.true_and]
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Interfaces.row_testBit,
    Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R]
  unfold Rule30Diagonals.R
  rw [show ((t + Q : Nat) : Int) - ((j + Q : Nat) : Int) = (t : Int) - (j : Int) by omega]
  rfl

theorem alignedDefect_center (Q t : Nat) :
    (alignedDefect Q t).testBit (t + Q) = defect Q t 0 := by
  simpa using alignedDefect_readout Q t t

/-- The difference is always nonzero at the later row's right edge. This is not a
nonzero-center theorem: the center is bit `t + Q`, not bit zero. -/
theorem alignedDefect_bit_zero (Q t : Nat) (hQ : 0 < Q) :
    (alignedDefect Q t).testBit 0 = true := by
  simp only [alignedDefect, background, Nat.testBit_xor, Nat.testBit_shiftLeft]
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Interfaces.rdiag_zero_all]
  simp [show ¬ Q ≤ 0 by omega]

/-- Exact remaining obligation, retaining the full seeded nonlinear pair evolution. -/
theorem problem1_iff_pairOrbit_center :
    Problem1 ↔ ∀ Q : Nat, 0 < Q → ∀ T : Nat,
      ∃ t : Nat, T ≤ t ∧ (pairOrbit Q t).2.testBit (t + Q) = true := by
  constructor
  · intro h Q hQ T
    apply Classical.byContradiction
    intro hn
    apply h
    refine ⟨T, Q, hQ, fun t ht => ?_⟩
    apply (difference_eq_false_iff center Q t).mp
    have hh : (pairOrbit Q t).2.testBit (t + Q) ≠ true := fun hb => hn ⟨t, ht, hb⟩
    rw [pairOrbit_eq, alignedDefect_center] at hh
    cases hb : defect Q t 0
    · exact hb
    · exact (hh hb).elim
  · intro h ⟨T, Q, hQ, hc⟩
    obtain ⟨t, ht, hb⟩ := h Q hQ T
    rw [pairOrbit_eq, alignedDefect_center] at hb
    have hz : defect Q t 0 = false := (difference_eq_false_iff center Q t).mpr (hc t ht)
    rw [hz] at hb
    contradiction

/-! ## Signed phase and its exact characteristic flux

The signed phase retains the orientation of a disagreement. The background is still
part of the state: phase zero alone does not distinguish common white from common black.
No monotonicity or periodicity of this phase is assumed.
-/

def bitValue (a : Bool) : Int := if a then 1 else 0

def rowBit (a i : Nat) : Bool := a.testBit i

def pairPhase (b d i : Nat) : Int :=
  bitValue ((b ^^^ d).testBit i) - bitValue (b.testBit i)

def alignedPhase (Q t i : Nat) : Int := pairPhase (background Q t) (alignedDefect Q t) i

def phase (Q t : Nat) (p : Int) : Int := bitValue (cell (t + Q) p) - bitValue (cell t p)

def gatePhase (Q t : Nat) (p : Int) : Int :=
  bitValue (cell (t + Q) p || cell (t + Q) (p + 1)) -
    bitValue (cell t p || cell t (p + 1))

/-- The flux is written in the old local cells, including the later OR gate.
It is not defined as the difference of two successive phases. -/
def phaseFlux (Q t : Nat) (p : Int) : Int :=
  -2 * bitValue (cell (t + Q) p || cell (t + Q) (p + 1)) * phase Q t (p - 1) +
    (1 - 2 * bitValue (cell t (p - 1))) * gatePhase Q t p

def leftPhase (Q t k : Nat) : Int := phase Q t (-(k : Int))
def leftGatePhase (Q t k : Nat) : Int := gatePhase Q t (-(k : Int))
def leftPhaseFlux (Q t k : Nat) : Int := phaseFlux Q t (-(k : Int))

theorem pair_phase_step (b d i : Nat) :
    pairPhase (phi b) (phi d ^^^ (crossCarry b d <<< 1)) i =
      bitValue (rowBit (phi (b ^^^ d)) i) - bitValue (rowBit (phi b) i) := by
  change pairPhase (phi b) (defectStep b d) i = _
  rw [defectStep_eq]
  unfold pairPhase rowBit
  have he : phi b ^^^ (phi (b ^^^ d) ^^^ phi b) = phi (b ^^^ d) := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_xor]
    cases (phi b).testBit j <;> cases (phi (b ^^^ d)).testBit j <;> rfl
  rw [he]

private theorem background_readout (Q t j : Nat) :
    (background Q t).testBit (j + Q) = cell t ((t : Int) - (j : Int)) := by
  simp only [background, Nat.testBit_shiftLeft, Nat.le_add_left, decide_true,
    Nat.add_sub_cancel, Bool.true_and]
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Right.rdiag_eq_R]
  rfl

theorem aligned_phase_left (Q t k : Nat) :
    alignedPhase Q t (t + k + Q) = leftPhase Q t k := by
  unfold alignedPhase pairPhase
  rw [reconstruct, Rule30UOR.Interfaces.row_testBit, Rule30UOR.Right.rdiag_eq_R,
    background_readout]
  unfold Rule30Diagonals.R leftPhase phase
  rw [show ((t + Q : Nat) : Int) - ((t + k + Q : Nat) : Int) = -(k : Int) by omega,
    show (t : Int) - ((t + k : Nat) : Int) = -(k : Int) by omega]

theorem phase_zero_iff (Q t k : Nat) :
    leftPhase Q t k = 0 ↔ Rule30UOR.Collision.leftDefect Q t k = false := by
  unfold leftPhase phase Rule30UOR.Collision.leftDefect defect difference
  dsimp only
  cases cell t (-(k : Int)) <;> cases cell (t + Q) (-(k : Int)) <;> decide

theorem phase_unit_iff (Q t k : Nat) :
    (leftPhase Q t k = -1 ∨ leftPhase Q t k = 1) ↔
      Rule30UOR.Collision.leftDefect Q t k = true := by
  unfold leftPhase phase Rule30UOR.Collision.leftDefect defect difference
  dsimp only
  cases cell t (-(k : Int)) <;> cases cell (t + Q) (-(k : Int)) <;> decide

private theorem xor_phase_balance : ∀ a a' g g' : Bool,
    bitValue (xor a' g') - bitValue (xor a g) =
      (bitValue a' - bitValue a) +
        (-2 * bitValue g' * (bitValue a' - bitValue a) +
          (1 - 2 * bitValue a) * (bitValue g' - bitValue g)) := by
  unfold bitValue
  decide +kernel

theorem phase_balance (Q t : Nat) (p : Int) :
    phase Q (t + 1) p = phase Q t (p - 1) + phaseFlux Q t p := by
  unfold phaseFlux phase gatePhase
  rw [show t + 1 + Q = (t + Q) + 1 by omega]
  exact xor_phase_balance (cell t (p - 1)) (cell (t + Q) (p - 1))
    (cell t p || cell t (p + 1)) (cell (t + Q) p || cell (t + Q) (p + 1))

theorem left_phase_balance (Q t k : Nat) :
    leftPhase Q (t + 1) k = leftPhase Q t (k + 1) + leftPhaseFlux Q t k := by
  simpa only [leftPhase, leftPhaseFlux,
    show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] using
      phase_balance Q t (-(k : Int))

open Rule30UOR.Collision Rule30UOR.DefectSource

theorem collision_phase_flip (Q t k : Nat) (hc : collisionCode Q t k ≠ 0) :
    leftPhaseFlux Q t k = -2 * leftPhase Q t (k + 1) := by
  have hs := (collision_code_nonzero Q t k).1 hc
  unfold collisionBit collision at hs
  unfold leftPhaseFlux phaseFlux leftPhase phase gatePhase
  rw [show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega]
  cases ha : cell t (-(k : Int)) <;> cases hb : cell (t + Q) (-(k : Int)) <;>
    cases hc : cell t (-(k : Int) + 1) <;> cases hd : cell (t + Q) (-(k : Int) + 1) <;>
    simp_all [bitValue]

theorem advancing_phase_flip (Q t k : Nat) (hk : 0 < k) (ha : advancingAtDepth Q t k) :
    leftPhase Q (t + 1) (k - 1) = -leftPhase Q t k := by
  rcases ha with ⟨hd, hb, hb'⟩
  have hh := phase_balance Q t (-(k : Int) + 1)
  simp only [phaseFlux, gatePhase, hb, hb', Bool.true_or, bitValue, ite_true,
    show -(k : Int) + 1 - 1 = -(k : Int) by omega] at hh
  change phase Q (t + 1) (-((k - 1 : Nat) : Int)) = -phase Q t (-(k : Int))
  rw [show -((k - 1 : Nat) : Int) = -(k : Int) + 1 by omega]
  omega

theorem gate_phase_cases (Q t k : Nat) :
    (gateCode Q t k = 1 → leftGatePhase Q t k = -1) ∧
    (gateCode Q t k = 2 → leftGatePhase Q t k = -1) ∧
    (gateCode Q t k = 3 → leftGatePhase Q t k = -1) ∧
    (gateCode Q t k = 4 → leftGatePhase Q t k = 1) ∧
    (gateCode Q t k = 5 → leftGatePhase Q t k = 1) ∧
    (gateCode Q t k = 6 → leftGatePhase Q t k = 1) := by
  unfold gateCode leftGatePhase gatePhase
  cases cell t (-(k : Int)) <;> cases cell (t + Q) (-(k : Int)) <;>
    cases cell t (-(k : Int) + 1) <;> cases cell (t + Q) (-(k : Int) + 1) <;>
    decide

theorem erasure_phase_balance (Q t k : Nat) (he : ErasureEvent Q t k) :
    leftPhase Q (t + 1) k = 0 ∧
      leftPhaseFlux Q t k = -leftPhase Q t (k + 1) ∧
      (leftPhase Q t (k + 1) = -1 ∨ leftPhase Q t (k + 1) = 1) := by
  have h0 := (phase_zero_iff Q (t + 1) k).2 he.2.1
  have hu := (phase_unit_iff Q t (k + 1)).2 he.1
  have hb := left_phase_balance Q t k
  exact ⟨h0, by omega, hu⟩

private theorem reset_product_table : ∀ a a' b b' c c' : Bool,
    xor a' a = true → xor (rule a' b' c') (rule a b c) = false →
    (colourCode (rule a b c) (rule a' b' c') = 3 ↔
      (bitValue (b' || c') - bitValue (b || c)) * (bitValue a' - bitValue a) = -1) ∧
    (colourCode (rule a b c) (rule a' b' c') = 0 ↔
      (bitValue (b' || c') - bitValue (b || c)) * (bitValue a' - bitValue a) = 1) := by
  unfold rule colourCode bitValue
  decide +kernel

theorem erasure_reset_product (Q t k : Nat) (he : ErasureEvent Q t k) :
    (leftColour Q (t + 1) k = 3 ↔ leftGatePhase Q t k * leftPhase Q t (k + 1) = -1) ∧
    (leftColour Q (t + 1) k = 0 ↔ leftGatePhase Q t k * leftPhase Q t (k + 1) = 1) := by
  have hin := he.1
  have hout := he.2.1
  simp only [leftDefect, defect, difference,
    show -((k + 1 : Nat) : Int) = -(k : Int) - 1 by omega,
    show t + 1 + Q = (t + Q) + 1 by omega] at hin hout
  simp only [leftColour, leftCell, leftGatePhase, gatePhase, leftPhase, phase,
    show -((k + 1 : Nat) : Int) = -(k : Int) - 1 by omega,
    show t + 1 + Q = (t + Q) + 1 by omega]
  exact reset_product_table (cell t (-(k : Int) - 1)) (cell (t + Q) (-(k : Int) - 1))
    (cell t (-(k : Int))) (cell (t + Q) (-(k : Int)))
    (cell t (-(k : Int) + 1)) (cell (t + Q) (-(k : Int) + 1)) hin hout

/-- The path starts at `(t,-k)` and advances one physical site per time step. -/
def pathPhase (Q t k n : Nat) : Int := phase Q (t + n) (-(k : Int) + (n : Int))

def pathFlux (Q t k : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => pathFlux Q t k n + phaseFlux Q (t + n) (-(k : Int) + (n : Int) + 1)

theorem path_balance (Q t k : Nat) : ∀ n : Nat,
    pathPhase Q t k n = leftPhase Q t k + pathFlux Q t k n := by
  intro n
  induction n with
  | zero => simp [pathPhase, pathFlux, leftPhase]
  | succ n ih =>
    have hs := phase_balance Q (t + n) (-(k : Int) + (n : Int) + 1)
    simp only [show -(k : Int) + (n : Int) + 1 - 1 = -(k : Int) + (n : Int) by omega] at hs
    change phase Q (t + (n + 1)) (-(k : Int) + ((n + 1 : Nat) : Int)) = _
    rw [show t + (n + 1) = (t + n) + 1 by omega,
      show -(k : Int) + ((n + 1 : Nat) : Int) = -(k : Int) + (n : Int) + 1 by omega, hs]
    change pathPhase Q t k n + _ = _
    rw [ih]
    simp only [pathFlux, Int.add_assoc]

theorem seed_left_phase (Q t : Nat) (hQ : 0 < Q) : leftPhase Q t (t + Q) = 1 := by
  unfold leftPhase phase
  rw [cell_left_edge, cell_eq_false_of_lt t _ (by omega)]
  rfl

theorem seed_center_balance (Q t : Nat) (hQ : 0 < Q) :
    leftPhase Q (t + (t + Q)) 0 = 1 + pathFlux Q t (t + Q) (t + Q) := by
  have hh := path_balance Q t (t + Q) (t + Q)
  rw [seed_left_phase Q t hQ] at hh
  simpa only [pathPhase, leftPhase, Int.natCast_zero, Int.neg_zero,
    show -((t + Q : Nat) : Int) + ((t + Q : Nat) : Int) = 0 by omega] using hh

/-- Periodicity requires exact cancellation of the seed's oriented boundary charge.
The value is minus one, not zero; a coboundary argument cannot discard this flux. -/
theorem periodic_seed_flux (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    pathFlux (m * P) N (N + m * P) (N + m * P) = -1 := by
  have hp := Rule30UOR.Scale.center_mul hc m (N + (N + m * P)) (by omega)
  rw [Rule30UOR.Scale.center_eq_kit, Rule30UOR.Scale.center_eq_kit] at hp
  have hz : leftPhase (m * P) (N + (N + m * P)) 0 = 0 := by
    unfold leftPhase phase
    change bitValue (center ((N + (N + m * P)) + m * P)) -
      bitValue (center (N + (N + m * P))) = 0
    rw [hp]
    omega
  have hb := seed_center_balance (m * P) N (Nat.mul_pos hm hP)
  omega

/-- The actual seed realizes a full signed cancellation immediately. This excludes
a monotone, unsigned interpretation of the signed balance law. -/
theorem seed_phase_cancellation :
    leftPhase 3 0 3 = 1 ∧ leftPhase 3 1 2 = 0 ∧ leftPhaseFlux 3 0 2 = -1 ∧
      leftGatePhase 3 0 2 = 1 := by
  decide +kernel

end Rule30UOR.WittDefect
