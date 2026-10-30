module

public import Rule30UOR.Interfaces
public import Rule30UOR.TemporalDefect
public import Rule30UOR.CentralCollision

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

private theorem phase_lag_add (Q R t : Nat) (p : Int) :
    phase (Q + R) t p = phase Q t p + phase R (t + Q) p := by
  unfold phase
  rw [show t + (Q + R) = (t + Q) + R by omega]
  omega

theorem left_phase_lag_add (Q R t k : Nat) :
    leftPhase (Q + R) t k = leftPhase Q t k + leftPhase R (t + Q) k := by
  exact phase_lag_add Q R t (-(k : Int))

private theorem phase_flux_lag_add (Q R t : Nat) (p : Int) :
    phaseFlux (Q + R) t p = phaseFlux Q t p + phaseFlux R (t + Q) p := by
  have h0 := phase_balance (Q + R) t p
  have h1 := phase_balance Q t p
  have h2 := phase_balance R (t + Q) p
  have ha := phase_lag_add Q R (t + 1) p
  have hb := phase_lag_add Q R t (p - 1)
  rw [show t + 1 + Q = (t + Q) + 1 by omega] at ha
  omega

/-- Lag compensation is additive only with the second background shifted by Q.
This does not give repeated copies of one fixed-background flux. -/
theorem path_flux_lag_add (Q R t k : Nat) : ∀ n : Nat,
    pathFlux (Q + R) t k n = pathFlux Q t k n + pathFlux R (t + Q) k n := by
  intro n
  induction n with
  | zero => simp [pathFlux]
  | succ n ih =>
    simp only [pathFlux, ih, phase_flux_lag_add,
      show t + n + Q = t + Q + n by omega]
    omega

/-- The physical leading-front witness ties the source's initial orientation
and its intervening flux to the actual center reset. -/
theorem leading_phase_reset (Q t k : Nat)
    (hl : Rule30UOR.CentralCollision.LeadingAdvance Q t k)
    (hc : Rule30UOR.DefectFront.CenterCleanThrough Q t k) :
    (leftColour Q (t + k) 0 = 3 ↔
      leftGatePhase Q (t + (k - 1)) 0 *
        (leftPhase Q t k + pathFlux Q t k (k - 1)) = -1) ∧
    (leftColour Q (t + k) 0 = 0 ↔
      leftGatePhase Q (t + (k - 1)) 0 *
        (leftPhase Q t k + pathFlux Q t k (k - 1)) = 1) := by
  obtain ⟨hf, he, hg, hw⟩ := Rule30UOR.CentralCollision.leading_first_erasure Q t k hl hc
  have hp : leftPhase Q (t + (k - 1)) 1 = leftPhase Q t k + pathFlux Q t k (k - 1) := by
    have hk := hl.1
    simpa only [pathPhase, leftPhase,
      show -(k : Int) + ((k - 1 : Nat) : Int) = -(1 : Int) by omega,
      show -((1 : Nat) : Int) = -(1 : Int) by omega] using
      path_balance Q t k (k - 1)
  have hr := erasure_reset_product Q (t + (k - 1)) 0 he
  have hk := hl.1
  simpa only [Nat.zero_add, show t + (k - 1) + 1 = t + k by omega, hp] using hr

/-! ## Compatibility of center erasures within a white block -/

def CommonWhiteBlock (Q b n : Nat) : Prop :=
  ∀ s : Nat, s ≤ n → cell (b + s) 0 = false ∧ cell (b + s + Q) 0 = false

private theorem right_black_persists (t : Nat) : ∀ n : Nat,
    (∀ s : Nat, s < n → cell (t + s) 0 = false) → cell t 1 = true → cell (t + n) 1 = true := by
  intro n
  induction n with
  | zero => intro _ hb; simpa using hb
  | succ n ih =>
    intro hw hb
    have hprev := ih (fun s hs => hw s (by omega)) hb
    rw [show t + (n + 1) = (t + n) + 1 by omega]
    change rule (cell (t + n) 0) (cell (t + n) 1) (cell (t + n) 2) = true
    rw [hw n (by omega), hprev]
    rfl

private theorem white_block_mono (Q b n i j : Nat) (hw : CommonWhiteBlock Q b n)
    (hij : i ≤ j) (hjn : j ≤ n) :
    (cell (b + i) 1 = true → cell (b + j) 1 = true) ∧
    (cell (b + i + Q) 1 = true → cell (b + j + Q) 1 = true) := by
  constructor
  · intro hb
    have hh := right_black_persists (b + i) (j - i) (fun s hs => by
      simpa only [Nat.add_assoc] using (hw (i + s) (by omega)).1) hb
    simpa only [show b + i + (j - i) = b + j by omega] using hh
  · intro hb
    have hh := right_black_persists (b + i + Q) (j - i) (fun s hs => by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hw (i + s) (by omega)).2) hb
    simpa only [show b + i + Q + (j - i) = b + j + Q by omega] using hh

private theorem center_gate_white (Q t : Nat) (hw : cell t 0 = false)
    (hw' : cell (t + Q) 0 = false) :
    (gateCode Q t 0 = 2 ↔ cell t 1 = true ∧ cell (t + Q) 1 = false) ∧
    (gateCode Q t 0 = 5 ↔ cell t 1 = false ∧ cell (t + Q) 1 = true) := by
  simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add, hw, hw']
  cases cell t 1 <;> cases cell (t + Q) 1 <;> decide

private theorem center_gate_nonzero (Q t : Nat) (h0 : leftDefect Q t 0 = false)
    (hg : gateCode Q t 0 ≠ 0) : gateCode Q t 0 = 2 ∨ gateCode Q t 0 = 5 := by
  simp only [leftDefect, defect, difference, Int.natCast_zero, Int.neg_zero] at h0
  simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add] at hg ⊢
  cases ha : cell t 0 <;> cases hb : cell (t + Q) 0 <;>
    cases hc : cell t 1 <;> cases hd : cell (t + Q) 1 <;> simp_all [gateCase]

theorem center_erasure_iff_gate (Q t : Nat) (h0 : leftDefect Q t 0 = false)
    (h1 : leftDefect Q (t + 1) 0 = false) :
    ErasureEvent Q t 0 ↔ gateCode Q t 0 = 2 ∨ gateCode Q t 0 = 5 := by
  constructor
  · intro he
    exact center_gate_nonzero Q t h0 he.2.2.1
  · intro hg
    have hne : gateCode Q t 0 ≠ 0 := by rcases hg with he | he <;> omega
    have hgate := (gate_code_nonzero Q t 0).1 hne
    have hs := left_defect_step_gate Q t 0
    rw [h1, hgate] at hs
    have hin : leftDefect Q t 1 = true := by
      cases hd : leftDefect Q t 1
      · simp only [Nat.zero_add, hd] at hs
        cases hs
      · rfl
    exact erasure_event_of_step Q t 0 hin h1

/-- Two mismatching OR gates within a common white block force every intervening
gate to have the same orientation. Deeper right cells remain unrestricted. -/
theorem white_block_gate_convex (Q b n i j k : Nat) (hw : CommonWhiteBlock Q b n)
    (hij : i ≤ j) (hjk : j ≤ k) (hkn : k ≤ n)
    (hi : gateCode Q (b + i) 0 = 2 ∨ gateCode Q (b + i) 0 = 5)
    (hk : gateCode Q (b + k) 0 = 2 ∨ gateCode Q (b + k) 0 = 5) :
    gateCode Q (b + j) 0 = gateCode Q (b + i) 0 := by
  have ci := center_gate_white Q (b + i) (hw i (by omega)).1 (hw i (by omega)).2
  have cj := center_gate_white Q (b + j) (hw j (by omega)).1 (hw j (by omega)).2
  have ck := center_gate_white Q (b + k) (hw k hkn).1 (hw k hkn).2
  have mij := white_block_mono Q b n i j hw hij (by omega)
  have mjk := white_block_mono Q b n j k hw hjk hkn
  have mik := white_block_mono Q b n i k hw (by omega) hkn
  rcases hi with hi | hi <;> rcases hk with hk | hk
  · have ai := (ci.1.1 hi).1
    have bk := (ck.1.1 hk).2
    have aj := mij.1 ai
    have bj : cell (b + j + Q) 1 = false := by
      cases he : cell (b + j + Q) 1
      · rfl
      · have hh := mjk.2 he
        rw [bk] at hh
        contradiction
    exact (cj.1.2 ⟨aj, bj⟩).trans hi.symm
  · have hh := mik.1 (ci.1.1 hi).1
    rw [(ck.2.1 hk).1] at hh
    contradiction
  · have hh := mik.2 (ci.2.1 hi).2
    rw [(ck.1.1 hk).2] at hh
    contradiction
  · have bi := (ci.2.1 hi).2
    have ak := (ck.2.1 hk).1
    have bj := mij.2 bi
    have aj : cell (b + j) 1 = false := by
      cases he : cell (b + j) 1
      · rfl
      · have hh := mjk.1 he
        rw [ak] at hh
        contradiction
    exact (cj.2.2 ⟨aj, bj⟩).trans hi.symm

/-- With the finite center-agreement window retained, the entire erasure burst
is an interval with one gate orientation. -/
theorem white_block_erasure_convex (Q b n i j k : Nat) (hw : CommonWhiteBlock Q b n)
    (hc : Rule30UOR.DefectFront.CenterCleanThrough Q b (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkn : k ≤ n)
    (hi : ErasureEvent Q (b + i) 0) (hk : ErasureEvent Q (b + k) 0) :
    ErasureEvent Q (b + j) 0 ∧ gateCode Q (b + j) 0 = gateCode Q (b + i) 0 := by
  have cases_at : ∀ s : Nat, s ≤ n →
      (ErasureEvent Q (b + s) 0 ↔ gateCode Q (b + s) 0 = 2 ∨ gateCode Q (b + s) 0 = 5) := by
    intro s hs
    exact center_erasure_iff_gate Q (b + s) (hc s (by omega))
      (by simpa only [Nat.add_assoc] using hc (s + 1) (by omega))
  have gi := (cases_at i (by omega)).1 hi
  have gk := (cases_at k hkn).1 hk
  have ge := white_block_gate_convex Q b n i j k hw hij hjk hkn gi gk
  exact ⟨(cases_at j (by omega)).2 (by rw [ge]; exact gi), ge⟩

/-! These finite certificates establish that the surviving gate cases, including
a common-black reset, occur in the actual seed orbit. They are not recurrence
premises or evidence for any unbounded statement. -/

private theorem cell_as_row (t : Nat) (p : Int) (hp : p ≤ (t : Int)) :
    cell t p = (row t).testBit (((t : Int) - p).toNat) := by
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Right.rdiag_eq_R]
  unfold Rule30Diagonals.R
  rw [show (t : Int) - ((((t : Int) - p).toNat : Nat) : Int) = p by omega]

private theorem cell_left_as_row (t k : Nat) :
    cell t (-(k : Int)) = (row t).testBit (t + k) := by
  rw [cell_as_row t (-(k : Int)) (by omega)]
  congr 1
  omega

private def RowLeadingData (Q t k : Nat) : Prop :=
  2 ≤ k ∧ (row t).testBit (t + k) ≠ (row (t + Q)).testBit (t + Q + k) ∧
    (row t).testBit (t + (k - 1)) = true ∧ (row (t + Q)).testBit (t + Q + (k - 1)) = true ∧
    (∀ r : Nat, r < k → (row t).testBit (t + r) = (row (t + Q)).testBit (t + Q + r)) ∧
    (∀ s : Nat, s ≤ k → (row (t + s)).testBit (t + s) = (row (t + s + Q)).testBit (t + s + Q))

private theorem leading_of_rows (Q t k : Nat) (h : RowLeadingData Q t k) :
    Rule30UOR.CentralCollision.LeadingAdvance Q t k ∧
      Rule30UOR.DefectFront.CenterCleanThrough Q t k := by
  obtain ⟨hk, hne, hb, hb', hp, hc⟩ := h
  have hu : leftDefect Q t k = true := by
    unfold leftDefect defect difference
    dsimp only
    rw [cell_left_as_row, cell_left_as_row]
    cases ha : (row t).testBit (t + k) <;>
      cases hb : (row (t + Q)).testBit (t + Q + k) <;> simp_all
  refine ⟨⟨hk, ?_, by omega, hu, ?_⟩, ?_⟩
  · change cell t (-(k : Int)) ≠ cell (t + Q) (-(k : Int)) ∧
      cell t (-(k : Int) + 1) = true ∧ cell (t + Q) (-(k : Int) + 1) = true
    rw [show -(k : Int) + 1 = -((k - 1 : Nat) : Int) by omega,
      cell_left_as_row, cell_left_as_row, cell_left_as_row, cell_left_as_row]
    exact ⟨hne, hb, hb'⟩
  · intro r hr
    apply (difference_eq_false_iff (fun u => cell u (-(r : Int))) Q t).2
    simpa only [cell_left_as_row] using (hp r hr).symm
  · intro s hs
    apply (difference_eq_false_iff (fun u => cell u (-((0 : Nat) : Int))) Q (t + s)).2
    simpa only [cell_left_as_row, Nat.add_zero] using (hc s hs).symm

theorem seed_leading_gate_five :
    Rule30UOR.CentralCollision.LeadingAdvance 4 5 2 ∧
      Rule30UOR.DefectFront.CenterCleanThrough 4 5 2 ∧ gateCode 4 6 0 = 5 := by
  obtain ⟨hl, hc⟩ := leading_of_rows 4 5 2 (by unfold RowLeadingData; decide +kernel)
  refine ⟨hl, hc, ?_⟩
  simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add]
  rw [cell_as_row 6 0 (by omega), cell_as_row 10 0 (by omega),
    cell_as_row 6 1 (by omega), cell_as_row 10 1 (by omega)]
  decide +kernel

theorem seed_leading_gate_two :
    Rule30UOR.CentralCollision.LeadingAdvance 7 7 4 ∧
      Rule30UOR.DefectFront.CenterCleanThrough 7 7 4 ∧ gateCode 7 10 0 = 2 := by
  obtain ⟨hl, hc⟩ := leading_of_rows 7 7 4 (by unfold RowLeadingData; decide +kernel)
  refine ⟨hl, hc, ?_⟩
  simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add]
  rw [cell_as_row 10 0 (by omega), cell_as_row 17 0 (by omega),
    cell_as_row 10 1 (by omega), cell_as_row 17 1 (by omega)]
  decide +kernel

theorem seed_leading_black_reset :
    Rule30UOR.CentralCollision.LeadingAdvance 11 4 4 ∧
      Rule30UOR.DefectFront.CenterCleanThrough 11 4 4 ∧
      gateCode 11 7 0 = 5 ∧ leftColour 11 8 0 = 3 := by
  obtain ⟨hl, hc⟩ := leading_of_rows 11 4 4 (by unfold RowLeadingData; decide +kernel)
  refine ⟨hl, hc, ?_, ?_⟩
  · simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add]
    rw [cell_as_row 7 0 (by omega), cell_as_row 18 0 (by omega),
      cell_as_row 7 1 (by omega), cell_as_row 18 1 (by omega)]
    decide +kernel
  · simp only [leftColour, leftCell, Int.natCast_zero, Int.neg_zero]
    rw [cell_as_row 8 0 (by omega), cell_as_row 19 0 (by omega)]
    decide +kernel

/-! ## The erasure kernel with its gate channel retained

This is an exact local bookkeeping map, not an autonomous finite-state model.
Its coefficients and gate channel are supplied by the actual paired background.
-/

def transferPhase (a g : Bool) (incoming gate : Int) : Int :=
  (1 - 2 * bitValue g) * incoming + (1 - 2 * bitValue a) * gate

def recoverPhase (a g : Bool) (outgoing gate : Int) : Int :=
  (1 - 2 * bitValue g) * (outgoing - (1 - 2 * bitValue a) * gate)

def laterGate (Q t k : Nat) : Bool :=
  cell (t + Q) (-(k : Int)) || cell (t + Q) (-(k : Int) + 1)

theorem transfer_recover (a g : Bool) (incoming gate : Int) :
    recoverPhase a g (transferPhase a g incoming gate) gate = incoming := by
  cases a <;> cases g <;> simp [transferPhase, recoverPhase, bitValue] <;> omega

theorem transfer_kernel (a g : Bool) (incoming gate : Int) :
    transferPhase a g incoming gate = 0 ↔ incoming = recoverPhase a g 0 gate := by
  cases a <;> cases g <;> simp [transferPhase, recoverPhase, bitValue] <;> omega

theorem phase_transfer (Q t k : Nat) :
    leftPhase Q (t + 1) k =
      transferPhase (leftCell t (k + 1)) (laterGate Q t k)
        (leftPhase Q t (k + 1)) (leftGatePhase Q t k) := by
  have hb := left_phase_balance Q t k
  simp only [leftPhase, leftPhaseFlux, phaseFlux, transferPhase, laterGate, leftCell, leftGatePhase,
    show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] at hb ⊢
  cases ha : cell t (-((k + 1 : Nat) : Int)) <;>
    cases hg : (cell (t + Q) (-(k : Int)) || cell (t + Q) (-(k : Int) + 1)) <;>
    simp_all [bitValue] <;> omega

theorem phase_recover (Q t k : Nat) :
    leftPhase Q t (k + 1) =
      recoverPhase (leftCell t (k + 1)) (laterGate Q t k)
        (leftPhase Q (t + 1) k) (leftGatePhase Q t k) := by
  rw [phase_transfer]
  exact (transfer_recover _ _ _ _).symm

/-- A zero center/left readout at an erasure still retains a nonzero gate channel.
The erased incoming unit is recoverable from that channel and its background. -/
theorem erasure_recovery (Q t k : Nat) (he : ErasureEvent Q t k) :
    leftGatePhase Q t k ≠ 0 ∧ leftPhase Q t (k + 1) =
      recoverPhase (leftCell t (k + 1)) (laterGate Q t k) 0 (leftGatePhase Q t k) := by
  constructor
  · have hg := (gate_code_nonzero Q t k).1 he.2.2.1
    unfold leftGateDifference gateDifference at hg
    unfold leftGatePhase gatePhase
    cases ha : (cell t (-(k : Int)) || cell t (-(k : Int) + 1)) <;>
      cases hb : (cell (t + Q) (-(k : Int)) || cell (t + Q) (-(k : Int) + 1)) <;>
      simp_all [bitValue]
  · have hr := phase_recover Q t k
    rw [(phase_zero_iff Q (t + 1) k).2 he.2.1] at hr
    exact hr

/-! ## Both erasure orientations are forced under a periodic center

A Boolean signal with only downward Q-shifts eventually becomes Q-periodic.
The proof uses the exact mass of a sliding Q-window and well-foundedness of Nat;
there is no density or measured-frequency premise.
-/

private def windowMass (f : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, t => (if f t then 1 else 0) + windowMass f n (t + 1)

private theorem window_mass_slide (f : Nat → Bool) : ∀ Q t : Nat,
    windowMass f Q (t + 1) + (if f t then 1 else 0) =
      windowMass f Q t + (if f (t + Q) then 1 else 0) := by
  intro Q
  induction Q with
  | zero => intro t; simp [windowMass]
  | succ Q ih =>
    intro t
    have hh := ih (t + 1)
    simp only [windowMass] at ⊢
    rw [show t + 1 + Q = t + (Q + 1) by omega] at hh
    omega

private theorem decreasing_nat_stabilizes (g : Nat → Nat)
    (hs : ∀ n : Nat, g (n + 1) ≤ g n) : ∃ U : Nat, ∀ t : Nat, U ≤ t → g t = g U := by
  have hle : ∀ i d : Nat, g (i + d) ≤ g i := by
    intro i d
    induction d with
    | zero => simp
    | succ d ih =>
      have hh := hs (i + d)
      rw [show i + (d + 1) = i + d + 1 by omega]
      omega
  have aux : ∀ a s : Nat, g s ≤ a → ∃ U : Nat, s ≤ U ∧ ∀ t : Nat, U ≤ t → g t = g U := by
    intro a
    induction a with
    | zero =>
      intro s hgs
      refine ⟨s, Nat.le_refl s, ?_⟩
      intro t ht
      have hh := hle s (t - s)
      rw [show s + (t - s) = t by omega] at hh
      omega
    | succ a ih =>
      intro s hgs
      by_cases he : ∀ t : Nat, s ≤ t → g t = g s
      · exact ⟨s, Nat.le_refl s, he⟩
      · have hex : ∃ t : Nat, s ≤ t ∧ g t < g s := by
          apply Classical.byContradiction
          intro hn
          apply he
          intro t ht
          have hh := hle s (t - s)
          rw [show s + (t - s) = t by omega] at hh
          by_cases hlt : g t < g s
          · exact (hn ⟨t, ht, hlt⟩).elim
          · omega
        obtain ⟨t, ht, hlt⟩ := hex
        obtain ⟨U, hU, hh⟩ := ih t (by omega)
        exact ⟨U, by omega, hh⟩
  obtain ⟨U, hU, hh⟩ := aux (g 0) 0 (Nat.le_refl _)
  exact ⟨U, hh⟩

private theorem no_rise_eventually_periodic (f : Nat → Bool) (Q T : Nat) (hQ : 0 < Q)
    (hn : ∀ t : Nat, T ≤ t → f t = false → f (t + Q) = false) : EventuallyPeriodic f := by
  let g (n : Nat) := windowMass f Q (T + n)
  have hg : ∀ n : Nat, g (n + 1) ≤ g n := by
    intro n
    have hh := window_mass_slide f Q (T + n)
    cases ha : f (T + n)
    · have hb := hn (T + n) (by omega) ha
      simp only [ha, hb, Bool.false_eq_true, ite_false] at hh
      dsimp [g]
      rw [show T + (n + 1) = T + n + 1 by omega]
      omega
    · cases hb : f (T + n + Q) <;>
        simp only [ha, hb, Bool.false_eq_true, ite_false, ite_true] at hh <;>
        dsimp [g] <;> rw [show T + (n + 1) = T + n + 1 by omega] <;> omega
  obtain ⟨U, hu⟩ := decreasing_nat_stabilizes g hg
  refine ⟨T + U, Q, hQ, ?_⟩
  intro t ht
  have h0 := hu (t - T) (by omega)
  have h1 := hu (t + 1 - T) (by omega)
  dsimp [g] at h0 h1
  rw [show T + (t - T) = t by omega] at h0
  rw [show T + (t + 1 - T) = t + 1 by omega] at h1
  have hh := window_mass_slide f Q t
  rw [h0, h1] at hh
  cases ha : f t <;> cases hb : f (t + Q) <;> simp_all

private theorem nonperiodic_has_rise (f : Nat → Bool) (hf : ¬ EventuallyPeriodic f)
    (Q N : Nat) (hQ : 0 < Q) : ∃ t : Nat, N ≤ t ∧ f t = false ∧ f (t + Q) = true := by
  apply Classical.byContradiction
  intro hn
  apply hf
  apply no_rise_eventually_periodic f Q N hQ
  intro t ht hw
  cases hb : f (t + Q)
  · rfl
  · exact (hn ⟨t, ht, hw, hb⟩).elim

private theorem nonperiodic_has_fall (f : Nat → Bool) (hf : ¬ EventuallyPeriodic f)
    (Q N : Nat) (hQ : 0 < Q) : ∃ t : Nat, N ≤ t ∧ f t = true ∧ f (t + Q) = false := by
  have hn : ¬ EventuallyPeriodic (fun t => !f t) := by
    rintro ⟨U, R, hR, hp⟩
    apply hf
    refine ⟨U, R, hR, ?_⟩
    intro t ht
    have hh := hp t ht
    cases ha : f t <;> cases hb : f (t + R) <;> simp_all
  obtain ⟨t, ht, h0, h1⟩ := nonperiodic_has_rise (fun t => !f t) hn Q N hQ
  refine ⟨t, ht, ?_, ?_⟩
  · cases ha : f t <;> simp_all
  · cases hb : f (t + Q) <;> simp_all

private def maskedRight (t : Nat) : Bool := (!center t) && cell t 1

private theorem masked_right_nonperiodic {T P : Nat} (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : ¬ EventuallyPeriodic maskedRight := by
  intro hm
  have hp : EventuallyPeriodic center := ⟨T, P, hP, fun t ht => by
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht⟩
  obtain ⟨U, R, hR, hpc, hpm⟩ := common_period hp hm
  apply Rule30MaskedJen.masked_jen 0 hR
    (fun t ht => by simpa only [Rule30Prize.center] using hpc t ht)
  intro t ht hw
  have h0 : center t = false := by simpa only [Rule30Prize.center] using hw
  have h1 : center (t + R) = false := (hpc t ht).trans h0
  simpa only [maskedRight, h0, h1, Bool.not_false, Bool.true_and, Int.zero_add] using hpm t ht

private theorem mask_gate_table : ∀ a b r s : Bool,
    b = a → (!b && s) ≠ (!a && r) →
      gateCase a b r s = (if !a && r then 2 else 5) := by
  unfold gateCase
  decide +kernel

private theorem gate_of_mask_change (Q t : Nat) (hc : center (t + Q) = center t)
    (hm : maskedRight (t + Q) ≠ maskedRight t) :
    gateCode Q t 0 = (if maskedRight t then 2 else 5) := by
  simp only [maskedRight, Rule30Prize.center] at hc hm ⊢
  simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add]
  exact mask_gate_table (cell t 0) (cell (t + Q) 0) (cell t 1) (cell (t + Q) 1) hc hm

/-- For every positive multiple of a hypothetical center period, both orientations
of actual center erasures recur arbitrarily late. A one-sided phase drift cannot
be inferred by selecting just one recurring cancellation case. -/
theorem periodic_erasure_orientation (T P m N g : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hg : g = 2 ∨ g = 5) :
    ∃ t : Nat, N ≤ t ∧ ErasureEvent (m * P) t 0 ∧ gateCode (m * P) t 0 = g := by
  have hf := masked_right_nonperiodic hP hc
  have hp : ∀ t : Nat, T ≤ t → center (t + P) = center t := by
    intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht
  have produce : ∀ t : Nat, max T N ≤ t →
      gateCode (m * P) t 0 = g →
      ∃ u : Nat, N ≤ u ∧ ErasureEvent (m * P) u 0 ∧ gateCode (m * P) u 0 = g := by
    intro t ht hgate
    have h0 : leftDefect (m * P) t 0 = false := by
      simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using
        Rule30UOR.DefectFront.center_defect_zero hp m t (by omega)
    have h1 : leftDefect (m * P) (t + 1) 0 = false := by
      simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using
        Rule30UOR.DefectFront.center_defect_zero hp m (t + 1) (by omega)
    exact ⟨t, by omega, (center_erasure_iff_gate (m * P) t h0 h1).2 (by rw [hgate]; exact hg), hgate⟩
  rcases hg with hg | hg
  · obtain ⟨t, ht, h0, h1⟩ := nonperiodic_has_fall maskedRight hf (m * P) (max T N) (Nat.mul_pos hm hP)
    have hchange : maskedRight (t + m * P) ≠ maskedRight t := by rw [h0, h1]; decide
    have hgate := gate_of_mask_change (m * P) t (periodic_mul hp m t (by omega)) hchange
    simp only [h0, ite_true] at hgate
    exact produce t ht (by simpa only [hg] using hgate)
  · obtain ⟨t, ht, h0, h1⟩ := nonperiodic_has_rise maskedRight hf (m * P) (max T N) (Nat.mul_pos hm hP)
    have hchange : maskedRight (t + m * P) ≠ maskedRight t := by rw [h0, h1]; decide
    have hgate := gate_of_mask_change (m * P) t (periodic_mul hp m t (by omega)) hchange
    simp only [h0, Bool.false_eq_true, ite_false] at hgate
    exact produce t ht (by simpa only [hg] using hgate)

/-! ## The physical black-boundary origin of an oriented erasure burst -/

open Rule30UOR.CentralCollision Rule30UOR.DefectFront

/-- An erasure in a black-then-white gap has a leading source at the initial
black boundary. Its first center erasure has the same orientation as the given
erasure, even when the latter lies later in the burst. -/
theorem black_gap_erasure_origin (Q b r g : Nat) (hr : 0 < r)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hb : Rule30UOR.Core.center b = true) (hw : WhiteCenterGap b r)
    (he : ErasureEvent Q (b + r) 0) (hg : gateCode Q (b + r) 0 = g) :
    ∃ k : Nat, k ≤ r + 1 ∧ LeadingAdvance Q b k ∧
      FirstPathErasure Q b k (k - 2) ∧ gateCode Q (b + (k - 1)) 0 = g := by
  have clean : CenterCleanThrough Q b (r + 1) := by
    intro j hj
    simp only [leftDefect, Int.natCast_zero, Int.neg_zero]
    apply (difference_eq_false_iff (fun u => cell u 0) Q (b + j)).2
    simpa only [center, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hc j hj).symm
  obtain ⟨k, hk, hl⟩ := black_gap_forces_initial_leading Q b r hr hc hb hw (by
    change defect Q (b + r) (-1) = true
    exact he.1)
  obtain ⟨hf, _he, hfirst, _hw⟩ := leading_first_erasure Q b k hl
    (fun j hj => clean j (by omega))
  have hlast := (center_erasure_iff_gate Q (b + r) (clean r (by omega))
    (by simpa only [Nat.add_assoc] using clean (r + 1) (Nat.le_refl _))).1 he
  have block : CommonWhiteBlock Q (b + 1) (r - 1) := by
    intro j hj
    have hw0 : cell (b + 1 + j) 0 = false := by
      simpa only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center, Nat.add_assoc] using
        hw (1 + j) (by omega) (by omega)
    have hs := (difference_eq_false_iff (fun u => cell u 0) Q (b + 1 + j)).1 (by
      simpa only [leftDefect, defect, Int.natCast_zero, Int.neg_zero, Nat.add_assoc] using
        clean (1 + j) (by omega))
    exact ⟨hw0, hs.trans hw0⟩
  have hk2 := hl.1
  have eqg := white_block_gate_convex Q (b + 1) (r - 1) (k - 2) (r - 1) (r - 1)
    block (by omega) (Nat.le_refl _) (Nat.le_refl _)
    (by simpa only [show b + 1 + (k - 2) = b + (k - 1) by omega] using hfirst)
    (by simpa only [show b + 1 + (r - 1) = b + r by omega] using hlast)
  have same : gateCode Q (b + r) 0 = gateCode Q (b + (k - 1)) 0 := by
    simpa only [show b + 1 + (r - 1) = b + r by omega,
      show b + 1 + (k - 2) = b + (k - 1) by omega] using eqg
  exact ⟨k, hk, hl, hf, same.symm.trans hg⟩

private theorem last_black_prefix (f : Nat → Bool) : ∀ n : Nat,
    f 0 = true → f n = false →
      ∃ j : Nat, j < n ∧ f j = true ∧ ∀ i : Nat, j < i → i ≤ n → f i = false := by
  intro n
  induction n with
  | zero => intro h0 hn; rw [h0] at hn; contradiction
  | succ n ih =>
    intro h0 hn
    cases hb : f n
    · obtain ⟨j, hj, hblack, hwhite⟩ := ih h0 hb
      refine ⟨j, by omega, hblack, ?_⟩
      intro i hji hi
      by_cases hin : i ≤ n
      · exact hwhite i hji hin
      · simpa only [show i = n + 1 by omega] using hn
    · refine ⟨n, by omega, hb, ?_⟩
      intro i hni hi
      simpa only [show i = n + 1 by omega] using hn

private theorem black_in_period {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (t : Nat) (ht : T ≤ t) :
    ∃ r : Nat, r < P ∧ center (t + r) = true := by
  have hex : ∃ u : Nat, t ≤ u ∧ center u = true := by
    apply Classical.byContradiction
    intro hn
    apply center_not_eventually_constant
    refine ⟨t, false, fun u hu => ?_⟩
    cases hb : center u
    · rfl
    · exact (hn ⟨u, hu, hb⟩).elim
  obtain ⟨u, hu, hb⟩ := hex
  let r := (u - t) % P
  have hr : r < P := Nat.mod_lt _ hP
  have he : (t + r) + ((u - t) / P) * P = u := by
    have hh := Nat.mod_add_div (u - t) P
    rw [Nat.mul_comm P ((u - t) / P)] at hh
    dsimp [r]
    omega
  have hp := periodic_mul hc ((u - t) / P) (t + r) (by omega)
  rw [he] at hp
  exact ⟨r, hr, hp.symm.trans hb⟩

/-- Both gate orientations recur with their actual leading sources on common
black boundaries. The entire interval from that boundary to the first erasure
is retained, so orientation recurrence and source recurrence are correlated. -/
theorem periodic_black_erasure_origin (T P m N g : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hg : g = 2 ∨ g = 5) :
    ∃ b k : Nat, N ≤ b ∧ k ≤ P ∧ Rule30UOR.Core.center b = true ∧
      WhiteCenterGap b (k - 1) ∧ LeadingAdvance (m * P) b k ∧
      FirstPathErasure (m * P) b k (k - 2) ∧ gateCode (m * P) (b + (k - 1)) 0 = g := by
  have hp : ∀ t, T ≤ t → center (t + P) = center t := by
    intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht
  obtain ⟨t, ht, he, hgate⟩ := periodic_erasure_orientation T P m (max T N + P) g hP hm hc hg
  have h0 := center_defect_zero hp m t (by omega)
  have h1 := center_defect_zero hp m (t + 1) (by omega)
  have hwhite : center t = false := (defect_right_and_white_of_clean_pair (m * P) t 0
    h0 h1 he.1).2
  let a := t + 1 - P
  have haT : T ≤ a := by dsimp [a]; omega
  have haN : N ≤ a := by dsimp [a]; omega
  obtain ⟨s, hs, hblack⟩ := black_in_period hP hp a haT
  have hst : a + s ≤ t := by dsimp [a] at *; omega
  obtain ⟨j, hj, hb, hw⟩ := last_black_prefix (fun i => center (a + s + i)) (t - (a + s))
    (by simpa only [Nat.add_zero] using hblack)
    (by simpa only [show a + s + (t - (a + s)) = t by omega] using hwhite)
  let b := a + s + j
  let r := t - b
  have hbN : N ≤ b := by dsimp [b]; omega
  have hbT : T ≤ b := by dsimp [b]; omega
  have hbr : b + r = t := by dsimp [b, r]; omega
  have hr : 0 < r := by dsimp [b, r]; omega
  have hrP : r < P := by dsimp [a, b, r] at *; omega
  have hwb : WhiteCenterGap b r := by
    intro i hi hir
    have hh := hw (j + i) (by omega) (by dsimp [b, r] at hir; omega)
    simpa only [Rule30UOR.Scale.center_eq_kit, Nat.add_assoc, b] using hh
  have win : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + m * P) (r + 1) := by
    intro i _hi
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (periodic_mul hp m (b + i) (by omega)).symm
  have hbc : Rule30UOR.Core.center b = true := by
    simpa only [Rule30UOR.Scale.center_eq_kit, b] using hb
  obtain ⟨k, hk, hl, hf, hge⟩ := black_gap_erasure_origin (m * P) b r g hr win hbc hwb
    (by simpa only [hbr] using he) (by simpa only [hbr] using hgate)
  refine ⟨b, k, hbN, by omega, hbc, ?_, hl, hf, hge⟩
  intro i hi hik
  exact hwb i hi (by omega)

/-! ## Return across black phases retains the deeper right input

The effective input is (!head) && next. It is a physical signal of the same
seed orbit, not an independent driver. The white-center convexity argument
cannot discard it when passing from one black boundary to the next.
-/

def rightCell (t k : Nat) : Bool := cell t (k : Int)
def rightDefect (Q t k : Nat) : Bool := xor (rightCell (t + Q) k) (rightCell t k)
def rightPhase (Q t k : Nat) : Int := bitValue (rightCell (t + Q) k) - bitValue (rightCell t k)
def rightImport (t : Nat) : Bool := (!rightCell t 1) && rightCell t 2
def rightImportDifference (Q t : Nat) : Bool := difference rightImport Q t

/-- Exact XOR decomposition of the head update with its masked deeper input. -/
theorem right_import_step (t : Nat) :
    rightCell (t + 1) 1 = Rule30UOR.Core.bxor (Rule30UOR.Core.center t)
      (Rule30UOR.Core.bxor (rightCell t 1) (rightImport t)) := by
  simp only [Rule30UOR.Scale.bxor_eq]
  rw [Rule30UOR.Scale.center_eq_kit]
  change rule (cell t 0) (cell t 1) (cell t 2) =
    xor (cell t 0) (xor (cell t 1) ((!cell t 1) && cell t 2))
  cases cell t 0 <;> cases cell t 1 <;> cases cell t 2 <;> rfl

/-- With the common center retained, the import difference is exactly the
change of the head defect. The mask still contains both physical backgrounds. -/
theorem right_defect_import_balance (Q t : Nat)
    (hc : Rule30UOR.Core.center (t + Q) = Rule30UOR.Core.center t) :
    rightDefect Q (t + 1) 1 = Rule30UOR.Core.bxor (rightDefect Q t 1) (rightImportDifference Q t) := by
  simp only [rightDefect, rightImportDifference, difference]
  rw [show t + 1 + Q = (t + Q) + 1 by omega, right_import_step, right_import_step, hc]
  simp only [Rule30UOR.Scale.bxor_eq]
  cases Rule30UOR.Core.center t <;> cases rightCell t 1 <;> cases rightCell (t + Q) 1 <;>
    cases rightImport t <;> cases rightImport (t + Q) <;> rfl

private theorem black_reset_table : ∀ a b c d : Bool,
    (xor b a = true → xor (rule true b d) (rule true a c) = true →
      bitValue (rule true b d) - bitValue (rule true a c) = -(bitValue b - bitValue a)) ∧
    (xor b a = false → xor (rule true b d) (rule true a c) = true →
      a = false ∧ b = false ∧ xor d c = true ∧
      bitValue (rule true b d) - bitValue (rule true a c) = -(bitValue d - bitValue c)) := by
  unfold rule bitValue
  decide +kernel

private theorem black_reset_physical (Q t : Nat)
    (hb : Rule30UOR.Core.center t = true) (hb' : Rule30UOR.Core.center (t + Q) = true) :
    (rightDefect Q t 1 = true → rightDefect Q (t + 1) 1 = true →
      rightPhase Q (t + 1) 1 = -rightPhase Q t 1) ∧
    (rightDefect Q t 1 = false → rightDefect Q (t + 1) 1 = true →
      rightCell t 1 = false ∧ rightCell (t + Q) 1 = false ∧ rightDefect Q t 2 = true ∧
      rightPhase Q (t + 1) 1 = -rightPhase Q t 2) := by
  have h0 : cell t 0 = true := by
    simpa only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] using hb
  have h0' : cell (t + Q) 0 = true := by
    simpa only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] using hb'
  have step0 : rightCell (t + 1) 1 = rule true (rightCell t 1) (rightCell t 2) := by
    change rule (cell t 0) (cell t 1) (cell t 2) = _
    rw [h0]
    rfl
  have step1 : rightCell (t + 1 + Q) 1 =
      rule true (rightCell (t + Q) 1) (rightCell (t + Q) 2) := by
    rw [show t + 1 + Q = (t + Q) + 1 by omega]
    change rule (cell (t + Q) 0) (cell (t + Q) 1) (cell (t + Q) 2) = _
    rw [h0']
    rfl
  simp only [rightDefect, rightPhase, step0, step1]
  exact black_reset_table (rightCell t 1) (rightCell (t + Q) 1) (rightCell t 2) (rightCell (t + Q) 2)

/-- An existing head disagreement that survives a common black step reverses
its signed orientation. No restriction on column 2 was imposed. -/
theorem black_reset_survival (Q t : Nat)
    (hb : Rule30UOR.Core.center t = true) (hb' : Rule30UOR.Core.center (t + Q) = true)
    (hd : rightDefect Q t 1 = true) (hn : rightDefect Q (t + 1) 1 = true) :
    rightPhase Q (t + 1) 1 = -rightPhase Q t 1 :=
  (black_reset_physical Q t hb hb').1 hd hn

/-- A new head disagreement at a common black step is imported from column 2
through a common white head. Its signed orientation also reverses. -/
theorem black_reset_import (Q t : Nat)
    (hb : Rule30UOR.Core.center t = true) (hb' : Rule30UOR.Core.center (t + Q) = true)
    (hd : rightDefect Q t 1 = false) (hn : rightDefect Q (t + 1) 1 = true) :
    rightCell t 1 = false ∧ rightCell (t + Q) 1 = false ∧ rightDefect Q t 2 = true ∧
      rightPhase Q (t + 1) 1 = -rightPhase Q t 2 :=
  (black_reset_physical Q t hb hb').2 hd hn

private theorem right_head_derivative (t : Nat) :
    difference (fun u => rightCell u 1) 1 t = xor (Rule30UOR.Core.center t) (rightImport t) := by
  simp only [difference]
  rw [right_import_step]
  simp only [Rule30UOR.Scale.bxor_eq]
  cases Rule30UOR.Core.center t <;> cases rightCell t 1 <;> cases rightImport t <;> rfl

private theorem right_import_nonperiodic {T P : Nat} (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : ¬ EventuallyPeriodic rightImport := by
  intro hi
  have hp : EventuallyPeriodic (Rule30UOR.Core.center) := ⟨T, P, hP, hc⟩
  obtain ⟨U, R, hR, hpc, hpi⟩ := common_period hp hi
  have hder : EventuallyPeriodic (difference (fun u => rightCell u 1) 1) := by
    refine ⟨U, R, hR, fun t ht => ?_⟩
    rw [right_head_derivative, right_head_derivative, hpc t ht, hpi t ht]
  have hhead := (difference_eventuallyPeriodic_iff (fun u => rightCell u 1) 1 (by decide)).1 hder
  have hc' : EventuallyPeriodic center := ⟨T, P, hP, fun t ht => by
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht⟩
  exact jen 1 0 (by decide) ⟨by simpa only [rightCell, Int.natCast_one] using hhead, hc'⟩

/-- Both orientations of the actual gated column-2 input occur arbitrarily late
for every positive period multiple. Each changes the head defect on that step;
thus a periodic center cannot make this return input periodic or discard it. -/
theorem periodic_right_import_orientation (T P m N : Nat) (before : Bool)
    (hP : 0 < P) (hm : 0 < m) (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∃ t : Nat, N ≤ t ∧ rightImport t = before ∧ rightImport (t + m * P) = !before ∧
      rightDefect (m * P) (t + 1) 1 = !rightDefect (m * P) t 1 := by
  have hf := right_import_nonperiodic hP hc
  have hex : ∃ t : Nat, max T N ≤ t ∧ rightImport t = before ∧
      rightImport (t + m * P) = !before := by
    cases before
    · exact nonperiodic_has_rise rightImport hf (m * P) (max T N) (Nat.mul_pos hm hP)
    · exact nonperiodic_has_fall rightImport hf (m * P) (max T N) (Nat.mul_pos hm hP)
  obtain ⟨t, ht, h0, h1⟩ := hex
  have hd : rightImportDifference (m * P) t = true := by
    simp only [rightImportDifference, difference, h0, h1]
    cases before <;> rfl
  have hc0 := Rule30UOR.Scale.center_mul hc m t (by omega)
  have hs := right_defect_import_balance (m * P) t hc0
  rw [Rule30UOR.Scale.bxor_eq, hd] at hs
  refine ⟨t, by omega, h0, h1, ?_⟩
  simpa only [Bool.xor_true] using hs

/-! ## A joint history from the deeper right input to a left-source erasure -/

/-- The sign accumulated from actual common-center values, including black
resets. No periodicity or cancellation of this product is assumed. -/
def centerSign (start : Nat) : Nat → Int
  | 0 => 1
  | n + 1 => (1 - 2 * bitValue (Rule30UOR.Core.center start)) * centerSign (start + 1) n

/-- A physical birth of a head defect followed without interruption to finish.
The input is at column 2 of the same pair, through a common white head. -/
def HeadImportPath (Q start finish : Nat) : Prop :=
  start < finish ∧ rightDefect Q start 1 = false ∧
    rightCell start 1 = false ∧ rightCell (start + Q) 1 = false ∧
    rightDefect Q start 2 = true ∧ rightImportDifference Q start = true ∧
    ∀ s : Nat, start < s → s ≤ finish → rightDefect Q s 1 = true

private theorem head_birth_table : ∀ c a b r s : Bool,
    xor b a = false → xor (rule c b s) (rule c a r) = true →
      a = false ∧ b = false ∧ xor s r = true ∧
        xor ((!b) && s) ((!a) && r) = true ∧
        bitValue (rule c b s) - bitValue (rule c a r) =
          (1 - 2 * bitValue c) * (bitValue s - bitValue r) := by
  unfold rule bitValue
  decide +kernel

private theorem head_survival_table : ∀ c a b r s : Bool,
    xor b a = true → xor (rule c b s) (rule c a r) = true →
      bitValue (rule c b s) - bitValue (rule c a r) =
        (1 - 2 * bitValue c) * (bitValue b - bitValue a) := by
  unfold rule bitValue
  decide +kernel

private theorem right_head_next (t : Nat) :
    rightCell (t + 1) 1 = rule (Rule30UOR.Core.center t) (rightCell t 1) (rightCell t 2) := by
  rw [Rule30UOR.Scale.center_eq_kit]
  rfl

/-- A birth at either center color imports a column-2 unit through white heads.
Black centers reverse its sign; white centers preserve it. -/
theorem right_head_birth (Q t : Nat)
    (hc : Rule30UOR.Core.center (t + Q) = Rule30UOR.Core.center t)
    (hd : rightDefect Q t 1 = false) (hn : rightDefect Q (t + 1) 1 = true) :
    rightCell t 1 = false ∧ rightCell (t + Q) 1 = false ∧ rightDefect Q t 2 = true ∧
      rightImportDifference Q t = true ∧
      rightPhase Q (t + 1) 1 = (1 - 2 * bitValue (Rule30UOR.Core.center t)) * rightPhase Q t 2 := by
  have next : rightCell (t + 1 + Q) 1 =
      rule (Rule30UOR.Core.center t) (rightCell (t + Q) 1) (rightCell (t + Q) 2) := by
    rw [show t + 1 + Q = (t + Q) + 1 by omega, right_head_next, hc]
  have hb := head_birth_table (Rule30UOR.Core.center t) (rightCell t 1)
    (rightCell (t + Q) 1) (rightCell t 2) (rightCell (t + Q) 2)
    hd (by simpa only [rightDefect, next, right_head_next] using hn)
  simpa only [rightDefect, rightImportDifference, difference, rightImport, rightPhase,
    next, right_head_next] using hb

private theorem right_head_survival (Q t : Nat)
    (hc : Rule30UOR.Core.center (t + Q) = Rule30UOR.Core.center t)
    (hd : rightDefect Q t 1 = true) (hn : rightDefect Q (t + 1) 1 = true) :
    rightPhase Q (t + 1) 1 = (1 - 2 * bitValue (Rule30UOR.Core.center t)) * rightPhase Q t 1 := by
  have next : rightCell (t + 1 + Q) 1 =
      rule (Rule30UOR.Core.center t) (rightCell (t + Q) 1) (rightCell (t + Q) 2) := by
    rw [show t + 1 + Q = (t + Q) + 1 by omega, right_head_next, hc]
  have hh := head_survival_table (Rule30UOR.Core.center t) (rightCell t 1)
    (rightCell (t + Q) 1) (rightCell t 2) (rightCell (t + Q) 2)
    hd (by simpa only [rightDefect, next, right_head_next] using hn)
  simpa only [rightPhase, next, right_head_next] using hh

private theorem right_head_transport (Q : Nat) : ∀ n start : Nat,
    (∀ s : Nat, s ≤ n → Rule30UOR.Core.center (start + s + Q) = Rule30UOR.Core.center (start + s)) →
    (∀ s : Nat, s ≤ n → rightDefect Q (start + s) 1 = true) →
      rightPhase Q (start + n) 1 = centerSign start n * rightPhase Q start 1 := by
  intro n
  induction n with
  | zero => intro start _ _; simp [centerSign]
  | succ n ih =>
    intro start hc hd
    have step := right_head_survival Q start (by simpa only [Nat.add_zero] using hc 0 (by omega))
      (by simpa only [Nat.add_zero] using hd 0 (by omega))
      (by simpa only [Nat.add_zero] using hd 1 (by omega))
    have tail := ih (start + 1) (fun s hs => by
      simpa only [Nat.add_assoc] using hc (1 + s) (by omega))
      (fun s hs => by simpa only [Nat.add_assoc] using hd (1 + s) (by omega))
    rw [show start + (n + 1) = start + 1 + n by omega, tail, step]
    simp only [centerSign, Int.mul_assoc, Int.mul_left_comm]

private theorem clean_center_core (Q start n : Nat) (hc : CenterCleanThrough Q start n)
    (s : Nat) (hs : s ≤ n) :
    Rule30UOR.Core.center (start + s + Q) = Rule30UOR.Core.center (start + s) := by
  have hh := (difference_eq_false_iff (fun u => cell u 0) Q (start + s)).1 (by
    simpa only [leftDefect, defect, Int.natCast_zero, Int.neg_zero] using hc s hs)
  simpa only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] using hh

/-- The exact phase carried from the column-2 birth to this same erasure time. -/
theorem head_import_path_phase (Q start finish : Nat) (hp : HeadImportPath Q start finish)
    (hc : CenterCleanThrough Q start (finish - start)) :
    rightPhase Q finish 1 = centerSign start (finish - start) * rightPhase Q start 2 := by
  obtain ⟨hlt, hzero, _hwhite, _hwhite', _hdeep, _himport, hpath⟩ := hp
  have birth := (right_head_birth Q start
    (by simpa only [Nat.add_zero] using clean_center_core Q start (finish - start) hc 0 (by omega))
    hzero (hpath (start + 1) (by omega) (by omega))).2.2.2.2
  have tail := right_head_transport Q (finish - start - 1) (start + 1)
    (fun s hs => by
      simpa only [Nat.add_assoc] using
        clean_center_core Q start (finish - start) hc (1 + s) (by omega))
    (fun s hs => hpath (start + 1 + s) (by omega) (by omega))
  rw [show start + 1 + (finish - start - 1) = finish by omega, birth] at tail
  rw [show finish - start = (finish - start - 1) + 1 by omega]
  simpa only [centerSign, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using tail

private theorem common_xor_phase : ∀ c a b : Bool,
    bitValue (xor c b) - bitValue (xor c a) =
      (1 - 2 * bitValue c) * (bitValue b - bitValue a) := by
  unfold bitValue
  decide +kernel

/-- At a common white center, the two incoming signed phases match with the
actual next center color determining the sign. -/
theorem white_center_phase_matching (Q t : Nat)
    (hc0 : leftDefect Q t 0 = false) (hc1 : leftDefect Q (t + 1) 0 = false)
    (hw : Rule30UOR.Core.center t = false) :
    leftPhase Q t 1 = (1 - 2 * bitValue (Rule30UOR.Core.center (t + 1))) * rightPhase Q t 1 := by
  have window0 : CenterCleanThrough Q t 0 := by
    intro s hs
    have he : s = 0 := by omega
    simpa only [he, Nat.add_zero] using hc0
  have window1 : CenterCleanThrough Q (t + 1) 0 := by
    intro s hs
    have he : s = 0 := by omega
    simpa only [he, Nat.add_zero] using hc1
  have same0 := clean_center_core Q t 0 window0 0 (Nat.le_refl _)
  have same1 := clean_center_core Q (t + 1) 0 window1 0 (Nat.le_refl _)
  simp only [Nat.add_zero, Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] at same0 same1 hw
  have white' : cell (t + Q) 0 = false := same0.trans hw
  have hl := cell_left t 0
  have hl' := cell_left (t + Q) 0
  simp only [show (0 : Int) - 1 = -1 by omega, show (0 : Int) + 1 = 1 by omega,
    hw, white', Bool.false_or] at hl hl'
  rw [show t + Q + 1 = t + 1 + Q by omega, same1] at hl'
  simp only [leftPhase, phase, rightPhase, rightCell, Int.natCast_one,
    Rule30UOR.Scale.center_eq_kit, Rule30Prize.center]
  rw [hl, hl']
  exact common_xor_phase (cell (t + 1) 0) (cell t 1) (cell (t + Q) 1)

/-- A late right import, its uninterrupted head path, and a particular left
leading source are coupled at the same first erasure, with exact signed balance.
Neither side is selected independently of the other. -/
theorem periodic_coupled_cancellation (T P m N g : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hg : g = 2 ∨ g = 5) :
    ∃ start b k : Nat, N ≤ start ∧ N ≤ b ∧ k ≤ P ∧ Rule30UOR.Core.center b = true ∧
      WhiteCenterGap b (k - 1) ∧ LeadingAdvance (m * P) b k ∧
      FirstPathErasure (m * P) b k (k - 2) ∧ gateCode (m * P) (b + (k - 1)) 0 = g ∧
      HeadImportPath (m * P) start (b + (k - 1)) ∧
      leftPhase (m * P) b k + pathFlux (m * P) b k (k - 1) =
        (1 - 2 * bitValue (Rule30UOR.Core.center (b + k))) *
          centerSign start (b + (k - 1) - start) * rightPhase (m * P) start 2 := by
  have hp : ∀ t, T ≤ t → center (t + P) = center t := by
    intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht
  have hper : EventuallyPeriodic center := ⟨T, P, hP, hp⟩
  obtain ⟨v, hv, hzero⟩ := exists_defect_false_of_periodic hper (m * P) (Nat.mul_pos hm hP)
    1 (by decide) (max T N)
  have hz : rightDefect (m * P) v 1 = false := hzero
  obtain ⟨b, k, hbv, hkP, hb, hw, hl, hf, hgate⟩ :=
    periodic_black_erasure_origin T P m (v + 1) g hP hm hc hg
  have hk2 := hl.1
  let finish := b + (k - 1)
  have clean : ∀ t : Nat, T ≤ t → leftDefect (m * P) t 0 = false := by
    intro t ht
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using center_defect_zero hp m t ht
  obtain ⟨_hf, he, _hg, hwhite⟩ := leading_first_erasure (m * P) b k hl
    (fun s _hs => clean (b + s) (by omega))
  have hend : rightDefect (m * P) finish 1 = true := by
    have hh := (defect_right_and_white_of_clean_pair (m * P) finish 0
      (clean finish (by dsimp [finish]; omega))
      (clean (finish + 1) (by dsimp [finish]; omega)) he.1).1
    exact hh
  obtain ⟨j, hj, hzj, hpath⟩ := last_black_prefix (fun s => !rightDefect (m * P) (v + s) 1)
    (finish - v) (by simp only [Nat.add_zero, hz, Bool.not_false])
    (by simp only [show v + (finish - v) = finish by dsimp [finish]; omega, hend, Bool.not_true])
  let start := v + j
  have hstart : start < finish := by dsimp [start]; omega
  have hzstart : rightDefect (m * P) start 1 = false := by
    cases hh : rightDefect (m * P) start 1 <;> simp_all [start]
  have persist : ∀ s : Nat, start < s → s ≤ finish → rightDefect (m * P) s 1 = true := by
    intro s hs hsf
    have hh := hpath (s - v) (by dsimp [start] at hs; omega) (by omega)
    rw [show v + (s - v) = s by dsimp [start] at hs; omega] at hh
    cases hd : rightDefect (m * P) s 1 <;> simp_all
  have hbirth := right_head_birth (m * P) start (Rule30UOR.Scale.center_mul hc m start
    (by dsimp [start]; omega)) hzstart (persist (start + 1) (by omega) (by omega))
  have path : HeadImportPath (m * P) start finish :=
    ⟨hstart, hzstart, hbirth.1, hbirth.2.1, hbirth.2.2.1, hbirth.2.2.2.1, persist⟩
  have transported := head_import_path_phase (m * P) start finish path (fun s _hs =>
    clean (start + s) (by dsimp [start]; omega))
  have matched := white_center_phase_matching (m * P) finish
    (clean finish (by dsimp [finish]; omega))
    (clean (finish + 1) (by dsimp [finish]; omega)) hwhite
  have leftpath := path_balance (m * P) b k (k - 1)
  have leftphase : leftPhase (m * P) finish 1 =
      leftPhase (m * P) b k + pathFlux (m * P) b k (k - 1) := by
    simpa only [pathPhase, leftPhase, finish, Int.natCast_one,
      show -(k : Int) + ((k - 1 : Nat) : Int) = -1 by omega] using leftpath
  refine ⟨start, b, k, by dsimp [start]; omega, by omega, hkP, hb, hw, hl, hf, hgate, path, ?_⟩
  rw [← leftphase, matched, transported]
  simp only [finish, show b + (k - 1) + 1 = b + k by omega, Int.mul_assoc]

/-! ## Sign and seed-boundary audit of proposed closing arguments -/

private theorem white_gate_phase (Q t : Nat) (hc : leftDefect Q t 0 = false)
    (hw : Rule30UOR.Core.center t = false) : leftGatePhase Q t 0 = rightPhase Q t 1 := by
  have same := (difference_eq_false_iff (fun u => cell u 0) Q t).1 (by
    simpa only [leftDefect, defect, Int.natCast_zero, Int.neg_zero] using hc)
  have hw0 : cell t 0 = false := by
    simpa only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] using hw
  have hw1 : cell (t + Q) 0 = false := same.trans hw0
  simp only [leftGatePhase, gatePhase, rightPhase, rightCell, Int.natCast_zero, Int.neg_zero,
    Int.zero_add, Int.natCast_one, hw0, hw1, Bool.false_or]

/-- The reset color multiplies the gate phase at the same physical arrival. -/
theorem leading_arrival_phase_eq_gate_phase (Q b k : Nat)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k) :
    leftPhase Q b k + pathFlux Q b k (k - 1) =
      (1 - 2 * bitValue (Rule30UOR.Core.center (b + k))) * leftGatePhase Q (b + (k - 1)) 0 := by
  obtain ⟨_hf, _he, _hg, hw⟩ := leading_first_erasure Q b k hl hc
  have hk := hl.1
  have h0 := hc (k - 1) (by omega)
  have h1 : leftDefect Q (b + (k - 1) + 1) 0 = false := by
    simpa only [show b + (k - 1) + 1 = b + k by omega] using hc k (Nat.le_refl _)
  have matching := white_center_phase_matching Q (b + (k - 1)) h0 h1 hw
  rw [← white_gate_phase Q (b + (k - 1)) h0 hw] at matching
  have path : leftPhase Q (b + (k - 1)) 1 = leftPhase Q b k + pathFlux Q b k (k - 1) := by
    simpa only [pathPhase, leftPhase, Int.natCast_one,
      show -(k : Int) + ((k - 1 : Nat) : Int) = -1 by omega] using path_balance Q b k (k - 1)
  simpa only [show b + (k - 1) + 1 = b + k by omega] using path.symm.trans matching

/-- With the stated phase conventions there is no extra minus sign at a white
center: the OR-gate phase is the transported right-head phase itself. -/
theorem head_import_path_gate_phase (Q start finish : Nat)
    (hp : HeadImportPath Q start finish) (hc : CenterCleanThrough Q start (finish - start))
    (hw : Rule30UOR.Core.center finish = false) :
    leftGatePhase Q finish 0 = centerSign start (finish - start) * rightPhase Q start 2 := by
  have hlt := hp.1
  have hfinish : leftDefect Q finish 0 = false := by
    simpa only [show start + (finish - start) = finish by omega] using
      hc (finish - start) (Nat.le_refl _)
  rw [white_gate_phase Q finish hfinish hw]
  exact head_import_path_phase Q start finish hp hc

/-- Reversing that sign is incompatible with an actual nonzero import path,
without assuming a periodic center. It cannot be used as an unproved local law. -/
theorem head_import_path_rejects_negative_gate (Q start finish : Nat)
    (hp : HeadImportPath Q start finish) (hc : CenterCleanThrough Q start (finish - start))
    (hw : Rule30UOR.Core.center finish = false) :
    leftGatePhase Q finish 0 ≠ -(centerSign start (finish - start) * rightPhase Q start 2) := by
  have positive := head_import_path_gate_phase Q start finish hp hc hw
  have phase_at_end := head_import_path_phase Q start finish hp hc
  have hd := hp.2.2.2.2.2.2 finish hp.1 (Nat.le_refl _)
  have nonzero : rightPhase Q finish 1 ≠ 0 := by
    intro hz
    simp only [rightDefect] at hd
    simp only [rightPhase] at hz
    cases ha : rightCell finish 1 <;> cases hb : rightCell (finish + Q) 1 <;> simp_all [bitValue]
  intro negative
  apply nonzero
  omega

/-- The coupled gate balance has the positive transport sign for either
recurring erasure orientation. The closing minus-sign assertion is not a
consequence of the coupled witness or its phase conventions. -/
theorem periodic_coupled_gate_phase_sign (T P m N g : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hg : g = 2 ∨ g = 5) :
    ∃ start b k : Nat, N ≤ start ∧ N ≤ b ∧ k ≤ P ∧ Rule30UOR.Core.center b = true ∧
      WhiteCenterGap b (k - 1) ∧ LeadingAdvance (m * P) b k ∧
      FirstPathErasure (m * P) b k (k - 2) ∧ gateCode (m * P) (b + (k - 1)) 0 = g ∧
      HeadImportPath (m * P) start (b + (k - 1)) ∧
      leftGatePhase (m * P) (b + (k - 1)) 0 =
        centerSign start (b + (k - 1) - start) * rightPhase (m * P) start 2 := by
  obtain ⟨start, b, k, hs, hb, hk, hblack, hwhite, hl, hf, hgate, path, _balance⟩ :=
    periodic_coupled_cancellation T P m (max T N) g hP hm hc hg
  have hp : ∀ t, T ≤ t → center (t + P) = center t := by
    intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht
  have clean : ∀ t n : Nat, T ≤ t → CenterCleanThrough (m * P) t n := by
    intro t n ht s _hbound
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using center_defect_zero hp m (t + s) (by omega)
  obtain ⟨_hf, _he, _hg, hw⟩ := leading_first_erasure (m * P) b k hl (clean b k (by omega))
  exact ⟨start, b, k, by omega, by omega, hk, hblack, hwhite, hl, hf, hgate, path,
    head_import_path_gate_phase (m * P) start (b + (k - 1)) path
      (clean start (b + (k - 1) - start) (by omega)) hw⟩

/-- On the doubled-lag seed characteristic the smaller-lag fluxes are 0 and
-1, not two copies of -1. The first component starts outside both seed cones. -/
theorem periodic_doubled_seed_flux_split (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    pathFlux (m * P + m * P) N (N + (m * P + m * P)) (N + (m * P + m * P)) = -1 ∧
    pathFlux (m * P) N (N + (m * P + m * P)) (N + (m * P + m * P)) = 0 ∧
    pathFlux (m * P) (N + m * P) (N + (m * P + m * P)) (N + (m * P + m * P)) = -1 := by
  have hQ := Nat.mul_pos hm hP
  let extent := N + (m * P + m * P)
  have initial : leftPhase (m * P) N extent = 0 := by
    unfold leftPhase phase
    rw [cell_eq_false_of_lt (N + m * P) _ (by dsimp [extent]; omega),
      cell_eq_false_of_lt N _ (by dsimp [extent]; omega)]
    rfl
  have hz : leftPhase (m * P) (N + extent) 0 = 0 := by
    apply (phase_zero_iff (m * P) (N + extent) 0).2
    have hp : ∀ t, T ≤ t → center (t + P) = center t := by
      intro t ht
      simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using center_defect_zero hp m (N + extent) (by omega)
  have balance : leftPhase (m * P) (N + extent) 0 =
      leftPhase (m * P) N extent + pathFlux (m * P) N extent extent := by
    simpa only [pathPhase, leftPhase, Int.natCast_zero, Int.neg_zero,
      show -(extent : Int) + (extent : Int) = 0 by omega] using path_balance (m * P) N extent extent
  have first : pathFlux (m * P) N extent extent = 0 := by omega
  have second : pathFlux (m * P) (N + m * P) extent extent = -1 := by
    simpa only [extent, Nat.add_assoc] using periodic_seed_flux T P m (N + m * P) hP hm hc (by omega)
  have split := path_flux_lag_add (m * P) (m * P) N extent extent
  have total : pathFlux (m * P + m * P) N extent extent = -1 := by omega
  exact ⟨total, first, second⟩

/-- A finite kernel certificate for the positive transport sign in an actual
seeded cancellation. This is not a counterexample to a periodic-center premise;
it refutes the proposed unconditional local negative-sign extension. -/
theorem seed_coupled_gate_sign :
    LeadingAdvance 11 4 4 ∧ CenterCleanThrough 11 4 4 ∧
    HeadImportPath 11 6 7 ∧ CenterCleanThrough 11 6 1 ∧
    leftGatePhase 11 7 0 = 1 ∧ centerSign 6 1 = 1 ∧ rightPhase 11 6 2 = 1 := by
  obtain ⟨hl, hc, hg, _hreset⟩ := seed_leading_black_reset
  have data : rightCell 6 1 = false ∧ rightCell 17 1 = false ∧
      rightCell 7 1 = false ∧ rightCell 18 1 = true ∧
      rightCell 6 2 = false ∧ rightCell 17 2 = true := by
    simp only [rightCell, Int.natCast_one, show ((2 : Nat) : Int) = 2 by omega]
    rw [cell_as_row 6 1 (by omega), cell_as_row 17 1 (by omega),
      cell_as_row 7 1 (by omega), cell_as_row 18 1 (by omega),
      cell_as_row 6 2 (by omega), cell_as_row 17 2 (by omega)]
    decide +kernel
  have hd : rightDefect 11 6 1 = false := by simp [rightDefect, data.1, data.2.1]
  have hn : rightDefect 11 7 1 = true := by simp [rightDefect, data.2.2.1, data.2.2.2.1]
  have hc' : CenterCleanThrough 11 6 1 := by
    intro s hs
    simpa only [show 4 + (2 + s) = 6 + s by omega] using hc (2 + s) (by omega)
  have birth := right_head_birth 11 6
    (by simpa only [Nat.add_zero] using clean_center_core 11 6 1 hc' 0 (by omega)) hd hn
  have path : HeadImportPath 11 6 7 := by
    refine ⟨by omega, hd, birth.1, birth.2.1, birth.2.2.1, birth.2.2.2.1, ?_⟩
    intro s h6 h7
    simpa only [show s = 7 by omega] using hn
  have hw6 : Rule30UOR.Core.center 6 = false := by
    obtain ⟨hl4, hc4, _hg4⟩ := seed_leading_gate_five
    exact (leading_first_erasure 4 5 2 hl4 hc4).2.2.2
  refine ⟨hl, hc, path, hc', (gate_phase_cases 11 7 0).2.2.2.2.1 hg, ?_, ?_⟩
  · simp [centerSign, hw6, bitValue]
  · simp [rightPhase, data.2.2.2.2.1, data.2.2.2.2.2, bitValue]

/-! ## Ancestry of imports: forced lineages, fronts, and the seed boundary

No defect appears from a clean neighbourhood. Every actual defect therefore has a
nearest-neighbour lineage of actual defects reaching the seed row, where the defects
are exactly the cells in which row `Q` differs from the single black cell. A clean
column is a one-way barrier for lineages. The leftmost right-half defect moves left by
at most one column per step, and only through a common white cell. These are exact
statements about the seeded pair; none assumes a periodic center.
-/

private theorem cell_eq_false_of_gt : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, h => by
    show decide (p = 0) = false
    simp only [decide_eq_false_iff_not]
    omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_gt t (p - 1) (by omega), cell_eq_false_of_gt t p (by omega),
      cell_eq_false_of_gt t (p + 1) (by omega)]
    rfl

private theorem cell_right_edge : ∀ t : Nat, cell t (t : Int) = true
  | 0 => rfl
  | t + 1 => by
    show rule (cell t (((t + 1 : Nat) : Int) - 1)) (cell t ((t + 1 : Nat) : Int))
      (cell t (((t + 1 : Nat) : Int) + 1)) = true
    rw [show ((t + 1 : Nat) : Int) - 1 = (t : Int) by omega, cell_right_edge t,
      cell_eq_false_of_gt t _ (by omega), cell_eq_false_of_gt t _ (by omega)]
    rfl

theorem rightDefect_eq_defect (Q t j : Nat) : rightDefect Q t j = defect Q t (j : Int) := rfl

/-- The exact one-step ancestry table. The next defect is the incoming left defect
XOR the gate difference, and the gate difference is fixed by which of `p, p+1`
are defective together with the earlier colours there. -/
theorem ancestry_gate_table (Q t : Nat) (p : Int) :
    (defect Q t p = false → defect Q t (p + 1) = false → gateDifference Q t p = false) ∧
    (defect Q t p = true → defect Q t (p + 1) = false →
      gateDifference Q t p = !cell t (p + 1)) ∧
    (defect Q t p = false → defect Q t (p + 1) = true →
      gateDifference Q t p = !cell t p) ∧
    (defect Q t p = true → defect Q t (p + 1) = true →
      gateDifference Q t p = (cell t p == cell t (p + 1))) := by
  unfold defect difference gateDifference
  dsimp only
  cases cell t p <;> cases cell (t + Q) p <;> cases cell t (p + 1) <;>
    cases cell (t + Q) (p + 1) <;> decide

/-- Defects are never created from a clean neighbourhood. -/
theorem defect_has_ancestor (Q t : Nat) (p : Int) (h : defect Q (t + 1) p = true) :
    defect Q t (p - 1) = true ∨ defect Q t p = true ∨ defect Q t (p + 1) = true := by
  cases h1 : defect Q t (p - 1)
  · cases h2 : defect Q t p
    · cases h3 : defect Q t (p + 1)
      · rw [defect_step_gate, h1, (ancestry_gate_table Q t p).1 h2 h3] at h
        exact absurd h (by decide)
      · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-- The right-half form of `defect_has_ancestor`; column `0` is the center. -/
theorem right_defect_has_ancestor (Q t j : Nat) (h : rightDefect Q (t + 1) (j + 1) = true) :
    rightDefect Q t j = true ∨ rightDefect Q t (j + 1) = true ∨
      rightDefect Q t (j + 2) = true := by
  have hh := defect_has_ancestor Q t ((j + 1 : Nat) : Int) h
  simpa only [rightDefect_eq_defect, show ((j + 1 : Nat) : Int) - 1 = (j : Int) by omega,
    show ((j + 1 : Nat) : Int) + 1 = ((j + 2 : Nat) : Int) by omega] using hh

/-- A nearest-neighbour backward lineage of actual defects. -/
def AncestryPath (Q t : Nat) (p : Int) (f : Nat → Int) : Prop :=
  f t = p ∧ (∀ s : Nat, s < t → f s - 1 ≤ f (s + 1) ∧ f (s + 1) ≤ f s + 1) ∧
    ∀ s : Nat, s ≤ t → defect Q s (f s) = true

/-- Every actual defect has a lineage reaching the seed row. -/
theorem defect_ancestry (Q : Nat) : ∀ (t : Nat) (p : Int), defect Q t p = true →
    ∃ f : Nat → Int, AncestryPath Q t p f := by
  intro t
  induction t with
  | zero =>
    intro p h
    refine ⟨fun _ => p, rfl, fun s hs => absurd hs (Nat.not_lt_zero _), fun s hs => ?_⟩
    rw [Nat.le_zero.1 hs]
    exact h
  | succ t ih =>
    intro p h
    have hq : ∃ q : Int, p - 1 ≤ q ∧ q ≤ p + 1 ∧ defect Q t q = true := by
      rcases defect_has_ancestor Q t p h with h' | h' | h'
      · exact ⟨p - 1, by omega, by omega, h'⟩
      · exact ⟨p, by omega, by omega, h'⟩
      · exact ⟨p + 1, by omega, by omega, h'⟩
    obtain ⟨q, hq1, hq2, hqd⟩ := hq
    obtain ⟨f, hf0, hf1, hf2⟩ := ih q hqd
    refine ⟨fun s => if s ≤ t then f s else p, ?_, ?_, ?_⟩
    · simp only [show ¬ (t + 1 ≤ t) by omega, if_false]
    · intro s hs
      by_cases hst : s + 1 ≤ t
      · simp only [show s ≤ t by omega, hst, if_true]
        exact hf1 s (by omega)
      · have hs' : s = t := by omega
        rw [hs']
        simp only [Nat.le_refl, if_true, show ¬ (t + 1 ≤ t) by omega, if_false, hf0]
        omega
    · intro s hs
      by_cases hst : s ≤ t
      · simp only [hst, if_true]
        exact hf2 s hst
      · have hs' : s = t + 1 := by omega
        rw [hs']
        simp only [show ¬ (t + 1 ≤ t) by omega, if_false]
        exact h

/-- A lineage moves by at most one column per step. -/
theorem ancestry_displacement (Q t : Nat) (p : Int) (f : Nat → Int) (h : AncestryPath Q t p f) :
    ∀ s : Nat, s ≤ t → f s ≤ p + ((t - s : Nat) : Int) ∧ p - ((t - s : Nat) : Int) ≤ f s := by
  obtain ⟨hf0, hf1, _⟩ := h
  have key : ∀ j : Nat, j ≤ t → f (t - j) ≤ p + (j : Int) ∧ p - (j : Int) ≤ f (t - j) := by
    intro j
    induction j with
    | zero => intro _; simp only [Nat.sub_zero, hf0]; omega
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hstep := hf1 (t - (j + 1)) (by omega)
      rw [show t - (j + 1) + 1 = t - j by omega] at hstep
      omega
  intro s hs
  have := key (t - s) (by omega)
  rwa [show t - (t - s) = s by omega] at this

/-- **Seed terminal.** Every lineage ends at a seed-row defect: a cell of row `Q`
that differs from the single seed. Off the center it is black in row `Q` (signed
phase `+1`); at the center it is white in row `Q` (signed phase `-1`). It lies in
`[-Q, Q]`. -/
theorem ancestry_seed_terminal (Q t : Nat) (p : Int) (f : Nat → Int) (h : AncestryPath Q t p f) :
    -(Q : Int) ≤ f 0 ∧ f 0 ≤ (Q : Int) ∧
      ((f 0 = 0 ∧ cell Q 0 = false ∧ phase Q 0 0 = -1) ∨
        (f 0 ≠ 0 ∧ cell Q (f 0) = true ∧ phase Q 0 (f 0) = 1)) := by
  have hd := h.2.2 0 (Nat.zero_le _)
  have hd' : xor (cell Q (f 0)) (decide (f 0 = 0)) = true := by
    have h0 : cell 0 (f 0) = decide (f 0 = 0) := rfl
    simpa only [defect, difference, Nat.zero_add, h0] using hd
  refine ⟨?_, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hlt
    rw [cell_eq_false_of_lt Q (f 0) (by omega)] at hd'
    have : decide (f 0 = 0) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [this] at hd'
    exact absurd hd' (by decide)
  · apply Classical.byContradiction
    intro hlt
    rw [cell_eq_false_of_gt Q (f 0) (by omega)] at hd'
    have : decide (f 0 = 0) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [this] at hd'
    exact absurd hd' (by decide)
  · by_cases h0 : f 0 = 0
    · left
      rw [h0] at hd'
      have hc : cell Q 0 = false := by
        cases hq : cell Q 0
        · rfl
        · rw [hq] at hd'; exact absurd hd' (by decide)
      refine ⟨h0, hc, ?_⟩
      simp only [phase, Nat.zero_add, hc, bitValue]
      rfl
    · right
      have hz : decide (f 0 = 0) = false := by simp only [decide_eq_false_iff_not]; exact h0
      rw [hz] at hd'
      have hc : cell Q (f 0) = true := by simpa using hd'
      have hc0 : cell 0 (f 0) = false := by
        show decide (f 0 = 0) = false
        exact hz
      refine ⟨h0, hc, ?_⟩
      simp only [phase, Nat.zero_add, hc, hc0, bitValue]
      rfl

/-- **Barrier.** A column that is clean on `[T, t]` cannot be crossed by a lineage
there: a lineage strictly right of it at time `t` stays strictly right of it. -/
theorem ancestry_barrier_right (Q t T : Nat) (p c : Int) (f : Nat → Int)
    (h : AncestryPath Q t p f) (hp : c < p)
    (hc : ∀ s : Nat, T ≤ s → s ≤ t → defect Q s c = false) :
    ∀ s : Nat, T ≤ s → s ≤ t → c < f s := by
  obtain ⟨hf0, hf1, hf2⟩ := h
  have key : ∀ j : Nat, j ≤ t - T → c < f (t - j) := by
    intro j
    induction j with
    | zero => intro _; simpa only [Nat.sub_zero, hf0] using hp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hstep := hf1 (t - (j + 1)) (by omega)
      rw [show t - (j + 1) + 1 = t - j by omega] at hstep
      have hne : f (t - (j + 1)) ≠ c := by
        intro h0
        have := hf2 (t - (j + 1)) (by omega)
        rw [h0, hc (t - (j + 1)) (by omega) (by omega)] at this
        exact absurd this (by decide)
      omega
  intro s hs hst
  have := key (t - s) (by omega)
  rwa [show t - (t - s) = s by omega] at this

/-- The mirror barrier: a lineage strictly left of a clean column stays left of it. -/
theorem ancestry_barrier_left (Q t T : Nat) (p c : Int) (f : Nat → Int)
    (h : AncestryPath Q t p f) (hp : p < c)
    (hc : ∀ s : Nat, T ≤ s → s ≤ t → defect Q s c = false) :
    ∀ s : Nat, T ≤ s → s ≤ t → f s < c := by
  obtain ⟨hf0, hf1, hf2⟩ := h
  have key : ∀ j : Nat, j ≤ t - T → f (t - j) < c := by
    intro j
    induction j with
    | zero => intro _; simpa only [Nat.sub_zero, hf0] using hp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hstep := hf1 (t - (j + 1)) (by omega)
      rw [show t - (j + 1) + 1 = t - j by omega] at hstep
      have hne : f (t - (j + 1)) ≠ c := by
        intro h0
        have := hf2 (t - (j + 1)) (by omega)
        rw [h0, hc (t - (j + 1)) (by omega) (by omega)] at this
        exact absurd this (by decide)
      omega
  intro s hs hst
  have := key (t - s) (by omega)
  rwa [show t - (t - s) = s by omega] at this

/-- A right-half lineage: a lineage of actual defects from right column `j` at time
`t`, confined to the right half on `[T, t]`. Before `T` it may cross the center. -/
def RightLineage (Q t j T : Nat) : Prop :=
  ∃ f : Nat → Int, AncestryPath Q t (j : Int) f ∧ ∀ s : Nat, T ≤ s → s ≤ t → 1 ≤ f s

/-- A left-half lineage from depth `k` at time `t`, confined to the left half on `[T, t]`. -/
def LeftLineage (Q t k T : Nat) : Prop :=
  ∃ f : Nat → Int, AncestryPath Q t (-(k : Int)) f ∧ ∀ s : Nat, T ≤ s → s ≤ t → f s ≤ -1

/-- While the center is clean, every right-half defect descends from right-half
defects only. -/
theorem right_lineage_of_clean_center (Q t j T : Nat) (hj : 1 ≤ j) (hT : T ≤ t)
    (hd : rightDefect Q t j = true) (hc : CenterCleanThrough Q T (t - T)) :
    RightLineage Q t j T := by
  obtain ⟨f, hf⟩ := defect_ancestry Q t (j : Int) hd
  refine ⟨f, hf, fun s hs hst => ?_⟩
  have := ancestry_barrier_right Q t T (j : Int) 0 f hf (by omega) (fun s hs hst => by
    have hh := hc (s - T) (by omega)
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero,
      show T + (s - T) = s by omega] using hh) s hs hst
  omega

/-- While the center is clean, every left-half defect descends from left-half
defects only. -/
theorem left_lineage_of_clean_center (Q t k T : Nat) (hk : 1 ≤ k) (hT : T ≤ t)
    (hd : leftDefect Q t k = true) (hc : CenterCleanThrough Q T (t - T)) :
    LeftLineage Q t k T := by
  obtain ⟨f, hf⟩ := defect_ancestry Q t (-(k : Int)) hd
  refine ⟨f, hf, fun s hs hst => ?_⟩
  have := ancestry_barrier_left Q t T (-(k : Int)) 0 f hf (by omega) (fun s hs hst => by
    have hh := hc (s - T) (by omega)
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero,
      show T + (s - T) = s by omega] using hh) s hs hst
  omega

/-- A right lineage reads a right-half defect at time `T` within light-cone distance. -/
theorem right_lineage_at_start (Q t j T : Nat) (hT : T ≤ t) (h : RightLineage Q t j T) :
    ∃ i : Nat, 1 ≤ i ∧ i ≤ j + (t - T) ∧ j ≤ i + (t - T) ∧ rightDefect Q T i = true := by
  obtain ⟨f, hf, hr⟩ := h
  have h1 := hr T (Nat.le_refl _) hT
  have hb := ancestry_displacement Q t (j : Int) f hf T hT
  refine ⟨(f T).toNat, by omega, by omega, by omega, ?_⟩
  rw [rightDefect_eq_defect, Int.toNat_of_nonneg (by omega)]
  exact hf.2.2 T hT

/-- A left lineage reads a left-half defect at time `T` within light-cone distance. -/
theorem left_lineage_at_start (Q t k T : Nat) (hT : T ≤ t) (h : LeftLineage Q t k T) :
    ∃ i : Nat, 1 ≤ i ∧ i ≤ k + (t - T) ∧ k ≤ i + (t - T) ∧ leftDefect Q T i = true := by
  obtain ⟨f, hf, hl⟩ := h
  have h1 := hl T (Nat.le_refl _) hT
  have hb := ancestry_displacement Q t (-(k : Int)) f hf T hT
  refine ⟨(-(f T)).toNat, by omega, by omega, by omega, ?_⟩
  simp only [leftDefect]
  rw [show -(((-(f T)).toNat : Nat) : Int) = f T by omega]
  exact hf.2.2 T hT

/-- **Seed boundary of a right lineage.** If the lineage is confined from time zero,
it ends at a black cell of the right half of row `Q`: a seed-row defect of signed
phase `+1` within light-cone distance. -/
theorem right_lineage_seed (Q t j : Nat) (h : RightLineage Q t j 0) :
    ∃ i : Nat, 1 ≤ i ∧ i ≤ Q ∧ i ≤ j + t ∧ j ≤ i + t ∧ rightDefect Q 0 i = true ∧
      rightCell Q i = true ∧ rightPhase Q 0 i = 1 := by
  obtain ⟨f, hf, hr⟩ := h
  have h1 := hr 0 (Nat.le_refl _) (Nat.zero_le _)
  have hb := ancestry_displacement Q t (j : Int) f hf 0 (Nat.zero_le _)
  have term := ancestry_seed_terminal Q t (j : Int) f hf
  have hi : ((f 0).toNat : Int) = f 0 := Int.toNat_of_nonneg (by omega)
  rcases term with ⟨_, hQ, hcase⟩
  rcases hcase with ⟨h0, _, _⟩ | ⟨_, hcell, hph⟩
  · omega
  · refine ⟨(f 0).toNat, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [rightDefect_eq_defect, hi]; exact hf.2.2 0 (Nat.zero_le _)
    · simp only [rightCell, hi]; exact hcell
    · simpa only [rightPhase, rightCell, hi, phase, Nat.zero_add] using hph

/-- **Seed boundary of a left lineage.** Confined from time zero, it ends at a black
cell of the left half of row `Q`, of signed phase `+1`. -/
theorem left_lineage_seed (Q t k : Nat) (h : LeftLineage Q t k 0) :
    ∃ i : Nat, 1 ≤ i ∧ i ≤ Q ∧ i ≤ k + t ∧ k ≤ i + t ∧ leftDefect Q 0 i = true ∧
      leftCell Q i = true ∧ leftPhase Q 0 i = 1 := by
  obtain ⟨f, hf, hl⟩ := h
  have h1 := hl 0 (Nat.le_refl _) (Nat.zero_le _)
  have hb := ancestry_displacement Q t (-(k : Int)) f hf 0 (Nat.zero_le _)
  have term := ancestry_seed_terminal Q t (-(k : Int)) f hf
  have hi : -(((-(f 0)).toNat : Nat) : Int) = f 0 := by omega
  rcases term with ⟨hQ, _, hcase⟩
  rcases hcase with ⟨h0, _, _⟩ | ⟨_, hcell, hph⟩
  · omega
  · refine ⟨(-(f 0)).toNat, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · simp only [leftDefect, hi]; exact hf.2.2 0 (Nat.zero_le _)
    · simp only [leftCell, hi]; exact hcell
    · simpa only [leftPhase, hi, Nat.zero_add] using hph

/-! ### The leftmost right-half defect -/

/-- The leftmost right-half defect at time `t` is at column `y ≥ 1`. -/
def RightFront (Q t y : Nat) : Prop :=
  1 ≤ y ∧ rightDefect Q t y = true ∧ ∀ j : Nat, 1 ≤ j → j < y → rightDefect Q t j = false

private theorem least_witness (P : Nat → Prop) : ∀ n : Nat, P n →
    ∃ y, y ≤ n ∧ P y ∧ ∀ j, j < y → ¬ P j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : ∃ j, j < n ∧ P j
    · obtain ⟨j, hj, hpj⟩ := h
      obtain ⟨y, hy, hpy, hmin⟩ := ih j hj hpj
      exact ⟨y, by omega, hpy, hmin⟩
    · exact ⟨n, Nat.le_refl n, hn, fun j hj hpj => h ⟨j, hj, hpj⟩⟩

/-- For a positive lag the right half always carries a defect: the later row's
right edge. Hence the leftmost one exists, within the later light cone. -/
theorem exists_right_front (Q t : Nat) (hQ : 0 < Q) :
    ∃ y : Nat, y ≤ t + Q ∧ RightFront Q t y := by
  have hedge : 1 ≤ t + Q ∧ rightDefect Q t (t + Q) = true := by
    refine ⟨by omega, ?_⟩
    simp only [rightDefect, rightCell]
    rw [cell_right_edge (t + Q), cell_eq_false_of_gt t _ (by omega)]
    rfl
  obtain ⟨y, hy, ⟨hy1, hyd⟩, hmin⟩ :=
    least_witness (fun y => 1 ≤ y ∧ rightDefect Q t y = true) (t + Q) hedge
  refine ⟨y, hy, hy1, hyd, fun j hj hjy => ?_⟩
  cases hb : rightDefect Q t j
  · rfl
  · exact absurd ⟨hj, hb⟩ (hmin j hjy)

private theorem right_front_clean (Q t y : Nat) (hc : leftDefect Q t 0 = false)
    (hy : RightFront Q t y) :
    ∀ p : Int, 0 ≤ p → p ≤ (y : Int) - 1 → defect Q t p = false := by
  intro p hp1 hp2
  by_cases hp0 : p = 0
  · rw [hp0]
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using hc
  · have hh := hy.2.2 p.toNat (by omega) (by omega)
    rwa [rightDefect_eq_defect, Int.toNat_of_nonneg hp1] at hh

/-- Under a clean center, the right front moves left by at most one column. -/
theorem right_front_lower (Q t y z : Nat) (hc : leftDefect Q t 0 = false)
    (hy : RightFront Q t y) (hz : RightFront Q (t + 1) z) : y ≤ z + 1 := by
  apply Classical.byContradiction
  intro hlt
  have hclean := defect_clean_step Q t 0 ((y : Int) - 1) (right_front_clean Q t y hc hy)
    (z : Int) (by have := hz.1; omega) (by omega)
  rw [← rightDefect_eq_defect, hz.2.1] at hclean
  exact absurd hclean (by decide)

/-- Under a clean center, a right front at `y ≥ 2` descends to `y - 1` exactly
when the common colour at `y - 1` is white. -/
theorem right_front_descent (Q t y : Nat) (hc : leftDefect Q t 0 = false)
    (hy : RightFront Q t y) (h2 : 2 ≤ y) :
    rightDefect Q (t + 1) (y - 1) = !rightCell t (y - 1) := by
  have hclean := right_front_clean Q t y hc hy
  have step := defect_left_front_step Q t ((y - 1 : Nat) : Int)
    (hclean _ (by omega) (by omega)) (hclean _ (by omega) (by omega))
    (by rw [show ((y - 1 : Nat) : Int) + 1 = (y : Int) by omega, ← rightDefect_eq_defect]
        exact hy.2.1)
  simpa only [rightDefect_eq_defect, rightCell] using step

/-! ### Rendezvous of the two fronts and the timing of the coupled import -/

private theorem center_clean_cell (Q t : Nat) (h : leftDefect Q t 0 = false) :
    defect Q t 0 = false := by
  simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using h

/-- Before the rightmost left defect arrives next to the center, a right-head
defect can occur only at a black center time. -/
theorem leading_head_black_before_arrival (Q b k s : Nat) (hr : RightmostLeft Q b k)
    (hc : CenterCleanThrough Q b k) (hs : s + 1 < k)
    (hh : rightDefect Q (b + s) 1 = true) : Rule30UOR.Core.center (b + s) = true := by
  have prof := rightmost_left_profile Q b k s hr (by omega) (fun j hj => hc j (by omega))
  have hl : leftDefect Q (b + s) 1 = false := prof.2.2 1 (by omega)
  have m := neighbor_matching Q (b + s) 0
    (center_clean_cell Q (b + s) (hc s (by omega)))
    (center_clean_cell Q (b + s + 1) (by
      simpa only [Nat.add_assoc] using hc (s + 1) (by omega)))
  have hl' : defect Q (b + s) (0 - 1) = false := by
    simpa only [leftDefect, show (0 : Int) - 1 = -((1 : Nat) : Int) by omega] using hl
  rw [hl', show (0 : Int) + 1 = ((1 : Nat) : Int) by omega, ← rightDefect_eq_defect, hh] at m
  rw [Rule30UOR.Scale.center_eq_kit]
  cases hcell : cell (b + s) 0
  · rw [hcell] at m; exact absurd m (by decide)
  · exact hcell

/-- **The coupled import is born at the arrival step.** For a leading source of
depth `k ≥ 3` followed by an all-white center gap, a head-import path ending at the
first center erasure must start exactly one step before it. Earlier persistence of
the head defect would put it at a white center before the left front arrives. -/
theorem coupled_import_born_at_arrival (Q b k start : Nat) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hp : HeadImportPath Q start (b + (k - 1))) :
    start = b + (k - 2) := by
  have hlt := hp.1
  apply Classical.byContradiction
  intro hne
  have hh : rightDefect Q (b + (k - 2)) 1 = true :=
    hp.2.2.2.2.2.2 (b + (k - 2)) (by omega) (by omega)
  have hb := leading_head_black_before_arrival Q b k (k - 2) hl.2.2 hc (by omega) hh
  have hwhite := hw (k - 2) (by omega) (by omega)
  rw [hb] at hwhite
  exact absurd hwhite (by decide)

/-- **Mirror domination.** Between the source and the import the head stays clean,
so the right front is at least `2`; it must reach column `2` at the import time and
moves left by at most one column per step. At every time `b + s` of the white gap it
therefore lies in `[2, k - s]`: never farther from the center than the left front,
which is at depth `k - s`. -/
theorem coupled_right_front_mirror (Q b k : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) :
    (∀ s : Nat, 1 ≤ s → s + 1 < k → rightDefect Q (b + s) 1 = false) ∧
      ∀ s : Nat, 1 ≤ s → s + 1 < k → ∃ y : Nat, RightFront Q (b + s) y ∧ 2 ≤ y ∧ y ≤ k - s := by
  have hclean : ∀ s : Nat, 1 ≤ s → s + 1 < k → rightDefect Q (b + s) 1 = false := by
    intro s hs1 hs
    cases hh : rightDefect Q (b + s) 1
    · rfl
    · have hb := leading_head_black_before_arrival Q b k s hl.2.2 hc hs hh
      have hwhite := hw s (by omega) (by omega)
      rw [hb] at hwhite
      exact absurd hwhite (by decide)
  refine ⟨hclean, ?_⟩
  have hge : ∀ s y : Nat, 1 ≤ s → s + 1 < k → RightFront Q (b + s) y → 2 ≤ y := by
    intro s y hs1 hs hy
    apply Classical.byContradiction
    intro hlt
    have hy1 : y = 1 := by have := hy.1; omega
    have := hy.2.1
    rw [hy1, hclean s hs1 hs] at this
    exact absurd this (by decide)
  -- the import: the head is clean at b+(k-2) and defective at b+(k-1)
  have hfront_end : ∀ y : Nat, RightFront Q (b + (k - 2)) y → y ≤ 2 := by
    intro y hy
    apply Classical.byContradiction
    intro hgt
    obtain ⟨_hf, he, _hg, _hw⟩ := leading_first_erasure Q b k hl hc
    have hin : leftDefect Q (b + (k - 1)) 1 = true := he.1
    have hk' : leftDefect Q (b + (k - 1) + 1) 0 = false := by
      rw [show b + (k - 1) + 1 = b + k by omega]
      exact hc k (Nat.le_refl _)
    have hin' : defect Q (b + (k - 1)) (0 - 1) = true := by
      simpa only [leftDefect, show (0 : Int) - 1 = -((1 : Nat) : Int) by omega] using hin
    have pair := defect_right_and_white_of_clean_pair Q (b + (k - 1)) 0
      (center_clean_cell Q _ (hc (k - 1) (by omega))) (center_clean_cell Q _ hk') hin'
    have hend : rightDefect Q (b + (k - 1)) 1 = true := by
      rw [rightDefect_eq_defect]
      simpa only [show (0 : Int) + 1 = ((1 : Nat) : Int) by omega] using pair.1
    have hclean' := defect_clean_step Q (b + (k - 2)) 0 ((y : Int) - 1)
      (right_front_clean Q (b + (k - 2)) y (hc (k - 2) (by omega)) hy)
      ((1 : Nat) : Int) (by omega) (by omega)
    rw [← rightDefect_eq_defect, show b + (k - 2) + 1 = b + (k - 1) by omega, hend] at hclean'
    exact absurd hclean' (by decide)
  have back : ∀ j : Nat, j + 3 ≤ k →
      ∃ y : Nat, RightFront Q (b + (k - 2 - j)) y ∧ y ≤ 2 + j := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨y, _, hy⟩ := exists_right_front Q (b + (k - 2)) hQ
      exact ⟨y, by simpa only [Nat.sub_zero] using hy, hfront_end y hy⟩
    | succ j ih =>
      intro hj
      obtain ⟨y', hy', hy'b⟩ := ih (by omega)
      obtain ⟨y, _, hy⟩ := exists_right_front Q (b + (k - 2 - (j + 1))) hQ
      have hlow := right_front_lower Q (b + (k - 2 - (j + 1))) y y'
        (by simpa only [Nat.add_assoc] using hc (k - 2 - (j + 1)) (by omega)) hy
        (by rwa [show b + (k - 2 - (j + 1)) + 1 = b + (k - 2 - j) by omega])
      exact ⟨y, hy, by omega⟩
  intro s hs1 hs
  obtain ⟨y, hy, hyb⟩ := back (k - 2 - s) (by omega)
  rw [show b + (k - 2 - (k - 2 - s)) = b + s by omega] at hy
  exact ⟨y, hy, hge s y hs1 hs hy, by omega⟩

/-- Under a clean center, a front that moves left must move by exactly one column,
through a common white cell. -/
theorem right_front_lockstep (Q t y z : Nat) (hc : leftDefect Q t 0 = false)
    (hy : RightFront Q t y) (h2 : 2 ≤ y) (hz : RightFront Q (t + 1) z) (hle : z + 1 ≤ y) :
    z = y - 1 ∧ rightCell t (y - 1) = false := by
  have hlow := right_front_lower Q t y z hc hy hz
  have he : z = y - 1 := by omega
  refine ⟨he, ?_⟩
  have hd := right_front_descent Q t y hc hy h2
  have hy'd := hz.2.1
  rw [he, show t + 1 = t + 1 from rfl, hd] at hy'd
  cases hcell : rightCell t (y - 1)
  · rfl
  · rw [hcell] at hy'd; exact absurd hy'd (by decide)

/-- **White staircase.** In the coupled gap, once the right front is at the mirror
position `k - s` of the left front, it must descend in lockstep with it until the
import. Each step needs a common white cell at the column just inside the front. -/
theorem coupled_white_staircase (Q b k s : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hs1 : 1 ≤ s) (heq : RightFront Q (b + s) (k - s)) :
    ∀ i : Nat, s ≤ i → i + 2 < k →
      RightFront Q (b + i) (k - i) ∧ rightCell (b + i) (k - i - 1) = false := by
  have dom := (coupled_right_front_mirror Q b k hQ h3 hl hc hw).2
  intro i
  induction i with
  | zero => intro hi; omega
  | succ i ih =>
    intro hi hik
    have hfront : RightFront Q (b + (i + 1)) (k - (i + 1)) := by
      by_cases hsi : s = i + 1
      · rw [← hsi]; exact heq
      · have prev := ih (by omega) (by omega)
        obtain ⟨y', hy', _, hy'b⟩ := dom (i + 1) (by omega) (by omega)
        have ls := right_front_lockstep Q (b + i) (k - i) y'
          (hc i (by omega)) prev.1 (by omega)
          (by rwa [show b + i + 1 = b + (i + 1) by omega]) (by omega)
        rw [ls.1, show k - i - 1 = k - (i + 1) by omega] at hy'
        exact hy'
    refine ⟨hfront, ?_⟩
    obtain ⟨y', hy', _, hy'b⟩ := dom (i + 2) (by omega) (by omega)
    have ls := right_front_lockstep Q (b + (i + 1)) (k - (i + 1)) y'
      (hc (i + 1) (by omega)) hfront (by omega)
      (by rwa [show b + (i + 1) + 1 = b + (i + 2) by omega]) (by omega)
    simpa only [show k - (i + 1) - 1 = k - (i + 1) - 1 from rfl] using ls.2

/-- The mirror domination at one time `b + s` of the white gap. -/
theorem coupled_right_front_mirror_at (Q b k s : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hs1 : 1 ≤ s) (hs : s + 1 < k) :
    ∃ y : Nat, rightDefect Q (b + s) 1 = false ∧ RightFront Q (b + s) y ∧ 2 ≤ y ∧ y ≤ k - s := by
  have h := coupled_right_front_mirror Q b k hQ h3 hl hc hw
  obtain ⟨y, hy, hy2, hyk⟩ := h.2 s hs1 hs
  exact ⟨y, h.1 s hs1 hs, hy, hy2, hyk⟩

/-- One stair of the forced white staircase: mirror position at `b + s` forces the
common white cell just inside the front and mirror position one step later. -/
theorem coupled_white_staircase_at (Q b k s : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hs1 : 1 ≤ s) (hs : s + 2 < k)
    (heq : RightFront Q (b + s) (k - s)) :
    rightCell (b + s) (k - s - 1) = false ∧ RightFront Q (b + (s + 1)) (k - (s + 1)) := by
  have st := coupled_white_staircase Q b k s hQ h3 hl hc hw hs1 heq
  refine ⟨(st s (Nat.le_refl _) hs).2, ?_⟩
  by_cases hk : s + 3 < k
  · exact (st (s + 1) (by omega) (by omega)).1
  · obtain ⟨y', _, hy', _, hy'b⟩ := coupled_right_front_mirror_at Q b k (s + 1) hQ h3 hl hc hw
      (by omega) (by omega)
    have ls := right_front_lockstep Q (b + s) (k - s) y' (hc s (by omega)) heq (by omega)
      (by rwa [show b + s + 1 = b + (s + 1) by omega]) (by omega)
    rwa [ls.1, show k - s - 1 = k - (s + 1) by omega] at hy'

/-- A finite kernel certificate that the coupled white-gap hypotheses are jointly
satisfiable in the actual seed: lag 14, black source time 5, depth 3, white centers
at 6 and 7, the right front at the mirror position 2 at time 6, and the head import
born at time 6, exactly one step before arrival. Not a premise of any unbounded claim. -/
theorem seed_coupled_import_at_arrival :
    LeadingAdvance 14 5 3 ∧ CenterCleanThrough 14 5 3 ∧ WhiteCenterGap 5 2 ∧
      Rule30UOR.Core.center 5 = true ∧ RightFront 14 6 2 ∧ HeadImportPath 14 6 7 := by
  obtain ⟨hl, hc⟩ := leading_of_rows 14 5 3 (by unfold RowLeadingData; decide +kernel)
  have data : cell 5 0 = true ∧ cell 6 0 = false ∧ cell 7 0 = false ∧
      rightCell 6 1 = false ∧ rightCell 20 1 = false ∧ rightCell 6 2 = false ∧
      rightCell 20 2 = true ∧ rightCell 7 1 = false ∧ rightCell 21 1 = true := by
    simp only [rightCell, Int.natCast_one, show ((2 : Nat) : Int) = 2 by omega]
    rw [cell_as_row 5 0 (by omega), cell_as_row 6 0 (by omega), cell_as_row 7 0 (by omega),
      cell_as_row 6 1 (by omega), cell_as_row 20 1 (by omega), cell_as_row 6 2 (by omega),
      cell_as_row 20 2 (by omega), cell_as_row 7 1 (by omega), cell_as_row 21 1 (by omega)]
    decide +kernel
  obtain ⟨h5, h6, h7, a61, a201, a62, a202, a71, a211⟩ := data
  have hd1 : rightDefect 14 6 1 = false := by simp [rightDefect, a61, a201]
  have hd2 : rightDefect 14 6 2 = true := by simp [rightDefect, a62, a202]
  have hn : rightDefect 14 7 1 = true := by simp [rightDefect, a71, a211]
  have hc6 : Rule30UOR.Core.center (6 + 14) = Rule30UOR.Core.center 6 := by
    have := clean_center_core 14 5 3 hc 1 (by omega)
    simpa only [show 5 + 1 = 6 by omega] using this
  have birth := right_head_birth 14 6 hc6 hd1 hn
  refine ⟨hl, hc, ?_, ?_, ⟨by omega, hd2, ?_⟩, ⟨by omega, hd1, birth.1, birth.2.1, birth.2.2.1,
    birth.2.2.2.1, ?_⟩⟩
  · intro j hj0 hj2
    rw [Rule30UOR.Scale.center_eq_kit]
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
    · exact h6
    · exact h7
  · rw [Rule30UOR.Scale.center_eq_kit]; exact h5
  · intro j hj1 hj2
    rw [show j = 1 by omega]; exact hd1
  · intro s h6' h7'
    rw [show s = 7 by omega]; exact hn

/-- **Coupled ancestry under a hypothetical periodic center.** The joint witness of
`periodic_coupled_cancellation` has, in addition: the import is born at the arrival
step whenever `k ≥ 3`; the right front one step after the source lies in `[2, k - 1]`
with a clean head until the import; and the import's column-2 defect and the left
source descend, after time `T`, from right-half and left-half defects respectively.
Their lineages meet only before `T`. -/
theorem periodic_coupled_import_ancestry (T P m N g : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hg : g = 2 ∨ g = 5) :
    ∃ start b k y : Nat, N ≤ start ∧ N ≤ b ∧ T ≤ b ∧ T ≤ start ∧ 2 ≤ k ∧ k ≤ P ∧
      Rule30UOR.Core.center b = true ∧ WhiteCenterGap b (k - 1) ∧
      LeadingAdvance (m * P) b k ∧ gateCode (m * P) (b + (k - 1)) 0 = g ∧
      HeadImportPath (m * P) start (b + (k - 1)) ∧
      (3 ≤ k → start = b + (k - 2)) ∧
      (3 ≤ k → RightFront (m * P) (b + 1) y ∧ 2 ≤ y ∧ y ≤ k - 1) ∧
      RightLineage (m * P) start 2 T ∧ LeftLineage (m * P) b k T := by
  obtain ⟨start, b, k, hs, hb, hk, hblack, hwhite, hl, _hf, hgate, path, _balance⟩ :=
    periodic_coupled_cancellation T P m (max T N) g hP hm hc hg
  have hp : ∀ t, T ≤ t → center (t + P) = center t := by
    intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht
  have clean : ∀ t n : Nat, T ≤ t → CenterCleanThrough (m * P) t n := by
    intro t n ht s _hbound
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using
      center_defect_zero hp m (t + s) (by omega)
  have hQ : 0 < m * P := Nat.mul_pos hm hP
  have hy : ∃ y : Nat, 3 ≤ k → RightFront (m * P) (b + 1) y ∧ 2 ≤ y ∧ y ≤ k - 1 := by
    by_cases h3 : 3 ≤ k
    · obtain ⟨y, _, hy, hy2, hyk⟩ := coupled_right_front_mirror_at (m * P) b k 1 hQ h3 hl
        (clean b k (by omega)) hwhite (Nat.le_refl _) (by omega)
      exact ⟨y, fun _ => ⟨hy, hy2, hyk⟩⟩
    · exact ⟨0, fun h => absurd h h3⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨start, b, k, y, by omega, by omega, by omega, by omega, hl.1, hk, hblack, hwhite, hl,
    hgate, path, fun h3 => coupled_import_born_at_arrival (m * P) b k start h3 hl
      (clean b k (by omega)) hwhite path, hy,
    right_lineage_of_clean_center (m * P) start 2 T (by omega) (by omega) path.2.2.2.2.1
      (clean T (start - T) (Nat.le_refl _)),
    left_lineage_of_clean_center (m * P) b k T (by have := hl.1; omega) (by omega)
      hl.2.2.2.1 (clean T (b - T) (Nat.le_refl _))⟩

/-! ## Moving-diagonal transport to a physical head

A diagonal point at time `t` has position `d - t`. Its right-moving
characteristic reaches column `-p` at time `t + (t - d - p)`.
The corresponding point at time `t + Q` reaches that same column `2 * Q`
steps later. The two characteristics have different lengths; neither flux
may be discarded. The reset pair on `z + 1` and `z + 3` has one common
physical endpoint, and its two tail fluxes differ by twice the initial phase.
-/

/-- One physical characteristic in the actual seeded orbit. -/
def rayBit (t k n : Nat) : Bool := cell (t + n) (-(k : Int) + (n : Int))

/-- Exact single-history OR contribution along that characteristic. -/
def rayFlux (t k : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => rayFlux t k n +
      (1 - 2 * bitValue (rayBit t k n)) *
        bitValue (cell (t + n) (-(k : Int) + (n : Int) + 1) ||
          cell (t + n) (-(k : Int) + (n : Int) + 2))

/-- Signed difference on a moving diagonal, distinct from `leftPhase`. -/
def diagonalPhase (Q d t : Nat) : Int :=
  bitValue (Rule30UOR.Core.ldiag d (t + Q)) - bitValue (Rule30UOR.Core.ldiag d t)

/-- Later minus earlier flux, with the later characteristic longer by `Q`. -/
def diagonalFlux (Q d t p : Nat) : Int :=
  rayFlux (t + Q) (t + Q - d) (t + Q - d - p) -
    rayFlux t (t - d) (t - d - p)

private theorem bit_toggle_balance (a g : Bool) :
    bitValue (xor a g) = bitValue a + (1 - 2 * bitValue a) * bitValue g := by
  cases a <;> cases g <;> decide

/-- Every interior toggle/reset is retained in the ray flux. -/
theorem ray_bit_balance (t k : Nat) : ∀ n : Nat,
    bitValue (rayBit t k n) = bitValue (rayBit t k 0) + rayFlux t k n := by
  intro n
  induction n with
  | zero => simp only [rayFlux, Int.add_zero]
  | succ n ih =>
    have hs : rayBit t k (n + 1) = xor (rayBit t k n)
        (cell (t + n) (-(k : Int) + (n : Int) + 1) ||
          cell (t + n) (-(k : Int) + (n : Int) + 2)) := by
      unfold rayBit
      rw [show t + (n + 1) = (t + n) + 1 by omega,
        show -(k : Int) + ((n + 1 : Nat) : Int) = -(k : Int) + (n : Int) + 1 by omega]
      change xor (cell (t + n) ((-(k : Int) + (n : Int) + 1) - 1))
        (cell (t + n) (-(k : Int) + (n : Int) + 1) ||
          cell (t + n) ((-(k : Int) + (n : Int) + 1) + 1)) = _
      rw [show (-(k : Int) + (n : Int) + 1) - 1 = -(k : Int) + (n : Int) by omega,
        show (-(k : Int) + (n : Int) + 1) + 1 = -(k : Int) + (n : Int) + 2 by omega]
    rw [hs, bit_toggle_balance]
    simp only [rayFlux]
    omega

private theorem ray_start_diagonal (d t : Nat) (hd : d ≤ t) :
    rayBit t (t - d) 0 = Rule30UOR.Core.ldiag d t := by
  have h := Rule30UOR.Interfaces.ldiag_eq_cell_neg d (t - d)
  rw [show d + (t - d) = t by omega, Rule30UOR.Scale.cell_eq_kit] at h
  simpa only [rayBit, Nat.add_zero, Int.natCast_zero, Int.add_zero] using h.symm

/-- Moving-diagonal lag `Q` arrives as physical-column lag `Q + Q`. -/
theorem diagonal_ray_balance (Q d t p : Nat) (hp : d + p ≤ t) :
    leftPhase (Q + Q) (t + (t - d - p)) p =
      diagonalPhase Q d t + diagonalFlux Q d t p := by
  have h0 := ray_bit_balance t (t - d) (t - d - p)
  have h1 := ray_bit_balance (t + Q) (t + Q - d) (t + Q - d - p)
  have e0 : rayBit t (t - d) (t - d - p) =
      cell (t + (t - d - p)) (-(p : Int)) := by
    unfold rayBit
    congr 1 <;> omega
  have e1 : rayBit (t + Q) (t + Q - d) (t + Q - d - p) =
      cell ((t + (t - d - p)) + (Q + Q)) (-(p : Int)) := by
    unfold rayBit
    congr 1 <;> omega
  rw [e0, ray_start_diagonal d t (by omega)] at h0
  rw [e1, ray_start_diagonal d (t + Q) (by omega)] at h1
  unfold leftPhase phase diagonalPhase diagonalFlux
  omega

/-- Lag addition shifts both the start time and the characteristic length. -/
theorem diagonal_flux_lag_add (Q R d t p : Nat) :
    diagonalFlux (Q + R) d t p =
      diagonalFlux Q d t p + diagonalFlux R d (t + Q) p := by
  unfold diagonalFlux
  rw [show t + (Q + R) = (t + Q) + R by omega]
  omega

/-- The settled doubling diagonal supplies a unit phase and its opposite
in the next history; the outer comparison has zero phase. -/
theorem diagonal_phase_doubles (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hd : Rule30UOR.CompilePoints.DoublesAt Q z)
    (hs : Rule30UOR.Interfaces.SettledBy (z + 1) t) :
    (diagonalPhase Q (z + 1) t = -1 ∨ diagonalPhase Q (z + 1) t = 1) ∧
      diagonalPhase Q (z + 1) (t + Q) = -diagonalPhase Q (z + 1) t ∧
      diagonalPhase (Q + Q) (z + 1) t = 0 := by
  have h0 := Rule30UOR.Interfaces.ldiag_settled_antiperiodic_of_doubles Q z t hz hd hs
  have h1 := Rule30UOR.Interfaces.ldiag_settled_antiperiodic_of_doubles Q z (t + Q) hz hd
    (show Rule30UOR.Interfaces.SettledBy (z + 1) (t + Q) from Nat.le_trans hs (by omega))
  have h2 : Rule30UOR.Core.ldiag (z + 1) (t + (Q + Q)) =
      Rule30UOR.Core.ldiag (z + 1) t := by
    rw [show t + (Q + Q) = (t + Q) + Q by omega, h1, h0, Bool.not_not]
  simp only [diagonalPhase, h1, h2, h0]
  cases Rule30UOR.Core.ldiag (z + 1) t <;> decide

private theorem zero_reset_value (z t : Nat)
    (hb : Rule30UOR.Core.ldiag (z + 2) t = true) :
    Rule30UOR.Core.ldiag (z + 3) (t + 1) = !Rule30UOR.Core.ldiag (z + 1) t := by
  change Rule30UOR.Core.bxor (Rule30UOR.Core.ldiag (z + 1) t)
    (Rule30UOR.Core.ldiag (z + 2) t || Rule30UOR.Core.ldiag (z + 3) t) = _
  rw [hb, Bool.true_or]
  cases Rule30UOR.Core.ldiag (z + 1) t <;> rfl

/-- The seed's settled black diagonal complements both moving histories. -/
theorem diagonal_reset_phase (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hs : Rule30UOR.Interfaces.SettledBy (z + 2) t) :
    diagonalPhase Q (z + 3) (t + 1) = -diagonalPhase Q (z + 1) t := by
  have b0 := Rule30UOR.Interfaces.ldiag_after_zero_diag z t hz hs
  have b1 := Rule30UOR.Interfaces.ldiag_after_zero_diag z (t + Q) hz (by
    exact Nat.le_trans hs (by omega))
  have r0 := zero_reset_value z t b0
  have r1 := zero_reset_value z (t + Q) b1
  unfold diagonalPhase
  rw [show (t + 1) + Q = (t + Q) + 1 by omega, r0, r1]
  cases Rule30UOR.Core.ldiag (z + 1) t <;>
    cases Rule30UOR.Core.ldiag (z + 1) (t + Q) <;> decide

/-- The `z + 1` and `z + 3` rays have the same physical head endpoint.
Their complete tail fluxes differ by twice the moving input phase. -/
theorem diagonal_reset_flux_jump (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hs : Rule30UOR.Interfaces.SettledBy (z + 2) t) (ht : z + 3 ≤ t) :
    diagonalFlux Q (z + 3) (t + 1) 1 =
      diagonalFlux Q (z + 1) t 1 + 2 * diagonalPhase Q (z + 1) t := by
  have h0 := diagonal_ray_balance Q (z + 1) t 1 (by omega)
  have h1 := diagonal_ray_balance Q (z + 3) (t + 1) 1 (by omega)
  rw [show (t + 1) + ((t + 1) - (z + 3) - 1) = t + (t - (z + 1) - 1) by omega] at h1
  have hr := diagonal_reset_phase Q z t hz hs
  omega

/-- At a specified common white arrival, the entire moving-diagonal input
and flux equal the physical right-head phase with the actual next-center sign.
The arrival time and white-center hypothesis are explicit, not inferred from
fixed-diagonal periodicity. -/
theorem periodic_diagonal_white_head_balance (T P m d t : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : d + 1 ≤ t)
    (hT : T ≤ t + (t - d - 1))
    (hw : Rule30UOR.Core.center (t + (t - d - 1)) = false) :
    diagonalPhase (m * P) d t + diagonalFlux (m * P) d t 1 =
      (1 - 2 * bitValue (Rule30UOR.Core.center (t + (t - d - 1) + 1))) *
        rightPhase (m * P + m * P) (t + (t - d - 1)) 1 := by
  have hp : ∀ s, T ≤ s → center (s + P) = center s := by
    intro s hs
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc s hs
  have clean (s : Nat) (hs : T ≤ s) : leftDefect (m * P + m * P) s 0 = false := by
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero, Nat.add_mul] using
      center_defect_zero hp (m + m) s hs
  have matched := white_center_phase_matching (m * P + m * P) (t + (t - d - 1))
    (clean _ hT) (clean _ (by omega)) hw
  exact (diagonal_ray_balance (m * P) d t 1 ht).symm.trans matched

/-- When that same physical head is supplied by an actual import path,
the moving input plus every intervening ray contribution matches its column-2
birth, including all black-center sign changes on the import path. -/
theorem periodic_diagonal_import_balance (T P m d t start : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : d + 1 ≤ t)
    (hs : T ≤ start)
    (hp : HeadImportPath (m * P + m * P) start (t + (t - d - 1)))
    (hw : Rule30UOR.Core.center (t + (t - d - 1)) = false) :
    diagonalPhase (m * P) d t + diagonalFlux (m * P) d t 1 =
      (1 - 2 * bitValue (Rule30UOR.Core.center (t + (t - d - 1) + 1))) *
        (centerSign start (t + (t - d - 1) - start) *
          rightPhase (m * P + m * P) start 2) := by
  have hT : T ≤ t + (t - d - 1) := by have := hp.1; omega
  have hpP : ∀ s, T ≤ s → center (s + P) = center s := by
    intro s h
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc s h
  have clean : CenterCleanThrough (m * P + m * P) start (t + (t - d - 1) - start) := by
    intro s _h
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero, Nat.add_mul] using
      center_defect_zero hpP (m + m) (start + s) (by omega)
  have matched := periodic_diagonal_white_head_balance T P m d t hc ht hT hw
  rw [head_import_path_phase (m * P + m * P) start (t + (t - d - 1)) hp clean] at matched
  exact matched

/-! ## Forced mirror front from the physical import birth

The import's common white heads, traced backwards through the white center
run, force both initial right prefixes to be white. Mirror domination is
therefore an equality, not merely an upper bound. This is a constraint on
the actual two-history background, without a phase or orientation assumption.
-/

private theorem right_cell_rh (t p : Nat) :
    rightCell t p = Rule30UOR.Interfaces.rhCenter t p := by
  unfold rightCell Rule30UOR.Interfaces.rhCenter
  rw [Rule30UOR.Fixed.Rh_center t (p : Int) (by omega)]

private theorem head_white_forces_prefix (t n : Nat)
    (hw : ∀ s : Nat, s < n → Rule30UOR.Core.center (t + s) = false)
    (hh : rightCell (t + n) 1 = false) :
    ∀ q : Nat, 1 ≤ q → q ≤ n + 1 → rightCell t q = false := by
  intro q hq1 hqn
  cases hb : rightCell t q
  · rfl
  · have init : Rule30UOR.Interfaces.rhCenter t ((q - 1) + 1) = true := by
      rw [show q - 1 + 1 = q by omega, ← right_cell_rh]
      exact hb
    have hit := Rule30UOR.Interfaces.rdrv_col_one_black_from_init_of_white_drive
      t t (q - 1) n n hw init (by omega) (Nat.le_refl _)
    rw [Rule30UOR.Interfaces.rdrv_diag_eq_rhCenter, ← right_cell_rh, hh] at hit
    exact absurd hit (by decide)

/-- A coupled white-gap cancellation forces the entire common white right
prefix and an exact mirror front at the first time after the source. -/
private theorem coupled_right_front_and_prefix (Q b k start : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hp : HeadImportPath Q start (b + (k - 1))) :
    RightFront Q (b + 1) (k - 1) ∧
      ∀ q : Nat, 1 ≤ q → q + 1 < k →
        rightCell (b + 1) q = false ∧ rightCell (b + 1 + Q) q = false := by
  have hs := coupled_import_born_at_arrival Q b k start h3 hl hc hw hp
  have wa : rightCell (b + 1 + (k - 3)) 1 = false := by
    simpa only [hs, show b + 1 + (k - 3) = b + (k - 2) by omega] using hp.2.2.1
  have wb : rightCell (b + 1 + Q + (k - 3)) 1 = false := by
    simpa only [hs, show b + 1 + Q + (k - 3) = b + (k - 2) + Q by omega] using hp.2.2.2.1
  have pa := head_white_forces_prefix (b + 1) (k - 3) (fun s hs => by
    simpa only [Nat.add_assoc] using hw (1 + s) (by omega) (by omega)) wa
  have pb := head_white_forces_prefix (b + 1 + Q) (k - 3) (fun s hs => by
    have eqc := clean_center_core Q b k hc (1 + s) (by omega)
    have wh := hw (1 + s) (by omega) (by omega)
    have eqc' : Rule30UOR.Core.center (b + 1 + Q + s) =
        Rule30UOR.Core.center (b + (1 + s)) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using eqc
    exact eqc'.trans wh) wb
  have whitePrefix : ∀ q : Nat, 1 ≤ q → q + 1 < k →
      rightCell (b + 1) q = false ∧ rightCell (b + 1 + Q) q = false := by
    intro q hq1 hq
    exact ⟨pa q hq1 (by omega), pb q hq1 (by omega)⟩
  obtain ⟨y, _hhead, hy, hy2, hyk⟩ :=
    coupled_right_front_mirror_at Q b k 1 hQ h3 hl hc hw (Nat.le_refl _) (by omega)
  have yeq : y = k - 1 := by
    apply Classical.byContradiction
    intro hne
    have white := whitePrefix y (by omega) (by omega)
    have hz : rightDefect Q (b + 1) y = false := by
      simp only [rightDefect, white.1, white.2, Bool.xor_self]
    have hin := hy.2.1
    rw [hz] at hin
    cases hin
  rw [yeq] at hy
  exact ⟨hy, whitePrefix⟩

/-- Pointwise readout of the exact initial mirror front and its common white prefix. -/
theorem coupled_right_front_exact (Q b k start q : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hp : HeadImportPath Q start (b + (k - 1)))
    (hq1 : 1 ≤ q) (hq : q + 1 < k) :
    RightFront Q (b + 1) (k - 1) ∧
      rightCell (b + 1) q = false ∧ rightCell (b + 1 + Q) q = false := by
  have h := coupled_right_front_and_prefix Q b k start hQ h3 hl hc hw hp
  exact ⟨h.1, h.2 q hq1 hq⟩

/-- The common white staircase is forced throughout the gap, including the
column-2 import time. Both fronts advance towards the center in exact mirror
positions, and each right descent crosses a common white cell. -/
theorem coupled_forced_white_staircase (Q b k start i : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hp : HeadImportPath Q start (b + (k - 1)))
    (hi : 1 ≤ i) (hik : i + 1 < k) :
    RightFront Q (b + i) (k - i) ∧
      rightCell (b + i) (k - i - 1) = false ∧
      rightCell (b + i + Q) (k - i - 1) = false := by
  have exact_front := (coupled_right_front_and_prefix Q b k start hQ h3 hl hc hw hp).1
  have hs := coupled_import_born_at_arrival Q b k start h3 hl hc hw hp
  by_cases hlast : i = k - 2
  · have htime : b + i = start := by omega
    have hpos : k - i = 2 := by omega
    have hinner : k - i - 1 = 1 := by omega
    have hf : RightFront Q start 2 := ⟨by omega, hp.2.2.2.2.1, fun q hq1 hq2 => by
      have hq : q = 1 := by omega
      rw [hq]
      exact hp.2.1⟩
    exact ⟨by simpa only [htime, hpos] using hf,
      by simpa only [htime, hinner] using hp.2.2.1,
      by simpa only [htime, hinner] using hp.2.2.2.1⟩
  · have he : RightFront Q (b + 1) (k - 1) := exact_front
    have stair := coupled_white_staircase Q b k 1 hQ h3 hl hc hw (Nat.le_refl _) he i hi (by omega)
    have same : rightCell (b + i + Q) (k - i - 1) = rightCell (b + i) (k - i - 1) := by
      have hz := stair.1.2.2 (k - i - 1) (by omega) (by omega)
      unfold rightDefect at hz
      cases a : rightCell (b + i) (k - i - 1) <;>
        cases c : rightCell (b + i + Q) (k - i - 1) <;> simp_all
    exact ⟨stair.1, stair.2, same.trans stair.2⟩

/-! ## The depth-two branch and the background entering a black reset

A depth-two erasure may carry an older head defect across its black root.
The alternative is a new column-2 import at that root. In both branches the
left source is coupled to the corresponding upstream phase with the actual
next-center sign. Longer gaps instead force the previously proved mirror
staircase. No bound on the number of such windows is inferred.
-/

/-- Complete upstream phase and birth-time classification at depth two. -/
theorem depth_two_cancellation_cases (Q b start : Nat)
    (hl : LeadingAdvance Q b 2) (hc : CenterCleanThrough Q b 2)
    (hp : HeadImportPath Q start (b + 1)) :
    Rule30UOR.Core.center b = true ∧ Rule30UOR.Core.center (b + 1) = false ∧
      ((start < b ∧ rightDefect Q b 1 = true ∧ rightImportDifference Q b = false ∧
          leftPhase Q b 2 = (1 - 2 * bitValue (Rule30UOR.Core.center (b + 2))) * rightPhase Q b 1) ∨
       (start = b ∧ rightDefect Q b 1 = false ∧ rightCell b 1 = false ∧
          rightCell (b + Q) 1 = false ∧ rightDefect Q b 2 = true ∧ rightImportDifference Q b = true ∧
          leftPhase Q b 2 = (1 - 2 * bitValue (Rule30UOR.Core.center (b + 2))) * rightPhase Q b 2)) := by
  have hb := leading_depth_two_black Q b hl hc
  have hw : Rule30UOR.Core.center (b + 1) = false := (leading_first_erasure Q b 2 hl hc).2.2.2
  have ce : Rule30UOR.Core.center (b + Q) = Rule30UOR.Core.center b := by
    simpa only [Nat.add_zero] using clean_center_core Q b 2 hc 0 (by omega)
  have hb' := ce.trans hb
  have hn := hp.2.2.2.2.2.2 (b + 1) hp.1 (Nat.le_refl _)
  have advance : leftPhase Q (b + 1) 1 = -leftPhase Q b 2 :=
    advancing_phase_flip Q b 2 (by omega) hl.2.1
  have matched := white_center_phase_matching Q (b + 1) (hc 1 (by omega)) (hc 2 (by omega)) hw
  rw [show b + 1 + 1 = b + 2 by omega] at matched
  have balance := right_defect_import_balance Q b ce
  refine ⟨hb, hw, ?_⟩
  cases hd : rightDefect Q b 1 with
  | false =>
    have born := right_head_birth Q b ce hd hn
    have reset := black_reset_import Q b hb hb' hd hn
    have hs : start = b := by
      apply Classical.byContradiction
      intro hne
      have hlt : start < b := by have := hp.1; omega
      have bad := hp.2.2.2.2.2.2 b hlt (by omega)
      rw [hd] at bad
      cases bad
    have phase_eq : leftPhase Q b 2 =
        (1 - 2 * bitValue (Rule30UOR.Core.center (b + 2))) * rightPhase Q b 2 := by
      rw [advance, reset.2.2.2] at matched
      simp only [Int.mul_neg] at matched
      omega
    exact Or.inr ⟨hs, rfl, born.1, born.2.1, born.2.2.1, born.2.2.2.1, phase_eq⟩
  | true =>
    have reset := black_reset_survival Q b hb hb' hd hn
    have hs : start < b := by
      have hne : start ≠ b := by
        intro he
        have bad := hp.2.1
        rw [he, hd] at bad
        cases bad
      have := hp.1
      omega
    have no_import : rightImportDifference Q b = false := by
      rw [hn, hd] at balance
      cases hi : rightImportDifference Q b with
      | false => rfl
      | true =>
        have bad : (true : Bool) = false := by
          simpa [hi, Rule30UOR.Core.bxor] using balance
        cases bad
    have phase_eq : leftPhase Q b 2 =
        (1 - 2 * bitValue (Rule30UOR.Core.center (b + 2))) * rightPhase Q b 1 := by
      rw [advance, reset] at matched
      simp only [Int.mul_neg] at matched
      omega
    exact Or.inl ⟨hs, rfl, no_import, phase_eq⟩

/-- Every coupled import is born one step before erasure, except for the
explicit depth-two branch that survives from before the black source. -/
theorem coupled_import_birth_or_depth_two_survival (Q b k start : Nat)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hw : WhiteCenterGap b (k - 1)) (hp : HeadImportPath Q start (b + (k - 1))) :
    start = b + (k - 2) ∨ (k = 2 ∧ start < b ∧ rightDefect Q b 1 = true) := by
  by_cases h3 : 3 ≤ k
  · exact Or.inl (coupled_import_born_at_arrival Q b k start h3 hl hc hw hp)
  · have hk : k = 2 := by have := hl.1; omega
    subst k
    rcases (depth_two_cancellation_cases Q b start hl hc hp).2.2 with carry | born
    · exact Or.inr ⟨rfl, carry.1, carry.2.1⟩
    · exact Or.inl (by simpa only [Nat.sub_self, Nat.add_zero] using born.1)

private theorem two_white_outputs (a b c d : Bool)
    (ha : a = true) (h0 : rule a b c = false) (h1 : rule b c d = false) : b = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [rule]

private theorem right_cell_step (t p : Nat) :
    rightCell (t + 1) (p + 1) =
      rule (rightCell t p) (rightCell t (p + 1)) (rightCell t (p + 2)) := by
  have step := Rule30UOR.Interfaces.rhCenter_step_succ t p
  simp only [← right_cell_rh, Rule30UOR.Scale.bxor_eq] at step
  have gate : xor (rightCell t p) (rightCell t (p + 1) || rightCell t (p + 2)) =
      rule (rightCell t p) (rightCell t (p + 1)) (rightCell t (p + 2)) := by
    cases rightCell t p <;> cases rightCell t (p + 1) <;> cases rightCell t (p + 2) <;> rfl
  exact step.trans gate

private theorem white_prefix_black_predecessor (t n : Nat)
    (hb : Rule30UOR.Core.center t = true)
    (hw : ∀ q : Nat, 1 ≤ q → q ≤ n + 1 → rightCell (t + 1) q = false) :
    ∀ q : Nat, q ≤ n → rightCell t q = true := by
  intro q
  induction q with
  | zero =>
    intro _
    simpa only [rightCell, Int.natCast_zero, Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] using hb
  | succ q ih =>
    intro hq
    exact two_white_outputs (rightCell t q) (rightCell t (q + 1))
      (rightCell t (q + 2)) (rightCell t (q + 3)) (ih (by omega))
      ((right_cell_step t q).symm.trans (hw (q + 1) (by omega) (by omega)))
      ((right_cell_step t (q + 1)).symm.trans (hw (q + 2) (by omega) (by omega)))

/-- A coupled white gap also fixes the backgrounds entering the reset:
columns `0 .. k-3` are black in both histories at the black source time. -/
theorem coupled_black_root_prefix (Q b k start q : Nat) (hQ : 0 < Q) (h3 : 3 ≤ k)
    (hl : LeadingAdvance Q b k) (hc : CenterCleanThrough Q b k)
    (hb : Rule30UOR.Core.center b = true) (hw : WhiteCenterGap b (k - 1))
    (hp : HeadImportPath Q start (b + (k - 1))) (hq : q + 2 < k) :
    rightCell b q = true ∧ rightCell (b + Q) q = true := by
  have data := (coupled_right_front_and_prefix Q b k start hQ h3 hl hc hw hp).2
  have hb' : Rule30UOR.Core.center (b + Q) = true := by
    have same := clean_center_core Q b k hc 0 (by omega)
    simpa only [Nat.add_zero] using same.trans hb
  have p0 := white_prefix_black_predecessor b (k - 3) hb (fun j hj1 hj =>
    (data j hj1 (by omega)).1)
  have p1 := white_prefix_black_predecessor (b + Q) (k - 3) hb' (fun j hj1 hj => by
    have white := (data j hj1 (by omega)).2
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using white)
  exact ⟨p0 q (by omega), p1 q (by omega)⟩

/-- The actual seed realizes the depth-two survival branch. This finite
certificate refutes an unconditional fresh-birth interpretation of that case;
it is not a periodic-center premise or an unbounded recurrence assertion. -/
theorem seed_depth_two_survival :
    LeadingAdvance 4 5 2 ∧ CenterCleanThrough 4 5 2 ∧ HeadImportPath 4 2 6 ∧
      rightDefect 4 5 1 = true ∧ rightImportDifference 4 5 = false := by
  obtain ⟨hl, hc, _hg⟩ := seed_leading_gate_five
  have data : rightCell 2 1 = false ∧ rightCell 6 1 = false ∧
      rightCell 2 2 = true ∧ rightCell 6 2 = false ∧
      rightDefect 4 3 1 = true ∧ rightDefect 4 4 1 = true ∧
      rightDefect 4 5 1 = true ∧ rightDefect 4 6 1 = true ∧ rightImportDifference 4 5 = false := by
    unfold rightDefect rightImportDifference rightImport difference rightCell
    simp only [Int.natCast_one, show ((2 : Nat) : Int) = 2 by omega]
    rw [cell_as_row 2 1 (by omega), cell_as_row 6 1 (by omega),
      cell_as_row 2 2 (by omega), cell_as_row 6 2 (by omega),
      cell_as_row 3 1 (by omega), cell_as_row 7 1 (by omega),
      cell_as_row 4 1 (by omega), cell_as_row 8 1 (by omega),
      cell_as_row 5 1 (by omega), cell_as_row 9 1 (by omega),
      cell_as_row 5 2 (by omega), cell_as_row 9 2 (by omega), cell_as_row 10 1 (by omega)]
    decide +kernel
  obtain ⟨a, b, c, d, h3, h4, h5, h6, hI⟩ := data
  have hd : rightDefect 4 2 1 = false := by simp [rightDefect, a, b]
  have hr : rightDefect 4 2 2 = true := by simp [rightDefect, c, d]
  have hi : rightImportDifference 4 2 = true := by
    simp [rightImportDifference, difference, rightImport, a, b, c, d]
  refine ⟨hl, hc, ⟨by omega, hd, a, b, hr, hi, ?_⟩, h5, hI⟩
  intro s hs hle
  have cases_s : s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases cases_s with rfl | rfl | rfl | rfl
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-! ## Three readings of the exact seeded defect pair

Magnitude and low-bit support retain the outer seed edges. Evaluation at
`omega` is a different, noninjective polynomial readout: it kills the linear
Phi_3 part and need not retain a nonzero value of the full defect. A dyadic
Witt window differs from the aligned defect by two outer copies of the earlier
row. Their center bits agree only under the stated cone hypothesis.
-/

/-- The earlier aligned copy has its top bit at `2*t + Q`. -/
theorem background_top_bit (Q t : Nat) : (background Q t).testBit (2 * t + Q) = true := by
  simp only [background, Nat.testBit_shiftLeft,
    show decide (2 * t + Q ≥ Q) = true from decide_eq_true (by omega), Bool.true_and]
  rw [show 2 * t + Q - Q = 2 * t by omega, Rule30UOR.Interfaces.row_testBit,
    Rule30UOR.Interfaces.rdiag_left_edge]

/-- The later left edge survives in the aligned defect above the earlier copy. -/
theorem aligned_defect_top_bit (Q t : Nat) (hQ : 0 < Q) :
    (alignedDefect Q t).testBit (2 * (t + Q)) = true := by
  simp only [alignedDefect, background, Nat.testBit_xor, Nat.testBit_shiftLeft,
    show decide (2 * (t + Q) ≥ Q) = true from decide_eq_true (by omega), Bool.true_and]
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Interfaces.rdiag_left_edge,
    Rule30UOR.Interfaces.row_testBit, Rule30UOR.Interfaces.rdiag_gt_two_mul t _ (by omega)]
  rfl

/-- No defect bit lies above the later seed cone. -/
theorem aligned_defect_above_top (Q t j : Nat) (hj : 2 * (t + Q) < j) :
    (alignedDefect Q t).testBit j = false := by
  simp only [alignedDefect, background, Nat.testBit_xor, Nat.testBit_shiftLeft,
    show decide (j ≥ Q) = true from decide_eq_true (by omega), Bool.true_and]
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Interfaces.rdiag_gt_two_mul (t + Q) j hj,
    Rule30UOR.Interfaces.row_testBit, Rule30UOR.Interfaces.rdiag_gt_two_mul t (j - Q) (by omega)]
  rfl

/-- Exact Archimedean magnitude interval of the nonzero seeded defect. -/
theorem aligned_defect_magnitude (Q t : Nat) (hQ : 0 < Q) :
    Rule30UOR.Core.twopow (2 * (t + Q)) ≤ alignedDefect Q t ∧
      alignedDefect Q t < Rule30UOR.Core.twopow (2 * (t + Q) + 1) := by
  simp only [Rule30UOR.Interfaces.twopow_eq_pow]
  exact ⟨Nat.ge_two_pow_of_testBit (aligned_defect_top_bit Q t hQ),
    Nat.lt_pow_two_of_testBit _ (fun j hj => aligned_defect_above_top Q t j (by omega))⟩

/-- Below the alignment shift the entire later low prefix survives unchanged. -/
theorem aligned_defect_low_prefix (Q t j : Nat) (hj : j < Q) :
    (alignedDefect Q t).testBit j = (row (t + Q)).testBit j := by
  simp only [alignedDefect, background, Nat.testBit_xor, Nat.testBit_shiftLeft,
    show decide (j ≥ Q) = false from decide_eq_false (by omega), Bool.false_and, Bool.xor_false]

/-- The exact polynomial update retains both quadratic carry contributions. -/
theorem defect_step_linear (b d : Nat) :
    defectStep b d = Rule30UOR.Core.phiLinear d ^^^
      ((Rule30UOR.Core.carry d ^^^ crossCarry b d) <<< 1) := by
  simp only [defectStep, Rule30UOR.Core.phi_split, Nat.shiftLeft_xor_distrib]
  exact Nat.xor_assoc _ _ _

/-- The unshifted low edge is unchanged by every exact pair update. -/
theorem defect_step_low_bit (b d : Nat) : (defectStep b d).testBit 0 = d.testBit 0 := by
  simp [defectStep, Rule30UOR.Core.phi]

private theorem defect_step_val (b d : Nat) :
    Rule30UOR.Interfaces.val (defectStep b d) =
      Rule30UOR.Interfaces.mulω (Rule30UOR.Interfaces.val (Rule30UOR.Core.carry d ^^^ crossCarry b d)) := by
  unfold defectStep
  rw [Rule30UOR.Interfaces.val_xor, Rule30UOR.Interfaces.val_phi,
    Rule30UOR.Interfaces.val_shl, Rule30UOR.Interfaces.val_xor]
  simp only [Rule30UOR.Interfaces.add4, Rule30UOR.Interfaces.mulω]
  cases (Rule30UOR.Interfaces.val (Rule30UOR.Core.carry d)).1 <;>
    cases (Rule30UOR.Interfaces.val (Rule30UOR.Core.carry d)).2 <;>
    cases (Rule30UOR.Interfaces.val (crossCarry b d)).1 <;>
    cases (Rule30UOR.Interfaces.val (crossCarry b d)).2 <;> rfl

/-- The two F4 coordinates of the same nonlinear pair update. -/
theorem defect_step_val_coordinates (b d : Nat) :
    Rule30UOR.Interfaces.valA (defectStep b d) =
      Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry d ^^^ crossCarry b d) ∧
    Rule30UOR.Interfaces.valB (defectStep b d) = Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.valA (Rule30UOR.Core.carry d ^^^ crossCarry b d))
      (Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry d ^^^ crossCarry b d)) := by
  constructor
  · unfold Rule30UOR.Interfaces.valA Rule30UOR.Interfaces.valB
    rw [defect_step_val]
    rfl
  · unfold Rule30UOR.Interfaces.valA Rule30UOR.Interfaces.valB
    rw [defect_step_val, Rule30UOR.Scale.bxor_eq]
    rfl

private theorem edge_val_unit : ∀ j : Nat,
    Rule30UOR.Interfaces.val (1 <<< j) = (true, false) ∨
      Rule30UOR.Interfaces.val (1 <<< j) = (false, true) ∨
      Rule30UOR.Interfaces.val (1 <<< j) = (true, true) := by
  intro j
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    rw [Nat.shiftLeft_add, Rule30UOR.Interfaces.val_shl]
    rcases ih with h | h | h <;> rw [h] <;> decide +kernel

/-- An isolated edge has nonzero F4 value cycling with its exponent modulo 3.
This is not a nonvanishing assertion about the sum of all defect bits. -/
theorem edge_val_coordinates (j : Nat) :
    Rule30UOR.Interfaces.valA (1 <<< (j + 3)) = Rule30UOR.Interfaces.valA (1 <<< j) ∧
      Rule30UOR.Interfaces.valB (1 <<< (j + 3)) = Rule30UOR.Interfaces.valB (1 <<< j) ∧
      (Rule30UOR.Interfaces.valA (1 <<< j) = true ∨ Rule30UOR.Interfaces.valB (1 <<< j) = true) := by
  have shift : 1 <<< (j + 3) = (((1 <<< j) <<< 1) <<< 1) <<< 1 := by
    simp only [← Nat.shiftLeft_add]
  have cycle : Rule30UOR.Interfaces.val (1 <<< (j + 3)) = Rule30UOR.Interfaces.val (1 <<< j) := by
    rw [shift, Rule30UOR.Interfaces.val_shl, Rule30UOR.Interfaces.val_shl, Rule30UOR.Interfaces.val_shl]
    simp only [Rule30UOR.Interfaces.mulω]
    cases hv : Rule30UOR.Interfaces.val (1 <<< j) with
    | mk a b => cases a <;> cases b <;> rfl
  unfold Rule30UOR.Interfaces.valA Rule30UOR.Interfaces.valB
  rw [cycle]
  refine ⟨rfl, rfl, ?_⟩
  rcases edge_val_unit j with h | h | h <;> rw [h] <;> decide +kernel

/-- A dyadic Witt window and a physically aligned defect differ by two outer
copies. This Nat identity may be evaluated in every reading. -/
theorem aligned_defect_window (t k : Nat) :
    alignedDefect (Rule30UOR.Core.twopow k) t =
      Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k) ^^^
        (row t ^^^ (row t <<< (Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k))) := by
  rw [alignedDefect, background, Rule30UOR.Interfaces.row_scale]
  change ((((row t ^^^ (row t <<< Rule30UOR.Core.twopow k)) ^^^
      (row t <<< (Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k))) ^^^
      Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) ^^^
      (row t <<< Rule30UOR.Core.twopow k)) =
    Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k) ^^^
      (row t ^^^ (row t <<< (Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k)))
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor]
  cases (row t).testBit j <;>
    cases (row t <<< Rule30UOR.Core.twopow k).testBit j <;>
    cases (row t <<< (Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k)).testBit j <;>
    cases (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)).testBit j <;> rfl

private theorem aligned_window_center (t k : Nat) (ht : t < Rule30UOR.Core.twopow k) :
    (alignedDefect (Rule30UOR.Core.twopow k) t).testBit (t + Rule30UOR.Core.twopow k) =
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)).testBit (t + Rule30UOR.Core.twopow k) := by
  have low : (row t).testBit (t + Rule30UOR.Core.twopow k) = false := by
    rw [Rule30UOR.Interfaces.row_testBit]
    exact Rule30UOR.Interfaces.rdiag_gt_two_mul t _ (by omega)
  rw [aligned_defect_window, Nat.testBit_xor, Nat.testBit_xor, low, Nat.testBit_shiftLeft]
  rw [show decide (t + Rule30UOR.Core.twopow k ≥ Rule30UOR.Core.twopow k + Rule30UOR.Core.twopow k) = false
    from decide_eq_false (by omega)]
  simp

/-- Audit of both outer edges, the cyclotomic evaluation, and the center bit
on the same dyadic window. The two objects agree at the center in this cone,
while their top and low edge bits differ. -/
theorem dyadic_window_readings (t k : Nat) (ht : t < Rule30UOR.Core.twopow k) :
    (alignedDefect (Rule30UOR.Core.twopow k) t).testBit 0 = true ∧
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)).testBit 0 = false ∧
      (alignedDefect (Rule30UOR.Core.twopow k) t).testBit (2 * (t + Rule30UOR.Core.twopow k)) = true ∧
      (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)).testBit (2 * (t + Rule30UOR.Core.twopow k)) = false ∧
      Rule30UOR.Interfaces.valA (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) =
        Rule30UOR.Interfaces.valA (row (t + Rule30UOR.Core.twopow k)) ∧
      Rule30UOR.Interfaces.valB (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)) =
        Rule30UOR.Interfaces.valB (row (t + Rule30UOR.Core.twopow k)) ∧
      (alignedDefect (Rule30UOR.Core.twopow k) t).testBit (t + Rule30UOR.Core.twopow k) =
        (Rule30UOR.Core.winWitt t (Rule30UOR.Core.twopow k)).testBit (t + Rule30UOR.Core.twopow k) := by
  have positive : 0 < Rule30UOR.Core.twopow k := by
    rw [Rule30UOR.Interfaces.twopow_eq_pow]
    exact Nat.two_pow_pos k
  exact ⟨alignedDefect_bit_zero _ t positive,
    Rule30UOR.Interfaces.winWitt_testBit_low t k 0 (by omega),
    aligned_defect_top_bit _ t positive,
    by simpa only [Rule30UOR.Core.twopow_succ, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using Rule30UOR.Interfaces.winWitt_testBit_top_edge_zero t k ht,
    Rule30UOR.Interfaces.valA_winWitt t k, Rule30UOR.Interfaces.valB_winWitt t k,
    aligned_window_center t k ht⟩

private theorem defect_step_succ_bit (b d n : Nat) :
    (defectStep b d).testBit (n + 1) =
      xor ((phi d).testBit (n + 1)) ((crossCarry b d).testBit n) := by
  simp only [defectStep, Nat.testBit_xor, Nat.testBit_shiftLeft,
    show decide (n + 1 ≥ 1) = true from decide_eq_true (by omega), Bool.true_and, Nat.add_sub_cancel]

/-- The periodic-center requirement is imposed at bit `t+Q+1` of the next
pair update, hence at bit `t+Q` of the cross-carry. No global F4 value or
outer-edge magnitude is substituted for this particular coefficient. -/
theorem periodic_center_cross_carry (T P m t : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    (phi (alignedDefect (m * P) t)).testBit (t + m * P + 1) =
      (crossCarry (background (m * P) t) (alignedDefect (m * P) t)).testBit (t + m * P) := by
  have same := Rule30UOR.Scale.center_mul hc m (t + 1) (by omega)
  have hz : (alignedDefect (m * P) (t + 1)).testBit ((t + 1) + m * P) = false := by
    rw [alignedDefect_center]
    apply (difference_eq_false_iff center (m * P) (t + 1)).2
    simpa only [Rule30UOR.Scale.center_eq_kit] using same
  rw [show (t + 1) + m * P = (t + m * P) + 1 by omega,
    alignedDefect_step, defect_step_succ_bit] at hz
  have xor_false : ∀ a b : Bool, xor a b = false → a = b := by decide +kernel
  exact xor_false _ _ hz

/-- The same actual lag-1 seed defect loses its nonzero F4 value while both
outer edges survive. Zero F4 value occurs with either center-bit value. -/
theorem seed_val_cancellation :
    alignedDefect 1 0 = 5 ∧ Rule30UOR.Interfaces.valA (alignedDefect 1 0) = false ∧
      Rule30UOR.Interfaces.valB (alignedDefect 1 0) = true ∧
      alignedDefect 1 2 = 93 ∧ Rule30UOR.Interfaces.valA (alignedDefect 1 2) = false ∧
      Rule30UOR.Interfaces.valB (alignedDefect 1 2) = false ∧ (alignedDefect 1 2).testBit 3 = true ∧
      alignedDefect 4 0 = 385 ∧ Rule30UOR.Interfaces.valA (alignedDefect 4 0) = false ∧
      Rule30UOR.Interfaces.valB (alignedDefect 4 0) = false ∧ (alignedDefect 4 0).testBit 4 = false := by
  decide +kernel

/-- A Phi_3 block centered at a chosen coefficient. -/
def centerFlipMask (n : Nat) : Nat := 7 <<< n

private theorem mask_val_zero : ∀ n : Nat,
    Rule30UOR.Interfaces.val (centerFlipMask n) = (false, false) := by
  intro n
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    unfold centerFlipMask at ih ⊢
    rw [Nat.shiftLeft_add, Rule30UOR.Interfaces.val_shl, ih]
    rfl

/-- The F4 coordinates and every bit outside `[n,n+2]` fail to distinguish a
center flip. This is a projection statement about Nat words, not a claim
that masking preserves the seeded orbit or its nonlinear update. -/
theorem center_flip_mask_invisible (d n j : Nat) (hj : j < n ∨ n + 2 < j) :
    (d ^^^ centerFlipMask n).testBit n = !(d.testBit n) ∧
      (d ^^^ centerFlipMask n).testBit j = d.testBit j ∧
      Rule30UOR.Interfaces.valA (d ^^^ centerFlipMask n) = Rule30UOR.Interfaces.valA d ∧
      Rule30UOR.Interfaces.valB (d ^^^ centerFlipMask n) = Rule30UOR.Interfaces.valB d := by
  have bit7 (i : Nat) : (7 : Nat).testBit i = decide (i < 3) := by
    rw [show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.testBit_two_pow_sub_one]
  have mn : (centerFlipMask n).testBit n = true := by
    simp [centerFlipMask, Nat.testBit_shiftLeft]
  have mj : (centerFlipMask n).testBit j = false := by
    simp only [centerFlipMask, Nat.testBit_shiftLeft, bit7]
    by_cases hn : j ≥ n
    · rw [show decide (j ≥ n) = true from decide_eq_true hn, Bool.true_and]
      exact decide_eq_false (by omega)
    · rw [show decide (j ≥ n) = false from decide_eq_false hn, Bool.false_and]
  have vv : Rule30UOR.Interfaces.val (d ^^^ centerFlipMask n) = Rule30UOR.Interfaces.val d := by
    rw [Rule30UOR.Interfaces.val_xor, mask_val_zero]
    simp only [Rule30UOR.Interfaces.add4]
    cases hv : Rule30UOR.Interfaces.val d with
    | mk a b => cases a <;> cases b <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.testBit_xor, mn]
    cases d.testBit n <;> rfl
  · rw [Nat.testBit_xor, mj, Bool.xor_false]
  · exact congrArg Prod.fst vv
  · exact congrArg Prod.snd vv

/-! ## F4 transport at the moving physical center cut

The observer word `row t >> t` begins at the center and continues to the
left seed edge. Its F4 update has a boundary term: the masked right head.
Under a periodic center, the difference of that boundary term is precisely
the column-minus-one defect. The full carry difference remains in the law.
-/

/-- Center at bit zero, left seed edge at bit `t`. -/
def observerCode (t : Nat) : Nat := row t >>> t

/-- The actual right-head input that survives the center's OR mask. -/
def observerInput (t : Nat) : Bool := (!Rule30UOR.Core.center t) && rightCell t 1

/-- The aligned temporal defect viewed from its moving physical center. -/
def observerDefect (Q t : Nat) : Nat := alignedDefect Q t >>> (t + Q)

theorem observer_code_readout (t j : Nat) : (observerCode t).testBit j = leftCell t j := by
  rw [observerCode, Nat.testBit_shiftRight, Rule30UOR.Interfaces.row_testBit,
    Rule30UOR.Right.rdiag_eq_R]
  unfold Rule30Diagonals.R leftCell
  congr 1
  omega

theorem observer_defect_alignment (Q t : Nat) :
    observerDefect Q t = observerCode (t + Q) ^^^ observerCode t := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [observerDefect, alignedDefect, background, observerCode,
    Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_shiftLeft,
    show decide (t + Q + j ≥ Q) = true from decide_eq_true (by omega), Bool.true_and]
  rw [show t + Q + j - Q = t + j by omega]

/-- Exact coefficient index of the moving physical cut. -/
theorem observer_defect_readout (Q t j : Nat) :
    (observerDefect Q t).testBit j = (alignedDefect Q t).testBit (t + Q + j) := by
  simp only [observerDefect, Nat.testBit_shiftRight]

private def observerPoly (x : Nat) (input : Bool) : Nat :=
  ((((x >>> 1) ^^^ x) ^^^ (x <<< 1)) ^^^ Rule30UOR.Core.carry x) ^^^ input.toNat

private theorem carry_bit (x j : Nat) :
    (Rule30UOR.Core.carry x).testBit j = (x.testBit j && (x <<< 1).testBit j) := by
  change (x &&& (x <<< 1)).testBit j = _
  rw [Nat.testBit_and]

private theorem observer_code_step (t : Nat) :
    observerCode (t + 1) = observerPoly (observerCode t) (observerInput t) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [observerPoly, Nat.testBit_xor, Nat.testBit_shiftRight, carry_bit,
    Nat.testBit_shiftLeft, Nat.testBit_bool_toNat]
  cases j with
  | zero =>
    simp only [Nat.add_zero, show decide (0 ≥ 1) = false by decide,
      show decide (0 = 0) = true by decide, decide_true, Bool.false_and, Bool.true_and, Bool.and_false,
      Bool.xor_false, observer_code_readout]
    unfold observerInput rightCell leftCell
    rw [Rule30UOR.Scale.center_eq_kit]
    change rule (cell t (-1)) (cell t 0) (cell t 1) =
      xor (xor (cell t (-1)) (cell t 0)) ((!cell t 0) && cell t 1)
    cases cell t (-1) <;> cases cell t 0 <;> cases cell t 1 <;> rfl
  | succ j =>
    simp only [show decide (j + 1 ≥ 1) = true from decide_eq_true (by omega),
      show decide (j + 1 = 0) = false from decide_eq_false (by omega),
      Nat.add_sub_cancel, Bool.true_and, Bool.false_and, Bool.xor_false,
      observer_code_readout]
    unfold leftCell
    change rule (cell t (-((j + 1 : Nat) : Int) - 1))
      (cell t (-((j + 1 : Nat) : Int))) (cell t (-((j + 1 : Nat) : Int) + 1)) = _
    rw [show -((j + 1 : Nat) : Int) - 1 = -((j + 2 : Nat) : Int) by omega,
      show -((j + 1 : Nat) : Int) + 1 = -(j : Int) by omega,
      show 1 + (j + 1) = j + 2 by omega]
    cases cell t (-((j + 2 : Nat) : Int)) <;>
      cases cell t (-((j + 1 : Nat) : Int)) <;> cases cell t (-(j : Int)) <;> rfl

private theorem val_unit (input : Bool) :
    Rule30UOR.Interfaces.val input.toNat = (input, false) := by
  cases input <;> decide +kernel

private theorem observer_poly_val (x : Nat) (input : Bool) :
    Rule30UOR.Interfaces.val (observerPoly x input) =
      (xor (x.testBit 0) (xor (Rule30UOR.Interfaces.valA (Rule30UOR.Core.carry x)) input),
        xor (x.testBit 0) (Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry x))) := by
  have div_shift : x / 2 = x >>> 1 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have decomposed := Rule30UOR.Interfaces.val_eq x
  rw [div_shift] at decomposed
  unfold observerPoly
  simp only [Rule30UOR.Interfaces.val_xor, Rule30UOR.Interfaces.val_shl, val_unit]
  simp only [decomposed, Rule30UOR.Interfaces.valA, Rule30UOR.Interfaces.valB,
    Rule30UOR.Interfaces.add4, Rule30UOR.Interfaces.mulω]
  cases x.testBit 0 <;> cases input <;>
    cases (Rule30UOR.Interfaces.val (x >>> 1)).1 <;>
    cases (Rule30UOR.Interfaces.val (x >>> 1)).2 <;>
    cases (Rule30UOR.Interfaces.val (Rule30UOR.Core.carry x)).1 <;>
    cases (Rule30UOR.Interfaces.val (Rule30UOR.Core.carry x)).2 <;> rfl

/-- The center cut restores the boundary terms lost by whole-row evaluation. -/
theorem observer_val_step (t : Nat) :
    Rule30UOR.Interfaces.valA (observerCode (t + 1)) = Rule30UOR.Core.bxor
      (Rule30UOR.Core.center t)
      (Rule30UOR.Core.bxor (Rule30UOR.Interfaces.valA (Rule30UOR.Core.carry (observerCode t))) (observerInput t)) ∧
    Rule30UOR.Interfaces.valB (observerCode (t + 1)) = Rule30UOR.Core.bxor
      (Rule30UOR.Core.center t) (Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry (observerCode t))) := by
  have c : (observerCode t).testBit 0 = Rule30UOR.Core.center t := by
    rw [observer_code_readout]
    simp only [leftCell, Int.natCast_zero, Int.neg_zero,
      Rule30UOR.Scale.center_eq_kit, Rule30Prize.center]
  unfold Rule30UOR.Interfaces.valA Rule30UOR.Interfaces.valB
  rw [observer_code_step, observer_poly_val, c]
  simp only [Rule30UOR.Scale.bxor_eq]
  exact ⟨rfl, rfl⟩

private theorem observer_input_difference (T P m t : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    difference observerInput (m * P) t = leftDefect (m * P) t 1 := by
  have hp : ∀ s, T ≤ s → center (s + P) = center s := by
    intro s hs
    simpa only [Rule30UOR.Scale.center_eq_kit] using hc s hs
  have same := Rule30UOR.Scale.center_mul hc m t ht
  have matched := center_matching hp m t ht
  change xor (observerInput (t + m * P)) (observerInput t) = defect (m * P) t (-1)
  unfold observerInput
  rw [same, matched]
  simp only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center, rightCell, defect, difference]
  cases cell t 0 <;> cases cell t 1 <;> cases cell (t + m * P) 1 <;> rfl

private theorem observer_xor_coordinates (x y : Nat) :
    Rule30UOR.Interfaces.valA (x ^^^ y) = xor (Rule30UOR.Interfaces.valA x) (Rule30UOR.Interfaces.valA y) ∧
      Rule30UOR.Interfaces.valB (x ^^^ y) = xor (Rule30UOR.Interfaces.valB x) (Rule30UOR.Interfaces.valB y) := by
  unfold Rule30UOR.Interfaces.valA Rule30UOR.Interfaces.valB
  rw [Rule30UOR.Interfaces.val_xor]
  exact ⟨rfl, rfl⟩

/-- At the physical center, periodicity cancels the common center term but
retains both the full carry difference and the actual left-neighbor defect. -/
theorem periodic_observer_val_step (T P m t : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    Rule30UOR.Interfaces.valA (observerDefect (m * P) (t + 1)) = Rule30UOR.Core.bxor
      (Rule30UOR.Interfaces.valA (Rule30UOR.Core.carry (observerCode (t + m * P)) ^^^
        Rule30UOR.Core.carry (observerCode t))) (leftDefect (m * P) t 1) ∧
    Rule30UOR.Interfaces.valB (observerDefect (m * P) (t + 1)) =
      Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry (observerCode (t + m * P)) ^^^
        Rule30UOR.Core.carry (observerCode t)) := by
  have later := observer_val_step (t + m * P)
  have earlier := observer_val_step t
  have same := Rule30UOR.Scale.center_mul hc m t ht
  have boundary := observer_input_difference T P m t hc ht
  change xor (observerInput (t + m * P)) (observerInput t) = leftDefect (m * P) t 1 at boundary
  rw [observer_defect_alignment,
    show (t + 1) + m * P = (t + m * P) + 1 by omega]
  have out := observer_xor_coordinates (observerCode ((t + m * P) + 1)) (observerCode (t + 1))
  have carr := observer_xor_coordinates (Rule30UOR.Core.carry (observerCode (t + m * P)))
    (Rule30UOR.Core.carry (observerCode t))
  rw [out.1, out.2, carr.1, carr.2, later.1, earlier.1, later.2, earlier.2, same]
  simp only [Rule30UOR.Scale.bxor_eq]
  rw [← boundary]
  cases Rule30UOR.Core.center t <;>
    cases observerInput (t + m * P) <;> cases observerInput t <;>
    cases Rule30UOR.Interfaces.valA (Rule30UOR.Core.carry (observerCode (t + m * P))) <;>
    cases Rule30UOR.Interfaces.valA (Rule30UOR.Core.carry (observerCode t)) <;>
    cases Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry (observerCode (t + m * P))) <;>
    cases Rule30UOR.Interfaces.valB (Rule30UOR.Core.carry (observerCode t)) <;> exact ⟨rfl, rfl⟩

/-- The two seed/periodicity constraints coexist at distinct coefficients of
one observer word: its leading bit is 1 and its center bit is 0. -/
theorem periodic_observer_edges (T P m t : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    (observerDefect (m * P) t).testBit (t + m * P) = true ∧
      (observerDefect (m * P) t).testBit 0 = false := by
  have top := aligned_defect_top_bit (m * P) t (Nat.mul_pos hm hP)
  have same := Rule30UOR.Scale.center_mul hc m t ht
  constructor
  · simpa only [observerDefect, Nat.testBit_shiftRight, Nat.two_mul] using top
  · simp only [observerDefect, Nat.testBit_shiftRight, Nat.add_zero]
    rw [alignedDefect_center]
    apply (difference_eq_false_iff center (m * P) t).2
    simpa only [Rule30UOR.Scale.center_eq_kit] using same

/-- At the moving cut, zero F4 value can accompany a nonzero center bit,
and nonzero F4 value can accompany a zero center bit. Both are actual seed
comparisons, without an infinite periodic-center premise. -/
theorem observer_seed_zero_val :
    observerDefect 2 0 = 7 ∧ Rule30UOR.Interfaces.valA (observerDefect 2 0) = false ∧
      Rule30UOR.Interfaces.valB (observerDefect 2 0) = false ∧
      (observerDefect 2 0).testBit 0 = true ∧
    observerDefect 4 0 = 24 ∧ Rule30UOR.Interfaces.valA (observerDefect 4 0) = true ∧
      Rule30UOR.Interfaces.valB (observerDefect 4 0) = true ∧
      (observerDefect 4 0).testBit 0 = false := by
  decide +kernel

end Rule30UOR.WittDefect
