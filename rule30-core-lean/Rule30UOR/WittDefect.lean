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

end Rule30UOR.WittDefect
