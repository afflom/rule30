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

end Rule30UOR.WittDefect
