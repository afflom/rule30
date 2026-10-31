module
public import Rule30UOR.Ledger
public import Rule30UOR.Interfaces.Part03
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The edge-sourced and interior-sourced ledgers

The carry of a row is the mask of adjacent black pairs. Two of them are
explicit at every time: the left edge pair `(-t, -t+1)` (both edge diagonals
are black), which is bit `2t` of the carry, and the right pair `(0, 1)` at the
right edge, bit `1`, which is `rdiag 1 t`. Splitting the carry into these edge
sources and the interior mask splits the ledger, by linearity of the Rule-150
propagation, into an edge-sourced ledger — the linear evolution of an
explicit, periodic source — and an interior-sourced ledger. The center is the
complement of the XOR of their diagonals. So the aperiodicity of the center is
the aperiodicity of the interior-sourced diagonal against the edge-sourced
background: the bulk carries alone carry the solution. -/

@[expose] public section

namespace Rule30UOR.EdgeSplit

open Rule30UOR.Core Rule30UOR.Ledger

/-- The two explicit carry events of row `t`: the left edge pair and the right pair. -/
def edgeSource (t : Nat) : Nat := (1 <<< (2 * t)) ^^^ (if rdiag 1 t then 2 else 0)

/-- The interior carry mask: the carry of the row with its two edge events removed. -/
def interior (t : Nat) : Nat := carry (row t) ^^^ edgeSource t

theorem carry_split (t : Nat) : carry (row t) = edgeSource t ^^^ interior t := by
  unfold interior
  rw [Nat.xor_comm (carry (row t)) (edgeSource t)]
  exact (Rule30UOR.Ledger.xor_xor_self _ _).symm

/-- The left edge pair: bit `2t` of the carry of row `t` is set for `t ≥ 1`. -/
theorem carry_row_left_edge (t : Nat) (ht : 1 ≤ t) : (carry (row t)).testBit (2 * t) = true := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by cfomega⟩
  rw [show 2 * (s + 1) = (2 * s + 1) + 1 by cfomega, Rule30UOR.Interfaces.carry_row_testBit_succ]
  have h1 : rdiag (2 * s + 1 + 1) (s + 1) = true := by
    rw [show 2 * s + 1 + 1 = 2 * (s + 1) by cfomega]
    exact Rule30UOR.Interfaces.rdiag_left_edge (s + 1)
  have h2 : rdiag (2 * s + 1) (s + 1) = true := by
    rw [Rule30UOR.Right.rdiag_eq_R]
    unfold Ruliology.CellularAutomata.Rule30Diagonals.R
    rw [show ((s + 1 : Nat) : Int) - ((2 * s + 1 : Nat) : Int) = -((s : Nat) : Int) by push_cast; cfomega]
    have := Rule30UOR.Interfaces.ldiag_eq_cell_neg 1 s
    rw [Rule30UOR.Interfaces.ldiag_one_eq_true, Rule30UOR.Scale.cell_eq_kit, Nat.add_comm 1 s] at this
    exact this.symm
  rw [h1, h2]; rfl

/-- The right pair: bit `1` of the carry of row `t` is `rdiag 1 t` (the right edge is black). -/
theorem carry_row_right_pair (t : Nat) : (carry (row t)).testBit 1 = rdiag 1 t := by
  rw [show (1 : Nat) = 0 + 1 from rfl, Rule30UOR.Interfaces.carry_row_testBit_succ, Rule30UOR.Right.rdiag_eq_R,
    Rule30UOR.Right.rdiag_eq_R, Ruliology.CellularAutomata.Rule30Diagonals.R_zero]
  cases Ruliology.CellularAutomata.Rule30Diagonals.R 1 t <;> rfl

/-- The interior mask carries neither edge event. -/
theorem interior_testBit_left_edge (t : Nat) (ht : 1 ≤ t) : (interior t).testBit (2 * t) = false := by
  unfold interior edgeSource
  rw [Nat.testBit_xor, Nat.testBit_xor, carry_row_left_edge t ht, Nat.testBit_shiftLeft]
  have h1 : (if rdiag 1 t then 2 else 0).testBit (2 * t) = false := by
    cases rdiag 1 t
    · simp
    · show (2 : Nat).testBit (2 * t) = false
      rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]
      simp; cfomega
  rw [h1]
  simp

theorem interior_testBit_right_pair (t : Nat) (ht : 1 ≤ t) : (interior t).testBit 1 = false := by
  unfold interior edgeSource
  rw [Nat.testBit_xor, Nat.testBit_xor, carry_row_right_pair, Nat.testBit_shiftLeft]
  have h1 : (if rdiag 1 t then 2 else 0).testBit 1 = rdiag 1 t := by
    cases rdiag 1 t <;> rfl
  rw [h1]
  have h2 : decide (1 ≥ 2 * t) = false := by simp; cfomega
  rw [h2]
  cases rdiag 1 t <;> rfl

/-! ## The split ledgers -/

/-- The ledger sourced by the edge events only. -/
def edgeLedger : Nat → Nat
  | 0 => 0
  | t + 1 => phiLinear (edgeLedger t) ^^^ (edgeSource t <<< 1)

/-- The ledger sourced by the interior carries only. -/
def interiorLedger : Nat → Nat
  | 0 => 0
  | t + 1 => phiLinear (interiorLedger t) ^^^ (interior t <<< 1)

/-- **The ledger splits**: `winWitt 0 t = edgeLedger t ^^^ interiorLedger t`. -/
theorem ledger_split : ∀ t, winWitt 0 t = edgeLedger t ^^^ interiorLedger t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (winWitt 0 t) ^^^ (carry (row (0 + t)) <<< 1) =
      (phiLinear (edgeLedger t) ^^^ (edgeSource t <<< 1)) ^^^ (phiLinear (interiorLedger t) ^^^ (interior t <<< 1))
    rw [Nat.zero_add, ih, phiLinear_xor, carry_split, Nat.shiftLeft_xor_distrib]
    simp only [Nat.xor_assoc, Nat.xor_comm, Rule30UOR.Ledger.xor_left_comm]

/-- **The center is the complement of the XOR of the two diagonals.** -/
theorem center_eq_not_edge_xor_interior (t : Nat) :
    center t = !((edgeLedger t).testBit t ^^ (interiorLedger t).testBit t) := by
  rw [center_eq_not_ledgerDiagonal]
  unfold ledgerDiagonal
  rw [ledger_split, Nat.testBit_xor]

/-- The diagonal of the interior-sourced ledger. -/
def interiorDiagonal (t : Nat) : Bool := (interiorLedger t).testBit t

/-- The diagonal of the edge-sourced ledger. -/
def edgeDiagonal (t : Nat) : Bool := (edgeLedger t).testBit t

theorem center_eq_not_bxor_diagonals (t : Nat) :
    center t = !(bxor (edgeDiagonal t) (interiorDiagonal t)) := by
  rw [center_eq_not_edge_xor_interior, Rule30UOR.Scale.bxor_eq]
  rfl

/-! ## The edge diagonal in closed form

The edge-sourced ledger is the Rule-150 propagation of the edge events,
`edgeLedger t = ⊕_{m<t} q^(t-1-m) · (edgeSource m · X)`, and its diagonal is a
finite XOR of trinomial parities: the left-edge event of row `m` reaches the
center through `trinomialParity (t-1-m) (t-2m-1)`, the right pair through
`trinomialParity (t-1-m) (t-2)` when `rdiag 1 m`. The background of the
center is therefore an explicit 2-automatic expression. -/

theorem phiLinearPow_xor (n a b : Nat) : phiLinearPow n (a ^^^ b) = phiLinearPow n a ^^^ phiLinearPow n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [phiLinearPow_step, phiLinearPow_step, phiLinearPow_step, ih, phiLinear_xor]

theorem phiLinearPow_shiftLeft (n k y : Nat) : phiLinearPow n (y <<< k) = phiLinearPow n y <<< k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [phiLinearPow_step, phiLinearPow_step, ih, phiLinear_eq_phiLin, phiLinear_eq_phiLin, phiLin_shiftLeft]

/-- Bit `t` of `q^n · X^k`. -/
theorem testBit_phiLinearPow_shift (n k t : Nat) :
    (phiLinearPow n 1 <<< k).testBit t = (if k ≤ t then trinomialParity n (t - k) else false) := by
  rw [Nat.testBit_shiftLeft, phiLinearPow_eq_phiLinPow, testBit_phiLinPow_eq_trinomialParity]
  rcases Nat.lt_or_ge t k with h | h
  · rw [decide_eq_false (by cfomega), if_neg (by cfomega)]; rfl
  · rw [decide_eq_true h, if_pos h]; rfl

/-- The contribution of row `m`'s edge events to the center at time `t`
(`m < t`): bit `t` of `q^(t-1-m) · (edgeSource m · X)`. -/
def edgeTerm (t m : Nat) : Bool :=
  bxor (if 2 * m + 1 ≤ t then trinomialParity (t - 1 - m) (t - (2 * m + 1)) else false)
    (if rdiag 1 m then (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false) else false)

theorem phiLinear_zero : phiLinear 0 = 0 := by
  show (0 ^^^ (0 <<< 1)) ^^^ (0 <<< 2) = 0
  simp

theorem phiLinearPow_zero (n : Nat) : phiLinearPow n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [phiLinearPow_step, ih, phiLinear_zero]

theorem testBit_edge_propagated (t m : Nat) :
    (phiLinearPow (t - 1 - m) (edgeSource m <<< 1)).testBit t = edgeTerm t m := by
  have h2 : (phiLinearPow (t - 1 - m) ((if rdiag 1 m then 2 else 0) <<< 1)).testBit t =
      (if rdiag 1 m then (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false) else false) := by
    cases rdiag 1 m
    · show (phiLinearPow (t - 1 - m) (0 <<< 1)).testBit t = false
      rw [phiLinearPow_shiftLeft, phiLinearPow_zero]
      simp
    · show (phiLinearPow (t - 1 - m) (2 <<< 1)).testBit t = (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false)
      rw [show (2 : Nat) <<< 1 = 1 <<< 2 from rfl, phiLinearPow_shiftLeft, testBit_phiLinearPow_shift]
  unfold edgeSource edgeTerm
  rw [Nat.shiftLeft_xor_distrib, phiLinearPow_xor, Nat.testBit_xor, ← Nat.shiftLeft_add,
    phiLinearPow_shiftLeft, testBit_phiLinearPow_shift, h2, Rule30UOR.Scale.bxor_eq]

/-- The partial sums of the propagated edge events. -/
def edgeLedgerSum (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => edgeLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (edgeSource n <<< 1)

theorem phiLinear_edgeLedgerSum (t : Nat) : ∀ n, n ≤ t →
    phiLinear (edgeLedgerSum t n) = edgeLedgerSum (t + 1) n := by
  intro n
  induction n with
  | zero => intro _; exact phiLinear_zero
  | succ n ih =>
    intro hn
    show phiLinear (edgeLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (edgeSource n <<< 1)) =
      edgeLedgerSum (t + 1) n ^^^ phiLinearPow (t + 1 - 1 - n) (edgeSource n <<< 1)
    rw [phiLinear_xor, ih (by cfomega), show t + 1 - 1 - n = (t - 1 - n) + 1 by cfomega, phiLinearPow_step]

theorem edgeLedger_eq_sum : ∀ t, edgeLedger t = edgeLedgerSum t t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (edgeLedger t) ^^^ (edgeSource t <<< 1) =
      edgeLedgerSum (t + 1) t ^^^ phiLinearPow (t + 1 - 1 - t) (edgeSource t <<< 1)
    rw [ih, phiLinear_edgeLedgerSum t t (Nat.le_refl t), show t + 1 - 1 - t = 0 by cfomega]
    rfl

/-- The closed form of the edge diagonal: the XOR of the edge terms over `m < n`. -/
def edgeFormula (t : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => bxor (edgeFormula t n) (edgeTerm t n)

theorem testBit_edgeLedgerSum (t : Nat) : ∀ n, (edgeLedgerSum t n).testBit t = edgeFormula t n := by
  intro n
  induction n with
  | zero => show (0 : Nat).testBit t = false; simp
  | succ n ih =>
    show (edgeLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (edgeSource n <<< 1)).testBit t = bxor (edgeFormula t n) (edgeTerm t n)
    rw [Nat.testBit_xor, ih, testBit_edge_propagated, Rule30UOR.Scale.bxor_eq]

/-- **The edge diagonal is an explicit 2-automatic expression.** -/
theorem edgeDiagonal_eq_formula (t : Nat) : edgeDiagonal t = edgeFormula t t := by
  unfold edgeDiagonal
  rw [edgeLedger_eq_sum, testBit_edgeLedgerSum]

/-- The center against the explicit background: `center t = ¬(edgeFormula t t ⊕ interiorDiagonal t)`. -/
theorem center_eq_not_formula_xor_interior (t : Nat) :
    center t = !(bxor (edgeFormula t t) (interiorDiagonal t)) := by
  rw [center_eq_not_bxor_diagonals, edgeDiagonal_eq_formula]

end Rule30UOR.EdgeSplit
