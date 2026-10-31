module
public import Rule30UOR.Ledger
public import Rule30UOR.Interfaces.Part03
public import Rule30UOR.WittDefect
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

/-! ## The interior diagonal in the same form

Bit `t` of `q^n · y` is the convolution of the bits of `y` with the trinomial
row: `⊕_i y_i · trinomialParity n (t - i)` (`testBit_phiLinearPow_conv`, by the
binary decomposition of `y`). Applied to the interior masks, the interior
diagonal is the explicit XOR over the rows `m < t` and the interior carry
events `i` of row `m` of `trinomialParity (t-1-m) (t-1-i)`: the parity of
the bulk carry events on the gasket, which is the object of the open leaf. -/

/-- Convolution of the bits of `y` (fuel `f ≥ y`) with the trinomial row `n`, read at `t`. -/
def convFuel (n : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | f + 1, y, t =>
    if y = 0 then false
    else bxor (if y % 2 = 1 then trinomialParity n t else false)
      (if 1 ≤ t then convFuel n f (y / 2) (t - 1) else false)

def conv (n y t : Nat) : Bool := convFuel n y y t

theorem convFuel_congr (n : Nat) : ∀ f g y t, y ≤ f → y ≤ g → convFuel n f y t = convFuel n g y t
  | 0, g, y, t, hf, _ => by
    have : y = 0 := by cfomega
    subst this
    cases g <;> rfl
  | f + 1, 0, y, t, _, hg => by
    have : y = 0 := by cfomega
    subst this
    rfl
  | f + 1, g + 1, y, t, hf, hg => by
    show (if y = 0 then false else _) = (if y = 0 then false else _)
    by_cases hy : y = 0
    · rw [if_pos hy, if_pos hy]
    · rw [if_neg hy, if_neg hy, convFuel_congr n f g (y / 2) (t - 1) (by cfomega) (by cfomega)]

/-- `y = 2 (y / 2) ⊕ (y mod 2)` as bit vectors. -/
theorem nat_eq_shift_xor_mod (y : Nat) : y = ((y / 2) <<< 1) ^^^ (y % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    rw [Nat.mod_mod]
    simp
  | succ i =>
    have h2 : (2 : Nat) ≤ 2 ^ (i + 1) := @Nat.pow_le_pow_right 2 (by decide) 1 (i + 1) (by cfomega)
    have hlt : y % 2 < 2 ^ (i + 1) := Nat.lt_of_lt_of_le (Nat.mod_lt y (by decide)) h2
    rw [Nat.testBit_add_one, decide_eq_true (by cfomega : i + 1 ≥ 1), Bool.true_and, Nat.add_sub_cancel,
      Nat.testBit_lt_two_pow hlt]
    cases (y / 2).testBit i <;> rfl

/-- **The convolution law**: bit `t` of `q^n · y`. -/
theorem testBit_phiLinearPow_conv (n : Nat) : ∀ y t, (phiLinearPow n y).testBit t = conv n y t := by
  intro y
  induction y using Nat.strongRecOn with
  | ind y ih =>
    intro t
    unfold conv
    rcases Nat.eq_zero_or_pos y with h0 | hpos
    · subst h0
      rw [phiLinearPow_zero, Nat.zero_testBit]
      rfl
    · obtain ⟨f, rfl⟩ : ∃ f, y = f + 1 := ⟨y - 1, by cfomega⟩
      show (phiLinearPow n (f + 1)).testBit t = (if f + 1 = 0 then false else _)
      rw [if_neg (by cfomega)]
      have hrec : ∀ t', convFuel n f ((f + 1) / 2) t' = conv n ((f + 1) / 2) t' := fun t' =>
        convFuel_congr n f ((f + 1) / 2) ((f + 1) / 2) t' (by cfomega) (Nat.le_refl _)
      rw [hrec]
      conv => lhs; rw [nat_eq_shift_xor_mod (f + 1)]
      rw [phiLinearPow_xor, Nat.testBit_xor, phiLinearPow_shiftLeft, Nat.testBit_shiftLeft]
      have hlow : (phiLinearPow n ((f + 1) % 2)).testBit t = (if (f + 1) % 2 = 1 then trinomialParity n t else false) := by
        rcases Nat.mod_two_eq_zero_or_one (f + 1) with h | h
        · rw [h, phiLinearPow_zero, if_neg (by decide)]; simp
        · rw [h, if_pos rfl, phiLinearPow_eq_phiLinPow, testBit_phiLinPow_eq_trinomialParity]
      have hlt : (f + 1) / 2 < f + 1 := Nat.div_lt_self (by cfomega) (by decide)
      rw [hlow, ih ((f + 1) / 2) hlt]
      rcases Nat.lt_or_ge t 1 with ht | ht
      · have hd : decide (t ≥ 1) = false := decide_eq_false (by cfomega)
        rw [hd, if_neg (by cfomega : ¬ (1 ≤ t))]
        cases (if (f + 1) % 2 = 1 then trinomialParity n t else false) <;> rfl
      · have hd : decide (t ≥ 1) = true := decide_eq_true ht
        rw [hd, if_pos ht, Bool.true_and, Rule30UOR.Scale.bxor_eq]
        cases (if (f + 1) % 2 = 1 then trinomialParity n t else false) <;>
          cases conv n ((f + 1) / 2) (t - 1) <;> rfl

/-- The partial sums of the propagated interior masks. -/
def interiorLedgerSum (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => interiorLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (interior n <<< 1)

theorem phiLinear_interiorLedgerSum (t : Nat) : ∀ n, n ≤ t →
    phiLinear (interiorLedgerSum t n) = interiorLedgerSum (t + 1) n := by
  intro n
  induction n with
  | zero => intro _; exact phiLinear_zero
  | succ n ih =>
    intro hn
    show phiLinear (interiorLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (interior n <<< 1)) =
      interiorLedgerSum (t + 1) n ^^^ phiLinearPow (t + 1 - 1 - n) (interior n <<< 1)
    rw [phiLinear_xor, ih (by cfomega), show t + 1 - 1 - n = (t - 1 - n) + 1 by cfomega, phiLinearPow_step]

theorem interiorLedger_eq_sum : ∀ t, interiorLedger t = interiorLedgerSum t t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (interiorLedger t) ^^^ (interior t <<< 1) =
      interiorLedgerSum (t + 1) t ^^^ phiLinearPow (t + 1 - 1 - t) (interior t <<< 1)
    rw [ih, phiLinear_interiorLedgerSum t t (Nat.le_refl t), show t + 1 - 1 - t = 0 by cfomega]
    rfl

/-- The closed form of the interior diagonal: the XOR over `m < n` of the
convolution of row `m`'s interior carries with the trinomial row `t-1-m`. -/
def interiorFormula (t : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => bxor (interiorFormula t n) (conv (t - 1 - n) (interior n <<< 1) t)

theorem testBit_interiorLedgerSum (t : Nat) : ∀ n, (interiorLedgerSum t n).testBit t = interiorFormula t n := by
  intro n
  induction n with
  | zero => show (0 : Nat).testBit t = false; simp
  | succ n ih =>
    show (interiorLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (interior n <<< 1)).testBit t =
      bxor (interiorFormula t n) (conv (t - 1 - n) (interior n <<< 1) t)
    rw [Nat.testBit_xor, ih, testBit_phiLinearPow_conv, Rule30UOR.Scale.bxor_eq]

/-- **The interior diagonal is the gasket parity of the bulk carries.** -/
theorem interiorDiagonal_eq_formula (t : Nat) : interiorDiagonal t = interiorFormula t t := by
  unfold interiorDiagonal
  rw [interiorLedger_eq_sum, testBit_interiorLedgerSum]

/-- The right pair alternates: `rdiag 1 t = [t odd]`, so the edge source is fully explicit. -/
theorem rdiag_one_eq_parity : ∀ t, rdiag 1 t = decide (t % 2 = 1) := by
  intro t
  rw [Rule30UOR.Right.rdiag_eq_R]
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Ruliology.CellularAutomata.Rule30Diagonals.R_one_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · rw [h, show (t + 1) % 2 = 1 by cfomega]; rfl
    · rw [h, show (t + 1) % 2 = 0 by cfomega]; rfl

/-- The edge term with the right pair made explicit. -/
theorem edgeTerm_eq (t m : Nat) :
    edgeTerm t m = bxor (if 2 * m + 1 ≤ t then trinomialParity (t - 1 - m) (t - (2 * m + 1)) else false)
      (if m % 2 = 1 then (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false) else false) := by
  unfold edgeTerm
  rw [rdiag_one_eq_parity]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl

/-- A center period `P` from `T`, in the carries: the interior parity, read against the
edge parity, repeats with period `P`. -/
def InteriorAgainstEdge (T P : Nat) : Prop :=
  ∀ t, T ≤ t → bxor (interiorFormula (t + P) (t + P)) (edgeFormula (t + P) (t + P)) =
    bxor (interiorFormula t t) (edgeFormula t t)

/-- **The center, fully explicit in the carries**:
`center t = ¬(edgeFormula t t ⊕ interiorFormula t t)`. -/
theorem center_eq_not_formulas (t : Nat) :
    center t = !(bxor (edgeFormula t t) (interiorFormula t t)) := by
  rw [center_eq_not_formula_xor_interior, interiorDiagonal_eq_formula]

/-- **`aperiodic-compensation` in the carries**: a center period is exactly a period of the
interior parity against the edge parity. -/
theorem centerPeriodic_iff_interiorAgainstEdge (T P : Nat) :
    Rule30UOR.Scale.CenterPeriodic T P ↔ InteriorAgainstEdge T P := by
  unfold Rule30UOR.Scale.CenterPeriodic InteriorAgainstEdge
  constructor
  · intro h t ht
    have := h t ht
    rw [center_eq_not_formulas, center_eq_not_formulas] at this
    have this' := Bool.not_inj this
    rcases Bool.eq_false_or_eq_true (interiorFormula (t + P) (t + P)) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (edgeFormula (t + P) (t + P)) with h2 | h2 <;>
      rcases Bool.eq_false_or_eq_true (interiorFormula t t) with h3 | h3 <;>
      rcases Bool.eq_false_or_eq_true (edgeFormula t t) with h4 | h4 <;>
      rw [h1, h2, h3, h4] at this' ⊢ <;> first | rfl | exact absurd this' (by decide)
  · intro h t ht
    rw [center_eq_not_formulas, center_eq_not_formulas]
    have := h t ht
    rcases Bool.eq_false_or_eq_true (interiorFormula (t + P) (t + P)) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (edgeFormula (t + P) (t + P)) with h2 | h2 <;>
      rcases Bool.eq_false_or_eq_true (interiorFormula t t) with h3 | h3 <;>
      rcases Bool.eq_false_or_eq_true (edgeFormula t t) with h4 | h4 <;>
      rw [h1, h2, h3, h4] at this ⊢ <;> first | rfl | exact absurd this (by decide)

/-! ## The causal horizon of the edge background

`q^n` has degree `2n`, so `trinomialParity n d = false` for `d > 2n`. Both edge
terms of row `m` at time `t` need `2m ≤ t`: the edge background at time `t`
depends only on the first half of the history, `m ≤ t/2`, while the interior
ledger receives the carries of every row up to `t − 1`. -/

theorem phiLinearPow_lt (n : Nat) : phiLinearPow n 1 < 2 ^ (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [phiLinearPow_step]
    show (phiLinearPow n 1 ^^^ (phiLinearPow n 1 <<< 1)) ^^^ (phiLinearPow n 1 <<< 2) < 2 ^ (2 * (n + 1) + 1)
    have h0 : phiLinearPow n 1 < 2 ^ (2 * (n + 1) + 1) :=
      Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by cfomega))
    have h1 : phiLinearPow n 1 <<< 1 < 2 ^ (2 * (n + 1) + 1) := by
      rw [Nat.shiftLeft_eq]
      have h := Nat.mul_lt_mul_of_pos_right ih (by decide : 0 < 2 ^ 1)
      rw [← Nat.pow_add] at h
      exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by cfomega))
    have h2 : phiLinearPow n 1 <<< 2 < 2 ^ (2 * (n + 1) + 1) := by
      rw [Nat.shiftLeft_eq]
      have h := Nat.mul_lt_mul_of_pos_right ih (by decide : 0 < 2 ^ 2)
      rw [← Nat.pow_add] at h
      exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by cfomega))
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 h1) h2

/-- Beyond the degree `2n` the trinomial row is zero. -/
theorem trinomialParity_eq_false_of_gt (n d : Nat) (h : 2 * n < d) : trinomialParity n d = false := by
  rw [← testBit_phiLinPow_eq_trinomialParity, ← phiLinearPow_eq_phiLinPow]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (phiLinearPow_lt n)
    (Nat.pow_le_pow_right (by decide) (by cfomega)))

/-- Rows after the half-time contribute nothing to the edge background. -/
theorem edgeTerm_eq_false_of_half (t m : Nat) (hm : m < t) (h : t < 2 * m) : edgeTerm t m = false := by
  unfold edgeTerm
  rw [if_neg (by cfomega : ¬ (2 * m + 1 ≤ t))]
  have h2 : (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false) = false := by
    rcases Nat.lt_or_ge t 2 with ht | ht
    · rw [if_neg (by cfomega)]
    · rw [if_pos ht, trinomialParity_eq_false_of_gt _ _ (by cfomega)]
  cases rdiag 1 m
  · rfl
  · show bxor false (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false) = false
    rw [h2]; rfl

/-- **The causal horizon**: the edge background at time `t` is the XOR over `m ≤ t/2` only. -/
theorem edgeFormula_half (t : Nat) : ∀ n, t / 2 + 1 ≤ n → n ≤ t → edgeFormula t n = edgeFormula t (t / 2 + 1) := by
  intro n
  induction n with
  | zero => intro h _; cfomega
  | succ n ih =>
    intro h1 h2
    rcases Nat.lt_or_ge (t / 2 + 1) (n + 1) with hlt | hge
    · show bxor (edgeFormula t n) (edgeTerm t n) = _
      rw [edgeTerm_eq_false_of_half t n (by cfomega) (by cfomega), ih (by cfomega) (by cfomega)]
      cases edgeFormula t (t / 2 + 1) <;> rfl
    · have : n + 1 = t / 2 + 1 := by cfomega
      rw [this]

theorem edgeDiagonal_half (t : Nat) : edgeDiagonal t = edgeFormula t (t / 2 + 1) := by
  rw [edgeDiagonal_eq_formula]
  rcases Nat.lt_or_ge t (t / 2 + 1) with h | h
  · have : t = 0 := by cfomega
    subst this; rfl
  · exact edgeFormula_half t t h (Nat.le_refl t)

/-! ## Palindromy of the trinomial row

`q` is palindromic, so `q^n` is: `trinomialParity n d = trinomialParity n (2n − d)`
for `d ≤ 2n`. With it the left-edge part of the edge background is the column
parity of the trinomial triangle, `⊕_{n ≤ N} trinomialParity n N` with `N = t − 1`,
the form in which its 2-automaticity is to be proved. -/

/-- One digit of the recursion, with the fuel discharged. -/
theorem trinomialParity_succ (f d : Nat) :
    trinomialParity (f + 1) d =
      (if (f + 1) % 2 = 0 then
        (if d % 2 = 0 then trinomialParity ((f + 1) / 2) (d / 2) else false)
      else
        bxor (bxor (if d % 2 = 0 then trinomialParity ((f + 1) / 2) (d / 2) else false)
          (if 1 ≤ d then (if (d - 1) % 2 = 0 then trinomialParity ((f + 1) / 2) ((d - 1) / 2) else false) else false))
          (if 2 ≤ d then (if (d - 2) % 2 = 0 then trinomialParity ((f + 1) / 2) ((d - 2) / 2) else false) else false)) := by
  unfold trinomialParity
  show (if f + 1 = 0 then decide (d = 0) else _) = _
  rw [if_neg (by cfomega)]
  have hrec : ∀ e, trinomialParityFuel f ((f + 1) / 2) e = trinomialParityFuel ((f + 1) / 2) ((f + 1) / 2) e :=
    fun e => trinomialParityFuel_congr f ((f + 1) / 2) ((f + 1) / 2) e (by cfomega) (Nat.le_refl _)
  simp only [hrec]

/-- `q^n` is palindromic on the lower half, `d ≤ n`. -/
theorem trinomialParity_palindrome_half : ∀ n d, d ≤ n → trinomialParity n d = trinomialParity n (2 * n - d) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro d hd
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : d = 0 := by cfomega
      subst this; rfl
    · obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by cfomega⟩
      rcases Nat.lt_or_ge f 1 with hf0 | hf1
      · -- n = 1
        have : f = 0 := by cfomega
        subst this
        rcases Nat.lt_or_ge d 1 with h | h
        · have : d = 0 := by cfomega
          subst this; decide
        · have : d = 1 := by cfomega
          subst this; decide
      have ihh : ∀ e, e ≤ (f + 1) / 2 → trinomialParity ((f + 1) / 2) e =
          trinomialParity ((f + 1) / 2) (2 * ((f + 1) / 2) - e) :=
        ih ((f + 1) / 2) (by cfomega)
      obtain ⟨r, hr⟩ : ∃ r, r = 2 * (f + 1) - d := ⟨_, rfl⟩
      rw [← hr, trinomialParity_succ, trinomialParity_succ]
      rcases Nat.mod_two_eq_zero_or_one (f + 1) with hf | hf
      · rw [if_pos hf, if_pos hf]
        rcases Nat.mod_two_eq_zero_or_one d with hdp | hdp
        · have hrp : r % 2 = 0 := by cfomega
          have hq : r / 2 = 2 * ((f + 1) / 2) - d / 2 := by cfomega
          have hle : d / 2 ≤ (f + 1) / 2 := by cfomega
          rw [if_pos hdp, if_pos hrp, hq]
          exact ihh (d / 2) hle
        · have hrp : ¬ (r % 2 = 0) := by cfomega
          rw [if_neg (by cfomega : ¬ (d % 2 = 0)), if_neg hrp]
      · have hfn : ¬ ((f + 1) % 2 = 0) := by cfomega
        rw [if_neg hfn, if_neg hfn]
        rcases Nat.mod_two_eq_zero_or_one d with hdp | hdp
        · have hrp : r % 2 = 0 := by cfomega
          rw [if_pos hdp, if_pos hrp]
          rcases Nat.lt_or_ge d 2 with hd2 | hd2
          · have hd0 : d = 0 := by cfomega
            subst hd0
            have hr1 : 1 ≤ r := by cfomega
            have hr1p : ¬ ((r - 1) % 2 = 0) := by cfomega
            have hr2 : 2 ≤ r := by cfomega
            have hr2p : (r - 2) % 2 = 0 := by cfomega
            have hq1 : r / 2 = 2 * ((f + 1) / 2) + 1 := by cfomega
            have hq2 : (r - 2) / 2 = 2 * ((f + 1) / 2) := by cfomega
            rw [if_neg (by cfomega : ¬ (1 ≤ 0)), if_neg (by cfomega : ¬ (2 ≤ 0)), if_pos hr1, if_neg hr1p, if_pos hr2,
              if_pos hr2p, hq1, hq2, Nat.zero_div,
              trinomialParity_eq_false_of_gt ((f + 1) / 2) (2 * ((f + 1) / 2) + 1) (by cfomega),
              ihh 0 (by cfomega), Nat.sub_zero]
            cases trinomialParity ((f + 1) / 2) (2 * ((f + 1) / 2)) <;> rfl
          · have h1 : 1 ≤ d := by cfomega
            have h1p : ¬ ((d - 1) % 2 = 0) := by cfomega
            have h2p : (d - 2) % 2 = 0 := by cfomega
            have hr1 : 1 ≤ r := by cfomega
            have hr1p : ¬ ((r - 1) % 2 = 0) := by cfomega
            have hr2 : 2 ≤ r := by cfomega
            have hr2p : (r - 2) % 2 = 0 := by cfomega
            have hq1 : r / 2 = 2 * ((f + 1) / 2) - (d - 2) / 2 := by cfomega
            have hq2 : (r - 2) / 2 = 2 * ((f + 1) / 2) - d / 2 := by cfomega
            have hle1 : d / 2 ≤ (f + 1) / 2 := by cfomega
            have hle2 : (d - 2) / 2 ≤ (f + 1) / 2 := by cfomega
            rw [if_pos h1, if_neg h1p, if_pos hd2, if_pos h2p, if_pos hr1, if_neg hr1p, if_pos hr2, if_pos hr2p,
              hq1, hq2, ← ihh (d / 2) hle1, ← ihh ((d - 2) / 2) hle2]
            cases trinomialParity ((f + 1) / 2) (d / 2) <;> cases trinomialParity ((f + 1) / 2) ((d - 2) / 2) <;> rfl
        · have hrp : ¬ (r % 2 = 0) := by cfomega
          have h1 : 1 ≤ d := by cfomega
          have h1p : (d - 1) % 2 = 0 := by cfomega
          have hr1 : 1 ≤ r := by cfomega
          have hr1p : (r - 1) % 2 = 0 := by cfomega
          rw [if_neg (by cfomega : ¬ (d % 2 = 0)), if_neg hrp, if_pos h1, if_pos h1p, if_pos hr1, if_pos hr1p]
          rcases Nat.lt_or_ge d 2 with hd2 | hd2
          · have hd1 : d = 1 := by cfomega
            subst hd1
            have hr2 : 2 ≤ r := by cfomega
            have hr2p : ¬ ((r - 2) % 2 = 0) := by cfomega
            have hq1 : (r - 1) / 2 = 2 * ((f + 1) / 2) := by cfomega
            rw [if_neg (by cfomega : ¬ (2 ≤ 1)), if_pos hr2, if_neg hr2p, hq1, show (1 - 1) / 2 = 0 by rfl,
              ihh 0 (by cfomega), Nat.sub_zero]
          · have h2p : ¬ ((d - 2) % 2 = 0) := by cfomega
            have hr2 : 2 ≤ r := by cfomega
            have hr2p : ¬ ((r - 2) % 2 = 0) := by cfomega
            have hq1 : (r - 1) / 2 = 2 * ((f + 1) / 2) - (d - 1) / 2 := by cfomega
            have hle : (d - 1) / 2 ≤ (f + 1) / 2 := by cfomega
            rw [if_pos hd2, if_neg h2p, if_pos hr2, if_neg hr2p, hq1, ← ihh ((d - 1) / 2) hle]

/-- `q^n` is palindromic: `trinomialParity n d = trinomialParity n (2n − d)` for `d ≤ 2n`. -/
theorem trinomialParity_palindrome (n d : Nat) (hd : d ≤ 2 * n) :
    trinomialParity n d = trinomialParity n (2 * n - d) := by
  rcases Nat.lt_or_ge n d with h | h
  · have := trinomialParity_palindrome_half n (2 * n - d) (by cfomega)
    rw [show 2 * n - (2 * n - d) = d by cfomega] at this
    exact this.symm
  · exact trinomialParity_palindrome_half n d h

/-! ## The edge background as a column parity

Splitting `edgeFormula` into its left-edge and right-pair parts and reversing
the fold, the left-edge part is the column parity of the trinomial triangle,
`columnParity (t − 1) = ⊕_{n ≤ t−1} trinomialParity n (t − 1)`, by palindromy and
the degree bound. -/

/-- XOR of `g m` over `m < n`. -/
def xorBelow (g : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bxor (xorBelow g n) (g n)

theorem xorBelow_congr (g h : Nat → Bool) : ∀ n, (∀ m, m < n → g m = h m) → xorBelow g n = xorBelow h n
  | 0, _ => rfl
  | n + 1, hgh => by
    show bxor (xorBelow g n) (g n) = bxor (xorBelow h n) (h n)
    rw [xorBelow_congr g h n (fun m hm => hgh m (by cfomega)), hgh n (by cfomega)]

theorem xorBelow_front (g : Nat → Bool) : ∀ n, xorBelow g (n + 1) = bxor (g 0) (xorBelow (fun m => g (m + 1)) n) := by
  intro n
  induction n with
  | zero => show bxor false (g 0) = bxor (g 0) false; cases g 0 <;> rfl
  | succ n ih =>
    show bxor (xorBelow g (n + 1)) (g (n + 1)) = bxor (g 0) (bxor (xorBelow (fun m => g (m + 1)) n) (g (n + 1)))
    rw [ih]
    cases g 0 <;> cases xorBelow (fun m => g (m + 1)) n <;> cases g (n + 1) <;> rfl

/-- Fold reversal: `⊕_{m<n} g m = ⊕_{m<n} g (n − 1 − m)`. -/
theorem xorBelow_rev (g : Nat → Bool) : ∀ n, xorBelow g n = xorBelow (fun m => g (n - 1 - m)) n := by
  intro n
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [xorBelow_front, ih (fun m => g (m + 1))]
    show bxor (g 0) (xorBelow (fun m => g (n - 1 - m + 1)) n) =
      bxor (xorBelow (fun m => g (n + 1 - 1 - m)) n) (g (n + 1 - 1 - n))
    rw [show n + 1 - 1 - n = 0 by cfomega,
      xorBelow_congr (fun m => g (n - 1 - m + 1)) (fun m => g (n + 1 - 1 - m)) n
        (fun m hm => by show g (n - 1 - m + 1) = g (n + 1 - 1 - m); rw [show n - 1 - m + 1 = n + 1 - 1 - m by cfomega])]
    cases g 0 <;> cases xorBelow (fun m => g (n + 1 - 1 - m)) n <;> rfl

theorem xorBelow_bxor (a b : Nat → Bool) : ∀ n, xorBelow (fun m => bxor (a m) (b m)) n = bxor (xorBelow a n) (xorBelow b n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show bxor (xorBelow (fun m => bxor (a m) (b m)) n) (bxor (a n) (b n)) = bxor (bxor (xorBelow a n) (a n)) (bxor (xorBelow b n) (b n))
    rw [ih]
    cases xorBelow a n <;> cases xorBelow b n <;> cases a n <;> cases b n <;> rfl

/-- The left-edge and right-pair parts of the edge term. -/
def edgeLeftTerm (t m : Nat) : Bool :=
  if 2 * m + 1 ≤ t then trinomialParity (t - 1 - m) (t - (2 * m + 1)) else false

def edgeRightTerm (t m : Nat) : Bool :=
  if rdiag 1 m then (if 2 ≤ t then trinomialParity (t - 1 - m) (t - 2) else false) else false

theorem edgeTerm_eq_parts (t m : Nat) : edgeTerm t m = bxor (edgeLeftTerm t m) (edgeRightTerm t m) := rfl

theorem edgeFormula_eq_xorBelow (t : Nat) : ∀ n, edgeFormula t n = xorBelow (edgeTerm t) n
  | 0 => rfl
  | n + 1 => by
    show bxor (edgeFormula t n) (edgeTerm t n) = bxor (xorBelow (edgeTerm t) n) (edgeTerm t n)
    rw [edgeFormula_eq_xorBelow t n]

/-- The column parity of the trinomial triangle at column `N`: `⊕_{n ≤ N} trinomialParity n N`. -/
def columnParity (N : Nat) : Bool := xorBelow (fun n => trinomialParity n N) (N + 1)

/-- **The left-edge background is the column parity of the trinomial triangle.** -/
theorem edgeLeft_eq_columnParity (t : Nat) (ht : 1 ≤ t) :
    xorBelow (edgeLeftTerm t) t = columnParity (t - 1) := by
  unfold columnParity
  rw [xorBelow_rev, show t - 1 + 1 = t by cfomega]
  apply xorBelow_congr
  intro n hn
  show (if 2 * (t - 1 - n) + 1 ≤ t then trinomialParity (t - 1 - (t - 1 - n)) (t - (2 * (t - 1 - n) + 1)) else false)
    = trinomialParity n (t - 1)
  rw [show t - 1 - (t - 1 - n) = n by cfomega]
  rcases Nat.lt_or_ge (2 * n) (t - 1) with h | h
  · rw [if_neg (by cfomega), trinomialParity_eq_false_of_gt n (t - 1) h]
  · rw [if_pos (by cfomega), show t - (2 * (t - 1 - n) + 1) = 2 * n - (t - 1) by cfomega,
      ← trinomialParity_palindrome n (t - 1) h]

/-- The edge background split into the column parity and the right-pair part. -/
theorem edgeFormula_split (t : Nat) (ht : 1 ≤ t) :
    edgeFormula t t = bxor (columnParity (t - 1)) (xorBelow (edgeRightTerm t) t) := by
  rw [edgeFormula_eq_xorBelow, ← edgeLeft_eq_columnParity t ht, ← xorBelow_bxor]
  apply xorBelow_congr
  intro m _
  exact edgeTerm_eq_parts t m

/-! ## The black-center absorption of the 2-adic flip

Under a periodic center no left defect arrives at a black center
(`periodic_black_no_arrival`), so at black-center times the ledger bit at
position `-1` flips across the period exactly when the trailing-ones parity
flips: the ledger absorbs the 2-adic signal of the linear part. -/

theorem periodic_black_ledger_absorbs (T P t : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) (hb : center t = true) :
    bxor (ledgerBit (t + P) (t + P + 1)) (ledgerBit t (t + 1)) =
      bxor (trailingParity (t + P)) (trailingParity t) := by
  have h := Rule30UOR.WittDefect.periodic_black_no_arrival T P 1 t hc ht hb
  rw [Nat.one_mul] at h
  unfold Rule30UOR.Collision.leftDefect Rule30UOR.TemporalDefect.defect Rule30UOR.TemporalDefect.difference at h
  rw [show (-((1 : Nat) : Int)) = -1 from rfl] at h
  have h' : xor (Ruliology.CellularAutomata.Rule30Jen.cell (t + P) (-1))
      (Ruliology.CellularAutomata.Rule30Jen.cell t (-1)) = false := h
  rw [← Rule30UOR.Scale.cell_eq_kit, ← Rule30UOR.Scale.cell_eq_kit, cell_left_eq, cell_left_eq] at h'
  clear h
  have h := h'
  rcases Bool.eq_false_or_eq_true (trailingParity (t + P)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (trailingParity t) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (ledgerBit (t + P) (t + P + 1)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (ledgerBit t (t + 1)) with h4 | h4 <;>
    rw [h1, h2, h3, h4] at h ⊢ <;> first | rfl | exact absurd h (by decide)

end Rule30UOR.EdgeSplit
