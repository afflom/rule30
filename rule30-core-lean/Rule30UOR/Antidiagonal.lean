module
public import Rule30UOR.Band
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The anti-diagonal form of the center

The center `center t = cell t 0` is the right diagonal `t` read at time `t`, `rdiag t t`
(`Ledger.cell_eq_rdiag`). Every right diagonal `rdiag j` is exactly `2^j`-periodic from time `0`
(`Right.rdiag_periodic`), so it is a word of length `2^j`, `towerWord j s = rdiag j (s mod 2^j)`,
and the center is the anti-diagonal of the tower of words: `center t = towerWord t t`. The words
obey the permutive recursion `towerWord (k+2) (s+1) = towerWord (k+2) s ⊕ (towerWord (k+1) s ∨
towerWord k s)` with the base words `towerWord 0 = 1` and `towerWord 1 = timeParity`. A center
period is a period of the anti-diagonal readout: Problem 1 is `AntidiagonalAperiodic`. -/

@[expose] public section

namespace Rule30UOR.Antidiagonal

open Rule30UOR.Core Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Band

/-! ## The center is the anti-diagonal of the right system -/

/-- `center t = rdiag t t`: the right diagonal `t` read at time `t` is the cell at position `0`. -/
theorem center_eq_rdiag_self (t : Nat) : center t = rdiag t t :=
  cell_eq_rdiag t t 0 (by cfomega)

/-- A center period is exactly a period of the anti-diagonal readout `rdiag t t`. -/
theorem centerPeriodic_iff_centerPer (T P : Nat) :
    Rule30UOR.Scale.CenterPeriodic T P ↔ Rule30UOR.Right.CenterPer T P := by
  unfold Rule30UOR.Scale.CenterPeriodic Rule30UOR.Right.CenterPer
  constructor
  · intro h t ht
    rw [← center_eq_rdiag_self, ← center_eq_rdiag_self]
    exact h t ht
  · intro h t ht
    rw [center_eq_rdiag_self, center_eq_rdiag_self]
    exact h t ht

/-- The anti-diagonal readout of the right system has no eventual period. -/
def AntidiagonalAperiodic : Prop := ∀ T P, 0 < P → ¬ Rule30UOR.Right.CenterPer T P

/-- **Problem 1 is `AntidiagonalAperiodic`.** -/
theorem problem1_iff_antidiagonal : Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ AntidiagonalAperiodic := by
  rw [Rule30UOR.Scale.problem1_iff]
  constructor
  · intro h T P hP hc
    exact h T P hP ((centerPeriodic_iff_centerPer T P).2 hc)
  · intro h T P hP hc
    exact h T P hP ((centerPeriodic_iff_centerPer T P).1 hc)

theorem problem1_of_antidiagonal (h : AntidiagonalAperiodic) : Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff_antidiagonal.2 h

/-! ## The tower of words -/

theorem twopow_eq_pow : ∀ j, twopow j = 2 ^ j
  | 0 => rfl
  | j + 1 => by
    rw [twopow_succ, twopow_eq_pow j, Nat.pow_succ]
    cfomega

/-- Diagonal `j` repeats with every multiple of `2^j`. -/
theorem rdiag_add_twopow_mul (j : Nat) : ∀ q t, rdiag j (t + twopow j * q) = rdiag j t
  | 0, t => by rw [Nat.mul_zero, Nat.add_zero]
  | q + 1, t => by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, twopow_eq_pow, Rule30UOR.Right.rdiag_periodic,
      ← twopow_eq_pow, rdiag_add_twopow_mul j q t]

/-- The word of diagonal `j`: its `2^j` values, read cyclically. -/
def towerWord (j s : Nat) : Bool := rdiag j (s % twopow j)

/-- Every right diagonal is its word. -/
theorem rdiag_eq_towerWord (j t : Nat) : rdiag j t = towerWord j t := by
  unfold towerWord
  have h := rdiag_add_twopow_mul j (t / twopow j) (t % twopow j)
  rw [Nat.mod_add_div t (twopow j)] at h
  exact h

theorem towerWord_mod (j s : Nat) : towerWord j (s % twopow j) = towerWord j s := by
  unfold towerWord
  rw [Nat.mod_mod]

/-- **The center is the anti-diagonal of the tower of words.** -/
theorem center_eq_towerWord (t : Nat) : center t = towerWord t t := by
  rw [center_eq_rdiag_self, rdiag_eq_towerWord]

/-- The permutive recursion on the words, read from the right edge. -/
theorem towerWord_step (k s : Nat) :
    towerWord (k + 2) (s + 1) = bxor (towerWord (k + 2) s) (towerWord (k + 1) s || towerWord k s) := by
  simp only [← rdiag_eq_towerWord]
  exact rdiag_step k s

/-- The base word `0` is constant `1`. -/
theorem towerWord_zero (s : Nat) : towerWord 0 s = true := by
  rw [← rdiag_eq_towerWord]
  exact rdiag_zero_eq s

/-- The base word `1` is the time parity. -/
theorem towerWord_one (s : Nat) : towerWord 1 s = timeParity s := by
  rw [← rdiag_eq_towerWord, rdiag_one_eq_parity]
  rfl

/-- The word of diagonal `j` is the word of diagonal `j - 1` extended by the recursion; the
word's value at time `0` is `false` for `j ≥ 1`. -/
theorem towerWord_succ_zero (j : Nat) : towerWord (j + 1) 0 = false := by
  rw [← rdiag_eq_towerWord]
  rfl

/-! ## A center period in the tower vocabulary -/

/-- Under a center period `P` from `T`, the anti-diagonal of the tower repeats. -/
theorem towerWord_centerPeriodic (T P : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (t : Nat) (ht : T ≤ t) :
    towerWord (t + P) (t + P) = towerWord t t := by
  rw [← center_eq_towerWord, ← center_eq_towerWord]
  exact hc t ht

/-- Conversely, a period of the anti-diagonal of the tower is a center period. -/
theorem centerPeriodic_of_towerWord (T P : Nat)
    (h : ∀ t, T ≤ t → towerWord (t + P) (t + P) = towerWord t t) : Rule30UOR.Scale.CenterPeriodic T P := by
  intro t ht
  rw [center_eq_towerWord, center_eq_towerWord]
  exact h t ht

/-! ## The recursion integrates to a prefix parity -/

/-- The OR-word of the diagonals `k + 1` and `k`. -/
def orWord (k s : Nat) : Bool := towerWord (k + 1) s || towerWord k s

/-- **The word `k + 2` is the prefix parity of the OR-word `k`.** -/
theorem towerWord_eq_prefix (k : Nat) : ∀ s, towerWord (k + 2) s = xorBelow (orWord k) s
  | 0 => by
    show towerWord (k + 2) 0 = false
    exact towerWord_succ_zero (k + 1)
  | s + 1 => by
    show towerWord (k + 2) (s + 1) = bxor (xorBelow (orWord k) s) (orWord k s)
    rw [towerWord_step, towerWord_eq_prefix k s]
    rfl

/-- **The center at time `t ≥ 2` is the parity of the OR of the diagonals `t − 1` and `t − 2`
over the first `t` times.** -/
theorem center_eq_prefix_or (t : Nat) (ht : 2 ≤ t) : center t = xorBelow (orWord (t - 2)) t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  rw [Nat.add_sub_cancel, center_eq_towerWord, towerWord_eq_prefix]

/-! ## The doubling law -/

/-- The parity of the OR-word `k` over its period `2^(k+1)`. -/
def wordWeight (k : Nat) : Bool := xorBelow (orWord k) (twopow (k + 1))

theorem towerWord_add_twopow (j s : Nat) : towerWord j (s + twopow j) = towerWord j s := by
  rw [← rdiag_eq_towerWord, ← rdiag_eq_towerWord]
  have h := rdiag_add_twopow_mul j 1 s
  rw [Nat.mul_one] at h
  exact h

/-- The OR-word `k` is `2^(k+1)`-periodic. -/
theorem orWord_periodic (k s : Nat) : orWord k (s + twopow (k + 1)) = orWord k s := by
  unfold orWord
  rw [towerWord_add_twopow, twopow_succ, ← Nat.add_assoc, towerWord_add_twopow, towerWord_add_twopow]

theorem xorBelow_split (g : Nat → Bool) (a b : Nat) :
    xorBelow g (a + b) = bxor (xorBelow g a) (xorBelow (fun i => g (a + i)) b) := by
  induction b with
  | zero =>
    show xorBelow g a = bxor (xorBelow g a) false
    cases xorBelow g a <;> rfl
  | succ b ih =>
    show bxor (xorBelow g (a + b)) (g (a + b)) =
      bxor (xorBelow g a) (bxor (xorBelow (fun i => g (a + i)) b) (g (a + b)))
    rw [ih]
    cases xorBelow g a <;> cases xorBelow (fun i => g (a + i)) b <;> cases g (a + b) <;> rfl

theorem bxor_window_aux (A B W : Bool) (h : bxor A B = bxor B W) : W = A := by
  cases A <;> cases B <;> cases W <;> first | rfl | exact absurd h (by decide)

/-- The parity of a `P`-periodic word over any window of length `P` is its parity over `[0, P)`. -/
theorem xorBelow_window (g : Nat → Bool) (P : Nat) (hg : ∀ i, g (i + P) = g i) (s : Nat) :
    xorBelow (fun i => g (s + i)) P = xorBelow g P := by
  have h1 := xorBelow_split g s P
  have h2 := xorBelow_split g P s
  rw [Nat.add_comm P s, xorBelow_congr (fun i => g (P + i)) g s (fun i _ => by rw [Nat.add_comm P i]; exact hg i)]
    at h2
  rw [h2] at h1
  exact bxor_window_aux _ _ _ h1

/-- **The half-period law**: shifting the word `k + 2` by `2^(k+1)` flips it by `wordWeight k`. -/
theorem towerWord_half_period (k s : Nat) :
    towerWord (k + 2) (s + twopow (k + 1)) = bxor (towerWord (k + 2) s) (wordWeight k) := by
  rw [towerWord_eq_prefix, towerWord_eq_prefix, xorBelow_split,
    xorBelow_window (orWord k) (twopow (k + 1)) (orWord_periodic k) s]
  rfl

/-- **Period halves**: if the OR-word has even weight, the word `k + 2` has period `2^(k+1)`. -/
theorem towerWord_period_halves (k : Nat) (h : wordWeight k = false) :
    ∀ s, towerWord (k + 2) (s + twopow (k + 1)) = towerWord (k + 2) s := by
  intro s
  rw [towerWord_half_period, h]
  cases towerWord (k + 2) s <;> rfl

/-- **Period doubles**: if the OR-word has odd weight, the second half of the word `k + 2` is the
complement of the first. -/
theorem towerWord_period_doubles (k : Nat) (h : wordWeight k = true) :
    ∀ s, towerWord (k + 2) (s + twopow (k + 1)) = !(towerWord (k + 2) s) := by
  intro s
  rw [towerWord_half_period, h]
  cases towerWord (k + 2) s <;> rfl

/-! ## The first weights -/

/-- The word read from the row register: `towerWord j s = bit j of row (s mod 2^j)`. -/
theorem towerWord_eq_row (j s : Nat) : towerWord j s = (row (s % twopow j)).testBit j := by
  unfold towerWord
  rw [Rule30UOR.Interfaces.row_testBit]

theorem wordWeight_eq_row (k : Nat) :
    wordWeight k = xorBelow (fun s => (row (s % twopow (k + 1))).testBit (k + 1) || (row (s % twopow k)).testBit k)
      (twopow (k + 1)) := by
  unfold wordWeight
  exact xorBelow_congr _ _ _ (fun s _ => by unfold orWord; rw [towerWord_eq_row, towerWord_eq_row])

theorem wordWeight_zero : wordWeight 0 = false := by rw [wordWeight_eq_row]; decide

theorem wordWeight_one : wordWeight 1 = false := by rw [wordWeight_eq_row]; decide

theorem wordWeight_two : wordWeight 2 = false := by rw [wordWeight_eq_row]; decide

theorem wordWeight_three : wordWeight 3 = false := by rw [wordWeight_eq_row]; decide

theorem wordWeight_four : wordWeight 4 = false := by rw [wordWeight_eq_row]; decide

theorem wordWeight_five : wordWeight 5 = false := by rw [wordWeight_eq_row]; decide

/-! ## A center period in prefix form -/

/-- Under a center period `P` from `T`, the prefix parities of the OR-words agree. -/
theorem centerPeriodic_prefix (T P t : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) (h2 : 2 ≤ t) :
    xorBelow (orWord (t + P - 2)) (t + P) = xorBelow (orWord (t - 2)) t := by
  rw [← center_eq_prefix_or _ (by cfomega), ← center_eq_prefix_or _ h2]
  exact hc t ht

end Rule30UOR.Antidiagonal
