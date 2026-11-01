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

/-! ## The general halving: every word `j ≥ 2` has period `2^(j−1)`

Two consecutive half-periodic words make their OR-word `2^(k+1)`-periodic, so its weight over
`2^(k+2)` is a doubled window and vanishes; the half-period law then halves the next word. The
bases are the words `2` (period `2`) and `3` (period `4`), decided above. -/

/-- The word `j` has period `2^(j−1)` (meaningful for `j ≥ 1`). -/
def HalfPeriodic (j : Nat) : Prop := ∀ s, towerWord j (s + twopow (j - 1)) = towerWord j s

theorem halfPeriodic_two : HalfPeriodic 2 := towerWord_period_halves 0 wordWeight_zero

theorem halfPeriodic_three : HalfPeriodic 3 := towerWord_period_halves 1 wordWeight_one

/-- The OR of a `2^(k+1)`-periodic word and a `2^k`-periodic word is `2^(k+1)`-periodic. -/
theorem orWord_half_periodic (k : Nat) (h1 : HalfPeriodic (k + 1)) (h2 : HalfPeriodic (k + 2)) :
    ∀ s, orWord (k + 1) (s + twopow (k + 1)) = orWord (k + 1) s := by
  intro s
  have e2 : towerWord (k + 1 + 1) (s + twopow (k + 1)) = towerWord (k + 1 + 1) s := by
    have h := h2 s
    rw [show k + 2 - 1 = k + 1 by cfomega] at h
    exact h
  have e1 : towerWord (k + 1) (s + twopow (k + 1)) = towerWord (k + 1) s := by
    have a := h1 (s + twopow k)
    have b := h1 s
    rw [Nat.add_sub_cancel] at a b
    rw [twopow_succ, ← Nat.add_assoc, a, b]
  unfold orWord
  rw [e2, e1]

/-- Two consecutive half-periodic words give the next OR-word even weight. -/
theorem wordWeight_succ_false (k : Nat) (h1 : HalfPeriodic (k + 1)) (h2 : HalfPeriodic (k + 2)) :
    wordWeight (k + 1) = false := by
  unfold wordWeight
  rw [show twopow (k + 1 + 1) = twopow (k + 1) + twopow (k + 1) from twopow_succ (k + 1), xorBelow_split,
    xorBelow_window (orWord (k + 1)) (twopow (k + 1)) (orWord_half_periodic k h1 h2) (twopow (k + 1))]
  cases xorBelow (orWord (k + 1)) (twopow (k + 1)) <;> rfl

/-- The induction step of the halving. -/
theorem halfPeriodic_succ (k : Nat) (h1 : HalfPeriodic (k + 1)) (h2 : HalfPeriodic (k + 2)) :
    HalfPeriodic (k + 3) := by
  intro s
  have h := towerWord_period_halves (k + 1) (wordWeight_succ_false k h1 h2) s
  rw [show k + 3 - 1 = k + 1 + 1 by cfomega]
  exact h

theorem halfPeriodic_pair : ∀ n, HalfPeriodic (n + 2) ∧ HalfPeriodic (n + 3)
  | 0 => ⟨halfPeriodic_two, halfPeriodic_three⟩
  | n + 1 => by
    obtain ⟨a, b⟩ := halfPeriodic_pair n
    exact ⟨b, halfPeriodic_succ (n + 1) a b⟩

/-- **Every word `j ≥ 2` has period `2^(j−1)`.** -/
theorem halfPeriodic_of_two_le (j : Nat) (hj : 2 ≤ j) : HalfPeriodic j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by cfomega⟩
  exact (halfPeriodic_pair n).1

/-- **Every right diagonal `j ≥ 2` has period `2^(j−1)`**, half of the period `2^j`. -/
theorem rdiag_period_half (j t : Nat) (hj : 2 ≤ j) : rdiag j (t + twopow (j - 1)) = rdiag j t := by
  rw [rdiag_eq_towerWord, rdiag_eq_towerWord]
  exact halfPeriodic_of_two_le j hj t

/-- **Every OR-word has even weight**: the half-period law always halves, never doubles. -/
theorem wordWeight_false (k : Nat) : wordWeight k = false := by
  rcases Nat.lt_or_ge k 2 with h | h
  · rcases Nat.lt_or_ge k 1 with h0 | h0
    · obtain rfl : k = 0 := by cfomega
      exact wordWeight_zero
    · obtain rfl : k = 1 := by cfomega
      exact wordWeight_one
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by cfomega⟩
    exact wordWeight_succ_false (n + 1) (halfPeriodic_of_two_le (n + 2) (by cfomega))
      (halfPeriodic_of_two_le (n + 3) (by cfomega))

/-- The half-period law with its weight evaluated: the word `k + 2` repeats after `2^(k+1)`. -/
theorem towerWord_add_twopow_half (k s : Nat) : towerWord (k + 2) (s + twopow (k + 1)) = towerWord (k + 2) s :=
  towerWord_period_halves k (wordWeight_false k) s

theorem towerWord_add_half_mul (j : Nat) (hj : 2 ≤ j) : ∀ q s, towerWord j (s + twopow (j - 1) * q) = towerWord j s
  | 0, s => by rw [Nat.mul_zero, Nat.add_zero]
  | q + 1, s => by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, halfPeriodic_of_two_le j hj, towerWord_add_half_mul j hj q s]

/-- The word `j ≥ 2` is determined by its first `2^(j−1)` values. -/
theorem towerWord_mod_half (j s : Nat) (hj : 2 ≤ j) : towerWord j s = towerWord j (s % twopow (j - 1)) := by
  have h := towerWord_add_half_mul j hj (s / twopow (j - 1)) (s % twopow (j - 1))
  rw [Nat.mod_add_div s (twopow (j - 1))] at h
  exact h

/-! ## The OR splits: the word and its exposed part

`a ∨ b = a ⊕ (b ∧ ¬a)`, so the OR-word is the word `k + 1` plus the part of the word `k` that
shows through it. The tower recursion is then the prefix parity of the previous word plus the
prefix parity of the exposed mask: the ledger's linear-plus-carry split in diagonal
coordinates. -/

/-- Where the word `k` shows through the word `k + 1`. -/
def exposed (k i : Nat) : Bool := towerWord k i && !(towerWord (k + 1) i)

theorem orWord_eq_exposed (k i : Nat) : orWord k i = bxor (towerWord (k + 1) i) (exposed k i) := by
  unfold orWord exposed
  cases towerWord (k + 1) i <;> cases towerWord k i <;> rfl

/-- **The split recursion**: the word `k + 2` is the prefix parity of the word `k + 1` plus the
prefix parity of the exposed mask `k`. -/
theorem towerWord_eq_prefix_split (k s : Nat) :
    towerWord (k + 2) s = bxor (xorBelow (towerWord (k + 1)) s) (xorBelow (exposed k) s) := by
  rw [towerWord_eq_prefix,
    xorBelow_congr (orWord k) (fun i => bxor (towerWord (k + 1) i) (exposed k i)) s (fun i _ => orWord_eq_exposed k i),
    xorBelow_bxor]

/-- The center at time `t ≥ 2`: the prefix parity of the diagonal `t − 1` plus the prefix parity
of the mask exposed by the diagonal `t − 2` through it. -/
theorem center_eq_prefix_split (t : Nat) (ht : 2 ≤ t) :
    center t = bxor (xorBelow (towerWord (t - 1)) t) (xorBelow (exposed (t - 2)) t) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  rw [Nat.add_sub_cancel, show s + 2 - 1 = s + 1 by cfomega, center_eq_towerWord, towerWord_eq_prefix_split]

/-! ## The iterated prefix operator and the transport of the masks -/

/-- The `n`-fold prefix parity (the gasket transport). -/
def prefixPow : Nat → (Nat → Bool) → Nat → Bool
  | 0, g => g
  | n + 1, g => xorBelow (prefixPow n g)

theorem prefixPow_zero (g : Nat → Bool) : prefixPow 0 g = g := rfl

theorem prefixPow_succ (n : Nat) (g : Nat → Bool) : prefixPow (n + 1) g = xorBelow (prefixPow n g) := rfl

theorem prefixPow_add (m n : Nat) (g : Nat → Bool) : prefixPow (m + n) g = prefixPow m (prefixPow n g) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by cfomega]
    show xorBelow (prefixPow (m + n) g) = xorBelow (prefixPow m (prefixPow n g))
    rw [ih]

/-- The transport of the exposed masks `0 .. k` to the word `k + 2`: each mask `i` is integrated
`k − i + 1` times. -/
def maskTransport : Nat → Nat → Bool
  | 0, s => xorBelow (exposed 0) s
  | k + 1, s => bxor (xorBelow (maskTransport k) s) (xorBelow (exposed (k + 1)) s)

theorem maskTransport_zero (s : Nat) : maskTransport 0 s = xorBelow (exposed 0) s := rfl

theorem maskTransport_succ (k s : Nat) :
    maskTransport (k + 1) s = bxor (xorBelow (maskTransport k) s) (xorBelow (exposed (k + 1)) s) := rfl

/-- **The tower unfolded**: the word `k + 2` is the `(k+1)`-fold prefix parity of the time parity
(the word `1`) plus the transport of the exposed masks. -/
theorem towerWord_unfold (k : Nat) :
    ∀ s, towerWord (k + 2) s = bxor (prefixPow (k + 1) (towerWord 1) s) (maskTransport k s) := by
  induction k with
  | zero =>
    intro s
    exact towerWord_eq_prefix_split 0 s
  | succ k ih =>
    intro s
    rw [towerWord_eq_prefix_split (k + 1) s,
      xorBelow_congr (towerWord (k + 1 + 1)) (fun i => bxor (prefixPow (k + 1) (towerWord 1) i) (maskTransport k i)) s
        (fun i _ => ih i),
      xorBelow_bxor]
    show bxor (bxor (xorBelow (prefixPow (k + 1) (towerWord 1)) s) (xorBelow (maskTransport k) s))
        (xorBelow (exposed (k + 1)) s) =
      bxor (xorBelow (prefixPow (k + 1) (towerWord 1)) s)
        (bxor (xorBelow (maskTransport k) s) (xorBelow (exposed (k + 1)) s))
    cases xorBelow (prefixPow (k + 1) (towerWord 1)) s <;> cases xorBelow (maskTransport k) s <;>
      cases xorBelow (exposed (k + 1)) s <;> rfl

/-- **The center is the gasket transport of the time parity plus the transport of the exposed
masks**: the dual of the carry-ledger formula, in diagonal coordinates. -/
theorem center_eq_transport (t : Nat) (ht : 2 ≤ t) :
    center t = bxor (prefixPow (t - 1) (towerWord 1) t) (maskTransport (t - 2) t) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  rw [Nat.add_sub_cancel, show s + 2 - 1 = s + 1 by cfomega, center_eq_towerWord, towerWord_unfold]

/-! ## The linear part is the transport of the constant word -/

/-- The time parity is the prefix parity of the constant word `1`. -/
theorem timeParity_eq_prefix_true : ∀ s, timeParity s = xorBelow (fun _ => true) s
  | 0 => rfl
  | s + 1 => by
    show timeParity (s + 1) = bxor (xorBelow (fun _ => true) s) true
    rw [← timeParity_eq_prefix_true s]
    unfold timeParity
    rcases Nat.mod_two_eq_zero_or_one s with h | h
    · rw [decide_eq_false (by cfomega : ¬ (s % 2 = 1)), decide_eq_true (by cfomega : (s + 1) % 2 = 1)]; rfl
    · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ ((s + 1) % 2 = 1))]; rfl

/-- The word `1` is the prefix parity of the constant word. -/
theorem towerWord_one_eq_prefix_true (s : Nat) : towerWord 1 s = prefixPow 1 (fun _ => true) s := by
  rw [towerWord_one, timeParity_eq_prefix_true]
  rfl

/-- The linear part of the tower is the `(n+1)`-fold prefix parity of the constant word. -/
theorem prefixPow_towerWord_one (n s : Nat) : prefixPow n (towerWord 1) s = prefixPow (n + 1) (fun _ => true) s := by
  rw [prefixPow_add n 1]
  have h : towerWord 1 = prefixPow 1 (fun _ => true) := funext towerWord_one_eq_prefix_true
  rw [h]

/-! ## The exposed masks are periodic -/

/-- For `k ≥ 2` the exposed mask `k` is `2^k`-periodic (both words have periods dividing `2^k`). -/
theorem exposed_periodic (k s : Nat) (hk : 2 ≤ k) : exposed k (s + twopow k) = exposed k s := by
  unfold exposed
  have h := halfPeriodic_of_two_le (k + 1) (by cfomega) s
  rw [Nat.add_sub_cancel] at h
  rw [towerWord_add_twopow, h]

/-! ## First-order forms -/

/-- The prefix parity of the word `j`. -/
def prefixWord (j s : Nat) : Bool := xorBelow (towerWord j) s

/-- The prefix parity of the exposed mask `k`. -/
def exposedPrefix (k s : Nat) : Bool := xorBelow (exposed k) s

/-- The linear part of the tower: the `n`-fold prefix parity of the word `1`. -/
def linearTower (n s : Nat) : Bool := prefixPow n (towerWord 1) s

/-- The `n`-fold prefix parity of the constant word `1`. -/
def constPrefix (n s : Nat) : Bool := prefixPow n (fun _ => true) s

theorem towerWord_split (k s : Nat) :
    towerWord (k + 2) s = bxor (prefixWord (k + 1) s) (exposedPrefix k s) :=
  towerWord_eq_prefix_split k s

theorem center_split (t : Nat) (ht : 2 ≤ t) :
    center t = bxor (prefixWord (t - 1) t) (exposedPrefix (t - 2) t) :=
  center_eq_prefix_split t ht

theorem towerWord_unfolded (k s : Nat) : towerWord (k + 2) s = bxor (linearTower (k + 1) s) (maskTransport k s) :=
  towerWord_unfold k s

theorem center_transport (t : Nat) (ht : 2 ≤ t) :
    center t = bxor (linearTower (t - 1) t) (maskTransport (t - 2) t) :=
  center_eq_transport t ht

theorem linearTower_eq_constPrefix (n s : Nat) : linearTower n s = constPrefix (n + 1) s :=
  prefixPow_towerWord_one n s

/-! ## The diagonal of the iterated prefix of the constant word -/

theorem constPrefix_below_diag : ∀ n, (∀ s, s < n → constPrefix n s = false) ∧ constPrefix n n = true
  | 0 => ⟨fun s hs => absurd hs (Nat.not_lt_zero s), rfl⟩
  | n + 1 => by
    obtain ⟨hb, hd⟩ := constPrefix_below_diag n
    have hz : ∀ s, s ≤ n → constPrefix (n + 1) s = false := by
      intro s hs
      show xorBelow (prefixPow n (fun _ => true)) s = false
      refine (xorBelow_congr _ (fun _ => false) s (fun i hi => ?_)).trans (xorBelow_false s)
      exact hb i (by cfomega)
    refine ⟨fun s hs => hz s (by cfomega), ?_⟩
    show bxor (xorBelow (prefixPow n (fun _ => true)) n) (prefixPow n (fun _ => true) n) = true
    rw [show xorBelow (prefixPow n (fun _ => true)) n = constPrefix (n + 1) n from rfl, hz n (Nat.le_refl n)]
    exact hd

/-- Below the diagonal the iterated prefix of the constant word vanishes. -/
theorem constPrefix_below (n s : Nat) (hs : s < n) : constPrefix n s = false :=
  (constPrefix_below_diag n).1 s hs

/-- On the diagonal the iterated prefix of the constant word is `1`. -/
theorem constPrefix_diag (n : Nat) : constPrefix n n = true :=
  (constPrefix_below_diag n).2

/-- The linear part of the tower on the anti-diagonal is `1`. -/
theorem linearTower_diag (t : Nat) (ht : 1 ≤ t) : linearTower (t - 1) t = true := by
  rw [linearTower_eq_constPrefix, show t - 1 + 1 = t by cfomega]
  exact constPrefix_diag t

/-- **The center is the complement of the transport of the exposed masks**: the exact dual of
`center = ¬ ledgerDiagonal`, in diagonal coordinates. -/
theorem center_eq_not_maskTransport (t : Nat) (ht : 2 ≤ t) : center t = !(maskTransport (t - 2) t) := by
  rw [center_transport t ht, linearTower_diag t (by cfomega)]
  cases maskTransport (t - 2) t <;> rfl

/-! ## The exposed masks in cells -/

/-- The exposed mask at diagonal `k`, time `i`, is a black cell whose left neighbour is white:
the left end of a black run. -/
theorem exposed_eq_cells (k i : Nat) :
    exposed k i = (cell i ((i : Int) - k) && !(cell i ((i : Int) - k - 1))) := by
  unfold exposed
  rw [← rdiag_eq_towerWord, ← rdiag_eq_towerWord, ← cell_eq_rdiag i k ((i : Int) - k) rfl,
    ← cell_eq_rdiag i (k + 1) ((i : Int) - k - 1) (by cfomega)]

/-! ## A center period in the mask vocabulary -/

theorem not_inj_aux (a b : Bool) (h : (!a) = (!b)) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Under a center period `P` from `T`, the transport of the exposed masks repeats on the
anti-diagonal. -/
theorem maskTransport_centerPeriodic (T P t : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t)
    (h2 : 2 ≤ t) : maskTransport (t + P - 2) (t + P) = maskTransport (t - 2) t := by
  have h := hc t ht
  rw [center_eq_not_maskTransport (t + P) (by cfomega), center_eq_not_maskTransport t h2] at h
  exact not_inj_aux _ _ h

/-! ## Lucas: the parity of the binomial coefficients

`pascalParity n k = C(n, k) mod 2` by the digit recursion (Lucas): `C(n, k)` is odd exactly when
every binary digit of `k` is at most the digit of `n`. -/

def pascalParityFuel : Nat → Nat → Nat → Bool
  | 0, _, k => decide (k = 0)
  | f + 1, n, k =>
    if k = 0 then true
    else if n = 0 then false
    else if k % 2 = 1 ∧ n % 2 = 0 then false
    else pascalParityFuel f (n / 2) (k / 2)

/-- The parity of `C(n, k)`, by the binary digits (fuel `n`). -/
def pascalParity (n k : Nat) : Bool := pascalParityFuel n n k

theorem pascalParityFuel_zero_left (k : Nat) : ∀ g, pascalParityFuel g 0 k = decide (k = 0)
  | 0 => rfl
  | g + 1 => by
    show (if k = 0 then true else if (0 : Nat) = 0 then false else _) = decide (k = 0)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rfl
    · rw [if_neg (by cfomega), if_pos rfl, decide_eq_false (by cfomega)]

theorem pascalParityFuel_congr : ∀ f g n k, n ≤ f → n ≤ g → pascalParityFuel f n k = pascalParityFuel g n k
  | 0, g, n, k, hf, _ => by
    have : n = 0 := by cfomega
    subst this
    rw [pascalParityFuel_zero_left, pascalParityFuel_zero_left]
  | f + 1, 0, n, k, _, hg => by
    have : n = 0 := by cfomega
    subst this
    rw [pascalParityFuel_zero_left, pascalParityFuel_zero_left]
  | f + 1, g + 1, n, k, hf, hg => by
    show (if k = 0 then true else if n = 0 then false else if k % 2 = 1 ∧ n % 2 = 0 then false
        else pascalParityFuel f (n / 2) (k / 2)) =
      (if k = 0 then true else if n = 0 then false else if k % 2 = 1 ∧ n % 2 = 0 then false
        else pascalParityFuel g (n / 2) (k / 2))
    rw [pascalParityFuel_congr f g (n / 2) (k / 2) (by cfomega) (by cfomega)]

theorem pascalParity_fuel (f n k : Nat) (h : n ≤ f) : pascalParity n k = pascalParityFuel f n k :=
  pascalParityFuel_congr n f n k (Nat.le_refl n) h

/-- `C(n, 0) = 1`. -/
theorem pascalParity_zero_right (n : Nat) : pascalParity n 0 = true := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- `C(0, k) = 0` for `k ≥ 1`. -/
theorem pascalParity_zero_left (k : Nat) (hk : k ≠ 0) : pascalParity 0 k = false := by
  show decide (k = 0) = false
  exact decide_eq_false hk

/-- One digit of the Lucas recursion. -/
theorem pascalParity_step (n k : Nat) (hk : k ≠ 0) (hn : n ≠ 0) :
    pascalParity n k = (if k % 2 = 1 ∧ n % 2 = 0 then false else pascalParity (n / 2) (k / 2)) := by
  rw [pascalParity_fuel (n + 1) n k (by cfomega)]
  show (if k = 0 then true else if n = 0 then false else if k % 2 = 1 ∧ n % 2 = 0 then false
      else pascalParityFuel n (n / 2) (k / 2)) = _
  rw [if_neg hk, if_neg hn, pascalParityFuel_congr n (n / 2) (n / 2) (k / 2) (by cfomega) (Nat.le_refl _)]
  rfl

theorem pascalParity_even_even (a b : Nat) : pascalParity (2 * a) (2 * b) = pascalParity a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.mul_zero, pascalParity_zero_right, pascalParity_zero_right]
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [Nat.mul_zero, pascalParity_zero_left _ (by cfomega), pascalParity_zero_left _ (by cfomega)]
    · rw [pascalParity_step (2 * a) (2 * b) (by cfomega) (by cfomega),
        if_neg (fun h => by cfomega : ¬ (2 * b % 2 = 1 ∧ 2 * a % 2 = 0)),
        show 2 * a / 2 = a by cfomega, show 2 * b / 2 = b by cfomega]

theorem pascalParity_even_odd (a b : Nat) : pascalParity (2 * a) (2 * b + 1) = false := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.mul_zero, pascalParity_zero_left _ (by cfomega)]
  · rw [pascalParity_step (2 * a) (2 * b + 1) (by cfomega) (by cfomega),
      if_pos (⟨by cfomega, by cfomega⟩ : (2 * b + 1) % 2 = 1 ∧ 2 * a % 2 = 0)]

theorem pascalParity_odd_even (a b : Nat) : pascalParity (2 * a + 1) (2 * b) = pascalParity a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.mul_zero, pascalParity_zero_right, pascalParity_zero_right]
  · rw [pascalParity_step (2 * a + 1) (2 * b) (by cfomega) (by cfomega),
      if_neg (fun h => by cfomega : ¬ (2 * b % 2 = 1 ∧ (2 * a + 1) % 2 = 0)),
      show (2 * a + 1) / 2 = a by cfomega, show 2 * b / 2 = b by cfomega]

theorem pascalParity_odd_odd (a b : Nat) : pascalParity (2 * a + 1) (2 * b + 1) = pascalParity a b := by
  rw [pascalParity_step (2 * a + 1) (2 * b + 1) (by cfomega) (by cfomega),
    if_neg (fun h => by cfomega : ¬ ((2 * b + 1) % 2 = 1 ∧ (2 * a + 1) % 2 = 0)),
    show (2 * a + 1) / 2 = a by cfomega, show (2 * b + 1) / 2 = b by cfomega]

/-- **Pascal's rule mod 2**: `C(n+1, k+1) = C(n, k) + C(n, k+1)`. -/
theorem pascalParity_succ (n : Nat) : ∀ k, pascalParity (n + 1) (k + 1) = bxor (pascalParity n k) (pascalParity n (k + 1)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a := ⟨n / 2, by cfomega⟩
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b := ⟨k / 2, by cfomega⟩
        rw [pascalParity_odd_odd, pascalParity_even_even, pascalParity_even_odd]
        cases pascalParity a b <;> rfl
      · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b + 1 := ⟨k / 2, by cfomega⟩
        rw [show 2 * b + 1 + 1 = 2 * (b + 1) by cfomega, pascalParity_odd_even, pascalParity_even_odd,
          pascalParity_even_even]
        cases pascalParity a (b + 1) <;> rfl
    · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by cfomega⟩
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b := ⟨k / 2, by cfomega⟩
        rw [show 2 * a + 1 + 1 = 2 * (a + 1) by cfomega, pascalParity_even_odd, pascalParity_odd_even,
          pascalParity_odd_odd]
        cases pascalParity a b <;> rfl
      · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b + 1 := ⟨k / 2, by cfomega⟩
        rw [show 2 * a + 1 + 1 = 2 * (a + 1) by cfomega, show 2 * b + 1 + 1 = 2 * (b + 1) by cfomega,
          pascalParity_even_even, pascalParity_odd_odd, pascalParity_odd_even, ih a (by cfomega) b]

/-- `C(n, k) = 0` for `n < k`. -/
theorem pascalParity_gt (n : Nat) : ∀ k, n < k → pascalParity n k = false := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact pascalParity_zero_left k (by cfomega)
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a := ⟨n / 2, by cfomega⟩
        rcases Nat.mod_two_eq_zero_or_one k with h' | h'
        · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b := ⟨k / 2, by cfomega⟩
          rw [pascalParity_even_even]
          exact ih a (by cfomega) b (by cfomega)
        · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b + 1 := ⟨k / 2, by cfomega⟩
          exact pascalParity_even_odd a b
      · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by cfomega⟩
        rcases Nat.mod_two_eq_zero_or_one k with h' | h'
        · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b := ⟨k / 2, by cfomega⟩
          rw [pascalParity_odd_even]
          exact ih a (by cfomega) b (by cfomega)
        · obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b + 1 := ⟨k / 2, by cfomega⟩
          rw [pascalParity_odd_odd]
          exact ih a (by cfomega) b (by cfomega)

/-- `C(n, n) = 1`. -/
theorem pascalParity_self (n : Nat) : pascalParity n n = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact pascalParity_zero_right 0
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a := ⟨n / 2, by cfomega⟩
        rw [pascalParity_even_even]
        exact ih a (by cfomega)
      · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by cfomega⟩
        rw [pascalParity_odd_odd]
        exact ih a (by cfomega)

/-! ## The iterated prefix is the Pascal transport -/

/-- **The `(n+1)`-fold prefix parity is the binomial transport**:
`prefixPow (n+1) g s = ⊕_{j<s} C(s−1−j, n) g j`. -/
theorem prefixPow_eq_pascal (g : Nat → Bool) :
    ∀ n s, prefixPow (n + 1) g s = xorBelow (fun j => pascalParity (s - 1 - j) n && g j) s
  | 0, s => by
    show xorBelow g s = _
    exact xorBelow_congr g _ s (fun j _ => by rw [pascalParity_zero_right, Bool.true_and])
  | n + 1, 0 => rfl
  | n + 1, s + 1 => by
    have ihs := prefixPow_eq_pascal g (n + 1) s
    have ihn := prefixPow_eq_pascal g n s
    show bxor (prefixPow (n + 2) g s) (prefixPow (n + 1) g s) =
      bxor (xorBelow (fun j => pascalParity (s + 1 - 1 - j) (n + 1) && g j) s)
        (pascalParity (s + 1 - 1 - s) (n + 1) && g s)
    rw [ihs, ihn, show s + 1 - 1 - s = 0 by cfomega, pascalParity_zero_left (n + 1) (by cfomega), Bool.false_and,
      ← xorBelow_bxor,
      xorBelow_congr (fun m => bxor (pascalParity (s - 1 - m) (n + 1) && g m) (pascalParity (s - 1 - m) n && g m))
        (fun j => pascalParity (s + 1 - 1 - j) (n + 1) && g j) s (fun j hj => ?_)]
    · cases xorBelow (fun j => pascalParity (s + 1 - 1 - j) (n + 1) && g j) s <;> rfl
    · show bxor (pascalParity (s - 1 - j) (n + 1) && g j) (pascalParity (s - 1 - j) n && g j) =
        (pascalParity (s + 1 - 1 - j) (n + 1) && g j)
      rw [show s + 1 - 1 - j = s - 1 - j + 1 by cfomega, pascalParity_succ]
      cases pascalParity (s - 1 - j) n <;> cases pascalParity (s - 1 - j) (n + 1) <;> cases g j <;> rfl

/-- The hockey stick mod 2: `⊕_{j<s} C(s−1−j, n) = C(s, n+1)`. -/
theorem pascalParity_hockey (n : Nat) : ∀ s, xorBelow (fun j => pascalParity (s - 1 - j) n) s = pascalParity s (n + 1)
  | 0 => by
    show false = pascalParity 0 (n + 1)
    rw [pascalParity_zero_left (n + 1) (by cfomega)]
  | s + 1 => by
    rw [xorBelow_front]
    show bxor (pascalParity (s + 1 - 1 - 0) n) (xorBelow (fun j => pascalParity (s + 1 - 1 - (j + 1)) n) s) = _
    rw [xorBelow_congr (fun j => pascalParity (s + 1 - 1 - (j + 1)) n) (fun j => pascalParity (s - 1 - j) n) s
        (fun j _ => by rw [show s + 1 - 1 - (j + 1) = s - 1 - j by cfomega]),
      pascalParity_hockey n s, show s + 1 - 1 - 0 = s by cfomega, pascalParity_succ]

/-- The iterated prefix of the constant word is the binomial transport of `1`. -/
theorem constPrefix_eq_pascal (n s : Nat) (hn : 1 ≤ n) :
    constPrefix n s = xorBelow (fun j => pascalParity (s - 1 - j) (n - 1)) s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by cfomega⟩
  rw [Nat.add_sub_cancel]
  show prefixPow (m + 1) (fun _ => true) s = _
  rw [prefixPow_eq_pascal]
  exact xorBelow_congr _ _ s (fun j _ => Bool.and_true _)

/-- **Lucas closed form**: `constPrefix n s = C(s, n) mod 2`. -/
theorem constPrefix_eq_lucas (n s : Nat) : constPrefix n s = pascalParity s n := by
  cases n with
  | zero =>
    show true = pascalParity s 0
    rw [pascalParity_zero_right]
  | succ n =>
    show prefixPow (n + 1) (fun _ => true) s = pascalParity s (n + 1)
    rw [prefixPow_eq_pascal, xorBelow_congr _ (fun j => pascalParity (s - 1 - j) n) s (fun j _ => Bool.and_true _),
      pascalParity_hockey n s]

/-- The linear part of the tower in closed form: `C(s, n+1) mod 2`. -/
theorem linearTower_eq_lucas (n s : Nat) : linearTower n s = pascalParity s (n + 1) := by
  rw [linearTower_eq_constPrefix, constPrefix_eq_lucas]

/-! ## The center as a Lucas-weighted sum of the masks -/

/-- The mask `i` transported `d + 1` times: `⊕_{j<s} C(s−1−j, d) ∧ exposed i j`. -/
def maskPascal (i d s : Nat) : Bool := xorBelow (fun j => pascalParity (s - 1 - j) d && exposed i j) s

/-- The weight of the mask at diagonal `i`, time `j`, at the center time `t`. -/
def maskWeight (t i j : Nat) : Bool := pascalParity (t - 1 - j) (t - 2 - i)

theorem maskPascal_eq_weight (t i : Nat) :
    maskPascal i (t - 2 - i) t = xorBelow (fun j => maskWeight t i j && exposed i j) t := rfl

theorem maskPascal_eq_prefixPow (i d s : Nat) : maskPascal i d s = prefixPow (d + 1) (exposed i) s :=
  (prefixPow_eq_pascal (exposed i) d s).symm

/-- One more integration of a transported mask. -/
theorem maskPascal_shift (i d s : Nat) : xorBelow (fun s' => maskPascal i d s') s = maskPascal i (d + 1) s := by
  rw [xorBelow_congr (fun s' => maskPascal i d s') (prefixPow (d + 1) (exposed i)) s
      (fun s' _ => maskPascal_eq_prefixPow i d s'),
    maskPascal_eq_prefixPow]
  rfl

/-- The partial Lucas sums: `lucasPartial k i s = ⊕_{i' ≤ i} maskPascal i' (k − i') s`. -/
def lucasPartial (k : Nat) : Nat → Nat → Bool
  | 0, s => maskPascal 0 k s
  | i + 1, s => bxor (lucasPartial k i s) (maskPascal (i + 1) (k - (i + 1)) s)

/-- The Lucas-weighted sum of the masks `0 .. k` at time `s`. -/
def lucasSum (k s : Nat) : Bool := lucasPartial k k s

theorem lucasPartial_shift (k : Nat) :
    ∀ i, i ≤ k → ∀ s, xorBelow (fun s' => lucasPartial k i s') s = lucasPartial (k + 1) i s
  | 0, _, s => by
    show xorBelow (fun s' => maskPascal 0 k s') s = maskPascal 0 (k + 1) s
    exact maskPascal_shift 0 k s
  | i + 1, hi, s => by
    show xorBelow (fun s' => bxor (lucasPartial k i s') (maskPascal (i + 1) (k - (i + 1)) s')) s =
      bxor (lucasPartial (k + 1) i s) (maskPascal (i + 1) (k + 1 - (i + 1)) s)
    rw [xorBelow_bxor (fun s' => lucasPartial k i s') (fun s' => maskPascal (i + 1) (k - (i + 1)) s') s,
      lucasPartial_shift k i (by cfomega) s, maskPascal_shift, show k - (i + 1) + 1 = k + 1 - (i + 1) by cfomega]

/-- **The transport of the masks is the Lucas-weighted sum.** -/
theorem maskTransport_eq_lucas (k : Nat) : ∀ s, maskTransport k s = lucasSum k s
  | s => by
    cases k with
    | zero =>
      show xorBelow (exposed 0) s = maskPascal 0 0 s
      unfold maskPascal
      exact xorBelow_congr _ _ s (fun j _ => by rw [pascalParity_zero_right, Bool.true_and])
    | succ k =>
      show bxor (xorBelow (maskTransport k) s) (xorBelow (exposed (k + 1)) s) = lucasPartial (k + 1) (k + 1) s
      rw [xorBelow_congr (maskTransport k) (fun s' => lucasPartial k k s') s (fun s' _ => maskTransport_eq_lucas k s'),
        lucasPartial_shift k k (Nat.le_refl k) s]
      show bxor (lucasPartial (k + 1) k s) (xorBelow (exposed (k + 1)) s) =
        bxor (lucasPartial (k + 1) k s) (maskPascal (k + 1) (k + 1 - (k + 1)) s)
      rw [Nat.sub_self]
      unfold maskPascal
      rw [xorBelow_congr (exposed (k + 1)) (fun j => pascalParity (s - 1 - j) 0 && exposed (k + 1) j) s
        (fun j _ => by rw [pascalParity_zero_right, Bool.true_and])]

theorem maskTransport_lucas (k s : Nat) : maskTransport k s = lucasSum k s := maskTransport_eq_lucas k s

/-- **The center is the complement of the Lucas-weighted sum of the exposed masks.** -/
theorem center_eq_lucas (t : Nat) (ht : 2 ≤ t) : center t = !(lucasSum (t - 2) t) := by
  rw [center_eq_not_maskTransport t ht, maskTransport_lucas]

/-! ## The first mask words, the corner, and Lucas's higher-bit law -/

/-- Diagonal `0` shows through diagonal `1` exactly at even times. -/
theorem exposed_zero (i : Nat) : exposed 0 i = !(timeParity i) := by
  show (towerWord 0 i && !(towerWord 1 i)) = !(timeParity i)
  rw [towerWord_zero, towerWord_one]
  cases timeParity i <;> rfl

/-- Diagonal `1` never shows through diagonal `2` (both are the time parity). -/
theorem exposed_one (i : Nat) : exposed 1 i = false := by
  show (towerWord 1 i && !(towerWord 2 i)) = false
  rw [towerWord_one, ← rdiag_eq_towerWord, Rule30UOR.Band.rdiag_two_eq_parity]
  show (timeParity i && !(timeParity i)) = false
  cases timeParity i <;> rfl

/-- **Lucas's higher-bit independence**: below `2^m` the binomial parity ignores the bits of the
row at and above `2^m`. The freezing law of the diagonal frame, with no side-terms. -/
theorem pascalParity_add_twopow_mul : ∀ m n d q, d < twopow m →
    pascalParity (n + twopow m * q) d = pascalParity n d
  | 0, n, d, q, hd => by
    have : d = 0 := by
      have h1 : twopow 0 = 1 := rfl
      cfomega
    subst this
    rw [pascalParity_zero_right, pascalParity_zero_right]
  | m + 1, n, d, q, hd => by
    have h2 : twopow (m + 1) = 2 * twopow m := by rw [twopow_succ]; cfomega
    rw [h2] at hd ⊢
    rw [Nat.mul_assoc]
    obtain ⟨a, e, he, rfl⟩ : ∃ a e, e < 2 ∧ n = 2 * a + e := ⟨n / 2, n % 2, Nat.mod_lt _ (by decide), by cfomega⟩
    obtain ⟨b, f, hf, rfl⟩ : ∃ b f, f < 2 ∧ d = 2 * b + f := ⟨d / 2, d % 2, Nat.mod_lt _ (by decide), by cfomega⟩
    have hb : b < twopow m := by cfomega
    have ih := pascalParity_add_twopow_mul m a b q hb
    rcases Nat.lt_or_ge e 1 with he0 | he1 <;> rcases Nat.lt_or_ge f 1 with hf0 | hf1
    · rw [show e = 0 by cfomega, show f = 0 by cfomega]
      simp only [Nat.add_zero]
      rw [show 2 * a + 2 * (twopow m * q) = 2 * (a + twopow m * q) by cfomega,
        pascalParity_even_even, pascalParity_even_even, ih]
    · rw [show e = 0 by cfomega, show f = 1 by cfomega]
      simp only [Nat.add_zero]
      rw [show 2 * a + 2 * (twopow m * q) = 2 * (a + twopow m * q) by cfomega,
        pascalParity_even_odd, pascalParity_even_odd]
    · rw [show e = 1 by cfomega, show f = 0 by cfomega]
      simp only [Nat.add_zero]
      rw [show 2 * a + 1 + 2 * (twopow m * q) = 2 * (a + twopow m * q) + 1 by cfomega,
        pascalParity_odd_even, pascalParity_odd_even, ih]
    · rw [show e = 1 by cfomega, show f = 1 by cfomega,
        show 2 * a + 1 + 2 * (twopow m * q) = 2 * (a + twopow m * q) + 1 by cfomega,
        pascalParity_odd_odd, pascalParity_odd_odd, ih]

/-- A fold over a window ignores terms that vanish between its first `n` places and `M`. -/
theorem xorBelow_of_vanish (g : Nat → Bool) (n M : Nat) (hg : ∀ j, n ≤ j → j < M → g j = false) :
    ∀ m, n ≤ m → m ≤ M → xorBelow g m = xorBelow g n
  | 0, h, _ => by rw [show n = 0 by cfomega]
  | m + 1, h, hM => by
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [show n = m + 1 by cfomega]
    · show bxor (xorBelow g m) (g m) = xorBelow g n
      rw [hg m hm (by cfomega), xorBelow_of_vanish g n M hg m hm (by cfomega)]
      cases xorBelow g n <;> rfl

/-- **The corner**: diagonal `i` reaches the center at time `t` only through its first `i + 2` times. -/
theorem maskPascal_corner (t i : Nat) (hi : i + 2 ≤ t) :
    maskPascal i (t - 2 - i) t = xorBelow (fun j => maskWeight t i j && exposed i j) (i + 2) := by
  rw [maskPascal_eq_weight]
  apply xorBelow_of_vanish _ (i + 2) t _ t hi (Nat.le_refl t)
  intro j hj hjt
  show (pascalParity (t - 1 - j) (t - 2 - i) && exposed i j) = false
  rw [pascalParity_gt _ _ (by cfomega)]
  rfl

/-- In the kit's vocabulary: diagonal `k + 1` has period `2^k` (`k ≥ 1`). -/
theorem per_succ_twopow (k : Nat) (hk : 1 ≤ k) :
    Ruliology.CellularAutomata.Rule30RightPeriods.Per (k + 1) (2 ^ k) := by
  intro t
  rw [← Rule30UOR.Right.rdiag_eq_R, ← Rule30UOR.Right.rdiag_eq_R, ← twopow_eq_pow]
  have h := rdiag_period_half (k + 1) t (by cfomega)
  rwa [show k + 1 - 1 = k by cfomega] at h

/-- **The right-period threshold of scale `k` is at least `k + 1`** (the kit proves `k`): the
halving gives diagonal `k + 1` the period `2^k`, and periods descend to lower diagonals. -/
theorem right_threshold_ge (k J : Nat) (hk : 1 ≤ k) (h : Rule30UOR.Interfaces.IsRightThreshold k J) :
    k + 1 ≤ J := by
  rcases Nat.lt_or_ge J (k + 1) with hJ | hJ
  · exact absurd (Rule30UOR.KitConstructive.per_mono_le (by cfomega) (per_succ_twopow k hk)) h.2
  · exact hJ

end Rule30UOR.Antidiagonal
