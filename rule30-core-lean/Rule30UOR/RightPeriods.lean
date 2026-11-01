module
public import Rule30UOR.LeftTower
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The periods of the right words

The word `k + 2` is the prefix parity of the OR-word `k` (`towerWord_eq_prefix`). If the OR-word
is `q`-periodic, the parity over any window of length `q` is the parity over `[0, q)`, which is the
word read at `q`: shifting by `q` adds the constant `towerWord (k + 2) q` (`towerWord_shift`). So
the word is `q`-periodic when that bit is `0` and `q`-antiperiodic when it is `1`; in both cases it
is `2q`-periodic. Starting from the periods `1` and `2` of the base words, the common period of two
consecutive words is `2^max`, and the doubling bit decides the next exponent (`jenExp`). -/

@[expose] public section

namespace Rule30UOR.RightPeriods

open Rule30UOR.Core Rule30UOR.Antidiagonal Rule30UOR.EdgeSplit

/-- The word `j` is `q`-periodic. -/
def WordPeriodic (j q : Nat) : Prop := ∀ s, towerWord j (s + q) = towerWord j s

/-- The OR-word `k` is `q`-periodic. -/
def OrPeriodic (k q : Nat) : Prop := ∀ s, orWord k (s + q) = orWord k s

/-! ## The affine shift law -/

/-- **Affine shift law**: under a period `q` of the OR-word, shifting the word `k + 2` by `q`
adds the word's value at `q`. -/
theorem towerWord_shift (k q : Nat) (h : OrPeriodic k q) :
    ∀ s, towerWord (k + 2) (s + q) = bxor (towerWord (k + 2) s) (towerWord (k + 2) q) := by
  intro s
  rw [towerWord_eq_prefix k (s + q), towerWord_eq_prefix k s, towerWord_eq_prefix k q, xorBelow_split,
    xorBelow_window (orWord k) q h s]

/-! ## The dichotomy -/

theorem wordPeriodic_of_or (k q : Nat) (h : OrPeriodic k q) (hz : towerWord (k + 2) q = false) :
    WordPeriodic (k + 2) q := by
  intro s
  rw [towerWord_shift k q h s, hz]
  cases towerWord (k + 2) s <;> rfl

theorem word_antiperiodic_of_or (k q : Nat) (h : OrPeriodic k q) (ho : towerWord (k + 2) q = true) :
    ∀ s, towerWord (k + 2) (s + q) = !(towerWord (k + 2) s) := by
  intro s
  rw [towerWord_shift k q h s, ho]
  cases towerWord (k + 2) s <;> rfl

/-- **Period `q` or `2q`**: a period of the OR-word doubles at most once in the word above. -/
theorem wordPeriodic_double (k q : Nat) (h : OrPeriodic k q) : WordPeriodic (k + 2) (2 * q) := by
  intro s
  rw [show s + 2 * q = (s + q) + q by cfomega, towerWord_shift k q h (s + q), towerWord_shift k q h s]
  cases towerWord (k + 2) s <;> cases towerWord (k + 2) q <;> rfl

/-! ## Periods combine -/

theorem orPeriodic_of_words (k q : Nat) (h1 : WordPeriodic (k + 1) q) (h0 : WordPeriodic k q) :
    OrPeriodic k q := by
  intro s
  unfold orWord
  rw [h1 s, h0 s]

theorem wordPeriodic_mul (j q n : Nat) (h : WordPeriodic j q) : WordPeriodic j (n * q) := by
  induction n with
  | zero => intro s; rw [Nat.zero_mul, Nat.add_zero]
  | succ n ih => intro s; rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]

theorem twopow_add (m n : Nat) : twopow (m + n) = twopow m * twopow n := by
  induction m with
  | zero => rw [Nat.zero_add]; show twopow n = 1 * twopow n; rw [Nat.one_mul]
  | succ m ih => rw [Nat.add_right_comm, twopow_succ, twopow_succ, ih, Nat.add_mul]

/-- A word with period `2^a` has every period `2^b` with `a ≤ b`. -/
theorem wordPeriodic_twopow_mono (j a b : Nat) (hab : a ≤ b) (h : WordPeriodic j (twopow a)) :
    WordPeriodic j (twopow b) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = d + a := ⟨b - a, by cfomega⟩
  rw [twopow_add]
  exact wordPeriodic_mul j (twopow a) (twopow d) h

/-! ## The Jen exponent -/

/-- `false ↦ 0`, `true ↦ 1`. -/
def boolNat : Bool → Nat
  | false => 0
  | true => 1

/-- The exponent computed by the law: the common period `2^max` of the two words below, doubled
when the word reads `1` at that period. -/
def jenExp : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => max (jenExp (k + 1)) (jenExp k) +
      boolNat (towerWord (k + 2) (twopow (max (jenExp (k + 1)) (jenExp k))))

theorem jenExp_zero : jenExp 0 = 0 := rfl

theorem jenExp_one : jenExp 1 = 1 := rfl

theorem jenExp_succ_succ (k : Nat) : jenExp (k + 2) = max (jenExp (k + 1)) (jenExp k) +
    boolNat (towerWord (k + 2) (twopow (max (jenExp (k + 1)) (jenExp k)))) := rfl

theorem jenExp_step_periodic (k : Nat) (h1 : WordPeriodic (k + 1) (twopow (jenExp (k + 1))))
    (h0 : WordPeriodic k (twopow (jenExp k))) : WordPeriodic (k + 2) (twopow (jenExp (k + 2))) := by
  have g1 := wordPeriodic_twopow_mono (k + 1) _ _ (Nat.le_max_left (jenExp (k + 1)) (jenExp k)) h1
  have g0 := wordPeriodic_twopow_mono k _ _ (Nat.le_max_right (jenExp (k + 1)) (jenExp k)) h0
  have hor := orPeriodic_of_words k _ g1 g0
  rw [jenExp_succ_succ]
  cases hb : towerWord (k + 2) (twopow (max (jenExp (k + 1)) (jenExp k))) with
  | false =>
    show WordPeriodic (k + 2) (twopow (max (jenExp (k + 1)) (jenExp k) + 0))
    rw [Nat.add_zero]
    exact wordPeriodic_of_or k _ hor hb
  | true =>
    show WordPeriodic (k + 2) (twopow (max (jenExp (k + 1)) (jenExp k) + 1))
    rw [twopow_succ, ← Nat.two_mul]
    exact wordPeriodic_double k _ hor

theorem jenExp_pair : ∀ n, WordPeriodic n (twopow (jenExp n)) ∧ WordPeriodic (n + 1) (twopow (jenExp (n + 1)))
  | 0 => ⟨towerWord_add_twopow 0, towerWord_add_twopow 1⟩
  | n + 1 => by
    have ih := jenExp_pair n
    exact ⟨ih.2, jenExp_step_periodic n ih.2 ih.1⟩

/-- **The word `j` is `2^(jenExp j)`-periodic.** -/
theorem towerWord_jen_periodic (j : Nat) : WordPeriodic j (twopow (jenExp j)) := (jenExp_pair j).1

/-! ## The first values -/

theorem jenExp_two : jenExp 2 = 1 := by
  rw [jenExp_succ_succ, jenExp_one, jenExp_zero, towerWord_eq_row]; decide

theorem jenExp_three : jenExp 3 = 2 := by
  rw [jenExp_succ_succ, jenExp_two, jenExp_one, towerWord_eq_row]; decide

theorem jenExp_four : jenExp 4 = 3 := by
  rw [jenExp_succ_succ, jenExp_three, jenExp_two, towerWord_eq_row]; decide

theorem jenExp_five : jenExp 5 = 3 := by
  rw [jenExp_succ_succ, jenExp_four, jenExp_three, towerWord_eq_row]; decide

theorem jenExp_six : jenExp 6 = 4 := by
  rw [jenExp_succ_succ, jenExp_five, jenExp_four, towerWord_eq_row]; decide

theorem jenExp_seven : jenExp 7 = 5 := by
  rw [jenExp_succ_succ, jenExp_six, jenExp_five, towerWord_eq_row]; decide

theorem jenExp_eight : jenExp 8 = 5 := by
  rw [jenExp_succ_succ, jenExp_seven, jenExp_six, towerWord_eq_row]; decide

theorem jenExp_nine : jenExp 9 = 6 := by
  rw [jenExp_succ_succ, jenExp_eight, jenExp_seven, towerWord_eq_row]; decide

theorem jenExp_values : jenExp 2 = 1 ∧ jenExp 3 = 2 ∧ jenExp 4 = 3 ∧ jenExp 5 = 3 ∧ jenExp 6 = 4 ∧
    jenExp 7 = 5 ∧ jenExp 8 = 5 ∧ jenExp 9 = 6 :=
  ⟨jenExp_two, jenExp_three, jenExp_four, jenExp_five, jenExp_six, jenExp_seven, jenExp_eight, jenExp_nine⟩

/-! ## The step bound -/

theorem boolNat_le_one (b : Bool) : boolNat b ≤ 1 := by
  cases b
  · show 0 ≤ 1; cfomega
  · show 1 ≤ 1; cfomega

/-- The exponent never decreases. -/
theorem jenExp_le_succ (j : Nat) : jenExp j ≤ jenExp (j + 1) := by
  cases j with
  | zero => show 0 ≤ 1; cfomega
  | succ k =>
    rw [jenExp_succ_succ]
    have := Nat.le_max_left (jenExp (k + 1)) (jenExp k)
    cfomega

/-- With monotonicity the maximum is the upper word's exponent. -/
theorem jenExp_succ_succ_eq (k : Nat) : jenExp (k + 2) = jenExp (k + 1) +
    boolNat (towerWord (k + 2) (twopow (jenExp (k + 1)))) := by
  rw [jenExp_succ_succ, Nat.max_eq_left (jenExp_le_succ k)]

/-- **The exponent rises by at most one per word.** -/
theorem jenExp_succ_le (j : Nat) : jenExp (j + 1) ≤ jenExp j + 1 := by
  cases j with
  | zero => show 1 ≤ 0 + 1; cfomega
  | succ k =>
    rw [jenExp_succ_succ_eq]
    have := boolNat_le_one (towerWord (k + 2) (twopow (jenExp (k + 1))))
    cfomega

theorem jenExp_le (j : Nat) : jenExp j ≤ j := by
  induction j with
  | zero => show 0 ≤ 0; cfomega
  | succ j ih => have := jenExp_succ_le j; cfomega

/-- From word `2` on, the proved period is at most the half period `2^(j-1)`. -/
theorem jenExp_le_pred (j : Nat) : jenExp (j + 2) ≤ j + 1 := by
  induction j with
  | zero => rw [jenExp_two]; cfomega
  | succ j ih =>
    have h : jenExp (j + 1 + 2) ≤ jenExp (j + 2) + 1 := jenExp_succ_le (j + 2)
    cfomega

/-! ## The two readings of a word -/

/-- The doubling bit of word `t`: the word read at the common period of the two words below. -/
def doublingBit (t : Nat) : Bool := towerWord t (twopow (max (jenExp (t - 1)) (jenExp (t - 2))))

/-- **The exponent recursion**: the doubling bit decides whether the period doubles. -/
theorem jenExp_succ_eq (k : Nat) :
    jenExp (k + 2) = max (jenExp (k + 1)) (jenExp k) + boolNat (doublingBit (k + 2)) := by
  rw [jenExp_succ_succ]
  rfl

/-- **Two readings of word `t`**: at position `t` it is the center; at the common period of the two
words below it is the doubling bit. -/
theorem towerWord_two_readings (t : Nat) :
    center t = towerWord t t ∧ doublingBit t = towerWord t (twopow (max (jenExp (t - 1)) (jenExp (t - 2)))) :=
  ⟨center_eq_towerWord t, rfl⟩

end Rule30UOR.RightPeriods
