module
public import Rule30UOR.Interfaces.Part01
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The carry ledger and the center readout

`phi` splits exactly into its `F₂`-linear part `phiLinear` (multiplication by
`q = 1 + X + X²`) and a shifted carry: `phi y = phiLinear y ^^^ (carry y <<< 1)`.
Iterating from the seed, every row is the linear evolution of the seed
XOR the accumulated carries, the ledger `winWitt 0 t`:

    row t = phiLinearPow t 1 ^^^ winWitt 0 t.

The center reads bit `t` of row `t`. On the linear part that bit is the
central trinomial coefficient of `q^t`, which is odd for every `t` (proved
here by Frobenius, `q^(2m) = q(X²)^m`, without binomial sums). Hence

    center t = !(winWitt 0 t).testBit t :

the center column is the complement of the diagonal of the carry ledger,
and a center period is exactly a period of that diagonal. This is the exact
form of "decode, accumulate exactly, encode once": the ledger is the exact
accumulation, the diagonal readout is the single encoding, and the
nonlinearity of Rule 30 sits entirely in the carries. -/

@[expose] public section

namespace Rule30UOR.Ledger

open Rule30UOR.Core

/-! ## Bitwise algebra -/

theorem xor_xor_self (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem xor_left_comm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem or_eq_xor_xor_and (a b : Nat) : a ||| b = (a ^^^ b) ^^^ (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem shiftLeft_one_and_two (y : Nat) : (y <<< 1) &&& (y <<< 2) = carry y <<< 1 := by
  show (y <<< 1) &&& (y <<< 2) = (y &&& (y <<< 1)) <<< 1
  rw [Nat.shiftLeft_and_distrib, Nat.shiftLeft_add y 1 1]

/-- The exact split of `phi` into its linear part and the shifted carry. -/
theorem phi_eq_linear_xor_carry (y : Nat) : phi y = phiLinear y ^^^ (carry y <<< 1) := by
  show y ^^^ ((y <<< 1) ||| (y <<< 2)) = (y ^^^ (y <<< 1)) ^^^ (y <<< 2) ^^^ (carry y <<< 1)
  rw [or_eq_xor_xor_and, shiftLeft_one_and_two]
  simp only [Nat.xor_assoc]

theorem phiLinear_xor (a b : Nat) : phiLinear (a ^^^ b) = phiLinear a ^^^ phiLinear b := by
  show ((a ^^^ b) ^^^ ((a ^^^ b) <<< 1)) ^^^ ((a ^^^ b) <<< 2) =
    ((a ^^^ (a <<< 1)) ^^^ (a <<< 2)) ^^^ ((b ^^^ (b <<< 1)) ^^^ (b <<< 2))
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases (a <<< 1).testBit i <;> cases (b <<< 1).testBit i <;>
    cases (a <<< 2).testBit i <;> cases (b <<< 2).testBit i <;> rfl

/-! ## The row as linear evolution plus ledger -/

/-- `row t = q^t · 1 ⊕ ledger t`. -/
theorem row_eq_linear_xor_ledger (t : Nat) : row t = phiLinearPow t 1 ^^^ winWitt 0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show phi (row t) = phiLinearPow (Nat.succ t) 1 ^^^ winWitt 0 (Nat.succ t)
    rw [phiLinearPow_step, winWitt_step, phi_eq_linear_xor_carry, ih, phiLinear_xor, Nat.zero_add, ← ih]
    show _ = phiLinear (phiLinearPow t 1) ^^^ (phiLinear (winWitt 0 t) ^^^ (carry (row t) <<< 1))
    simp only [Nat.xor_assoc]

/-! ## The central trinomial coefficient is odd

`phiLin s` is multiplication by `1 + X^s + X^(2s)`. Frobenius: `phiLin s ∘ phiLin s
= phiLin (2s)`, so `q^(2m) = (q(X²))^m`, whose coefficients are those of `q^m`
spread to even positions. -/

def phiLin (s y : Nat) : Nat := (y ^^^ (y <<< s)) ^^^ (y <<< (2 * s))

def phiLinPow (s : Nat) : Nat → Nat → Nat
  | 0, y => y
  | m + 1, y => phiLin s (phiLinPow s m y)

theorem phiLinear_eq_phiLin (y : Nat) : phiLinear y = phiLin 1 y := by
  show (y ^^^ (y <<< 1)) ^^^ (y <<< 2) = (y ^^^ (y <<< 1)) ^^^ (y <<< (2 * 1))
  rfl

theorem phiLinearPow_eq_phiLinPow (m y : Nat) : phiLinearPow m y = phiLinPow 1 m y := by
  induction m with
  | zero => rfl
  | succ m ih => rw [phiLinearPow_step, ih, phiLinear_eq_phiLin]; rfl

theorem phiLin_xor (s a b : Nat) : phiLin s (a ^^^ b) = phiLin s a ^^^ phiLin s b := by
  unfold phiLin
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases (a <<< s).testBit i <;> cases (b <<< s).testBit i <;>
    cases (a <<< (2 * s)).testBit i <;> cases (b <<< (2 * s)).testBit i <;> rfl

theorem phiLin_shiftLeft (s k y : Nat) : phiLin s (y <<< k) = phiLin s y <<< k := by
  unfold phiLin
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib, ← Nat.shiftLeft_add, ← Nat.shiftLeft_add,
    Nat.add_comm k s, Nat.add_comm k (2 * s), Nat.shiftLeft_add, Nat.shiftLeft_add]

/-- Frobenius: `(1 + X^s + X^(2s))² = 1 + X^(2s) + X^(4s)`. -/
theorem phiLin_phiLin (s y : Nat) : phiLin s (phiLin s y) = phiLin (2 * s) y := by
  rw [show phiLin s y = (y ^^^ (y <<< s)) ^^^ (y <<< (2 * s)) from rfl, phiLin_xor, phiLin_xor,
    phiLin_shiftLeft, phiLin_shiftLeft]
  unfold phiLin
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib,
    Nat.shiftLeft_xor_distrib, ← Nat.shiftLeft_add, ← Nat.shiftLeft_add, ← Nat.shiftLeft_add,
    ← Nat.shiftLeft_add]
  have e1 : s + s = 2 * s := by cfomega
  have e2 : 2 * s + s = s + 2 * s := by cfomega
  have e3 : 2 * s + 2 * s = 2 * (2 * s) := by cfomega
  rw [e1, e2, e3]
  simp only [Nat.xor_assoc]
  simp only [Nat.xor_comm, xor_left_comm, Nat.xor_self, Nat.xor_zero, Nat.zero_xor, xor_xor_self]

theorem phiLinPow_two_mul (m y : Nat) : phiLinPow 1 (2 * m) y = phiLinPow 2 m y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show phiLin 1 (phiLin 1 (phiLinPow 1 (2 * m) y)) = phiLin 2 (phiLinPow 2 m y)
    rw [ih, phiLin_phiLin]

theorem testBit_phiLin (s y j : Nat) :
    (phiLin s y).testBit j =
      ((y.testBit j ^^ (decide (j ≥ s) && y.testBit (j - s))) ^^
        (decide (j ≥ 2 * s) && y.testBit (j - 2 * s))) := by
  unfold phiLin
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]

/-- The coefficients of `(1 + X^s + X^(2s))^m` are those of `q^m` at the
multiples of `s`, and zero elsewhere. -/
theorem phiLinPow_spread (s : Nat) (hs : 0 < s) (m : Nat) :
    ∀ i r, r < s → (phiLinPow s m 1).testBit (s * i + r) =
      (decide (r = 0) && (phiLinPow 1 m 1).testBit i) := by
  induction m with
  | zero =>
    intro i r hr
    show (1 : Nat).testBit (s * i + r) = (decide (r = 0) && (1 : Nat).testBit i)
    rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases hi : i = 0
    · subst hi
      by_cases hr0 : r = 0
      · subst hr0; simp
      · simp [hr0, Ne.symm hr0]
    · have h1 : ¬ (0 = s * i + r) := by
        intro h
        have : s * i ≥ s := Nat.le_mul_of_pos_right s (Nat.pos_of_ne_zero hi)
        cfomega
      simp [h1, Ne.symm hi]
  | succ m ih =>
    intro i r hr
    show (phiLin s (phiLinPow s m 1)).testBit (s * i + r) = _
    rw [testBit_phiLin]
    show _ = (decide (r = 0) && (phiLin 1 (phiLinPow 1 m 1)).testBit i)
    rw [testBit_phiLin]
    rcases i with _ | _ | k
    · have h0 := ih 0 r hr
      simp only [Nat.mul_zero, Nat.zero_add] at h0 ⊢
      have g1 : ¬ (r ≥ s) := by cfomega
      have g2 : ¬ (r ≥ 2 * s) := by cfomega
      have g3 : ¬ ((0 : Nat) ≥ 1) := by cfomega
      have g4 : ¬ ((0 : Nat) ≥ 2 * 1) := by cfomega
      rw [h0]
      simp only [g1, g2, g3, g4, decide_false, Bool.false_and, Bool.xor_false]
    · have h1 := ih 1 r hr
      have h0 := ih 0 r hr
      simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_add] at h1 h0 ⊢
      have g1 : s + r ≥ s := by cfomega
      have g2 : ¬ (s + r ≥ 2 * s) := by cfomega
      have g3 : (1 : Nat) ≥ 1 := by cfomega
      have g4 : ¬ ((1 : Nat) ≥ 2 * 1) := by cfomega
      have e1 : s + r - s = r := by cfomega
      have e2 : (1 : Nat) - 1 = 0 := by cfomega
      rw [e1, e2, h1, h0]
      simp only [g1, g2, g3, g4, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.xor_false]
      cases hd : decide (r = 0) <;> simp
    · have h2 := ih (k + 2) r hr
      have h1 := ih (k + 1) r hr
      have h0 := ih k r hr
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at h2 h1 h0 ⊢
      simp only [Nat.add_assoc] at h2 h1 h0 ⊢
      have g1 : s * k + (s + (s + r)) ≥ s := by cfomega
      have g2 : s * k + (s + (s + r)) ≥ 2 * s := by cfomega
      have g3 : k + 2 ≥ 1 := by cfomega
      have g4 : k + 2 ≥ 2 := by cfomega
      have e1 : s * k + (s + (s + r)) - s = s * k + (s + r) := by cfomega
      have e2 : s * k + (s + (s + r)) - 2 * s = s * k + r := by cfomega
      have e3 : k + 2 - 1 = k + 1 := by cfomega
      have e4 : k + 2 - 2 = k := by cfomega
      rw [e1, e2, e3, e4, h2, h1, h0]
      simp only [g1, g2, g3, g4, decide_true, Bool.true_and]
      cases hd : decide (r = 0) <;> simp

/-- The central trinomial coefficient of `q^t` is odd: bit `t` of `q^t · 1`. -/
theorem linear_center : ∀ t, (phiLinPow 1 t 1).testBit t = true := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0; rfl
      · have ht : t = 2 * (t / 2) := by cfomega
        rw [ht, phiLinPow_two_mul]
        have hs := phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 0 (by decide)
        rw [Nat.add_zero] at hs
        rw [hs, ih (t / 2) (by cfomega)]
        rfl
    · have ht : t = 2 * (t / 2) + 1 := by cfomega
      rw [ht]
      show (phiLin 1 (phiLinPow 1 (2 * (t / 2)) 1)).testBit (2 * (t / 2) + 1) = true
      rw [phiLinPow_two_mul, testBit_phiLin]
      have b1 := phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 1 (by decide)
      have b0 := phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 0 (by decide)
      rw [Nat.add_zero] at b0
      have e1 : 2 * (t / 2) + 1 - 1 = 2 * (t / 2) := by cfomega
      have g1 : 2 * (t / 2) + 1 ≥ 1 := by cfomega
      rw [b1, e1, b0, ih (t / 2) (by cfomega)]
      rcases Nat.eq_zero_or_pos (t / 2) with hm | hm
      · rw [hm]
        decide
      · have g2 : 2 * (t / 2) + 1 ≥ 2 * 1 := by cfomega
        have e2 : 2 * (t / 2) + 1 - 2 * 1 = 2 * (t / 2 - 1) + 1 := by cfomega
        rw [e2]
        have b2 := phiLinPow_spread 2 (by decide) (t / 2) (t / 2 - 1) 1 (by decide)
        rw [b2]
        simp [g1, g2]

/-! ## The center as the complement of the ledger diagonal -/

theorem center_eq_testBit_row (t : Nat) : center t = (row t).testBit t := by
  rw [Rule30UOR.Interfaces.row_testBit, Rule30UOR.Scale.center_eq_kit, Rule30UOR.Right.center_eq_rcenter]
  rfl

/-- The diagonal of the carry ledger: bit `t` of the accumulated carries at time `t`. -/
def ledgerDiagonal (t : Nat) : Bool := (winWitt 0 t).testBit t

/-- `center t = ¬ ledgerDiagonal t`: the center column is the complement of the
diagonal of the carry ledger. -/
theorem center_eq_not_ledgerDiagonal (t : Nat) : center t = !ledgerDiagonal t := by
  unfold ledgerDiagonal
  rw [center_eq_testBit_row, row_eq_linear_xor_ledger, Nat.testBit_xor, phiLinearPow_eq_phiLinPow,
    linear_center]
  cases (winWitt 0 t).testBit t <;> rfl

/-- The ledger diagonal has period `P` from `T`. -/
def LedgerPeriodic (T P : Nat) : Prop := ∀ t, T ≤ t → ledgerDiagonal (t + P) = ledgerDiagonal t

/-- A center period is exactly a period of the ledger diagonal. -/
theorem centerPeriodic_iff_ledgerPeriodic (T P : Nat) :
    Rule30UOR.Scale.CenterPeriodic T P ↔ LedgerPeriodic T P := by
  unfold Rule30UOR.Scale.CenterPeriodic LedgerPeriodic
  constructor
  · intro h t ht
    have := h t ht
    rw [center_eq_not_ledgerDiagonal, center_eq_not_ledgerDiagonal] at this
    exact Bool.not_inj this
  · intro h t ht
    rw [center_eq_not_ledgerDiagonal, center_eq_not_ledgerDiagonal, h t ht]

/-! ## The linear part beside the center

The coefficients of `q^t` at `t ± 1` are the parity of the number of trailing
ones of `t`: `a(2m) = 0`, `a(2m+1) = ¬a(m)`. With `linear_center` this gives the
three coefficients of the linear part that the center's update reads. -/

def trailingParityFuel : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, t => if t % 2 = 0 then false else !trailingParityFuel f (t / 2)

/-- The parity of the number of trailing ones in the binary expansion of `t`. -/
def trailingParity (t : Nat) : Bool := trailingParityFuel t t

theorem trailingParityFuel_congr : ∀ f g t, t ≤ f → t ≤ g →
    trailingParityFuel f t = trailingParityFuel g t
  | 0, g, t, hf, _ => by
    have : t = 0 := by cfomega
    subst this
    cases g <;> rfl
  | f + 1, 0, t, _, hg => by
    have : t = 0 := by cfomega
    subst this
    rfl
  | f + 1, g + 1, t, hf, hg => by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; rfl
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by cfomega⟩
      show (if (u + 1) % 2 = 0 then false else !trailingParityFuel f ((u + 1) / 2)) =
        (if (u + 1) % 2 = 0 then false else !trailingParityFuel g ((u + 1) / 2))
      rw [trailingParityFuel_congr f g ((u + 1) / 2) (by cfomega) (by cfomega)]

theorem trailingParity_even (m : Nat) : trailingParity (2 * m) = false := by
  unfold trailingParity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; rfl
  · obtain ⟨u, hu⟩ : ∃ u, 2 * m = u + 1 := ⟨2 * m - 1, by cfomega⟩
    rw [hu]
    show (if (u + 1) % 2 = 0 then false else _) = false
    have : (u + 1) % 2 = 0 := by cfomega
    simp [this]

theorem trailingParity_odd (m : Nat) : trailingParity (2 * m + 1) = !trailingParity m := by
  unfold trailingParity
  show (if (2 * m + 1) % 2 = 0 then false else !trailingParityFuel (2 * m) ((2 * m + 1) / 2)) = _
  have h1 : ¬ ((2 * m + 1) % 2 = 0) := by cfomega
  have h2 : (2 * m + 1) / 2 = m := by cfomega
  rw [if_neg h1, h2, trailingParityFuel_congr (2 * m) m m (by cfomega) (Nat.le_refl m)]

/-- Bit `t + 1` of `q^t · 1` is the trailing-ones parity of `t`. -/
theorem linear_above_center : ∀ t, (phiLinPow 1 t 1).testBit (t + 1) = trailingParity t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have ht : t = 2 * (t / 2) := by cfomega
      rw [ht, phiLinPow_two_mul, trailingParity_even]
      have hs := phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 1 (by decide)
      rw [hs]
      rfl
    · have ht : t = 2 * (t / 2) + 1 := by cfomega
      rw [ht, trailingParity_odd]
      show (phiLin 1 (phiLinPow 1 (2 * (t / 2)) 1)).testBit (2 * (t / 2) + 1 + 1) = _
      rw [phiLinPow_two_mul, testBit_phiLin]
      have e0 : 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1) + 0 := by cfomega
      have e1 : 2 * (t / 2) + 1 + 1 - 1 = 2 * (t / 2) + 1 := by cfomega
      have e2 : 2 * (t / 2) + 1 + 1 - 2 * 1 = 2 * (t / 2) + 0 := by cfomega
      have g1 : 2 * (t / 2) + 1 + 1 ≥ 1 := by cfomega
      have g2 : 2 * (t / 2) + 1 + 1 ≥ 2 * 1 := by cfomega
      rw [e1, e2, e0, phiLinPow_spread 2 (by decide) (t / 2) (t / 2 + 1) 0 (by decide),
        phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 1 (by decide),
        phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 0 (by decide),
        ih (t / 2) (by cfomega), linear_center]
      have g3 : 2 ≤ 2 * (t / 2 + 1) := by cfomega
      simp [g1, g2, g3]

/-- Bit `t - 1` of `q^t · 1` is the trailing-ones parity of `t`, for `t ≥ 1`. -/
theorem linear_below_center : ∀ t, 1 ≤ t → (phiLinPow 1 t 1).testBit (t - 1) = trailingParity t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht1
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have ht : t = 2 * (t / 2) := by cfomega
      rw [ht, phiLinPow_two_mul, trailingParity_even]
      have e : 2 * (t / 2) - 1 = 2 * (t / 2 - 1) + 1 := by cfomega
      rw [e, phiLinPow_spread 2 (by decide) (t / 2) (t / 2 - 1) 1 (by decide)]
      rfl
    · have ht : t = 2 * (t / 2) + 1 := by cfomega
      rw [ht, trailingParity_odd]
      show (phiLin 1 (phiLinPow 1 (2 * (t / 2)) 1)).testBit (2 * (t / 2) + 1 - 1) = _
      rw [phiLinPow_two_mul, testBit_phiLin]
      have e0 : 2 * (t / 2) + 1 - 1 = 2 * (t / 2) + 0 := by cfomega
      rw [e0, phiLinPow_spread 2 (by decide) (t / 2) (t / 2) 0 (by decide), linear_center]
      rcases Nat.eq_zero_or_pos (t / 2) with hm | hm
      · rw [hm]
        decide
      · have g1 : 2 * (t / 2) + 0 ≥ 1 := by cfomega
        have g2 : 2 * (t / 2) + 0 ≥ 2 * 1 := by cfomega
        have e1 : 2 * (t / 2) + 0 - 1 = 2 * (t / 2 - 1) + 1 := by cfomega
        have e2 : 2 * (t / 2) + 0 - 2 * 1 = 2 * (t / 2 - 1) + 0 := by cfomega
        rw [e1, e2, phiLinPow_spread 2 (by decide) (t / 2) (t / 2 - 1) 1 (by decide),
          phiLinPow_spread 2 (by decide) (t / 2) (t / 2 - 1) 0 (by decide), ih (t / 2) (by cfomega) hm]
        have g3 : ¬ (2 * (t / 2) < 2) := by cfomega
        simp [g1, g2, g3]

/-! ## The center's update in ledger coordinates

Every cell is a coefficient of `q^t` XOR a ledger bit. The three cells the
center's update reads are, in the linear part, `a(t)`, `1`, `a(t)` with
`a = trailingParity`; so the self-referential equation of the orbit, read at
the center, is an update of ledger bits with a 2-automatic coefficient. -/

/-- Bit `j` of the ledger at time `t`. -/
def ledgerBit (t j : Nat) : Bool := (winWitt 0 t).testBit j

theorem rdiag_eq_linear_xor_ledger (j t : Nat) :
    rdiag j t = ((phiLinPow 1 t 1).testBit j ^^ ledgerBit t j) := by
  rw [← Rule30UOR.Interfaces.row_testBit, row_eq_linear_xor_ledger, Nat.testBit_xor,
    phiLinearPow_eq_phiLinPow]
  rfl

theorem cell_eq_rdiag (t j : Nat) (p : Int) (h : (t : Int) - j = p) : cell t p = rdiag j t := by
  rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Scale.cell_eq_kit]
  unfold Ruliology.CellularAutomata.Rule30Diagonals.R
  rw [h]

theorem cell_left_eq (t : Nat) : cell t (-1) = (trailingParity t ^^ ledgerBit t (t + 1)) := by
  rw [cell_eq_rdiag t (t + 1) (-1) (by push_cast; cfomega), rdiag_eq_linear_xor_ledger,
    linear_above_center]

theorem cell_right_eq (t : Nat) (ht : 1 ≤ t) :
    cell t 1 = (trailingParity t ^^ ledgerBit t (t - 1)) := by
  rw [cell_eq_rdiag t (t - 1) 1 (by push_cast [ht]; cfomega), rdiag_eq_linear_xor_ledger,
    linear_below_center t ht]

theorem center_eq_ledgerBit (t : Nat) : center t = !ledgerBit t t :=
  center_eq_not_ledgerDiagonal t

/-- The self-referential equation at the center, in ledger coordinates: for
`t ≥ 1`, `center (t+1) = rule (a t ⊕ ℓ(t, t+1)) (¬ ℓ(t, t)) (a t ⊕ ℓ(t, t−1))`
with `a` the trailing-ones parity and `ℓ` the ledger bits. -/
theorem center_succ_ledger (t : Nat) (ht : 1 ≤ t) :
    center (t + 1) = rule (trailingParity t ^^ ledgerBit t (t + 1)) (!ledgerBit t t)
      (trailingParity t ^^ ledgerBit t (t - 1)) := by
  rw [← cell_left_eq, ← center_eq_ledgerBit, ← cell_right_eq t ht]
  show cell (Nat.succ t) 0 = rule (cell t (-1)) (cell t 0) (cell t 1)
  rw [cell_succ]
  rfl

/-! ### Paper-facing forms (`bxor` for `xor`) -/

theorem rdiag_eq_linear_bxor_ledger (j t : Nat) :
    rdiag j t = bxor ((phiLinPow 1 t 1).testBit j) (ledgerBit t j) := by
  rw [Rule30UOR.Scale.bxor_eq]; exact rdiag_eq_linear_xor_ledger j t

theorem cell_left_eq_paper (t : Nat) : cell t (-1) = bxor (trailingParity t) (ledgerBit t (t + 1)) := by
  rw [Rule30UOR.Scale.bxor_eq]; exact cell_left_eq t

theorem cell_right_eq_paper (t : Nat) (ht : 1 ≤ t) :
    cell t 1 = bxor (trailingParity t) (ledgerBit t (t - 1)) := by
  rw [Rule30UOR.Scale.bxor_eq]; exact cell_right_eq t ht

/-- The center's update in ledger coordinates (paper form). -/
theorem center_succ_ledger_paper (t : Nat) (ht : 1 ≤ t) :
    center (t + 1) = rule (bxor (trailingParity t) (ledgerBit t (t + 1))) (!ledgerBit t t)
      (bxor (trailingParity t) (ledgerBit t (t - 1))) := by
  rw [Rule30UOR.Scale.bxor_eq, Rule30UOR.Scale.bxor_eq]; exact center_succ_ledger t ht

end Rule30UOR.Ledger
