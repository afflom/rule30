module
public import Rule30UOR.Band
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The left band of the bulk carries

Bit `2m − d` of `carry (row m)` is the carry on the *left* diagonal `d` of row `m`
(`ldiag d m = rdiag (2m − d) m`). The left diagonals `2..7` are explicit:
`ldiag 2 = false`, `ldiag 3 = ldiag 5 = ldiag 6 = [m odd]`, `ldiag 4 = true`,
`ldiag 7 = false`. So the bulk mask `interiorThree m` carries, for odd `m ≥ 5`, the
three left-edge events on bits `2m − 5, 2m − 4, 2m − 3`, and at `m = 3` the single
bulk bit `3` (bits `1, 2` of row `3` are the right-edge pair and the low event that
`interiorThree` has already removed). Splitting these off (`leftBandSource`) splits
the bulk ledger into the left band and `interiorEight`, the carries on the right
diagonals `≥ 3` and the left diagonals `≥ 8`. The left band's diagonal collapses to
an explicit 2-automatic background: for `t ≥ 6`,
`leftBandDiagonal t = ¬ timeParity t ⊕ trailingParity (t − 4) ⊕ trailingParity ((t − 4) / 2)`,
so `center t = trailingParity (t − 2) ⊕ ¬ timeParity t ⊕ trailingParity (t − 4) ⊕
trailingParity ((t − 4) / 2) ⊕ interiorEightDiagonal t`, and a center period is exactly a
period of the `interiorEight` gasket parity read against these rulers. -/

@[expose] public section

namespace Rule30UOR.LeftBand

open Rule30UOR.Core Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Band

/-! ## The left diagonals `2..7` in closed form -/

theorem ldiag_two_eq (t : Nat) (ht : 2 ≤ t) : ldiag 2 t = false := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  rw [show ldiag 2 (s + 2) = bxor (ldiag 0 (s + 1)) (ldiag 1 (s + 1) || ldiag 2 (s + 1)) from
      ldiag_step 0 (s + 1),
    show ldiag 0 (s + 1) = true from ldiag_zero s, show ldiag 1 (s + 1) = true from ldiag_one s]
  rfl

theorem ldiag_three_eq (t : Nat) (ht : 2 ≤ t) : ldiag 3 t = timeParity t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  clear ht
  unfold timeParity
  induction s with
  | zero => decide
  | succ s ih =>
    rw [show ldiag 3 (s + 1 + 2) = bxor (ldiag 1 (s + 2)) (ldiag 2 (s + 2) || ldiag 3 (s + 2)) from
        ldiag_step 1 (s + 2),
      show ldiag 1 (s + 2) = true from ldiag_one (s + 1), ldiag_two_eq (s + 2) (by cfomega), ih]
    rcases Nat.mod_two_eq_zero_or_one (s + 2) with h | h
    · rw [decide_eq_false (by cfomega : ¬ ((s + 2) % 2 = 1)),
        decide_eq_true (by cfomega : (s + 1 + 2) % 2 = 1)]
      rfl
    · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ ((s + 1 + 2) % 2 = 1))]
      rfl

theorem ldiag_four_eq (t : Nat) (ht : 2 ≤ t) : ldiag 4 t = true := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  clear ht
  induction s with
  | zero => decide
  | succ s ih =>
    rw [show ldiag 4 (s + 1 + 2) = bxor (ldiag 2 (s + 2)) (ldiag 3 (s + 2) || ldiag 4 (s + 2)) from
        ldiag_step 2 (s + 2),
      ldiag_two_eq (s + 2) (by cfomega), ih, Bool.or_true]
    rfl

theorem ldiag_five_eq (t : Nat) (ht : 3 ≤ t) : ldiag 5 t = timeParity t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by cfomega⟩
  rw [show ldiag 5 (s + 3) = bxor (ldiag 3 (s + 2)) (ldiag 4 (s + 2) || ldiag 5 (s + 2)) from
      ldiag_step 3 (s + 2),
    ldiag_four_eq (s + 2) (by cfomega), Bool.true_or, ldiag_three_eq (s + 2) (by cfomega)]
  unfold timeParity
  rcases Nat.mod_two_eq_zero_or_one (s + 2) with h | h
  · rw [decide_eq_false (by cfomega : ¬ ((s + 2) % 2 = 1)),
      decide_eq_true (by cfomega : (s + 3) % 2 = 1)]
    rfl
  · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ ((s + 3) % 2 = 1))]
    rfl

theorem ldiag_six_eq (t : Nat) (ht : 3 ≤ t) : ldiag 6 t = timeParity t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by cfomega⟩
  clear ht
  unfold timeParity
  induction s with
  | zero => decide
  | succ s ih =>
    rw [show ldiag 6 (s + 1 + 3) = bxor (ldiag 4 (s + 3)) (ldiag 5 (s + 3) || ldiag 6 (s + 3)) from
        ldiag_step 4 (s + 3),
      ldiag_four_eq (s + 3) (by cfomega), ih, ldiag_five_eq (s + 3) (by cfomega)]
    unfold timeParity
    rcases Nat.mod_two_eq_zero_or_one (s + 3) with h | h
    · rw [decide_eq_false (by cfomega : ¬ ((s + 3) % 2 = 1)),
        decide_eq_true (by cfomega : (s + 1 + 3) % 2 = 1)]
      rfl
    · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ ((s + 1 + 3) % 2 = 1))]
      rfl

theorem ldiag_five_eq_six (t : Nat) : ldiag 5 t = ldiag 6 t := by
  rcases Nat.lt_or_ge t 3 with h | h
  · rcases t with _ | _ | _ | t
    · decide
    · decide
    · decide
    · exact absurd h (by cfomega)
  · rw [ldiag_five_eq t h, ldiag_six_eq t h]

theorem ldiag_seven_eq (t : Nat) : ldiag 7 t = false := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show ldiag 7 (t + 1) = bxor (ldiag 5 t) (ldiag 6 t || ldiag 7 t) from ldiag_step 5 t, ih,
      Bool.or_false, ldiag_five_eq_six]
    cases ldiag 6 t <;> rfl

/-! ## The left-edge carry bits of a row -/

/-- The two-place shear `ldiag d m = rdiag (2m − d) m`, with the indices as hypotheses. -/
theorem rdiag_eq_ldiag (d s j m : Nat) (hj : j = d + 2 * s) (hm : m = d + s) : rdiag j m = ldiag d m := by
  subst hj hm
  exact (Rule30UOR.Interfaces.ldiag_eq_rdiag d s).symm

/-- Bits `2m − 5, 2m − 4, 2m − 3` of `carry (row m)` are all `[m odd]` for `m ≥ 6`. -/
theorem carry_row_testBit_band (u : Nat) :
    (carry (row (u + 6))).testBit (2 * u + 7) = timeParity (u + 6) ∧
    (carry (row (u + 6))).testBit (2 * u + 8) = timeParity (u + 6) ∧
    (carry (row (u + 6))).testBit (2 * u + 9) = timeParity (u + 6) := by
  have h7 : (carry (row (u + 6))).testBit (2 * u + 7) = (rdiag (2 * u + 7) (u + 6) && rdiag (2 * u + 6) (u + 6)) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ (u + 6) (2 * u + 6)
  have h8 : (carry (row (u + 6))).testBit (2 * u + 8) = (rdiag (2 * u + 8) (u + 6) && rdiag (2 * u + 7) (u + 6)) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ (u + 6) (2 * u + 7)
  have h9 : (carry (row (u + 6))).testBit (2 * u + 9) = (rdiag (2 * u + 9) (u + 6) && rdiag (2 * u + 8) (u + 6)) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ (u + 6) (2 * u + 8)
  rw [h7, h8, h9, rdiag_eq_ldiag 3 (u + 3) (2 * u + 9) (u + 6) (by cfomega) (by cfomega),
    rdiag_eq_ldiag 4 (u + 2) (2 * u + 8) (u + 6) (by cfomega) (by cfomega),
    rdiag_eq_ldiag 5 (u + 1) (2 * u + 7) (u + 6) (by cfomega) (by cfomega),
    rdiag_eq_ldiag 6 u (2 * u + 6) (u + 6) (by cfomega) (by cfomega),
    ldiag_three_eq _ (by cfomega), ldiag_four_eq _ (by cfomega), ldiag_five_eq _ (by cfomega),
    ldiag_six_eq _ (by cfomega)]
  cases timeParity (u + 6) <;> exact ⟨rfl, rfl, rfl⟩

/-- **Bits `2m − 6` and `2m − 7` of `carry (row m)` vanish for `m ≥ 4`** (`ldiag 7 = false`). -/
theorem carry_left_six_seven (m : Nat) (hm : 4 ≤ m) :
    (carry (row m)).testBit (2 * m - 6) = false ∧ (carry (row m)).testBit (2 * m - 7) = false := by
  rcases Nat.lt_or_ge m 8 with h | h
  · rcases Nat.lt_or_ge m 6 with h6 | h6
    · rcases Nat.lt_or_ge m 5 with h5 | h5
      · have : m = 4 := by cfomega
        subst this; decide
      · have : m = 5 := by cfomega
        subst this; decide
    · rcases Nat.lt_or_ge m 7 with h7 | h7
      · have : m = 6 := by cfomega
        subst this; decide
      · have : m = 7 := by cfomega
        subst this; decide
  · obtain ⟨u, rfl⟩ : ∃ u, m = u + 8 := ⟨m - 8, by cfomega⟩
    rw [show 2 * (u + 8) - 6 = 2 * u + 10 by cfomega, show 2 * (u + 8) - 7 = 2 * u + 9 by cfomega]
    have h10 : (carry (row (u + 8))).testBit (2 * u + 10) = (rdiag (2 * u + 10) (u + 8) && rdiag (2 * u + 9) (u + 8)) :=
      Rule30UOR.Interfaces.carry_row_testBit_succ (u + 8) (2 * u + 9)
    have h9 : (carry (row (u + 8))).testBit (2 * u + 9) = (rdiag (2 * u + 9) (u + 8) && rdiag (2 * u + 8) (u + 8)) :=
      Rule30UOR.Interfaces.carry_row_testBit_succ (u + 8) (2 * u + 8)
    rw [h10, h9, rdiag_eq_ldiag 7 (u + 1) (2 * u + 9) (u + 8) (by cfomega) (by cfomega), ldiag_seven_eq,
      Bool.and_false, Bool.false_and]
    exact ⟨rfl, rfl⟩

/-! ## The left band of the bulk mask -/

/-- The left-band events of row `m`: the bulk bit `3` of row `3`, and for odd `m ≥ 5` the three
left-edge carries on bits `2m − 5, 2m − 4, 2m − 3` (left diagonals `5, 4, 3`). -/
def leftBandSource (m : Nat) : Nat :=
  if m = 3 then 8 else if 5 ≤ m ∧ m % 2 = 1 then 7 <<< (2 * m - 5) else 0

theorem leftBandSource_three : leftBandSource 3 = 8 := by decide

theorem leftBandSource_of_odd (m : Nat) (hm : 5 ≤ m) (h : m % 2 = 1) :
    leftBandSource m = 7 <<< (2 * m - 5) := by
  unfold leftBandSource
  rw [if_neg (by cfomega), if_pos ⟨hm, h⟩]

theorem leftBandSource_of_even (m : Nat) (h : m % 2 = 0) : leftBandSource m = 0 := by
  unfold leftBandSource
  rw [if_neg (by cfomega), if_neg (fun hc => by cfomega)]

theorem testBit_small (x i : Nat) (hx : x < 8) (hi : 3 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by decide : 0 < 2) hi : 2 ^ 3 ≤ 2 ^ i))

theorem lowSource_lt_eight (m : Nat) : lowSource m < 8 := by
  unfold lowSource
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [if_pos h]; decide
  · rw [if_neg (by cfomega)]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · rw [if_neg (fun hc => by cfomega)]; decide
    · rcases Nat.mod_two_eq_zero_or_one m with hp | hp
      · rw [if_neg (fun hc => by cfomega)]; decide
      · rw [if_pos ⟨hm, hp⟩]; decide

/-- Between bit `3` and the left edge, the edge and low sources are empty. -/
theorem edge_low_testBit (m i : Nat) (h3 : 3 ≤ i) (hm : i < 2 * m) :
    (edgeSource m ^^^ lowSource m).testBit i = false := by
  unfold edgeSource
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, decide_eq_false (by cfomega : ¬ (i ≥ 2 * m)),
    Bool.false_and, testBit_small (lowSource m) i (lowSource_lt_eight m) h3]
  have h2 : (if rdiag 1 m then 2 else 0).testBit i = false := by
    cases rdiag 1 m
    · exact Nat.zero_testBit i
    · exact testBit_small 2 i (by decide) h3
  rw [h2]
  rfl

/-- Between bit `3` and the left edge, the bulk mask is the carry itself. -/
theorem interiorThree_testBit_mid (m i : Nat) (h3 : 3 ≤ i) (hm : i < 2 * m) :
    (interiorThree m).testBit i = (carry (row m)).testBit i := by
  unfold interiorThree interior
  rw [Nat.xor_assoc, Nat.testBit_xor, edge_low_testBit m i h3 hm]
  cases (carry (row m)).testBit i <;> rfl

theorem testBit_seven_shiftLeft (j i : Nat) : (7 <<< j).testBit i = decide (j ≤ i ∧ i < j + 3) := by
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i j with h | h
  · rw [decide_eq_false (by cfomega : ¬ (i ≥ j)), decide_eq_false (fun hc => by cfomega)]
    rfl
  · rw [decide_eq_true (h : i ≥ j)]
    obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by cfomega⟩
    rw [Nat.add_sub_cancel_left]
    rcases d with _ | _ | _ | d
    · rw [decide_eq_true ⟨by cfomega, by cfomega⟩]; decide
    · rw [decide_eq_true ⟨by cfomega, by cfomega⟩]; decide
    · rw [decide_eq_true ⟨by cfomega, by cfomega⟩]; decide
    · rw [testBit_small 7 _ (by decide) (by cfomega), decide_eq_false (fun hc => by cfomega), Bool.and_false]

theorem and_mask_eq (x j i : Nat) (b : Bool) (h0 : x.testBit j = b) (h1 : x.testBit (j + 1) = b)
    (h2 : x.testBit (j + 2) = b) :
    (x.testBit i && decide (j ≤ i ∧ i < j + 3)) = (b && decide (j ≤ i ∧ i < j + 3)) := by
  rcases Nat.lt_or_ge i j with h | h
  · rw [decide_eq_false (fun hc => by cfomega), Bool.and_false, Bool.and_false]
  · rcases Nat.lt_or_ge i (j + 3) with h' | h'
    · rcases Nat.lt_or_ge i (j + 1) with g | g
      · have : i = j := by cfomega
        subst this; rw [h0]
      · rcases Nat.lt_or_ge i (j + 2) with g' | g'
        · have : i = j + 1 := by cfomega
          subst this; rw [h1]
        · have : i = j + 2 := by cfomega
          subst this; rw [h2]
    · rw [decide_eq_false (fun hc => by cfomega), Bool.and_false, Bool.and_false]

/-- **The left band of the bulk mask**: the three band bits of `interiorThree m` are exactly
`leftBandSource m` (for `m ≥ 3`; at `m = 3` the band is the single bulk bit `3`). -/
theorem interiorThree_left_band (m : Nat) (hm : 3 ≤ m) :
    interiorThree m &&& (7 <<< (2 * m - 5)) = leftBandSource m := by
  rcases Nat.lt_or_ge m 6 with h | h
  · rcases Nat.lt_or_ge m 4 with h4 | h4
    · have : m = 3 := by cfomega
      subst this; decide
    · rcases Nat.lt_or_ge m 5 with h5 | h5
      · have : m = 4 := by cfomega
        subst this; decide
      · have : m = 5 := by cfomega
        subst this; decide
  · obtain ⟨u, rfl⟩ : ∃ u, m = u + 6 := ⟨m - 6, by cfomega⟩
    obtain ⟨c7, c8, c9⟩ := carry_row_testBit_band u
    have b7 : (interiorThree (u + 6)).testBit (2 * u + 7) = timeParity (u + 6) := by
      rw [interiorThree_testBit_mid _ _ (by cfomega) (by cfomega), c7]
    have b8 : (interiorThree (u + 6)).testBit (2 * u + 8) = timeParity (u + 6) := by
      rw [interiorThree_testBit_mid _ _ (by cfomega) (by cfomega), c8]
    have b9 : (interiorThree (u + 6)).testBit (2 * u + 9) = timeParity (u + 6) := by
      rw [interiorThree_testBit_mid _ _ (by cfomega) (by cfomega), c9]
    rw [show 2 * (u + 6) - 5 = 2 * u + 7 by cfomega]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, testBit_seven_shiftLeft, and_mask_eq _ _ i _ b7 b8 b9]
    unfold timeParity
    rcases Nat.mod_two_eq_zero_or_one (u + 6) with hp | hp
    · rw [leftBandSource_of_even _ hp, Nat.zero_testBit, decide_eq_false (by cfomega : ¬ ((u + 6) % 2 = 1))]
      rfl
    · rw [leftBandSource_of_odd _ (by cfomega) hp, testBit_seven_shiftLeft, decide_eq_true hp]
      rfl

/-! ## The split of the bulk ledger -/

/-- The bulk carries with the left band removed: the carries on the right diagonals `≥ 3`
and the left diagonals `≥ 8`. -/
def interiorEight (m : Nat) : Nat := interiorThree m ^^^ leftBandSource m

theorem interiorThree_split_eight (m : Nat) : interiorThree m = leftBandSource m ^^^ interiorEight m := by
  unfold interiorEight
  rw [Nat.xor_comm (interiorThree m) (leftBandSource m)]
  exact (Rule30UOR.Ledger.xor_xor_self _ _).symm

/-- The ledger sourced by the left band only. -/
def leftBandLedger : Nat → Nat
  | 0 => 0
  | t + 1 => phiLinear (leftBandLedger t) ^^^ (leftBandSource t <<< 1)

/-- The ledger sourced by the carries on right diagonals `≥ 3` and left diagonals `≥ 8`. -/
def interiorEightLedger : Nat → Nat
  | 0 => 0
  | t + 1 => phiLinear (interiorEightLedger t) ^^^ (interiorEight t <<< 1)

/-- **The bulk ledger splits** into the left band and the rest. -/
theorem interiorThreeLedger_split_eight : ∀ t, interiorThreeLedger t = leftBandLedger t ^^^ interiorEightLedger t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (interiorThreeLedger t) ^^^ (interiorThree t <<< 1) =
      (phiLinear (leftBandLedger t) ^^^ (leftBandSource t <<< 1)) ^^^
        (phiLinear (interiorEightLedger t) ^^^ (interiorEight t <<< 1))
    rw [ih, phiLinear_xor, interiorThree_split_eight, Nat.shiftLeft_xor_distrib]
    simp only [Nat.xor_assoc, Nat.xor_comm, Rule30UOR.Ledger.xor_left_comm]

/-- The diagonal of the left-band ledger. -/
def leftBandDiagonal (t : Nat) : Bool := (leftBandLedger t).testBit t

/-- The diagonal of the ledger of the carries on right diagonals `≥ 3` and left diagonals `≥ 8`. -/
def interiorEightDiagonal (t : Nat) : Bool := (interiorEightLedger t).testBit t

theorem interiorThreeDiagonal_split_eight (t : Nat) :
    interiorThreeDiagonal t = bxor (leftBandDiagonal t) (interiorEightDiagonal t) := by
  unfold interiorThreeDiagonal leftBandDiagonal interiorEightDiagonal
  rw [interiorThreeLedger_split_eight, Nat.testBit_xor, Rule30UOR.Scale.bxor_eq]

/-! ## The left-band diagonal as a fold of trinomial parities -/

def leftLedgerSum (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => leftLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (leftBandSource n <<< 1)

theorem phiLinear_leftLedgerSum (t : Nat) : ∀ n, n ≤ t →
    phiLinear (leftLedgerSum t n) = leftLedgerSum (t + 1) n := by
  intro n
  induction n with
  | zero => intro _; exact phiLinear_zero
  | succ n ih =>
    intro hn
    show phiLinear (leftLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (leftBandSource n <<< 1)) =
      leftLedgerSum (t + 1) n ^^^ phiLinearPow (t + 1 - 1 - n) (leftBandSource n <<< 1)
    rw [phiLinear_xor, ih (by cfomega), show t + 1 - 1 - n = (t - 1 - n) + 1 by cfomega, phiLinearPow_step]

theorem leftBandLedger_eq_sum : ∀ t, leftBandLedger t = leftLedgerSum t t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (leftBandLedger t) ^^^ (leftBandSource t <<< 1) =
      leftLedgerSum (t + 1) t ^^^ phiLinearPow (t + 1 - 1 - t) (leftBandSource t <<< 1)
    rw [ih, phiLinear_leftLedgerSum t t (Nat.le_refl t), show t + 1 - 1 - t = 0 by cfomega]
    rfl

/-- The contribution of row `m`'s left-band events to the center at time `t`. -/
def leftTerm (t m : Nat) : Bool := (phiLinearPow (t - 1 - m) (leftBandSource m <<< 1)).testBit t

theorem testBit_leftLedgerSum (t : Nat) : ∀ n, (leftLedgerSum t n).testBit t = xorBelow (leftTerm t) n := by
  intro n
  induction n with
  | zero => show (0 : Nat).testBit t = false; simp
  | succ n ih =>
    show (leftLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (leftBandSource n <<< 1)).testBit t =
      bxor (xorBelow (leftTerm t) n) (leftTerm t n)
    rw [Nat.testBit_xor, ih, Rule30UOR.Scale.bxor_eq]
    rfl

theorem leftBandDiagonal_eq_xorBelow (t : Nat) : leftBandDiagonal t = xorBelow (leftTerm t) t := by
  unfold leftBandDiagonal
  rw [leftBandLedger_eq_sum, testBit_leftLedgerSum]

theorem seven_shiftLeft (j : Nat) : 7 <<< j = (1 <<< j) ^^^ ((1 <<< (j + 1)) ^^^ (1 <<< (j + 2))) := by
  rw [show (7 : Nat) = 1 ^^^ (2 ^^^ 4) by decide, Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib,
    show (2 : Nat) <<< j = 1 <<< (j + 1) by rw [Nat.add_comm, Nat.shiftLeft_add]; rfl,
    show (4 : Nat) <<< j = 1 <<< (j + 2) by rw [Nat.add_comm, Nat.shiftLeft_add]; rfl]

theorem leftTerm_three (t : Nat) :
    leftTerm t 3 = (if 4 ≤ t then trinomialParity (t - 1 - 3) (t - 4) else false) := by
  unfold leftTerm
  rw [leftBandSource_three, show (8 : Nat) <<< 1 = 1 <<< 4 from rfl, phiLinearPow_shiftLeft,
    testBit_phiLinearPow_shift]

theorem leftTerm_of_odd (t m : Nat) (hm : 5 ≤ m) (h : m % 2 = 1) :
    leftTerm t m = bxor (if 2 * m - 4 ≤ t then trinomialParity (t - 1 - m) (t - (2 * m - 4)) else false)
      (bxor (if 2 * m - 3 ≤ t then trinomialParity (t - 1 - m) (t - (2 * m - 3)) else false)
        (if 2 * m - 2 ≤ t then trinomialParity (t - 1 - m) (t - (2 * m - 2)) else false)) := by
  unfold leftTerm
  rw [leftBandSource_of_odd m hm h, ← Nat.shiftLeft_add, show 2 * m - 5 + 1 = 2 * m - 4 by cfomega,
    seven_shiftLeft, show 2 * m - 4 + 1 = 2 * m - 3 by cfomega, show 2 * m - 4 + 2 = 2 * m - 2 by cfomega,
    phiLinearPow_xor, phiLinearPow_xor, Nat.testBit_xor, Nat.testBit_xor, phiLinearPow_shiftLeft,
    phiLinearPow_shiftLeft, phiLinearPow_shiftLeft, testBit_phiLinearPow_shift, testBit_phiLinearPow_shift,
    testBit_phiLinearPow_shift, Rule30UOR.Scale.bxor_eq, Rule30UOR.Scale.bxor_eq]

theorem leftTerm_eq_false (t m : Nat) (h : leftBandSource m = 0) : leftTerm t m = false := by
  unfold leftTerm
  rw [h, show (0 : Nat) <<< 1 = 0 from rfl, phiLinearPow_zero, Nat.zero_testBit]

/-- A guarded mirrored coefficient is the unguarded coefficient: palindromy inside the degree
bound, and `0` outside it. -/
theorem guard_mirror (n d a b : Nat) (h1 : a ≤ b ↔ d ≤ 2 * n) (h2 : d ≤ 2 * n → b - a = 2 * n - d) :
    (if a ≤ b then trinomialParity n (b - a) else false) = trinomialParity n d := by
  rcases Nat.lt_or_ge (2 * n) d with h | h
  · rw [if_neg (fun hc => by have := h1.1 hc; cfomega)]
    exact (trinomialParity_eq_false_of_gt n d h).symm
  · rw [if_pos (h1.2 h), h2 h]
    exact (trinomialParity_palindrome n d h).symm

/-! ## Parity classes of a column of the trinomial triangle -/

/-- The column `N` of the trinomial triangle restricted to the rows of the parity of `p`. -/
def parityColumn (p N : Nat) : Bool :=
  xorBelow (fun n => if n % 2 = p % 2 then trinomialParity n N else false) (N + 1)

theorem parityColumn_self (N : Nat) : parityColumn N N = columnParity (N / 2) := sameParityColumn_eq N

theorem parityColumn_add_two (p N : Nat) : parityColumn (p + 2) N = parityColumn p N := by
  unfold parityColumn
  rw [show (p + 2) % 2 = p % 2 by cfomega]

theorem columnParity_split (N : Nat) : columnParity N = bxor (parityColumn N N) (parityColumn (N + 1) N) := by
  unfold columnParity parityColumn
  rw [← xorBelow_bxor]
  apply xorBelow_congr
  intro n _
  show trinomialParity n N = bxor (if n % 2 = N % 2 then trinomialParity n N else false)
    (if n % 2 = (N + 1) % 2 then trinomialParity n N else false)
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> rcases Nat.mod_two_eq_zero_or_one N with hN | hN
  · rw [if_pos (by cfomega : n % 2 = N % 2), if_neg (by cfomega : ¬ (n % 2 = (N + 1) % 2))]
    cases trinomialParity n N <;> rfl
  · rw [if_neg (by cfomega : ¬ (n % 2 = N % 2)), if_pos (by cfomega : n % 2 = (N + 1) % 2)]
    cases trinomialParity n N <;> rfl
  · rw [if_neg (by cfomega : ¬ (n % 2 = N % 2)), if_pos (by cfomega : n % 2 = (N + 1) % 2)]
    cases trinomialParity n N <;> rfl
  · rw [if_pos (by cfomega : n % 2 = N % 2), if_neg (by cfomega : ¬ (n % 2 = (N + 1) % 2))]
    cases trinomialParity n N <;> rfl

/-! ## The left-band diagonal in closed form -/

/-- For `t = s + 6` the left-band diagonal is a sum of four column parities: the bulk bit of
row `3` gives the central coefficient `1`, and the three band bits of the odd rows `m ≥ 5` give,
by palindromy, the rows `n ≡ s (mod 2)` of the columns `s + 2, s + 1, s`. -/
theorem leftBandDiagonal_six (s : Nat) :
    leftBandDiagonal (s + 6) = bxor (columnParity ((s + 2) / 2))
      (bxor (columnParity (s + 1)) (bxor (columnParity ((s + 1) / 2)) (columnParity (s / 2)))) := by
  rw [leftBandDiagonal_eq_xorBelow, xorBelow_rev]
  have hmain : xorBelow (fun m => leftTerm (s + 6) (s + 6 - 1 - m)) (s + 1) =
      bxor (bxor (xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 2) else false) (s + 1))
        (xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 1) else false) (s + 1)))
        (xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n s else false) (s + 1)) := by
    rw [← xorBelow_bxor, ← xorBelow_bxor]
    apply xorBelow_congr
    intro n hn
    show leftTerm (s + 6) (s + 6 - 1 - n) =
      bxor (bxor (if n % 2 = s % 2 then trinomialParity n (s + 2) else false)
        (if n % 2 = s % 2 then trinomialParity n (s + 1) else false))
        (if n % 2 = s % 2 then trinomialParity n s else false)
    rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2 <;> rcases Nat.mod_two_eq_zero_or_one s with hs2 | hs2
    · have hp : n % 2 = s % 2 := by cfomega
      rw [if_pos hp, if_pos hp, if_pos hp, leftTerm_of_odd _ _ (by cfomega) (by cfomega),
        show s + 6 - 1 - (s + 6 - 1 - n) = n by cfomega,
        guard_mirror n s (2 * (s + 6 - 1 - n) - 4) (s + 6) ⟨fun h => by cfomega, fun h => by cfomega⟩
          (fun h => by cfomega),
        guard_mirror n (s + 1) (2 * (s + 6 - 1 - n) - 3) (s + 6) ⟨fun h => by cfomega, fun h => by cfomega⟩
          (fun h => by cfomega),
        guard_mirror n (s + 2) (2 * (s + 6 - 1 - n) - 2) (s + 6) ⟨fun h => by cfomega, fun h => by cfomega⟩
          (fun h => by cfomega)]
      cases trinomialParity n s <;> cases trinomialParity n (s + 1) <;> cases trinomialParity n (s + 2) <;> rfl
    · have hp : ¬ (n % 2 = s % 2) := by cfomega
      rw [if_neg hp, if_neg hp, if_neg hp, leftTerm_eq_false _ _ (leftBandSource_of_even _ (by cfomega))]
      rfl
    · have hp : ¬ (n % 2 = s % 2) := by cfomega
      rw [if_neg hp, if_neg hp, if_neg hp, leftTerm_eq_false _ _ (leftBandSource_of_even _ (by cfomega))]
      rfl
    · have hp : n % 2 = s % 2 := by cfomega
      rw [if_pos hp, if_pos hp, if_pos hp, leftTerm_of_odd _ _ (by cfomega) (by cfomega),
        show s + 6 - 1 - (s + 6 - 1 - n) = n by cfomega,
        guard_mirror n s (2 * (s + 6 - 1 - n) - 4) (s + 6) ⟨fun h => by cfomega, fun h => by cfomega⟩
          (fun h => by cfomega),
        guard_mirror n (s + 1) (2 * (s + 6 - 1 - n) - 3) (s + 6) ⟨fun h => by cfomega, fun h => by cfomega⟩
          (fun h => by cfomega),
        guard_mirror n (s + 2) (2 * (s + 6 - 1 - n) - 2) (s + 6) ⟨fun h => by cfomega, fun h => by cfomega⟩
          (fun h => by cfomega)]
      cases trinomialParity n s <;> cases trinomialParity n (s + 1) <;> cases trinomialParity n (s + 2) <;> rfl
  have hA2 : xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 2) else false) (s + 1) =
      bxor (columnParity ((s + 2) / 2)) true := by
    have h := parityColumn_self (s + 2)
    rw [parityColumn_add_two s (s + 2)] at h
    unfold parityColumn at h
    rw [show xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 2) else false) (s + 2 + 1) =
        bxor (bxor (xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 2) else false) (s + 1))
          (if (s + 1) % 2 = s % 2 then trinomialParity (s + 1) (s + 2) else false))
          (if (s + 2) % 2 = s % 2 then trinomialParity (s + 2) (s + 2) else false) from rfl,
      if_neg (by cfomega : ¬ ((s + 1) % 2 = s % 2)), if_pos (by cfomega : (s + 2) % 2 = s % 2),
      trinomialParity_central] at h
    rw [← h]
    cases xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 2) else false) (s + 1) <;> rfl
  have hA1 : xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 1) else false) (s + 1) =
      bxor (columnParity (s + 1)) (columnParity ((s + 1) / 2)) := by
    have h := columnParity_split (s + 1)
    rw [parityColumn_self, show s + 1 + 1 = s + 2 from rfl, parityColumn_add_two] at h
    unfold parityColumn at h
    rw [show xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 1) else false) (s + 1 + 1) =
        bxor (xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 1) else false) (s + 1))
          (if (s + 1) % 2 = s % 2 then trinomialParity (s + 1) (s + 1) else false) from rfl,
      if_neg (by cfomega : ¬ ((s + 1) % 2 = s % 2))] at h
    rw [h]
    cases columnParity ((s + 1) / 2) <;>
      cases xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n (s + 1) else false) (s + 1) <;> rfl
  have hA0 : xorBelow (fun n => if n % 2 = s % 2 then trinomialParity n s else false) (s + 1) =
      columnParity (s / 2) := sameParityColumn_eq s
  show bxor (bxor (bxor (bxor (bxor (xorBelow (fun m => leftTerm (s + 6) (s + 6 - 1 - m)) (s + 1))
    (leftTerm (s + 6) (s + 6 - 1 - (s + 1)))) (leftTerm (s + 6) (s + 6 - 1 - (s + 2))))
    (leftTerm (s + 6) (s + 6 - 1 - (s + 3)))) (leftTerm (s + 6) (s + 6 - 1 - (s + 4))))
    (leftTerm (s + 6) (s + 6 - 1 - (s + 5))) = _
  rw [hmain, hA2, hA1, hA0, show s + 6 - 1 - (s + 1) = 4 by cfomega, show s + 6 - 1 - (s + 2) = 3 by cfomega,
    show s + 6 - 1 - (s + 3) = 2 by cfomega, show s + 6 - 1 - (s + 4) = 1 by cfomega,
    show s + 6 - 1 - (s + 5) = 0 by cfomega, leftTerm_eq_false _ 4 (by decide), leftTerm_eq_false _ 2 (by decide),
    leftTerm_eq_false _ 1 (by decide), leftTerm_eq_false _ 0 (by decide), leftTerm_three,
    if_pos (by cfomega : 4 ≤ s + 6), show s + 6 - 1 - 3 = s + 2 by cfomega, show s + 6 - 4 = s + 2 by cfomega,
    trinomialParity_central]
  cases columnParity ((s + 2) / 2) <;> cases columnParity (s + 1) <;> cases columnParity ((s + 1) / 2) <;>
    cases columnParity (s / 2) <;> rfl

/-- **The left band collapses to the time parity and two period-doubling rulers.** -/
theorem leftBandDiagonal_eq (t : Nat) (ht : 6 ≤ t) :
    leftBandDiagonal t = bxor (!(timeParity t)) (bxor (trailingParity (t - 4)) (trailingParity ((t - 4) / 2))) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 6 := ⟨t - 6, by cfomega⟩
  rw [leftBandDiagonal_six, show s + 6 - 4 = s + 2 by cfomega]
  unfold timeParity
  rcases Nat.mod_two_eq_zero_or_one s with hs | hs
  · obtain ⟨e, rfl⟩ : ∃ e, s = 2 * e := ⟨s / 2, by cfomega⟩
    rw [decide_eq_false (by cfomega : ¬ ((2 * e + 6) % 2 = 1)), show (2 * e + 2) / 2 = e + 1 by cfomega,
      show (2 * e + 1) / 2 = e by cfomega, show 2 * e / 2 = e by cfomega, columnParity_odd,
      show 2 * e + 2 = 2 * (e + 1) by cfomega, trailingParity_even]
    have ht : trailingParity (e + 1) = !(bxor (columnParity (e + 1)) (columnParity e)) := by
      rw [columnParity_succ_bxor e]
      cases trailingParity (e + 1) <;> rfl
    rw [ht]
    cases columnParity (e + 1) <;> cases columnParity e <;> rfl
  · obtain ⟨e, rfl⟩ : ∃ e, s = 2 * e + 1 := ⟨s / 2, by cfomega⟩
    rw [decide_eq_true (by cfomega : (2 * e + 1 + 6) % 2 = 1), show (2 * e + 1 + 2) / 2 = e + 1 by cfomega,
      show 2 * e + 1 + 2 = 2 * (e + 1) + 1 by cfomega, trailingParity_odd,
      show (2 * e + 1 + 1) / 2 = e + 1 by cfomega, show 2 * e + 1 + 1 = 2 * e + 2 from rfl,
      columnParity_even_succ, show (2 * e + 1) / 2 = e by cfomega]
    cases columnParity (e + 1) <;> cases columnParity e <;> cases trailingParity (e + 1) <;> rfl

/-! ## The center against the rulers -/

/-- **The center is the two period-doubling rulers, the time parity, and the gasket parity of
the carries on right diagonals `≥ 3` and left diagonals `≥ 8`.** -/
theorem center_eq_left_band (t : Nat) (ht : 6 ≤ t) :
    center t = bxor (trailingParity (t - 2)) (bxor (bxor (!(timeParity t))
      (bxor (trailingParity (t - 4)) (trailingParity ((t - 4) / 2)))) (interiorEightDiagonal t)) := by
  rw [center_eq_trailingParity_bxor_three t (by cfomega), interiorThreeDiagonal_split_eight,
    leftBandDiagonal_eq t ht]

/-- The explicit background a periodic center must reproduce: the trailing-ones rulers at
lags `2` and `4`, the ruler one scale up, and the time parity. -/
def rulerBackground (t : Nat) : Bool :=
  bxor (trailingParity (t - 2)) (bxor (!(timeParity t)) (bxor (trailingParity (t - 4)) (trailingParity ((t - 4) / 2))))

theorem center_eq_rulerBackground_bxor_eight (t : Nat) (ht : 6 ≤ t) :
    center t = bxor (rulerBackground t) (interiorEightDiagonal t) := by
  rw [center_eq_left_band t ht]
  unfold rulerBackground
  cases trailingParity (t - 2) <;> cases timeParity t <;> cases trailingParity (t - 4) <;>
    cases trailingParity ((t - 4) / 2) <;> cases interiorEightDiagonal t <;> rfl

/-- A center period `P` from `T`, in the carries on right diagonals `≥ 3` and left diagonals `≥ 8`:
their lag-`P` difference is the lag-`P` difference of the rulers. -/
def EightAgainstRulers (T P : Nat) : Prop :=
  ∀ t, T ≤ t → bxor (interiorEightDiagonal (t + P)) (interiorEightDiagonal t) =
    bxor (rulerBackground (t + P)) (rulerBackground t)

theorem centerPeriodic_iff_eightAgainstRulers (T P : Nat) (hT : 6 ≤ T) :
    Rule30UOR.Scale.CenterPeriodic T P ↔ EightAgainstRulers T P := by
  unfold Rule30UOR.Scale.CenterPeriodic EightAgainstRulers
  constructor
  · intro h t ht
    have hc := h t ht
    rw [center_eq_rulerBackground_bxor_eight (t + P) (by cfomega),
      center_eq_rulerBackground_bxor_eight t (by cfomega)] at hc
    exact bxor_aux_period _ _ _ _ hc
  · intro h t ht
    rw [center_eq_rulerBackground_bxor_eight (t + P) (by cfomega),
      center_eq_rulerBackground_bxor_eight t (by cfomega)]
    exact bxor_aux_period' _ _ _ _ (h t ht)

/-- The `interiorEight` gasket parity never repeats against the rulers. -/
def EightAperiodic : Prop := ∀ T P, 0 < P → ¬ EightAgainstRulers (T + 6) P

/-- **Problem 1 is `EightAperiodic`.** -/
theorem problem1_iff_eightAperiodic : Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ EightAperiodic := by
  rw [Rule30UOR.Scale.problem1_iff]
  constructor
  · intro h T P hP h8
    exact h (T + 6) P hP ((centerPeriodic_iff_eightAgainstRulers (T + 6) P (by cfomega)).2 h8)
  · intro h T P hP hc
    apply h T P hP
    apply (centerPeriodic_iff_eightAgainstRulers (T + 6) P (by cfomega)).1
    intro t ht
    exact hc t (by cfomega)

theorem problem1_of_eightAperiodic (h : EightAperiodic) : Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff_eightAperiodic.2 h

/-! ## The second coefficient beside the center -/

/-- The coefficient two places below the center of `q^(n+2)` is the trailing-ones parity of
`(n + 2) / 2` (companion of `linear_below_center`). -/
theorem trinomialParity_below_two (n : Nat) : trinomialParity (n + 2) n = trailingParity ((n + 2) / 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by cfomega⟩
    rw [show 2 * k + 2 = 2 * (k + 1) by cfomega, show 2 * k = 2 * (k + 1 - 1) by cfomega,
      trinomialParity_even_even, show 2 * (k + 1) / 2 = k + 1 by cfomega,
      ← testBit_phiLinPow_eq_trinomialParity, linear_below_center (k + 1) (by cfomega)]
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by cfomega⟩
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by cfomega, show 2 * k + 1 = 2 * (k + 1 - 1) + 1 by cfomega,
      trinomialParity_odd_odd, show (2 * (k + 1) + 1) / 2 = k + 1 by cfomega,
      ← testBit_phiLinPow_eq_trinomialParity, linear_below_center (k + 1) (by cfomega)]

end Rule30UOR.LeftBand
