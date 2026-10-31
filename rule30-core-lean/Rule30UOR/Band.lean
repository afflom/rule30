module
public import Rule30UOR.EdgeParity
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The low band of the interior carries is the trailing-ones parity

The interior mask `interior m` still carries three explicit low events: bit `0`
of `interior 0` (the seed row) and bit `2` of `interior m` for odd `m ≥ 3`
(the pair on right diagonals `1, 2`, since `rdiag 2 m = [m odd]`). Splitting
them off (`lowSource`) splits the interior ledger into a low band and the
bulk carries on the right diagonals `j ≥ 3` (`interiorThree`). The low band's
diagonal collapses, through the column parities of the trinomial triangle, to
the trailing-ones parity: `timeParity t ⊕ lowDiagonal t = ¬ trailingParity (t − 2)`.
So `center t = trailingParity (t − 2) ⊕ interiorThreeDiagonal t` for `t ≥ 2`,
and a center period is exactly a period of the bulk gasket parity read against
the trailing-ones parity. -/

@[expose] public section

namespace Rule30UOR.Band

open Rule30UOR.Core Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity

/-! ## The right diagonal `2` alternates -/

theorem rdiag_zero_eq (t : Nat) : rdiag 0 t = true := by
  cases t with
  | zero => rfl
  | succ s => exact rdiag_zero s

theorem rdiag_two_succ (s : Nat) : rdiag 2 (s + 1) = !(rdiag 2 s) := by
  rw [show rdiag 2 (s + 1) = bxor (rdiag 2 s) (rdiag 1 s || rdiag 0 s) from rdiag_step 0 s, rdiag_zero_eq,
    Bool.or_true]
  cases rdiag 2 s <;> rfl

/-- `rdiag 2 m = [m odd]`. -/
theorem rdiag_two_eq_parity : ∀ m, rdiag 2 m = decide (m % 2 = 1) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rdiag_two_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [h, show (m + 1) % 2 = 1 by cfomega]; rfl
    · rw [h, show (m + 1) % 2 = 0 by cfomega]; rfl

/-! ## The three low bits of the interior mask -/

/-- The three explicit low carry events left in `interior`: bit `0` of `interior 0`
(the seed row) and bit `2` of `interior m` for odd `m ≥ 3` (the diagonal-`2` pair). -/
def lowSource (m : Nat) : Nat := if m = 0 then 1 else if 2 ≤ m ∧ m % 2 = 1 then 4 else 0

theorem lowSource_zero : lowSource 0 = 1 := by decide

theorem lowSource_one : lowSource 1 = 0 := by decide

theorem lowSource_of_even (m : Nat) (hm : 1 ≤ m) (h : m % 2 = 0) : lowSource m = 0 := by
  unfold lowSource
  rw [if_neg (by cfomega), if_neg (fun hc => by cfomega)]

theorem lowSource_of_odd (m : Nat) (hm : 2 ≤ m) (h : m % 2 = 1) : lowSource m = 4 := by
  unfold lowSource
  rw [if_neg (by cfomega), if_pos ⟨hm, h⟩]

theorem interior_testBit_zero (m : Nat) : (interior m).testBit 0 = decide (m = 0) := by
  unfold interior edgeSource
  rw [Nat.testBit_xor, Nat.testBit_xor]
  have hc : (carry (row m)).testBit 0 = false := by
    show ((row m) &&& ((row m) <<< 1)).testBit 0 = false
    rw [Nat.testBit_and, Nat.testBit_shiftLeft]
    simp
  have hr : (if rdiag 1 m then 2 else 0).testBit 0 = false := by
    cases rdiag 1 m <;> rfl
  rw [hc, hr, Nat.testBit_shiftLeft]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; decide
  · rw [decide_eq_false (by cfomega : ¬ (0 ≥ 2 * m)), decide_eq_false (by cfomega : ¬ (m = 0))]; rfl

theorem interior_testBit_one (m : Nat) : (interior m).testBit 1 = false := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; decide
  · exact interior_testBit_right_pair m h

/-- Bit `2` of `interior m` is the diagonal-`2` pair, present exactly for odd `m ≥ 3`. -/
theorem interior_testBit_two (m : Nat) : (interior m).testBit 2 = decide (2 ≤ m ∧ m % 2 = 1) := by
  unfold interior edgeSource
  rw [Nat.testBit_xor, Nat.testBit_xor]
  have hc : (carry (row m)).testBit 2 = (rdiag 2 m && rdiag 1 m) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ m 1
  have hr : (if rdiag 1 m then 2 else 0).testBit 2 = false := by
    cases rdiag 1 m <;> rfl
  rw [hc, hr, rdiag_two_eq_parity, rdiag_one_eq_parity, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge m 2 with h | h
  · rcases Nat.lt_or_ge m 1 with h1 | h1
    · have : m = 0 := by cfomega
      subst this; decide
    · have : m = 1 := by cfomega
      subst this; decide
  · rw [decide_eq_false (by cfomega : ¬ (2 ≥ 2 * m))]
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · rw [decide_eq_false (by cfomega : ¬ (m % 2 = 1)), decide_eq_false (fun hc => by cfomega)]; rfl
    · rw [decide_eq_true h2, decide_eq_true ⟨h, h2⟩]; rfl

theorem testBit_lt_eight (L i : Nat) (h : L < 8) : L.testBit (i + 3) = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by cfomega : 3 ≤ i + 3) : 2 ^ 3 ≤ 2 ^ (i + 3)))

/-- The low three bits of the interior mask are exactly `lowSource`. -/
theorem interior_low (m : Nat) : interior m &&& 7 = lowSource m := by
  have h0 := interior_testBit_zero m
  have h1 := interior_testBit_one m
  have h2 := interior_testBit_two m
  have hL : lowSource m < 8 := by
    unfold lowSource
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [if_pos h]; decide
    · rw [if_neg (by cfomega)]
      rcases Nat.lt_or_ge m 2 with hm | hm
      · rw [if_neg (fun hc => by cfomega)]; decide
      · rcases Nat.mod_two_eq_zero_or_one m with hp | hp
        · rw [if_neg (fun hc => by cfomega)]; decide
        · rw [if_pos ⟨hm, hp⟩]; decide
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  rcases i with _ | _ | _ | i
  · rw [h0]
    unfold lowSource
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [if_pos h, decide_eq_true h]; rfl
    · rw [if_neg (by cfomega), decide_eq_false (by cfomega)]
      rcases Nat.lt_or_ge m 2 with hm | hm
      · rw [if_neg (fun hc => by cfomega)]; rfl
      · rcases Nat.mod_two_eq_zero_or_one m with hp | hp
        · rw [if_neg (fun hc => by cfomega)]; rfl
        · rw [if_pos ⟨hm, hp⟩]; rfl
  · rw [h1]
    unfold lowSource
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [if_pos h]; rfl
    · rw [if_neg (by cfomega)]
      rcases Nat.lt_or_ge m 2 with hm | hm
      · rw [if_neg (fun hc => by cfomega)]; rfl
      · rcases Nat.mod_two_eq_zero_or_one m with hp | hp
        · rw [if_neg (fun hc => by cfomega)]; rfl
        · rw [if_pos ⟨hm, hp⟩]; rfl
  · rw [h2]
    unfold lowSource
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [if_pos h, decide_eq_false (fun hc => by cfomega)]; rfl
    · rw [if_neg (by cfomega)]
      rcases Nat.lt_or_ge m 2 with hm | hm
      · rw [if_neg (fun hc => by cfomega), decide_eq_false (fun hc => by cfomega)]; rfl
      · rcases Nat.mod_two_eq_zero_or_one m with hp | hp
        · rw [if_neg (fun hc => by cfomega), decide_eq_false (fun hc => by cfomega)]; rfl
        · rw [if_pos ⟨hm, hp⟩, decide_eq_true ⟨hm, hp⟩]; rfl
  · rw [testBit_lt_eight 7 i (by decide), testBit_lt_eight (lowSource m) i hL, Bool.and_false]

/-! ## The split of the interior ledger -/

/-- The bulk carries on the right diagonals `j ≥ 3`: `interior` with its three low bits removed. -/
def interiorThree (m : Nat) : Nat := interior m ^^^ lowSource m

theorem interior_split_three (m : Nat) : interior m = lowSource m ^^^ interiorThree m := by
  unfold interiorThree
  rw [Nat.xor_comm (interior m) (lowSource m)]
  exact (Rule30UOR.Ledger.xor_xor_self _ _).symm

/-- The ledger sourced by the three low events only. -/
def lowLedger : Nat → Nat
  | 0 => 0
  | t + 1 => phiLinear (lowLedger t) ^^^ (lowSource t <<< 1)

/-- The ledger sourced by the bulk carries on diagonals `j ≥ 3` only. -/
def interiorThreeLedger : Nat → Nat
  | 0 => 0
  | t + 1 => phiLinear (interiorThreeLedger t) ^^^ (interiorThree t <<< 1)

/-- **The interior ledger splits** into the low band and the bulk. -/
theorem interiorLedger_split_three : ∀ t, interiorLedger t = lowLedger t ^^^ interiorThreeLedger t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (interiorLedger t) ^^^ (interior t <<< 1) =
      (phiLinear (lowLedger t) ^^^ (lowSource t <<< 1)) ^^^
        (phiLinear (interiorThreeLedger t) ^^^ (interiorThree t <<< 1))
    rw [ih, phiLinear_xor, interior_split_three, Nat.shiftLeft_xor_distrib]
    simp only [Nat.xor_assoc, Nat.xor_comm, Rule30UOR.Ledger.xor_left_comm]

/-- The diagonal of the low-band ledger. -/
def lowDiagonal (t : Nat) : Bool := (lowLedger t).testBit t

/-- The diagonal of the bulk ledger: the gasket parity of the carries on diagonals `j ≥ 3`. -/
def interiorThreeDiagonal (t : Nat) : Bool := (interiorThreeLedger t).testBit t

theorem interiorDiagonal_split_three (t : Nat) :
    interiorDiagonal t = bxor (lowDiagonal t) (interiorThreeDiagonal t) := by
  unfold interiorDiagonal lowDiagonal interiorThreeDiagonal
  rw [interiorLedger_split_three, Nat.testBit_xor, Rule30UOR.Scale.bxor_eq]

/-! ## The low diagonal as a fold of trinomial parities -/

def lowLedgerSum (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lowLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (lowSource n <<< 1)

theorem phiLinear_lowLedgerSum (t : Nat) : ∀ n, n ≤ t →
    phiLinear (lowLedgerSum t n) = lowLedgerSum (t + 1) n := by
  intro n
  induction n with
  | zero => intro _; exact phiLinear_zero
  | succ n ih =>
    intro hn
    show phiLinear (lowLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (lowSource n <<< 1)) =
      lowLedgerSum (t + 1) n ^^^ phiLinearPow (t + 1 - 1 - n) (lowSource n <<< 1)
    rw [phiLinear_xor, ih (by cfomega), show t + 1 - 1 - n = (t - 1 - n) + 1 by cfomega, phiLinearPow_step]

theorem lowLedger_eq_sum : ∀ t, lowLedger t = lowLedgerSum t t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show phiLinear (lowLedger t) ^^^ (lowSource t <<< 1) =
      lowLedgerSum (t + 1) t ^^^ phiLinearPow (t + 1 - 1 - t) (lowSource t <<< 1)
    rw [ih, phiLinear_lowLedgerSum t t (Nat.le_refl t), show t + 1 - 1 - t = 0 by cfomega]
    rfl

/-- The contribution of row `m`'s low events to the center at time `t`. -/
def lowTerm (t m : Nat) : Bool := (phiLinearPow (t - 1 - m) (lowSource m <<< 1)).testBit t

theorem testBit_lowLedgerSum (t : Nat) : ∀ n, (lowLedgerSum t n).testBit t = xorBelow (lowTerm t) n := by
  intro n
  induction n with
  | zero => show (0 : Nat).testBit t = false; simp
  | succ n ih =>
    show (lowLedgerSum t n ^^^ phiLinearPow (t - 1 - n) (lowSource n <<< 1)).testBit t =
      bxor (xorBelow (lowTerm t) n) (lowTerm t n)
    rw [Nat.testBit_xor, ih, Rule30UOR.Scale.bxor_eq]
    rfl

theorem lowDiagonal_eq_xorBelow (t : Nat) : lowDiagonal t = xorBelow (lowTerm t) t := by
  unfold lowDiagonal
  rw [lowLedger_eq_sum, testBit_lowLedgerSum]

theorem lowTerm_zero (t : Nat) :
    lowTerm t 0 = (if 1 ≤ t then trinomialParity (t - 1) (t - 1) else false) := by
  unfold lowTerm
  rw [lowSource_zero, phiLinearPow_shiftLeft, testBit_phiLinearPow_shift, Nat.sub_zero]

theorem lowTerm_of_odd (t m : Nat) (hm : 2 ≤ m) (h : m % 2 = 1) :
    lowTerm t m = (if 3 ≤ t then trinomialParity (t - 1 - m) (t - 3) else false) := by
  unfold lowTerm
  rw [lowSource_of_odd m hm h, show (4 : Nat) <<< 1 = 1 <<< 3 from rfl, phiLinearPow_shiftLeft,
    testBit_phiLinearPow_shift]

theorem lowTerm_eq_false (t m : Nat) (h : lowSource m = 0) : lowTerm t m = false := by
  unfold lowTerm
  rw [h, show (0 : Nat) <<< 1 = 0 from rfl, phiLinearPow_zero, Nat.zero_testBit]

/-! ## The column parities step by the trailing-ones parity -/

/-- The Thue–Morse step of the column parity is the trailing-ones parity. -/
theorem columnParity_succ_bxor : ∀ e, bxor (columnParity (e + 1)) (columnParity e) = !(trailingParity (e + 1)) := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by cfomega⟩
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; decide
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by cfomega⟩
        rw [columnParity_odd, show 2 * (k' + 1) = 2 * k' + 2 by cfomega, columnParity_even_succ,
          show 2 * k' + 2 + 1 = 2 * (k' + 1) + 1 by cfomega, trailingParity_odd, ← ih k' (by cfomega)]
        cases columnParity (k' + 1) <;> cases columnParity k' <;> rfl
    · obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by cfomega⟩
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by cfomega, columnParity_even_succ, columnParity_odd,
        show 2 * k + 2 = 2 * (k + 1) by cfomega, trailingParity_even]
      cases columnParity k <;> rfl

/-! ## The low diagonal in closed form -/

/-- For `t = s + 3` the low diagonal is `¬(columnParity s ⊕ columnParity (s / 2))`:
the seed event gives the central coefficient `1`, the diagonal-`2` pairs give the
opposite-parity column of the trinomial triangle. -/
theorem lowDiagonal_three (s : Nat) :
    lowDiagonal (s + 2 + 1) = !(bxor (columnParity s) (columnParity (s / 2))) := by
  rw [lowDiagonal_eq_xorBelow, xorBelow_front, lowTerm_zero, if_pos (by cfomega : 1 ≤ s + 2 + 1),
    show s + 2 + 1 - 1 = s + 2 by cfomega, trinomialParity_central]
  have hcong : xorBelow (fun m => lowTerm (s + 2 + 1) (s + 2 - 1 - m + 1)) (s + 1) =
      bxor (columnParity s) (sameParityColumn s) := by
    unfold columnParity sameParityColumn
    rw [← xorBelow_bxor]
    apply xorBelow_congr
    intro n hn
    show lowTerm (s + 2 + 1) (s + 2 - 1 - n + 1) =
      bxor (trinomialParity n s) (if n % 2 = s % 2 then trinomialParity n s else false)
    rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2 <;> rcases Nat.mod_two_eq_zero_or_one s with hs2 | hs2
    · rw [lowTerm_eq_false _ _ (lowSource_of_even _ (by cfomega) (by cfomega)), if_pos (by cfomega)]
      cases trinomialParity n s <;> rfl
    · rw [lowTerm_of_odd _ _ (by cfomega) (by cfomega), if_pos (by cfomega), if_neg (by cfomega),
        show s + 2 + 1 - 1 - (s + 2 - 1 - n + 1) = n by cfomega, show s + 2 + 1 - 3 = s by cfomega]
      cases trinomialParity n s <;> rfl
    · rw [lowTerm_of_odd _ _ (by cfomega) (by cfomega), if_pos (by cfomega), if_neg (by cfomega),
        show s + 2 + 1 - 1 - (s + 2 - 1 - n + 1) = n by cfomega, show s + 2 + 1 - 3 = s by cfomega]
      cases trinomialParity n s <;> rfl
    · rw [lowTerm_eq_false _ _ (lowSource_of_even _ (by cfomega) (by cfomega)), if_pos (by cfomega)]
      cases trinomialParity n s <;> rfl
  have hmain : xorBelow (fun m => lowTerm (s + 2 + 1) (m + 1)) (s + 2) =
      bxor (columnParity s) (columnParity (s / 2)) := by
    rw [xorBelow_rev]
    show bxor (xorBelow (fun m => lowTerm (s + 2 + 1) (s + 2 - 1 - m + 1)) (s + 1))
      (lowTerm (s + 2 + 1) (s + 2 - 1 - (s + 1) + 1)) = _
    rw [show s + 2 - 1 - (s + 1) + 1 = 1 by cfomega, lowTerm_eq_false _ _ lowSource_one, hcong,
      sameParityColumn_eq]
    cases columnParity s <;> cases columnParity (s / 2) <;> rfl
  rw [hmain]
  cases columnParity s <;> cases columnParity (s / 2) <;> rfl

/-- **The low background collapses to the trailing-ones parity.** -/
theorem lowDiagonal_eq (t : Nat) (ht : 2 ≤ t) :
    bxor (timeParity t) (lowDiagonal t) = !(trailingParity (t - 2)) := by
  rcases Nat.lt_or_ge t 3 with h | h
  · have : t = 2 := by cfomega
    subst this; decide
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 + 1 := ⟨t - 3, by cfomega⟩
    rw [lowDiagonal_three, show s + 2 + 1 - 2 = s + 1 by cfomega]
    unfold timeParity
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · obtain ⟨e, rfl⟩ : ∃ e, s = 2 * e := ⟨s / 2, by cfomega⟩
      rw [decide_eq_true (by cfomega : (2 * e + 2 + 1) % 2 = 1), show 2 * e / 2 = e by cfomega,
        trailingParity_odd]
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; decide
      · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by cfomega⟩
        rw [show 2 * (e' + 1) = 2 * e' + 2 by cfomega, columnParity_even_succ, ← columnParity_succ_bxor e']
        cases columnParity (e' + 1) <;> cases columnParity e' <;> rfl
    · obtain ⟨e, rfl⟩ : ∃ e, s = 2 * e + 1 := ⟨s / 2, by cfomega⟩
      rw [decide_eq_false (by cfomega : ¬ ((2 * e + 1 + 2 + 1) % 2 = 1)), columnParity_odd,
        show (2 * e + 1) / 2 = e by cfomega, show 2 * e + 1 + 1 = 2 * (e + 1) by cfomega, trailingParity_even]
      cases columnParity e <;> rfl

/-! ## The center against the trailing-ones parity -/

theorem bxor_aux_center (a b c d : Bool) (h : bxor a b = !d) : (!(bxor a (bxor b c))) = bxor d c := by
  cases a <;> cases b <;> cases c <;> cases d <;> first | rfl | exact absurd h (by decide)

/-- **The center is the trailing-ones parity of `t − 2` XOR the gasket parity of the
carries on diagonals `j ≥ 3`.** -/
theorem center_eq_trailingParity_bxor_three (t : Nat) (ht : 2 ≤ t) :
    center t = bxor (trailingParity (t - 2)) (interiorThreeDiagonal t) := by
  rw [center_eq_not_timeParity_xor_interior, interiorDiagonal_split_three]
  exact bxor_aux_center _ _ _ _ (lowDiagonal_eq t ht)

/-! ## Problem 1 as the bulk gasket parity against the trailing-ones parity -/

/-- A center period `P` from `T`, in the bulk carries: the lag-`P` difference of the
`j ≥ 3` gasket parity is the lag-`P` difference of the trailing-ones parity. -/
def ThreeAgainstTrailing (T P : Nat) : Prop :=
  ∀ t, T ≤ t → bxor (interiorThreeDiagonal (t + P)) (interiorThreeDiagonal t) =
    bxor (trailingParity (t + P - 2)) (trailingParity (t - 2))

theorem bxor_aux_period (a b c d : Bool) (h : bxor a c = bxor b d) : bxor c d = bxor a b := by
  cases a <;> cases b <;> cases c <;> cases d <;> first | rfl | exact absurd h (by decide)

theorem bxor_aux_period' (a b c d : Bool) (h : bxor c d = bxor a b) : bxor a c = bxor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> first | rfl | exact absurd h (by decide)

theorem centerPeriodic_iff_threeAgainstTrailing (T P : Nat) (hT : 2 ≤ T) :
    Rule30UOR.Scale.CenterPeriodic T P ↔ ThreeAgainstTrailing T P := by
  unfold Rule30UOR.Scale.CenterPeriodic ThreeAgainstTrailing
  constructor
  · intro h t ht
    have hc := h t ht
    rw [center_eq_trailingParity_bxor_three (t + P) (by cfomega),
      center_eq_trailingParity_bxor_three t (by cfomega)] at hc
    exact bxor_aux_period _ _ _ _ hc
  · intro h t ht
    rw [center_eq_trailingParity_bxor_three (t + P) (by cfomega),
      center_eq_trailingParity_bxor_three t (by cfomega)]
    exact bxor_aux_period' _ _ _ _ (h t ht)

theorem problem1_iff_threeAgainstTrailing : Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔
    ∀ T P, 0 < P → ¬ ThreeAgainstTrailing (T + 2) P := by
  rw [Rule30UOR.Scale.problem1_iff]
  constructor
  · intro h T P hP h3
    exact h (T + 2) P hP ((centerPeriodic_iff_threeAgainstTrailing (T + 2) P (by cfomega)).2 h3)
  · intro h T P hP hc
    apply h T P hP
    apply (centerPeriodic_iff_threeAgainstTrailing (T + 2) P (by cfomega)).1
    intro t ht
    exact hc t (by cfomega)

/-- The bulk gasket parity never repeats against the trailing-ones parity. -/
def ThreeAperiodic : Prop := ∀ T P, 0 < P → ¬ ThreeAgainstTrailing (T + 2) P

/-- **Problem 1 is `ThreeAperiodic`.** -/
theorem problem1_iff_threeAperiodic : Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ ThreeAperiodic :=
  problem1_iff_threeAgainstTrailing

theorem problem1_of_threeAperiodic (h : ThreeAperiodic) : Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff_threeAperiodic.2 h

/-! ## The trailing-ones parity is not eventually periodic -/

theorem lt_twopow : ∀ k, k < twopow k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih => rw [twopow_succ]; cfomega

/-- `trailingParity (2^k − 1) = [k odd]`. -/
theorem trailingParity_twopow_sub_one : ∀ k, trailingParity (twopow k - 1) = decide (k % 2 = 1) := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    have hpos := Rule30UOR.Scale.twopow_pos k
    rw [twopow_succ, show twopow k + twopow k - 1 = 2 * (twopow k - 1) + 1 by cfomega, trailingParity_odd, ih]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [h, show (k + 1) % 2 = 1 by cfomega]; rfl
    · rw [h, show (k + 1) % 2 = 0 by cfomega]; rfl

/-- The trailing ones of `2^k + s` are those of `s` when `s + 1 < 2^k`. -/
theorem trailingParity_twopow_add : ∀ k s, s + 1 < twopow k →
    trailingParity (twopow k + s) = trailingParity s := by
  intro k
  induction k with
  | zero =>
    intro s hs
    have h0 : twopow 0 = 1 := rfl
    rw [h0] at hs
    cfomega
  | succ k ih =>
    intro s hs
    rw [twopow_succ] at hs ⊢
    rcases Nat.mod_two_eq_zero_or_one s with h | h
    · obtain ⟨u, rfl⟩ : ∃ u, s = 2 * u := ⟨s / 2, by cfomega⟩
      rw [show twopow k + twopow k + 2 * u = 2 * (twopow k + u) by cfomega, trailingParity_even,
        trailingParity_even]
    · obtain ⟨u, rfl⟩ : ∃ u, s = 2 * u + 1 := ⟨s / 2, by cfomega⟩
      rw [show twopow k + twopow k + (2 * u + 1) = 2 * (twopow k + u) + 1 by cfomega, trailingParity_odd,
        trailingParity_odd, ih u (by cfomega)]

/-- The trailing-ones parity has period `P` from `T`. -/
def TrailingParityPeriodic (T P : Nat) : Prop := ∀ t, T ≤ t → trailingParity (t + P) = trailingParity t

/-- **The trailing-ones parity has no eventual period.** -/
theorem trailingParity_not_periodic (T P : Nat) (hP : 0 < P) : ¬ TrailingParityPeriodic T P := by
  intro h
  have hk := lt_twopow (T + P)
  have hk1 : twopow (T + P + 1) = twopow (T + P) + twopow (T + P) := twopow_succ (T + P)
  have h1 := h (twopow (T + P) - 1) (by cfomega)
  have h2 := h (twopow (T + P + 1) - 1) (by cfomega)
  rw [show twopow (T + P) - 1 + P = twopow (T + P) + (P - 1) by cfomega,
    trailingParity_twopow_add _ _ (by cfomega), trailingParity_twopow_sub_one] at h1
  rw [show twopow (T + P + 1) - 1 + P = twopow (T + P + 1) + (P - 1) by cfomega,
    trailingParity_twopow_add _ _ (by cfomega), trailingParity_twopow_sub_one] at h2
  rw [h1] at h2
  rcases Nat.mod_two_eq_zero_or_one (T + P) with hp | hp
  · rw [decide_eq_false (by cfomega : ¬ ((T + P) % 2 = 1)),
      decide_eq_true (by cfomega : (T + P + 1) % 2 = 1)] at h2
    exact absurd h2 (by decide)
  · rw [decide_eq_true hp, decide_eq_false (by cfomega : ¬ ((T + P + 1) % 2 = 1))] at h2
    exact absurd h2 (by decide)

/-! ## Consequences for the bulk gasket parity -/

/-- The bulk gasket parity has period `P` from `T`. -/
def ThreePeriodic (T P : Nat) : Prop :=
  ∀ t, T ≤ t → interiorThreeDiagonal (t + P) = interiorThreeDiagonal t

theorem bxor_aux_cancel (a b c : Bool) (h : bxor a c = bxor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> first | rfl | exact absurd h (by decide)

/-- **Under a periodic center the bulk gasket parity is itself not eventually periodic**:
it must carry the 2-adic signal. -/
theorem interiorThree_aperiodic_of_centerPeriodic (T P : Nat) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : ¬ ThreePeriodic T P := by
  intro h3
  apply trailingParity_not_periodic T P hP
  intro u hu
  have hc' := hc (u + 2) (by cfomega)
  rw [center_eq_trailingParity_bxor_three (u + 2 + P) (by cfomega),
    center_eq_trailingParity_bxor_three (u + 2) (by cfomega), h3 (u + 2) (by cfomega),
    show u + 2 + P - 2 = u + P by cfomega, show u + 2 - 2 = u by cfomega] at hc'
  exact bxor_aux_cancel _ _ _ hc'

theorem bxor_aux_comm (a b : Bool) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl

/-- **The obligation at the times `2^k + 1`**: under a center period `P < 2^k`, the lag-`P`
difference of the bulk gasket parity alternates with the parity of `k`. -/
theorem dyadic_one_obligation (T P k : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P)
    (hk : T ≤ twopow k + 1) (hP : 0 < P) (hPk : P < twopow k) :
    bxor (interiorThreeDiagonal (twopow k + 1 + P)) (interiorThreeDiagonal (twopow k + 1)) =
      bxor (decide (k % 2 = 1)) (trailingParity (P - 1)) := by
  have hpos := Rule30UOR.Scale.twopow_pos k
  have hc' := hc (twopow k + 1) hk
  rw [center_eq_trailingParity_bxor_three (twopow k + 1 + P) (by cfomega),
    center_eq_trailingParity_bxor_three (twopow k + 1) (by cfomega),
    show twopow k + 1 + P - 2 = twopow k + (P - 1) by cfomega, show twopow k + 1 - 2 = twopow k - 1 by cfomega,
    trailingParity_twopow_add _ _ (by cfomega), trailingParity_twopow_sub_one] at hc'
  rw [bxor_aux_comm (decide (k % 2 = 1))]
  exact bxor_aux_period _ _ _ _ hc'

end Rule30UOR.Band
