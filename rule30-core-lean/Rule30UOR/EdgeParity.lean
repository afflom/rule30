module
public import Rule30UOR.EdgeSplit
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The edge background is the time parity

The edge-sourced diagonal is `edgeFormula t t = columnParity (t-1) ⊕ (right-pair part)`.
The column parity of the trinomial triangle is 2-automatic by the digit
recursion of the trinomial parity (`columnParity (2e+1) = columnParity e`,
`columnParity (2e+2) = ¬ columnParity e`), and the right-pair part is the
same-parity column `sameParityColumn (t-2) = columnParity ((t-2)/2)`. The two
cancel to the parity of `t`: `edgeFormula t t = [t odd]`. So the center is
`¬([t odd] ⊕ interiorDiagonal t)`, and a center period `P` is exactly an
interior-diagonal period `2P` (and conversely): Problem 1 is the aperiodicity
of the interior-sourced diagonal. -/

@[expose] public section

namespace Rule30UOR.EdgeParity

open Rule30UOR.Core
open Rule30UOR.Ledger Rule30UOR.EdgeSplit

/-! ## Even/odd splitting of a fold -/

theorem xorBelow_even_odd (g : Nat → Bool) : ∀ k, xorBelow g (2 * k) =
    bxor (xorBelow (fun m => g (2 * m)) k) (xorBelow (fun m => g (2 * m + 1)) k) := by
  intro k
  induction k with
  | zero => rw [Nat.mul_zero]; rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by cfomega]
    show bxor (bxor (xorBelow g (2 * k)) (g (2 * k))) (g (2 * k + 1)) =
      bxor (bxor (xorBelow (fun m => g (2 * m)) k) (g (2 * k)))
        (bxor (xorBelow (fun m => g (2 * m + 1)) k) (g (2 * k + 1)))
    rw [ih]
    cases xorBelow (fun m => g (2 * m)) k <;> cases xorBelow (fun m => g (2 * m + 1)) k <;>
      cases g (2 * k) <;> cases g (2 * k + 1) <;> rfl

theorem xorBelow_false : ∀ n, xorBelow (fun _ => false) n = false := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show bxor (xorBelow (fun _ => false) n) false = false
    rw [ih]; rfl

/-! ## The digits of the trinomial parity -/

theorem trinomialParity_zero (d : Nat) : trinomialParity 0 d = decide (d = 0) := rfl

theorem trinomialParity_even_even (m e : Nat) : trinomialParity (2 * m) (2 * e) = trinomialParity m e := by
  cases m with
  | zero =>
    cases e with
    | zero => rfl
    | succ e =>
      rw [Nat.mul_zero, trinomialParity_zero, trinomialParity_zero,
        decide_eq_false (by cfomega : ¬ (2 * (e + 1) = 0)), decide_eq_false (by cfomega : ¬ (e + 1 = 0))]
  | succ m =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by cfomega, trinomialParity_succ,
      if_pos (by cfomega : (2 * m + 1 + 1) % 2 = 0), if_pos (by cfomega : (2 * e) % 2 = 0),
      show (2 * m + 1 + 1) / 2 = m + 1 by cfomega, show 2 * e / 2 = e by cfomega]

theorem trinomialParity_even_odd (m e : Nat) : trinomialParity (2 * m) (2 * e + 1) = false := by
  cases m with
  | zero =>
    rw [Nat.mul_zero, trinomialParity_zero, decide_eq_false (by cfomega : ¬ (2 * e + 1 = 0))]
  | succ m =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by cfomega, trinomialParity_succ,
      if_pos (by cfomega : (2 * m + 1 + 1) % 2 = 0), if_neg (by cfomega : ¬ ((2 * e + 1) % 2 = 0))]

theorem trinomialParity_odd_odd (m e : Nat) : trinomialParity (2 * m + 1) (2 * e + 1) = trinomialParity m e := by
  rw [trinomialParity_succ, if_neg (by cfomega : ¬ ((2 * m + 1) % 2 = 0)),
    if_neg (by cfomega : ¬ ((2 * e + 1) % 2 = 0)), if_pos (by cfomega : 1 ≤ 2 * e + 1),
    if_pos (by cfomega : (2 * e + 1 - 1) % 2 = 0), show (2 * m + 1) / 2 = m by cfomega,
    show (2 * e + 1 - 1) / 2 = e by cfomega]
  have h3 : (if 2 ≤ 2 * e + 1 then
      (if (2 * e + 1 - 2) % 2 = 0 then trinomialParity m ((2 * e + 1 - 2) / 2) else false) else false) = false := by
    rcases Nat.lt_or_ge (2 * e + 1) 2 with h | h
    · rw [if_neg (by cfomega : ¬ (2 ≤ 2 * e + 1))]
    · rw [if_pos h, if_neg (by cfomega : ¬ ((2 * e + 1 - 2) % 2 = 0))]
  rw [h3]
  cases trinomialParity m e <;> rfl

theorem trinomialParity_odd_even_succ (m e : Nat) :
    trinomialParity (2 * m + 1) (2 * e + 2) = bxor (trinomialParity m (e + 1)) (trinomialParity m e) := by
  rw [trinomialParity_succ, if_neg (by cfomega : ¬ ((2 * m + 1) % 2 = 0)),
    if_pos (by cfomega : (2 * e + 2) % 2 = 0), if_pos (by cfomega : 1 ≤ 2 * e + 2),
    if_neg (by cfomega : ¬ ((2 * e + 2 - 1) % 2 = 0)), if_pos (by cfomega : 2 ≤ 2 * e + 2),
    if_pos (by cfomega : (2 * e + 2 - 2) % 2 = 0), show (2 * m + 1) / 2 = m by cfomega,
    show (2 * e + 2) / 2 = e + 1 by cfomega, show (2 * e + 2 - 2) / 2 = e by cfomega]
  cases trinomialParity m (e + 1) <;> cases trinomialParity m e <;> rfl

theorem trinomialParity_odd_zero (m : Nat) : trinomialParity (2 * m + 1) 0 = trinomialParity m 0 := by
  rw [trinomialParity_succ, if_neg (by cfomega : ¬ ((2 * m + 1) % 2 = 0)),
    if_pos (by decide : 0 % 2 = 0), if_neg (by decide : ¬ (1 ≤ 0)), if_neg (by decide : ¬ (2 ≤ 0)),
    show (2 * m + 1) / 2 = m by cfomega, Nat.zero_div]
  cases trinomialParity m 0 <;> rfl

/-! ## The central coefficient is one -/

theorem trinomialParity_central_fuel : ∀ f n, n ≤ f → trinomialParity n n = true := by
  intro f
  induction f with
  | zero =>
    intro n hn
    have : n = 0 := by cfomega
    subst this; rfl
  | succ f ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; rfl
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * (m + 1) := ⟨n / 2 - 1, by cfomega⟩
        rw [trinomialParity_even_even]
        exact ih (m + 1) (by cfomega)
      · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by cfomega⟩
        rw [trinomialParity_odd_odd]
        exact ih m (by cfomega)

/-- The central coefficient of `q^n` is `1`: `trinomialParity n n = true`. -/
theorem trinomialParity_central (n : Nat) : trinomialParity n n = true :=
  trinomialParity_central_fuel n n (Nat.le_refl n)

/-! ## The column parity is 2-automatic -/

theorem columnParity_zero : columnParity 0 = true := by decide

theorem columnParity_odd (e : Nat) : columnParity (2 * e + 1) = columnParity e := by
  have h1 : xorBelow (fun m => trinomialParity (2 * m) (2 * e + 1)) (e + 1) = false := by
    rw [xorBelow_congr (fun m => trinomialParity (2 * m) (2 * e + 1)) (fun _ => false) (e + 1)
      (fun m _ => trinomialParity_even_odd m e), xorBelow_false]
  have h2 : xorBelow (fun m => trinomialParity (2 * m + 1) (2 * e + 1)) (e + 1) = columnParity e :=
    xorBelow_congr (fun m => trinomialParity (2 * m + 1) (2 * e + 1)) (fun m => trinomialParity m e) (e + 1)
      (fun m _ => trinomialParity_odd_odd m e)
  show xorBelow (fun n => trinomialParity n (2 * e + 1)) (2 * e + 1 + 1) = columnParity e
  rw [show 2 * e + 1 + 1 = 2 * (e + 1) by cfomega, xorBelow_even_odd]
  show bxor (xorBelow (fun m => trinomialParity (2 * m) (2 * e + 1)) (e + 1))
    (xorBelow (fun m => trinomialParity (2 * m + 1) (2 * e + 1)) (e + 1)) = columnParity e
  rw [h1, h2]
  cases columnParity e <;> rfl

theorem columnParity_even_succ (e : Nat) : columnParity (2 * e + 2) = !(columnParity e) := by
  have hc : trinomialParity (2 * (e + 1)) (2 * e + 2) = true := by
    rw [show 2 * (e + 1) = 2 * e + 2 by cfomega]; exact trinomialParity_central _
  have h1 : xorBelow (fun m => trinomialParity (2 * m) (2 * e + 2)) (e + 1) =
      xorBelow (fun m => trinomialParity m (e + 1)) (e + 1) :=
    xorBelow_congr (fun m => trinomialParity (2 * m) (2 * e + 2)) (fun m => trinomialParity m (e + 1)) (e + 1)
      (fun m _ => by
        show trinomialParity (2 * m) (2 * e + 2) = trinomialParity m (e + 1)
        rw [show 2 * e + 2 = 2 * (e + 1) by cfomega]
        exact trinomialParity_even_even m (e + 1))
  have h2 : xorBelow (fun m => trinomialParity (2 * m + 1) (2 * e + 2)) (e + 1) =
      bxor (xorBelow (fun m => trinomialParity m (e + 1)) (e + 1)) (xorBelow (fun m => trinomialParity m e) (e + 1)) := by
    rw [← xorBelow_bxor]
    exact xorBelow_congr (fun m => trinomialParity (2 * m + 1) (2 * e + 2))
      (fun m => bxor (trinomialParity m (e + 1)) (trinomialParity m e)) (e + 1)
      (fun m _ => trinomialParity_odd_even_succ m e)
  show xorBelow (fun n => trinomialParity n (2 * e + 2)) (2 * e + 2 + 1) =
    !(xorBelow (fun n => trinomialParity n e) (e + 1))
  rw [show 2 * e + 2 + 1 = 2 * (e + 1) + 1 by cfomega]
  show bxor (xorBelow (fun n => trinomialParity n (2 * e + 2)) (2 * (e + 1)))
    (trinomialParity (2 * (e + 1)) (2 * e + 2)) = _
  rw [hc, xorBelow_even_odd]
  show bxor (bxor (xorBelow (fun m => trinomialParity (2 * m) (2 * e + 2)) (e + 1))
    (xorBelow (fun m => trinomialParity (2 * m + 1) (2 * e + 2)) (e + 1))) true = _
  rw [h1, h2]
  cases xorBelow (fun m => trinomialParity m (e + 1)) (e + 1) <;>
    cases xorBelow (fun n => trinomialParity n e) (e + 1) <;> rfl

/-! ## The same-parity column -/

/-- The column `N` of the trinomial triangle restricted to the rows of the parity of `N`. -/
def sameParityColumn (N : Nat) : Bool :=
  xorBelow (fun j => if j % 2 = N % 2 then trinomialParity j N else false) (N + 1)

theorem sameParityColumn_eq (N : Nat) : sameParityColumn N = columnParity (N / 2) := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, N = 2 * e := ⟨N / 2, by cfomega⟩
    have h1 : xorBelow (fun m => if (2 * m) % 2 = (2 * e) % 2 then trinomialParity (2 * m) (2 * e) else false) e =
        xorBelow (fun m => trinomialParity m e) e :=
      xorBelow_congr (fun m => if (2 * m) % 2 = (2 * e) % 2 then trinomialParity (2 * m) (2 * e) else false)
        (fun m => trinomialParity m e) e
        (fun m _ => by
          show (if (2 * m) % 2 = (2 * e) % 2 then trinomialParity (2 * m) (2 * e) else false) = trinomialParity m e
          rw [if_pos (by cfomega : (2 * m) % 2 = (2 * e) % 2)]
          exact trinomialParity_even_even m e)
    have h2 : xorBelow (fun m => if (2 * m + 1) % 2 = (2 * e) % 2 then trinomialParity (2 * m + 1) (2 * e) else false) e =
        false := by
      rw [xorBelow_congr (fun m => if (2 * m + 1) % 2 = (2 * e) % 2 then trinomialParity (2 * m + 1) (2 * e) else false)
        (fun _ => false) e
        (fun m _ => by
          show (if (2 * m + 1) % 2 = (2 * e) % 2 then trinomialParity (2 * m + 1) (2 * e) else false) = false
          rw [if_neg (by cfomega : ¬ ((2 * m + 1) % 2 = (2 * e) % 2))]), xorBelow_false]
    show xorBelow (fun j => if j % 2 = (2 * e) % 2 then trinomialParity j (2 * e) else false) (2 * e + 1) =
      columnParity (2 * e / 2)
    rw [show 2 * e / 2 = e by cfomega]
    show bxor (xorBelow (fun j => if j % 2 = (2 * e) % 2 then trinomialParity j (2 * e) else false) (2 * e))
      (if (2 * e) % 2 = (2 * e) % 2 then trinomialParity (2 * e) (2 * e) else false) =
      bxor (xorBelow (fun n => trinomialParity n e) e) (trinomialParity e e)
    rw [if_pos (rfl : (2 * e) % 2 = (2 * e) % 2), trinomialParity_central, trinomialParity_central, xorBelow_even_odd]
    show bxor (bxor (xorBelow (fun m => if (2 * m) % 2 = (2 * e) % 2 then trinomialParity (2 * m) (2 * e) else false) e)
      (xorBelow (fun m => if (2 * m + 1) % 2 = (2 * e) % 2 then trinomialParity (2 * m + 1) (2 * e) else false) e)) true =
      bxor (xorBelow (fun n => trinomialParity n e) e) true
    rw [h1, h2]
    cases xorBelow (fun n => trinomialParity n e) e <;> rfl
  · obtain ⟨e, rfl⟩ : ∃ e, N = 2 * e + 1 := ⟨N / 2, by cfomega⟩
    have h1 : xorBelow (fun m => if (2 * m) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m) (2 * e + 1) else false)
        (e + 1) = false := by
      rw [xorBelow_congr (fun m => if (2 * m) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m) (2 * e + 1) else false)
        (fun _ => false) (e + 1)
        (fun m _ => by
          show (if (2 * m) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m) (2 * e + 1) else false) = false
          rw [if_neg (by cfomega : ¬ ((2 * m) % 2 = (2 * e + 1) % 2))]), xorBelow_false]
    have h2 : xorBelow (fun m => if (2 * m + 1) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m + 1) (2 * e + 1) else false)
        (e + 1) = columnParity e := by
      unfold columnParity
      exact xorBelow_congr
        (fun m => if (2 * m + 1) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m + 1) (2 * e + 1) else false)
        (fun n => trinomialParity n e) (e + 1)
        (fun m _ => by
          show (if (2 * m + 1) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m + 1) (2 * e + 1) else false) =
            trinomialParity m e
          rw [if_pos (by cfomega : (2 * m + 1) % 2 = (2 * e + 1) % 2)]
          exact trinomialParity_odd_odd m e)
    show xorBelow (fun j => if j % 2 = (2 * e + 1) % 2 then trinomialParity j (2 * e + 1) else false) (2 * e + 1 + 1) =
      columnParity ((2 * e + 1) / 2)
    rw [show (2 * e + 1) / 2 = e by cfomega, show 2 * e + 1 + 1 = 2 * (e + 1) by cfomega, xorBelow_even_odd]
    show bxor
      (xorBelow (fun m => if (2 * m) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m) (2 * e + 1) else false) (e + 1))
      (xorBelow (fun m => if (2 * m + 1) % 2 = (2 * e + 1) % 2 then trinomialParity (2 * m + 1) (2 * e + 1) else false)
        (e + 1)) = columnParity e
    rw [h1, h2]
    cases columnParity e <;> rfl

/-! ## The right-pair part is the same-parity column -/

theorem edgeRight_eq (t : Nat) (ht : 2 ≤ t) : xorBelow (edgeRightTerm t) t = sameParityColumn (t - 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
  rw [show s + 2 - 2 = s by cfomega, xorBelow_rev]
  have hlast : edgeRightTerm (s + 2) (s + 2 - 1 - (s + 1)) = false := by
    rw [show s + 2 - 1 - (s + 1) = 0 by cfomega]
    unfold edgeRightTerm
    rw [rdiag_one_eq_parity]
    rfl
  have hmain : xorBelow (fun m => edgeRightTerm (s + 2) (s + 2 - 1 - m)) (s + 1) =
      xorBelow (fun j => if j % 2 = s % 2 then trinomialParity j s else false) (s + 1) := by
    apply xorBelow_congr
    intro j hj
    show edgeRightTerm (s + 2) (s + 2 - 1 - j) = (if j % 2 = s % 2 then trinomialParity j s else false)
    unfold edgeRightTerm
    rw [rdiag_one_eq_parity, if_pos (by cfomega : 2 ≤ s + 2), show s + 2 - 1 - (s + 2 - 1 - j) = j by cfomega,
      show s + 2 - 2 = s by cfomega]
    rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;> rcases Nat.mod_two_eq_zero_or_one s with hs2 | hs2
    · rw [decide_eq_true (by cfomega : (s + 2 - 1 - j) % 2 = 1), if_pos (by cfomega : j % 2 = s % 2)]
      rfl
    · rw [decide_eq_false (by cfomega : ¬ ((s + 2 - 1 - j) % 2 = 1)), if_neg (by cfomega : ¬ (j % 2 = s % 2))]
      rfl
    · rw [decide_eq_false (by cfomega : ¬ ((s + 2 - 1 - j) % 2 = 1)), if_neg (by cfomega : ¬ (j % 2 = s % 2))]
      rfl
    · rw [decide_eq_true (by cfomega : (s + 2 - 1 - j) % 2 = 1), if_pos (by cfomega : j % 2 = s % 2)]
      rfl
  show bxor (xorBelow (fun m => edgeRightTerm (s + 2) (s + 2 - 1 - m)) (s + 1))
    (edgeRightTerm (s + 2) (s + 2 - 1 - (s + 1))) = sameParityColumn s
  rw [hlast, hmain]
  unfold sameParityColumn
  cases xorBelow (fun j => if j % 2 = s % 2 then trinomialParity j s else false) (s + 1) <;> rfl

/-! ## The edge background is the time parity -/

/-- **The edge background is the parity of the time**: `edgeFormula t t = [t odd]`. -/
theorem edgeFormula_eq_parity (t : Nat) : edgeFormula t t = decide (t % 2 = 1) := by
  rcases Nat.lt_or_ge t 2 with h | h
  · rcases Nat.lt_or_ge t 1 with h1 | h1
    · have : t = 0 := by cfomega
      subst this; rfl
    · have : t = 1 := by cfomega
      subst this
      show bxor (edgeFormula 1 0) (edgeTerm 1 0) = decide (1 % 2 = 1)
      rw [edgeTerm_eq]
      rfl
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by cfomega⟩
    rw [edgeFormula_split (s + 2) (by cfomega), edgeRight_eq (s + 2) (by cfomega), sameParityColumn_eq,
      show s + 2 - 2 = s by cfomega, show s + 2 - 1 = s + 1 by cfomega]
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · obtain ⟨e, rfl⟩ : ∃ e, s = 2 * e := ⟨s / 2, by cfomega⟩
      rw [columnParity_odd, show 2 * e / 2 = e by cfomega,
        decide_eq_false (by cfomega : ¬ ((2 * e + 2) % 2 = 1))]
      cases columnParity e <;> rfl
    · obtain ⟨e, rfl⟩ : ∃ e, s = 2 * e + 1 := ⟨s / 2, by cfomega⟩
      rw [show 2 * e + 1 + 1 = 2 * e + 2 by cfomega, columnParity_even_succ,
        show (2 * e + 1) / 2 = e by cfomega, decide_eq_true (by cfomega : (2 * e + 1 + 2) % 2 = 1)]
      cases columnParity e <;> rfl

/-- The parity of the time. -/
def timeParity (t : Nat) : Bool := decide (t % 2 = 1)

theorem timeParity_add_two_mul (t P : Nat) : timeParity (t + 2 * P) = timeParity t := by
  unfold timeParity
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [decide_eq_false (by cfomega : ¬ ((t + 2 * P) % 2 = 1)), decide_eq_false (by cfomega : ¬ (t % 2 = 1))]
  · rw [decide_eq_true (by cfomega : (t + 2 * P) % 2 = 1), decide_eq_true h]

/-- **The edge diagonal is the time parity.** -/
theorem edgeDiagonal_eq_timeParity (t : Nat) : edgeDiagonal t = timeParity t := by
  unfold timeParity
  rw [edgeDiagonal_eq_formula, edgeFormula_eq_parity]

/-- **The center against the time parity**: `center t = ¬([t odd] ⊕ interiorDiagonal t)`. -/
theorem center_eq_not_timeParity_xor_interior (t : Nat) :
    center t = !(bxor (timeParity t) (interiorDiagonal t)) := by
  unfold timeParity
  rw [center_eq_not_formula_xor_interior, edgeFormula_eq_parity]

/-- The interior diagonal is the complemented center shifted by the time parity. -/
theorem interiorDiagonal_eq_center (t : Nat) : interiorDiagonal t = bxor (!(center t)) (timeParity t) := by
  rw [center_eq_not_timeParity_xor_interior]
  cases timeParity t <;> cases interiorDiagonal t <;> rfl

/-! ## Problem 1 is the aperiodicity of the interior diagonal -/

/-- The interior diagonal has period `P` from `T`. -/
def InteriorPeriodic (T P : Nat) : Prop := ∀ t, T ≤ t → interiorDiagonal (t + P) = interiorDiagonal t

theorem interiorPeriodic_of_centerPeriodic (T P : Nat) (h : Rule30UOR.Scale.CenterPeriodic T P) :
    InteriorPeriodic T (2 * P) := by
  unfold InteriorPeriodic
  intro t ht
  rw [interiorDiagonal_eq_center, interiorDiagonal_eq_center, timeParity_add_two_mul,
    show t + 2 * P = t + P + P by cfomega, h (t + P) (by cfomega), h t ht]

theorem centerPeriodic_of_interiorPeriodic (T P : Nat) (h : InteriorPeriodic T P) :
    Rule30UOR.Scale.CenterPeriodic T (2 * P) := by
  unfold Rule30UOR.Scale.CenterPeriodic
  intro t ht
  rw [center_eq_not_timeParity_xor_interior, center_eq_not_timeParity_xor_interior, timeParity_add_two_mul,
    show t + 2 * P = t + P + P by cfomega, h (t + P) (by cfomega), h t ht]

/-- **Problem 1 is the aperiodicity of the interior-sourced diagonal.** -/
theorem problem1_iff_interior : Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔
    ∀ T P, 0 < P → ¬ InteriorPeriodic T P := by
  rw [Rule30UOR.Scale.problem1_iff]
  constructor
  · intro h T P hP hI
    exact h T (2 * P) (by cfomega) (centerPeriodic_of_interiorPeriodic T P hI)
  · intro h T P hP hc
    exact h T (2 * P) (by cfomega) (interiorPeriodic_of_centerPeriodic T P hc)

theorem problem1_of_interior_aperiodic (h : ∀ T P, 0 < P → ¬ InteriorPeriodic T P) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff_interior.2 h

/-- The interior diagonal is not eventually periodic. -/
def InteriorAperiodic : Prop := ∀ T P, 0 < P → ¬ InteriorPeriodic T P

/-- **Problem 1 is the aperiodicity of the interior diagonal.** -/
theorem problem1_iff_interiorAperiodic :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ InteriorAperiodic :=
  problem1_iff_interior

end Rule30UOR.EdgeParity
