module

public import Rule30UOR.Scale

/-!
# Problem 1 as the irrationality of the center's binary constant

`ldrem b r t` and `lddig b r t` are the remainders and digits of the long division of `r / b` in
base two (LexLean core). A tail of the center that equals these digits is the binary expansion
of the rational number `r / b`.

* `periodic_digits`: the digits of `r / b` (with `0 < b`, `r ≤ b`) repeat from some point (the
  remainders stay in `[0, b]`, two of them coincide, the division is deterministic).
* `digits_of_periodic`: a tail of the center with period `P` from `T` is the expansion of
  `V / (2^P - 1)`, `V` the value of its first block (`2 V_t = c (T + t) (2^P - 1) + V_(t+1)`).
* `problem1_iff_irrational`: **Problem 1 holds exactly when no tail of the center is the binary
  expansion of a rational number**, i.e. when `x₃₀ = Σ c(t) 2^-(t+1)` is irrational.
-/

@[expose] public section

namespace Rule30UOR.Rational

open Rule30UOR.Core Rule30UOR.Scale

theorem ldrem_succ (b r t : Nat) :
    ldrem b r (t + 1) = if ldrem b r t + ldrem b r t < b then ldrem b r t + ldrem b r t
      else ldrem b r t + ldrem b r t - b := by
  show (if LexLeanCollections.lessThan (ldrem b r t + ldrem b r t) b then _ else LexLeanRuntime.subtract _ b) = _
  rw [lt_bool_nat]
  by_cases h : ldrem b r t + ldrem b r t < b
  · simp [h]
  · simp [h]; rfl

theorem lddig_eq (b r t : Nat) : lddig b r t = !decide (ldrem b r t + ldrem b r t < b) := by
  show (!(LexLeanCollections.lessThan _ _)) = _
  rw [lt_bool_nat]

/-! ### Rational digits repeat -/

theorem ldrem_le {b r : Nat} (hr : r ≤ b) : ∀ t, ldrem b r t ≤ b := by
  intro t
  induction t with
  | zero => exact hr
  | succ t ih => rw [ldrem_succ]; split <;> omega

theorem ldrem_shift {b r : Nat} {m n : Nat} (h : ldrem b r m = ldrem b r n) :
    ∀ i, ldrem b r (m + i) = ldrem b r (n + i) := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [show m + (i + 1) = (m + i) + 1 by omega, show n + (i + 1) = (n + i) + 1 by omega,
      ldrem_succ, ldrem_succ, ih]

/-- Unary code of a remainder, for the kit's pigeonhole. -/
def code (b r : Nat) : List Bool := (List.range (b + 1)).map fun i => decide (i = r)

theorem code_length (b r : Nat) : (code b r).length = b + 1 := by simp [code]

theorem code_inj {b r r' : Nat} (hr : r ≤ b) (h : code b r = code b r') : r = r' := by
  have e := congrArg (fun l => l[r]?) h
  simp [code, List.getElem?_map, List.getElem?_range (show r < b + 1 by omega)] at e
  exact e

theorem periodic_digits {b r : Nat} (hr : r ≤ b) :
    ∃ m P, 0 < P ∧ ∀ i, lddig b r (m + i + P) = lddig b r (m + i) := by
  obtain ⟨m, n, hmn, -, he⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole (b + 1)
    (fun t => code b (ldrem b r t)) (fun t => code_length b _)
  have eq : ldrem b r m = ldrem b r n := code_inj (ldrem_le hr m) he
  refine ⟨m, n - m, by omega, fun i => ?_⟩
  rw [lddig_eq, lddig_eq, show m + i + (n - m) = n + i by omega, ← ldrem_shift eq i]

/-! ### Periodic tails are rational -/

section Window

variable (c : Nat → Bool) (T : Nat)

/-- The value of the `n` bits of `c` from `T + t`, most significant first. -/
def win : Nat → Nat → Nat
  | _, 0 => 0
  | t, n + 1 => win t n + win t n + (c (T + t + n)).toNat

theorem win_lt : ∀ t n, win c T t n < 2 ^ n := by
  intro t n
  induction n with
  | zero => simp [win]
  | succ n ih =>
    show win c T t n + win c T t n + (c (T + t + n)).toNat < 2 ^ (n + 1)
    have : (c (T + t + n)).toNat ≤ 1 := by cases c (T + t + n) <;> decide
    rw [Nat.pow_succ]; omega

theorem win_shift : ∀ t n, win c T (t + 1) n + (c (T + t)).toNat * 2 ^ n =
    win c T t n + win c T t n + (c (T + t + n)).toNat := by
  intro t n
  induction n with
  | zero => simp [win]
  | succ n ih =>
    show (win c T (t + 1) n + win c T (t + 1) n + (c (T + (t + 1) + n)).toNat) + (c (T + t)).toNat * 2 ^ (n + 1) =
      (win c T t n + win c T t n + (c (T + t + n)).toNat) + (win c T t n + win c T t n + (c (T + t + n)).toNat) +
        (c (T + t + (n + 1))).toNat
    rw [show T + (t + 1) + n = T + t + (n + 1) by omega, Nat.pow_succ]
    have e : (c (T + t)).toNat * (2 ^ n * 2) = (c (T + t)).toNat * 2 ^ n + (c (T + t)).toNat * 2 ^ n := by
      rw [Nat.mul_two]; exact Nat.mul_add _ _ _
    rw [e]; omega

end Window

theorem digits_of_periodic {c : Nat → Bool} {T P : Nat} (hP : 0 < P)
    (h : ∀ t, T ≤ t → c (t + P) = c t) :
    ∀ t, ldrem (2 ^ P - 1) (win c T 0 P) t = win c T t P ∧ lddig (2 ^ P - 1) (win c T 0 P) t = c (T + t) := by
  have hpow : 2 ≤ 2 ^ P := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hP; simpa using this
  -- the block relation `2 V_t = c (T + t) (2^P - 1) + V_(t+1)`
  have rel : ∀ t, win c T t P + win c T t P = (c (T + t)).toNat * (2 ^ P - 1) + win c T (t + 1) P := by
    intro t
    have s := win_shift c T t P
    rw [h (T + t) (by omega)] at s
    have : (c (T + t)).toNat ≤ 1 := by cases c (T + t) <;> decide
    rcases Nat.lt_or_ge (c (T + t)).toNat 1 with h0 | h1
    · have e : (c (T + t)).toNat = 0 := by omega
      rw [e] at s ⊢; omega
    · have e : (c (T + t)).toNat = 1 := by omega
      rw [e] at s ⊢; rw [Nat.one_mul] at s ⊢; omega
  have dig : ∀ t, (!decide (win c T t P + win c T t P < 2 ^ P - 1)) = c (T + t) := by
    intro t
    have r := rel t
    have hl := win_lt c T (t + 1) P
    cases hc : c (T + t)
    · rw [hc] at r
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add] at r
      -- `2 V_t = V_(t+1)` is even and `2^P - 1` is odd, so `V_(t+1) < 2^P - 1`
      have hodd : (2 ^ P - 1) % 2 = 1 := by
        have : 2 ^ P % 2 = 0 := by
          obtain ⟨q, hq⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
          rw [hq, Nat.pow_succ]; omega
        omega
      have : win c T t P + win c T t P ≠ 2 ^ P - 1 := by omega
      simp only [Bool.not_eq_false', decide_eq_true_eq]; omega
    · rw [hc] at r
      simp only [Bool.toNat_true, Nat.one_mul] at r
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
  intro t
  induction t with
  | zero => exact ⟨rfl, by rw [lddig_eq]; exact dig 0⟩
  | succ t ih =>
    have hr : ldrem (2 ^ P - 1) (win c T 0 P) (t + 1) = win c T (t + 1) P := by
      rw [ldrem_succ, ih.1]
      have r := rel t
      cases hc : c (T + t)
      · rw [hc] at r
        simp only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add] at r
        have d := dig t; rw [hc] at d
        have hlt : win c T t P + win c T t P < 2 ^ P - 1 := by
          simp only [Bool.not_eq_false', decide_eq_true_eq] at d; exact d
        rw [if_pos hlt]; exact r
      · rw [hc] at r
        simp only [Bool.toNat_true, Nat.one_mul] at r
        have d := dig t; rw [hc] at d
        have hge : ¬ win c T t P + win c T t P < 2 ^ P - 1 := by
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at d; exact d
        rw [if_neg hge]; omega
    exact ⟨hr, by rw [lddig_eq, hr]; exact dig (t + 1)⟩

/-! ### The equivalence -/

/-- Some tail of the center is the binary expansion of a rational number `r / b`. -/
def RationalTail : Prop :=
  ∃ b r T, 0 < b ∧ r ≤ b ∧ ∀ t, center (T + t) = lddig b r t

theorem problem1_iff_irrational :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ ¬ RationalTail := by
  rw [problem1_iff]
  constructor
  · rintro hno ⟨b, r, T, hb, hr, hd⟩
    obtain ⟨m, P, hP, hper⟩ := periodic_digits hr
    refine hno (T + m) P hP fun t ht => ?_
    obtain ⟨i, rfl⟩ : ∃ i, t = T + m + i := ⟨t - (T + m), by omega⟩
    rw [show T + m + i + P = T + (m + i + P) by omega, show T + m + i = T + (m + i) by omega, hd, hd,
      hper i]
  · intro hrat T P hP hc
    refine hrat ⟨2 ^ P - 1, win center T 0 P, T, ?_, ?_, fun t => (digits_of_periodic hP hc t).2.symm⟩
    · have := Nat.pow_le_pow_right (show 0 < 2 by decide) hP; simp at this; omega
    · have := win_lt center T 0 P; omega

end Rule30UOR.Rational

namespace Rule30UOR.Rational
def Irrational30 : Prop := ¬ RationalTail
theorem problem1_of_irrational (h : Irrational30) : Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff_irrational.2 h
theorem irrational_of_problem1 (h : Ruliology.CellularAutomata.Rule30Prize.Problem1) : Irrational30 :=
  problem1_iff_irrational.1 h
end Rule30UOR.Rational
