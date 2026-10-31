module
public import Rule30UOR.Interfaces
public import Rule30UOR.Automatic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The Rule-60 gasket

The window response is the Rule-60 propagation of the carry masks
(`duhamel`): `L x p = x (p-1) ⊕ x p` is multiplication by `1 + X`, and
`Lpow n` is `(1 + X)^n`. Over `F₂`, `(1 + X)^(2m) = (1 + X²)^m`, so the powers of
`L` factor through the binary digits of `n` (Lucas): `Lpow n` is the composition
of the spaced operators `Ls (2^i)` over the set bits `i` of `n`, the Sierpinski
gasket. This module proves the halving law and the digit recursion, which make
the response of a dyadic block an explicit parity of carry masks on the gasket. -/

@[expose] public section

namespace Rule30UOR.Gasket

open Rule30UOR.Core Rule30UOR.Scale

/-- Rule 60 at spacing `s`: multiplication by `1 + X^s`. -/
def Ls (s : Nat) (x : Int → Bool) : Int → Bool := fun p => xor (x (p - (s : Int))) (x p)

def LsPow (s : Nat) : Nat → (Int → Bool) → Int → Bool
  | 0, x => x
  | n + 1, x => Ls s (LsPow s n x)

theorem Ls_one (x : Int → Bool) : Ls 1 x = L x := rfl

theorem LsPow_one (n : Nat) (x : Int → Bool) : LsPow 1 n x = Lpow n x := by
  induction n with
  | zero => rfl
  | succ n ih => show Ls 1 (LsPow 1 n x) = L (Lpow n x); rw [ih]; rfl

theorem LsPow_add (s m n : Nat) (x : Int → Bool) : LsPow s (m + n) x = LsPow s m (LsPow s n x) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by cfomega]
    show Ls s (LsPow s (m + n) x) = Ls s (LsPow s m (LsPow s n x))
    rw [ih]

/-- Frobenius: `(1 + X^s)² = 1 + X^(2s)`. -/
theorem Ls_Ls (s : Nat) (x : Int → Bool) (p : Int) : Ls s (Ls s x) p = Ls (2 * s) x p := by
  show xor (xor (x (p - s - s)) (x (p - s))) (xor (x (p - s)) (x p)) = xor (x (p - ((2 * s : Nat) : Int))) (x p)
  rw [show p - (s : Int) - (s : Int) = p - ((2 * s : Nat) : Int) by push_cast; cfomega]
  cases x (p - ((2 * s : Nat) : Int)) <;> cases x (p - (s : Int)) <;> cases x p <;> rfl

theorem Ls_Ls_fun (s : Nat) (x : Int → Bool) : Ls s (Ls s x) = Ls (2 * s) x :=
  funext (Ls_Ls s x)

/-- Halving: `(1 + X^s)^(2m) = (1 + X^(2s))^m`. -/
theorem LsPow_two_mul (s m : Nat) (x : Int → Bool) : LsPow s (2 * m) x = LsPow (2 * s) m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by cfomega]
    show Ls s (Ls s (LsPow s (2 * m) x)) = Ls (2 * s) (LsPow (2 * s) m x)
    rw [ih, Ls_Ls_fun]

/-- The digit recursion: the lowest binary digit of `n` is applied at spacing `s`,
the rest at spacing `2s`. -/
theorem LsPow_digit (s n : Nat) (x : Int → Bool) :
    LsPow s n x = LsPow s (n % 2) (LsPow (2 * s) (n / 2) x) := by
  have h : n = n % 2 + 2 * (n / 2) := by cfomega
  conv => lhs; rw [h]
  rw [LsPow_add, LsPow_two_mul]

/-- `Lpow n` through the binary digits of `n`. -/
theorem Lpow_digit (n : Nat) (x : Int → Bool) :
    Lpow n x = LsPow 1 (n % 2) (LsPow 2 (n / 2) x) := by
  rw [← LsPow_one, LsPow_digit]

/-- The two cases of a digit at spacing `s`. -/
theorem LsPow_zero_digit (s : Nat) (x : Int → Bool) : LsPow s 0 x = x := rfl

theorem LsPow_one_digit (s : Nat) (x : Int → Bool) (p : Int) :
    LsPow s 1 x p = xor (x (p - (s : Int))) (x p) := rfl

/-- The response of a window is `duhamel` read at the center; with `Lpow_digit`
each term of the window sum is a parity of the carry masks on the gasket. -/
theorem response_eq_duhamel (t k : Nat) :
    Rule30UOR.Scale.response t k = xor (cell (t + twopow k) 0) (Lpow (twopow k) (cell t) 0) := by
  unfold Rule30UOR.Scale.response
  have h := duhamel t (twopow k) 0
  rw [h]
  cases Lpow (twopow k) (cell t) 0 <;> cases window60 t (twopow k) 0 <;> rfl

/-! ## The window as a sum of propagated carry rows

`window60 t0 (n+1) p = L (window60 t0 n) p ⊕ carry60 (t0 + n) p`, so the first
carry row of the window is propagated `n` steps by `Lpow n` and the rest is
the window of the next time: each carry row enters through the gasket of its
remaining steps. -/

theorem window60_shift (t0 : Nat) : ∀ n p,
    window60 t0 (n + 1) p = xor (Lpow n (carry60 t0) p) (window60 (t0 + 1) n p) := by
  intro n
  induction n with
  | zero =>
    intro p
    show bxor (bxor (window60 t0 0 (p - 1)) (window60 t0 0 p)) (carry60 (t0 + 0) p) = xor (carry60 t0 p) false
    show bxor (bxor false false) (carry60 (t0 + 0) p) = xor (carry60 t0 p) false
    rw [Nat.add_zero]
    cases carry60 t0 p <;> rfl
  | succ n ih =>
    intro p
    show bxor (bxor (window60 t0 (n + 1) (p - 1)) (window60 t0 (n + 1) p)) (carry60 (t0 + (n + 1)) p) =
      xor (L (Lpow n (carry60 t0)) p) (window60 (t0 + 1) (n + 1) p)
    rw [ih (p - 1), ih p]
    show bxor (bxor (xor (Lpow n (carry60 t0) (p - 1)) (window60 (t0 + 1) n (p - 1)))
        (xor (Lpow n (carry60 t0) p) (window60 (t0 + 1) n p))) (carry60 (t0 + (n + 1)) p) =
      xor (xor (Lpow n (carry60 t0) (p - 1)) (Lpow n (carry60 t0) p))
        (bxor (bxor (window60 (t0 + 1) n (p - 1)) (window60 (t0 + 1) n p)) (carry60 (t0 + 1 + n) p))
    rw [show t0 + 1 + n = t0 + (n + 1) by cfomega]
    cases Lpow n (carry60 t0) (p - 1) <;> cases Lpow n (carry60 t0) p <;>
      cases window60 (t0 + 1) n (p - 1) <;> cases window60 (t0 + 1) n p <;>
      cases carry60 (t0 + (n + 1)) p <;> rfl

/-- Duhamel additivity: the window over `a + b` steps is the window over the
first `a` steps propagated `b` steps, XOR the window of the last `b` steps. This
is the cocycle that relates the responses of a block to those of its halves. -/
theorem window60_add (t0 a : Nat) : ∀ b p,
    window60 t0 (a + b) p = xor (Lpow b (window60 t0 a) p) (window60 (t0 + a) b p) := by
  intro b
  induction b with
  | zero =>
    intro p
    show window60 t0 a p = xor (window60 t0 a p) false
    cases window60 t0 a p <;> rfl
  | succ b ih =>
    intro p
    rw [show a + (b + 1) = (a + b) + 1 by cfomega]
    show bxor (bxor (window60 t0 (a + b) (p - 1)) (window60 t0 (a + b) p)) (carry60 (t0 + (a + b)) p) =
      xor (L (Lpow b (window60 t0 a)) p)
        (bxor (bxor (window60 (t0 + a) b (p - 1)) (window60 (t0 + a) b p)) (carry60 (t0 + a + b) p))
    rw [ih (p - 1), ih p, show t0 + a + b = t0 + (a + b) by cfomega]
    show bxor (bxor (xor (Lpow b (window60 t0 a) (p - 1)) (window60 (t0 + a) b (p - 1)))
        (xor (Lpow b (window60 t0 a) p) (window60 (t0 + a) b p))) (carry60 (t0 + (a + b)) p) =
      xor (xor (Lpow b (window60 t0 a) (p - 1)) (Lpow b (window60 t0 a) p))
        (bxor (bxor (window60 (t0 + a) b (p - 1)) (window60 (t0 + a) b p)) (carry60 (t0 + (a + b)) p))
    cases Lpow b (window60 t0 a) (p - 1) <;> cases Lpow b (window60 t0 a) p <;>
      cases window60 (t0 + a) b (p - 1) <;> cases window60 (t0 + a) b p <;>
      cases carry60 (t0 + (a + b)) p <;> rfl

/-- The dyadic-diagonal response at scale `j + 1` through the two halves of its
block, both of length `2^j`: `freshman` applied to the first half. -/
theorem dyadic_response_halves (j : Nat) :
    Rule30UOR.Scale.response (twopow (j + 1)) (j + 1) =
      xor (xor (window60 (twopow (j + 1)) (twopow j) 0)
        (window60 (twopow (j + 1)) (twopow j) (0 - (twopow j : Int))))
        (window60 (twopow (j + 1) + twopow j) (twopow j) 0) := by
  unfold Rule30UOR.Scale.response
  rw [show twopow (j + 1) = twopow j + twopow j from rfl, window60_add, freshman]

/-- Paper form of `dyadic_response_halves`. -/
theorem dyadic_response_halves_paper (j : Nat) :
    Rule30UOR.Scale.response (twopow (j + 1)) (j + 1) =
      bxor (bxor (window60 (twopow (j + 1)) (twopow j) 0)
        (window60 (twopow (j + 1)) (twopow j) (Rule30UOR.Scale.negpow j)))
        (window60 (twopow (j + 1) + twopow j) (twopow j) 0) := by
  rw [Rule30UOR.Scale.bxor_eq, Rule30UOR.Scale.bxor_eq, dyadic_response_halves]
  show _ = xor (xor _ (window60 (twopow (j + 1)) (twopow j) (-((twopow j : Nat) : Int)))) _
  rw [show (0 : Int) - ((twopow j : Nat) : Int) = -((twopow j : Nat) : Int) by cfomega]

end Rule30UOR.Gasket
