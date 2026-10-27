module

public import Rule30UOR.Core
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# The dyadic scale identity (steps 1–3)

All objects are the LexLean core's: `cell`, `carry60 s p = !cell s p && cell s (p + 1)`,
`window60 t0 n p` (the rule-60 accumulation of the carries over the window `[t0, t0 + n)`, by its
law) and `twopow`.

* `cell_eq_kit`: the core's `cell` is the kit's.
* **Step 1, the kernel's power-of-two reuse** (`freshman`): the rule-60 operator
  `L x p = x (p-1) xor x p` satisfies `L^(2^k) x p = x p xor x (p - 2^k)`.
* **Step 2, the scale identity** (`scale`, `scale_center`):
  `cell (t0 + 2^k) p = cell t0 p xor cell t0 (p - 2^k) xor window60 t0 (2^k) p`. At the center:
  `center (t + 2^k) = center t xor cell t (-2^k) xor window60 t (2^k) 0`.
* **Step 3, the constraint of periodicity** (`periodic_scale`, `periodic_scale_cone`): if the
  center has period `P` from `T`, then for every scale `k` and every `t ≥ T`,
  `cell t (-2^k) xor window60 t (2^k) 0 = center (t + 2^k % P) xor center t`; for
  `T ≤ t < 2^k` the first term is white, so the window response alone equals the center's
  difference at lag `2^k mod P`.
-/

@[expose] public section

namespace Rule30UOR.Scale

open Rule30UOR.Core

/-! ### Runtime primitives -/

theorem sub_one (p : Int) : LexLeanRuntime.subtract p 1 = p - 1 := rfl
theorem sub_neg_one (p : Int) : LexLeanRuntime.subtract p (-1) = p + 1 := by
  show p - (-1) = p + 1; omega

theorem lt_bool (p q : Int) : LexLeanCollections.lessThan p q = decide (p < q) := by
  show (match compareOfLessAndEq p q with | Ordering.lt => true | _ => false) = _
  unfold compareOfLessAndEq
  by_cases h : p < q
  · simp [h]
  · by_cases e : p = q
    · simp [e]
    · simp [h, e]

theorem bxor_eq (a b : Bool) : bxor a b = xor a b := by cases a <;> cases b <;> rfl

/-! ### The core's cell is the kit's -/

theorem cell_zero_eq (p : Int) : cell 0 p = decide (p = 0) := by
  show ((!(LexLeanCollections.lessThan p (0 : Int) : Bool)) && (!(LexLeanCollections.lessThan (0 : Int) p : Bool))) = decide (p = 0)
  rw [lt_bool, lt_bool]
  by_cases h : p = 0
  · subst h; rfl
  · rcases Int.lt_or_gt_of_ne h with h1 | h1
    · simp [h1, h]
    · simp [h1, h]

theorem cell_eq_kit : ∀ t p, cell t p = Ruliology.CellularAutomata.Rule30Jen.cell t p := by
  intro t
  induction t with
  | zero => intro p; rw [cell_zero_eq]; rfl
  | succ t ih =>
    intro p
    show rule (cell t (LexLeanRuntime.subtract p 1)) (cell t p) (cell t (LexLeanRuntime.subtract p (-1))) = _
    rw [sub_one, sub_neg_one, ih, ih, ih]
    show bxor _ _ = xor _ _
    rw [bxor_eq]

theorem center_eq_kit (t : Nat) : center t = Ruliology.CellularAutomata.Rule30Prize.center t :=
  cell_eq_kit t 0

/-! ### Step 1: the kernel's power-of-two reuse -/

/-- The rule-60 operator. -/
def L (x : Int → Bool) : Int → Bool := fun p => xor (x (p - 1)) (x p)

def Lpow : Nat → (Int → Bool) → Int → Bool
  | 0, x => x
  | n + 1, x => L (Lpow n x)

theorem Lpow_add (m n : Nat) (x : Int → Bool) : Lpow (m + n) x = Lpow m (Lpow n x) := by
  induction m with
  | zero => simp [Lpow]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    show L (Lpow (m + n) x) = L (Lpow m (Lpow n x)); rw [ih]

theorem L_xor (x y : Int → Bool) (p : Int) :
    L (fun p => xor (x p) (y p)) p = xor (L x p) (L y p) := by
  show xor (xor (x (p - 1)) (y (p - 1))) (xor (x p) (y p)) = xor (xor (x (p - 1)) (x p)) (xor (y (p - 1)) (y p))
  cases x (p - 1) <;> cases x p <;> cases y (p - 1) <;> cases y p <;> rfl

theorem Lpow_xor (n : Nat) (x y : Int → Bool) :
    Lpow n (fun p => xor (x p) (y p)) = fun p => xor (Lpow n x p) (Lpow n y p) := by
  induction n with
  | zero => rfl
  | succ n ih => show L (Lpow n fun p => xor (x p) (y p)) = _; rw [ih]; funext p; exact L_xor _ _ p

theorem twopow_pos (k : Nat) : 0 < twopow k := by
  induction k with
  | zero => decide
  | succ k ih => rw [twopow_succ]; omega

/-- **Step 1.** `L^(2^k) x p = x p xor x (p - 2^k)`: the kernel reuses one module at every power
of two. -/
theorem freshman : ∀ k (x : Int → Bool) (p : Int), Lpow (twopow k) x p = xor (x p) (x (p - twopow k)) := by
  intro k
  induction k with
  | zero =>
    intro x p
    show xor (x (p - 1)) (x p) = xor (x p) (x (p - 1))
    cases x (p - 1) <;> cases x p <;> rfl
  | succ k ih =>
    intro x p
    rw [twopow_succ, Lpow_add, ih, ih, ih]
    rw [show p - twopow k - twopow k = p - ((twopow k + twopow k : Nat) : Int) by push_cast; omega]
    cases x p <;> cases x (p - twopow k) <;> cases x (p - ((twopow k + twopow k : Nat) : Int)) <;> rfl

/-! ### Step 2: the scale identity -/

theorem split_cell (s : Nat) (p : Int) :
    cell (s + 1) p = xor (L (cell s) p) (carry60 s p) := by
  show rule (cell s (LexLeanRuntime.subtract p 1)) (cell s p) (cell s (LexLeanRuntime.subtract p (-1))) = _
  unfold carry60 L
  rw [sub_one, sub_neg_one]
  show bxor (cell s (p - 1)) (cell s p || cell s (p + 1)) = _
  cases cell s (p - 1) <;> cases cell s p <;> cases cell s (p + 1) <;> rfl

theorem window_step (t0 m : Nat) (p : Int) :
    window60 t0 (m + 1) p = xor (L (window60 t0 m) p) (carry60 (t0 + m) p) := by
  rw [window60_step, sub_one, bxor_eq, bxor_eq]; rfl

/-- Duhamel: the pattern over a window is the kernel applied to the start plus the window
response. -/
theorem duhamel (t0 : Nat) : ∀ n p, cell (t0 + n) p = xor (Lpow n (cell t0) p) (window60 t0 n p) := by
  intro n
  induction n with
  | zero => intro p; show cell t0 p = xor (cell t0 p) false; cases cell t0 p <;> rfl
  | succ n ih =>
    intro p
    rw [show t0 + (n + 1) = (t0 + n) + 1 by omega, split_cell, window_step]
    have e : cell (t0 + n) = fun p => xor (Lpow n (cell t0) p) (window60 t0 n p) := funext ih
    rw [e, L_xor]
    show xor (xor (L (Lpow n (cell t0)) p) (L (window60 t0 n) p)) (carry60 (t0 + n) p) =
      xor (L (Lpow n (cell t0)) p) (xor (L (window60 t0 n) p) (carry60 (t0 + n) p))
    cases L (Lpow n (cell t0)) p <;> cases L (window60 t0 n) p <;> cases carry60 (t0 + n) p <;> rfl

/-- **Step 2.** The scale identity. -/
theorem scale (t0 k : Nat) (p : Int) :
    cell (t0 + twopow k) p = xor (xor (cell t0 p) (cell t0 (p - twopow k))) (window60 t0 (twopow k) p) := by
  rw [duhamel, freshman]

theorem scale_center (t k : Nat) :
    center (t + twopow k) = xor (xor (center t) (cell t (-(twopow k : Int)))) (window60 t (twopow k) 0) := by
  show cell (t + twopow k) 0 = xor (xor (cell t 0) (cell t (-(twopow k : Int)))) (window60 t (twopow k) 0)
  rw [scale, show (0 : Int) - twopow k = -(twopow k : Int) by omega]

/-- Left of the edge the pattern is white. -/
theorem cell_left_white (t : Nat) (p : Int) (h : p < -(t : Int)) : cell t p = false := by
  rw [cell_eq_kit]; exact Ruliology.CellularAutomata.Rule30Jen.cell_eq_false_of_lt t p h

/-! ### Step 3: the constraint of periodicity -/

/-- The center has period `P` from `T`. -/
def CenterPeriodic (T P : Nat) : Prop := ∀ t, T ≤ t → center (t + P) = center t

theorem center_mul {T P : Nat} (h : CenterPeriodic T P) : ∀ m t, T ≤ t → center (t + m * P) = center t := by
  intro m
  induction m with
  | zero => intro t _; simp
  | succ m ih =>
    intro t ht
    rw [show t + (m + 1) * P = (t + m * P) + P by rw [Nat.succ_mul]; omega, h _ (by omega), ih t ht]

theorem center_mod {T P : Nat} (hP : 0 < P) (h : CenterPeriodic T P) (t n : Nat) (ht : T ≤ t) :
    center (t + n) = center (t + n % P) := by
  have e : t + n = (t + n % P) + (n / P) * P := by
    have := Nat.div_add_mod n P; rw [Nat.mul_comm] at this; omega
  rw [e, center_mul h (n / P) _ (by omega)]

/-- **Step 3.** Under a periodic center, at every scale the left cell and the window response
together equal the center's difference at lag `2^k mod P`. -/
theorem periodic_scale {T P : Nat} (hP : 0 < P) (h : CenterPeriodic T P) (k t : Nat) (ht : T ≤ t) :
    xor (cell t (-(twopow k : Int))) (window60 t (twopow k) 0) =
      xor (center (t + twopow k % P)) (center t) := by
  have s := scale_center t k
  rw [center_mod hP h t (twopow k) ht] at s
  rw [s]
  cases center t <;> cases cell t (-(twopow k : Int)) <;> cases window60 t (twopow k) 0 <;>
    cases center (t + twopow k % P) <;> simp

/-- Inside the cone (`t < 2^k`) the left cell is white: the window response alone carries the
constraint. -/
theorem periodic_scale_cone {T P : Nat} (hP : 0 < P) (h : CenterPeriodic T P) (k t : Nat) (ht : T ≤ t)
    (hk : t < twopow k) :
    window60 t (twopow k) 0 = xor (center (t + twopow k % P)) (center t) := by
  have := periodic_scale hP h k t ht
  rw [cell_left_white t _ (by omega)] at this
  simpa using this

/-- The kit's Problem 1 in the core's terms. -/
theorem problem1_iff : Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔
    ∀ T P, 0 < P → ¬ CenterPeriodic T P := by
  unfold Ruliology.CellularAutomata.Rule30Prize.Problem1 Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic
  constructor
  · intro h T P hP hc
    exact h ⟨T, P, hP, fun t ht => by rw [← center_eq_kit, ← center_eq_kit]; exact hc t ht⟩
  · rintro h ⟨T, P, hP, hc⟩
    exact h T P hP fun t ht => by rw [center_eq_kit, center_eq_kit]; exact hc t ht

end Rule30UOR.Scale

namespace Rule30UOR.Scale

open Rule30UOR.Core

/-! ### Paper-facing forms -/

/-- `-(2^k)` as an integer position. -/
def negpow (k : Nat) : Int := -((twopow k : Nat) : Int)

/-- `2^k mod P`, the lag at scale `k` under period `P`. -/
def lag (P k : Nat) : Nat := twopow k % P

/-- The window response at the center: `window60 t (2^k) 0`. -/
def response (t k : Nat) : Bool := window60 t (twopow k) 0

theorem scale_center_paper (t k : Nat) :
    center (t + twopow k) = bxor (bxor (center t) (cell t (negpow k))) (response t k) := by
  rw [bxor_eq, bxor_eq]; exact scale_center t k

theorem periodic_scale_paper (T P : Nat) (hP : 0 < P) (h : CenterPeriodic T P) (k t : Nat) (ht : T ≤ t) :
    bxor (cell t (negpow k)) (response t k) = bxor (center (t + lag P k)) (center t) := by
  rw [bxor_eq, bxor_eq]; exact periodic_scale hP h k t ht

theorem periodic_scale_cone_paper (T P : Nat) (hP : 0 < P) (h : CenterPeriodic T P) (k t : Nat)
    (ht : T ≤ t) (hk : t < twopow k) :
    response t k = bxor (center (t + lag P k)) (center t) := by
  rw [bxor_eq]; exact periodic_scale_cone hP h k t ht hk

/-- Problem 1 as the core states it. -/
def NoPeriod : Prop := ∀ T P, 0 < P → ¬ CenterPeriodic T P

theorem problem1_of_noPeriod (h : NoPeriod) : Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff.2 h
theorem noPeriod_of_problem1 (h : Ruliology.CellularAutomata.Rule30Prize.Problem1) : NoPeriod :=
  problem1_iff.1 h

end Rule30UOR.Scale

namespace Rule30UOR.Scale
open Rule30UOR.Core
theorem window_step_paper (t0 m : Nat) (p : Int) :
    window60 t0 (Nat.succ m) p = bxor (bxor (window60 t0 m (leftOf p)) (window60 t0 m p)) (carry60 (t0 + m) p) :=
  window60_step t0 m p
end Rule30UOR.Scale

namespace Rule30UOR.Scale

open Rule30UOR.Core

/-! ### The split of the window response: left half and masked column 1

Carries at positions `≥ 1` never reach position `0` (the kernel moves rightward), and the carries
at position `0`, `!center s && cell s 1`, reach it with coefficient `1` at every step. So the
window response at the center is the response to the left-half carries (positions `≤ -1`) plus
the parity of the masked column-1 count over the window. -/

/-- The left-half carries. -/
def carryL (s : Nat) (p : Int) : Bool := if p < 0 then carry60 s p else false

/-- The window response to the left-half carries alone. -/
def leftwin (t0 : Nat) : Nat → Int → Bool
  | 0 => fun _ => false
  | m + 1 => fun p => xor (L (leftwin t0 m) p) (carryL (t0 + m) p)

/-- The masked column-1 count over the window, mod 2. -/
def maskcount (t0 : Nat) : Nat → Bool
  | 0 => false
  | m + 1 => xor (maskcount t0 m) (carry60 (t0 + m) 0)

/-- The window response at positions `≤ 0` ignores carries at positions `≥ 1`; at positions
`≤ -1` it is the left response alone. -/
theorem window_left (t0 : Nat) : ∀ m p, p < 0 → window60 t0 m p = leftwin t0 m p := by
  intro m
  induction m with
  | zero => intro p _; rfl
  | succ m ih =>
    intro p hp
    rw [window_step]
    show _ = xor (L (leftwin t0 m) p) (carryL (t0 + m) p)
    unfold L carryL
    rw [if_pos hp, ih (p - 1) (by omega), ih p hp]

/-- **The split.** -/
theorem window_split (t0 : Nat) : ∀ m, window60 t0 m 0 = xor (leftwin t0 m 0) (maskcount t0 m) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [window_step]
    show xor (xor (window60 t0 m (0 - 1)) (window60 t0 m 0)) (carry60 (t0 + m) 0) =
      xor (xor (xor (leftwin t0 m (0 - 1)) (leftwin t0 m 0)) (carryL (t0 + m) 0))
        (xor (maskcount t0 m) (carry60 (t0 + m) 0))
    rw [window_left t0 m (0 - 1) (by omega), ih]
    unfold carryL; rw [if_neg (by omega)]
    cases leftwin t0 m (0 - 1) <;> cases leftwin t0 m 0 <;> cases maskcount t0 m <;>
      cases carry60 (t0 + m) 0 <;> rfl

/-- The masked count is the parity of `!center s && cell s 1` over the window. -/
theorem maskcount_step (t0 m : Nat) :
    maskcount t0 (m + 1) = xor (maskcount t0 m) ((!center (t0 + m)) && cell (t0 + m) 1) := rfl

/-- **Step 3, split form.** Under a periodic center, inside the cone, the masked column-1 parity
over each dyadic window is fixed by the left response and the center's phase. -/
theorem periodic_mask {T P : Nat} (hP : 0 < P) (h : CenterPeriodic T P) (k t : Nat) (ht : T ≤ t)
    (hk : t < twopow k) :
    maskcount t (twopow k) = xor (leftwin t (twopow k) 0) (xor (center (t + twopow k % P)) (center t)) := by
  have e := periodic_scale_cone hP h k t ht hk
  rw [window_split] at e
  rw [← e]
  cases leftwin t (twopow k) 0 <;> cases maskcount t (twopow k) <;> rfl

end Rule30UOR.Scale

namespace Rule30UOR.Scale
open Rule30UOR.Core
/-- Paper-facing: the left response at the center and the masked parity at scale `k`. -/
def leftresponse (t k : Nat) : Bool := leftwin t (twopow k) 0
def maskparity (t k : Nat) : Bool := maskcount t (twopow k)

theorem split_paper (t k : Nat) : response t k = bxor (leftresponse t k) (maskparity t k) := by
  rw [bxor_eq]; exact window_split t (twopow k)

theorem periodic_mask_paper (T P : Nat) (hP : 0 < P) (h : CenterPeriodic T P) (k t : Nat) (ht : T ≤ t)
    (hk : t < twopow k) :
    maskparity t k = bxor (leftresponse t k) (bxor (center (t + lag P k)) (center t)) := by
  rw [bxor_eq, bxor_eq]; exact periodic_mask hP h k t ht hk
end Rule30UOR.Scale

namespace Rule30UOR.Scale
theorem lt_bool_nat (p q : Nat) : LexLeanCollections.lessThan p q = decide (p < q) := by
  show (match compareOfLessAndEq p q with | Ordering.lt => true | _ => false) = _
  unfold compareOfLessAndEq
  by_cases h : p < q
  · simp [h]
  · by_cases e : p = q
    · simp [e]
    · simp [h, e]
end Rule30UOR.Scale
