module

public import Rule30UOR.Constructive
public import Ruliology.CellularAutomata.Rule30Prize
public import Rule30UOR.Core

/-!
# Rule 30 projected onto its nearest known rules

Rule 30 is at distance `2` from four affine rules and from no closer one (LexLean core:
`deep_hole`, `nearest_affine`): rules 150, 90, 60, 15. Against each, it differs by one carry, and
the four carries are the four minterms of `(c, r)`, orthogonal and covering (`split150`, `split90`,
`split60`, `split15`, `carries_orthogonal`, `carries_cover`).

For each neighbour `k` the rule-30 pattern is the neighbour's own evolution of the seed plus the
neighbour's evolution of the rule-30 carries (Duhamel), with the accumulator defined by its law:

  `acc (t + 1) = L_k (acc t) xor q_k t`,   `cell t = L_k^t seed xor acc t`.

Proved here for the two one-sided neighbours.
* Rule 60 (`L x p = x (p - 1) xor x p`, carry `!c && r`): `cell_eq_proj60`; the neighbour's
  center is always black (`lin60_center`), so **Problem 1 holds exactly when the center of the
  carry response `acc60 t 0` is not eventually periodic** (`problem1_iff_resp60`).
* Rule 15 (`A x p = !x (p - 1)`, carry `!c && !r`): `cell_eq_proj15`, `problem1_iff_resp15`.
* `resp_relation`: the two responses, driven by orthogonal carries, differ by an eventually
  periodic sequence.
-/

@[expose] public section

namespace Rule30UOR.Project

open Ruliology.CellularAutomata Rule30Jen Rule30Prize

/-- The seed as a configuration. -/
def seed (p : Int) : Bool := decide (p = 0)

theorem cell_zero (p : Int) : cell 0 p = seed p := rfl

/-! ### Rule 60 -/

def L60 (x : Int → Bool) : Int → Bool := fun p => xor (x (p - 1)) (x p)

def pow60 : Nat → (Int → Bool) → Int → Bool
  | 0, x => x
  | n + 1, x => L60 (pow60 n x)

/-- The rule-30 carry against rule 60: `!c && r`. -/
def q60 (s : Nat) (p : Int) : Bool := (!cell s p) && cell s (p + 1)

/-- The Duhamel accumulator for rule 60, defined by its law. -/
def acc60 : Nat → Int → Bool
  | 0 => fun _ => false
  | t + 1 => fun p => xor (L60 (acc60 t) p) (q60 t p)

theorem L60_xor (x y : Int → Bool) (p : Int) :
    L60 (fun p => xor (x p) (y p)) p = xor (L60 x p) (L60 y p) := by
  show xor (xor (x (p - 1)) (y (p - 1))) (xor (x p) (y p)) = xor (xor (x (p - 1)) (x p)) (xor (y (p - 1)) (y p))
  cases x (p - 1) <;> cases x p <;> cases y (p - 1) <;> cases y p <;> rfl

theorem pow60_succ (n : Nat) (x : Int → Bool) : pow60 (n + 1) x = L60 (pow60 n x) := rfl

/-- **The rule-60 projection.** -/
theorem cell_eq_proj60 : ∀ t p, cell t p = xor (pow60 t seed p) (acc60 t p) := by
  intro t
  induction t with
  | zero => intro p; show cell 0 p = xor (seed p) false; rw [cell_zero]; cases seed p <;> rfl
  | succ t ih =>
    intro p
    have hcell : cell (t + 1) p = xor (L60 (fun p => cell t p) p) (q60 t p) := by
      show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) =
        xor (xor (cell t (p - 1)) (cell t p)) ((!cell t p) && cell t (p + 1))
      unfold rule
      cases cell t (p - 1) <;> cases cell t p <;> cases cell t (p + 1) <;> rfl
    rw [hcell]
    have e : (fun p => cell t p) = (fun p => xor (pow60 t seed p) (acc60 t p)) := funext ih
    rw [e, L60_xor]
    show _ = xor (L60 (pow60 t seed) p) (xor (L60 (acc60 t) p) (q60 t p))
    cases L60 (pow60 t seed) p <;> cases L60 (acc60 t) p <;> cases q60 t p <;> rfl

theorem lin60_left : ∀ t p, p < 0 → pow60 t seed p = false := by
  intro t
  induction t with
  | zero => intro p hp; simp [pow60, seed]; omega
  | succ t ih => intro p hp; simp only [pow60, L60, ih (p - 1) (by omega), ih p hp]; rfl

/-- The known rule's center: rule 60 from the seed is black on the center at every time. -/
theorem lin60_center : ∀ t, pow60 t seed 0 = true := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp only [pow60, L60, lin60_left t (0 - 1) (by omega), ih]; rfl

/-- The center is the complement of the carry response. -/
theorem center_eq_resp60 (t : Nat) : center t = !acc60 t 0 := by
  show cell t 0 = _
  rw [cell_eq_proj60, lin60_center]; cases acc60 t 0 <;> rfl

theorem ep_not {f : Nat → Bool} : EventuallyPeriodic (fun t => !f t) ↔ EventuallyPeriodic f := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun t ht => by have := h t ht; simp only at this; cases e1 : f (t + P) <;> cases e2 : f t <;> simp_all⟩
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun t ht => by simp only [h t ht]⟩

/-- **Problem 1 projected onto rule 60.** -/
theorem problem1_iff_resp60 : Problem1 ↔ ¬ EventuallyPeriodic (fun t => acc60 t 0) := by
  have e : center = fun t => !acc60 t 0 := funext center_eq_resp60
  unfold Problem1; rw [e, ep_not]

/-! ### Rule 15 -/

/-- The affine neighbour rule 15: `A x p = !x (p - 1)`. -/
def A15 (x : Int → Bool) : Int → Bool := fun p => !x (p - 1)

def pow15 : Nat → (Int → Bool) → Int → Bool
  | 0, x => x
  | n + 1, x => A15 (pow15 n x)

/-- The shift, the linear part of `A15`. -/
def S (x : Int → Bool) : Int → Bool := fun p => x (p - 1)

/-- The rule-30 carry against rule 15: `!c && !r`. -/
def q15 (s : Nat) (p : Int) : Bool := (!cell s p) && !cell s (p + 1)

def acc15 : Nat → Int → Bool
  | 0 => fun _ => false
  | t + 1 => fun p => xor (S (acc15 t) p) (q15 t p)

/-- **The rule-15 projection.** -/
theorem cell_eq_proj15 : ∀ t p, cell t p = xor (pow15 t seed p) (acc15 t p) := by
  intro t
  induction t with
  | zero => intro p; show cell 0 p = xor (seed p) false; rw [cell_zero]; cases seed p <;> rfl
  | succ t ih =>
    intro p
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = xor (!pow15 t seed (p - 1))
      (xor (acc15 t (p - 1)) (q15 t p))
    rw [ih (p - 1)]
    unfold q15 rule
    cases pow15 t seed (p - 1) <;> cases acc15 t (p - 1) <;> cases cell t p <;>
      cases cell t (p + 1) <;> rfl

/-- Rule 15 from the seed: the seed shifted right, over a background that flips each step. -/
theorem lin15_gen : ∀ t p, pow15 t seed p = xor (seed (p - t)) (decide (t % 2 = 1)) := by
  intro t
  induction t with
  | zero => intro p; simp [pow15]
  | succ t ih =>
    intro p
    show (!pow15 t seed (p - 1)) = _
    rw [ih, show p - 1 - (t : Int) = p - ((t + 1 : Nat) : Int) by omega]
    by_cases h : t % 2 = 1
    · have h' : ¬ (t + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (t + 1) % 2 = 1 := by omega
      simp [h, h']

/-- After time `0`, the known rule's center is black exactly at odd times. -/
theorem lin15_center (t : Nat) (ht : 1 ≤ t) : pow15 t seed 0 = decide (t % 2 = 1) := by
  rw [lin15_gen]
  have hs : seed (0 - (t : Int)) = false := by
    unfold seed
    exact decide_eq_false (by cfomega)
  rw [hs]; cases decide (t % 2 = 1) <;> rfl

theorem center_eq_resp15 (t : Nat) (ht : 1 ≤ t) :
    center t = xor (decide (t % 2 = 1)) (acc15 t 0) := by
  show cell t 0 = _
  rw [cell_eq_proj15, lin15_center t ht]

theorem ep_congr {f g : Nat → Bool} {N : Nat} (h : ∀ t, N ≤ t → f t = g t) :
    EventuallyPeriodic f ↔ EventuallyPeriodic g := by
  constructor
  · rintro ⟨T, P, hP, hf⟩
    exact ⟨max T N, P, hP, fun t ht => by
      rw [← h t (by omega), ← h (t + P) (by omega)]; exact hf t (by omega)⟩
  · rintro ⟨T, P, hP, hg⟩
    exact ⟨max T N, P, hP, fun t ht => by
      rw [h t (by omega), h (t + P) (by omega)]; exact hg t (by omega)⟩

theorem ep_xor_two {f : Nat → Bool} :
    EventuallyPeriodic (fun t => xor (decide (t % 2 = 1)) (f t)) ↔ EventuallyPeriodic f := by
  have hg : ∀ k s, decide ((s + 2 * k) % 2 = 1) = decide (s % 2 = 1) := by
    intro k s; congr 1; apply propext; cfomega
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, 2 * P, by cfomega, fun t ht => ?_⟩
    have h1 := h t ht
    have h2 := h (t + P) (by cfomega)
    simp only at h1 h2
    rw [show t + P + P = t + 2 * P by cfomega] at h2
    have e := hg P t
    revert h1 h2 e
    cases decide ((t + 2 * P) % 2 = 1) <;> cases decide (t % 2 = 1) <;>
      cases decide ((t + P) % 2 = 1) <;> cases f (t + 2 * P) <;> cases f t <;>
      cases f (t + P) <;> simp
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, 2 * P, by cfomega, fun t ht => ?_⟩
    have hf2 : f (t + 2 * P) = f t := by
      rw [show t + 2 * P = (t + P) + P by cfomega, h (t + P) (by cfomega), h t ht]
    show xor (decide ((t + 2 * P) % 2 = 1)) (f (t + 2 * P)) = xor (decide (t % 2 = 1)) (f t)
    rw [hg P t, hf2]

/-- **Problem 1 projected onto rule 15.** -/
theorem problem1_iff_resp15 : Problem1 ↔ ¬ EventuallyPeriodic (fun t => acc15 t 0) := by
  unfold Problem1
  rw [ep_congr (N := 1) (g := fun t => xor (decide (t % 2 = 1)) (acc15 t 0))
    (fun t ht => center_eq_resp15 t ht), ep_xor_two]

/-! ### Orthogonal carries, one center -/

/-- The responses to the two orthogonal carries differ by the alternating sequence. -/
theorem resp_relation (t : Nat) (ht : 1 ≤ t) :
    xor (acc60 t 0) (acc15 t 0) = decide (t % 2 = 0) := by
  have h1 := center_eq_resp60 t
  have h2 := center_eq_resp15 t ht
  rw [h1] at h2
  have hd : decide (t % 2 = 0) = !decide (t % 2 = 1) := by
    by_cases h : t % 2 = 1
    · have : ¬ t % 2 = 0 := by omega
      simp [h, this]
    · have : t % 2 = 0 := by omega
      simp [h, this]
  rw [hd]
  revert h2; cases acc60 t 0 <;> cases acc15 t 0 <;> cases decide (t % 2 = 1) <;> simp

/-! ### Paper-facing forms -/

/-- The carry responses read at the center. -/
def resp60 (t : Nat) : Bool := acc60 t 0
def resp15 (t : Nat) : Bool := acc15 t 0

/-- Parity of time. -/
def even (t : Nat) : Bool := decide (t % 2 = 0)

def Resp60Aperiodic : Prop := ¬ EventuallyPeriodic resp60
def Resp15Aperiodic : Prop := ¬ EventuallyPeriodic resp15

theorem resp60_of_problem1 (h : Problem1) : Resp60Aperiodic := problem1_iff_resp60.1 h
theorem problem1_of_resp60 (h : Resp60Aperiodic) : Problem1 := problem1_iff_resp60.2 h
theorem resp15_of_problem1 (h : Problem1) : Resp15Aperiodic := problem1_iff_resp15.1 h
theorem problem1_of_resp15 (h : Resp15Aperiodic) : Problem1 := problem1_iff_resp15.2 h

theorem center_resp60 (t : Nat) : center t = !resp60 t := center_eq_resp60 t

theorem resp_relation_bxor (t : Nat) (ht : 1 ≤ t) :
    Rule30UOR.Core.bxor (resp60 t) (resp15 t) = even t := by
  have h := resp_relation t ht
  unfold resp60 resp15 even
  rw [← h]; unfold Rule30UOR.Core.bxor; cases acc60 t 0 <;> cases acc15 t 0 <;> rfl

end Rule30UOR.Project
