module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30 from a single white cell, and rule 135

Two single-seed patterns are column `-1` of the usual rule-30 pattern in disguise.

* `cellW_succ`: rule 30 started from a single white cell on an all-black background is, after
  one step, a single black cell at position `1`: `cellW (t + 1) p = cell t (p - 1)`. So its
  center column at time `t + 1` is column `-1` of the usual pattern at time `t`.
* `cell135_succ`: rule 135 (`!left xor (center && right)`, the black-white conjugate of rule 30)
  from a single black cell is, from step `1` on, the usual rule-30 pattern shifted one step and
  one cell and complemented: `cell135 (t + 1) p = !cell t (p - 1)`. So its center column at time
  `t + 1` is `!cell t (-1)`.
* `problem1_black_or_white`, `problem1_30_or_135`: by Jen's theorem (`Rule30Jen.jen`, columns `0`
  and `-1` are not both eventually periodic), **the center column of rule 30 from a single black
  cell or the center column from a single white cell is not eventually periodic**, and likewise
  for rule 30 and rule 135 from a single black cell. Which one is not is left open.

By mirror symmetry, rule 86 (the mirror image of rule 30) and rule 149 (that of rule 135) have
the same single-seed center columns as rules 30 and 135; this is not formalized here.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242, for the
reduction to columns `0` and `-1`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WhiteSeed

open Rule30Jen

/-! ### Rule 30 from a single white cell -/

/-- Rule 30 from a single white cell at `0` on an all-black background. -/
def cellW : Nat → Int → Bool
  | 0, p => !decide (p = 0)
  | t + 1, p => rule (cellW t (p - 1)) (cellW t p) (cellW t (p + 1))

/-- After one step the white seed has become a single black cell at position `1`. -/
theorem cellW_succ : ∀ (t : Nat) (p : Int), cellW (t + 1) p = cell t (p - 1)
  | 0, p => by
    show rule (!decide (p - 1 = 0)) (!decide (p = 0)) (!decide (p + 1 = 0)) = decide (p - 1 = 0)
    rcases (show p = 1 ∨ p = 0 ∨ p = -1 ∨ (p ≠ 1 ∧ p ≠ 0 ∧ p ≠ -1) by omega) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have e1 : decide (p - 1 = 0) = false := decide_eq_false (by omega)
      have e2 : decide (p = 0) = false := decide_eq_false (by omega)
      have e3 : decide (p + 1 = 0) = false := decide_eq_false (by omega)
      rw [e1, e2, e3]; rfl
  | t + 1, p => by
    show rule (cellW (t + 1) (p - 1)) (cellW (t + 1) p) (cellW (t + 1) (p + 1)) =
      rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1))
    rw [cellW_succ t (p - 1), cellW_succ t p, cellW_succ t (p + 1),
      show p + 1 - 1 = p by omega, show p - 1 + 1 = p by omega]

/-- **Black seed or white seed.** The center column of rule 30 from a single black cell and the
center column from a single white cell on a black background are not both eventually
periodic. -/
theorem problem1_black_or_white :
    ¬ (EventuallyPeriodic (fun t => cell t 0) ∧ EventuallyPeriodic (fun t => cellW t 0)) := by
  rintro ⟨h30, ⟨T, P, hP, hW⟩⟩
  have hm1 : EventuallyPeriodic (fun t => cell t (-1)) := by
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h := hW (t + 1) (by omega)
    simp only [] at h
    rw [show t + 1 + P = (t + P) + 1 by omega, cellW_succ, cellW_succ] at h
    exact h
  exact jen 0 (-1) (by omega) ⟨h30, hm1⟩

/-! ### Rule 135 -/

/-- Rule 135: `!left xor (center && right)`. -/
def rule135 (a b c : Bool) : Bool := xor (!a) (b && c)

/-- Rule 135 from a single black cell at position `0`. -/
def cell135 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule135 (cell135 t (p - 1)) (cell135 t p) (cell135 t (p + 1))

theorem cell135_succ : ∀ (t : Nat) (p : Int), cell135 (t + 1) p = !cell t (p - 1)
  | 0, p => by
    show rule135 (decide (p - 1 = 0)) (decide (p = 0)) (decide (p + 1 = 0)) = !decide (p - 1 = 0)
    rcases (show p = 1 ∨ p = 0 ∨ p = -1 ∨ (p ≠ 1 ∧ p ≠ 0 ∧ p ≠ -1) by omega) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have e1 : decide (p - 1 = 0) = false := decide_eq_false (by omega)
      have e2 : decide (p = 0) = false := decide_eq_false (by omega)
      have e3 : decide (p + 1 = 0) = false := decide_eq_false (by omega)
      rw [e1, e2, e3]; rfl
  | t + 1, p => by
    show rule135 (cell135 (t + 1) (p - 1)) (cell135 (t + 1) p) (cell135 (t + 1) (p + 1)) =
      !rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1))
    rw [cell135_succ t (p - 1), cell135_succ t p, cell135_succ t (p + 1),
      show p + 1 - 1 = p by omega, show p - 1 + 1 = p by omega]
    cases cell t (p - 1 - 1) <;> cases cell t (p - 1) <;> cases cell t p <;> rfl

theorem center135_succ (t : Nat) : cell135 (t + 1) 0 = !cell t (-1) := by
  rw [cell135_succ]; rfl

/-- **Rule 30 or rule 135.** The single-seed center columns of rule 30 and rule 135 are not both
eventually periodic. -/
theorem problem1_30_or_135 :
    ¬ (EventuallyPeriodic (fun t => cell t 0) ∧ EventuallyPeriodic (fun t => cell135 t 0)) := by
  rintro ⟨h30, ⟨T, P, hP, h135⟩⟩
  have hm1 : EventuallyPeriodic (fun t => cell t (-1)) := by
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have e : cell135 ((t + P) + 1) 0 = cell135 (t + 1) 0 := by
      have h := h135 (t + 1) (by omega)
      simp only [] at h
      rw [show t + 1 + P = (t + P) + 1 by omega] at h
      exact h
    rw [center135_succ, center135_succ] at e
    show cell (t + P) (-1) = cell t (-1)
    revert e
    cases cell (t + P) (-1) <;> cases cell t (-1) <;> simp
  exact jen 0 (-1) (by omega) ⟨h30, hm1⟩

end Rule30WhiteSeed
end Ruliology.CellularAutomata
