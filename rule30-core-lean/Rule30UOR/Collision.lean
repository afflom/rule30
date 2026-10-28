module

public import Ruliology.CellularAutomata.Rule30XorRigidity
public import Rule30UOR.TemporalDefect
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Finite-horizon carry collisions

This quantitative version of XOR rigidity assumes absence of adjacent cross-carry only
in a finite rectangle. Incompatible paired colors force a collision within that rectangle.
The theorem retains the actual Rule 30 updates of both histories, not just their difference.
-/

@[expose] public section

namespace Rule30UOR.Collision

open Ruliology.CellularAutomata
open Rule30XorRigidity (Actual)
open Rule30XorRigidity.HalfLine (Good good_self middle_zero gap_two gap_large)

/-- If adjacent cross-carries vanish for `d + 1` time slices on the interval from `p`
through `p + d` (including the pair starting at its right endpoint), then the endpoint
colors at the initial slice are compatible. Coordinates are sheared as in XOR rigidity. -/
theorem finite_distant_good (A B : Nat → Int → Bool) (ha : Actual A) (hb : Actual B)
    (d : Nat) : ∀ (t : Nat) (p : Int),
    (∀ s : Nat, s ≤ d → ∀ i : Int, p ≤ i → i ≤ p + (d : Int) →
      Good (A (t + s) i) (B (t + s) i) (A (t + s) (i + 1)) (B (t + s) (i + 1))) →
    Good (A t p) (B t p) (A t (p + (d : Int))) (B t (p + (d : Int))) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro t p h
    by_cases hd0 : d = 0
    · subst d
      simpa using good_self (A t p) (B t p)
    by_cases hd1 : d = 1
    · subst d
      simpa using h 0 (by omega) p (by omega) (by omega)
    apply Classical.byContradiction
    intro bad
    have mid : ∀ k : Nat, 0 < k → k < d →
        A t (p + (k : Int)) = false ∧ B t (p + (k : Int)) = false := by
      intro k hk hkd
      have hl := ih k hkd t p (fun s hs i hi hix => h s (by omega) i hi (by omega))
      have hr := ih (d - k) (by omega) t (p + (k : Int))
        (fun s hs i hi hix => h s (by omega) i (by omega) (by omega))
      rw [show p + (k : Int) + ((d - k : Nat) : Int) = p + (d : Int) by omega] at hr
      exact middle_zero _ _ _ _ _ _ bad hl hr
    by_cases hd2 : d = 2
    · subst d
      obtain ⟨az, bz⟩ := mid 1 (by omega) (by omega)
      have hn := ih 1 (by omega) (t + 1) p (by
        intro s hs i hi hix
        have hh := h (s + 1) (by omega) i hi (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh)
      have hr := h 0 (by omega) (p + 2) (by omega) (by omega)
      simp only [Nat.add_zero] at hr
      change A t (p + 1) = false at az
      change B t (p + 1) = false at bz
      change Good (A (t + 1) p) (B (t + 1) p) (A (t + 1) (p + 1)) (B (t + 1) (p + 1)) at hn
      rw [show p + 2 + 1 = p + 3 by omega] at hr
      rw [ha t p, hb t p, ha t (p + 1), hb t (p + 1), az, bz,
        show p + 1 + 1 = p + 2 by omega, show p + 1 + 2 = p + 3 by omega] at hn
      exact bad (gap_two _ _ _ _ _ _ hr hn)
    · obtain ⟨a1, b1⟩ := mid 1 (by omega) (by omega)
      obtain ⟨a2, b2⟩ := mid 2 (by omega) (by omega)
      change A t (p + 1) = false at a1
      change B t (p + 1) = false at b1
      change A t (p + 2) = false at a2
      change B t (p + 2) = false at b2
      obtain ⟨az, bz⟩ := mid (d - 2) (by omega) (by omega)
      obtain ⟨az1, bz1⟩ := mid (d - 1) (by omega) (by omega)
      have hn := ih (d - 2) (by omega) (t + 1) p (by
        intro s hs i hi hix
        have hh := h (s + 1) (by omega) i hi (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh)
      rw [ha t p, hb t p, ha t (p + ((d - 2 : Nat) : Int)),
        hb t (p + ((d - 2 : Nat) : Int)),
        show p + ((d - 2 : Nat) : Int) + 1 = p + ((d - 1 : Nat) : Int) by omega,
        show p + ((d - 2 : Nat) : Int) + 2 = p + (d : Int) by omega,
        a1, b1, a2, b2, az, bz, az1, bz1] at hn
      exact bad (gap_large _ _ _ _ hn)

/-- Constructive witness location (by classical contraposition), with explicit time and
space bounds. No periodicity or support assumption is needed. -/
theorem finite_collision (A B : Nat → Int → Bool) (ha : Actual A) (hb : Actual B)
    (t : Nat) (p : Int) (d : Nat)
    (hbad : ¬ Good (A t p) (B t p) (A t (p + (d : Int))) (B t (p + (d : Int)))) :
    ∃ s : Nat, s ≤ d ∧ ∃ i : Int, p ≤ i ∧ i ≤ p + (d : Int) ∧
      ¬ Good (A (t + s) i) (B (t + s) i)
        (A (t + s) (i + 1)) (B (t + s) (i + 1)) := by
  apply Classical.byContradiction
  intro hn
  apply hbad
  apply finite_distant_good A B ha hb d t p
  intro s hs i hi hix
  exact Classical.byContradiction (fun hh => hn ⟨s, hs, i, hi, hix, hh⟩)

open Rule30Jen Rule30Prize

/-- Adjacent determinant of two time-shifted rows, in physical coordinates. -/
def collision (Q t : Nat) (p : Int) : Bool :=
  xor (cell t p && cell (t + Q) (p + 1)) (cell t (p + 1) && cell (t + Q) p)

theorem collision_iff (Q t : Nat) (p : Int) :
    collision Q t p = true ↔
      ¬ Good (cell t p) (cell (t + Q) p) (cell t (p + 1)) (cell (t + Q) (p + 1)) := by
  unfold collision Good
  cases cell t p <;> cases cell (t + Q) p <;>
    cases cell t (p + 1) <;> cases cell (t + Q) (p + 1) <;> decide

private def history (T : Nat) : Nat → Int → Bool := fun s p => cell (T + s) p

private theorem history_standard (T : Nat) : Rule30XorRigidity.Standard (history T) := by
  intro s p
  change cell (T + (s + 1)) p = _
  rw [show T + (s + 1) = (T + s) + 1 by omega]
  rfl

/-- Incompatible columns separated by `d` force a temporal carry collision within `d`
steps, in the explicitly bounded right-moving rectangle. -/
theorem temporal_collision_of_incompatible (Q T : Nat) (p : Int) (d : Nat)
    (hbad : ¬ Good (cell T p) (cell (T + Q) p)
      (cell T (p + (d : Int))) (cell (T + Q) (p + (d : Int)))) :
    ∃ s : Nat, s ≤ d ∧ ∃ x : Int, p + (s : Int) ≤ x ∧
      x ≤ p + (d : Int) + (s : Int) ∧ collision Q (T + s) x = true := by
  let A := Rule30XorRigidity.shear (history T)
  let B := Rule30XorRigidity.shear (history (T + Q))
  have ha : Actual A := (Rule30XorRigidity.shear_actual_iff _).mpr (history_standard T)
  have hb : Actual B := (Rule30XorRigidity.shear_actual_iff _).mpr (history_standard (T + Q))
  have hbad' : ¬ Good (A 0 p) (B 0 p) (A 0 (p + (d : Int))) (B 0 (p + (d : Int))) := by
    simpa [A, B, Rule30XorRigidity.shear, history] using hbad
  obtain ⟨s, hs, i, hi, hix, hh⟩ := finite_collision A B ha hb 0 p d hbad'
  refine ⟨s, hs, (s : Int) + i, by omega, by omega, (collision_iff Q (T + s) _).mpr ?_⟩
  simpa only [A, B, Rule30XorRigidity.shear, history, Nat.zero_add,
    show T + Q + s = T + s + Q by omega, Int.add_assoc] using hh

/-- The two distinct left edges force a collision within every `Q + 1` time slices.
The witness lies near the moving left edge, not necessarily near the center. -/
theorem left_edge_collision (Q T : Nat) (hQ : 0 < Q) :
    ∃ s : Nat, s ≤ Q ∧ ∃ x : Int,
      -((T + Q : Nat) : Int) + (s : Int) ≤ x ∧ x ≤ -(T : Int) + (s : Int) ∧
      collision Q (T + s) x = true := by
  have hbad : ¬ Good (cell T (-((T + Q : Nat) : Int))) (cell (T + Q) (-((T + Q : Nat) : Int)))
      (cell T (-((T + Q : Nat) : Int) + (Q : Int)))
      (cell (T + Q) (-((T + Q : Nat) : Int) + (Q : Int))) := by
    rw [cell_eq_false_of_lt T _ (by omega), cell_left_edge,
      show -((T + Q : Nat) : Int) + (Q : Int) = -(T : Int) by omega, cell_left_edge]
    simp [Good]
  have hh := temporal_collision_of_incompatible Q T (-((T + Q : Nat) : Int)) Q hbad
  simpa only [show -((T + Q : Nat) : Int) + (Q : Int) = -(T : Int) by omega] using hh

end Rule30UOR.Collision
