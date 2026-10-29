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


/-- A disagreement colour and a shared black colour, in either order. -/
private def Mixed (a b c d : Bool) : Prop :=
  (a ≠ b ∧ c = true ∧ d = true) ∨ (a = true ∧ b = true ∧ c ≠ d)

private theorem mixed_self (a b : Bool) : ¬ Mixed a b a b := by
  unfold Mixed
  cases a <;> cases b <;> decide

private theorem mixed_bad : ∀ a b c d : Bool, Mixed a b c d → ¬ Good a b c d := by
  unfold Mixed Good
  decide +kernel

private theorem mixed_middle : ∀ a b c d e f : Bool, Mixed a b e f →
    (c = false ∧ d = false) ∨ Mixed a b c d ∨ Mixed c d e f := by
  unfold Mixed
  decide +kernel

private theorem mixed_gap_two : ∀ a b c d e f : Bool, Mixed a b c d →
    ¬ Good (rule a false c) (rule b false d)
      (rule false c e) (rule false d f) := by
  unfold Mixed Good
  decide +kernel

private theorem cell_step (t : Nat) (p : Int) :
    cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl

/-- Mixed colours collide inside their initial spatial hull. A zero gap closes from
both ends; the time is at most half the initial distance. -/
private theorem mixed_collision (Q : Nat) : ∀ (d t : Nat) (p : Int),
    Mixed (cell t p) (cell (t + Q) p)
      (cell t (p + (d : Int))) (cell (t + Q) (p + (d : Int))) →
    ∃ s : Nat, 2 * s ≤ d ∧ ∃ x : Int, p ≤ x ∧ x < p + (d : Int) ∧
      collision Q (t + s) x = true := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro t p hm
    by_cases hd0 : d = 0
    · subst d
      simp only [Int.ofNat_zero, Int.add_zero] at hm
      exact (mixed_self _ _ hm).elim
    by_cases hd1 : d = 1
    · subst d
      refine ⟨0, by omega, p, by omega, by omega, ?_⟩
      apply (collision_iff Q t p).2
      exact mixed_bad _ _ _ _ (by simpa using hm)
    apply Classical.byContradiction
    intro hn
    have mid : ∀ x : Int, p < x → x < p + (d : Int) →
        cell t x = false ∧ cell (t + Q) x = false := by
      intro x hx1 hx2
      let k := (x - p).toNat
      have hk : (k : Int) = x - p := Int.toNat_of_nonneg (by omega)
      rcases mixed_middle (cell t p) (cell (t + Q) p) (cell t x) (cell (t + Q) x)
        (cell t (p + (d : Int))) (cell (t + Q) (p + (d : Int))) hm with hz | hl | hr
      · exact hz
      · obtain ⟨s, hs, y, hy1, hy2, hc⟩ := ih k (by omega) t p (by
          simpa only [show p + (k : Int) = x by omega] using hl)
        exact (hn ⟨s, by omega, y, hy1, by omega, hc⟩).elim
      · obtain ⟨s, hs, y, hy1, hy2, hc⟩ := ih (d - k) (by omega) t x (by
          simpa only [show x + ((d - k : Nat) : Int) = p + (d : Int) by omega] using hr)
        exact (hn ⟨s, by omega, y, by omega, by omega, hc⟩).elim
    by_cases hd2 : d = 2
    · subst d
      obtain ⟨az, bz⟩ := mid (p + 1) (by omega) (by omega)
      have hc : collision Q (t + 1) (p + 1) = true := by
        apply (collision_iff Q (t + 1) (p + 1)).2
        rw [show t + 1 + Q = (t + Q) + 1 by omega,
          show p + 1 + 1 = p + 2 by omega,
          cell_step t (p + 1), cell_step (t + Q) (p + 1),
          cell_step t (p + 2), cell_step (t + Q) (p + 2),
          show p + 1 - 1 = p by omega, show p + 2 - 1 = p + 1 by omega,
          show p + 1 + 1 = p + 2 by omega, az, bz]
        exact mixed_gap_two _ _ _ _ _ _ (by simpa using hm)
      exact hn ⟨1, by omega, p + 1, by omega, by omega, hc⟩
    · obtain ⟨a1, b1⟩ := mid (p + 1) (by omega) (by omega)
      obtain ⟨a2, b2⟩ := mid (p + 2) (by omega) (by omega)
      obtain ⟨az, bz⟩ := mid (p + (d : Int) - 2) (by omega) (by omega)
      obtain ⟨az1, bz1⟩ := mid (p + (d : Int) - 1) (by omega) (by omega)
      have la : cell (t + 1) (p + 1) = cell t p := by
        rw [cell_step, show p + 1 - 1 = p by omega,
          show p + 1 + 1 = p + 2 by omega, a1, a2]
        simp [rule]
      have lb : cell (t + 1 + Q) (p + 1) = cell (t + Q) p := by
        rw [show t + 1 + Q = (t + Q) + 1 by omega, cell_step,
          show p + 1 - 1 = p by omega, show p + 1 + 1 = p + 2 by omega, b1, b2]
        simp [rule]
      have ra : cell (t + 1) (p + (d : Int) - 1) = cell t (p + (d : Int)) := by
        rw [cell_step, show p + (d : Int) - 1 - 1 = p + (d : Int) - 2 by omega,
          show p + (d : Int) - 1 + 1 = p + (d : Int) by omega, az, az1]
        simp [rule]
      have rb : cell (t + 1 + Q) (p + (d : Int) - 1) = cell (t + Q) (p + (d : Int)) := by
        rw [show t + 1 + Q = (t + Q) + 1 by omega, cell_step,
          show p + (d : Int) - 1 - 1 = p + (d : Int) - 2 by omega,
          show p + (d : Int) - 1 + 1 = p + (d : Int) by omega, bz, bz1]
        simp [rule]
      obtain ⟨s, hs, x, hx1, hx2, hc⟩ := ih (d - 2) (by omega) (t + 1) (p + 1) (by
        rw [show p + 1 + ((d - 2 : Nat) : Int) = p + (d : Int) - 1 by omega,
          la, lb, ra, rb]
        exact hm)
      exact hn ⟨s + 1, by omega, x, by omega, by omega, by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc⟩

/-- A left defect and a shared black center force a collision entirely to the left
of the center, within half the defect's distance. No periodicity is assumed. -/
theorem left_collision_of_defect_and_black (Q t k : Nat)
    (hd : Rule30UOR.TemporalDefect.defect Q t (-(k : Int)) = true)
    (ha : center t = true) (hb : center (t + Q) = true) :
    ∃ s : Nat, 2 * s ≤ k ∧ ∃ x : Int, -(k : Int) ≤ x ∧ x < 0 ∧
      collision Q (t + s) x = true := by
  have hm : Mixed (cell t (-(k : Int))) (cell (t + Q) (-(k : Int)))
      (cell t (-(k : Int) + (k : Int))) (cell (t + Q) (-(k : Int) + (k : Int))) := by
    left
    refine ⟨?_, ?_, ?_⟩
    · intro he
      simp [Rule30UOR.TemporalDefect.defect, Rule30UOR.TemporalDefect.difference, he] at hd
    · simpa only [show -(k : Int) + (k : Int) = 0 by omega, center] using ha
    · simpa only [show -(k : Int) + (k : Int) = 0 by omega, center] using hb
  simpa only [show -(k : Int) + (k : Int) = 0 by omega] using mixed_collision Q k t (-(k : Int)) hm

end Rule30UOR.Collision
