module

public import Rule30UOR.DefectFront
public import Rule30UOR.Scale

/-!
# Central localization of collision sources

Statements are authored in `rule30-paper/src/Observations.lex.tex`.
An adjacent defect and a common future black center force incompatible paired colors
within a bounded distance. Finite XOR rigidity then forces a nearby carry collision.
Under a hypothetical period `P`, common black centers occur within `P` steps, so collision
sources recur in the fixed band `[-2P, 2P]`. This is a necessary condition, not Problem 1.
-/

@[expose] public section

namespace Rule30UOR.CentralCollision

open Ruliology.CellularAutomata Rule30Jen Rule30Prize
open Rule30UOR.TemporalDefect Rule30UOR.Collision Rule30UOR.DefectFront
open Rule30XorRigidity.HalfLine (Good good_symm)

def leftAdjacentDefect (Q t : Nat) : Bool := defect Q t (-1)

def CentralCollision (Q t B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ (B : Int) ∧ collision Q t x = true

def NearCollision (Q t H B : Nat) : Prop :=
  ∃ s : Nat, s ≤ H ∧ CentralCollision Q (t + s) B

/-- One fixed central column, distinct from the collision-free column `-1`, carries
nonzero collisions arbitrarily late. -/
def RecurrentCentralCollision (Q B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ (B : Int) ∧ x ≠ -1 ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collision Q t x = true

private theorem white_cone (t : Nat) : ∀ (r : Nat) (p : Int),
    (∀ q : Int, p - (r : Int) ≤ q → q ≤ p + (r : Int) → cell t q = false) →
    cell (t + r) p = false := by
  intro r
  induction r with
  | zero => intro p h; simpa using h p (by omega) (by omega)
  | succ r ih =>
    intro p h
    rw [show t + (r + 1) = (t + r) + 1 by omega]
    change rule (cell (t + r) (p - 1)) (cell (t + r) p) (cell (t + r) (p + 1)) = false
    rw [ih (p - 1) (fun q hq1 hq2 => h q (by omega) (by omega)),
      ih p (fun q hq1 hq2 => h q (by omega) (by omega)),
      ih (p + 1) (fun q hq1 hq2 => h q (by omega) (by omega))]
    rfl

private theorem black_ancestor (t r : Nat) (h : center (t + r) = true) :
    ∃ q : Int, -(r : Int) ≤ q ∧ q ≤ (r : Int) ∧ cell t q = true := by
  apply Classical.byContradiction
  intro hn
  have hw := white_cone t r 0 (by
    intro q hq1 hq2
    cases hq : cell t q
    · rfl
    · exact (hn ⟨q, by omega, by omega, hq⟩).elim)
  change cell (t + r) 0 = true at h
  rw [hw] at h
  contradiction

/-- Generic finite-horizon localization, before imposing any periodicity hypothesis. -/
theorem unit_defect_forces_near_collision_kit (Q t r : Nat)
    (hd : leftAdjacentDefect Q t = true)
    (ha : center (t + r) = true) (hb : center ((t + r) + Q) = true) :
    NearCollision Q t (r + 1) (2 * (r + 1)) := by
  have incompatible : ∃ q : Int, -(r : Int) ≤ q ∧ q ≤ (r : Int) ∧
      ¬ Good (cell t (-1)) (cell (t + Q) (-1)) (cell t q) (cell (t + Q) q) := by
    cases h1 : cell t (-1) <;> cases h2 : cell (t + Q) (-1)
    · simp [leftAdjacentDefect, defect, difference, h1, h2] at hd
    · obtain ⟨q, hq1, hq2, hq⟩ := black_ancestor t r ha
      exact ⟨q, hq1, hq2, by simp [Good, hq]⟩
    · have hb' : center ((t + Q) + r) = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
      obtain ⟨q, hq1, hq2, hq⟩ := black_ancestor (t + Q) r hb'
      exact ⟨q, hq1, hq2, by simp [Good, hq]⟩
    · simp [leftAdjacentDefect, defect, difference, h1, h2] at hd
  obtain ⟨q, hq1, hq2, hbad⟩ := incompatible
  by_cases hq : -1 ≤ q
  · let d := (q + 1).toNat
    have hcast : (d : Int) = q + 1 := Int.toNat_of_nonneg (by omega)
    have hh := temporal_collision_of_incompatible Q t (-1) d (by
      simpa only [show (-1 : Int) + (d : Int) = q by omega] using hbad)
    obtain ⟨s, hs, x, hx1, hx2, hcol⟩ := hh
    exact ⟨s, by omega, x, by omega, by omega, hcol⟩
  · let d := (-1 - q).toNat
    have hcast : (d : Int) = -1 - q := Int.toNat_of_nonneg (by omega)
    have hh := temporal_collision_of_incompatible Q t q d (by
      rw [show q + (d : Int) = -1 by omega]
      intro he
      exact hbad (good_symm _ _ _ _ he))
    obtain ⟨s, hs, x, hx1, hx2, hcol⟩ := hh
    exact ⟨s, by omega, x, by omega, by omega, hcol⟩

theorem unit_defect_forces_near_collision (Q t r : Nat)
    (hd : leftAdjacentDefect Q t = true)
    (ha : Rule30UOR.Core.center (t + r) = true)
    (hb : Rule30UOR.Core.center ((t + r) + Q) = true) :
    NearCollision Q t (r + 1) (2 * (r + 1)) :=
  unit_defect_forces_near_collision_kit Q t r hd
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using ha)
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using hb)

private theorem black_within_period {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (t : Nat) (ht : T ≤ t) :
    ∃ r : Nat, r < P ∧ center (t + r) = true := by
  have hex : ∃ u : Nat, t ≤ u ∧ center u = true := by
    apply Classical.byContradiction
    intro hn
    apply center_not_eventually_constant
    refine ⟨t, false, fun u hu => ?_⟩
    cases hb : center u
    · rfl
    · exact (hn ⟨u, hu, hb⟩).elim
  obtain ⟨u, hu, hb⟩ := hex
  let r := (u - t) % P
  have hr : r < P := Nat.mod_lt _ hP
  have he : (t + r) + ((u - t) / P) * P = u := by
    have hh := Nat.mod_add_div (u - t) P
    rw [Nat.mul_comm P ((u - t) / P)] at hh
    dsimp [r]
    omega
  have hp := periodic_mul hc ((u - t) / P) (t + r) (by omega)
  rw [he] at hp
  exact ⟨r, hr, hp.symm.trans hb⟩

private theorem kit_period {T P : Nat} (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∀ t, T ≤ t → center (t + P) = center t := by
  intro t ht
  simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht

/-- The localization radius depends only on the proposed period, not the transient,
time, or period multiplier. -/
theorem periodic_unit_defect_forces_near_collision (T P m t : Nat) (hP : 0 < P)
    (_hm : 0 < m) (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t)
    (hd : leftAdjacentDefect (m * P) t = true) : NearCollision (m * P) t P (2 * P) := by
  have hp := kit_period hc
  obtain ⟨r, hr, hb⟩ := black_within_period hP hp t ht
  have hb' : center ((t + r) + m * P) = true := (periodic_mul hp m (t + r) (by omega)).trans hb
  obtain ⟨s, hs, x, hx1, hx2, hcol⟩ :=
    unit_defect_forces_near_collision_kit (m * P) t r hd hb hb'
  exact ⟨s, by omega, x, by omega, by omega, hcol⟩

/-- A hypothetical periodic center forces collision sources arbitrarily late in a
fixed central strip. They cannot all escape with the moving cone edges. -/
theorem periodic_central_collisions (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∃ t : Nat, N ≤ t ∧ CentralCollision (m * P) t (2 * P) := by
  have hp := kit_period hc
  obtain ⟨t, ht, hd⟩ := exists_defect_true_of_periodic ⟨T, P, hP, hp⟩
    (m * P) (Nat.mul_pos hm hP) (-1) (by decide) (max T N)
  obtain ⟨s, hs, hcol⟩ := periodic_unit_defect_forces_near_collision T P m t hP hm hc (by omega) hd
  exact ⟨t + s, by omega, hcol⟩

private theorem finite_recurrent_choice (f : Nat → Nat → Prop) (n : Nat) :
    (∀ N : Nat, ∃ t : Nat, N ≤ t ∧ ∃ i : Nat, i < n ∧ f i t) →
    ∃ i : Nat, i < n ∧ ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ f i t := by
  induction n with
  | zero =>
    intro h
    obtain ⟨t, ht, i, hi, hf⟩ := h 0
    omega
  | succ n ih =>
    intro h
    by_cases hn : ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ f n t
    · exact ⟨n, by omega, hn⟩
    · obtain ⟨N0, hN0⟩ := Classical.not_forall.mp hn
      obtain ⟨i, hi, hf⟩ := ih (by
        intro N
        obtain ⟨t, ht, j, hj, hf⟩ := h (max N N0)
        have hne : j ≠ n := by
          intro he
          subst j
          exact hN0 ⟨t, by omega, hf⟩
        exact ⟨t, by omega, j, by omega, hf⟩)
      exact ⟨i, by omega, hf⟩

/-- Finite choice localizes recurrence to one fixed source column. The central strip
is not a closed dynamical system: this theorem does not make its source signal periodic. -/
theorem periodic_recurrent_central_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentCentralCollision (m * P) (2 * P) := by
  let B := 2 * P
  obtain ⟨i, hi, hf⟩ := finite_recurrent_choice
    (fun i t => collision (m * P) t (-(B : Int) + (i : Int)) = true) (2 * B + 1) (by
      intro N
      obtain ⟨t, ht, x, hx1, hx2, hcol⟩ := periodic_central_collisions T P m N hP hm hc
      refine ⟨t, ht, (x + (B : Int)).toNat, by omega, ?_⟩
      simpa only [Int.toNat_of_nonneg (show 0 ≤ x + (B : Int) by omega),
        show -(B : Int) + (x + (B : Int)) = x by omega] using hcol)
  refine ⟨-(B : Int) + (i : Int), by omega, by omega, ?_, hf⟩
  intro he
  obtain ⟨t, ht, hcol⟩ := hf T
  rw [he] at hcol
  have hz := Rule30UOR.DefectSource.collision_neg_one_of_agree (m * P) t
    (center_defect_zero (kit_period hc) m t ht)
    (center_defect_zero (kit_period hc) m (t + 1) (by omega))
  rw [hz] at hcol
  contradiction

end Rule30UOR.CentralCollision
