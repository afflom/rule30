module

public import Rule30UOR.DefectFront
public import Rule30UOR.Scale
public import Rule30UOR.MaskedObservation

/-!
# Central localization of collision sources

Statements are authored in `rule30-paper/src/Observations.lex.tex`.
An adjacent defect and a common future black center force incompatible paired colors
within a bounded distance. Finite XOR rigidity then forces a nearby carry collision.
Under a hypothetical period `P`, common black centers occur within `P` steps, so collision
sources recur in the fixed left band `[-P, -2]`. This strengthens the earlier
central-band localization. It remains a necessary condition, not Problem 1.
-/

@[expose] public section

namespace Rule30UOR.CentralCollision

open Ruliology.CellularAutomata Rule30Jen Rule30Prize
open Rule30UOR.TemporalDefect Rule30UOR.Collision Rule30UOR.DefectFront Rule30UOR.DefectSource
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

/-- A collision source in a fixed left strip, excluding the source-free column `-1`. -/
def LeftCollision (Q t B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ -2 ∧ collision Q t x = true

/-- A single fixed column of the left strip carries collisions arbitrarily late. -/
def RecurrentLeftCollision (Q B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ -2 ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collision Q t x = true

/-- A cone witness retaining the collision's unit/black endpoint orientation. -/
def AdvancingLeftCone (Q t k : Nat) : Prop :=
  ∃ s : Nat, 2 * s ≤ k ∧ ∃ x : Int, -(k : Int) + (s : Int) ≤ x ∧
    x ≤ -(s : Int) ∧ x < 0 ∧ AdvancingCollision Q (t + s) x

def AdvancingLeftCollision (Q t B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ -2 ∧ AdvancingCollision Q t x

/-- The advancing source is on the rightmost defect front. -/
def LeadingAdvance (Q t k : Nat) : Prop :=
  2 ≤ k ∧ advancingAtDepth Q t k ∧ RightmostLeft Q t k

/-- Both the column and one of the advancing orientations recur infinitely often. -/
def RecurrentAdvancingLeftCollision (Q B : Nat) : Prop :=
  ∃ k c : Nat, 2 ≤ k ∧ k ≤ B ∧ (c = 3 ∨ c = 5) ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collisionCode Q t k = c

/-- The sharper mixed-colour witness is a cone with an advancing right endpoint. -/
theorem left_defect_black_cone (Q t k : Nat)
    (hd : leftDefect Q t k = true)
    (ha : Rule30UOR.Core.center t = true) (hb : Rule30UOR.Core.center (t + Q) = true) :
    AdvancingLeftCone Q t k := by
  exact left_advancing_collision_of_defect_and_black Q t k
    (by simpa only [leftDefect] using hd)
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using ha)
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using hb)

/-- The characteristic starting one step after an advancing source is true up to
its first erasure. The target depth decreases by one at each step. -/
def FirstPathErasure (Q t k j : Nat) : Prop :=
  j + 1 < k ∧
    (∀ i : Nat, i ≤ j → leftDefect Q (t + 1 + i) (k - (i + 1)) = true) ∧
    ErasureEvent Q (t + 1 + j) (k - (j + 2))

/-- A fixed source orientation, first-erasure offset, gate pattern and reset colour
recur together. This is a finite observation pattern, not a closed strip dynamics. -/
def RecurrentSourceErasure (Q B : Nat) : Prop :=
  ∃ k c j g z : Nat, 2 ≤ k ∧ k ≤ B ∧ (c = 3 ∨ c = 5) ∧ j + 1 < k ∧
    1 ≤ g ∧ g ≤ 6 ∧ (z = 0 ∨ z = 3) ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collisionCode Q t k = c ∧
      FirstPathErasure Q t k j ∧ gateCode Q (t + 1 + j) (k - (j + 2)) = g ∧
      leftColour Q (t + 2 + j) (k - (j + 2)) = z

/-- A leading source reaches its first erasure exactly at the center. -/
def RecurrentLeadingErasure (Q B : Nat) : Prop :=
  ∃ k c g : Nat, 2 ≤ k ∧ k ≤ B ∧ (c = 3 ∨ c = 5) ∧ (g = 2 ∨ g = 5) ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collisionCode Q t k = c ∧
      LeadingAdvance Q t k ∧ FirstPathErasure Q t k (k - 2) ∧
      gateCode Q (t + (k - 1)) 0 = g

/-- A leading front cannot erase before reaching the center. Its center erasure
has a common-white center and a unit right neighbor: only gate cases 0X and 0Y. -/
theorem leading_first_erasure (Q t k : Nat) (hl : LeadingAdvance Q t k)
    (hc : CenterCleanThrough Q t k) :
    FirstPathErasure Q t k (k - 2) ∧ ErasureEvent Q (t + (k - 1)) 0 ∧
      (gateCode Q (t + (k - 1)) 0 = 2 ∨ gateCode Q (t + (k - 1)) 0 = 5) ∧
      Rule30UOR.Core.center (t + (k - 1)) = false := by
  obtain ⟨hk, ha, hr⟩ := hl
  have prof : ∀ s : Nat, s < k → RightmostLeft Q (t + s) (k - s) := by
    intro s hs
    exact rightmost_left_profile Q t k s hr hs (fun j hj => hc j (by omega))
  have hin : leftDefect Q (t + (k - 1)) 1 = true := by
    have hh := (prof (k - 1) (by omega)).2.1
    simpa only [show k - (k - 1) = 1 by omega] using hh
  have hout : leftDefect Q (t + (k - 1) + 1) 0 = false := by
    simpa only [show t + (k - 1) + 1 = t + k by omega] using hc k (Nat.le_refl k)
  have he := erasure_event_of_step Q (t + (k - 1)) 0 hin hout
  have hf : FirstPathErasure Q t k (k - 2) := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      have hh := (prof (i + 1) (by omega)).2.1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · simpa only [show t + 1 + (k - 2) = t + (k - 1) by omega,
        show k - ((k - 2) + 2) = 0 by omega] using he
  have pair := defect_right_and_white_of_clean_pair Q (t + (k - 1)) 0
    (by simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using hc (k - 1) (by omega))
    (by simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using hout) hin
  have same := (difference_eq_false_iff (fun u => cell u 0) Q (t + (k - 1))).1
    (by simpa only [leftDefect, defect, Int.natCast_zero, Int.neg_zero]
      using hc (k - 1) (by omega))
  have hw : cell (t + (k - 1)) 0 = false := pair.2
  have hw' : cell (t + (k - 1) + Q) 0 = false := same.trans hw
  have hg : gateCode Q (t + (k - 1)) 0 = 2 ∨ gateCode Q (t + (k - 1)) 0 = 5 := by
    have hd := pair.1
    unfold defect difference at hd
    dsimp only at hd
    simp only [gateCode, Int.natCast_zero, Int.neg_zero, Int.zero_add, hw, hw']
    cases h0 : cell (t + (k - 1)) 1 <;> cases h1 : cell (t + (k - 1) + Q) 1 <;>
      simp_all [gateCase]
  exact ⟨hf, he, hg, by simpa only [Rule30UOR.Scale.center_eq_kit, Rule30Prize.center] using hw⟩

private theorem first_drop : ∀ n : Nat, ∀ f : Nat → Bool, f 0 = true → f n = false →
    ∃ j : Nat, j < n ∧ (∀ i : Nat, i ≤ j → f i = true) ∧ f (j + 1) = false := by
  intro n
  induction n with
  | zero =>
    intro f h0 hn
    rw [h0] at hn
    contradiction
  | succ n ih =>
    intro f h0 hn
    cases h1 : f 1
    · refine ⟨0, by omega, ?_, h1⟩
      intro i hi
      have he : i = 0 := by omega
      simpa only [he] using h0
    · obtain ⟨j, hj, hp, he⟩ := ih (fun i => f (i + 1)) h1
        (by simpa only [Nat.add_comm n 1] using hn)
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · simpa only [hi0] using h0
        · have hh := hp (i - 1) (by omega)
          simpa only [show i - 1 + 1 = i by omega] using hh
      · exact he

/-- Every forced advance whose characteristic ends at a clean center has a first
later erasure. All time, depth, prefix and colour data are retained. -/
theorem advancing_source_first_erasure (Q t k : Nat) (hk : 2 ≤ k)
    (ha : advancingAtDepth Q t k) (hc : leftDefect Q (t + k) 0 = false) :
    ∃ j : Nat, FirstPathErasure Q t k j := by
  have hstart : leftDefect Q (t + 1) (k - 1) = true := by
    simpa only [leftDefect, show -((k - 1 : Nat) : Int) = -(k : Int) + 1 by omega] using
      advancing_collision_step Q t (-(k : Int)) (by simpa only [advancingAtDepth] using ha)
  have hend : leftDefect Q (t + 1 + (k - 1)) (k - ((k - 1) + 1)) = false := by
    simpa only [show t + 1 + (k - 1) = t + k by omega,
      show k - ((k - 1) + 1) = 0 by omega] using hc
  obtain ⟨j, hj, hp, he⟩ := first_drop (k - 1)
    (fun i => leftDefect Q (t + 1 + i) (k - (i + 1))) (by simpa using hstart) hend
  have hin : leftDefect Q (t + 1 + j) ((k - (j + 2)) + 1) = true := by
    simpa only [show k - (j + 1) = k - (j + 2) + 1 by omega] using hp j (Nat.le_refl j)
  have hout : leftDefect Q (t + 1 + j + 1) (k - (j + 2)) = false := by
    simpa only [Nat.add_assoc, show j + 1 + 1 = j + 2 by omega] using he
  exact ⟨j, by omega, hp, erasure_event_of_step Q (t + 1 + j) (k - (j + 2)) hin hout⟩

/-- Frontier obstruction at fixed period: under a hypothetical periodic center of period `P`,
the period-scale recurrent central collision witness must fail. -/
def NoRecurrentCentralCollision : Prop :=
  ∀ T P : Nat, 0 < P → Rule30UOR.Scale.CenterPeriodic T P →
    ¬ RecurrentCentralCollision P (2 * P)

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

/-- A matching finite center window transports an agreeing left prefix forward.
Consequently a unit defect at the end has a witness in the initial prefix. -/
private theorem left_defect_of_agreeing_window (Q b r : Nat)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ r + 1 ∧ defect Q b (-(k : Int)) = true := by
  apply Classical.byContradiction
  intro hn
  have pref : Rule30UOR.MaskedObservation.LeftPrefixAgree b (b + Q) (r + 1) := by
    intro k hk1 hkr
    have hz : defect Q b (-(k : Int)) = false := by
      cases hh : defect Q b (-(k : Int))
      · rfl
      · exact (hn ⟨k, hk1, hkr, hh⟩).elim
    exact ((difference_eq_false_iff (fun t => cell t (-(k : Int))) Q b).1 hz).symm
  have he := Rule30UOR.MaskedObservation.trace_of_prefix hc pref r (by omega)
  have he' : cell (b + r) (-1) = cell (b + r + Q) (-1) := by
    simpa only [show b + Q + r = b + r + Q by omega] using he
  have hz : leftAdjacentDefect Q (b + r) = false := by
    simp [leftAdjacentDefect, defect, difference, he']
  rw [hz] at hd
  contradiction

private theorem nearest_left (Q t : Nat) (hz : leftDefect Q t 0 = false) :
    ∀ n : Nat, leftDefect Q t n = true → ∃ k : Nat, k ≤ n ∧ RightmostLeft Q t k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hd
    by_cases hp : ∀ r : Nat, r < n → leftDefect Q t r = false
    · refine ⟨n, Nat.le_refl n, ?_, hd, hp⟩
      cases n with
      | zero => rw [hz] at hd; contradiction
      | succ n => omega
    · apply Classical.byContradiction
      intro hn
      apply hp
      intro r hr
      cases hb : leftDefect Q t r
      · rfl
      · obtain ⟨k, hk, hh⟩ := ih r hr hb
        exact (hn ⟨k, by omega, hh⟩).elim

private theorem window_clean (Q t n : Nat)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree t (t + Q) n) :
    CenterCleanThrough Q t n := by
  intro j hj
  simp only [leftDefect, Int.natCast_zero, Int.neg_zero]
  apply (difference_eq_false_iff (fun u => cell u 0) Q (t + j)).2
  simpa only [center, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hc j hj).symm

/-- The oriented cone source lies on the actual rightmost defect front. Its
right endpoint is in the clean prefix and it cannot be a collision behind the front. -/
theorem black_window_forces_leading_source (Q b r : Nat) (hr : 0 < r)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hb : Rule30UOR.Core.center b = true)
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ s k : Nat, 2 * s ≤ r + 1 ∧ s ≤ r ∧ k + s ≤ r + 1 ∧
      LeadingAdvance Q (b + s) k := by
  have clean := window_clean Q b (r + 1) hc
  obtain ⟨n, hn, hnr, hdef⟩ := left_defect_of_agreeing_window Q b r hc hd
  obtain ⟨k, hkn, hk0, hdk, hpref⟩ := nearest_left Q b (clean 0 (by omega)) n hdef
  have hb' : center b = true := by
    simpa only [Rule30UOR.Scale.center_eq_kit] using hb
  have hbQ : center (b + Q) = true := by
    have he := hc 0 (by omega)
    simp only [Nat.add_zero] at he
    exact he.symm.trans hb'
  obtain ⟨s, hs, x, hx1, hx2, hx3, hadv⟩ :=
    left_advancing_collision_of_defect_and_black Q b k hdk hb' hbQ
  have hslt : s < k := by omega
  have prof := rightmost_left_profile Q b k s ⟨hk0, hdk, hpref⟩ hslt
    (fun j hj => clean j (by omega))
  have hxfront : x = -((k - s : Nat) : Int) := by
    apply Classical.byContradiction
    intro hn
    have hz := prof.2.2 (-x).toNat (by omega)
    have hs : cell (b + s) x = cell (b + s + Q) x := by
      apply Eq.symm
      apply (difference_eq_false_iff (fun u => cell u x) Q (b + s)).1
      simpa only [leftDefect, defect, Int.toNat_of_nonneg (show 0 ≤ -x by omega),
        show -(-x) = x by omega] using hz
    exact hadv.1 hs
  have hne : x ≠ -1 := by
    intro he
    have hcol := advancing_collision_has_source Q (b + s) x hadv
    rw [he] at hcol
    have hz := collision_neg_one_of_agree Q (b + s)
      (by simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using clean s (by omega))
      (by simpa only [leftDefect, Int.natCast_zero, Int.neg_zero, Nat.add_assoc]
        using clean (s + 1) (by omega))
    rw [hz] at hcol
    contradiction
  refine ⟨s, k - s, by omega, by omega, by omega, by omega, ?_, prof⟩
  simpa only [advancingAtDepth, hxfront] using hadv

/-- Forgetting the clean prefix recovers the finite advancing-collision interface. -/
theorem black_window_forces_advancing_collision (Q b r : Nat) (hr : 0 < r)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hb : Rule30UOR.Core.center b = true)
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ s : Nat, 2 * s ≤ r + 1 ∧ s ≤ r ∧ AdvancingLeftCollision Q (b + s) (r + 1) := by
  obtain ⟨s, k, hs, hsr, hk, hlead⟩ := black_window_forces_leading_source Q b r hr hc hb hd
  exact ⟨s, hs, hsr, -(k : Int), by omega, by have := hlead.1; omega, hlead.2.1⟩

/-- The original collision interface follows by forgetting the endpoint colours. -/
theorem black_window_forces_left_collision (Q b r : Nat) (hr : 0 < r)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hb : Rule30UOR.Core.center b = true)
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ s : Nat, 2 * s ≤ r + 1 ∧ s ≤ r ∧ LeftCollision Q (b + s) (r + 1) := by
  obtain ⟨s, hs, hsr, x, hx1, hx2, hadv⟩ := black_window_forces_advancing_collision Q b r hr hc hb hd
  exact ⟨s, hs, hsr, x, hx1, hx2, advancing_collision_has_source Q (b + s) x hadv⟩

/-- The source occurs no later than the unit defect supplied by the moving edge. This
removes the extra future localization allowance from the earlier deadline. -/
theorem periodic_leading_source_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t k : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 2 * P ∧ k ≤ P ∧
      LeadingAdvance (m * P) t k := by
  have hp := kit_period hc
  obtain ⟨r, hr0, hr, hd, _, hw⟩ := exists_unit_defect_and_white_center_of_periodic
    hP hp m (N + P) hm (by omega)
  let v := N + P + (r - 1)
  let a := v + 1 - P
  have haT : T ≤ a := by dsimp [a, v]; omega
  have haN : N ≤ a := by dsimp [a, v]; omega
  obtain ⟨j, hj, hb⟩ := black_within_period hP hp a haT
  let b := a + j
  have hbT : T ≤ b := by dsimp [b]; omega
  have hbN : N ≤ b := by dsimp [b]; omega
  have hbv : b ≤ v := by dsimp [b, a]; omega
  have hgap : v - b < P := by dsimp [b, a]; omega
  have hgap0 : 0 < v - b := by
    apply Classical.byContradiction
    intro hn
    have he : v = b := by omega
    have hwhite : center v = false := hw
    have hblack : center b = true := hb
    rw [he, hblack] at hwhite
    contradiction
  have win : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + m * P) (v - b + 1) := by
    intro k hk
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (periodic_mul hp m (b + k) (by omega)).symm
  obtain ⟨s, k, hs, hsr, hk, hlead⟩ := black_window_forces_leading_source
    (m * P) b (v - b) hgap0 win
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using hb) (by
      simpa only [show b + (v - b) = v by omega, leftAdjacentDefect, v] using hd)
  refine ⟨b + s, k, by omega, ?_, by omega, hlead⟩
  dsimp [v] at hsr
  omega

/-- The advancing-source bound follows by forgetting the leading profile. -/
theorem periodic_advancing_left_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 2 * P ∧
      AdvancingLeftCollision (m * P) t P := by
  obtain ⟨t, k, ht, hb, hk, hl⟩ := periodic_leading_source_window T P m N hP hm hc hN
  exact ⟨t, ht, hb, -(k : Int), by omega, by have := hl.1; omega, hl.2.1⟩

/-- A leading source in the period-width strip reaches its first erasure at the
center at its exact characteristic arrival time. -/
theorem periodic_leading_erasure_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t k : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 2 * P ∧ k ≤ P ∧
      LeadingAdvance (m * P) t k ∧ FirstPathErasure (m * P) t k (k - 2) ∧
      (gateCode (m * P) (t + (k - 1)) 0 = 2 ∨ gateCode (m * P) (t + (k - 1)) 0 = 5) := by
  obtain ⟨t, k, ht, hb, hk, hl⟩ := periodic_leading_source_window T P m N hP hm hc hN
  have clean : CenterCleanThrough (m * P) t k := by
    intro j hj
    simpa only [leftDefect, Int.natCast_zero, Int.neg_zero] using
      center_defect_zero (kit_period hc) m (t + j) (by omega)
  obtain ⟨hf, he, hg, hw⟩ := leading_first_erasure (m * P) t k hl clean
  exact ⟨t, k, ht, hb, hk, hl, hf, hg⟩

/-- The selected center erasure also supplies the earlier strip-wide erasure API. -/
theorem periodic_erasure_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ u d : Nat, N ≤ u ∧ u + 1 ≤ 2 * N + m * P + 3 * P ∧ d + 2 ≤ P ∧
      ErasureEvent (m * P) u d := by
  obtain ⟨t, k, ht, hb, hk, hl, hf, hg⟩ := periodic_leading_erasure_window T P m N hP hm hc hN
  have hk2 := hl.1
  have he : ErasureEvent (m * P) (t + (k - 1)) 0 := by
    simpa only [show t + 1 + (k - 2) = t + (k - 1) by omega,
      show k - ((k - 2) + 2) = 0 by omega] using hf.2.2
  exact ⟨t + (k - 1), 0, by omega, by omega, by omega, he⟩

/-- Forgetting the advancing orientation preserves the existing quantitative API. -/
theorem periodic_left_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 2 * P ∧
      LeftCollision (m * P) t P := by
  obtain ⟨t, ht, hb, x, hx1, hx2, hadv⟩ :=
    periodic_advancing_left_collision_window T P m N hP hm hc hN
  exact ⟨t, ht, hb, x, hx1, hx2, advancing_collision_has_source (m * P) t x hadv⟩

theorem periodic_left_collisions (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∃ t : Nat, N ≤ t ∧ LeftCollision (m * P) t P := by
  obtain ⟨t, ht, _, hcol⟩ := periodic_left_collision_window T P m (max T N) hP hm hc (by omega)
  exact ⟨t, by omega, hcol⟩

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

/-- The moving left edge gives a quantitative recurrence window. A left defect at
distance `N + m*P` reaches a unit pair within that many steps; localization then
takes at most `P` more steps. No recurrence rate is inferred from measured data. -/
theorem periodic_central_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + P ∧
      CentralCollision (m * P) t (2 * P) := by
  obtain ⟨r, hr0, hr, hd, _, _⟩ :=
    exists_unit_defect_and_white_center_of_periodic hP (kit_period hc) m N hm hN
  obtain ⟨s, hs, hcol⟩ := periodic_unit_defect_forces_near_collision
    T P m (N + (r - 1)) hP hm hc (by omega) hd
  exact ⟨N + (r - 1) + s, by omega, by omega, hcol⟩

/-- A hypothetical periodic center forces collision sources arbitrarily late in a
fixed central strip. They cannot all escape with the moving cone edges. -/
theorem periodic_central_collisions (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∃ t : Nat, N ≤ t ∧ CentralCollision (m * P) t (2 * P) := by
  obtain ⟨t, ht, _, hcol⟩ := periodic_central_collision_window
    T P m (max T N) hP hm hc (by omega)
  exact ⟨t, by omega, hcol⟩

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

/-- The recurring witness can be chosen on the leading front, with its first
cancellation at the center. Only two of the six erasure gate cases remain. -/
theorem periodic_recurrent_leading_erasure (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentLeadingErasure (m * P) P := by
  obtain ⟨k, hk, hfront⟩ := finite_recurrent_choice
    (fun k t => LeadingAdvance (m * P) t k ∧ FirstPathErasure (m * P) t k (k - 2) ∧
      (gateCode (m * P) (t + (k - 1)) 0 = 2 ∨ gateCode (m * P) (t + (k - 1)) 0 = 5))
    (P + 1) (by
      intro N
      obtain ⟨t, k, ht, hb, hk, hl, hf, hg⟩ :=
        periodic_leading_erasure_window T P m (max T N) hP hm hc (by omega)
      exact ⟨t, by omega, k, by omega, hl, hf, hg⟩)
  have hk2 : 2 ≤ k := by
    obtain ⟨t, ht, hl, hf, hg⟩ := hfront 0
    exact hl.1
  obtain ⟨j, hj, horient⟩ := finite_recurrent_choice
    (fun j t => collisionCode (m * P) t k = (if j = 0 then 3 else 5) ∧
      LeadingAdvance (m * P) t k ∧ FirstPathErasure (m * P) t k (k - 2) ∧
      (gateCode (m * P) (t + (k - 1)) 0 = 2 ∨ gateCode (m * P) (t + (k - 1)) 0 = 5))
    2 (by
      intro N
      obtain ⟨t, ht, hl, hf, hg⟩ := hfront N
      rcases (advancing_collision_codes (m * P) t k).1 hl.2.1 with hx | hy
      · exact ⟨t, ht, 0, by omega, by simpa using hx, hl, hf, hg⟩
      · exact ⟨t, ht, 1, by omega, by simpa using hy, hl, hf, hg⟩)
  obtain ⟨i, hi, hgate⟩ := finite_recurrent_choice
    (fun i t => collisionCode (m * P) t k = (if j = 0 then 3 else 5) ∧
      LeadingAdvance (m * P) t k ∧ FirstPathErasure (m * P) t k (k - 2) ∧
      gateCode (m * P) (t + (k - 1)) 0 = (if i = 0 then 2 else 5)) 2 (by
      intro N
      obtain ⟨t, ht, hs, hl, hf, hg⟩ := horient N
      rcases hg with hx | hy
      · exact ⟨t, ht, 0, by omega, hs, hl, hf, by simpa using hx⟩
      · exact ⟨t, ht, 1, by omega, hs, hl, hf, by simpa using hy⟩)
  refine ⟨k, (if j = 0 then 3 else 5), (if i = 0 then 2 else 5), hk2, by omega,
    ?_, ?_, hgate⟩
  · by_cases he : j = 0 <;> simp [he]
  · by_cases he : i = 0 <;> simp [he]

/-- The older fixed-column source interface follows by forgetting the leading
profile and its correlated center erasure. -/
theorem periodic_recurrent_advancing_left_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentAdvancingLeftCollision (m * P) P := by
  obtain ⟨k, c, g, hk, hkP, hcs, hgs, hf⟩ := periodic_recurrent_leading_erasure T P m hP hm hc
  refine ⟨k, c, hk, hkP, hcs, ?_⟩
  intro N
  obtain ⟨t, ht, hs, hl, hp, hg⟩ := hf N
  exact ⟨t, ht, hs⟩

/-- Finite choice fixes an entire source-to-first-erasure pattern, including the
OR-gate case and common reset colour, under the hypothetical periodic center. -/
theorem periodic_recurrent_source_erasure (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentSourceErasure (m * P) P := by
  obtain ⟨k, c, g, hk, hkP, hcs, hgs, hf⟩ := periodic_recurrent_leading_erasure T P m hP hm hc
  obtain ⟨i, hi, hreset⟩ := finite_recurrent_choice
    (fun i t => collisionCode (m * P) t k = c ∧ FirstPathErasure (m * P) t k (k - 2) ∧
      gateCode (m * P) (t + 1 + (k - 2)) (k - ((k - 2) + 2)) = g ∧
      leftColour (m * P) (t + 2 + (k - 2)) (k - ((k - 2) + 2)) = (if i = 0 then 0 else 3))
    2 (by
      intro N
      obtain ⟨t, ht, hs, hl, hp, hg⟩ := hf N
      have hg' : gateCode (m * P) (t + 1 + (k - 2)) (k - ((k - 2) + 2)) = g := by
        simpa only [show t + 1 + (k - 2) = t + (k - 1) by omega,
          show k - ((k - 2) + 2) = 0 by omega] using hg
      have hh := hp.2.2.2.2.2.2
      have hh' : leftColour (m * P) (t + 2 + (k - 2)) (k - ((k - 2) + 2)) = 0 ∨
          leftColour (m * P) (t + 2 + (k - 2)) (k - ((k - 2) + 2)) = 3 := by
        simpa only [show t + 1 + (k - 2) + 1 = t + 2 + (k - 2) by omega] using hh
      rcases hh' with hx | hy
      · exact ⟨t, ht, 0, by omega, hs, hp, hg', by simpa using hx⟩
      · exact ⟨t, ht, 1, by omega, hs, hp, hg', by simpa using hy⟩)
  refine ⟨k, c, k - 2, g, (if i = 0 then 0 else 3), hk, hkP, hcs, by omega,
    ?_, ?_, ?_, hreset⟩
  · rcases hgs with he | he <;> omega
  · rcases hgs with he | he <;> omega
  · by_cases he : i = 0 <;> simp [he]

/-- The weaker recurring-source interface follows from a fixed advancing type. -/
theorem periodic_recurrent_left_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentLeftCollision (m * P) P := by
  obtain ⟨k, c, hk, hkP, hc0, hf⟩ := periodic_recurrent_advancing_left_column T P m hP hm hc
  refine ⟨-(k : Int), by omega, by omega, ?_⟩
  intro N
  obtain ⟨t, ht, hcode⟩ := hf N
  have hne : collisionCode (m * P) t k ≠ 0 := by rw [hcode]; rcases hc0 with h | h <;> omega
  refine ⟨t, ht, ?_⟩
  simpa only [collisionBit] using (collision_code_nonzero (m * P) t k).1 hne

/-- Finite choice localizes recurrence to one fixed source column. The central strip
is not a closed dynamical system: this theorem does not make its source signal periodic. -/
theorem periodic_recurrent_central_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentCentralCollision (m * P) (2 * P) := by
  obtain ⟨x, hx1, hx2, hf⟩ := periodic_recurrent_left_column T P m hP hm hc
  exact ⟨x, by omega, by omega, by omega, hf⟩

/-- Frontier reduction: any eventual periodic center hypothesis yields a fixed-band
recurrent central collision witness. This packages the `T, P` witness extraction and
the periodic recurrence theorem into one contradiction-ready consequence. -/
theorem recurrent_central_collision_of_eventual_periodic
  (m : Nat) (hm : 0 < m) (hc : EventuallyPeriodic Rule30Prize.center) :
    ∃ T P : Nat, 0 < P ∧ Rule30UOR.Scale.CenterPeriodic T P ∧
      RecurrentCentralCollision (m * P) (2 * P) := by
  obtain ⟨T, P, hP, hper⟩ := hc
  refine ⟨T, P, hP, ?_, periodic_recurrent_central_column T P m hP hm ?_⟩
  · intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hper t ht
  · intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hper t ht

/-- Canonical interface form of the same frontier reduction: excluding periodic-center
recurrent central collisions is exactly a `NoPeriod` witness. -/
theorem noPeriod_of_no_recurrent_central_collision
    (hno : ∀ T P : Nat, 0 < P →
      Rule30UOR.Scale.CenterPeriodic T P →
      ¬ RecurrentCentralCollision P (2 * P)) :
    Rule30UOR.Scale.NoPeriod := by
  intro T P hP hcP
  have hrec : RecurrentCentralCollision P (2 * P) := by
    simpa [Nat.one_mul] using
      periodic_recurrent_central_column T P 1 hP (by decide) hcP
  exact hno T P hP hcP hrec

/-- Canonical `NoPeriod` implies the recurrent-central-collision criterion vacuously,
since its periodic-center premise is impossible. -/
theorem no_recurrent_central_collision_of_noPeriod
    (h : Rule30UOR.Scale.NoPeriod) : NoRecurrentCentralCollision := by
  intro T P hP hcP
  exact (h T P hP hcP).elim

/-- Exact canonical form at this layer: excluding periodic-center recurrent central
collisions is equivalent to `NoPeriod`. -/
theorem no_recurrent_central_collision_iff_noPeriod :
    NoRecurrentCentralCollision ↔ Rule30UOR.Scale.NoPeriod := by
  constructor
  · exact noPeriod_of_no_recurrent_central_collision
  · exact no_recurrent_central_collision_of_noPeriod

/-- Problem 1 follows once one rules out fixed-band recurrent central collisions under
every hypothetical periodic-center witness. -/
theorem problem1_of_no_recurrent_central_collision
    (hno : ∀ T P : Nat, 0 < P →
      Rule30UOR.Scale.CenterPeriodic T P →
      ¬ RecurrentCentralCollision P (2 * P)) :
    Rule30Prize.Problem1 := by
  exact Rule30UOR.Scale.problem1_of_noPeriod
    (noPeriod_of_no_recurrent_central_collision hno)

/-- Problem 1 implies the recurrent-central-collision obstruction criterion. -/
theorem no_recurrent_central_collision_of_problem1
    (h : Rule30Prize.Problem1) : NoRecurrentCentralCollision := by
  exact no_recurrent_central_collision_of_noPeriod
    (Rule30UOR.Scale.noPeriod_of_problem1 h)

/-- Exact frontier at this layer: Problem 1 is equivalent to excluding recurrent central
collision witnesses under every periodic-center hypothesis. -/
theorem problem1_iff_no_recurrent_central_collision :
    Rule30Prize.Problem1 ↔ NoRecurrentCentralCollision := by
  rw [Rule30UOR.Scale.problem1_iff]
  exact (no_recurrent_central_collision_iff_noPeriod).symm

end Rule30UOR.CentralCollision
