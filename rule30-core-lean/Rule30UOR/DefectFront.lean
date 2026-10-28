module

public import Rule30UOR.DefectSource
public import Rule30UOR.CompilePoints

/-!
# Defect fronts: exact rightward transport of temporal disagreement

Rule 30 is permutive in its left input. For the temporal defect
`defect Q t p = cell (t+Q) p XOR cell t p` this gives an exact transport law, with no
periodicity assumption: a defect followed by two clean cells moves one step to the right,
because the collision source at that site vanishes (`DefectSource.collision_eq_defect`).

Iterating gives the **front lemma** (`defect_front_propagates`). A defect at `x` with a clean
window `(x, x + 2k]` reaches `x + k` at time `t + k`. At the center:

* `defect_center_of_leftHeavy`: a defect at `-k` with clean window `(-k, k]` forces a center
  disagreement at time `t + k`.
* `problem1_of_leftHeavy_recurrence`: if for every `P` and `T` some multiple `m * P` has a
  left-heavy profile at a time `t ≥ T`, then Problem 1 holds. This is a sufficient condition,
  stated without any periodicity hypothesis. Its converse is not claimed.
* `right_shield_of_periodic`: a necessary condition under a hypothetical periodic center.
  Every left defect at distance `k` is matched by a right-half defect at distance at most `k`.
  This is a structural consequence, not a refutation: its hypotheses are satisfiable.
-/

@[expose] public section

namespace Rule30UOR.DefectFront

open Ruliology.CellularAutomata Rule30Jen Rule30Prize
open Rule30UOR.TemporalDefect Rule30UOR.Collision Rule30UOR.DefectSource

/-- A defect followed by two clean cells moves one step right. -/
theorem defect_front_step (Q t : Nat) (x : Int)
    (h0 : defect Q t x = true) (h1 : defect Q t (x + 1) = false)
    (h2 : defect Q t (x + 2) = false) :
    defect Q (t + 1) (x + 1) = true := by
  rw [defect_source_law, collision_eq_defect, show x + 1 - 1 = x by omega,
    show x + 1 + 1 = x + 2 by omega, h0, h1, h2]
  unfold rule
  simp

/-- A clean interval stays clean on its interior one step later. -/
theorem defect_clean_step (Q t : Nat) (a b : Int)
    (h : ∀ p : Int, a ≤ p → p ≤ b → defect Q t p = false) :
    ∀ p : Int, a + 1 ≤ p → p ≤ b - 1 → defect Q (t + 1) p = false := by
  intro p hp1 hp2
  rw [defect_source_law, collision_eq_defect, h (p - 1) (by omega) (by omega),
    h p (by omega) (by omega), h (p + 1) (by omega) (by omega)]
  unfold rule
  simp

/-- **Front lemma.** A defect at `x` with a clean window `(x, x + 2k]` reaches `x + k` at
time `t + k`. Exact, unconditional. -/
theorem defect_front_propagates (Q : Nat) :
    ∀ (k t : Nat) (x : Int), defect Q t x = true →
      (∀ p : Int, x < p → p ≤ x + 2 * (k : Int) → defect Q t p = false) →
      defect Q (t + k) (x + (k : Int)) = true := by
  intro k
  induction k with
  | zero =>
    intro t x h0 _
    simpa using h0
  | succ k ih =>
    intro t x h0 hc
    have h1 : defect Q (t + 1) (x + 1) = true :=
      defect_front_step Q t x h0 (hc (x + 1) (by omega) (by omega))
        (hc (x + 2) (by omega) (by omega))
    have hc1 : ∀ p : Int, x + 1 < p → p ≤ (x + 1) + 2 * (k : Int) →
        defect Q (t + 1) p = false := by
      intro p hp1 hp2
      exact defect_clean_step Q t (x + 1) (x + 2 * ((k + 1 : Nat) : Int))
        (fun q hq1 hq2 => hc q (by omega) hq2) p (by omega) (by omega)
    have := ih (t + 1) (x + 1) h1 hc1
    rw [show t + 1 + k = t + (k + 1) by omega,
      show x + 1 + (k : Int) = x + ((k + 1 : Nat) : Int) by omega] at this
    exact this

/-- A left-heavy defect profile at time `t`: a defect at `-k` and a clean window `(-k, k]`. -/
def LeftHeavy (Q t k : Nat) : Prop :=
  0 < k ∧ defect Q t (-(k : Int)) = true ∧
    ∀ p : Int, -(k : Int) < p → p ≤ (k : Int) → defect Q t p = false

/-- A left-heavy profile forces a center disagreement `k` steps later. -/
theorem defect_center_of_leftHeavy (Q t k : Nat) (h : LeftHeavy Q t k) :
    defect Q (t + k) 0 = true := by
  obtain ⟨_, hd, hc⟩ := h
  have := defect_front_propagates Q k t (-(k : Int)) hd
    (fun p hp1 hp2 => hc p hp1 (by omega))
  rwa [show -(k : Int) + (k : Int) = 0 by omega] at this

/-- Under a center of period `P` from `T`, the defect at the center vanishes for every
multiple `m * P` at every time `t ≥ T`. -/
theorem center_defect_zero {T P : Nat} (hc : ∀ t, T ≤ t → center (t + P) = center t)
    (m t : Nat) (ht : T ≤ t) : defect (m * P) t 0 = false :=
  (difference_eq_false_iff center (m * P) t).mpr (periodic_mul hc m t ht)

/-- **Sufficient condition for Problem 1, with no periodicity assumption.** If for every
period `P` and time `T` some multiple `m * P` has a left-heavy profile at some `t ≥ T`,
then the center column is not eventually periodic. -/
theorem problem1_of_leftHeavy_recurrence
    (h : ∀ T P : Nat, 0 < P → ∃ m t k : Nat, T ≤ t ∧ LeftHeavy (m * P) t k) :
    Problem1 := by
  rintro ⟨T, P, hP, hc⟩
  obtain ⟨m, t, k, ht, hl⟩ := h T P hP
  have h1 := defect_center_of_leftHeavy (m * P) t k hl
  rw [center_defect_zero hc m (t + k) (by omega)] at h1
  contradiction

/--
Bridge hypothesis for the defect-front route: at every scale `(T, P)` there is a witness time
carrying both a zero-diagonal doubling certificate and a left-heavy defect profile at period
multiple `m * P`.
-/
def ZeroDiagDoublesLeftHeavyRecurrence : Prop :=
  ∀ T P : Nat, 0 < P →
    ∃ m z t k : Nat,
      T ≤ t ∧
      Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      LeftHeavy (m * P) t k

/--
Finer-grained bridge obligation for the same route. It keeps the zero-diagonal/doubling witness,
and spells the left-heavy profile in component form: distance positivity, a left defect at `-k`,
and a clean window `(-k, k]`.
-/
def ZeroDiagDoublesLeftHeavyAssembly : Prop :=
  ∀ T P : Nat, 0 < P →
    ∃ m z t k : Nat,
      T ≤ t ∧
      Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt (m * P) z ∧
      0 < k ∧
      defect (m * P) t (-(k : Int)) = true ∧
      (∀ p : Int, -(k : Int) < p → p ≤ (k : Int) → defect (m * P) t p = false)

/--
The assembly form implies `ZeroDiagDoublesLeftHeavyRecurrence` by repackaging the component
conditions as `LeftHeavy`.
-/
theorem zeroDiag_doubles_leftHeavyRecurrence_of_assembly
    (h : ZeroDiagDoublesLeftHeavyAssembly) :
    ZeroDiagDoublesLeftHeavyRecurrence := by
  intro T P hP
  obtain ⟨m, z, t, k, ht, hz, hd, hk, hdef, hclean⟩ := h T P hP
  exact ⟨m, z, t, k, ht, hz, hd, ⟨hk, hdef, hclean⟩⟩

/--
Concrete bridge theorem: the zero-diagonal/doubling witness schema implies the left-heavy
recurrence hypothesis used by `problem1_of_leftHeavy_recurrence`.
-/
theorem leftHeavy_recurrence_of_zeroDiag_doubles
    (h : ZeroDiagDoublesLeftHeavyRecurrence) :
    ∀ T P : Nat, 0 < P → ∃ m t k : Nat, T ≤ t ∧ LeftHeavy (m * P) t k := by
  intro T P hP
  obtain ⟨m, _z, t, k, ht, _hz, _hd, hl⟩ := h T P hP
  exact ⟨m, t, k, ht, hl⟩

/--
Submission-facing reduction for the current defect-front strategy: proving
`ZeroDiagDoublesLeftHeavyRecurrence` is sufficient to solve Problem 1.
-/
theorem submission_problem1_of_zeroDiag_doubles_leftHeavy
    (h : ZeroDiagDoublesLeftHeavyRecurrence) :
    Problem1 :=
  problem1_of_leftHeavy_recurrence (leftHeavy_recurrence_of_zeroDiag_doubles h)

/--
Submission-facing reduction in the finer-grained assembly form.
-/
theorem submission_problem1_of_zeroDiag_doubles_assembly
    (h : ZeroDiagDoublesLeftHeavyAssembly) :
    Problem1 :=
  submission_problem1_of_zeroDiag_doubles_leftHeavy
    (zeroDiag_doubles_leftHeavyRecurrence_of_assembly h)

/--
Primitive-period bridge obligation: for every `(T, P)`, at some zero-diagonal doubling point for
the same period `P`, there is a left-heavy witness for shift `P` itself (`m = 1`).
-/
def PrimitiveDoublesLeftHeavyRecurrence : Prop :=
  ∀ T P : Nat, 0 < P →
    ∃ z t k : Nat,
      T ≤ t ∧
      Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt P z ∧
      LeftHeavy P t k

/--
Component A at primitive period: at a doubling point of `P`, produce a left defect at `-k`.
-/
def PrimitiveDoublesLeftDefect : Prop :=
  ∀ T P : Nat, 0 < P →
    ∃ z t k : Nat,
      T ≤ t ∧
      Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt P z ∧
      0 < k ∧ defect P t (-(k : Int)) = true

/--
Stronger local form: at every certified primitive doubling point `(z, P)`, a left defect witness
can be produced after any lower time bound `T`.
-/
def PrimitiveLeftDefectAtAnyDoublesPoint : Prop :=
  ∀ T P z : Nat,
    0 < P →
    Rule30UOR.ZeroDiagonals.IsZeroDiag z →
    Rule30UOR.CompilePoints.DoublesAt P z →
    ∃ t k : Nat, T ≤ t ∧ 0 < k ∧ defect P t (-(k : Int)) = true

/--
Component B' at primitive period: any witness from `PrimitiveDoublesLeftDefect` can be upgraded
to a clean window on `(-k, k]`.
-/
def PrimitiveDoublesCleanWindowFromWitness : Prop :=
  ∀ T P z t k : Nat,
    0 < P → T ≤ t →
    Rule30UOR.ZeroDiagonals.IsZeroDiag z →
    Rule30UOR.CompilePoints.DoublesAt P z →
    0 < k → defect P t (-(k : Int)) = true →
    (∀ p : Int, -(k : Int) < p → p ≤ (k : Int) → defect P t p = false)

/--
Stronger local form: at every certified primitive doubling point `(z, P)`, directly produce
a full clean-window witness after any lower time bound `T`.
-/
def PrimitiveCleanWindowAtAnyDoublesPoint : Prop :=
  ∀ T P z : Nat,
    0 < P →
    Rule30UOR.ZeroDiagonals.IsZeroDiag z →
    Rule30UOR.CompilePoints.DoublesAt P z →
    ∃ t k : Nat,
      T ≤ t ∧ 0 < k ∧ defect P t (-(k : Int)) = true ∧
      (∀ p : Int, -(k : Int) < p → p ≤ (k : Int) → defect P t p = false)

/--
From the local-any-point form and `CompilePoints.doubling_points`, obtain
`PrimitiveDoublesLeftDefect`.
-/
theorem primitive_doubles_leftDefect_of_any_doubling_point
    (h : PrimitiveLeftDefectAtAnyDoublesPoint) :
    PrimitiveDoublesLeftDefect := by
  intro T P hP
  obtain ⟨z, hz, hd⟩ := Rule30UOR.CompilePoints.doubling_points P hP
  obtain ⟨t, k, ht, hk, hdef⟩ := h T P z hP hz hd
  exact ⟨z, t, k, ht, hz, hd, hk, hdef⟩

/--
Component B at primitive period: for the same witness data, provide the clean window `(-k, k]`.
-/
def PrimitiveDoublesCleanWindow : Prop :=
  ∀ T P : Nat, 0 < P →
    ∃ z t k : Nat,
      T ≤ t ∧
      Rule30UOR.ZeroDiagonals.IsZeroDiag z ∧
      Rule30UOR.CompilePoints.DoublesAt P z ∧
      0 < k ∧
      defect P t (-(k : Int)) = true ∧
      (∀ p : Int, -(k : Int) < p → p ≤ (k : Int) → defect P t p = false)

/--
From the stronger local clean-window form and `CompilePoints.doubling_points`, obtain
`PrimitiveDoublesCleanWindow`.
-/
theorem primitive_doubles_cleanWindow_of_any_doubling_point
    (h : PrimitiveCleanWindowAtAnyDoublesPoint) :
    PrimitiveDoublesCleanWindow := by
  intro T P hP
  obtain ⟨z, hz, hd⟩ := Rule30UOR.CompilePoints.doubling_points P hP
  obtain ⟨t, k, ht, hk, hdef, hclean⟩ := h T P z hP hz hd
  exact ⟨z, t, k, ht, hz, hd, hk, hdef, hclean⟩

/--
Component composition: the clean-window component already packages component A and yields
primitive-period left-heavy recurrence.
-/
theorem primitive_doubles_leftHeavy_of_cleanWindow
    (h : PrimitiveDoublesCleanWindow) :
    PrimitiveDoublesLeftHeavyRecurrence := by
  intro T P hP
  obtain ⟨z, t, k, ht, hz, hd, hk, hdef, hclean⟩ := h T P hP
  exact ⟨z, t, k, ht, hz, hd, ⟨hk, hdef, hclean⟩⟩

/--
Compositional assembly: witness production (component A) plus witness-to-window upgrade
(component B') imply `PrimitiveDoublesCleanWindow`.
-/
theorem primitive_doubles_cleanWindow_of_components
    (hA : PrimitiveDoublesLeftDefect)
    (hB : PrimitiveDoublesCleanWindowFromWitness) :
    PrimitiveDoublesCleanWindow := by
  intro T P hP
  obtain ⟨z, t, k, ht, hz, hd, hk, hdef⟩ := hA T P hP
  exact ⟨z, t, k, ht, hz, hd, hk, hdef, hB T P z t k hP ht hz hd hk hdef⟩

/--
Submission-facing reduction through the compositional component split.
-/
theorem submission_problem1_of_primitive_doubles_components
    (hA : PrimitiveDoublesLeftDefect)
    (hB : PrimitiveDoublesCleanWindowFromWitness) :
    Problem1 := by
  have hprim : PrimitiveDoublesLeftHeavyRecurrence :=
    primitive_doubles_leftHeavy_of_cleanWindow
      (primitive_doubles_cleanWindow_of_components hA hB)
  apply submission_problem1_of_zeroDiag_doubles_leftHeavy
  intro T P hP
  obtain ⟨z, t, k, ht, hz, hd, hl⟩ := hprim T P hP
  exact ⟨1, z, t, k, ht, hz, by simpa using hd, by simpa using hl⟩

/--
Submission-facing reduction through the split components. This isolates the remaining work to
proving `PrimitiveDoublesCleanWindow`.
-/
theorem submission_problem1_of_primitive_doubles_cleanWindow
    (h : PrimitiveDoublesCleanWindow) :
    Problem1 := by
  have hprim : PrimitiveDoublesLeftHeavyRecurrence :=
    primitive_doubles_leftHeavy_of_cleanWindow h
  apply submission_problem1_of_zeroDiag_doubles_leftHeavy
  intro T P hP
  obtain ⟨z, t, k, ht, hz, hd, hl⟩ := hprim T P hP
  exact ⟨1, z, t, k, ht, hz, by simpa using hd, by simpa using hl⟩

/-- Primitive-period recurrence implies the zero-diagonal/doubling recurrence schema (`m = 1`). -/
theorem zeroDiag_doubles_leftHeavyRecurrence_of_primitive
    (h : PrimitiveDoublesLeftHeavyRecurrence) :
    ZeroDiagDoublesLeftHeavyRecurrence := by
  intro T P hP
  obtain ⟨z, t, k, ht, hz, hd, hl⟩ := h T P hP
  exact ⟨1, z, t, k, ht, hz, by simpa using hd, by simpa using hl⟩

/--
Submission-facing reduction at primitive period: proving left-heavy recurrence at doubling points
for shift `P` is sufficient for Problem 1.
-/
theorem submission_problem1_of_primitive_doubles_leftHeavy
    (h : PrimitiveDoublesLeftHeavyRecurrence) :
    Problem1 :=
  submission_problem1_of_zeroDiag_doubles_leftHeavy
    (zeroDiag_doubles_leftHeavyRecurrence_of_primitive h)

/--
Direct submission-facing reduction from the strongest local clean-window assumption at
every primitive doubling point.
-/
theorem submission_problem1_of_any_doubling_point_cleanWindow
    (h : PrimitiveCleanWindowAtAnyDoublesPoint) :
    Problem1 :=
  submission_problem1_of_primitive_doubles_cleanWindow
    (primitive_doubles_cleanWindow_of_any_doubling_point h)

/--
Direct submission-facing reduction from local-any-point defect production plus global
witness-to-window upgrade.
-/
theorem submission_problem1_of_any_doubling_point_components
    (hA : PrimitiveLeftDefectAtAnyDoublesPoint)
    (hB : PrimitiveDoublesCleanWindowFromWitness) :
    Problem1 :=
  submission_problem1_of_primitive_doubles_components
    (primitive_doubles_leftDefect_of_any_doubling_point hA) hB

/-- Under a periodic center, every left defect is shielded inside `(-k, k]`. -/
theorem shield_of_periodic {T P : Nat} (hc : ∀ t, T ≤ t → center (t + P) = center t)
    (m t k : Nat) (ht : T ≤ t) (hk : 0 < k) (hd : defect (m * P) t (-(k : Int)) = true) :
    ∃ p : Int, -(k : Int) < p ∧ p ≤ (k : Int) ∧ p ≠ 0 ∧ defect (m * P) t p = true := by
  apply Classical.byContradiction
  intro hn
  have hl : LeftHeavy (m * P) t k := by
    refine ⟨hk, hd, fun p hp1 hp2 => ?_⟩
    by_cases hp0 : p = 0
    · subst hp0
      exact center_defect_zero hc m t ht
    · cases hb : defect (m * P) t p
      · rfl
      · exact (hn ⟨p, hp1, hp2, hp0, hb⟩).elim
  have h1 := defect_center_of_leftHeavy (m * P) t k hl
  rw [center_defect_zero hc m (t + k) (by omega)] at h1
  contradiction

/-- **Right shielding (necessary condition).** Under a periodic center, every left defect at
distance `k` is matched by a right-half defect at distance at most `k`. -/
theorem right_shield_of_periodic {T P : Nat} (hc : ∀ t, T ≤ t → center (t + P) = center t)
    (m t : Nat) (ht : T ≤ t) :
    ∀ k : Nat, 0 < k → defect (m * P) t (-(k : Int)) = true →
      ∃ y : Nat, 0 < y ∧ y ≤ k ∧ defect (m * P) t (y : Int) = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk hd
    obtain ⟨p, hp1, hp2, hp0, hpd⟩ := shield_of_periodic hc m t k ht hk hd
    by_cases hpos : 0 < p
    · refine ⟨p.toNat, by omega, by omega, ?_⟩
      rwa [Int.toNat_of_nonneg (by omega)]
    · have hlt : (-p).toNat < k := by omega
      obtain ⟨y, hy0, hyk, hyd⟩ := ih (-p).toNat hlt (by omega)
        (by rwa [show -((-p).toNat : Int) = p by omega])
      exact ⟨y, hy0, by omega, hyd⟩

/-- **Clean-site gated transport law.** At any site `p` where `defect Q t p = false`,
the next defect at `p` is the XOR of the left defect `defect Q t (p - 1)` and the
right defect `defect Q t (p + 1)` gated by `!cell t p`. -/
theorem defect_succ_of_clean (Q t : Nat) (p : Int) (hp : defect Q t p = false) :
    defect Q (t + 1) p = xor (defect Q t (p - 1)) (defect Q t (p + 1) && !cell t p) := by
  rw [defect_source_law, collision_eq_defect, hp]
  unfold rule
  cases defect Q t (p - 1) <;> cases defect Q t (p + 1) <;> cases cell t p <;> simp

/-- If a site `p` is clean at both `t` and `t + 1`, its left defect equals its right
defect gated by `!cell t p`. -/
theorem defect_left_eq_of_clean_pair (Q t : Nat) (p : Int)
    (hp0 : defect Q t p = false) (hp1 : defect Q (t + 1) p = false) :
    defect Q t (p - 1) = (defect Q t (p + 1) && !cell t p) := by
  have h := defect_succ_of_clean Q t p hp0
  rw [hp1] at h
  cases ha : defect Q t (p - 1) <;> cases hb : (defect Q t (p + 1) && !cell t p) <;>
    rw [ha, hb] at h <;> first | rfl | contradiction

/-- If `p` is clean at `t` and `t + 1` and has a defect on its left, then it must also
have a defect on its right and `cell t p` must be `false` (white). -/
theorem defect_right_and_white_of_clean_pair (Q t : Nat) (p : Int)
    (hp0 : defect Q t p = false) (hp1 : defect Q (t + 1) p = false)
    (hl : defect Q t (p - 1) = true) :
    defect Q t (p + 1) = true ∧ cell t p = false := by
  have h := defect_left_eq_of_clean_pair Q t p hp0 hp1
  rw [hl] at h
  cases hd : defect Q t (p + 1) <;> cases hc : cell t p
  · rw [hd, hc] at h; contradiction
  · rw [hd, hc] at h; contradiction
  · exact ⟨rfl, rfl⟩
  · rw [hd, hc] at h; contradiction

/-- **Leftward front step.** At the left edge of a right-half defect (`p - 1` and `p` clean,
`p + 1` defective), the defect steps left into `p` iff `cell t p = false`. -/
theorem defect_left_front_step (Q t : Nat) (p : Int)
    (hl : defect Q t (p - 1) = false) (hc : defect Q t p = false)
    (hr : defect Q t (p + 1) = true) :
    defect Q (t + 1) p = !cell t p := by
  rw [defect_succ_of_clean Q t p hc, hl, hr]
  cases cell t p <;> rfl

/-- **Pinch step.** When a clean site `p` is flanked by defects on both sides, the next
defect at `p` equals `cell t p`. -/
theorem defect_pinch_step (Q t : Nat) (p : Int)
    (hl : defect Q t (p - 1) = true) (hc : defect Q t p = false)
    (hr : defect Q t (p + 1) = true) :
    defect Q (t + 1) p = cell t p := by
  rw [defect_succ_of_clean Q t p hc, hl, hr]
  cases cell t p <;> rfl

/-- **Rightmost left-half defect step.** Because `p = 0` is clean at `t` and `t + 1`, no
right-half defect can cross `0` into the left half. Thus the rightmost left-half defect at
`x ≤ -2` steps deterministically to `x + 1` at `t + 1`, and `(x + 1, 0]` remains clean. -/
theorem rightmost_left_defect_step (Q t : Nat) (x : Int) (hx : x ≤ -2)
    (hd : defect Q t x = true)
    (hc : ∀ p : Int, x < p → p ≤ 0 → defect Q t p = false)
    (hc0 : defect Q (t + 1) 0 = false) :
    defect Q (t + 1) (x + 1) = true ∧
      ∀ p : Int, x + 1 < p → p ≤ 0 → defect Q (t + 1) p = false := by
  refine ⟨defect_front_step Q t x hd (hc (x + 1) (by omega) (by omega))
    (hc (x + 2) (by omega) (by omega)), ?_⟩
  intro p hp1 hp2
  by_cases hp0 : p = 0
  · subst hp0; exact hc0
  · exact defect_clean_step Q t (x + 1) 0
      (fun q hq1 hq2 => hc q (by omega) hq2) p (by omega) (by omega)

/-- **Rightmost left-half defect propagation.** If `-(k + 1)` is the rightmost left-half
defect at time `t` and the center `0` is clean during `[t, t + k]`, then the rightmost
left-half defect reaches `-1` at time `t + k` with `(-1, 0]` clean. -/
theorem rightmost_left_defect_propagates (Q : Nat) :
    ∀ (k t : Nat),
      defect Q t (-((k + 1 : Nat) : Int)) = true →
      (∀ p : Int, -((k + 1 : Nat) : Int) < p → p ≤ 0 → defect Q t p = false) →
      (∀ j : Nat, j ≤ k → defect Q (t + j) 0 = false) →
      defect Q (t + k) (-1) = true ∧ defect Q (t + k) 0 = false := by
  intro k
  induction k with
  | zero =>
    intro t hd _ hc0
    exact ⟨by simpa using hd, by simpa using hc0 0 (Nat.le_refl 0)⟩
  | succ k ih =>
    intro t hd hc hc0
    have hstep := rightmost_left_defect_step Q t (-((k + 1 + 1 : Nat) : Int)) (by omega)
      hd hc (by simpa using hc0 1 (by omega))
    rw [show -((k + 1 + 1 : Nat) : Int) + 1 = -((k + 1 : Nat) : Int) by omega] at hstep
    have hih := ih (t + 1) hstep.1 hstep.2 (fun j hj => by
      have := hc0 (j + 1) (by omega)
      rwa [show t + 1 + j = t + (j + 1) by omega])
    rwa [show t + 1 + k = t + (k + 1) by omega] at hih

/-- Under a periodic center, if `-k` (`k > 0`) is the rightmost left-half defect at `t ≥ T`,
then at the exact time `t + (k - 1)` there is a unit defect pair at `-1` and `1`, and the
center cell `center (t + (k - 1))` is `false` (white). -/
theorem center_white_and_right_defect_of_rightmost_left
    {T P : Nat} (hc : ∀ t, T ≤ t → center (t + P) = center t)
    (m t k : Nat) (ht : T ≤ t) (hk : 0 < k)
    (hd : defect (m * P) t (-(k : Int)) = true)
    (hclean : ∀ p : Int, -(k : Int) < p → p ≤ 0 → defect (m * P) t p = false) :
    defect (m * P) (t + (k - 1)) (-1) = true ∧
      defect (m * P) (t + (k - 1)) 1 = true ∧
      center (t + (k - 1)) = false := by
  have hk1 : (k - 1) + 1 = k := by omega
  have hprop := rightmost_left_defect_propagates (m * P) (k - 1) t
    (by rwa [hk1])
    (fun p hp1 hp2 => hclean p (by omega) hp2)
    (fun j _ => center_defect_zero hc m (t + j) (by omega))
  have hpair := defect_right_and_white_of_clean_pair (m * P) (t + (k - 1)) 0
    hprop.2 (center_defect_zero hc m (t + (k - 1) + 1) (by omega)) hprop.1
  exact ⟨hprop.1, hpair.1, hpair.2⟩

/-- Under a periodic center, **every** left-half defect at distance `k > 0` at `t ≥ T`
(with no cleanliness hypothesis) forces a unit defect pair at `-1` and `1` and a white
center cell at some time `t + (r - 1)` with `0 < r ≤ k`. -/
theorem exists_unit_defect_and_white_center_of_left_defect
    {T P : Nat} (hc : ∀ t, T ≤ t → center (t + P) = center t)
    (m t : Nat) (ht : T ≤ t) :
    ∀ k : Nat, 0 < k → defect (m * P) t (-(k : Int)) = true →
      ∃ r : Nat, 0 < r ∧ r ≤ k ∧
        defect (m * P) (t + (r - 1)) (-1) = true ∧
        defect (m * P) (t + (r - 1)) 1 = true ∧
        center (t + (r - 1)) = false := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk hd
    by_cases hclean : ∀ p : Int, -(k : Int) < p → p ≤ 0 → defect (m * P) t p = false
    · exact ⟨k, hk, Nat.le_refl k,
        center_white_and_right_defect_of_rightmost_left hc m t k ht hk hd hclean⟩
    · apply Classical.byContradiction
      intro hno
      apply hclean
      intro p hp1 hp2
      by_cases hp0 : p = 0
      · subst hp0; exact center_defect_zero hc m t ht
      · cases hb : defect (m * P) t p
        · rfl
        · have hlt : (-p).toNat < k := by omega
          obtain ⟨r, hr0, hrk, hr1, hr2, hr3⟩ := ih (-p).toNat hlt (by omega)
            (by rwa [show -((-p).toNat : Int) = p by omega])
          exact (hno ⟨r, hr0, by omega, hr1, hr2, hr3⟩).elim

end Rule30UOR.DefectFront

