module

public import Ruliology.CellularAutomata.Rule30BlackRuns
public import Ruliology.CellularAutomata.Rule30DrivenLeft

/-!
# Rule 30: what an eventual period 2 of the center column would force

Period `1` is excluded (`Rule30Prize.center_not_eventually_constant`); period `2` is the first
open case. This module records the structure that an eventual period `2` would force and reduces
its exclusion to a question about the left half alone.

**Normal form.** `normalize`: if `c (t + 2) = c t` for all `t ≥ T₀`, then there is `T` with
`c (T + 2k) = 1` and `c (T + 2k + 1) = 0` for all `k` (the column is not eventually constant).

**The forced skeleton.** With `c` alternating from `T` as above, write `s k = cell (T+2k+1) (-1)`.
* `m1_even`: column `-1` is black at every time `T + 2k`.
* `p1_odd`: column `1` at time `T + 2k + 1` is `!s k`.
* `golden`: `s` never has two consecutive zeros, so the white cells of column `-1` are at least
  four steps apart.
* `m2_even`, `m2_odd`, `m3_even`, `m3_odd`: columns `-2`, `-3` are functions of `s`;
  `m4_odd`: column `-4` is white at every time `T + 2k + 1`.
* `no_AA`, `no_BB`, `no_ABAB`, `col4_white_of_alt`: the same kind of constraint from a finite
  window of alternation (white first): column `1` at four consecutive steps never reads `0000`
  or `0101`, at eight steps never `00010001`, and with `c = 0 1 0 1 0` on `[t, t + 4]` column
  `-4` is white at `t`. Finite checks over all window contents.

**Reduction to the zero-driven left half.** By the effective boundary
(`Rule30MaskedJen.effective_step`), the left half sees `c` only through `c t && c (t + 1)`,
which is white once `c` alternates (`effective_white`). So from time `T` on, columns `p < 0`
evolve as rule 30 on the half-line with column `0` held white (`left_half_zero_driven`), started
from a finite row whose leftmost black cell is at `-T`.
* `Q01`: **the open question.** No start of the zero-driven left half with a leftmost black
  cell keeps column `-1` black at every even step.
* `not_eventually_period_two_of_Q01`: **`Q01` implies that the center column is not eventually
  2-periodic**, for every transient.
* `stripe_fixed`, `stripe_col`: the infinite stripe (black exactly at the odd positions `< 0`)
  is fixed by the zero-driven left half and keeps column `-1` black at every step. So the
  finiteness hypothesis in `Q01` is essential.

`Q01` is not proved here. As numerical evidence only: exhaustive searches in the Rule 30 Prize
project found that for every start of support width `W ≤ 39`, column `-1` turns white at some
even step, within roughly `1.25 W` to `2 W` steps.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwo

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30BlackRuns Rule30DrivenLeft

/-! ### Normal form -/

theorem step' (t : Nat) (p a b d : Int) (ha : a = p - 1) (hb : b = p) (hd : d = p + 1) :
    cell (t + 1) p = rule (cell t a) (cell t b) (cell t d) := by
  subst ha hb hd; rfl

/-- Every eventual period 2 of the center column has the normalized shape for some `T`. -/
theorem normalize {T0 : Nat} (hp : ∀ t, T0 ≤ t → center (t + 2) = center t) :
    ∃ T, ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false := by
  have per : ∀ k t, T0 ≤ t → center (t + 2 * k) = center t := by
    intro k; induction k with
    | zero => intro t _; rfl
    | succ k ih => intro t ht; rw [show t + 2 * (k + 1) = (t + 2 * k) + 2 by omega, hp _ (by omega), ih t ht]
  have hne : center T0 ≠ center (T0 + 1) := by
    intro e
    apply center_not_eventually_constant
    refine ⟨T0, center T0, fun t ht => ?_⟩
    obtain ⟨k, hk | hk⟩ : ∃ k, t = T0 + 2 * k ∨ t = T0 + 1 + 2 * k := ⟨(t - T0) / 2, by omega⟩
    · rw [hk, per k T0 (by omega)]
    · rw [hk, per k (T0 + 1) (by omega), e]
  cases h0 : center T0
  · refine ⟨T0 + 1, fun k => ⟨?_, ?_⟩⟩
    · have := per k (T0 + 1) (by omega)
      have h1 : center (T0 + 1) = true := by
        cases e : center (T0 + 1)
        · exact absurd (h0.trans e.symm) hne
        · rfl
      exact this.trans h1
    · have := per (k + 1) T0 (Nat.le_refl _)
      rw [show T0 + 2 * (k + 1) = T0 + 1 + 2 * k + 1 by omega] at this
      exact this.trans h0
  · refine ⟨T0, fun k => ⟨(per k T0 (Nat.le_refl _)).trans h0, ?_⟩⟩
    have := per k (T0 + 1) (by omega)
    rw [show T0 + 1 + 2 * k = T0 + 2 * k + 1 by omega] at this
    have h1 : center (T0 + 1) = false := by
      cases e : center (T0 + 1)
      · rfl
      · exact absurd (h0.trans e.symm) hne
    exact this.trans h1

/-! ### Finite windows of alternation -/

/-- Column-1 word of the right half: run the row with the given center values and record its
first cell before each step. -/
def col1 : List Bool → List Bool → List Bool
  | [], _ => []
  | c :: cs, l => l.headD false :: col1 cs (stepRow c l)

theorem col1_rowAt : ∀ (cs : List Bool) (t n : Nat),
    (∀ i, (h : i < cs.length) → cell (t + i) 0 = cs[i]) →
    col1 cs (rowAt t 1 (n + cs.length + 1)) =
      (List.range cs.length).map (fun i => cell (t + i) 1)
  | [], t, n, _ => rfl
  | c :: cs, t, n, h => by
    have h0 : cell t 0 = c := h 0 (by simp)
    have hs : stepRow c (rowAt t 1 ((n + cs.length + 1) + 1)) =
        rowAt (t + 1) 1 (n + cs.length + 1) := by
      have := stepRow_rowAt t (n + cs.length + 1) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    have ih := col1_rowAt cs (t + 1) n (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show t + 1 + i = t + (i + 1) by omega]
      simpa using this)
    show (rowAt t 1 (n + (cs.length + 1) + 1)).headD false ::
        col1 cs (stepRow c (rowAt t 1 (n + (cs.length + 1) + 1)))
      = (List.range (cs.length + 1)).map (fun i => cell (t + i) 1)
    rw [show n + (cs.length + 1) + 1 = (n + cs.length + 1) + 1 by omega, hs, ih,
      List.range_succ_eq_map]
    simp only [rowAt, List.headD_cons, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show t + 1 + i = t + (i + 1) by omega]

/-- Alternating center values starting with `0`. -/
def alt (k : Nat) : List Bool := (List.range k).map (fun i => i % 2 == 1)

theorem alt_length (k : Nat) : (alt k).length = k := by simp [alt]

/-- Under an alternating center (white first), the column-1 word of length 8 never reads
`00 01 00 01`, and the words of length 4 never read `00 00` or `01 01`. -/
theorem alt_check_AA : (allLists 6).all (fun l => (col1 (alt 4) l) != [false, false, false, false]) = true := by
  decide +kernel
theorem alt_check_BB : (allLists 6).all (fun l => (col1 (alt 4) l) != [false, true, false, true]) = true := by
  decide +kernel
theorem alt_check_ABAB : (allLists 10).all
    (fun l => (col1 (alt 8) l) != [false, false, false, true, false, false, false, true]) = true := by
  decide +kernel

theorem alt_spec (t k : Nat) (h : ∀ i, i < k → center (t + i) = (i % 2 == 1)) :
    ∀ i, (hi : i < (alt k).length) → cell (t + i) 0 = (alt k)[i] := by
  intro i hi
  simp only [alt, List.getElem_map, List.getElem_range]
  exact h i (by simpa [alt_length] using hi)

theorem col1_alt (t k : Nat) (h : ∀ i, i < k → center (t + i) = (i % 2 == 1)) :
    col1 (alt k) (rowAt t 1 (k + 2)) = (List.range k).map (fun i => cell (t + i) 1) := by
  have := col1_rowAt (alt k) t 1 (alt_spec t k h)
  rw [alt_length] at this
  rw [show k + 2 = 1 + k + 1 by omega]
  exact this

theorem no_AA (t : Nat) (h : ∀ i, i < 4 → center (t + i) = (i % 2 == 1)) :
    ¬ (cell t 1 = false ∧ cell (t + 1) 1 = false ∧ cell (t + 2) 1 = false ∧ cell (t + 3) 1 = false) := by
  rintro ⟨h0, h1, h2, h3⟩
  have hw := col1_alt t 4 h
  have hmem : rowAt t 1 (4 + 2) ∈ allLists 6 := by
    have := mem_allLists (rowAt t 1 (4 + 2)); rwa [length_rowAt] at this
  have hc := List.all_eq_true.1 alt_check_AA _ hmem
  rw [hw] at hc
  simp [List.range_succ, h0, h1, h2, h3] at hc

theorem no_BB (t : Nat) (h : ∀ i, i < 4 → center (t + i) = (i % 2 == 1)) :
    ¬ (cell t 1 = false ∧ cell (t + 1) 1 = true ∧ cell (t + 2) 1 = false ∧ cell (t + 3) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  have hw := col1_alt t 4 h
  have hmem : rowAt t 1 (4 + 2) ∈ allLists 6 := by
    have := mem_allLists (rowAt t 1 (4 + 2)); rwa [length_rowAt] at this
  have hc := List.all_eq_true.1 alt_check_BB _ hmem
  rw [hw] at hc
  simp [List.range_succ, h0, h1, h2, h3] at hc

theorem no_ABAB (t : Nat) (h : ∀ i, i < 8 → center (t + i) = (i % 2 == 1)) :
    ¬ (cell t 1 = false ∧ cell (t + 1) 1 = false ∧ cell (t + 2) 1 = false ∧ cell (t + 3) 1 = true ∧
       cell (t + 4) 1 = false ∧ cell (t + 5) 1 = false ∧ cell (t + 6) 1 = false ∧ cell (t + 7) 1 = true) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hw := col1_alt t 8 h
  have hmem : rowAt t 1 (8 + 2) ∈ allLists 10 := by
    have := mem_allLists (rowAt t 1 (8 + 2)); rwa [length_rowAt] at this
  have hc := List.all_eq_true.1 alt_check_ABAB _ hmem
  rw [hw] at hc
  simp [List.range_succ, h0, h1, h2, h3, h4, h5, h6, h7] at hc


/-- With `c = 0,1,0,1,0` on `[t, t+4]`, column `-4` is white at time `t`. -/
theorem col4_white_of_alt (t : Nat) (h0 : center t = false) (h1 : center (t + 1) = true)
    (h2 : center (t + 2) = false) (h3 : center (t + 3) = true) (h4 : center (t + 4) = false) :
    cell t (-4) = false := by
  have L : ∀ (s : Nat) (i : Int), cell s (i - 1) = xor (cell (s + 1) i) (cell s i || cell s (i + 1)) :=
    cell_left
  have k := L t (-3); have hA := L (t + 1) (-2); have hB := L t (-2)
  have f2 := L (t + 2) (-1); have f1 := L (t + 1) (-1); have f0 := L t (-1)
  have a3 := L (t + 3) 0; have a2 := L (t + 2) 0; have a1 := L (t + 1) 0; have a0 := L t 0
  simp only [show (-3 : Int) - 1 = -4 by rfl, show (-2 : Int) - 1 = -3 by rfl,
    show (-1 : Int) - 1 = -2 by rfl, show (0 : Int) - 1 = -1 by rfl,
    show (-3 : Int) + 1 = -2 by rfl, show (-2 : Int) + 1 = -1 by rfl,
    show (-1 : Int) + 1 = 0 by rfl, show (0 : Int) + 1 = 1 by rfl,
    show t + 1 + 1 = t + 2 by omega, show t + 2 + 1 = t + 3 by omega,
    show t + 3 + 1 = t + 4 by omega] at k hA hB f2 f1 f0 a3 a2 a1 a0
  unfold center at h0 h1 h2 h3 h4
  -- column 1 constraint: b(t) = 1 forces b(t+2) = 0
  have hb1 : cell (t + 1) 1 = (cell t 1 || cell t 2) := by
    show rule (cell t (1 - 1)) (cell t 1) (cell t (1 + 1)) = _
    rw [show (1 : Int) - 1 = 0 by rfl, h0, show (1 : Int) + 1 = 2 by rfl]
    cases cell t 1 <;> cases cell t 2 <;> rfl
  have hb2 : cell (t + 2) 1 = !(cell (t + 1) 1 || cell (t + 1) 2) := by
    show rule (cell (t + 1) (1 - 1)) (cell (t + 1) 1) (cell (t + 1) (1 + 1)) = _
    rw [show (1 : Int) - 1 = 0 by rfl, h1, show (1 : Int) + 1 = 2 by rfl]
    cases cell (t + 1) 1 <;> cases cell (t + 1) 2 <;> rfl
  rw [k, hA, hB, f2, f1, f0, a3, a2, a1, a0, h0, h1, h2, h3, h4, hb2, hb1]
  cases cell t 1 <;> cases cell t 2 <;> cases cell (t + 1) 2 <;> cases cell (t + 3) 1 <;> rfl

/-! ### The skeleton forced by an alternating center -/

section
variable {T : Nat} (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
include h

theorem m1_even (k : Nat) : cell (T + 2 * k) (-1) = true := by
  have e := step' (T + 2 * k) 0 (-1) 0 1 rfl rfl rfl
  rw [show T + 2 * k + 1 = T + 2 * k + 1 from rfl, (h k).2, (h k).1] at e
  revert e; cases cell (T + 2 * k) (-1) <;> simp [rule]

theorem p1_odd (k : Nat) : cell (T + 2 * k + 1) 1 = !cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k + 1) 0 (-1) 0 1 rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, (h (k + 1)).1, (h k).2] at e
  revert e; cases cell (T + 2 * k + 1) (-1) <;> cases cell (T + 2 * k + 1) 1 <;> simp [rule]

theorem m2_even (k : Nat) : cell (T + 2 * k) (-2) = !cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k) (-1) (-2) (-1) 0 rfl rfl rfl
  rw [m1_even h k, (h k).1] at e
  rw [e]; cases cell (T + 2 * k) (-2) <;> rfl

theorem m2_odd (k : Nat) : cell (T + 2 * k + 1) (-2) = !cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k + 1) (-1) (-2) (-1) 0 rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, m1_even h (k + 1), (h k).2] at e
  revert e; cases cell (T + 2 * k + 1) (-2) <;> cases cell (T + 2 * k + 1) (-1) <;> simp [rule]

theorem m3_even (k : Nat) : cell (T + 2 * k) (-3) = cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k) (-2) (-3) (-2) (-1) rfl rfl rfl
  rw [m1_even h k, m2_odd h k] at e
  revert e; cases cell (T + 2 * k) (-3) <;> cases cell (T + 2 * k + 1) (-1) <;>
    cases cell (T + 2 * k) (-2) <;> simp [rule]

theorem m3_odd (k : Nat) : cell (T + 2 * k + 1) (-3) = cell (T + 2 * k + 3) (-1) := by
  have e := step' (T + 2 * k + 1) (-2) (-3) (-2) (-1) rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, m2_even h (k + 1), m2_odd h k,
    show T + 2 * (k + 1) + 1 = T + 2 * k + 3 by omega] at e
  revert e; cases cell (T + 2 * k + 1) (-3) <;> cases cell (T + 2 * k + 3) (-1) <;>
    cases cell (T + 2 * k + 1) (-1) <;> simp [rule]

/-- `s` has no two consecutive zeros. -/
theorem golden (k : Nat) (hs : cell (T + 2 * k + 1) (-1) = false) :
    cell (T + 2 * k + 3) (-1) = true := by
  have h1 : cell (T + 2 * k + 1) 1 = true := by rw [p1_odd h k, hs]; rfl
  have e1 := step' (T + 2 * k + 1) 1 0 1 2 rfl rfl rfl
  rw [(h k).2, h1] at e1
  have h2 : cell (T + 2 * k + 2) 1 = true := by rw [e1]; rfl
  have e2 := step' (T + 2 * k + 2) 1 0 1 2 rfl rfl rfl
  rw [show T + 2 * k + 2 = T + 2 * (k + 1) by omega, (h (k + 1)).1,
    show T + 2 * (k + 1) = T + 2 * k + 2 by omega, h2] at e2
  have h3 : cell (T + 2 * k + 3) 1 = false := by rw [e2]; rfl
  have := p1_odd h (k + 1)
  rw [show T + 2 * (k + 1) + 1 = T + 2 * k + 3 by omega, h3] at this
  revert this; cases cell (T + 2 * k + 3) (-1) <;> simp

/-- Column `-4` is white at every odd offset (a case of `col4_white_of_alt`). -/
theorem m4_odd (k : Nat) : cell (T + 2 * k + 1) (-4) = false := by
  refine col4_white_of_alt (T + 2 * k + 1) (h k).2 ?_ ?_ ?_ ?_
  · have := (h (k + 1)).1
    rwa [show T + 2 * (k + 1) = T + 2 * k + 1 + 1 by omega] at this
  · have := (h (k + 1)).2
    rwa [show T + 2 * (k + 1) + 1 = T + 2 * k + 1 + 2 by omega] at this
  · have := (h (k + 2)).1
    rwa [show T + 2 * (k + 2) = T + 2 * k + 1 + 3 by omega] at this
  · have := (h (k + 2)).2
    rwa [show T + 2 * (k + 2) + 1 = T + 2 * k + 1 + 4 by omega] at this

end

/-! ### Reduction to the zero-driven left half -/

/-- Under an alternating center the effective boundary `c t && c (t + 1)` is white. -/
theorem effective_white {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
    (k : Nat) : (center (T + k) && center (T + k + 1)) = false := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
    rw [(h j).2]; cases cell (T + 2 * j) 0 <;> rfl
  · show (cell (T + (2 * j + 1)) 0 && cell (T + (2 * j + 1) + 1) 0) = false
    rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega, (h j).2]; rfl

/-- **The left half is the zero-driven left half.** Under an alternating center from `T`, the
columns `p < 0` evolve from the row at time `T` as rule 30 on `p < 0` with column `0` held
white. -/
theorem left_half_zero_driven {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) :
    ∀ k : Nat, ∀ p : Int, p < 0 → L (fun _ => false) (fun p => cell T p) k p = cell (T + k) p := by
  have hfun : (fun k => center (T + k) && center (T + k + 1)) = fun _ => false :=
    funext (effective_white h)
  intro k p hp
  have := cell_eq_L_effective T k p hp
  rwa [hfun] at this

/-- **`Q₀₁`.** No start of the zero-driven left half with a leftmost black cell (at `-m`,
`m ≥ 1`, white beyond) keeps column `-1` black at every even step. Open. -/
def Q01 : Prop :=
  ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, L (fun _ => false) s (2 * k) (-1) = true

/-- **`Q₀₁` excludes period `2`.** If `Q01` holds, the center column is not eventually
2-periodic, whatever the transient. -/
theorem not_eventually_period_two_of_Q01 (hQ : Q01) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := normalize hp
  -- one period later the start time is at least `1`, so the start has a leftmost black cell
  have h' : ∀ k, cell (T + 2 + 2 * k) 0 = true ∧ cell (T + 2 + 2 * k + 1) 0 = false := by
    intro k
    have := hT (k + 1)
    rw [show T + 2 * (k + 1) = T + 2 + 2 * k by omega] at this
    exact this
  refine hQ (T + 2) (fun p => cell (T + 2) p) (by omega)
    (fun p hp => cell_eq_false_of_lt (T + 2) p hp) (cell_left_edge (T + 2)) (fun k => ?_)
  rw [left_half_zero_driven h' (2 * k) (-1) (by omega)]
  exact m1_even h' k

/-- The stripe: black exactly at the odd positions. -/
def stripe (p : Int) : Bool := decide (p % 2 = 1)

/-- The stripe is a fixed point of the zero-driven left half. -/
theorem stripe_fixed : ∀ t : Nat, ∀ p : Int, p < 0 → L (fun _ => false) stripe t p = stripe p := by
  intro t
  induction t with
  | zero => intro p hp; exact L_zero hp
  | succ t ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), ih p hp]
    by_cases hq : p + 1 < 0
    · rw [ih (p + 1) hq]
      simp only [stripe, rule]
      have : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases this with h | h
      · have h1 : (p - 1) % 2 = 1 := by omega
        have h2 : (p + 1) % 2 = 1 := by omega
        simp [h, h1, h2]
      · have h1 : (p - 1) % 2 = 0 := by omega
        have h2 : (p + 1) % 2 = 0 := by omega
        simp [h, h1, h2]
    · have hp1 : p = -1 := by omega
      subst hp1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0]
      decide

/-- **Finiteness is essential in `Q01`**: from the (infinite) stripe, column `-1` of the
zero-driven left half is black at every step. -/
theorem stripe_col (t : Nat) : L (fun _ => false) stripe t (-1) = true := by
  rw [stripe_fixed t (-1) (by omega)]; decide

end Rule30PeriodTwo
end Ruliology.CellularAutomata
