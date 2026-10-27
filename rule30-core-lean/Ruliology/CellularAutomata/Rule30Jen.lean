module

/-!
# Rule 30: no two columns are both eventually periodic (Jen 1986)

Wolfram, *Announcing the Rule 30 Prizes* (2019): "Erica Jen showed in 1986 that no two columns
can both become periodic." The pattern is the classic evolution of rule 30 from a single black
cell.
<https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/>
E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242.

* `jen`: two different columns of the pattern are never both eventually periodic.
* `periodic_column_unique`: at most one column is eventually periodic. Whether the center column
  is aperiodic, the Rule 30 Prize's Problem 1, is open.

**Proof.**
- Rule 30 is `l xor (c || r)`, so `cell t (i - 1) = cell (t + 1) i xor (cell t i || cell t (i + 1))`
  (`cell_left`). If two adjacent columns are eventually periodic (same start, same period), every
  column to their left is too (`periodic_left_all`).
- That is impossible: the left edge of the pattern moves left one cell per step. Far to the left,
  a column is white until the edge reaches it and black at that moment, which contradicts
  periodicity (`no_left_periodic`).
- For columns `j < k` that are not adjacent: the strip strictly between them evolves
  deterministically from its own state and the two boundary columns (`strip_agree`). With
  eventually periodic boundaries, pigeonhole over the `2 ^ (k - j - 1)` strip states makes the
  strip eventually periodic (`between_periodic`). So column `j + 1` is eventually periodic, and
  the adjacent case applies.
-/

@[expose] public section

theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} :
    (if c then t else e) = t := @if_pos c h hc α t e

theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} :
    (if c then t else e) = e := @if_neg c h hnc α t e

namespace Ruliology.CellularAutomata
namespace Rule30Jen

/-- Rule 30: `left xor (center || right)`. -/
def rule (a b c : Bool) : Bool := xor a (b || c)

/-- Rule 30 from a single black cell at position `0`: `cell t p` is the color (`true` = black)
at position `p` after `t` steps. -/
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

/-- A sequence of colors is eventually periodic. -/
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

/-! ### The left edge -/

theorem cell_eq_false_of_lt : ∀ (t : Nat) (p : Int), p < -(t : Int) → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_lt t (p - 1) (by omega), cell_eq_false_of_lt t p (by omega),
      cell_eq_false_of_lt t (p + 1) (by omega)]
    rfl

/-- The leftmost black cell is at `-t`. -/
theorem cell_left_edge : ∀ t : Nat, cell t (-(t : Int)) = true
  | 0 => rfl
  | t + 1 => by
    show rule (cell t (-((t + 1 : Nat) : Int) - 1)) (cell t (-((t + 1 : Nat) : Int)))
      (cell t (-((t + 1 : Nat) : Int) + 1)) = true
    rw [cell_eq_false_of_lt t _ (by omega), cell_eq_false_of_lt t _ (by omega),
      show -((t + 1 : Nat) : Int) + 1 = -(t : Int) by omega, cell_left_edge t]
    rfl

/-! ### Reconstruction to the left -/

theorem cell_left (t : Nat) (i : Int) :
    cell t (i - 1) = xor (cell (t + 1) i) (cell t i || cell t (i + 1)) := by
  show cell t (i - 1) = xor (rule (cell t (i - 1)) (cell t i) (cell t (i + 1))) (cell t i || cell t (i + 1))
  cases cell t (i - 1) <;> cases cell t i <;> cases cell t (i + 1) <;> rfl

theorem periodic_left {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell (t + P) (i + 1) = cell t (i + 1)) :
    ∀ t, T ≤ t → cell (t + P) (i - 1) = cell t (i - 1) := by
  intro t ht
  rw [cell_left, cell_left t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

/-- If two adjacent columns are periodic from `T` with period `P`, so is every column to their
left. -/
theorem periodic_left_all {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell (t + P) (i + 1) = cell t (i + 1)) :
    ∀ m : Nat, (∀ t, T ≤ t → cell (t + P) (i - m) = cell t (i - m)) ∧
      ∀ t, T ≤ t → cell (t + P) (i - m + 1) = cell t (i - m + 1) := by
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · have := periodic_left ih.1 ih.2
      rwa [show i - (m : Int) - 1 = i - ((m + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((m + 1 : Nat) : Int) + 1 = i - (m : Int) by omega]
      exact ih.1

/-- No column far enough to the left is periodic: the edge reaches it once. -/
theorem no_left_periodic {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ m : Nat, ∀ t, T ≤ t → cell (t + P) (i - m) = cell t (i - m)) : False := by
  -- a column `q ≤ i` left of `-(T + P)`
  let q : Int := min i (-((T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ -((T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = -q := ⟨(-q).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : cell t₁ q = true := by
    have := cell_left_edge t₁
    rwa [show -(t₁ : Int) = q by omega] at this
  have hwhite : cell (t₁ - P) q = false := cell_eq_false_of_lt _ _ (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

/-! ### Periods -/

theorem periodic_mul {f : Nat → Bool} {T P : Nat} (h : ∀ t, T ≤ t → f (t + P) = f t) :
    ∀ n t, T ≤ t → f (t + n * P) = f t
  | 0, t, _ => by simp
  | n + 1, t, ht => by
    rw [show t + (n + 1) * P = (t + n * P) + P by rw [Nat.succ_mul]; omega,
      h (t + n * P) (by omega), periodic_mul h n t ht]

/-- Two eventually periodic sequences share a start and a period. -/
theorem common_period {f g : Nat → Bool} (hf : EventuallyPeriodic f) (hg : EventuallyPeriodic g) :
    ∃ T P : Nat, 0 < P ∧ (∀ t, T ≤ t → f (t + P) = f t) ∧ ∀ t, T ≤ t → g (t + P) = g t := by
  obtain ⟨T₁, P₁, hP₁, h₁⟩ := hf
  obtain ⟨T₂, P₂, hP₂, h₂⟩ := hg
  refine ⟨max T₁ T₂, P₁ * P₂, Nat.mul_pos hP₁ hP₂, fun t ht => ?_, fun t ht => ?_⟩
  · rw [Nat.mul_comm]; exact periodic_mul h₁ P₂ t (by omega)
  · exact periodic_mul h₂ P₁ t (by omega)

/-! ### The strip between two columns -/

/-- The cells strictly between columns `j` and `k` at step `t`. -/
def strip (j k : Int) (t : Nat) : List Bool :=
  (List.range (k - j - 1).toNat).map fun (r : Nat) => cell t (j + 1 + (r : Int))

set_option linter.unusedSimpArgs false in
/-- The strip evolves from its own state and the two boundary columns. -/
theorem strip_agree {j k : Int} (hjk : j < k) {t₁ t₂ : Nat} (hs : strip j k t₁ = strip j k t₂)
    (hb : ∀ r, cell (t₁ + r) j = cell (t₂ + r) j ∧ cell (t₁ + r) k = cell (t₂ + r) k) :
    ∀ r, ∀ i, j ≤ i → i ≤ k → cell (t₁ + r) i = cell (t₂ + r) i := by
  intro r
  induction r with
  | zero =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb 0).1
    by_cases e2 : i = k
    · subst e2; exact (hb 0).2
    have := congrArg (fun l => l.getD (i - j - 1).toNat false) hs
    simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show (i - j - 1).toNat < (k - j - 1).toNat by omega),
      Option.map_some, Option.getD_some] at this
    rwa [show j + 1 + (((i - j - 1).toNat : Nat) : Int) = i by omega] at this
  | succ r ih =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb (r + 1)).1
    by_cases e2 : i = k
    · subst e2; exact (hb (r + 1)).2
    show rule (cell (t₁ + r) (i - 1)) (cell (t₁ + r) i) (cell (t₁ + r) (i + 1)) =
      rule (cell (t₂ + r) (i - 1)) (cell (t₂ + r) i) (cell (t₂ + r) (i + 1))
    rw [ih (i - 1) (by omega) (by omega), ih i (by omega) (by omega), ih (i + 1) (by omega) (by omega)]

/-- All Boolean lists of length `n`. -/
def allLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).map (false :: ·) ++ (allLists n).map (true :: ·)

theorem mem_allLists : ∀ (l : List Bool), l ∈ allLists l.length
  | [] => by simp [allLists]
  | b :: l => by
    cases b <;> simp [allLists, mem_allLists l]

theorem length_allLists : ∀ n, (allLists n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by simp [allLists, length_allLists n, Nat.pow_succ]; omega

theorem length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l₁, l₂, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ l₂ := hs x (by simp)
    have := length_le_of_subset (l₂ := l₂.erase x) hn.2 fun y hy =>
      (List.mem_erase_of_ne (fun (e : y = x) => hn.1 (by rw [← e]; exact hy))).2 (hs y (by simp [hy]))
    rw [List.length_erase_of_mem hx] at this
    simp only [List.length_cons]
    have : 0 < l₂.length := List.length_pos_of_mem hx
    omega

theorem nodup_map_of_inj {α β : Type} (f : α → β) : ∀ {l : List α}, l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, hinj => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj f hl.2 fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    exact hl.1 (hinj a (by simp) b (by simp [hb]) hfb.symm ▸ hb)

/-- Pigeonhole: among `2 ^ w + 1` lists of length `w`, two are equal. -/
theorem pigeonhole (w : Nat) (a : Nat → List Bool) (ha : ∀ m, (a m).length = w) :
    ∃ m n, m < n ∧ n ≤ 2 ^ w ∧ a m = a n := by
  refine Classical.byContradiction fun hne => ?_
  have hinj : ∀ m ∈ List.range (2 ^ w + 1), ∀ n ∈ List.range (2 ^ w + 1), a m = a n → m = n := by
    intro m hm n hn e
    simp only [List.mem_range] at hm hn
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd ⟨m, n, h, by omega, e⟩ hne
    · exact h
    · exact absurd ⟨n, m, h, by omega, e.symm⟩ hne
  have hnd := nodup_map_of_inj a List.nodup_range hinj
  have := length_le_of_subset hnd fun x hx => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    have := mem_allLists (a m)
    rwa [ha m] at this
  simp only [List.length_map, List.length_range, length_allLists] at this
  omega

/-- **Between two eventually periodic columns, the next column is eventually periodic.** -/
theorem between_periodic {j k : Int} (hjk : j + 1 < k)
    (hj : EventuallyPeriodic fun t => cell t j) (hk : EventuallyPeriodic fun t => cell t k) :
    EventuallyPeriodic fun t => cell t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have key := strip_agree (by omega) he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1) (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by
        rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => cell t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => cell t k) hpk (n - m) _ (by omega)).symm

/-! ### Jen's theorem -/

/-- Two adjacent columns are never both eventually periodic. -/
theorem not_adjacent (i : Int) (h0 : EventuallyPeriodic fun t => cell t i)
    (h1 : EventuallyPeriodic fun t => cell t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact no_left_periodic hP fun m => (periodic_left_all hp0 hp1 m).1

/-- **Jen's theorem.** No two different columns of rule 30 from a single black cell are both
eventually periodic. -/
theorem jen (j k : Int) (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => cell t j) ∧ EventuallyPeriodic (fun t => cell t k)) := by
  have lt_case : ∀ a b : Int, a < b → (EventuallyPeriodic fun t => cell t a) →
      (EventuallyPeriodic fun t => cell t b) → False := by
    intro a b hab ha hb
    by_cases hadj : b = a + 1
    · subst hadj; exact not_adjacent a ha hb
    · exact not_adjacent a ha (between_periodic (by omega) ha hb)
  rintro ⟨hj, hk⟩
  rcases Int.lt_or_gt_of_ne hjk with h | h
  · exact lt_case j k h hj hk
  · exact lt_case k j h hk hj

/-- **At most one column is eventually periodic.** -/
theorem periodic_column_unique (j k : Int) (hj : EventuallyPeriodic fun t => cell t j)
    (hk : EventuallyPeriodic fun t => cell t k) : j = k :=
  Classical.byContradiction fun h => jen j k h ⟨hj, hk⟩

end Rule30Jen
end Ruliology.CellularAutomata
