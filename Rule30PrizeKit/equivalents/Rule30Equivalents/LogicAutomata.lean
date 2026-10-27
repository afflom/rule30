module

public import Rule30Equivalents.ShiftOrbit
public import Mathlib.ModelTheory.Arithmetic.Presburger.Definability
public import Mathlib.Computability.MyhillNerode

/-!
# Problem 1 in logic and automata

A `Bool` sequence is eventually periodic exactly when its set of black times is *ultimately
periodic*, Mathlib's notion for subsets of `ℕ`. Mathlib characterizes those sets in two classical
ways, and Myhill–Nerode gives two more:

* `problem1_iff_not_presburger`: the set of black times of the centre column is not definable in
  Presburger arithmetic `(ℕ, +)`, with any set of parameters (Presburger 1929; Ginsburg–Spanier 1966).
* `problem1_iff_not_semilinear`: that set is not semilinear.
* `problem1_iff_unary_not_regular`: the unary language `{1ⁿ : c(n) = 1}` is not regular.
* `problem1_iff_prefixes_not_regular`: the language of finite prefixes of the centre column is not
  regular.

For the two languages the proof counts left quotients (Myhill–Nerode): the quotients of the unary
language are the unary languages of the shifts of `c`, and those of the prefix language are the
prefix languages of the shifts together with the empty language. Both counts are finite exactly
when the shift orbit is finite (`ShiftOrbit.eventuallyPeriodic_iff_finite_shifts`).
-/

@[expose] public section

namespace Rule30Equivalents.LogicAutomata

open Ruliology.CellularAutomata

/-- Eventual periodicity is ultimate periodicity of the set of `true` times, in Mathlib's form. -/
theorem eventuallyPeriodic_iff_ultimately_periodic (b : ℕ → Bool) :
    EventuallyPeriodic b ↔
      ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ {t | b t = true} ↔ x + p ∈ {t | b t = true} := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun x hx => by simp only [Set.mem_ofPred_eq, h x hx]⟩
  · rintro ⟨k, p, hp, h⟩
    refine ⟨k, p, hp, fun t ht => ?_⟩
    have := h t ht
    simp only [Set.mem_ofPred_eq] at this
    cases h1 : b t <;> cases h2 : b (t + p) <;> simp_all

/-! ### Presburger arithmetic and semilinear sets -/

/-- **Problem 1 ⟺ the black times are not Presburger-definable**, with any parameters `A`. -/
theorem problem1_iff_not_presburger (A : Set ℕ) :
    Rule30Prize.Problem1 ↔ ¬ A.Definable₁ FirstOrder.Language.presburger {t | c t = true} := by
  rw [FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic,
    ← eventuallyPeriodic_iff_ultimately_periodic]
  rfl

/-- **Problem 1 ⟺ the black times do not form a semilinear set.** -/
theorem problem1_iff_not_semilinear :
    Rule30Prize.Problem1 ↔ ¬ IsSemilinearSet {t : ℕ | c t = true} := by
  rw [Nat.isSemilinearSet_iff_ultimately_periodic, ← eventuallyPeriodic_iff_ultimately_periodic]
  rfl

/-! ### The unary language of the black times -/

/-- The unary language `{1ⁿ : b n = true}`. -/
def unaryLang (b : ℕ → Bool) : Language Unit := {l : List Unit | b l.length = true}

theorem leftQuotient_unaryLang (b : ℕ → Bool) (x : List Unit) :
    (unaryLang b).leftQuotient x = unaryLang (fun m => b (x.length + m)) := by
  ext y
  rw [Language.mem_leftQuotient]
  change b (x ++ y).length = true ↔ b (x.length + y.length) = true
  rw [List.length_append]

theorem unaryLang_injective : Function.Injective unaryLang := by
  intro f g h
  funext m
  have := congrArg (fun L : Language Unit => List.replicate m () ∈ L) h
  simp only [unaryLang] at this
  change (f (List.replicate m ()).length = true) = (g (List.replicate m ()).length = true) at this
  simp only [List.length_replicate] at this
  cases hf : f m <;> cases hg : g m <;> simp_all

theorem range_leftQuotient_unaryLang (b : ℕ → Bool) :
    Set.range (unaryLang b).leftQuotient =
      unaryLang '' Set.range (fun n : ℕ => fun t => b (n + t)) := by
  ext L
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x.length, rfl⟩, (leftQuotient_unaryLang b x).symm⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨List.replicate n (), by rw [leftQuotient_unaryLang, List.length_replicate]⟩

/-- A `Bool` sequence is eventually periodic iff its unary language is regular. -/
theorem eventuallyPeriodic_iff_unary_isRegular (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ (unaryLang b).IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient, range_leftQuotient_unaryLang,
    Set.finite_image_iff unaryLang_injective.injOn, ShiftOrbit.eventuallyPeriodic_iff_finite_shifts]

/-- **Problem 1 ⟺ the unary language `{1ⁿ : c(n) = 1}` is not regular.** -/
theorem problem1_iff_unary_not_regular : Rule30Prize.Problem1 ↔ ¬ (unaryLang c).IsRegular :=
  not_congr (eventuallyPeriodic_iff_unary_isRegular c)

/-! ### The language of prefixes -/

/-- The finite prefixes of `b`. -/
def prefLang (b : ℕ → Bool) : Language Bool :=
  {l : List Bool | l = (List.range l.length).map b}

theorem mem_prefLang {b : ℕ → Bool} {l : List Bool} :
    l ∈ prefLang b ↔ l = (List.range l.length).map b := Iff.rfl

theorem range_mem_prefLang (b : ℕ → Bool) (n : ℕ) : (List.range n).map b ∈ prefLang b := by
  rw [mem_prefLang, List.length_map, List.length_range]

theorem map_range_add (b : ℕ → Bool) (m n : ℕ) :
    (List.range (m + n)).map b =
      (List.range m).map b ++ (List.range n).map (fun k => b (m + k)) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem append_mem_prefLang {b : ℕ → Bool} {x y : List Bool} (hx : x ∈ prefLang b) :
    x ++ y ∈ prefLang b ↔ y ∈ prefLang (fun k => b (x.length + k)) := by
  rw [mem_prefLang, mem_prefLang, List.length_append, map_range_add]
  rw [mem_prefLang] at hx
  constructor
  · intro h
    conv_lhs at h => rw [hx]
    exact List.append_cancel_left h
  · intro h
    conv_lhs => rw [hx, h]

theorem append_not_mem_prefLang {b : ℕ → Bool} {x : List Bool} (hx : x ∉ prefLang b)
    (y : List Bool) : x ++ y ∉ prefLang b := by
  intro h
  apply hx
  rw [mem_prefLang, List.length_append, map_range_add] at h
  have := congrArg (List.take x.length) h
  rw [List.take_left' rfl, List.take_left' (by simp)] at this
  exact this

theorem leftQuotient_prefLang_of_mem (b : ℕ → Bool) {x : List Bool} (hx : x ∈ prefLang b) :
    (prefLang b).leftQuotient x = prefLang (fun k => b (x.length + k)) := by
  ext y
  rw [Language.mem_leftQuotient]
  exact append_mem_prefLang hx

theorem leftQuotient_prefLang_of_not_mem (b : ℕ → Bool) {x : List Bool} (hx : x ∉ prefLang b) :
    (prefLang b).leftQuotient x = 0 := by
  ext y
  rw [Language.mem_leftQuotient]
  exact ⟨fun h => absurd h (append_not_mem_prefLang hx y),
    fun h => absurd h (Language.notMem_zero y)⟩

theorem prefLang_injective : Function.Injective prefLang := by
  intro f g h
  funext m
  have hm := range_mem_prefLang f (m + 1)
  rw [h, mem_prefLang, List.length_map, List.length_range, List.map_inj_left] at hm
  exact hm m (List.mem_range.2 (Nat.lt_succ_self m))

theorem range_leftQuotient_prefLang (b : ℕ → Bool) :
    Set.range (prefLang b).leftQuotient ⊆
      insert 0 (prefLang '' Set.range (fun n : ℕ => fun t => b (n + t))) := by
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ prefLang b
  · rw [leftQuotient_prefLang_of_mem b hx]
    exact Or.inr ⟨_, ⟨x.length, rfl⟩, rfl⟩
  · rw [leftQuotient_prefLang_of_not_mem b hx]
    exact Or.inl rfl

theorem image_subset_range_leftQuotient (b : ℕ → Bool) :
    prefLang '' (Set.range (fun n : ℕ => fun t => b (n + t))) ⊆
      Set.range (prefLang b).leftQuotient := by
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  refine ⟨(List.range n).map b, ?_⟩
  rw [leftQuotient_prefLang_of_mem b (range_mem_prefLang b n), List.length_map, List.length_range]

/-- A `Bool` sequence is eventually periodic iff its prefix language is regular. -/
theorem eventuallyPeriodic_iff_prefLang_isRegular (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ (prefLang b).IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient,
    ShiftOrbit.eventuallyPeriodic_iff_finite_shifts]
  constructor
  · intro h
    exact ((h.image prefLang).insert 0).subset (range_leftQuotient_prefLang b)
  · intro h
    exact (Set.finite_image_iff prefLang_injective.injOn).1
      (h.subset (image_subset_range_leftQuotient b))

/-- **Problem 1 ⟺ the language of prefixes of the centre column is not regular.** -/
theorem problem1_iff_prefixes_not_regular : Rule30Prize.Problem1 ↔ ¬ (prefLang c).IsRegular :=
  not_congr (eventuallyPeriodic_iff_prefLang_isRegular c)

end Rule30Equivalents.LogicAutomata
