module

public import Rule30Equivalents.RandomConfigurations
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.PartrecCode
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Tauto
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Problem 1 is Π⁰₂ and Problem 2 is Π⁰₃

Row `t + 1` of the single-seed pattern is a primitive recursive
function of row `t`, stored as the list of its cells `-t, …, t` (`stepList`, `getD_rowList`). So:

* `primrec_center`: **the center column `c` is primitive recursive**.
* `problem1_iff_forall_exists_defect`: Problem 1 says that for every time `T` and every period
  `P + 1` some `t ≥ T` has `c(t + P + 1) ≠ c(t)`, a primitive recursive condition on `(T, P, t)`
  (`primrec_defect`). So **Problem 1 is a Π⁰₂ sentence**, and its negation is Σ⁰₂.
* `problem1_iff_firstDefect_dom`: **Problem 1 holds iff a partial recursive function is total**:
  the unbounded search for the first such `t` (`firstDefect`, `partrec_firstDefect`) halts on
  every input `(T, P)`. A counterexample is an input on which it runs forever, so no finite
  computation settles Problem 1 in either direction.
* `problem2_iff_forall_exists_forall`: Problem 2 says that for every `k` there is an `N` such that
  `(k + 1) |2 N(n) - n| ≤ n` for every `n ≥ N`, where `N(n)` counts the black cells among the
  first `n`; the condition is primitive recursive (`primrec_balanced`). So **Problem 2 is Π⁰₃**.
* `ae_not_computable_trace`, `residual_not_computable_trace`: **the center column of almost every
  and of a generic configuration is not computable**. Computable sequences are countably many
  (`countable_computable`, through Mathlib's codes for partial recursive functions); the fair-coin
  measure has no atoms (`RandomConfigurations.coins_singleton`), and a single sequence is nowhere
  dense (`Genericity.isNowhereDense_singleton`). The seed is special in this respect too.
-/

@[expose] public section

namespace Rule30Equivalents.Computability

open Ruliology.CellularAutomata Rule30Jen

/-! ### The rows as lists -/

/-- One step of rule 30 on a row stored as a list, white beyond its ends. The new row is two
cells longer. -/
def stepList (l : List Bool) : List Bool :=
  (List.range (l.length + 2)).map fun i =>
    rule ((false :: false :: l).getD i false) ((false :: false :: l).getD (i + 1) false)
      ((false :: false :: l).getD (i + 2) false)

/-- Row `t` of the single-seed pattern: the cells `-t, …, t`. -/
def rowList (t : ℕ) : List Bool := stepList^[t] [true]

theorem rowList_succ (t : ℕ) : rowList (t + 1) = stepList (rowList t) :=
  Function.iterate_succ_apply' _ _ _

theorem length_stepList (l : List Bool) : (stepList l).length = l.length + 2 := by
  simp [stepList]

theorem length_rowList (t : ℕ) : (rowList t).length = 2 * t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [rowList_succ, length_stepList, ih]
    omega

theorem getD_stepList (l : List Bool) (i : ℕ) :
    (stepList l).getD i false = if i < l.length + 2 then
      rule ((false :: false :: l).getD i false) ((false :: false :: l).getD (i + 1) false)
        ((false :: false :: l).getD (i + 2) false) else false := by
  unfold stepList
  by_cases hi : i < l.length + 2
  · rw [ite_eq_left hi, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  · rw [ite_eq_right hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

/-- **The list rows are the rows of the single-seed pattern**: entry `i` of row `t` is the cell
`i - t`, and the entries beyond the end are white like the cells beyond the light cone. -/
theorem getD_rowList (t : ℕ) : ∀ i : ℕ, (rowList t).getD i false = cell t (i - t) := by
  induction t with
  | zero =>
    intro i
    rcases i with _ | i
    · rfl
    · simp [rowList, cell]
      omega
  | succ t ih =>
    -- the row padded with two white cells on the left
    have hpad : ∀ k : ℕ, (false :: false :: rowList t).getD k false = cell t (k - 2 - t) := by
      intro k
      rcases k with _ | _ | k
      · exact (cell_eq_false_of_lt t _ (by omega)).symm
      · exact (cell_eq_false_of_lt t _ (by omega)).symm
      · rw [List.getD_cons_succ, List.getD_cons_succ, ih k]
        congr 1
        omega
    intro i
    rw [rowList_succ, getD_stepList, length_rowList, hpad, hpad, hpad]
    split_ifs with hi
    · have e1 : ((i : ℕ) : ℤ) - 2 - t = (i - (t + 1 : ℕ)) - 1 := by omega
      have e2 : (((i + 1 : ℕ) : ℤ)) - 2 - t = i - (t + 1 : ℕ) := by omega
      have e3 : (((i + 2 : ℕ) : ℤ)) - 2 - t = (i - (t + 1 : ℕ)) + 1 := by omega
      rw [e1, e2, e3]
      rfl
    · exact (Rule30Diagonals.cell_eq_false_of_gt (t + 1) _ (by omega)).symm

theorem center_eq_getD (t : ℕ) : Rule30Prize.center t = (rowList t).getD t false := by
  rw [getD_rowList, sub_self]
  rfl

/-! ### Primitive recursion -/

theorem primrec_stepList : Primrec stepList := by
  have hpad : Primrec fun l : List Bool => false :: false :: l :=
    Primrec.list_cons.comp (Primrec.const false)
      (Primrec.list_cons.comp (Primrec.const false) Primrec.id)
  have hget : ∀ k : ℕ,
      Primrec fun p : List Bool × ℕ => (false :: false :: p.1).getD (p.2 + k) false :=
    fun k => (Primrec.list_getD false).comp (hpad.comp Primrec.fst)
      (Primrec.nat_add.comp Primrec.snd (Primrec.const k))
  have hrule : Primrec fun q : Bool × Bool × Bool => rule q.1 q.2.1 q.2.2 := Primrec.dom_finite _
  have hg : Primrec₂ fun (l : List Bool) (i : ℕ) =>
      rule ((false :: false :: l).getD i false) ((false :: false :: l).getD (i + 1) false)
        ((false :: false :: l).getD (i + 2) false) :=
    hrule.comp ((hget 0).pair ((hget 1).pair (hget 2)))
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.list_length (Primrec.const 2))) hg

theorem primrec_rowList : Primrec rowList :=
  Primrec.nat_iterate Primrec.id (Primrec.const [true])
    (primrec_stepList.comp Primrec.snd : Primrec₂ fun (_ : ℕ) (l : List Bool) => stepList l)

/-- **The center column is primitive recursive.** -/
theorem primrec_center : Primrec Rule30Prize.center :=
  ((Primrec.list_getD false).comp primrec_rowList Primrec.id).of_eq fun t =>
    (center_eq_getD t).symm

/-! ### Problem 1 -/

/-- A defect of the period `P + 1` at a time `t ≥ T`: `c(t + P + 1) ≠ c(t)`. -/
def defect (T P t : ℕ) : Bool := decide (T ≤ t) && (c (t + P + 1) != c t)

theorem primrec_defect : Primrec fun q : ℕ × ℕ × ℕ => defect q.1 q.2.1 q.2.2 := by
  have hle : Primrec fun q : ℕ × ℕ × ℕ => decide (q.1 ≤ q.2.2) :=
    Primrec.nat_le.decide.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hc1 : Primrec fun q : ℕ × ℕ × ℕ => c (q.2.2 + q.2.1 + 1) :=
    primrec_center.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)) (Primrec.const 1))
  have hc0 : Primrec fun q : ℕ × ℕ × ℕ => c q.2.2 :=
    primrec_center.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec fun x : Bool × Bool × Bool => x.1 && (x.2.1 != x.2.2) := Primrec.dom_finite _
  exact hb.comp (hle.pair (hc1.pair hc0))

/-- **Problem 1 is Π⁰₂**: for every time `T` and period `P + 1` there is a defect. -/
theorem problem1_iff_forall_exists_defect :
    Rule30Prize.Problem1 ↔ ∀ T P : ℕ, ∃ t, defect T P t = true := by
  constructor
  · intro h T P
    by_contra hne
    push Not at hne
    refine h ⟨T, P + 1, Nat.succ_pos P, fun t ht => ?_⟩
    have := hne t
    simp only [defect, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
      not_not] at this
    rw [← add_assoc]
    exact this ht
  · rintro h ⟨T, P, hP, hper⟩
    obtain ⟨t, ht⟩ := h T (P - 1)
    simp only [defect, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at ht
    exact ht.2 (by rw [show t + (P - 1) + 1 = t + P by omega]; exact hper t ht.1)

/-- The first time `t ≥ T` with a defect of the period `P + 1`, found by unbounded search. -/
def firstDefect (TP : ℕ × ℕ) : Part ℕ := Nat.rfind fun t => Part.some (defect TP.1 TP.2 t)

theorem partrec_firstDefect : Partrec firstDefect := by
  have h : Primrec₂ fun (TP : ℕ × ℕ) (t : ℕ) => defect TP.1 TP.2 t :=
    primrec_defect.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  exact Partrec.rfind h.to_comp.partrec₂

theorem firstDefect_dom (TP : ℕ × ℕ) :
    (firstDefect TP).Dom ↔ ∃ t, defect TP.1 TP.2 t = true := by
  let p : ℕ →. Bool := fun t => Part.some (defect TP.1 TP.2 t)
  exact (@Nat.rfind_dom p).trans ⟨fun ⟨t, h, _⟩ => ⟨t, (Part.mem_some_iff.1 h).symm⟩,
    fun ⟨t, h⟩ => ⟨t, Part.mem_some_iff.2 h.symm, fun _ => trivial⟩⟩

/-- **Problem 1 as the totality of a partial recursive function**: the search for a defect halts on
every input. -/
theorem problem1_iff_firstDefect_dom : Rule30Prize.Problem1 ↔ ∀ TP, (firstDefect TP).Dom := by
  rw [problem1_iff_forall_exists_defect]
  simp only [firstDefect_dom]
  exact ⟨fun h TP => h TP.1 TP.2, fun h T P => h (T, P)⟩

/-! ### Problem 2 -/

/-- The number of black cells among the first `n` cells of the center column, by recursion. -/
theorem blackCount_succ (n : ℕ) :
    Rule30Prize.blackCount (n + 1) = Rule30Prize.blackCount n + if c n then 1 else 0 := by
  simp only [Rule30Prize.blackCount, List.range_succ, List.filter_append, List.length_append]
  cases h : c n <;> simp [h]

theorem primrec_blackCount : Primrec Rule30Prize.blackCount := by
  have hind : Primrec fun p : ℕ × ℕ => if c p.1 then 1 else 0 :=
    (Primrec.cond (primrec_center.comp Primrec.fst) (Primrec.const 1) (Primrec.const 0)).of_eq
      fun p => by cases h : c p.1 <;> simp [h]
  have h : Primrec₂ fun (n a : ℕ) => a + if c n then 1 else 0 :=
    Primrec.nat_add.comp Primrec.snd hind
  refine (Primrec.nat_rec₁ 0 h).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [blackCount_succ, ← ih]

/-- `(k + 1) |2 N(n) - n| ≤ n` once `n ≥ N`, in natural numbers. -/
def balanced (k N n : ℕ) : Bool :=
  !decide (N ≤ n) ||
    (decide ((k + 1) * (2 * Rule30Prize.blackCount n) ≤ (k + 1) * n + n) &&
      decide ((k + 1) * n ≤ (k + 1) * (2 * Rule30Prize.blackCount n) + n))

theorem primrec_balanced : Primrec fun q : ℕ × ℕ × ℕ => balanced q.1 q.2.1 q.2.2 := by
  have hn : Primrec fun q : ℕ × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
  have hk : Primrec fun q : ℕ × ℕ × ℕ => q.1 + 1 :=
    Primrec.nat_add.comp Primrec.fst (Primrec.const 1)
  have ha : Primrec fun q : ℕ × ℕ × ℕ => 2 * Rule30Prize.blackCount q.2.2 :=
    Primrec.nat_mul.comp (Primrec.const 2) (primrec_blackCount.comp hn)
  have h1 : Primrec fun q : ℕ × ℕ × ℕ => decide (q.2.1 ≤ q.2.2) :=
    Primrec.nat_le.decide.comp (Primrec.fst.comp Primrec.snd) hn
  have h2 : Primrec fun q : ℕ × ℕ × ℕ =>
      decide ((q.1 + 1) * (2 * Rule30Prize.blackCount q.2.2) ≤ (q.1 + 1) * q.2.2 + q.2.2) :=
    Primrec.nat_le.decide.comp (Primrec.nat_mul.comp hk ha)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hk hn) hn)
  have h3 : Primrec fun q : ℕ × ℕ × ℕ =>
      decide ((q.1 + 1) * q.2.2 ≤ (q.1 + 1) * (2 * Rule30Prize.blackCount q.2.2) + q.2.2) :=
    Primrec.nat_le.decide.comp (Primrec.nat_mul.comp hk hn)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hk ha) hn)
  have hb : Primrec fun x : Bool × Bool × Bool => !x.1 || (x.2.1 && x.2.2) := Primrec.dom_finite _
  exact hb.comp (h1.pair (h2.pair h3))

/-- `k |2a - n| ≤ n` in natural numbers. -/
theorem mul_natAbs_le_iff (k a n : ℕ) :
    k * (2 * (a : ℤ) - n).natAbs ≤ n ↔ k * (2 * a) ≤ k * n + n ∧ k * n ≤ k * (2 * a) + n := by
  have hk : (0 : ℤ) ≤ k := Nat.cast_nonneg k
  have e : ((k * (2 * (a : ℤ) - n).natAbs : ℕ) : ℤ) = |(k : ℤ) * (2 * a - n)| := by
    rw [Nat.cast_mul, Int.natCast_natAbs, abs_mul, abs_of_nonneg hk]
  rw [← Nat.cast_le (α := ℤ), e, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> zify <;> linarith
  · rintro ⟨h1, h2⟩
    zify at h1 h2
    constructor <;> linarith

/-- **Problem 2 is Π⁰₃**: for every `k` there is an `N` beyond which the count is balanced up to
`n/(k + 1)`. -/
theorem problem2_iff_forall_exists_forall :
    Rule30Prize.Problem2 ↔ ∀ k, ∃ N, ∀ n, balanced k N n = true := by
  have key : ∀ k N n, balanced k N n = true ↔
      (N ≤ n → (k + 1) * (2 * (Rule30Prize.blackCount n : ℤ) - n).natAbs ≤ n) := by
    intro k N n
    rw [mul_natAbs_le_iff]
    simp only [balanced, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.and_eq_true, decide_eq_true_eq]
    tauto
  constructor
  · intro h k
    obtain ⟨N, hN⟩ := h (k + 1) (Nat.succ_pos k)
    exact ⟨N, fun n => (key k N n).2 (hN n)⟩
  · intro h k hk
    obtain ⟨N, hN⟩ := h (k - 1)
    refine ⟨N, fun n hn => ?_⟩
    have := (key (k - 1) N n).1 (hN n) hn
    rwa [Nat.sub_add_cancel hk] at this

/-! ### Random and generic center columns are not computable -/

section NotComputable

open MeasureTheory Filter Topology RandomConfigurations Genericity

/-- **Countably many sequences are computable**: a computable `v` is the partial recursive function
`n ↦ encode (v n)`, which has a code. -/
theorem countable_computable : {v : ℕ → Bool | Computable v}.Countable := by
  let g : (ℕ → Bool) → (ℕ →. ℕ) := fun v n => Part.some (Encodable.encode (v n))
  refine Set.MapsTo.countable_of_injOn (f := g) (t := Set.range Nat.Partrec.Code.eval) ?_ ?_
    (Set.countable_range _)
  · intro v hv
    have h : Nat.Partrec (g v) := by
      have h' : Partrec (v : ℕ →. Bool) := hv
      unfold Partrec at h'
      refine (congrArg Nat.Partrec ?_).mpr h'
      funext n
      simp [g]
    exact Nat.Partrec.Code.exists_code.1 h
  · intro v _ w _ h
    funext n
    have := congrFun h n
    simp only [g, Part.some_inj] at this
    exact Encodable.encode_injective this

/-- **A random configuration has a non-computable center column**, almost surely, while that of
the single seed is primitive recursive (`primrec_center`). -/
theorem ae_not_computable_trace : ∀ᵐ x ∂(coins ℤ), ¬ Computable (trace x) := by
  have h : ∀ᵐ v ∂(coins ℕ), ¬ Computable v := by
    rw [ae_iff]
    simpa using countable_computable.measure_zero (coins ℕ)
  exact measurePreserving_trace.quasiMeasurePreserving.ae (p := fun v => ¬ Computable v) h

/-- **A generic configuration has a non-computable center column**: the configurations with a
computable center column form a meager set. -/
theorem residual_not_computable_trace :
    {x : ℤ → Bool | ¬ Computable (trace x)} ∈ residual (ℤ → Bool) := by
  have hmeagre : IsMeagre {v : ℕ → Bool | Computable v} := by
    rw [← Set.biUnion_of_singleton {v : ℕ → Bool | Computable v}]
    exact isMeagre_biUnion countable_computable fun v _ => (isNowhereDense_singleton v).isMeagre
  exact tendsto_residual_of_isOpenMap continuous_trace isOpenMap_trace hmeagre

end NotComputable

end Rule30Equivalents.Computability
