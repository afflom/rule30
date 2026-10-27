module

public import Ruliology.CellularAutomata.Rule30Jen
public import Rule30Equivalents.Basic
public import Mathlib.ModelTheory.Arithmetic.Presburger.Definability
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Multiplication in Presburger arithmetic with the black times

A definable form of "Th(ℕ, +, S) is undecidable". Let
`S = {t : c(t) = 1}`. **If multiplication is first-order definable in `(ℕ, 0, 1, +, S)`, with any
parameters, then Problem 1 holds** (`problem1_of_mul_definable`).

* `presburgerS`: the language `(0, 1, +)` of Presburger arithmetic with one unary relation symbol,
  interpreted in `ℕ` as a set `S` (`structS S`).
* `isSemilinearSet_of_definable`: if `S` is semilinear (eventually periodic), every set definable in
  `(ℕ, +, S)` is semilinear. This is Mathlib's induction for Presburger arithmetic
  (`presburger.definable_iff_isSemilinearSet`) with one more atomic case: a term is `k + u ⬝ v`, and
  `{v | k + u ⬝ v ∈ S}` is the preimage of the semilinear set `{x | k + x ∈ S}` under the additive
  map `v ↦ u ⬝ v`.
* The graph of multiplication is not semilinear (Mathlib's `presburger.mul_not_definable`).

Conversely, **if every finite word occurs in `c`, multiplication is definable in `(ℕ, +, S)`**,
without parameters (`mul_definable_of_center_disjunctive`). A window `{i | x + i ∈ S}` can hold any finite
set. `SqPred y z` says that some window contains `0`, `1` and `z`, that the gaps between its
consecutive elements up to `z` grow by `2`, and that the last gap is `2y - 1`; for a disjunctive
`S` this holds iff `z = y²` (`sqPred_iff`), and `ab = c` iff `(a + b)² = a² + b² + 2c`.
-/

@[expose] public section

namespace Rule30Equivalents.PresburgerExpansion

open Set FirstOrder Language Ruliology.CellularAutomata

/-- The relation symbols of `(ℕ, +, S)`: one unary relation. -/
inductive RelS : ℕ → Type
  | mem : RelS 1

/-- The language of Presburger arithmetic `(0, 1, +)` with one unary relation symbol. -/
def presburgerS : Language := ⟨presburgerFunc, RelS⟩

/-- `ℕ` as a structure for `(ℕ, +, S)`. -/
@[reducible] def structS (S : Set ℕ) : presburgerS.Structure ℕ where
  funMap {n} f v := Structure.funMap (L := presburger) (show presburgerFunc n from f) v
  RelMap {n} r v := match n, (show RelS n from r) with
    | _, .mem => v 0 ∈ S

variable {α : Type*} {S A : Set ℕ}

lemma term_realize_eq_add_dotProduct [Fintype α] (S : Set ℕ) (t : presburgerS[[A]].Term α) :
    letI := structS S
    ∃ (k : ℕ) (u : α → ℕ), ∀ (v : α → ℕ), t.realize v = k + u ⬝ᵥ v := by
  let := structS S
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        erw [withConstants_funMap_sumInl]
        simp
        rfl
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        erw [withConstants_funMap_sumInl]
        simp
        rfl
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        erw [withConstants_funMap_sumInl]
        show (ts 0).realize v + (ts 1).realize v = _
        rw [ih 0, ih 1, add_dotProduct]
        ring
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [zero_dotProduct, add_zero]
        rfl
      | succ => nomatch f

/-- The preimage of a semilinear set under `v ↦ k + u ⬝ v` is semilinear. -/
lemma isSemilinearSet_setOf_add_dotProduct_mem [Fintype α] (hS : IsSemilinearSet S) (k : ℕ)
    (u : α → ℕ) : IsSemilinearSet {v : α → ℕ | k + u ⬝ᵥ v ∈ S} := by
  have hS' : IsSemilinearSet {x : ℕ | k + x ∈ S} := by
    rw [Nat.isSemilinearSet_iff_ultimately_periodic] at hS ⊢
    obtain ⟨m, p, hp, h⟩ := hS
    exact ⟨m, p, hp, fun x hx => by rw [mem_ofPred, mem_ofPred, ← add_assoc]; exact h _ (by omega)⟩
  let f : (α → ℕ) →+ ℕ :=
    { toFun := fun v => u ⬝ᵥ v, map_zero' := dotProduct_zero u, map_add' := dotProduct_add u }
  exact hS'.preimage f

variable [Finite α]

lemma isSemilinearSet_boundedFormula_realize (hS : IsSemilinearSet S) {n}
    (φ : presburgerS[[A]].BoundedFormula α n) :
    letI := structS S
    IsSemilinearSet {v : α ⊕ Fin n → ℕ | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
  let := structS S
  have := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct S t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct S t₂ with ⟨k₂, u₂, ht₂⟩
    convert! Nat.isSemilinearSet_setOfPred_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂, Matrix.vecHead, Matrix.mulVec]
  | rel R ts =>
    cases R with
    | inl R =>
      cases R with
      | mem =>
        rcases term_realize_eq_add_dotProduct S (ts 0) with ⟨k, u, ht⟩
        convert! isSemilinearSet_setOf_add_dotProduct_mem hS k u using 1
        ext v
        show (ts 0).realize _ ∈ S ↔ _
        rw [ht, Sum.elim_comp_inl_inr]
        rfl
    | inr R => nomatch R
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert! (ih₂.compl.inter ih₁).compl using 1
    simp [ofPred_inter_eq_sep, imp_iff_not_or, compl_ofPred]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft ℕ ℕ e)] at ih
    convert! ih.compl.proj.compl using 1
    simp_rw [compl_ofPred, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_ofPred, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]

/-- **Definable in `(ℕ, +, S)` with `S` semilinear ⟹ semilinear.** -/
theorem isSemilinearSet_of_definable (hS : IsSemilinearSet S) {s : Set (α → ℕ)}
    (h : letI := structS S; A.Definable presburgerS s) : IsSemilinearSet s := by
  let := structS S
  obtain ⟨φ, rfl⟩ := h
  let e := Equiv.sumEmpty α (Fin 0)
  convert! (isSemilinearSet_boundedFormula_realize hS φ).image (LinearMap.funLeft ℕ ℕ e.symm)
  ext x
  simp only [mem_ofPred_eq, mem_image]
  rw [(e.arrowCongr (.refl ℕ)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

/-- An eventually periodic set of naturals is semilinear. -/
theorem isSemilinearSet_of_eventuallyPeriodic {b : ℕ → Bool} (hb : EventuallyPeriodic b) :
    IsSemilinearSet {t | b t = true} := by
  obtain ⟨T, P, hP, hper⟩ := hb
  rw [Nat.isSemilinearSet_iff_ultimately_periodic]
  exact ⟨T, P, hP, fun x hx => by rw [mem_ofPred, mem_ofPred, hper x hx]⟩

/-- **Multiplication is not definable from an eventually periodic set.** -/
theorem mul_not_definable_of_eventuallyPeriodic {b : ℕ → Bool} (hb : EventuallyPeriodic b) :
    letI := structS {t | b t = true}
    ¬ A.Definable presburgerS {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := fun h =>
  presburger.mul_not_definable (A := ∅) (presburger.definable_iff_isSemilinearSet.2
    (isSemilinearSet_of_definable (isSemilinearSet_of_eventuallyPeriodic hb) h))

/-- **Multiplication definable in `(ℕ, +, S)` ⟹ Problem 1**, for `S` the black times of the center
column, with any parameters `A`. -/
theorem problem1_of_mul_definable
    (h : letI := structS {t | c t = true}
      A.Definable presburgerS {v : Fin 3 → ℕ | v 0 = v 1 * v 2}) :
    Rule30Prize.Problem1 := fun hep => mul_not_definable_of_eventuallyPeriodic hep h

/-! ### Definable sets and functions of `(ℕ, 0, 1, +, S)` -/

/-- Definable in `(ℕ, 0, 1, +, S)` without parameters. -/
abbrev SDef (S : Set ℕ) {β : Type} (s : Set (β → ℕ)) : Prop :=
  letI := structS S; (∅ : Set ℕ).Definable presburgerS s

/-- A function definable in `(ℕ, 0, 1, +, S)` without parameters. -/
abbrev SFun (S : Set ℕ) {β : Type} (f : (β → ℕ) → ℕ) : Prop :=
  letI := structS S; (∅ : Set ℕ).DefinableFun presburgerS f

section Layer

variable {S : Set ℕ} {β γ : Type}

theorem sfun_var (i : β) : SFun S fun v : β → ℕ => v i := by
  let := structS S
  exact presburgerS.definableFun_var i

theorem sfun_add {f g : (β → ℕ) → ℕ} (hf : SFun S f) (hg : SFun S g) :
    SFun S fun v => f v + g v := by
  let := structS S
  have hmap : (∅ : Set ℕ).DefinableMap presburgerS fun v => ![f v, g v] := by
    simp [DefinableMap, Fin.forall_fin_two, hf, hg]
  exact DefinableFun.comp hmap
    (DefinableFun.fun_symbol (L := presburgerS) (M := ℕ)
      (presburgerFunc.add : presburgerS.Functions 2))

theorem sfun_const : ∀ n : ℕ, SFun S fun _ : β → ℕ => n
  | 0 => by
    let := structS S
    have hmap : (∅ : Set ℕ).DefinableMap presburgerS fun _ : β → ℕ => (![] : Fin 0 → ℕ) :=
      fun i => i.elim0
    exact DefinableFun.comp hmap
      (DefinableFun.fun_symbol (L := presburgerS) (M := ℕ)
        (presburgerFunc.zero : presburgerS.Functions 0))
  | n + 1 => by
    let := structS S
    have hmap : (∅ : Set ℕ).DefinableMap presburgerS fun _ : β → ℕ => (![] : Fin 0 → ℕ) :=
      fun i => i.elim0
    exact sfun_add (sfun_const n) (DefinableFun.comp hmap
      (DefinableFun.fun_symbol (L := presburgerS) (M := ℕ)
        (presburgerFunc.one : presburgerS.Functions 0)))

theorem sdef_eq {f g : (β → ℕ) → ℕ} (hf : SFun S f) (hg : SFun S g) :
    SDef S {v | f v = g v} := by
  let := structS S
  exact hf.ofPred_eq hg

theorem sdef_le [Finite β] {f g : (β → ℕ) → ℕ} (hf : SFun S f) (hg : SFun S g) :
    SDef S {v | f v ≤ g v} := by
  let := structS S
  have hf' : SFun S fun w : β ⊕ Unit → ℕ => f (w ∘ Sum.inl) :=
    DefinableFun.comp (fun i => sfun_var (Sum.inl i)) hf
  have hg' : SFun S fun w : β ⊕ Unit → ℕ => g (w ∘ Sum.inl) :=
    DefinableFun.comp (fun i => sfun_var (Sum.inl i)) hg
  have h : SDef S {w : β ⊕ Unit → ℕ | f (w ∘ Sum.inl) + w (Sum.inr ()) = g (w ∘ Sum.inl)} :=
    sdef_eq (sfun_add hf' (sfun_var _)) hg'
  convert h.exists_of_finite using 1
  ext v
  simp only [Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
  constructor
  · intro hle
    exact ⟨fun _ => g v - f v, Nat.add_sub_of_le hle⟩
  · rintro ⟨u, hu⟩
    omega

theorem sdef_lt [Finite β] {f g : (β → ℕ) → ℕ} (hf : SFun S f) (hg : SFun S g) :
    SDef S {v | f v < g v} := by
  exact sdef_le (sfun_add hf (sfun_const 1)) hg

theorem sdef_mem_var (i : β) : SDef S {v : β → ℕ | v i ∈ S} := by
  let := structS S
  refine ⟨Relations.formula₁ (Sum.inl RelS.mem) (Term.var i), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rfl

theorem sdef_mem {f : (β → ℕ) → ℕ} (hf : SFun S f) : SDef S {v | f v ∈ S} := by
  let := structS S
  have hmap : (∅ : Set ℕ).DefinableMap presburgerS fun v => ![f v] := by
    simp [DefinableMap, hf]
  exact (sdef_mem_var (0 : Fin 1)).preimage_map hmap

end Layer

/-! ### Squaring from a disjunctive `S` -/

section Squares

variable {S : Set ℕ}

/-- `p < q` are consecutive elements of the window `{i | x + i ∈ S}`. -/
def Consec (S : Set ℕ) (x p q : ℕ) : Prop :=
  x + p ∈ S ∧ x + q ∈ S ∧ p < q ∧ ∀ r, p < r → r < q → x + r ∉ S

/-- The window at `x` encodes the squares `0, 1, 4, …, z` with `z = y²` (for `y ≥ 1`): it contains
`0`, `1` and `z`, the gaps between consecutive elements up to `z` grow by `2`, and the last gap is
`2y - 1`. -/
def SqWin (S : Set ℕ) (x y z : ℕ) : Prop :=
  x ∈ S ∧ x + 1 ∈ S ∧ x + z ∈ S ∧
    (∀ p q r, r ≤ z → Consec S x p q → Consec S x q r → r + p = q + q + 2) ∧
    ∃ p, Consec S x p z ∧ p + y + y = z + 1

/-- The formula that defines squaring from a disjunctive `S`. -/
def SqPred (S : Set ℕ) (y z : ℕ) : Prop := (y = 0 ∧ z = 0) ∨ (1 ≤ y ∧ ∃ x, SqWin S x y z)

theorem sdef_consec : SDef S {v : Fin 3 → ℕ | Consec S (v 0) (v 1) (v 2)} := by
  let := structS S
  have hall : SDef S {v : Fin 3 → ℕ | ∀ r, v 1 < r → r < v 2 → v 0 + r ∉ S} := by
    have hA : SDef S {w : Fin 3 ⊕ Unit → ℕ | w (Sum.inl 1) < w (Sum.inr ())} :=
      sdef_lt (sfun_var _) (sfun_var _)
    have hB : SDef S {w : Fin 3 ⊕ Unit → ℕ | w (Sum.inr ()) < w (Sum.inl 2)} :=
      sdef_lt (sfun_var _) (sfun_var _)
    have hC : SDef S {w : Fin 3 ⊕ Unit → ℕ | w (Sum.inl 0) + w (Sum.inr ()) ∈ S} :=
      sdef_mem (sfun_add (sfun_var _) (sfun_var _))
    convert (hA.compl.union (hB.compl.union hC.compl)).forall_of_finite using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro h u
      by_contra hc
      push Not at hc
      exact h (u ()) hc.1 hc.2.1 hc.2.2
    · intro h r h1 h2 h3
      rcases h fun _ => r with h' | h' | h'
      · exact h' h1
      · exact h' h2
      · exact h' h3
  have h0 : SDef S {v : Fin 3 → ℕ | v 0 + v 1 ∈ S} := sdef_mem (sfun_add (sfun_var _) (sfun_var _))
  have h1 : SDef S {v : Fin 3 → ℕ | v 0 + v 2 ∈ S} := sdef_mem (sfun_add (sfun_var _) (sfun_var _))
  have h2 : SDef S {v : Fin 3 → ℕ | v 1 < v 2} := sdef_lt (sfun_var _) (sfun_var _)
  exact h0.inter (h1.inter (h2.inter hall))

/-- `Consec` at three definable coordinates. -/
theorem sdef_consec_comp {β : Type} [Finite β] (i j k : β) :
    SDef S {w : β → ℕ | Consec S (w i) (w j) (w k)} := by
  let := structS S
  exact sdef_consec.preimage_comp ![i, j, k]

theorem sdef_sqWin : SDef S {v : Fin 3 → ℕ | SqWin S (v 0) (v 1) (v 2)} := by
  let := structS S
  have hgap : SDef S {v : Fin 3 → ℕ | ∀ p q r, r ≤ v 2 → Consec S (v 0) p q →
      Consec S (v 0) q r → r + p = q + q + 2} := by
    have hA : SDef S {w : Fin 3 ⊕ Fin 3 → ℕ | w (Sum.inr 2) ≤ w (Sum.inl 2)} :=
      sdef_le (sfun_var _) (sfun_var _)
    have hB := sdef_consec_comp (S := S) (Sum.inl 0 : Fin 3 ⊕ Fin 3) (Sum.inr 0) (Sum.inr 1)
    have hC := sdef_consec_comp (S := S) (Sum.inl 0 : Fin 3 ⊕ Fin 3) (Sum.inr 1) (Sum.inr 2)
    have hD : SDef S {w : Fin 3 ⊕ Fin 3 → ℕ |
        w (Sum.inr 2) + w (Sum.inr 0) = w (Sum.inr 1) + w (Sum.inr 1) + 2} :=
      sdef_eq (sfun_add (sfun_var _) (sfun_var _))
        (sfun_add (sfun_add (sfun_var _) (sfun_var _)) (sfun_const 2))
    convert (hA.compl.union (hB.compl.union (hC.compl.union hD))).forall_of_finite using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro h u
      by_contra hc
      push Not at hc
      exact hc.2.2.2 (h (u 0) (u 1) (u 2) hc.1 hc.2.1 hc.2.2.1)
    · intro h p q r h1 h2 h3
      rcases h ![p, q, r] with h' | h' | h' | h'
      · exact absurd h1 h'
      · exact absurd h2 h'
      · exact absurd h3 h'
      · simpa using h'
  have hlast : SDef S {v : Fin 3 → ℕ | ∃ p, Consec S (v 0) p (v 2) ∧ p + v 1 + v 1 = v 2 + 1} := by
    have hB := sdef_consec_comp (S := S) (Sum.inl 0 : Fin 3 ⊕ Unit) (Sum.inr ()) (Sum.inl 2)
    have hE : SDef S {w : Fin 3 ⊕ Unit → ℕ |
        w (Sum.inr ()) + w (Sum.inl 1) + w (Sum.inl 1) = w (Sum.inl 2) + 1} :=
      sdef_eq (sfun_add (sfun_add (sfun_var _) (sfun_var _)) (sfun_var _))
        (sfun_add (sfun_var _) (sfun_const 1))
    convert (hB.inter hE).exists_of_finite using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩, fun ⟨u, hu⟩ => ⟨u (), hu⟩⟩
  have h0 : SDef S {v : Fin 3 → ℕ | v 0 ∈ S} := sdef_mem_var 0
  have h1 : SDef S {v : Fin 3 → ℕ | v 0 + 1 ∈ S} := sdef_mem (sfun_add (sfun_var _) (sfun_const 1))
  have h2 : SDef S {v : Fin 3 → ℕ | v 0 + v 2 ∈ S} := sdef_mem (sfun_add (sfun_var _) (sfun_var _))
  exact h0.inter (h1.inter (h2.inter (hgap.inter hlast)))

theorem sdef_sqPred : SDef S {v : Fin 2 → ℕ | SqPred S (v 0) (v 1)} := by
  let := structS S
  have hz0 : SDef S {v : Fin 2 → ℕ | v 0 = 0} := sdef_eq (sfun_var _) (sfun_const 0)
  have hz1 : SDef S {v : Fin 2 → ℕ | v 1 = 0} := sdef_eq (sfun_var _) (sfun_const 0)
  have hpos : SDef S {v : Fin 2 → ℕ | 1 ≤ v 0} := sdef_le (sfun_const 1) (sfun_var _)
  have hwin : SDef S {w : Fin 2 ⊕ Unit → ℕ | SqWin S (w (Sum.inr ())) (w (Sum.inl 0))
      (w (Sum.inl 1))} := sdef_sqWin.preimage_comp ![Sum.inr (), Sum.inl 0, Sum.inl 1]
  have hex : SDef S {v : Fin 2 → ℕ | ∃ x, SqWin S x (v 0) (v 1)} := by
    convert hwin.exists_of_finite using 1
    ext v
    simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩, fun ⟨u, hu⟩ => ⟨u (), hu⟩⟩
  exact (hz0.inter hz1).union (hpos.inter hex)

/-- Above a window element `q < z` with `z` in the window there is a next element `r ≤ z`. -/
theorem exists_consec {x q z : ℕ} (hq : x + q ∈ S) (hz : x + z ∈ S) (hqz : q < z) :
    ∃ r, r ≤ z ∧ Consec S x q r := by
  classical
  have hex : ∃ r, q < r ∧ r ≤ z ∧ x + r ∈ S := ⟨z, hqz, le_rfl, hz⟩
  have hspec := Nat.find_spec hex
  refine ⟨Nat.find hex, hspec.2.1, hq, hspec.2.2, hspec.1, fun r h1 h2 hr => ?_⟩
  exact Nat.find_min hex h2 ⟨h1, by omega, hr⟩

/-- An element of the window has at most one predecessor. -/
theorem consec_unique_left {x p p' q : ℕ} (h : Consec S x p q) (h' : Consec S x p' q) :
    p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · exact absurd h'.1 (h.2.2.2 p' hlt h'.2.2.1)
  · exact heq
  · exact absurd h.1 (h'.2.2.2 p hgt h.2.2.1)

/-- **The window formula only defines squares.** -/
theorem eq_of_sqPred {y z : ℕ} (h : SqPred S y z) : z = y * y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hy, x, h0, h1, hz, hgap, p, hpz, hpy⟩
  · rfl
  have hz1 : 1 ≤ z := by have := hpz.2.2.1; omega
  -- consecutive squares are consecutive elements of the window
  have hA : ∀ k, (k + 1) * (k + 1) ≤ z → Consec S x (k * k) ((k + 1) * (k + 1)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simpa using h0, by simpa using h1, by norm_num, fun r hr1 hr2 => by omega⟩
    | succ k ih =>
      intro hk
      have hk' : (k + 1) * (k + 1) ≤ z := le_trans (by nlinarith) hk
      have hc := ih hk'
      obtain ⟨r, hrz, hr⟩ := exists_consec hc.2.1 hz (by nlinarith)
      have e := hgap _ _ _ hrz hc hr
      have hr' : r = (k + 1 + 1) * (k + 1 + 1) := by nlinarith
      rw [hr'] at hr
      exact hr
  -- the last square is `z`
  obtain ⟨n, hn⟩ : ∃ n, Nat.sqrt z = n + 1 := ⟨Nat.sqrt z - 1, by
    have := Nat.sqrt_pos.2 (show 0 < z by omega); omega⟩
  have hmz : (n + 1) * (n + 1) ≤ z := hn ▸ Nat.sqrt_le z
  have hzm : z < (n + 1 + 1) * (n + 1 + 1) := hn ▸ Nat.lt_succ_sqrt z
  have hcm := hA n hmz
  have hzeq : z = (n + 1) * (n + 1) := by
    by_contra hne
    have hlt : (n + 1) * (n + 1) < z := lt_of_le_of_ne hmz (Ne.symm hne)
    obtain ⟨r, hrz, hr⟩ := exists_consec hcm.2.1 hz hlt
    have e := hgap _ _ _ hrz hcm hr
    nlinarith
  -- its predecessor is `n²`, and the last gap gives `y = n + 1`
  rw [hzeq] at hpz hpy
  have hp : p = n * n := consec_unique_left hpz hcm
  rw [hp] at hpy
  rw [hzeq]
  have : y = n + 1 := by nlinarith
  rw [this]

variable (S) in
/-- `S` is disjunctive: every finite pattern occurs in its characteristic sequence. -/
def Disjunctive : Prop := ∀ n (w : Fin n → Bool), ∃ x, ∀ j : Fin n, x + (j : ℕ) ∈ S ↔ w j = true

/-- **A disjunctive `S` has a window for every square.** -/
theorem sqPred_of_eq (hS : Disjunctive S) (y : ℕ) : SqPred S y (y * y) := by
  classical
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · exact Or.inl ⟨rfl, rfl⟩
  refine Or.inr ⟨hy, ?_⟩
  obtain ⟨x, hx⟩ := hS (y * y + 1) fun j => decide (∃ k ≤ y, (j : ℕ) = k * k)
  have hmem : ∀ i ≤ y * y, x + i ∈ S ↔ ∃ k ≤ y, i = k * k := fun i hi => by
    have := hx ⟨i, by omega⟩
    simpa using this
  -- consecutive elements of the window below `y²` are consecutive squares
  have hcons : ∀ p q, q ≤ y * y → Consec S x p q → ∃ k, p = k * k ∧ q = (k + 1) * (k + 1) := by
    intro p q hq hc
    obtain ⟨a, ha, rfl⟩ := (hmem p (by have := hc.2.2.1; omega)).1 hc.1
    obtain ⟨b, hb, rfl⟩ := (hmem _ hq).1 hc.2.1
    have hab : a < b := Nat.mul_self_lt_mul_self_iff.1 hc.2.2.1
    refine ⟨a, rfl, ?_⟩
    by_contra hne
    have hab' : a + 1 < b := by
      rcases Nat.lt_or_ge (a + 1) b with h | h
      · exact h
      · exact absurd (by rw [show b = a + 1 by omega]) hne
    exact hc.2.2.2 ((a + 1) * (a + 1)) (by nlinarith) (Nat.mul_self_lt_mul_self hab')
      ((hmem _ (by nlinarith)).2 ⟨a + 1, by omega, rfl⟩)
  obtain ⟨n, rfl⟩ : ∃ n, y = n + 1 := ⟨y - 1, by omega⟩
  refine ⟨x, ?_, ?_, ?_, ?_, n * n, ?_, by ring⟩
  · simpa using (hmem 0 (Nat.zero_le _)).2 ⟨0, Nat.zero_le _, rfl⟩
  · exact (hmem 1 (by nlinarith)).2 ⟨1, by omega, rfl⟩
  · exact (hmem _ le_rfl).2 ⟨n + 1, le_rfl, rfl⟩
  · intro p q r hr hpq hqr
    obtain ⟨k, rfl, rfl⟩ := hcons p q (le_trans hqr.2.2.1.le hr) hpq
    obtain ⟨k', hk', rfl⟩ := hcons _ r hr hqr
    have : k' = k + 1 := Nat.mul_self_inj.1 hk'.symm
    subst this
    ring
  · refine ⟨(hmem _ (by nlinarith)).2 ⟨n, by omega, rfl⟩, (hmem _ le_rfl).2 ⟨n + 1, le_rfl, rfl⟩,
      by nlinarith, fun r hr1 hr2 hr => ?_⟩
    obtain ⟨k, hk, rfl⟩ := (hmem r hr2.le).1 hr
    have h1 : n < k := Nat.mul_self_lt_mul_self_iff.1 hr1
    have h2 : k < n + 1 := Nat.mul_self_lt_mul_self_iff.1 hr2
    omega

/-- **Squaring is definable from a disjunctive `S`.** -/
theorem sqPred_iff (hS : Disjunctive S) (y z : ℕ) : SqPred S y z ↔ z = y * y :=
  ⟨eq_of_sqPred, fun h => h ▸ sqPred_of_eq hS y⟩

/-- `SqPred` at two definable functions. -/
theorem sdef_sqPred_comp {β : Type} {f g : (β → ℕ) → ℕ} (hf : SFun S f) (hg : SFun S g) :
    SDef S {v | SqPred S (f v) (g v)} := by
  let := structS S
  have hmap : (∅ : Set ℕ).DefinableMap presburgerS fun v => ![f v, g v] := by
    simp [DefinableMap, Fin.forall_fin_two, hf, hg]
  exact sdef_sqPred.preimage_map hmap

/-- **A disjunctive `S` defines multiplication** in `(ℕ, 0, 1, +, S)`: `a b = c` iff
`(a + b)² = a² + b² + 2c`, and `SqPred` defines squaring. -/
theorem mul_definable_of_disjunctive (hS : Disjunctive S) :
    SDef S {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := by
  let := structS S
  have h1 : SDef S {w : Fin 3 ⊕ Fin 3 → ℕ |
      SqPred S (w (Sum.inl 1) + w (Sum.inl 2)) (w (Sum.inr 0))} :=
    sdef_sqPred_comp (sfun_add (sfun_var _) (sfun_var _)) (sfun_var _)
  have h2 : SDef S {w : Fin 3 ⊕ Fin 3 → ℕ | SqPred S (w (Sum.inl 1)) (w (Sum.inr 1))} :=
    sdef_sqPred_comp (sfun_var _) (sfun_var _)
  have h3 : SDef S {w : Fin 3 ⊕ Fin 3 → ℕ | SqPred S (w (Sum.inl 2)) (w (Sum.inr 2))} :=
    sdef_sqPred_comp (sfun_var _) (sfun_var _)
  have h4 : SDef S {w : Fin 3 ⊕ Fin 3 → ℕ |
      w (Sum.inr 0) = w (Sum.inr 1) + w (Sum.inr 2) + w (Sum.inl 0) + w (Sum.inl 0)} :=
    sdef_eq (sfun_var _)
      (sfun_add (sfun_add (sfun_add (sfun_var _) (sfun_var _)) (sfun_var _)) (sfun_var _))
  convert (h1.inter (h2.inter (h3.inter h4))).exists_of_finite using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr, sqPred_iff hS]
  constructor
  · intro h
    refine ⟨![(v 1 + v 2) * (v 1 + v 2), v 1 * v 1, v 2 * v 2], rfl, rfl, rfl, ?_⟩
    show (v 1 + v 2) * (v 1 + v 2) = v 1 * v 1 + v 2 * v 2 + v 0 + v 0
    rw [h]
    ring
  · rintro ⟨u, e1, e2, e3, e4⟩
    rw [e1, e2, e3] at e4
    nlinarith

end Squares

/-- **If every finite word occurs in the center column, multiplication is definable in
`(ℕ, 0, 1, +, S)`**, `S` the black times. With `problem1_of_mul_definable` this is the chain
"disjunctive ⟹ `(ℕ, +, S)` defines multiplication ⟹ Problem 1". -/
theorem mul_definable_of_center_disjunctive
    (h : ∀ n (w : Fin n → Bool), ∃ i, ∀ j : Fin n, c (i + j) = w j) :
    SDef {t | c t = true} {v : Fin 3 → ℕ | v 0 = v 1 * v 2} :=
  mul_definable_of_disjunctive fun n w => by
    obtain ⟨i, hi⟩ := h n w
    exact ⟨i, fun j => by rw [Set.mem_ofPred_eq, hi j]⟩

end Rule30Equivalents.PresburgerExpansion
