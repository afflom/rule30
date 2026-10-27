module

public import Rule30Equivalents.AlgebraicDegree
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
# Query complexity of rule 30's `t`-step map

A decision tree computes a Boolean function of a configuration by querying
cells one at a time, each query chosen from the answers so far; its depth is the largest number of
queries on one run. This is the query model of computational effort.

* `coef_eval_eq_zero`: the function computed by a decision tree of depth `d` has algebraic degree
  at most `d` over `𝔽₂`. The tree that queries `x_i` and continues with `l` or `r` computes
  `l ⊕ x_i (l ⊕ r)`, and multiplying by one variable raises the degree by at most one
  (`coef_and_var_eq_zero`).
* `le_depth_of_eval_eq`: **every decision tree that computes the center cell after `t ≥ 2` steps
  from the initial cells has depth at least `2t − 1`**, because that function has degree `2t − 1`
  (`AlgebraicDegree.coef_center_top`). Of the `2t + 1` cells in the light cone, at most two can
  be skipped on the worst run. Querying all of them suffices (`exists_depth_eq`), so the query
  complexity lies between `2t − 1` and `2t + 1`.

This is a linear lower bound for computing `Φ_t` from an arbitrary initial row. It says nothing
directly about Prize Problem 3, where the initial row is the single black cell and the only input
is `t`.
-/

@[expose] public section

namespace Rule30Equivalents.QueryComplexity

open Finset Ruliology.CellularAutomata Rule30Realization AlgebraicDegree

/-- A decision tree that queries the cells of a configuration indexed by `ι`: a leaf answers, and
`query i l r` reads the cell `i` and continues with `l` if it is white, `r` if it is black. -/
inductive DecisionTree (ι : Type*)
  | leaf (b : Bool)
  | query (i : ι) (l r : DecisionTree ι)

namespace DecisionTree

variable {ι : Type*}

/-- The answer of a decision tree on a configuration. -/
def eval : DecisionTree ι → (ι → Bool) → Bool
  | leaf b, _ => b
  | query i l r, x => if x i then r.eval x else l.eval x

/-- The largest number of queries on one run. -/
def depth : DecisionTree ι → ℕ
  | leaf _ => 0
  | query _ l r => max l.depth r.depth + 1

end DecisionTree

open DecisionTree

variable {ι : Type*} [DecidableEq ι]

/-- Setting a variable that `S` does not involve to `0` leaves the coefficient of `S` unchanged. -/
theorem coef_update_false {i : ι} {S : Finset ι} (hi : i ∉ S) (h : (ι → Bool) → Bool) :
    coef (fun x => h (Function.update x i false)) S = coef h S := by
  unfold coef
  refine sum_congr rfl fun U hU => ?_
  have hiU : i ∉ U := fun h => hi (mem_powerset.1 hU h)
  have h0 : Function.update (ind U) i false = ind U := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [ind, hiU]
    · simp [ind, hj]
  simp only [h0]

/-- **Multiplying by a variable raises the degree by at most one**: if `h` has no monomial with
more than `k` variables, then `x_i h` has none with more than `k + 1`. -/
theorem coef_and_var_eq_zero {i : ι} {h : (ι → Bool) → Bool} {k : ℕ}
    (hh : ∀ S : Finset ι, k < S.card → coef h S = 0) {S : Finset ι} (hS : k + 1 < S.card) :
    coef (fun x => x i && h x) S = 0 := by
  by_cases hi : i ∈ S
  · rw [coef_of_mem hi]
    have hd : deriv i (fun x => x i && h x) =
        fun x => xor (deriv i h x) (h (Function.update x i false)) := by
      funext x
      simp only [deriv, Function.update_self, Bool.true_and, Bool.false_and, Bool.xor_false]
      cases h (Function.update x i true) <;> cases h (Function.update x i false) <;> rfl
    have hcard := card_erase_of_mem hi
    rw [hd, coef_xor, ← coef_insert (notMem_erase i S), insert_erase hi, hh S (by omega),
      zero_add, coef_update_false (notMem_erase i S)]
    exact hh _ (by omega)
  · -- no `ind U` with `U ⊆ S` has the cell `i` black
    unfold coef
    refine sum_eq_zero fun U hU => ?_
    have : ind U i = false := by
      simp only [ind, decide_eq_false_iff_not]
      exact fun h => hi (mem_powerset.1 hU h)
    simp [this]

/-- **A decision tree of depth `d` computes a function of degree at most `d`** over `𝔽₂`. -/
theorem coef_eval_eq_zero :
    ∀ (T : DecisionTree ι) {S : Finset ι}, T.depth < S.card → coef T.eval S = 0
  | leaf b, S, hS => by
    have hne : S.Nonempty := card_pos.1 (by simp only [depth] at hS; omega)
    exact coef_const hne b
  | query i l r, S, hS => by
    simp only [depth] at hS
    have he : (query i l r).eval =
        fun x => xor (l.eval x) (x i && xor (l.eval x) (r.eval x)) := by
      funext x
      simp only [eval]
      cases x i <;> cases l.eval x <;> cases r.eval x <;> rfl
    rw [he, coef_xor, coef_eval_eq_zero l (by omega), zero_add]
    refine coef_and_var_eq_zero (k := max l.depth r.depth) (fun S' hS' => ?_) (by omega)
    rw [coef_xor, coef_eval_eq_zero l (by omega), coef_eval_eq_zero r (by omega), add_zero]

/-- **The query complexity of rule 30's `t`-step map**: every decision tree that computes the
center cell after `t ≥ 2` steps from the initial cells has depth at least `2t − 1`. -/
theorem le_depth_of_eval_eq {t : ℕ} (ht : 2 ≤ t) (T : DecisionTree ℤ)
    (hT : ∀ x, T.eval x = evol x t 0) : 2 * t - 1 ≤ T.depth := by
  by_contra hlt
  have h := coef_center_top ht
  have he : (fun x => evol x t 0) = T.eval := funext fun x => (hT x).symm
  rw [he, coef_eval_eq_zero T (by rw [Int.card_Icc]; omega)] at h
  exact absurd h (by decide)

/-- The tree that queries the cells of the list `l` in order and then answers `f` on the
configuration read so far (white elsewhere). -/
def full (f : (ℤ → Bool) → Bool) : List ℤ → (ℤ → Bool) → DecisionTree ℤ
  | [], ρ => leaf (f ρ)
  | i :: l, ρ =>
    query i (full f l (Function.update ρ i false)) (full f l (Function.update ρ i true))

theorem depth_full (f : (ℤ → Bool) → Bool) : ∀ (l : List ℤ) (ρ : ℤ → Bool),
    (full f l ρ).depth = l.length
  | [], _ => rfl
  | i :: l, ρ => by
    simp only [full, depth, depth_full f l, max_self, List.length_cons]

/-- The full tree answers `f` on the configuration that agrees with `x` on the queried cells and
with `ρ` elsewhere. -/
theorem eval_full (f : (ℤ → Bool) → Bool) : ∀ (l : List ℤ) (ρ x : ℤ → Bool),
    (full f l ρ).eval x = f fun j => if j ∈ l then x j else ρ j
  | [], ρ, x => by simp [full, eval]
  | i :: l, ρ, x => by
    simp only [full, eval]
    have key : ∀ b, x i = b → (fun j => if j ∈ l then x j else Function.update ρ i b j) =
        fun j => if j ∈ i :: l then x j else ρ j := by
      intro b hb
      funext j
      by_cases hj : j ∈ l
      · simp [hj]
      · by_cases hji : j = i
        · subst hji
          simp [hj, hb]
        · simp [hj, hji]
    cases hx : x i
    · rw [ite_eq_right (by simp), eval_full f l, key false hx]
    · rw [ite_eq_left rfl, eval_full f l, key true hx]

/-- **The matching upper bound**: querying the `2t + 1` cells of the light cone computes the
center cell after `t` steps, so its query complexity lies between `2t − 1` and `2t + 1`. -/
theorem exists_depth_eq (t : ℕ) : ∃ T : DecisionTree ℤ,
    (∀ x, T.eval x = evol x t 0) ∧ T.depth = 2 * t + 1 := by
  classical
  let l : List ℤ := (Finset.Icc (-(t : ℤ)) t).toList
  refine ⟨full (fun x => evol x t 0) l fun _ => false, fun x => ?_, ?_⟩
  · rw [eval_full]
    refine evol_congr t 0 fun j hj1 hj2 => ?_
    have : j ∈ l := by
      simp only [l, Finset.mem_toList, Finset.mem_Icc]
      omega
    simp [this]
  · rw [depth_full, Finset.length_toList, Int.card_Icc]
    omega

end Rule30Equivalents.QueryComplexity
