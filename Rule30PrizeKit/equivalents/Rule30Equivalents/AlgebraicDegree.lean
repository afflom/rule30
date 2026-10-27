module

public import Rule30Equivalents.Basic
public import Rule30Equivalents.WordsAutomata
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring

/-!
# The algebraic degree of rule 30's `t`-step map

Run rule 30 for `t` steps from an arbitrary configuration `x`. The center
cell is a Boolean function `Φ_t` of the `2t + 1` cells `x_{-t}, …, x_t`. Over `𝔽₂` it is a sum of
monomials `∏_{i ∈ S} x_i`, its algebraic normal form, and the coefficient of the monomial `S` is
the Möbius transform `coef Φ_t S = ∑_{U ⊆ S} Φ_t(1_U)`.

* `isGreatest_card_coef_center`: for `t ≥ 2`, `Φ_t` has degree exactly `2t − 1`.
  - `coef_evol_eq_zero` (upper bound): the cell at time `s` has no monomial with at least
    `max 3 (2s)` variables. Rule 30 is left-permutive, so the leftmost variable `x_{q-s}` of the
    cell `(s, q)` enters only linearly. The derivative along the next variable telescopes along
    the left diagonal (`coef_deriv_evol_eq_zero`), and each of its terms is again linear in its
    leftmost variable, so the full monomial on the remaining `2s` variables cancels.
  - `coef_center_top` (lower bound): the monomial `x_{2-t} ⋯ x_t` has coefficient `1`. The
    derivative along `x_t` is `1` exactly when the diagonal left of the right edge is white
    (`deriv_evol_right`), so the coefficient is the parity of the number of such configurations.
    Running rule 30 sideways (`side`) maps them bijectively to the words `w` of length `t − 1`
    with `side w (2t − 2) 0 = 0` (`card_white_diag`), and the parity of those is `1` by an
    induction on the length (`coef_side_top`).
* `eq_Icc_of_coef_ne_zero`: for `t ≥ 3` this is the only monomial of degree `2t − 1`.
* `coef_center_singleton`: the coefficient of `x_0` is the center column `c(t)`, so Problem 1
  concerns the linear part of `Φ_t`.
* `walsh_center_eq_zero`, `card_center_true`: `Φ_t` is balanced, and uncorrelated with every affine
  function that does not involve `x_{-t}`: its Walsh coefficient there is `0`, because `Φ_t` flips
  with `x_{-t}`.
* `card_trace`: the whole center trace is uniform: each word `w(0), …, w(n)` is the trace of
  exactly `2ⁿ` of the `2^(2n+1)` configurations on `[-n, n]` (cells `±(n+1)` do not affect the
  trace up to time `n`, and flipping `x_{-(n+1)}` flips the center at time `n + 1`).
* `card_window`: every window of every row is balanced (Hedlund's theorem for rule 30): each word
  on the cells `a, …, a + m - 1` of the `t`-th row comes from exactly `4^t` of the `2^(m + 2t)`
  configurations on `[a - t, a + m - 1 + t]`.

The degree does not decide Problem 1: there are rules of maximal degree whose single-seed center
columns are eventually periodic.
-/

@[expose] public section

namespace Rule30Equivalents.AlgebraicDegree

open Ruliology.CellularAutomata Rule30Jen Rule30Realization Finset

/-! ### Coefficients of the algebraic normal form -/

section Coef

variable {ι : Type*} [DecidableEq ι]

/-- The indicator of a finite set. -/
def ind (U : Finset ι) : ι → Bool := fun i => decide (i ∈ U)

/-- The coefficient of the monomial `∏_{i ∈ S} x_i` in the algebraic normal form of `f` over
`𝔽₂`: the Möbius transform `∑_{U ⊆ S} f(1_U)`. -/
def coef (f : (ι → Bool) → Bool) (S : Finset ι) : ZMod 2 :=
  ∑ U ∈ S.powerset, if f (ind U) then 1 else 0

/-- The derivative of `f` along the variable `i`. -/
def deriv (i : ι) (f : (ι → Bool) → Bool) (x : ι → Bool) : Bool :=
  xor (f (Function.update x i true)) (f (Function.update x i false))

/-- `f` does not depend on the variable `i`. -/
def Indep (i : ι) (f : (ι → Bool) → Bool) : Prop := ∀ x b, f (Function.update x i b) = f x

theorem ite_xor (a b : Bool) :
    (if xor a b then 1 else 0 : ZMod 2) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem coef_xor (f g : (ι → Bool) → Bool) (S : Finset ι) :
    coef (fun x => xor (f x) (g x)) S = coef f S + coef g S := by
  simp only [coef, ite_xor, sum_add_distrib]

/-- The monomials containing `x_i` are `x_i` times those of the derivative along `x_i`. -/
theorem coef_insert {i : ι} {S : Finset ι} (hi : i ∉ S) (f : (ι → Bool) → Bool) :
    coef f (insert i S) = coef (deriv i f) S := by
  rw [coef, sum_powerset_insert hi, coef, ← sum_add_distrib]
  refine sum_congr rfl fun U hU => ?_
  have hiU : i ∉ U := fun h => hi (mem_powerset.1 hU h)
  have h1 : ind (insert i U) = Function.update (ind U) i true := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [ind]
    · simp [ind, hj]
  have h0 : Function.update (ind U) i false = ind U := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [ind, hiU]
    · simp [ind, hj]
  rw [deriv, ite_xor, h1, h0, add_comm]

theorem coef_of_mem {i : ι} {S : Finset ι} (hi : i ∈ S) (f : (ι → Bool) → Bool) :
    coef f S = coef (deriv i f) (S.erase i) := by
  rw [← coef_insert (notMem_erase i S), insert_erase hi]

theorem coef_false (S : Finset ι) : coef (fun _ => false) S = 0 := by
  simp [coef]

theorem coef_eq_zero_of_indep {i : ι} {S : Finset ι} {f : (ι → Bool) → Bool} (h : Indep i f)
    (hi : i ∈ S) : coef f S = 0 := by
  have : deriv i f = fun _ => false := funext fun x => by
    unfold deriv
    rw [h x true, h x false, Bool.xor_self]
  rw [coef_of_mem hi, this, coef_false]

theorem coef_const {S : Finset ι} (hS : S.Nonempty) (b : Bool) : coef (fun _ => b) S = 0 :=
  let ⟨_, hi⟩ := hS
  coef_eq_zero_of_indep (fun _ _ => rfl) hi

theorem coef_not {S : Finset ι} (hS : S.Nonempty) (f : (ι → Bool) → Bool) :
    coef (fun x => !f x) S = coef f S := by
  have : (fun x => !f x) = fun x => xor true (f x) := funext fun x => by cases f x <;> rfl
  rw [this, coef_xor, coef_const hS, zero_add]

/-- If `f` flips with `x_i` and `g` does not depend on `x_i`, the monomials of `f ∧ g` that
contain `x_i` are `x_i` times those of `g`. -/
theorem coef_and {i : ι} {S : Finset ι} (hi : i ∈ S) {f g : (ι → Bool) → Bool}
    (hf : ∀ x, f (Function.update x i true) = !f (Function.update x i false)) (hg : Indep i g) :
    coef (fun x => f x && g x) S = coef g (S.erase i) := by
  rw [coef_of_mem hi]
  congr 1
  funext x
  show xor (f _ && g _) (f _ && g _) = g x
  rw [hf x, hg x true, hg x false]
  cases f (Function.update x i false) <;> cases g x <;> rfl

end Coef

/-! ### Rule 30 from an arbitrary configuration -/

theorem evol_succ (x : ℤ → Bool) (t : ℕ) (p : ℤ) :
    evol x (t + 1) p = xor (evol x t (p - 1)) (evol x t p || evol x t (p + 1)) := rfl

/-- The light cone: the cell `(t, p)` depends only on the cells `p - t, …, p + t`. -/
theorem evol_congr {x y : ℤ → Bool} (t : ℕ) (p : ℤ)
    (h : ∀ j, p - t ≤ j → j ≤ p + t → x j = y j) : evol x t p = evol y t p :=
  Rule30ZeroBoundaryBarriers.evol_local (x := y) (x' := x) h t p (by omega) (by omega)

theorem evol_update_of_far {t : ℕ} {p i : ℤ} (hi : i < p - t ∨ p + t < i) (x : ℤ → Bool)
    (b : Bool) : evol (Function.update x i b) t p = evol x t p :=
  evol_congr t p fun j h1 h2 => by
    rw [Function.update_apply, ite_eq_right (show j ≠ i by omega)]

/-- Rule 30 is left-permutive: the cell `(t, p)` flips with `x_{p-t}`. -/
theorem evol_update_left (x : ℤ → Bool) :
    ∀ (t : ℕ) (p : ℤ),
      evol (Function.update x (p - t) true) t p = !evol (Function.update x (p - t) false) t p
  | 0, p => by simp only [Nat.cast_zero, sub_zero]; simp [evol]
  | t + 1, p => by
    have e : p - ((t + 1 : ℕ) : ℤ) = p - 1 - t := by push_cast; omega
    rw [evol_succ, evol_succ, e, evol_update_left x t (p - 1),
      evol_update_of_far (t := t) (p := p) (i := p - 1 - t) (Or.inl (by omega)) x true,
      evol_update_of_far (t := t) (p := p) (i := p - 1 - t) (Or.inl (by omega)) x false,
      evol_update_of_far (t := t) (p := p + 1) (i := p - 1 - t) (Or.inl (by omega)) x true,
      evol_update_of_far (t := t) (p := p + 1) (i := p - 1 - t) (Or.inl (by omega)) x false]
    cases evol (Function.update x (p - 1 - t) false) t (p - 1) <;>
      cases (evol x t p || evol x t (p + 1)) <;> rfl

/-- The monomials of the cell `(s, p)` that contain its leftmost variable: only `x_{p-s}`. -/
theorem coef_evol_left {s : ℕ} {p : ℤ} {S : Finset ℤ} (hl : p - s ∈ S) (h2 : 2 ≤ S.card) :
    coef (fun x => evol x s p) S = 0 := by
  rw [coef_of_mem hl]
  have : deriv (p - s) (fun x => evol x s p) = fun _ => true := funext fun x => by
    simp only [deriv, evol_update_left]
    cases evol (Function.update x (p - s) false) s p <;> rfl
  rw [this, coef_const]
  rw [← card_pos, card_erase_of_mem hl]
  omega

/-! ### The upper bound -/

/-- One step down the left diagonal of the cone of `(t, q)`: the derivative along `x_{q-t+1}`
gains the negated cell two to the right. -/
theorem deriv_evol_diag_succ (q : ℤ) (t s : ℕ) (x : ℤ → Bool) :
    deriv (q - t + 1) (fun x => evol x (s + 1) (q - t + ((s + 1 : ℕ) : ℤ))) x =
      xor (deriv (q - t + 1) (fun x => evol x s (q - t + s)) x) (!evol x s (q - t + s + 2)) := by
  simp only [deriv]
  have e1 : q - t + ((s + 1 : ℕ) : ℤ) - 1 = q - t + s := by push_cast; omega
  have e3 : q - t + ((s + 1 : ℕ) : ℤ) + 1 = q - t + s + 2 := by push_cast; omega
  have e2 : q - t + ((s + 1 : ℕ) : ℤ) = q - t + s + 1 := by push_cast; omega
  rw [evol_succ, evol_succ, e1, e3, e2]
  have hB := evol_update_left x s (q - t + s + 1)
  rw [show q - t + s + 1 - (s : ℤ) = q - t + 1 by omega] at hB
  rw [hB, evol_update_of_far (t := s) (p := q - t + s + 2) (i := q - t + 1) (Or.inl (by omega)),
    evol_update_of_far (t := s) (p := q - t + s + 2) (i := q - t + 1) (Or.inl (by omega))]
  generalize evol (Function.update x (q - t + 1) true) s (q - t + s) = a1
  generalize evol (Function.update x (q - t + 1) false) s (q - t + s) = a0
  generalize evol (Function.update x (q - t + 1) false) s (q - t + s + 1) = b
  generalize evol x s (q - t + s + 2) = c
  revert a1 a0 b c
  decide

/-- The derivative of the cell `(t, q)` along `x_{q-t+1}` has no monomial `S` if no cell
`(s, q - t + s + 2)`, `s < t`, has one. -/
theorem coef_deriv_evol_eq_zero (q : ℤ) (t : ℕ) {S : Finset ℤ} (hS : S.Nonempty)
    (h : ∀ s < t, coef (fun x => evol x s (q - t + s + 2)) S = 0) :
    coef (deriv (q - t + 1) fun x => evol x t q) S = 0 := by
  have key : ∀ s ≤ t, coef (deriv (q - t + 1) fun x => evol x s (q - t + s)) S = 0 := by
    intro s
    induction s with
    | zero =>
      intro _
      simp only [Nat.cast_zero, add_zero]
      simp [coef, deriv, evol]
    | succ s ih =>
      intro hs
      rw [show (deriv (q - t + 1) fun x => evol x (s + 1) (q - t + ((s + 1 : ℕ) : ℤ))) =
          fun x => xor (deriv (q - t + 1) (fun x => evol x s (q - t + s)) x)
            (!evol x s (q - t + s + 2)) from funext (deriv_evol_diag_succ q t s),
        coef_xor, ih (by omega), coef_not hS, h s (by omega), add_zero]
  have := key t le_rfl
  rwa [show q - (t : ℤ) + (t : ℤ) = q by omega] at this

/-- **Upper bound.** The cell at time `s` has no monomial with at least `max 3 (2s)` variables. -/
theorem coef_evol_eq_zero (s : ℕ) (q : ℤ) {S : Finset ℤ} (h3 : 3 ≤ S.card) (hs : 2 * s ≤ S.card) :
    coef (fun x => evol x s q) S = 0 := by
  -- a variable outside the light cone
  by_cases hout : ∃ i ∈ S, i < q - s ∨ q + s < i
  · obtain ⟨i, hi, hi'⟩ := hout
    exact coef_eq_zero_of_indep (fun x b => evol_update_of_far hi' x b) hi
  push Not at hout
  -- the leftmost variable enters linearly
  by_cases hl : q - s ∈ S
  · exact coef_evol_left hl (by omega)
  -- otherwise `S` is the whole cone except its leftmost cell
  have hsub : S ⊆ Icc (q - s + 1) (q + s) := fun i hi => by
    have h1 := hout i hi
    have h2 : i ≠ q - s := fun e => hl (e ▸ hi)
    simp only [mem_Icc]
    omega
  have hcard : (Icc (q - s + 1) (q + s)).card = 2 * s := by
    rw [Int.card_Icc]
    omega
  have hS : S = Icc (q - s + 1) (q + s) := eq_of_subset_of_card_le hsub (by omega)
  subst hS
  have hmem : q - s + 1 ∈ Icc (q - s + 1) (q + s) := by
    simp only [mem_Icc]
    omega
  have herase : (Icc (q - s + 1) (q + s)).erase (q - s + 1) = Icc (q - s + 2) (q + s) := by
    ext i
    simp only [mem_erase, mem_Icc]
    omega
  rw [coef_of_mem hmem, herase]
  refine coef_deriv_evol_eq_zero q s ⟨q + s, by simp only [mem_Icc]; omega⟩ fun s' _ => ?_
  -- every cell on the next diagonal is linear in `x_{q-s+2}`
  refine coef_evol_left ?_ ?_
  · rw [show q - s + s' + 2 - (s' : ℤ) = q - s + 2 by omega]
    simp only [mem_Icc]
    omega
  · rw [Int.card_Icc]
    omega

/-- **Uniqueness.** For `t ≥ 3` the only monomial of degree `2t − 1` of the cell `(t, q)` is
`x_{q-t+2} ⋯ x_{q+t}`. -/
theorem eq_Icc_of_coef_ne_zero {t : ℕ} (ht : 3 ≤ t) (q : ℤ) {S : Finset ℤ}
    (hS : S.card = 2 * t - 1) (h : coef (fun x => evol x t q) S ≠ 0) :
    S = Icc (q - t + 2) (q + t) := by
  have hout : ∀ i ∈ S, q - t ≤ i ∧ i ≤ q + t := by
    intro i hi
    by_contra hc
    exact h (coef_eq_zero_of_indep (fun x b => evol_update_of_far (by omega) x b) hi)
  have hl : q - t ∉ S := fun hl => h (coef_evol_left hl (by omega))
  have hl1 : q - t + 1 ∉ S := by
    intro hl1
    apply h
    have hcard : (S.erase (q - t + 1)).card = 2 * t - 2 := by
      rw [card_erase_of_mem hl1]
      omega
    rw [coef_of_mem hl1]
    refine coef_deriv_evol_eq_zero q t ?_ fun s hs => coef_evol_eq_zero s _ (by omega) (by omega)
    rw [← card_pos]
    omega
  have hsub : S ⊆ Icc (q - t + 2) (q + t) := fun i hi => by
    have h0 := hout i hi
    have h1 : i ≠ q - t := fun e => hl (e ▸ hi)
    have h2 : i ≠ q - t + 1 := fun e => hl1 (e ▸ hi)
    simp only [mem_Icc]
    omega
  exact eq_of_subset_of_card_le hsub (by rw [Int.card_Icc, hS]; omega)

/-! ### The lower bound -/

/-- The derivative along the right end `x_r` of the cone of `(s, r - s)` is `1` iff the diagonal
just left of the right edge of the cone is white. -/
theorem deriv_evol_right (r : ℤ) (x : ℤ → Bool) :
    ∀ s : ℕ, deriv r (fun x => evol x s (r - s)) x = true ↔
      ∀ s' < s, evol x s' (r - s' - 1) = false
  | 0 => by simp only [Nat.cast_zero, sub_zero]; simp [deriv, evol]
  | s + 1 => by
    have ih := deriv_evol_right r x s
    simp only [deriv] at ih ⊢
    have e1 : r - ((s + 1 : ℕ) : ℤ) - 1 = r - s - 2 := by push_cast; omega
    have e2 : r - ((s + 1 : ℕ) : ℤ) + 1 = r - s := by push_cast; omega
    have e3 : r - ((s + 1 : ℕ) : ℤ) = r - s - 1 := by push_cast; omega
    rw [evol_succ, evol_succ, e1, e2, e3,
      evol_update_of_far (t := s) (p := r - s - 2) (i := r) (Or.inr (by omega)),
      evol_update_of_far (t := s) (p := r - s - 2) (i := r) (Or.inr (by omega)),
      evol_update_of_far (t := s) (p := r - s - 1) (i := r) (Or.inr (by omega)),
      evol_update_of_far (t := s) (p := r - s - 1) (i := r) (Or.inr (by omega)),
      show ∀ a b c d : Bool, (xor (xor a (b || c)) (xor a (b || d)) = true) ↔
        (b = false ∧ xor c d = true) by decide, ih]
    constructor
    · rintro ⟨hB, hall⟩ s' hs'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with h | h
      · exact hall s' h
      · subst h
        exact hB
    · intro hall
      exact ⟨hall s (by omega), fun s' hs' => hall s' (by omega)⟩

/-- Rule 30 run sideways: `side w k s` is the cell on the `k`-th diagonal left of a white right
diagonal, at time `s`, when the first diagonal left of it is `w`. -/
def side (w : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | 1, s => w s
  | k + 2, s => xor (side w k (s + 1)) (side w (k + 1) s || side w k s)

theorem side_add_two (w : ℕ → Bool) (k s : ℕ) :
    side w (k + 2) s = xor (side w k (s + 1)) (side w (k + 1) s || side w k s) := rfl

/-- Reading the cone of `(m, 0)` by diagonals: if its right diagonal is white and the next one is
`w`, the `k`-th diagonal is `side w k`. -/
theorem evol_eq_side_of_diag {x : ℤ → Bool} {w : ℕ → Bool} {m : ℕ}
    (h0 : ∀ s ≤ m, evol x s ((m : ℤ) - s) = false)
    (h1 : ∀ s < m, evol x s ((m : ℤ) - 1 - s) = w s) :
    ∀ k s, 2 * s + k ≤ 2 * m → evol x s ((m : ℤ) - k - s) = side w k s
  | 0, s, h => by simpa [side] using h0 s (by omega)
  | 1, s, h => by simpa [side] using h1 s (by omega)
  | k + 2, s, h => by
    have ih0 := evol_eq_side_of_diag h0 h1 k (s + 1) (by omega)
    have ih1 := evol_eq_side_of_diag h0 h1 (k + 1) s (by omega)
    have ih2 := evol_eq_side_of_diag h0 h1 k s (by omega)
    have e := evol_succ x s ((m : ℤ) - ((k + 1 : ℕ) : ℤ) - s)
    rw [show (m : ℤ) - k - ((s + 1 : ℕ) : ℤ) = m - ((k + 1 : ℕ) : ℤ) - s by push_cast; omega]
      at ih0
    rw [show (m : ℤ) - ((k + 1 : ℕ) : ℤ) - s - 1 = m - ((k + 2 : ℕ) : ℤ) - s by push_cast; omega,
      show (m : ℤ) - ((k + 1 : ℕ) : ℤ) - s + 1 = m - k - s by push_cast; omega, ih0, ih1, ih2] at e
    rw [side_add_two, e, xor_xor_cancel]

/-- Conversely, a row that reads `side w k 0` on the cells `m - k` evolves by diagonals into
`side w`. -/
theorem evol_eq_side_of_row {x : ℤ → Bool} {w : ℕ → Bool} {m : ℕ}
    (h : ∀ k ≤ 2 * m, x ((m : ℤ) - k) = side w k 0) :
    ∀ s k, 2 * s + k ≤ 2 * m → evol x s ((m : ℤ) - k - s) = side w k s
  | 0, k, hk => by simpa [evol] using h k (by omega)
  | s + 1, k, hk => by
    have ih0 := evol_eq_side_of_row h s (k + 2) (by omega)
    have ih1 := evol_eq_side_of_row h s (k + 1) (by omega)
    have ih2 := evol_eq_side_of_row h s k (by omega)
    rw [evol_succ,
      show (m : ℤ) - k - ((s + 1 : ℕ) : ℤ) - 1 = m - ((k + 2 : ℕ) : ℤ) - s by push_cast; omega,
      show (m : ℤ) - k - ((s + 1 : ℕ) : ℤ) + 1 = m - k - s by push_cast; omega,
      show (m : ℤ) - k - ((s + 1 : ℕ) : ℤ) = m - ((k + 1 : ℕ) : ℤ) - s by push_cast; omega,
      ih0, ih1, ih2, side_add_two, xor_xor_cancel]

/-- The configurations on `x_{1-m}, …, x_m` whose cone of `(m, 0)` has a white right diagonal
correspond to the words `w` of length `m` with `side w (2m) 0 = 0`, by reading the next diagonal. -/
theorem card_white_diag (m : ℕ) :
    ((Icc (1 - m : ℤ) m).powerset.filter fun U =>
        ∀ s ≤ m, evol (ind U) s ((m : ℤ) - s) = false).card =
      ((range m).powerset.filter fun V => side (ind V) (2 * m) 0 = false).card := by
  -- reading the diagonal next to the right edge
  have hfwd : ∀ U ∈ (Icc (1 - m : ℤ) m).powerset.filter (fun U =>
      ∀ s ≤ m, evol (ind U) s ((m : ℤ) - s) = false), ∀ k s, 2 * s + k ≤ 2 * m →
        evol (ind U) s ((m : ℤ) - k - s) =
          side (ind ((range m).filter fun s => evol (ind U) s ((m : ℤ) - 1 - s))) k s := by
    intro U hU
    rw [mem_filter] at hU
    exact evol_eq_side_of_diag hU.2 fun s hs => by simp [ind, hs]
  -- the row built from a word
  have hbwd : ∀ V ∈ (range m).powerset.filter (fun V => side (ind V) (2 * m) 0 = false),
      ∀ s k, 2 * s + k ≤ 2 * m → evol (ind ((Icc (1 - m : ℤ) m).filter fun i =>
        side (ind V) (m - i).toNat 0)) s ((m : ℤ) - k - s) = side (ind V) k s := by
    intro V hV
    rw [mem_filter] at hV
    refine evol_eq_side_of_row fun k hk => ?_
    by_cases hk' : k = 2 * m
    · subst hk'
      rw [hV.2]
      simp only [ind, mem_filter, mem_Icc, decide_eq_false_iff_not, not_and]
      intro h1
      push_cast at h1
      omega
    · simp only [ind, mem_filter, mem_Icc]
      rw [show ((m : ℤ) - (m - k)).toNat = k by omega]
      have h1 : 1 - (m : ℤ) ≤ m - k := by omega
      have h2 : (m : ℤ) - k ≤ m := by omega
      simp [h1, h2]
  apply card_nbij' (fun U => (range m).filter fun s => evol (ind U) s ((m : ℤ) - 1 - s))
    (fun V => (Icc (1 - m : ℤ) m).filter fun i => side (ind V) (m - i).toNat 0)
  · intro U hU
    have h := hfwd U hU (2 * m) 0 (by omega)
    rw [mem_coe, mem_filter] at hU
    rw [mem_coe, mem_filter, mem_powerset]
    refine ⟨filter_subset _ _, ?_⟩
    rw [← h]
    simp only [evol, ind, decide_eq_false_iff_not]
    intro hmem
    have := mem_Icc.1 (mem_powerset.1 hU.1 hmem)
    push_cast at this
    omega
  · intro V hV
    have h := hbwd V hV
    rw [mem_coe, mem_filter, mem_powerset]
    refine ⟨filter_subset _ _, fun s hs => ?_⟩
    have := h s 0 (by omega)
    simpa [side] using this
  · intro U hU
    have h := hfwd U hU
    rw [mem_coe, mem_filter, mem_powerset] at hU
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨hi, hside⟩
      have hi' := mem_Icc.1 hi
      have := h (m - i).toNat 0 (by omega)
      rw [← this, show (m : ℤ) - ((m - i).toNat : ℕ) - ((0 : ℕ) : ℤ) = i by omega] at hside
      simpa [evol, ind] using hside
    · intro hi
      have hi' := mem_Icc.1 (hU.1 hi)
      refine ⟨hU.1 hi, ?_⟩
      have := h (m - i).toNat 0 (by omega)
      rw [← this, show (m : ℤ) - ((m - i).toNat : ℕ) - ((0 : ℕ) : ℤ) = i by omega]
      simpa [evol, ind] using hi
  · intro V hV
    have h := hbwd V hV
    rw [mem_coe, mem_filter, mem_powerset] at hV
    ext s
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hs, hevol⟩
      have := h s 1 (by omega)
      rw [show (m : ℤ) - ((1 : ℕ) : ℤ) - s = m - 1 - s by push_cast; omega] at this
      rw [this] at hevol
      simpa [side, ind] using hevol
    · intro hs
      have hs' := mem_range.1 (hV.1 hs)
      refine ⟨hs', ?_⟩
      have := h s 1 (by omega)
      rw [show (m : ℤ) - ((1 : ℕ) : ℤ) - s = m - 1 - s by push_cast; omega] at this
      rw [this]
      simpa [side, ind] using hs

theorem side_congr {w w' : ℕ → Bool} :
    ∀ k s, (∀ j, s ≤ j → j < s + (k + 1) / 2 → w j = w' j) → side w k s = side w' k s
  | 0, _, _ => rfl
  | 1, s, h => h s le_rfl (by omega)
  | k + 2, s, h => by
    rw [side_add_two, side_add_two,
      side_congr k (s + 1) fun j h1 h2 => h j (by omega) (by omega),
      side_congr (k + 1) s fun j h1 h2 => h j (by omega) (by omega),
      side_congr k s fun j h1 h2 => h j (by omega) (by omega)]

theorem side_update_of_le {w : ℕ → Bool} {k s i : ℕ} (hi : s + (k + 1) / 2 ≤ i) (b : Bool) :
    side (Function.update w i b) k s = side w k s :=
  side_congr k s fun j _ h2 => by
    rw [Function.update_apply, ite_eq_right (show j ≠ i by omega)]

theorem side_update_of_lt {w : ℕ → Bool} {k s i : ℕ} (hi : i < s) (b : Bool) :
    side (Function.update w i b) k s = side w k s :=
  side_congr k s fun j h1 _ => by
    rw [Function.update_apply, ite_eq_right (show j ≠ i by omega)]

/-- The odd diagonals are linear in their last variable. -/
theorem side_update_flip (w : ℕ → Bool) : ∀ j s,
    side (Function.update w (s + j) true) (2 * j + 1) s =
      !side (Function.update w (s + j) false) (2 * j + 1) s
  | 0, s => by simp [side]
  | j + 1, s => by
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega, show s + (j + 1) = s + 1 + j by omega,
      side_add_two (Function.update w (s + 1 + j) true) (2 * j + 1) s,
      side_add_two (Function.update w (s + 1 + j) false) (2 * j + 1) s,
      side_update_flip w j (s + 1),
      side_update_of_le (k := 2 * j + 1 + 1) (s := s) (i := s + 1 + j) (by omega) true,
      side_update_of_le (k := 2 * j + 1 + 1) (s := s) (i := s + 1 + j) (by omega) false,
      side_update_of_le (k := 2 * j + 1) (s := s) (i := s + 1 + j) (by omega) true,
      side_update_of_le (k := 2 * j + 1) (s := s) (i := s + 1 + j) (by omega) false]
    cases side (Function.update w (s + 1 + j) false) (2 * j + 1) (s + 1) <;>
      cases (side w (2 * j + 1 + 1) s || side w (2 * j + 1) s) <;> rfl

/-- The top coefficient of `w ↦ side w (2m) 0` on `w_0, …, w_{m-1}` is `1`. -/
theorem coef_side_top : ∀ m, 1 ≤ m → coef (fun w => side w (2 * m) 0) (range m) = 1
  | 0, h => absurd h (by omega)
  | 1, _ => by
    have : (fun w : ℕ → Bool => side w (2 * 1) 0) = fun w => w 0 := funext fun w => by
      show xor false (w 0 || false) = w 0
      cases w 0 <;> rfl
    rw [this, range_one, coef_of_mem (mem_singleton_self 0), erase_singleton]
    simp [coef, deriv]
  | i + 2, _ => by
    have ih := coef_side_top (i + 1) (by omega)
    have hf : (fun w => side w (2 * (i + 2)) 0) = fun w =>
        xor (side w (2 * (i + 1)) 1) (xor (side w (2 * (i + 1)) 0)
          (side w (2 * (i + 1) + 1) 0 && !side w (2 * (i + 1)) 0)) := by
      funext w
      rw [show 2 * (i + 2) = 2 * (i + 1) + 2 by omega, side_add_two]
      cases side w (2 * (i + 1) + 1) 0 <;> cases side w (2 * (i + 1)) 0 <;> rfl
    have hmem : i + 1 ∈ range (i + 2) := mem_range.2 (by omega)
    have herase : (range (i + 2)).erase (i + 1) = range (i + 1) := by
      rw [range_add_one, erase_insert notMem_range_self]
    rw [hf, coef_xor, coef_xor,
      coef_eq_zero_of_indep (i := 0)
        (fun w b => side_update_of_lt (k := 2 * (i + 1)) (s := 1) (by omega) b) (by simp),
      coef_eq_zero_of_indep (i := i + 1)
        (fun w b => side_update_of_le (k := 2 * (i + 1)) (s := 0) (by omega) b) hmem,
      coef_and hmem (fun w => by simpa using side_update_flip w (i + 1) 0)
        (fun w b => by
          show (!side (Function.update w (i + 1) b) _ 0) = !side w _ 0
          rw [side_update_of_le (k := 2 * (i + 1)) (s := 0) (by omega) b]),
      herase, coef_not ⟨0, by simp⟩, ih, zero_add, zero_add]

/-- **Lower bound.** For `t ≥ 2` the monomial `x_{2-t} ⋯ x_t` of the center cell has
coefficient `1`. -/
theorem coef_center_top {t : ℕ} (ht : 2 ≤ t) :
    coef (fun x => evol x t 0) (Icc (2 - t : ℤ) t) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hmem : ((m + 1 : ℕ) : ℤ) ∈ Icc (2 - ((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) := by
    simp only [mem_Icc]
    omega
  have herase : (Icc (2 - ((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ)).erase ((m + 1 : ℕ) : ℤ) =
      Icc (1 - m : ℤ) m := by
    ext i
    simp only [mem_erase, mem_Icc]
    push_cast
    omega
  rw [coef_of_mem hmem, herase, coef, sum_boole]
  have hd : ∀ U ∈ (Icc (1 - m : ℤ) m).powerset,
      deriv ((m + 1 : ℕ) : ℤ) (fun x => evol x (m + 1) 0) (ind U) = true ↔
        ∀ s ≤ m, evol (ind U) s ((m : ℤ) - s) = false := by
    intro U _
    have := deriv_evol_right ((m + 1 : ℕ) : ℤ) (ind U) (m + 1)
    rw [sub_self] at this
    rw [this]
    constructor
    · intro h s hs
      have := h s (by omega)
      rwa [show ((m + 1 : ℕ) : ℤ) - s - 1 = m - s by push_cast; omega] at this
    · intro h s hs
      rw [show ((m + 1 : ℕ) : ℤ) - s - 1 = m - s by push_cast; omega]
      exact h s (by omega)
  rw [filter_congr hd, card_white_diag]
  have hcard := card_filter_add_card_filter_not (s := (range m).powerset)
    (fun V => side (ind V) (2 * m) 0 = true)
  simp only [Bool.not_eq_true, card_powerset, card_range] at hcard
  have htop := coef_side_top m (by omega)
  rw [coef, sum_boole] at htop
  have h2 : ((2 ^ m : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_pow (by omega)]
  have := congrArg (Nat.cast : ℕ → ZMod 2) hcard
  rw [Nat.cast_add, htop, h2] at this
  revert this
  generalize ((((range m).powerset.filter fun V => side (ind V) (2 * m) 0 = false).card : ℕ) :
    ZMod 2) = b
  revert b
  decide

/-! ### The degree -/

/-- **The algebraic degree of rule 30's `t`-step map.** For `t ≥ 2` the center cell after `t`
steps, as a Boolean function of the initial cells, has algebraic normal form of degree `2t − 1`. -/
theorem isGreatest_card_coef_center {t : ℕ} (ht : 2 ≤ t) :
    IsGreatest {n | ∃ S : Finset ℤ, S.card = n ∧ coef (fun x => evol x t 0) S ≠ 0} (2 * t - 1) := by
  refine ⟨⟨Icc (2 - t : ℤ) t, by rw [Int.card_Icc]; omega, by
    rw [coef_center_top ht]; decide⟩, ?_⟩
  rintro n ⟨S, rfl, hS⟩
  by_contra hlt
  exact hS (coef_evol_eq_zero t 0 (by omega) (by omega))

/-- For `t ≥ 3` the monomial of top degree is unique: `x_{2-t} ⋯ x_t`. -/
theorem eq_top_of_coef_center_ne_zero {t : ℕ} (ht : 3 ≤ t) {S : Finset ℤ}
    (hS : S.card = 2 * t - 1) (h : coef (fun x => evol x t 0) S ≠ 0) :
    S = Icc (2 - t : ℤ) t := by
  rw [eq_Icc_of_coef_ne_zero ht 0 hS h]
  congr 1 <;> omega

/-- The coefficient of `x_0` is the center column: Problem 1 concerns the linear part of `Φ_t`. -/
theorem coef_center_singleton (t : ℕ) :
    coef (fun x => evol x t 0) {0} = if Rule30Prize.center t then 1 else 0 := by
  have hw : ∀ s p, evol (fun _ => false) s p = false := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih => intro p; rw [evol_succ, ih, ih, ih]; rfl
  have h1 : Function.update (ind (∅ : Finset ℤ)) 0 true = seed := funext fun i => by
    rw [Function.update_apply]
    by_cases hi : i = 0
    · simp [seed, hi]
    · simp [ind, seed, hi]
  have h0 : Function.update (ind (∅ : Finset ℤ)) 0 false = fun _ => false := funext fun i => by
    rw [Function.update_apply]
    by_cases hi : i = 0
    · simp [hi]
    · simp [ind, hi]
  rw [coef_of_mem (mem_singleton_self 0), erase_singleton]
  simp only [coef, powerset_empty, sum_singleton, deriv, h1, h0, evol_seed, hw, Bool.xor_false]
  rfl

/-! ### Walsh coefficients -/

/-- The Walsh coefficient of `f` at the linear function `x ↦ ⊕_{i ∈ A} x_i`, over the cube on the
variables `S`: `∑_{U ⊆ S} (-1)^(f(1_U) ⊕ |U ∩ A|)`. -/
def walsh {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → Bool) (S A : Finset ι) : ℤ :=
  ∑ U ∈ S.powerset, if xor (f (ind U)) (decide ((U ∩ A).card % 2 = 1)) then -1 else 1

/-- A function that flips with `x_i` has Walsh coefficient `0` at every linear function that does
not involve `x_i`. -/
theorem walsh_eq_zero {ι : Type*} [DecidableEq ι] {f : (ι → Bool) → Bool} {S A : Finset ι}
    {i : ι} (hi : i ∈ S) (hiA : i ∉ A)
    (hf : ∀ x, f (Function.update x i true) = !f (Function.update x i false)) :
    walsh f S A = 0 := by
  rw [walsh, ← insert_erase hi, sum_powerset_insert (notMem_erase i S), ← sum_add_distrib]
  refine sum_eq_zero fun U hU => ?_
  have hiU : i ∉ U := fun h => notMem_erase i S (mem_powerset.1 hU h)
  have h1 : ind (insert i U) = Function.update (ind U) i true := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [ind]
    · simp [ind, hj]
  have h0 : Function.update (ind U) i false = ind U := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [ind, hiU]
    · simp [ind, hj]
  have hA : insert i U ∩ A = U ∩ A := by
    ext j
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | h, hj⟩
      · exact absurd hj hiA
      · exact ⟨h, hj⟩
    · rintro ⟨h, hj⟩
      exact ⟨Or.inr h, hj⟩
  rw [h1, hA, hf, h0]
  cases f (ind U) <;> cases decide ((U ∩ A).card % 2 = 1) <;> simp

/-- **`Φ_t` is uncorrelated with every affine function that does not involve `x_{-t}`.** -/
theorem walsh_center_eq_zero (t : ℕ) {A : Finset ℤ} (hA : -(t : ℤ) ∉ A) :
    walsh (fun x => evol x t 0) (Icc (-(t : ℤ)) t) A = 0 := by
  refine walsh_eq_zero (i := 0 - (t : ℤ)) (by simp) (by simpa using hA) fun x => ?_
  exact evol_update_left x t 0

/-- **`Φ_t` is balanced**: it takes the value `1` on exactly half of the `2^(2t+1)` inputs. -/
theorem card_center_true (t : ℕ) :
    ((Icc (-(t : ℤ)) t).powerset.filter fun U => evol (ind U) t 0 = true).card = 2 ^ (2 * t) := by
  have hw := walsh_center_eq_zero t (A := ∅) (by simp)
  simp only [walsh, inter_empty, card_empty, Nat.zero_mod, zero_ne_one, decide_false,
    Bool.xor_false] at hw
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_neg, mul_one, mul_one] at hw
  have htot := card_filter_add_card_filter_not (s := (Icc (-(t : ℤ)) t).powerset)
    (fun U => evol (ind U) t 0 = true)
  rw [card_powerset, Int.card_Icc, show ((t : ℤ) + 1 - -(t : ℤ)).toNat = 2 * t + 1 by omega]
    at htot
  simp only [Bool.not_eq_true] at htot hw
  have : ((((Icc (-(t : ℤ)) t).powerset.filter fun U => evol (ind U) t 0 = true).card : ℤ)) =
      (((Icc (-(t : ℤ)) t).powerset.filter fun U => evol (ind U) t 0 = false).card : ℤ) := by
    omega
  have h2 : (2 : ℕ) ^ (2 * t + 1) = 2 ^ (2 * t) * 2 := pow_succ 2 (2 * t)
  omega

/-! ### The center trace of a random configuration is uniform -/

/-- Splitting the subsets of `insert i S` by whether they contain `i`. -/
theorem card_filter_powerset_insert {S : Finset ℤ} {i : ℤ} (hi : i ∉ S) (P : Finset ℤ → Prop)
    [DecidablePred P] :
    ((insert i S).powerset.filter P).card =
      (S.powerset.filter P).card + (S.powerset.filter fun U => P (insert i U)).card := by
  rw [Finset.powerset_insert, Finset.filter_union, Finset.card_union_of_disjoint]
  · rw [Finset.filter_image, Finset.card_image_of_injOn]
    intro U hU V hV h
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hU hV
    have hiU : i ∉ U := fun h' => hi (hU.1 h')
    have hiV : i ∉ V := fun h' => hi (hV.1 h')
    rw [← Finset.erase_insert hiU, ← Finset.erase_insert hiV]
    exact congrArg (fun W => W.erase i) h
  · rw [Finset.disjoint_left]
    intro U hU hU'
    obtain ⟨V, -, hVU⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hU').1
    have hU1 := (Finset.mem_powerset.1 (Finset.mem_filter.1 hU).1)
    exact hi (hU1 (hVU ▸ Finset.mem_insert_self i V))

/-- **The center trace of a random configuration is uniform**: every
word `w(0), …, w(n)` is the center trace of exactly `2ⁿ` of the `2^(2n+1)` configurations on
`[-n, n]`, so the trace map pushes the uniform Bernoulli measure to the uniform measure. Cells
`±(n+1)` do not affect the trace up to time `n`, and flipping the cell `-(n+1)` flips the center at
time `n + 1` (left-permutivity). -/
theorem card_trace (w : ℕ → Bool) : ∀ n : ℕ,
    ((Icc (-(n : ℤ)) n).powerset.filter fun U => ∀ t ≤ n, evol (ind U) t 0 = w t).card = 2 ^ n
  | 0 => by
    rw [show Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} by simp, pow_zero, Finset.card_eq_one]
    refine ⟨if w 0 then {0} else ∅, ?_⟩
    ext U
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, Finset.subset_singleton_iff]
    have hev : (∀ t ≤ 0, evol (ind U) t 0 = w t) ↔ decide ((0 : ℤ) ∈ U) = w 0 :=
      ⟨fun h => h 0 le_rfl, fun h t ht => by
        obtain rfl : t = 0 := by omega
        exact h⟩
    rw [hev]
    cases hw : w 0
    · constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · simp at h
      · intro h
        rw [ite_eq_right (by simp)] at h
        subst h
        simp
    · constructor
      · rintro ⟨rfl | rfl, h⟩
        · simp at h
        · rfl
      · intro h
        rw [ite_eq_left rfl] at h
        subst h
        simp
  | n + 1 => by
    have ih := card_trace w n
    set B := Icc (-(n : ℤ)) n with hB
    set L : ℤ := -((n : ℤ) + 1)
    set R : ℤ := (n : ℤ) + 1
    have hRB : R ∉ B := by simp [B, R]
    have hLB : L ∉ insert R B := by simp [B, L, R]; omega
    have hA : Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) = insert L (insert R B) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, B, L, R]
      push_cast
      omega
    rw [hA]
    -- the constraints up to time `n` do not see the cells `L` and `R`
    set P : Finset ℤ → Prop := fun U => ∀ t ≤ n, evol (ind U) t 0 = w t
    have hfar : ∀ (U : Finset ℤ) (j : ℤ), j = L ∨ j = R → (P (insert j U) ↔ P U) := by
      intro U j hj
      refine forall_congr' fun t => imp_congr_right fun ht => ?_
      rw [evol_congr t 0 (y := ind U) fun k hk1 hk2 => ?_]
      simp only [ind, Finset.mem_insert]
      have : k ≠ j := by rcases hj with rfl | rfl <;> simp only [L, R] <;> omega
      simp [this]
    -- flipping `L` flips the center at time `n + 1`
    have hflip : ∀ U : Finset ℤ, L ∉ U →
        evol (ind (insert L U)) (n + 1) 0 = !evol (ind U) (n + 1) 0 := by
      intro U hLU
      have ha : (0 : ℤ) - ((n + 1 : ℕ) : ℤ) = L := by simp only [L]; push_cast; omega
      have e0 := evol_update_left (ind U) (n + 1) 0
      rw [ha] at e0
      have e1 : ind (insert L U) = Function.update (ind U) L true := by
        funext k
        by_cases hk : k = L
        · subst hk; simp [ind]
        · simp [ind, Function.update, hk]
      have e2 : Function.update (ind U) L false = ind U :=
        Function.update_eq_self_iff.2 (by simp [ind, hLU])
      rw [e1, e0, e2]
    have hsplit : ∀ U : Finset ℤ, (∀ t ≤ n + 1, evol (ind U) t 0 = w t) ↔
        P U ∧ evol (ind U) (n + 1) 0 = w (n + 1) := fun U =>
      ⟨fun h => ⟨fun t ht => h t (by omega), h (n + 1) le_rfl⟩, fun h t ht => by
        rcases Nat.lt_or_ge t (n + 1) with h' | h'
        · exact h.1 t (by omega)
        · obtain rfl : t = n + 1 := by omega
          exact h.2⟩
    simp only [Finset.filter_congr fun U _ => hsplit U]
    rw [card_filter_powerset_insert hLB]
    -- the half with `L` is the complement of the half without it
    have hL : ((insert R B).powerset.filter fun U =>
        P (insert L U) ∧ evol (ind (insert L U)) (n + 1) 0 = w (n + 1)) =
        (insert R B).powerset.filter fun U => P U ∧ ¬ evol (ind U) (n + 1) 0 = w (n + 1) := by
      refine Finset.filter_congr fun U hU => ?_
      rw [Finset.mem_powerset] at hU
      rw [hfar U L (Or.inl rfl), hflip U fun h => hLB (hU h)]
      cases evol (ind U) (n + 1) 0 <;> cases w (n + 1) <;> simp
    rw [hL, ← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun U _ h1 h2 => h2.2 h1.2),
      ← Finset.filter_or]
    have hP : ((insert R B).powerset.filter fun U =>
        (P U ∧ evol (ind U) (n + 1) 0 = w (n + 1)) ∨
          (P U ∧ ¬ evol (ind U) (n + 1) 0 = w (n + 1))) =
        (insert R B).powerset.filter P :=
      Finset.filter_congr fun U _ => by tauto
    rw [hP, card_filter_powerset_insert hRB]
    have hR : (B.powerset.filter fun U => P (insert R U)) = B.powerset.filter P :=
      Finset.filter_congr fun U _ => hfar U R (Or.inr rfl)
    rw [hR, ih, pow_succ]
    omega

/-- **Every window of every row is balanced** (Hedlund's theorem for rule 30, in counts): each word
on the cells `a, …, a + m - 1` of the `t`-th row comes from exactly `4^t` of the `2^(m + 2t)`
configurations on `[a - t, a + m - 1 + t]`. Adding the cell `a - 1` to the window adds the cell
`a - 1 - t` to the light cone; flipping it flips the new cell (left-permutivity) and no other. -/
theorem card_window (t : ℕ) (w : ℤ → Bool) : ∀ (m : ℕ) (a : ℤ),
    ((Icc (a - t) (a + m - 1 + t)).powerset.filter fun U =>
      ∀ i ∈ Ico a (a + m), evol (ind U) t i = w i).card = 4 ^ t
  | 0, a => by
    rw [Finset.filter_true_of_mem fun U _ i hi => absurd hi (by simp),
      Finset.card_powerset, Int.card_Icc, show a + ((0 : ℕ) : ℤ) - 1 + t + 1 - (a - t) =
        ((2 * t : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast, pow_mul]
    norm_num
  | m + 1, a => by
    have ih := card_window t w m (a + 1)
    set J := Icc (a + 1 - t) (a + 1 + m - 1 + t) with hJ
    set L : ℤ := a - t
    have hLJ : L ∉ J := by simp [J, L]
    have hA : Icc (a - t) (a + ((m + 1 : ℕ) : ℤ) - 1 + t) = insert L J := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, J, L]
      push_cast
      omega
    rw [hA]
    set P : Finset ℤ → Prop := fun U => ∀ i ∈ Ico (a + 1) (a + 1 + m), evol (ind U) t i = w i
    -- the old cells do not see the cell `L`
    have hfar : ∀ U : Finset ℤ, P (insert L U) ↔ P U := by
      intro U
      refine forall₂_congr fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [evol_congr t i (y := ind U) fun k hk1 _ => ?_]
      have : k ≠ L := by simp only [L]; omega
      simp [ind, this]
    -- flipping `L` flips the cell `a`
    have hflip : ∀ U : Finset ℤ, L ∉ U → evol (ind (insert L U)) t a = !evol (ind U) t a := by
      intro U hLU
      have e0 := evol_update_left (ind U) t a
      have e1 : ind (insert L U) = Function.update (ind U) L true := by
        funext k
        by_cases hk : k = L
        · subst hk
          simp [ind]
        · simp [ind, Function.update, hk]
      have e2 : Function.update (ind U) L false = ind U :=
        Function.update_eq_self_iff.2 (by simp [ind, hLU])
      rw [e1, e0, e2]
    have hsplit : ∀ U : Finset ℤ, (∀ i ∈ Ico a (a + ((m + 1 : ℕ) : ℤ)),
        evol (ind U) t i = w i) ↔ P U ∧ evol (ind U) t a = w a := fun U => by
      simp only [P, Finset.mem_Ico]
      constructor
      · intro h
        exact ⟨fun i hi => h i ⟨by omega, by push_cast; omega⟩,
          h a ⟨le_rfl, by push_cast; omega⟩⟩
      · intro h i hi
        rcases eq_or_lt_of_le hi.1 with rfl | hlt
        · exact h.2
        · exact h.1 i ⟨by omega, by push_cast at hi; omega⟩
    simp only [Finset.filter_congr fun U _ => hsplit U]
    rw [card_filter_powerset_insert hLJ]
    -- the half with `L` is the complement of the half without it
    have hL : (J.powerset.filter fun U => P (insert L U) ∧ evol (ind (insert L U)) t a = w a) =
        J.powerset.filter fun U => P U ∧ ¬ evol (ind U) t a = w a := by
      refine Finset.filter_congr fun U hU => ?_
      rw [Finset.mem_powerset] at hU
      rw [hfar U, hflip U fun h => hLJ (hU h)]
      cases evol (ind U) t a <;> cases w a <;> simp
    rw [hL, ← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun U _ h1 h2 => h2.2 h1.2),
      ← Finset.filter_or]
    have hP : (J.powerset.filter fun U => (P U ∧ evol (ind U) t a = w a) ∨
        (P U ∧ ¬ evol (ind U) t a = w a)) = J.powerset.filter P :=
      Finset.filter_congr fun U _ => by tauto
    rw [hP]
    exact ih

/-! ### Feedback functions of bounded algebraic degree -/

/-- `F` has algebraic degree at most `k`: its algebraic normal form has no monomial of more than
`k` variables. -/
def DegreeLE {m : ℕ} (k : ℕ) (F : (Fin m → Bool) → Bool) : Prop :=
  ∀ S : Finset (Fin m), k < S.card → coef F S = 0

/-- **Feedback of degree `k`**: for every `k ≥ 1`, Problem 1 holds iff no feedback shift
register whose feedback function has algebraic degree at most `k` generates the center column. An
eventually periodic column is generated by the linear feedback `c(i + T + P) = c(i + T)`; the case
`k = 0` (constant feedback) must be excluded. -/
theorem problem1_iff_no_feedback_degreeLE {k : ℕ} (hk : 1 ≤ k) : Rule30Prize.Problem1 ↔
    ∀ m, ¬ ∃ F : (Fin m → Bool) → Bool, DegreeLE k F ∧ ∀ i, c (i + m) = F fun j => c (i + j) := by
  constructor
  · rintro h m ⟨F, -, hF⟩
    exact (WordsAutomata.problem1_iff_no_feedback_from_zero.1 h) m ⟨F, hF⟩
  · intro h hep
    obtain ⟨T, P, hP, hper⟩ := hep
    -- the feedback reads the letter `T` places back
    let a : Fin (T + P) := ⟨T, by omega⟩
    refine h (T + P) ⟨fun w => w a, fun S hS => ?_, fun i => ?_⟩
    · obtain ⟨j, hj, hja⟩ := Finset.exists_mem_ne (s := S) (by omega) a
      refine coef_eq_zero_of_indep (i := j) (fun x b => ?_) hj
      show Function.update x j b a = x a
      rw [Function.update_of_ne (Ne.symm hja)]
    · show c (i + (T + P)) = c (i + T)
      rw [← Nat.add_assoc]
      exact hper _ (by omega)

end Rule30Equivalents.AlgebraicDegree
