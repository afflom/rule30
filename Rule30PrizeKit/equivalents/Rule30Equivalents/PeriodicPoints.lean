module

public import Rule30Equivalents.Genericity
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
# Periodic points of rule 30

Say that `x` recurs if `F^k x = σ^d x` for some `k ≥ 1` and `d`: it
comes back after `k` steps moved `d` cells to the left (`Recurs`), a pattern travelling at the
velocity `-d/k`. Periodic configurations are the case `d = 0`.

* `eq_of_recurs_of_eq_on`: **for `1 - k ≤ d ≤ k`, a recurring configuration is determined, to the
  left, by any `2k` adjacent cells**. Rule 30 is left-permutive, and so is `F^k`, in the cell
  `i - k` (`evol_ne_of_ne_left`, from `Genericity.evol_flip_at`): the cell `j - 1` is the one value
  that makes `F^k(x)_{j - 1 + k} = x_{j - 1 + k + d}` given the cells `j, …, j + 2k - 1`.
* `recurs_add_factorial`: so **every such configuration is spatially periodic**, with period
  `(4^k)!`. Among `4^k + 1` adjacent windows of `2k` cells two coincide, so `x` agrees with its
  shift by some `p ≤ 4^k` left of any given cell (`periodic_left_of_window`), and `p` divides
  `(4^k)!`. Every rational velocity in `[-1, 1)` is `-d/k` with `1 - k ≤ d ≤ k`, so **rule 30 has
  no gliders at these velocities**: a pattern that reappears exactly while moving left, standing
  still, or moving right slower than light is spatially periodic. `evol_add_factorial` is the
  periodic case.
* `ncard_recurs_le`, `ncard_fixedPoints_le`: hence **at most `4^k` configurations satisfy
  `F^k x = σ^d x`**: such a configuration is determined by its cells `0, …, 2k - 1`. Rule 30 has
  countably many periodic points, all of them spatially periodic.
* `evol_one_eq_self_iff`: **rule 30 has exactly three fixed points**, all white and the two phases
  of `…0101…`. `F x = x` says `x_{i-1} = ¬x_i ∧ x_{i+1}`, and one black cell forces the alternating
  pattern in both directions.
-/

@[expose] public section

namespace Rule30Equivalents.PeriodicPoints

open Ruliology.CellularAutomata Rule30Realization

/-- **`F^k` is left-permutive**: configurations that agree on the cells `i - k + 1, …, i + k` and
differ at `i - k` differ at `i` after `k` steps. -/
theorem evol_ne_of_ne_left {x y : ℤ → Bool} {k : ℕ} {i : ℤ}
    (h : ∀ j, i - k < j → j ≤ i + k → x j = y j) (hne : x (i - k) ≠ y (i - k)) :
    evol x k i ≠ evol y k i := by
  have hy : y (i - k) = !x (i - k) := by
    cases hx : x (i - k) <;> cases hy : y (i - k) <;> simp_all
  have e : evol (Function.update x (i - k) (!x (i - k))) k i = evol y k i :=
    AlgebraicDegree.evol_congr k i fun j hj1 hj2 => by
      by_cases hj : j = i - k
      · subst hj
        rw [Function.update_self, hy]
      · rw [Function.update_of_ne hj]
        exact h j (by omega) hj2
  rw [Genericity.evol_flip_at] at e
  rw [← e]
  cases evol x k i <;> simp

/-- `x` comes back after `k` steps, moved by `d` cells to the left: `F^k x = σ^d x`. For `d = 0`,
`F^k x = x`. -/
def Recurs (k : ℕ) (d : ℤ) (x : ℤ → Bool) : Prop := ∀ i, evol x k i = x (i + d)

theorem recurs_zero_iff {k : ℕ} {x : ℤ → Bool} : Recurs k 0 x ↔ evol x k = x := by
  simp only [Recurs, add_zero]
  exact funext_iff.symm

/-- A shift of a recurring configuration recurs in the same way. -/
theorem Recurs.shift {k : ℕ} {d : ℤ} {x : ℤ → Bool} (hx : Recurs k d x) (e : ℤ) :
    Recurs k d fun i => x (i + e) := fun i => by
  have := Rule30ZeroBoundaryBarriers.evol_shift_all (x := fun i => x (i + e)) (x' := x) (d := e)
    (fun p => rfl) k i
  rw [← this, hx, add_right_comm]

/-- **A recurring configuration is determined to the left by any `2k` adjacent cells**, when it
moves at most one cell per step to the left and less than one to the right (`1 - k ≤ d ≤ k`): if
`x, y` both satisfy `F^k z = σ^d z` and agree on `[j, j + 2k)`, they agree left of `j + 2k`. The
cell `j - 1` is the one value that makes `F^k(x)_{j - 1 + k}` equal `x_{j - 1 + k + d}`, a cell of
the window. -/
theorem eq_of_recurs_of_eq_on {k : ℕ} {d : ℤ} (hd1 : 1 - (k : ℤ) ≤ d) (hd2 : d ≤ k)
    {x y : ℤ → Bool} (hx : Recurs k d x) (hy : Recurs k d y) {j : ℤ}
    (h : ∀ i, j ≤ i → i < j + 2 * k → x i = y i) : ∀ i, i < j + 2 * k → x i = y i := by
  have key : ∀ n : ℕ, ∀ i, j - n ≤ i → i < j + 2 * k → x i = y i := by
    intro n
    induction n with
    | zero => intro i h1 h2; exact h i (by omega) h2
    | succ n ih =>
      intro i h1 h2
      by_cases hi : j - n ≤ i
      · exact ih i hi h2
      · -- `i = j - n - 1`, the cell left of the window `[j - n, j - n + 2k)`
        by_contra hne
        apply evol_ne_of_ne_left (k := k) (i := i + k)
          (fun l hl1 hl2 => ih l (by omega) (by omega)) (by rwa [add_sub_cancel_right])
        rw [hx, hy]
        exact ih (i + k + d) (by omega) (by omega)
  intro i hi
  exact key (j - i).toNat i (by omega) hi

/-- If two windows of `2k` cells at `a < b` coincide, `x` is `(b - a)`-periodic left of
`a + 2k`. -/
theorem periodic_left_of_window {k : ℕ} {d : ℤ} (hd1 : 1 - (k : ℤ) ≤ d) (hd2 : d ≤ k)
    {x : ℤ → Bool} (hx : Recurs k d x) {a b : ℤ}
    (h : ∀ j : ℕ, j < 2 * k → x (a + j) = x (b + j)) :
    ∀ i, i < a + 2 * k → x i = x (i + (b - a)) :=
  eq_of_recurs_of_eq_on hd1 hd2 hx (hx.shift (b - a)) fun i h1 h2 => by
    have := h (i - a).toNat (by omega)
    rw [show a + ((i - a).toNat : ℤ) = i by omega] at this
    rw [this, show b + ((i - a).toNat : ℤ) = i + (b - a) by omega]

/-- **Every recurring configuration of rule 30 with `1 - k ≤ d ≤ k` is spatially periodic**, with
period `(4^k)!`. -/
theorem recurs_add_factorial {k : ℕ} {d : ℤ} (hd1 : 1 - (k : ℤ) ≤ d) (hd2 : d ≤ k)
    {x : ℤ → Bool} (hx : Recurs k d x) (i : ℤ) : x (i + (4 ^ k).factorial) = x i := by
  set N := (4 ^ k).factorial with hN
  -- left of every cell `M`, `x` has a period `p ≤ 4^k`, which divides `N`
  have hleft : ∀ M : ℤ, ∀ i, i ≤ M → x (i - N) = x i := by
    intro M
    let W : Fin (4 ^ k + 1) → (Fin (2 * k) → Bool) := fun a j => x (M + a + j)
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt W (by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_mul]
      norm_num)
    -- order the two windows
    obtain ⟨a', b', hlt, ha', hb', he'⟩ : ∃ a' b' : ℕ, a' < b' ∧ a' ≤ 4 ^ k ∧ b' ≤ 4 ^ k ∧
        ∀ j : ℕ, j < 2 * k → x (M + a' + j) = x (M + b' + j) := by
      rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with h | h
      · exact ⟨a, b, h, Nat.lt_succ_iff.1 a.2, Nat.lt_succ_iff.1 b.2,
          fun j hj => congrFun he ⟨j, hj⟩⟩
      · exact ⟨b, a, h, Nat.lt_succ_iff.1 b.2, Nat.lt_succ_iff.1 a.2,
          fun j hj => (congrFun he ⟨j, hj⟩).symm⟩
    have hper := periodic_left_of_window hd1 hd2 hx (a := M + a') (b := M + b') he'
    set p := b' - a' with hp
    have hp0 : 0 < p := by omega
    obtain ⟨q, hq⟩ := Nat.dvd_factorial (n := 4 ^ k) hp0 (by omega)
    -- `x (i - N + j p) = x (i - N)` for `j ≤ q`, step by step
    intro i hi
    have hstep : ∀ j : ℕ, j ≤ q → x (i - N + (j * p : ℕ)) = x (i - N) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hjp : ((j * p : ℕ) : ℤ) + p ≤ N := by
          have h' : (j + 1) * p ≤ N := by
            rw [hN, hq, mul_comm p q]; exact Nat.mul_le_mul_right p hj
          have : (((j + 1) * p : ℕ) : ℤ) ≤ N := by exact_mod_cast h'
          push_cast at this ⊢
          linarith
        have h1 := hper (i - N + (j * p : ℕ)) (by omega)
        rw [← ih (by omega), h1]
        congr 1
        rw [show (j + 1) * p = j * p + p by ring]
        push_cast
        omega
    have := hstep q le_rfl
    rw [show (q * p : ℕ) = N by rw [hN, hq]; ring] at this
    rw [← this]
    congr 1
    ring
  have := hleft (i + N) (i + N) le_rfl
  rw [add_sub_cancel_right] at this
  exact this.symm

/-- **Every periodic configuration of rule 30 is spatially periodic**, with period `(4^k)!`. -/
theorem evol_add_factorial {k : ℕ} (hk : 0 < k) {x : ℤ → Bool} (hx : evol x k = x) (i : ℤ) :
    x (i + (4 ^ k).factorial) = x i :=
  recurs_add_factorial (d := 0) (by omega) (by omega) (recurs_zero_iff.2 hx) i

/-- **At most `4^k` configurations satisfy `F^k x = σ^d x`**, for `1 - k ≤ d ≤ k`: such a
configuration is determined by its cells `0, …, 2k - 1`. -/
theorem ncard_recurs_le {k : ℕ} {d : ℤ} (hd1 : 1 - (k : ℤ) ≤ d) (hd2 : d ≤ k) :
    {x : ℤ → Bool | Recurs k d x}.ncard ≤ 4 ^ k := by
  have hk : 0 < k := by omega
  have hinj : Set.InjOn (fun (x : ℤ → Bool) (j : Fin (2 * k)) => x j)
      {x : ℤ → Bool | Recurs k d x} := by
    intro x hx y hy hxy
    have hleft := eq_of_recurs_of_eq_on hd1 hd2 hx hy (j := 0) fun i h1 h2 => by
      have := congrFun hxy ⟨i.toNat, by omega⟩
      simpa [show ((i.toNat : ℕ) : ℤ) = i by omega] using this
    -- right of `2k`, go left by multiples of the spatial period
    funext i
    have hback : ∀ (z : ℤ → Bool), Recurs k d z → ∀ m : ℕ,
        z (i - m * (4 ^ k).factorial) = z i := by
      intro z hz m
      induction m with
      | zero => simp
      | succ m ih =>
        have := recurs_add_factorial hd1 hd2 hz (i - ((m + 1 : ℕ) : ℤ) * (4 ^ k).factorial)
        rw [← ih, ← this]
        congr 1
        push_cast
        ring
    rw [← hback x hx i.toNat, ← hback y hy i.toNat]
    refine hleft _ ?_
    have h1 : (1 : ℤ) ≤ (4 ^ k).factorial := Nat.one_le_cast.2 (Nat.factorial_pos _)
    have h2 := le_mul_of_one_le_right (Int.natCast_nonneg i.toNat) h1
    have h3 : (0 : ℤ) < k := by exact_mod_cast hk
    linarith [Int.self_le_toNat i]
  calc {x : ℤ → Bool | Recurs k d x}.ncard
      ≤ (Set.univ : Set (Fin (2 * k) → Bool)).ncard :=
        Set.ncard_le_ncard_of_injOn _ (fun _ _ => Set.mem_univ _) hinj Set.finite_univ
    _ = 4 ^ k := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, pow_mul]
      norm_num

/-- **At most `4^k` configurations satisfy `F^k x = x`.** -/
theorem ncard_fixedPoints_le {k : ℕ} (hk : 0 < k) :
    {x : ℤ → Bool | evol x k = x}.ncard ≤ 4 ^ k := by
  have h := ncard_recurs_le (k := k) (d := 0) (by omega) (by omega)
  simp only [recurs_zero_iff] at h
  exact h

/-! ### The fixed points -/

/-- The alternating configuration `…0101…`, black at the odd cells. -/
def alt (i : ℤ) : Bool := decide (i % 2 = 1)

/-- `F x = x` says `x_{i-1} = ¬x_i ∧ x_{i+1}` at every cell. -/
theorem evol_one_eq_self_iff_local (x : ℤ → Bool) :
    evol x 1 = x ↔ ∀ i, x (i - 1) = (!x i && x (i + 1)) := by
  constructor
  · intro h i
    have := congrFun h i
    show x (i - 1) = (!x i && x (i + 1))
    change xor (x (i - 1)) (x i || x (i + 1)) = x i at this
    cases h1 : x (i - 1) <;> cases h2 : x i <;> cases h3 : x (i + 1) <;> simp_all
  · intro h
    funext i
    show xor (x (i - 1)) (x i || x (i + 1)) = x i
    rw [h i]
    cases x i <;> cases x (i + 1) <;> rfl

/-- **Rule 30 has exactly three fixed points**: all white, and the two phases of `…0101…`. -/
theorem evol_one_eq_self_iff (x : ℤ → Bool) :
    evol x 1 = x ↔ x = (fun _ => false) ∨ x = alt ∨ x = fun i => alt (i + 1) := by
  rw [evol_one_eq_self_iff_local]
  constructor
  · intro h
    by_cases hb : ∃ j, x j = true
    · obtain ⟨j, hj⟩ := hb
      -- a black cell is followed and preceded by the alternating pattern
      have fwd : ∀ a, x a = true → x (a + 1) = false ∧ x (a + 2) = true := fun a ha => by
        have := h (a + 1)
        rw [show a + 1 - 1 = a by ring, show a + 1 + 1 = a + 2 by ring, ha] at this
        revert this
        cases x (a + 1) <;> cases x (a + 2) <;> decide
      have bwd : ∀ a, x a = true → x (a - 1) = false ∧ x (a - 2) = true := fun a ha => by
        have h1 : x (a - 1) = false := by
          rw [h a, ha]
          rfl
        refine ⟨h1, ?_⟩
        have h2 := h (a - 1)
        rw [show a - 1 - 1 = a - 2 by ring, show a - 1 + 1 = a by ring, h1, ha] at h2
        exact h2
      have hup : ∀ n : ℕ, x (j + 2 * n) = true := fun n => by
        induction n with
        | zero => simpa using hj
        | succ n ih => rw [show j + 2 * ((n + 1 : ℕ) : ℤ) = j + 2 * n + 2 by push_cast; ring]
                       exact (fwd _ ih).2
      have hdown : ∀ n : ℕ, x (j - 2 * n) = true := fun n => by
        induction n with
        | zero => simpa using hj
        | succ n ih => rw [show j - 2 * ((n + 1 : ℕ) : ℤ) = j - 2 * n - 2 by push_cast; ring]
                       exact (bwd _ ih).2
      have heven : ∀ i, (i - j) % 2 = 0 → x i = true := fun i hi => by
        rcases le_total j i with hij | hij
        · have := hup ((i - j) / 2).toNat
          rwa [show j + 2 * (((i - j) / 2).toNat : ℤ) = i by omega] at this
        · have := hdown ((j - i) / 2).toNat
          rwa [show j - 2 * (((j - i) / 2).toNat : ℤ) = i by omega] at this
      have hx : ∀ i, x i = decide ((i - j) % 2 = 0) := fun i => by
        by_cases hi : (i - j) % 2 = 0
        · rw [decide_eq_true hi]
          exact heven i hi
        · rw [decide_eq_false hi]
          have := (fwd (i - 1) (heven (i - 1) (by omega))).1
          rwa [sub_add_cancel] at this
      right
      rcases Int.emod_two_eq_zero_or_one j with hj2 | hj2
      · right
        funext i
        rw [hx i, alt, decide_eq_decide]
        omega
      · left
        funext i
        rw [hx i, alt, decide_eq_decide]
        omega
    · left
      funext i
      push Not at hb
      simpa using hb i
  · rintro (rfl | rfl | rfl) i
    · rfl
    · show decide ((i - 1) % 2 = 1) = (!decide (i % 2 = 1) && decide ((i + 1) % 2 = 1))
      rcases Int.emod_two_eq_zero_or_one i with hi | hi
      · rw [show (i - 1) % 2 = 1 by omega, hi, show (i + 1) % 2 = 1 by omega]
        decide
      · rw [show (i - 1) % 2 = 0 by omega, hi, show (i + 1) % 2 = 0 by omega]
        decide
    · show decide ((i - 1 + 1) % 2 = 1) =
        (!decide ((i + 1) % 2 = 1) && decide ((i + 1 + 1) % 2 = 1))
      rcases Int.emod_two_eq_zero_or_one i with hi | hi
      · rw [show (i - 1 + 1) % 2 = 0 by omega, show (i + 1) % 2 = 1 by omega,
          show (i + 1 + 1) % 2 = 0 by omega]
        decide
      · rw [show (i - 1 + 1) % 2 = 1 by omega, show (i + 1) % 2 = 0 by omega,
          show (i + 1 + 1) % 2 = 1 by omega]
        decide

end Rule30Equivalents.PeriodicPoints
