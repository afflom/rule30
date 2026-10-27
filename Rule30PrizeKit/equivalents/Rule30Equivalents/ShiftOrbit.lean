module

public import Rule30Equivalents.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Problem 1 as a statement about shifts and factor complexity

For a sequence `b : ℕ → Bool`, the `n`-th shift is `fun t => b (n + t)`, and the factors of length
`n` are the words `b i, b (i + 1), …, b (i + n - 1)` for `i : ℕ`. The factor complexity `p(n)` is
the number of distinct factors of length `n`.

## Statements

* `eventuallyPeriodic_iff_finite_shifts`: `b` is eventually periodic iff it has only finitely many
  distinct shifts, i.e. its orbit under the shift map is finite. So
  `problem1_iff_infinite_shifts`: **Problem 1 holds iff the center column has infinitely many
  distinct shifts**, and `problem1_iff_injective_shifts`: iff its shifts are pairwise distinct.
* `problem1_iff_not_preperiodic`: the same in the vocabulary of `Mathlib.Dynamics`: **Problem 1
  holds iff the center column is not a preperiodic point of the shift map** `shift`, i.e. no
  iterate `shift^[m] c` lies in `Function.periodicPts shift`.
* `eventuallyPeriodic_iff_exists_ncard_factors_le` (**Morse–Hedlund**): `b` is eventually periodic
  iff `p(n) ≤ n` for some `n`. So `problem1_iff_ncard_factors`: **Problem 1 holds iff the center
  column has at least `n + 1` distinct factors of every length `n`.**
* Two further forms of the same theorem: `b` is eventually periodic iff `p(n + 1) ≤ p(n)` for some
  `n`, and iff `p` is bounded. So Problem 1 holds iff `p` is strictly increasing
  (`problem1_iff_ncard_factors_lt_succ`, `problem1_iff_strictMono_ncard_factors`), and iff `p` is
  unbounded (`problem1_iff_ncard_factors_unbounded`).

## Proof

* Shifts. If `b (t + P) = b t` for `t ≥ T`, every shift equals one of the first `T + P` shifts. If
  only finitely many shifts exist, two of them coincide by pigeonhole, say the `n`-th and the
  `m`-th with `n < m`, and then `b` has period `m - n` from time `n` on. The `m`-th iterate of the
  shift map is the `m`-th shift (`shift_iterate`), so "`shift^[m] b` is periodic with period `P`"
  says exactly that the `m`-th and `(m + P)`-th shifts coincide.
* Morse–Hedlund, easy direction: if `b` has transient `T` and period `P`, every factor occurs at a
  position below `T + P`, so `p(n) ≤ T + P` for every `n`, in particular for `n = T + P`.
* Morse–Hedlund, hard direction. Deleting the last letter maps the factors of length `n + 1` onto
  those of length `n`, so `p` is monotone, and `p(0) ≥ 1`. If `p` were strictly increasing,
  `p(n) ≥ n + 1` for all `n`; so `p(n) ≤ n` forces `p(m + 1) = p(m)` for some `m`. Then deleting the
  last letter is injective on the factors of length `m + 1`: every factor of length `m` has a
  unique right extension, so the letter `b (i + m)` is a function of the window
  `b i, …, b (i + m - 1)`. By pigeonhole two windows of length `m` coincide, at positions
  `i < i'`, and then by strong induction `b (i + k) = b (i' + k)` for every `k`, so `b` is
  eventually periodic. The case `m = 0`, a constant sequence, needs no separate treatment.

## Sources

* M. Morse and G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. 60 (1938) 815–866,
  Theorems 7.3–7.4: a two-sided sequence is periodic iff `p(n + 1) = p(n)` for some `n`, iff
  `p(n) ≤ n` for some `n`.
* E. M. Coven and G. A. Hedlund, *Sequences with minimal block growth*, Math. Systems Theory 7
  (1973) 138–153: the one-sided form used here, with "eventually periodic".
* The finite-orbit form is the elementary fact that a point of the shift is preperiodic iff its
  forward orbit is finite (pigeonhole).
-/

@[expose] public section

namespace Rule30Equivalents
namespace ShiftOrbit

open Ruliology.CellularAutomata

/-! ### Shifts -/

/-- If `b` has transient `T` and period `P`, every shift of `b` equals a shift by less than
`T + P`. -/
theorem exists_lt_shift_eq {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (h : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) : ∃ m < T + P, ∀ t, b (n + t) = b (m + t) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < T + P
    · exact ⟨n, hn, fun _ => rfl⟩
    · obtain ⟨m, hm, hm'⟩ := ih (n - P) (by omega)
      refine ⟨m, hm, fun t => ?_⟩
      rw [← hm' t]
      have := h (n - P + t) (by omega)
      rwa [show n - P + t + P = n + t by omega] at this

/-- Two equal shifts, by `n < m`, make `b` eventually periodic with period `m - n`. -/
theorem eventuallyPeriodic_of_shift_eq {b : ℕ → Bool} {n m : ℕ} (hnm : n < m)
    (h : ∀ t, b (n + t) = b (m + t)) : EventuallyPeriodic b :=
  ⟨n, m - n, by omega, fun t ht => by
    have := h (t - n)
    rw [show n + (t - n) = t by omega, show m + (t - n) = t + (m - n) by omega] at this
    exact this.symm⟩

/-- **Finite shift orbit**: `b` is eventually periodic iff it has finitely many distinct shifts. -/
theorem eventuallyPeriodic_iff_finite_shifts (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ (Set.range (fun n : ℕ => fun t => b (n + t))).Finite := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ((Finset.range (T + P)).finite_toSet.image (fun n : ℕ => fun t => b (n + t))).subset ?_
    rintro _ ⟨n, rfl⟩
    obtain ⟨m, hm, hm'⟩ := exists_lt_shift_eq hP h n
    exact ⟨m, Finset.mem_coe.2 (Finset.mem_range.2 hm), funext fun t => (hm' t).symm⟩
  · intro hfin
    obtain ⟨n, m, hnm, h⟩ := hfin.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => fun t => b (n + t)) (fun n => Set.mem_range_self n)
    exact eventuallyPeriodic_of_shift_eq hnm fun t => congrFun h t

/-- `b` is eventually periodic iff two of its shifts coincide. -/
theorem eventuallyPeriodic_iff_not_injective_shifts (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ¬ Function.Injective (fun n : ℕ => fun t => b (n + t)) := by
  constructor
  · rintro ⟨T, P, hP, h⟩ hinj
    have := @hinj T (T + P) (funext fun t => by
      show b (T + t) = b (T + P + t)
      rw [show T + P + t = T + t + P by omega, h (T + t) (by omega)])
    omega
  · intro hinj
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨n, m, hnm, hne⟩ := hinj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact eventuallyPeriodic_of_shift_eq h fun t => congrFun hnm t
    · exact eventuallyPeriodic_of_shift_eq h fun t => (congrFun hnm t).symm

/-- The one-sided shift map on `ℕ → Bool`: `shift x t = x (t + 1)`. -/
def shift (x : ℕ → Bool) : ℕ → Bool := fun t => x (t + 1)

/-- The `n`-th iterate of the shift map is the `n`-th shift. -/
theorem shift_iterate (x : ℕ → Bool) (n : ℕ) : shift^[n] x = fun t => x (n + t) := by
  induction n generalizing x with
  | zero => funext t; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    funext t
    show x (n + t + 1) = x (n + 1 + t)
    rw [Nat.add_right_comm]

/-- **Preperiodic point**: `b` is eventually periodic iff some iterate of the shift map sends it
to a periodic point of the shift map. -/
theorem eventuallyPeriodic_iff_exists_iterate_mem_periodicPts (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ m, shift^[m] b ∈ Function.periodicPts shift := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, Function.mk_mem_periodicPts hP ?_⟩
    show shift^[P] (shift^[T] b) = shift^[T] b
    rw [← Function.iterate_add_apply, shift_iterate, shift_iterate]
    funext t
    rw [show P + T + t = T + t + P by omega, h (T + t) (by omega)]
  · rintro ⟨m, hm⟩
    obtain ⟨n, hn, hper⟩ := Function.mem_periodicPts.1 hm
    have hnm : shift^[n + m] b = shift^[m] b := by
      rw [Function.iterate_add_apply]
      exact hper
    rw [shift_iterate, shift_iterate] at hnm
    exact eventuallyPeriodic_of_shift_eq (show m < n + m by omega) fun t => (congrFun hnm t).symm

/-- **Problem 1 as an infinite shift orbit**: the center column has infinitely many distinct
shifts. -/
theorem problem1_iff_infinite_shifts :
    Rule30Prize.Problem1 ↔ (Set.range (fun n : ℕ => fun t => c (n + t))).Infinite :=
  (eventuallyPeriodic_iff_finite_shifts c).not

/-- **Problem 1 as injectivity of the shift orbit**: the shifts of the center column are pairwise
distinct. -/
theorem problem1_iff_injective_shifts :
    Rule30Prize.Problem1 ↔ Function.Injective (fun n : ℕ => fun t => c (n + t)) :=
  (eventuallyPeriodic_iff_not_injective_shifts c).not.trans not_not

/-- **Problem 1 in dynamical language**: the center column is not a preperiodic point of the shift
map; no iterate of the shift sends it to a periodic point. -/
theorem problem1_iff_not_preperiodic :
    Rule30Prize.Problem1 ↔ ∀ m, shift^[m] c ∉ Function.periodicPts shift :=
  (eventuallyPeriodic_iff_exists_iterate_mem_periodicPts c).not.trans not_exists

/-! ### Factor complexity -/

/-- The factors of length `n` of `b`: the words `b i, b (i + 1), …, b (i + n - 1)`, `i : ℕ`. -/
def factors (b : ℕ → Bool) (n : ℕ) : Set (Fin n → Bool) :=
  Set.range (fun i : ℕ => fun j : Fin n => b (i + j))

theorem factors_finite (b : ℕ → Bool) (n : ℕ) : (factors b n).Finite := Set.toFinite _

theorem factors_nonempty (b : ℕ → Bool) (n : ℕ) : (factors b n).Nonempty := ⟨_, 0, rfl⟩

/-- `p(n) ≥ 1`. -/
theorem one_le_ncard_factors (b : ℕ → Bool) (n : ℕ) : 1 ≤ (factors b n).ncard :=
  (Set.ncard_pos (factors_finite b n)).2 (factors_nonempty b n)

/-- Deleting the last letter maps the factors of length `n + 1` onto those of length `n`. -/
theorem image_init_factors (b : ℕ → Bool) (n : ℕ) :
    (fun w : Fin (n + 1) → Bool => fun j : Fin n => w (Fin.castSucc j)) '' factors b (n + 1) =
      factors b n := by
  ext u
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

/-- `p` is monotone: `p(n) ≤ p(n + 1)`. -/
theorem ncard_factors_le_succ (b : ℕ → Bool) (n : ℕ) :
    (factors b n).ncard ≤ (factors b (n + 1)).ncard := by
  rw [← image_init_factors b n]
  exact Set.ncard_image_le (factors_finite b (n + 1))

/-- If `p(n + 1) ≤ p(n)`, every factor of length `n` has a unique right extension: the letter after
a window of length `n` is a function of the window. -/
theorem unique_right_extension {b : ℕ → Bool} {n : ℕ}
    (h : (factors b (n + 1)).ncard ≤ (factors b n).ncard) {i i' : ℕ}
    (hw : ∀ j < n, b (i + j) = b (i' + j)) : b (i + n) = b (i' + n) := by
  have hinj : Set.InjOn (fun w : Fin (n + 1) → Bool => fun j : Fin n => w (Fin.castSucc j))
      (factors b (n + 1)) := by
    apply Set.injOn_of_ncard_image_eq _ (factors_finite b (n + 1))
    rw [image_init_factors]
    exact le_antisymm (ncard_factors_le_succ b n) h
  have hext := @hinj (fun j => b (i + j)) ⟨i, rfl⟩ (fun j => b (i' + j)) ⟨i', rfl⟩
    (funext fun j => hw j j.isLt)
  simpa using congrFun hext (Fin.last n)

/-- If `p(n + 1) ≤ p(n)` for some `n`, then `b` is eventually periodic. -/
theorem eventuallyPeriodic_of_ncard_factors_succ_le {b : ℕ → Bool} {n : ℕ}
    (h : (factors b (n + 1)).ncard ≤ (factors b n).ncard) : EventuallyPeriodic b := by
  obtain ⟨i, i', hii', hw⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => fun j : Fin n => b (i + j)) (fun _ => Set.mem_univ _)
  have key : ∀ k, b (i + k) = b (i' + k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < n
      · exact congrFun hw ⟨k, hk⟩
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + n := ⟨k - n, by omega⟩
        have := unique_right_extension h (i := i + k') (i' := i' + k') fun j hj => by
          rw [Nat.add_assoc, Nat.add_assoc]
          exact ih (k' + j) (by omega)
        rwa [Nat.add_assoc, Nat.add_assoc] at this
  exact eventuallyPeriodic_of_shift_eq hii' key

/-- If `b` has transient `T` and period `P`, then `p(n) ≤ T + P` for every `n`. -/
theorem ncard_factors_le_of_periodic {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (h : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) : (factors b n).ncard ≤ T + P := by
  have hsub : factors b n ⊆
      ((Finset.range (T + P)).image (fun i : ℕ => fun j : Fin n => b (i + j)) :
        Set (Fin n → Bool)) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm, hm'⟩ := exists_lt_shift_eq hP h i
    rw [Finset.coe_image]
    exact ⟨m, Finset.mem_coe.2 (Finset.mem_range.2 hm), funext fun j => (hm' j).symm⟩
  calc (factors b n).ncard
      ≤ (((Finset.range (T + P)).image (fun i : ℕ => fun j : Fin n => b (i + j)) :
          Set (Fin n → Bool))).ncard := Set.ncard_le_ncard hsub
    _ = ((Finset.range (T + P)).image (fun i : ℕ => fun j : Fin n => b (i + j))).card :=
          Set.ncard_coe_finset _
    _ ≤ (Finset.range (T + P)).card := Finset.card_image_le
    _ = T + P := Finset.card_range _

/-- If `p` is strictly increasing then `p(n) ≥ n + 1` for all `n`. -/
theorem succ_le_ncard_factors_of_strictMono {b : ℕ → Bool}
    (hlt : ∀ m, (factors b m).ncard < (factors b (m + 1)).ncard) (n : ℕ) :
    n + 1 ≤ (factors b n).ncard := by
  induction n with
  | zero => exact one_le_ncard_factors b 0
  | succ n ih => have := hlt n; omega

/-- `b` is eventually periodic iff `p(n + 1) ≤ p(n)` for some `n`, i.e. iff `p` is not strictly
increasing. -/
theorem eventuallyPeriodic_iff_exists_ncard_factors_succ_le (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ n, (factors b (n + 1)).ncard ≤ (factors b n).ncard := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    by_contra hne
    push Not at hne
    have h1 := succ_le_ncard_factors_of_strictMono hne (T + P)
    have h2 := ncard_factors_le_of_periodic hP h (T + P)
    omega
  · rintro ⟨n, hn⟩
    exact eventuallyPeriodic_of_ncard_factors_succ_le hn

/-- **Morse–Hedlund**: `b` is eventually periodic iff it has at most `n` distinct factors of some
length `n`. -/
theorem eventuallyPeriodic_iff_exists_ncard_factors_le (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ n, (factors b n).ncard ≤ n := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T + P, ncard_factors_le_of_periodic hP h (T + P)⟩
  · rintro ⟨n, hn⟩
    by_contra hnp
    have hlt : ∀ m, (factors b m).ncard < (factors b (m + 1)).ncard := fun m =>
      lt_of_not_ge fun hle => hnp (eventuallyPeriodic_of_ncard_factors_succ_le hle)
    have := succ_le_ncard_factors_of_strictMono hlt n
    omega

/-- `b` is eventually periodic iff its factor complexity is bounded. -/
theorem eventuallyPeriodic_iff_bounded_ncard_factors (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ C, ∀ n, (factors b n).ncard ≤ C := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T + P, ncard_factors_le_of_periodic hP h⟩
  · rintro ⟨C, hC⟩
    exact (eventuallyPeriodic_iff_exists_ncard_factors_le b).2 ⟨C, hC C⟩

/-- **Problem 1 via Morse–Hedlund**: the center column has at least `n + 1` distinct factors of
every length `n`. -/
theorem problem1_iff_ncard_factors :
    Rule30Prize.Problem1 ↔ ∀ n, n + 1 ≤ (factors c n).ncard := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_ncard_factors_le]
  push Not
  rfl

/-- **Problem 1 as strictly increasing complexity**: the center column has strictly more factors
of length `n + 1` than of length `n`, for every `n`. -/
theorem problem1_iff_ncard_factors_lt_succ :
    Rule30Prize.Problem1 ↔ ∀ n, (factors c n).ncard < (factors c (n + 1)).ncard := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_ncard_factors_succ_le]
  push Not
  rfl

/-- The same as `problem1_iff_ncard_factors_lt_succ`, with `StrictMono`. -/
theorem problem1_iff_strictMono_ncard_factors :
    Rule30Prize.Problem1 ↔ StrictMono (fun n => (factors c n).ncard) :=
  problem1_iff_ncard_factors_lt_succ.trans
    ⟨strictMono_nat_of_lt_succ, fun h n => h (Nat.lt_succ_self n)⟩

/-- **Problem 1 as unbounded complexity**: the center column has arbitrarily many distinct factors
of a single length. -/
theorem problem1_iff_ncard_factors_unbounded :
    Rule30Prize.Problem1 ↔ ∀ C, ∃ n, C < (factors c n).ncard := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_bounded_ncard_factors]
  push Not
  rfl

end ShiftOrbit
end Rule30Equivalents
