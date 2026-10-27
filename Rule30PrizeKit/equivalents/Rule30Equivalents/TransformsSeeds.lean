module

public import Rule30Equivalents.ShiftOrbit
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Problem 1 under simple transforms and decimations, its normal forms, and other seeds

Bookkeeping forms of Problem 1: transforms of the center column that keep the answer, decimations,
logical normal forms, the two published formal statements, and a family of initial rows with the
same center column. Where it makes sense, the statement is proved for every `b : ℕ → Bool` and
then specialized to the center column `c`.

## Statements

**Simple transforms.**
* Changing finitely many terms does not matter: two sequences that agree from some time on are
  both eventually periodic or both not (`eventuallyPeriodic_congr_of_eventually_eq`,
  `problem1_iff_of_eventually_eq`).
* **Index shift.** For every `k`, Problem 1 holds iff `t ↦ c (t + k)` is not eventually periodic
  (`problem1_iff_shifted`). Shifting the other way, it holds iff `w 0, …, w (k - 1), c 0, c 1, …`
  is not eventually periodic, for any `k` and any `w` (`problem1_iff_prepend`).
* **XOR derivative.** Problem 1 holds iff `t ↦ c t xor c (t + 1)` is not eventually periodic
  (`problem1_iff_xor_derivative`). This is OEIS A327974 shifted by one. If the derivative of `b` has
  period `P` from `T`, then `b` has period `2P` from `T` (`periodic_two_mul_of_xorDeriv`).
* **Running parity.** Problem 1 holds iff the prefix XOR `t ↦ c 0 xor c 1 xor ⋯ xor c t` (OEIS
  A327982 mod 2) is not eventually periodic (`problem1_iff_running_parity`, stated with
  `List.foldl`). Equivalently, the parity of `Rule30Prize.blackCount n`, the number of black cells
  among `c 0, …, c (n - 1)` (Problem 2's counting function), is not eventually periodic
  (`problem1_iff_blackCount_parity`).
* **Right-permutive sliding block codes.** Let `f (w, x)` be a local rule on a window
  `w = (b t, …, b (t + r - 1))` followed by one more letter `x = b (t + r)`, with
  `f w true ≠ f w false` for every `w`. Problem 1 holds iff the coded sequence
  `t ↦ f (c t, …, c (t + r - 1)) (c (t + r))` is not eventually periodic
  (`problem1_iff_right_permutive_code`). The XOR derivative, the index shift and the complement are
  the special cases `xorDeriv_eq_slidingCode`, `shift_eq_slidingCode` and
  `complement_eq_slidingCode`. The complement form itself is `Symmetry.problem1_iff_complement`.

**Decimations and residue classes.**
* For every `k > 0`, Problem 1 holds iff some decimation `n ↦ c (k n + r)` with `r < k` is not
  eventually periodic (`problem1_iff_decimation`). For `k = 2`: iff the center column at even times
  or the center column at odd times is not eventually periodic (`problem1_iff_even_or_odd`).
* For `P > 0`, `b` has an eventual period `P` iff every residue class `k ↦ b (r + k P)`, `r < P`, is
  eventually constant (`eventually_period_iff_classes_const`). So Problem 1 holds iff for every
  `P > 0` some residue class modulo `P` of the center column is not eventually constant
  (`problem1_iff_nonconstant_class`). The case `P = 1` is a theorem (`nonconstant_class_one`):
  the center column is not eventually constant (`Rule30Prize.center_not_eventually_constant`).

**Normal forms.**
* **`Π⁰₂` form.** Problem 1 holds iff for every `T` and every `P ≥ 1` some `t ≥ T` has
  `c (t + P) ≠ c t` (`problem1_iff_pi2`). Each instance `(T, P)` is a finite search: it holds iff
  the Boolean test `refutes T P m`, an executable Lean function that checks the times `t < m`,
  succeeds for some `m` (`problem1_iff_forall_exists_refutes`). The condition `P ≥ 1` is needed:
  with `P = 0` allowed the right side is false (`not_forall_pi2_without_pos`). That `c` is
  primitive recursive in the sense of Mathlib's `Primrec`, which would place the sentence in `Π⁰₂`
  formally, is not proved here.
* **Periods from a cofinal family.** If all `Q n > 0` and every `P > 0` divides some `Q n`, Problem
  1 holds iff no `Q n` is an eventual period of `c` (`problem1_iff_cofinal_periods`). For the
  factorials: Problem 1 holds iff no `(k + 1)!` is an eventual period of `c`
  (`problem1_iff_factorial_periods`).

**The published formal statements.**
* **formal-conjectures.** `FormalConjectures.step`, `FormalConjectures.state` and
  `FormalConjectures.centerColumn` copy the definitions of `FormalConjectures/Other/Rule30.lean`
  verbatim, and `problem1_iff_fc` proves Problem 1 equivalent to its
  `Rule30.centerColumn_not_eventually_periodic`, verbatim:
  `¬ ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t → centerColumn (t + p) = centerColumn t`.
  Its `state t` is the row `Rule30Jen.cell t` (`FormalConjectures.state_eq_cell`). The
  file's test `centerColumn_prefix` is re-proved by `decide`.
* **Wolfram (2019).** `NotExists[{p, i}, ForAll[t, t > i, c[t + p] == c[t]]]` with
  `c[t_] := CellularAutomaton[30, {{1}, 0}, {t, {{0}}}]`. Read as intended, with a period `p ≥ 1`
  and `c[t]` the value at step `t`, it is Problem 1 (`problem1_iff_wolfram`; with `Last[c[t]]`,
  `problem1_iff_wolfram_last`). Read literally it is degenerate. `c[t]` is the list
  `{c(0), …, c(t)}` of `t + 1` values (`wolframList`), so with `p = 0` allowed the formula is false
  (`wolfram_literal_iff_false`), and with `p ≥ 1` it is true, because the two lists have different
  lengths (`wolfram_literal_pos_iff_true`).

**Stripe seeds.** Let `s_n` (`stripeSeed n`) be black exactly at the even positions of `[0, n)` and
at `n`. Read from position `0`, `s_0, s_1, s_2, … = 1, 11, 101, 1011, 10101, …`
(`stripeSeed_pictures`, by `decide`), and `s_0` is the single black cell (`stripeSeed_zero`).
Rule 30 from `s_n` draws the single-seed pattern left of the diagonal `p = t`, the stripe (black
at even `p`) on `[t, t + n)`, one black cell at `t + n`, and white beyond (`evol_stripeSeed`). So
its center column is exactly `c` (`stripeSeed_center`), and for every `n`, Problem 1 holds iff the
center column of rule 30 from `s_n` is not eventually periodic (`problem1_iff_stripeSeed`).

## Proofs

* Shifts and finite changes only move the transient. Prepending `k` letters is undone by the shift
  by `k`.
* XOR derivative. If the derivative has period `P` from `T`, the difference
  `e t = b (t + P) xor b t` is constant from `T` on, and two periods cancel it:
  `b (t + 2P) = b t xor e t xor e (t + P) = b t`.
* Running parity. Its XOR derivative is `t ↦ b (t + 1)`. The parity of `blackCount n` changes at
  `n` exactly when `c n` is black, so its XOR derivative is `c`. In both cases eventual
  periodicity transfers along the derivative (`eventuallyPeriodic_iff_of_xorDeriv_eq`).
* Right-permutive codes. A sliding block code of an eventually periodic sequence is eventually
  periodic. Conversely, let the output `y` have period `P` from `T`. The windows
  `(b t, …, b (t + r - 1))` at the times `t = T + nP` lie in a finite set, so two of them coincide,
  at `n₁ < n₂`. Since `f w` is injective, `b (t + r)` is determined by the window at `t` and by
  `y t`, and `y` agrees at `T + n₁P + j` and `T + n₂P + j`. By strong induction on `j`,
  `b (T + n₁P + j) = b (T + n₂P + j)` for every `j`.
* Decimations. A period `P` of `b` from `T` is a period of each decimation from `T`, since
  `k n + r ≥ n`. Conversely, induction over the residues gives a common transient `T` and a common
  period `P` (a product of the individual periods), and then `b` has period `kP` from `kT`: write
  `t = k (t / k) + t % k`.
* Residue classes. An eventual period `P` makes every class `k ↦ b (r + kP)` constant from the
  transient on. Conversely, one threshold `K` works for all `P` classes (induction over the
  classes), and then `b (t + P) = b t` for `t ≥ KP`.
* Normal forms. The `Π⁰₂` form is the definition with the negation pushed in. A period `P` divides
  `P! = ((P - 1) + 1)!`, and any multiple of an eventual period is one.
* formal-conjectures. `state t = cell t` by induction on `t`, each step by `rfl`. After that the
  two statements differ only in the order of the quantifiers. Wolfram: `t > i` iff `t ≥ i + 1`.
* Stripe seeds. Induction on `t` with the explicit pattern. Rule 30 is `l xor (c || r)`, and the
  stripe `1010…1` satisfies `x p || x (p + 1) = true` at each of its cells (the `or` latch,
  `stripePattern_or`). Only the two cells next to the diagonal need care. The cell at `t` sees
  `c || r = true` in both patterns: in the single-seed pattern `t` is the right edge (`cell_diag`),
  and in the stripe pattern the latch holds. So it becomes `!cell t (t - 1)` in both. The cell at
  `t - 1` also sees `c || r = true` in both: its own cell is black when `t` is odd (the diagonal
  next to the right edge alternates, `cell_subdiag`, from `Rule30Diagonals.R_one_succ`), and when
  `t` is even the stripe is black at `t`, as is the right edge of the single seed. Cells further
  left see only the single-seed pattern. Inside the stripe each cell becomes `!x (p - 1) = x p`,
  so the stripe stays in place; the single-seed pattern overwrites its left end while the black
  cell at its right end moves right by one cell per step.

## Checks

* Stripe seeds, numerically (exact integer arithmetic). For `n ≤ 64` and `t ≤ 2000`,
  the row from `s_n` equals the claimed pattern, so its center column is `c`. Among all `8191`
  nonzero seeds supported in `[0, 13)`, exactly `s_0, …, s_12` reproduce `c` for `t ≤ 300`. For
  example `111` first differs at `t = 3`, `1001` at `t = 7` and `10111` at `t = 11`.
* Wolfram Language: `c[5]` is `{1, 1, 0, 1, 1, 1}` (six values), `Last[c[t]]` for
  `t = 0, …, 11` is `1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0` (OEIS A051023), and for `1 ≤ t ≤ 20`
  the literal test `c[t + p] == c[t]` holds with `p = 0` and fails for every `1 ≤ p ≤ 5`.

## Sources

* google-deepmind/formal-conjectures, `FormalConjectures/Other/Rule30.lean` at commit `7db2ea3`
  (2026-10-14, PR #6762), Apache License 2.0. The definitions `step`, `state` and `centerColumn`,
  the test `centerColumn_prefix` and the statement `centerColumn_not_eventually_periodic` are
  copied from it. The three earlier versions (PR #4377 of 2026-09-07, #4688, #6740) wrapped the
  same statement in formal-conjectures' `answer(…) ↔ …` question form; PR #6762 removed it.
* S. Wolfram, *Announcing the Rule 30 Prizes* (2019), section "Formal Statements of the Problems",
  <https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/>.
* OEIS: A051023 (the center column), A327974 (`a(n) = A051023(n) xor A051023(n - 1)`, offset 1,
  so `a(t + 1) = c t xor c (t + 1)`), A327982 (the partial sums of A051023; their parity is the
  running parity).
* The facts about shifts, derivatives, sliding block codes, decimations, residue classes, normal
  forms and cofinal periods are elementary. The proofs here are self-contained, and we cite no
  source for them.
* We know of no literature on the stripe seeds.
-/

@[expose] public section

namespace Rule30Equivalents
namespace TransformsSeeds

open Ruliology.CellularAutomata

/-! ### Changing finitely many terms, and index shifts -/

/-- Changing finitely many terms keeps a sequence eventually periodic. -/
theorem eventuallyPeriodic_of_eventually_eq {b b' : ℕ → Bool} {N : ℕ}
    (h : ∀ t, N ≤ t → b t = b' t) (hb : EventuallyPeriodic b) : EventuallyPeriodic b' := by
  obtain ⟨T, P, hP, hper⟩ := hb
  refine ⟨T + N, P, hP, fun t ht => ?_⟩
  rw [← h (t + P) (by omega), ← h t (by omega)]
  exact hper t (by omega)

/-- **Finitely many changes.** Two sequences that agree from some time on are both eventually
periodic or both not. -/
theorem eventuallyPeriodic_congr_of_eventually_eq {b b' : ℕ → Bool} {N : ℕ}
    (h : ∀ t, N ≤ t → b t = b' t) : EventuallyPeriodic b ↔ EventuallyPeriodic b' :=
  ⟨eventuallyPeriodic_of_eventually_eq h,
    eventuallyPeriodic_of_eventually_eq fun t ht => (h t ht).symm⟩

/-- Problem 1 for any sequence that agrees with the center column from some time on. -/
theorem problem1_iff_of_eventually_eq {b : ℕ → Bool} {N : ℕ} (h : ∀ t, N ≤ t → b t = c t) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic b :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_congr_of_eventually_eq h).symm)

/-- **Index shift.** Dropping the first `k` terms does not change eventual periodicity. -/
theorem eventuallyPeriodic_shift_iff (b : ℕ → Bool) (k : ℕ) :
    EventuallyPeriodic (fun t => b (t + k)) ↔ EventuallyPeriodic b := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T + k, P, hP, fun t ht => ?_⟩
    have e : b (t - k + P + k) = b (t - k + k) := h (t - k) (by omega)
    rwa [show t - k + P + k = t + P by omega, show t - k + k = t by omega] at e
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, P, hP, fun t ht => ?_⟩
    show b (t + P + k) = b (t + k)
    rw [show t + P + k = t + k + P by omega]
    exact h (t + k) (by omega)

/-- **Prepending `k` arbitrary terms** (an index shift the other way) does not change eventual
periodicity. -/
theorem eventuallyPeriodic_prepend_iff (w b : ℕ → Bool) (k : ℕ) :
    EventuallyPeriodic (fun t => if t < k then w t else b (t - k)) ↔ EventuallyPeriodic b := by
  refine (eventuallyPeriodic_shift_iff _ k).symm.trans
    (eventuallyPeriodic_congr_of_eventually_eq (N := 0) fun t _ => ?_)
  show (if t + k < k then w (t + k) else b (t + k - k)) = b t
  rw [ite_eq_right (by omega), Nat.add_sub_cancel]

/-- **Problem 1 after an index shift**: for every `k`, Problem 1 holds iff the shifted center
column `t ↦ c (t + k)` is not eventually periodic. -/
theorem problem1_iff_shifted (k : ℕ) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => c (t + k)) :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_shift_iff c k).symm)

/-- **Problem 1 after prepending a finite word**: for every `k` and `w`, Problem 1 holds iff the
sequence `w 0, …, w (k - 1), c 0, c 1, …` is not eventually periodic. -/
theorem problem1_iff_prepend (w : ℕ → Bool) (k : ℕ) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => if t < k then w t else c (t - k)) :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_prepend_iff w c k).symm)

/-! ### The XOR derivative and the running parity -/

/-- The XOR derivative `t ↦ b t xor b (t + 1)`: `true` exactly where the color changes. -/
def xorDeriv (b : ℕ → Bool) (t : ℕ) : Bool := xor (b t) (b (t + 1))

/-- If `b` has period `P` from `T`, so does its XOR derivative. -/
theorem xorDeriv_periodic {b : ℕ → Bool} {T P : ℕ} (h : ∀ t, T ≤ t → b (t + P) = b t) :
    ∀ t, T ≤ t → xorDeriv b (t + P) = xorDeriv b t := by
  intro t ht
  show xor (b (t + P)) (b (t + P + 1)) = xor (b t) (b (t + 1))
  rw [show t + P + 1 = t + 1 + P by omega, h t ht, h (t + 1) (by omega)]

/-- **Integrating a period.** If the XOR derivative of `b` has period `P` from `T`, then `b` has
period `2P` from `T`. The difference `b (t + P) xor b t` is constant from `T` on, so it cancels
over two periods. -/
theorem periodic_two_mul_of_xorDeriv {b : ℕ → Bool} {T P : ℕ}
    (h : ∀ t, T ≤ t → xorDeriv b (t + P) = xorDeriv b t) :
    ∀ t, T ≤ t → b (t + 2 * P) = b t := by
  have he : ∀ d, xor (b (T + d + P)) (b (T + d)) = xor (b (T + P)) (b T) := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have h1 : xor (b (T + d + P)) (b (T + d + P + 1)) = xor (b (T + d)) (b (T + d + 1)) :=
        h (T + d) (by omega)
      rw [← ih, show T + (d + 1) + P = T + d + P + 1 by omega,
        show T + (d + 1) = T + d + 1 by omega]
      revert h1
      cases b (T + d + P) <;> cases b (T + d + P + 1) <;> cases b (T + d) <;>
        cases b (T + d + 1) <;> decide
  intro t ht
  have e1 := he (t - T)
  have e2 := he (t + P - T)
  rw [show T + (t - T) = t by omega] at e1
  rw [show T + (t + P - T) = t + P by omega, ← e1] at e2
  rw [show t + 2 * P = t + P + P by omega]
  revert e2
  cases b (t + P + P) <;> cases b (t + P) <;> cases b t <;> decide

/-- **The XOR derivative.** `b` is eventually periodic iff `t ↦ b t xor b (t + 1)` is. -/
theorem eventuallyPeriodic_xorDeriv_iff (b : ℕ → Bool) :
    EventuallyPeriodic (xorDeriv b) ↔ EventuallyPeriodic b := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, 2 * P, by omega, periodic_two_mul_of_xorDeriv h⟩
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, xorDeriv_periodic h⟩

/-- **XOR antiderivatives.** If `a t xor a (t + 1) = b t` for all `t`, then `a` is eventually
periodic iff `b` is. -/
theorem eventuallyPeriodic_iff_of_xorDeriv_eq {a b : ℕ → Bool} (h : ∀ t, xorDeriv a t = b t) :
    EventuallyPeriodic a ↔ EventuallyPeriodic b := by
  rw [← eventuallyPeriodic_xorDeriv_iff a, show xorDeriv a = b from funext h]

/-- **Problem 1 for the XOR derivative**: Problem 1 holds iff `t ↦ c t xor c (t + 1)` (OEIS
A327974, shifted by one) is not eventually periodic. -/
theorem problem1_iff_xor_derivative :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => xor (c t) (c (t + 1))) :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_xorDeriv_iff c).symm)

/-- The running parity `b 0 xor b 1 xor ⋯ xor b t`. -/
def runningParity (b : ℕ → Bool) : ℕ → Bool
  | 0 => b 0
  | t + 1 => xor (runningParity b t) (b (t + 1))

/-- The running parity is the left fold of `xor` over `b 0, …, b t`. -/
theorem runningParity_eq_foldl (b : ℕ → Bool) (t : ℕ) :
    runningParity b t = ((List.range (t + 1)).map b).foldl xor false := by
  induction t with
  | zero => simp [runningParity]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ← ih]
    rfl

/-- The XOR derivative of the running parity of `b` is `b` shifted by one. -/
theorem xorDeriv_runningParity (b : ℕ → Bool) (t : ℕ) :
    xorDeriv (runningParity b) t = b (t + 1) := by
  show xor (runningParity b t) (xor (runningParity b t) (b (t + 1))) = b (t + 1)
  cases runningParity b t <;> cases b (t + 1) <;> rfl

/-- **The running parity.** `b` is eventually periodic iff `t ↦ b 0 xor ⋯ xor b t` is. -/
theorem eventuallyPeriodic_runningParity_iff (b : ℕ → Bool) :
    EventuallyPeriodic (runningParity b) ↔ EventuallyPeriodic b :=
  (eventuallyPeriodic_iff_of_xorDeriv_eq (xorDeriv_runningParity b)).trans
    (eventuallyPeriodic_shift_iff b 1)

/-- **Problem 1 for the running parity**: Problem 1 holds iff the prefix XOR
`t ↦ c 0 xor c 1 xor ⋯ xor c t` (OEIS A327982 mod 2) is not eventually periodic. -/
theorem problem1_iff_running_parity : Rule30Prize.Problem1 ↔
    ¬ EventuallyPeriodic (fun t => ((List.range (t + 1)).map c).foldl xor false) := by
  rw [show (fun t => ((List.range (t + 1)).map c).foldl xor false) = runningParity c from
    funext fun t => (runningParity_eq_foldl c t).symm]
  exact problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_runningParity_iff c).symm)

/-- One more cell: `blackCount (n + 1) = blackCount n + c n`. -/
theorem blackCount_succ (n : ℕ) :
    Rule30Prize.blackCount (n + 1) =
      Rule30Prize.blackCount n + (if Rule30Prize.center n then 1 else 0) := by
  simp only [Rule30Prize.blackCount, List.range_succ, List.filter_append, List.length_append]
  cases h : Rule30Prize.center n <;> simp [List.filter, h]

/-- The parity of `blackCount n`, the number of black cells among `c 0, …, c (n - 1)`, has XOR
derivative `c`. -/
theorem xorDeriv_blackCount_parity (n : ℕ) :
    xorDeriv (fun m => decide (Rule30Prize.blackCount m % 2 = 1)) n = c n := by
  show xor (decide (Rule30Prize.blackCount n % 2 = 1))
    (decide (Rule30Prize.blackCount (n + 1) % 2 = 1)) = Rule30Prize.center n
  rw [blackCount_succ]
  cases h : Rule30Prize.center n
  · simp
  · simp only [ite_true]
    by_cases hk : Rule30Prize.blackCount n % 2 = 1
    · rw [decide_eq_true hk, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false hk, decide_eq_true (by omega)]; rfl

/-- **Problem 1 for the parity of the black count**: Problem 1 holds iff the parity of
`Rule30Prize.blackCount n` (the counting function of Problem 2, here the exclusive running parity
`c 0 xor ⋯ xor c (n - 1)`) is not eventually periodic. -/
theorem problem1_iff_blackCount_parity : Rule30Prize.Problem1 ↔
    ¬ EventuallyPeriodic (fun n => decide (Rule30Prize.blackCount n % 2 = 1)) :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_iff_of_xorDeriv_eq xorDeriv_blackCount_parity).symm)

/-! ### Right-permutive sliding block codes -/

/-- The sliding block code with window length `r + 1` and local rule `f`:
`t ↦ f (b t, …, b (t + r - 1)) (b (t + r))`. Every sliding block code with window length `r + 1`
has this form. It is **right-permutive** if `f w` is a bijection of `Bool` for every `w`, that
is, `f w true ≠ f w false`. -/
def slidingCode (r : ℕ) (f : (Fin r → Bool) → Bool → Bool) (b : ℕ → Bool) (t : ℕ) : Bool :=
  f (fun i => b (t + (i : ℕ))) (b (t + r))

/-- Sliding block codes preserve eventual periodicity. -/
theorem slidingCode_eventuallyPeriodic {r : ℕ} {f : (Fin r → Bool) → Bool → Bool}
    {b : ℕ → Bool} (h : EventuallyPeriodic b) : EventuallyPeriodic (slidingCode r f b) := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T, P, hP, fun t ht => ?_⟩
  show f (fun i : Fin r => b (t + P + (i : ℕ))) (b (t + P + r)) =
    f (fun i : Fin r => b (t + (i : ℕ))) (b (t + r))
  have h1 : (fun i : Fin r => b (t + P + (i : ℕ))) = fun i : Fin r => b (t + (i : ℕ)) := by
    funext i
    rw [show t + P + (i : ℕ) = t + i + P by omega]
    exact hper _ (by omega)
  rw [h1, show t + P + r = t + r + P by omega, hper (t + r) (by omega)]

/-- **Right-permutive codes can be inverted forward.** If the code is right-permutive and its
output has period `P` from `T`, the input is eventually periodic. The windows of the last `r`
input letters at the times `T + nP` take finitely many values, so two of them coincide; from
there on the recurrence `b (t + r) = (f w)⁻¹ (y t)` repeats everything. -/
theorem eventuallyPeriodic_of_slidingCode {r : ℕ} {f : (Fin r → Bool) → Bool → Bool}
    (hf : ∀ w, f w true ≠ f w false) {b : ℕ → Bool}
    (h : EventuallyPeriodic (slidingCode r f b)) : EventuallyPeriodic b := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hinj : ∀ w x x', f w x = f w x' → x = x' := by
    intro w x x' e
    cases x <;> cases x'
    · rfl
    · exact absurd e.symm (hf w)
    · exact absurd e (hf w)
    · rfl
  obtain ⟨n₁, n₂, h12, hw⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => fun i : Fin r => b (T + n * P + i)) (fun _ => Set.mem_univ _)
  have hmul : n₁ * P + (n₂ - n₁) * P = n₂ * P := by
    rw [← Nat.add_mul, Nat.add_sub_of_le h12.le]
  -- the output agrees at the times `T + n₁ P + k` and `T + n₂ P + k`
  have hy : ∀ k, slidingCode r f b (T + n₁ * P + k) = slidingCode r f b (T + n₂ * P + k) := by
    intro k
    have e := Rule30Jen.periodic_mul hper (n₂ - n₁) (T + n₁ * P + k) (by omega)
    rw [show T + n₁ * P + k + (n₂ - n₁) * P = T + n₂ * P + k by omega] at e
    exact e.symm
  have key : ∀ k, b (T + n₁ * P + k) = b (T + n₂ * P + k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < r
      · exact congrFun hw ⟨k, hk⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + r := ⟨k - r, by omega⟩
        have e : f (fun i : Fin r => b (T + n₁ * P + j + (i : ℕ))) (b (T + n₁ * P + j + r)) =
            f (fun i : Fin r => b (T + n₂ * P + j + (i : ℕ))) (b (T + n₂ * P + j + r)) := hy j
        have hwin : (fun i : Fin r => b (T + n₁ * P + j + (i : ℕ))) =
            fun i : Fin r => b (T + n₂ * P + j + (i : ℕ)) := by
          funext i
          rw [Nat.add_assoc (T + n₁ * P), Nat.add_assoc (T + n₂ * P)]
          exact ih (j + i) (by omega)
        rw [hwin] at e
        rw [← Nat.add_assoc, ← Nat.add_assoc]
        exact hinj _ _ _ e
  have hlt : T + n₁ * P < T + n₂ * P := by
    have := Nat.mul_lt_mul_of_pos_right h12 hP
    omega
  exact ShiftOrbit.eventuallyPeriodic_of_shift_eq hlt key

/-- **Right-permutive sliding block codes**: for a right-permutive local rule `f`, the code
`slidingCode r f b` is eventually periodic iff `b` is. -/
theorem eventuallyPeriodic_slidingCode_iff {r : ℕ} {f : (Fin r → Bool) → Bool → Bool}
    (hf : ∀ w, f w true ≠ f w false) (b : ℕ → Bool) :
    EventuallyPeriodic (slidingCode r f b) ↔ EventuallyPeriodic b :=
  ⟨eventuallyPeriodic_of_slidingCode hf, slidingCode_eventuallyPeriodic⟩

/-- **Problem 1 for right-permutive codes**: for every right-permutive local rule `f`, Problem 1
holds iff the coded center column `t ↦ f (c t, …, c (t + r - 1)) (c (t + r))` is not eventually
periodic. -/
theorem problem1_iff_right_permutive_code {r : ℕ} {f : (Fin r → Bool) → Bool → Bool}
    (hf : ∀ w, f w true ≠ f w false) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (slidingCode r f c) :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_slidingCode_iff hf c).symm)

/-- The XOR derivative is the right-permutive code `f w x = w 0 xor x` with `r = 1`. -/
theorem xorDeriv_eq_slidingCode (b : ℕ → Bool) :
    xorDeriv b = slidingCode 1 (fun w x => xor (w 0) x) b := rfl

/-- The index shift by `k` is the right-permutive code `f w x = x` with `r = k`. -/
theorem shift_eq_slidingCode (b : ℕ → Bool) (k : ℕ) :
    (fun t => b (t + k)) = slidingCode k (fun _ x => x) b := rfl

/-- The complement is the right-permutive code `f w x = !x` with `r = 0`. -/
theorem complement_eq_slidingCode (b : ℕ → Bool) :
    (fun t => !b t) = slidingCode 0 (fun _ x => !x) b := rfl

/-! ### Decimations and residue classes -/

/-- A decimation `n ↦ b (k n + r)` (`k > 0`) of a sequence with period `P` from `T` has period
`P` from `T`. -/
theorem decimation_periodic {b : ℕ → Bool} {T P k : ℕ} (hk : 0 < k)
    (h : ∀ t, T ≤ t → b (t + P) = b t) (r : ℕ) :
    ∀ n, T ≤ n → b (k * (n + P) + r) = b (k * n + r) := by
  intro n hn
  have hkn : n ≤ k * n := Nat.le_mul_of_pos_left n hk
  rw [show k * (n + P) + r = k * n + r + k * P by rw [Nat.mul_add]; omega]
  exact Rule30Jen.periodic_mul h k (k * n + r) (by omega)

/-- Every decimation `n ↦ b (k n + r)` (`k > 0`) of an eventually periodic sequence is eventually
periodic. -/
theorem decimation_eventuallyPeriodic {b : ℕ → Bool} {k : ℕ} (hk : 0 < k)
    (h : EventuallyPeriodic b) (r : ℕ) : EventuallyPeriodic (fun n => b (k * n + r)) := by
  obtain ⟨T, P, hP, hper⟩ := h
  exact ⟨T, P, hP, decimation_periodic hk hper r⟩

/-- If the `k` decimations `n ↦ b (k n + r)`, `r < k`, are eventually periodic, so is `b`: with a
common transient `T` and a common period `P` (a product of the individual periods), `b` has
period `k P` from `k T`. -/
theorem eventuallyPeriodic_of_decimations {b : ℕ → Bool} {k : ℕ} (hk : 0 < k)
    (h : ∀ r < k, EventuallyPeriodic (fun n => b (k * n + r))) : EventuallyPeriodic b := by
  have common : ∀ m ≤ k, ∃ T P, 0 < P ∧
      ∀ r < m, ∀ n, T ≤ n → b (k * (n + P) + r) = b (k * n + r) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨0, 1, Nat.one_pos, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
    | succ m ih =>
      intro hm
      obtain ⟨T, P, hP, H⟩ := ih (by omega)
      obtain ⟨T', P', hP', H'⟩ := h m (by omega)
      refine ⟨T + T', P * P', Nat.mul_pos hP hP', fun r hr n hn => ?_⟩
      rcases Nat.lt_or_ge r m with hrm | hrm
      · have e := Rule30Jen.periodic_mul (f := fun n => b (k * n + r)) (H r hrm) P' n (by omega)
        rwa [Nat.mul_comm P' P] at e
      · obtain rfl : r = m := by omega
        exact Rule30Jen.periodic_mul (f := fun n => b (k * n + r)) H' P n (by omega)
  obtain ⟨T, P, hP, H⟩ := common k le_rfl
  refine ⟨k * T, k * P, Nat.mul_pos hk hP, fun t ht => ?_⟩
  have hdiv : k * (t / k) + t % k = t := Nat.div_add_mod t k
  have hq : T ≤ t / k := (Nat.le_div_iff_mul_le hk).2 (by rw [Nat.mul_comm]; exact ht)
  have e := H (t % k) (Nat.mod_lt t hk) (t / k) hq
  rw [show k * (t / k + P) + t % k = t + k * P by rw [Nat.mul_add]; omega, hdiv] at e
  exact e

/-- **Decimations.** For every `k > 0`, `b` is eventually periodic iff each of its `k`
decimations `n ↦ b (k n + r)`, `r < k`, is. -/
theorem eventuallyPeriodic_iff_decimations (b : ℕ → Bool) (k : ℕ) (hk : 0 < k) :
    EventuallyPeriodic b ↔ ∀ r < k, EventuallyPeriodic (fun n => b (k * n + r)) :=
  ⟨fun h r _ => decimation_eventuallyPeriodic hk h r, eventuallyPeriodic_of_decimations hk⟩

/-- **Problem 1 for decimations**: for every `k > 0`, Problem 1 holds iff some decimation
`n ↦ c (k n + r)` with `r < k` is not eventually periodic. -/
theorem problem1_iff_decimation (k : ℕ) (hk : 0 < k) :
    Rule30Prize.Problem1 ↔ ∃ r < k, ¬ EventuallyPeriodic (fun n => c (k * n + r)) := by
  constructor
  · intro h
    by_contra hne
    exact h ((eventuallyPeriodic_iff_decimations c k hk).2 fun r hr =>
      by_contra fun hr' => hne ⟨r, hr, hr'⟩)
  · rintro ⟨r, _, hne⟩ hep
    exact hne (decimation_eventuallyPeriodic hk hep r)

/-- **Even and odd times** (`k = 2`): Problem 1 holds iff the center column at even times or the
center column at odd times is not eventually periodic. -/
theorem problem1_iff_even_or_odd : Rule30Prize.Problem1 ↔
    ¬ EventuallyPeriodic (fun n => c (2 * n)) ∨ ¬ EventuallyPeriodic (fun n => c (2 * n + 1)) := by
  rw [problem1_iff_decimation 2 (by decide)]
  constructor
  · rintro ⟨r, hr, hne⟩
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · exact Or.inl hne
    · exact Or.inr hne
  · rintro (h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩

/-- **Residue classes.** For `P > 0`, `b` has eventual period `P` iff every residue class
`k ↦ b (r + k P)`, `r < P`, is eventually constant. -/
theorem eventually_period_iff_classes_const (b : ℕ → Bool) {P : ℕ} (hP : 0 < P) :
    (∃ T, ∀ t, T ≤ t → b (t + P) = b t) ↔
      ∀ r < P, ∃ K v, ∀ k, K ≤ k → b (r + k * P) = v := by
  constructor
  · rintro ⟨T, h⟩ r _
    refine ⟨T, b (r + T * P), fun k hk => ?_⟩
    have hTP : T ≤ T * P := Nat.le_mul_of_pos_right T hP
    have hmul : T * P + (k - T) * P = k * P := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hk]
    have e := Rule30Jen.periodic_mul h (k - T) (r + T * P) (by omega)
    rwa [show r + T * P + (k - T) * P = r + k * P by omega] at e
  · intro h
    -- one threshold `K` for all classes
    have uniform : ∀ m ≤ P, ∃ K, ∀ r < m, ∀ k, K ≤ k →
        b (r + (k + 1) * P) = b (r + k * P) := by
      intro m
      induction m with
      | zero => exact fun _ => ⟨0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
      | succ m ih =>
        intro hm
        obtain ⟨K₁, hK₁⟩ := ih (by omega)
        obtain ⟨K₂, v, hK₂⟩ := h m (by omega)
        refine ⟨K₁ + K₂, fun r hr k hk => ?_⟩
        rcases Nat.lt_or_ge r m with hrm | hrm
        · exact hK₁ r hrm k (by omega)
        · obtain rfl : r = m := by omega
          exact (hK₂ (k + 1) (by omega)).trans (hK₂ k (by omega)).symm
    obtain ⟨K, hK⟩ := uniform P le_rfl
    refine ⟨K * P, fun t ht => ?_⟩
    have hdiv : t % P + P * (t / P) = t := Nat.mod_add_div t P
    have hk : K ≤ t / P := (Nat.le_div_iff_mul_le hP).2 ht
    have e := hK (t % P) (Nat.mod_lt t hP) (t / P) hk
    rw [show t % P + (t / P + 1) * P = t + P by rw [Nat.add_mul, Nat.mul_comm (t / P) P]; omega,
      show t % P + t / P * P = t by rw [Nat.mul_comm (t / P) P]; omega] at e
    exact e

/-- `b` is eventually periodic iff for some `P > 0` every residue class modulo `P` is eventually
constant. -/
theorem eventuallyPeriodic_iff_classes_const (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ P, 0 < P ∧ ∀ r < P, ∃ K v, ∀ k, K ≤ k → b (r + k * P) = v := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨P, hP, (eventually_period_iff_classes_const b hP).1 ⟨T, h⟩⟩
  · rintro ⟨P, hP, h⟩
    obtain ⟨T, hT⟩ := (eventually_period_iff_classes_const b hP).2 h
    exact ⟨T, P, hP, hT⟩

/-- **Problem 1 as non-constant residue classes**: Problem 1 holds iff for every `P > 0` some
residue class `k ↦ c (r + k P)`, `r < P`, is not eventually constant. -/
theorem problem1_iff_nonconstant_class : Rule30Prize.Problem1 ↔
    ∀ P, 0 < P → ∃ r < P, ¬ ∃ K v, ∀ k, K ≤ k → c (r + k * P) = v := by
  constructor
  · intro h P hP
    by_contra hne
    exact h ((eventuallyPeriodic_iff_classes_const c).2 ⟨P, hP, fun r hr =>
      by_contra fun hr' => hne ⟨r, hr, hr'⟩⟩)
  · intro h hep
    obtain ⟨P, hP, hall⟩ := (eventuallyPeriodic_iff_classes_const c).1 hep
    obtain ⟨r, hr, hne⟩ := h P hP
    exact hne (hall r hr)

/-- The case `P = 1` of `problem1_iff_nonconstant_class` is a theorem: the center column is not
eventually constant (`Rule30Prize.center_not_eventually_constant`). -/
theorem nonconstant_class_one : ∃ r < 1, ¬ ∃ K v, ∀ k, K ≤ k → c (r + k * 1) = v :=
  ⟨0, Nat.one_pos, fun ⟨K, v, h⟩ => Rule30Prize.center_not_eventually_constant
    ⟨K, v, fun t ht => by
      have e := h t ht
      rwa [Nat.zero_add, Nat.mul_one] at e⟩⟩

/-! ### The `Π⁰₂` normal form, and periods restricted to a cofinal family -/

/-- **The `Π⁰₂` normal form**: Problem 1 holds iff for every transient `T` and every period
`P ≥ 1` some `t ≥ T` has `c (t + P) ≠ c t`. -/
theorem problem1_iff_pi2 : Rule30Prize.Problem1 ↔
    ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ c (t + P) ≠ c t := by
  constructor
  · intro h T P hP
    by_contra hne
    exact h ⟨T, P, hP, fun t ht => by_contra fun hc => hne ⟨t, ht, hc⟩⟩
  · rintro h ⟨T, P, hP, hper⟩
    obtain ⟨t, ht, hne⟩ := h T P hP
    exact hne (hper t ht)

/-- The side condition `0 < P` cannot be dropped: `P = 0` is never refuted. -/
theorem not_forall_pi2_without_pos : ¬ ∀ T P : ℕ, ∃ t, T ≤ t ∧ c (t + P) ≠ c t := fun h => by
  obtain ⟨t, _, ht⟩ := h 0 0
  exact ht rfl

/-- An executable test of one instance `(T, P)` of the `Π⁰₂` form: some `t < m` with `T ≤ t` has
`c (t + P) ≠ c t`. -/
def refutes (T P m : ℕ) : Bool :=
  (List.range m).any fun t => decide (T ≤ t) && (c (t + P) != c t)

/-- `refutes T P m` succeeds iff some `t < m` refutes the period `P` from `T`. -/
theorem refutes_eq_true_iff (T P m : ℕ) :
    refutes T P m = true ↔ ∃ t, t < m ∧ T ≤ t ∧ c (t + P) ≠ c t := by
  simp [refutes]

/-- **Each instance is `Σ⁰₁`**: Problem 1 holds iff for all `T` and `P ≥ 1` the finite test
`refutes T P m` succeeds for some `m`. -/
theorem problem1_iff_forall_exists_refutes : Rule30Prize.Problem1 ↔
    ∀ T P : ℕ, 0 < P → ∃ m, refutes T P m = true := by
  rw [problem1_iff_pi2]
  refine forall₂_congr fun T P => imp_congr_right fun _ => ?_
  simp only [refutes_eq_true_iff]
  constructor
  · rintro ⟨t, ht, hne⟩
    exact ⟨t + 1, t, Nat.lt_succ_self t, ht, hne⟩
  · rintro ⟨_, t, _, ht, hne⟩
    exact ⟨t, ht, hne⟩

/-- **Periods from a cofinal family.** If every `Q n` is positive and every `P > 0` divides some
`Q n`, then `b` is eventually periodic iff some `Q n` is an eventual period of `b`. -/
theorem eventuallyPeriodic_iff_of_cofinal {Q : ℕ → ℕ} (hQ : ∀ n, 0 < Q n)
    (hcof : ∀ P, 0 < P → ∃ n, P ∣ Q n) (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ n T, ∀ t, T ≤ t → b (t + Q n) = b t := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    obtain ⟨n, j, hj⟩ := hcof P hP
    refine ⟨n, T, fun t ht => ?_⟩
    rw [hj, Nat.mul_comm]
    exact Rule30Jen.periodic_mul h j t ht
  · rintro ⟨n, T, h⟩
    exact ⟨T, Q n, hQ n, h⟩

/-- **Factorial periods.** `b` is eventually periodic iff some factorial `(k + 1)!` is an eventual
period of `b`: a period `P` divides `P!`. -/
theorem eventuallyPeriodic_iff_factorial (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ k T, ∀ t, T ≤ t → b (t + (k + 1).factorial) = b t :=
  eventuallyPeriodic_iff_of_cofinal (Q := fun k => (k + 1).factorial)
    (fun k => Nat.factorial_pos _) (fun P hP => ⟨P - 1, Nat.dvd_factorial hP (by omega)⟩) b

/-- **Problem 1 with periods restricted to a cofinal family** `Q` (all `Q n > 0`, and every
`P > 0` divides some `Q n`). -/
theorem problem1_iff_cofinal_periods {Q : ℕ → ℕ} (hQ : ∀ n, 0 < Q n)
    (hcof : ∀ P, 0 < P → ∃ n, P ∣ Q n) :
    Rule30Prize.Problem1 ↔ ∀ n, ¬ ∃ T, ∀ t, T ≤ t → c (t + Q n) = c t :=
  problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_of_cofinal hQ hcof c)).trans not_exists)

/-- **Problem 1 with factorial periods**: Problem 1 holds iff no factorial `(k + 1)!` is an
eventual period of the center column. -/
theorem problem1_iff_factorial_periods : Rule30Prize.Problem1 ↔
    ∀ k : ℕ, ¬ ∃ T, ∀ t, T ≤ t → c (t + (k + 1).factorial) = c t :=
  problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_factorial c)).trans not_exists)

/-! ### The formal-conjectures statement -/

namespace FormalConjectures

/-- `Rule30.step` from formal-conjectures: the rule-30 update of a bi-infinite row. -/
def step (row : ℤ → Bool) : ℤ → Bool :=
  fun i => xor (row (i - 1)) (row i || row (i + 1))

/-- `Rule30.state` from formal-conjectures: the evolution from a single black cell. -/
def state : ℕ → ℤ → Bool
  | 0     => fun i => decide (i = 0)
  | t + 1 => step (state t)

/-- `Rule30.centerColumn` from formal-conjectures. -/
def centerColumn (t : ℕ) : Bool := state t 0

/-- formal-conjectures' `state t` is the row `Rule30Jen.cell t`. -/
theorem state_eq_cell : ∀ t, state t = fun i => Rule30Jen.cell t i
  | 0 => rfl
  | t + 1 => by rw [state, state_eq_cell t]; rfl

/-- formal-conjectures' `centerColumn` is `c`. -/
theorem centerColumn_eq (t : ℕ) : centerColumn t = c t := by
  rw [centerColumn, state_eq_cell]; rfl

/-- formal-conjectures' own sanity check `centerColumn_prefix`, re-proved here. -/
theorem centerColumn_prefix :
    (List.range 8).map centerColumn = [true, true, false, true, true, true, false, false] := by
  decide

end FormalConjectures

/-- **The formal-conjectures statement**: Problem 1 is equivalent to
`Rule30.centerColumn_not_eventually_periodic` of google-deepmind/formal-conjectures, verbatim. -/
theorem problem1_iff_fc : Rule30Prize.Problem1 ↔
    ¬ ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      FormalConjectures.centerColumn (t + p) = FormalConjectures.centerColumn t := by
  simp only [FormalConjectures.centerColumn_eq]
  constructor
  · rintro h ⟨p, hp, N, hN⟩
    exact h ⟨N, p, hp, hN⟩
  · rintro h ⟨N, p, hp, hN⟩
    exact h ⟨p, hp, N, hN⟩

/-! ### Wolfram's 2019 formal statement -/

/-- **Wolfram's formal statement, intended reading**: there are no period `p ≥ 1` and initial
length `i` with `c (t + p) = c t` for all `t > i`. -/
theorem problem1_iff_wolfram : Rule30Prize.Problem1 ↔
    ¬ ∃ p i : ℕ, 0 < p ∧ ∀ t, i < t → c (t + p) = c t := by
  rw [problem1_iff_not_eventuallyPeriodic]
  constructor
  · rintro h ⟨p, i, hp, hi⟩
    exact h ⟨i + 1, p, hp, fun t ht => hi t (by omega)⟩
  · rintro h ⟨T, P, hP, hT⟩
    exact h ⟨P, T, hP, fun t ht => hT t (by omega)⟩

/-- Wolfram's `c[t] = CellularAutomaton[30, {{1}, 0}, {t, {{0}}}]`, read literally: the list
`{c(0), …, c(t)}` of the first `t + 1` center values. -/
def wolframList (t : ℕ) : List Bool := (List.range (t + 1)).map c

/-- `c[t]` has `t + 1` entries. -/
theorem length_wolframList (t : ℕ) : (wolframList t).length = t + 1 := by
  simp [wolframList]

/-- `Last[c[t]]` is `c t`. -/
theorem getLast?_wolframList (t : ℕ) : (wolframList t).getLast? = some (c t) := by
  simp [wolframList, List.getLast?_range]

/-- The literal formula `NotExists[{p, i}, ForAll[t, t > i, c[t + p] == c[t]]]`, with `p = 0`
allowed, is false: `p = 0` is a witness. -/
theorem wolfram_literal_iff_false :
    (¬ ∃ p i : ℕ, ∀ t, i < t → wolframList (t + p) = wolframList t) ↔ False :=
  iff_false_intro fun h => h ⟨0, 0, fun _ _ => rfl⟩

/-- With `p ≥ 1` the literal formula is true for a trivial reason: `c[t + p]` and `c[t]` have
different lengths. -/
theorem wolfram_literal_pos_iff_true :
    (¬ ∃ p i : ℕ, 0 < p ∧ ∀ t, i < t → wolframList (t + p) = wolframList t) ↔ True := by
  refine iff_true_intro ?_
  rintro ⟨p, i, hp, h⟩
  have e := congrArg List.length (h (i + 1) (by omega))
  rw [length_wolframList, length_wolframList] at e
  omega

/-- **Wolfram's formal statement with `Last`**: comparing the last entries `Last[c[t + p]]` and
`Last[c[t]]`, with `p ≥ 1`, gives Problem 1. -/
theorem problem1_iff_wolfram_last : Rule30Prize.Problem1 ↔
    ¬ ∃ p i : ℕ, 0 < p ∧ ∀ t, i < t →
      (wolframList (t + p)).getLast? = (wolframList t).getLast? := by
  simp only [getLast?_wolframList, Option.some.injEq]
  exact problem1_iff_wolfram

/-! ### Stripe seeds `1, 11, 101, 1011, 10101, …` -/

section StripeSeeds

open Rule30Jen (cell rule)
open Rule30Realization (evol)

/-- The right edge of the single-seed pattern: `cell t t = true`. -/
theorem cell_diag (t : ℕ) : cell t (t : ℤ) = true := by
  have h := Rule30Diagonals.R_zero t
  unfold Rule30Diagonals.R at h
  exact (Rule30Diagonals.cell_congr (by omega)).trans h

/-- The diagonal next to the right edge alternates: `cell t (t - 1) = (t odd)`. -/
theorem cell_subdiag : ∀ t : ℕ, cell t ((t : ℤ) - 1) = decide (t % 2 = 1)
  | 0 => by decide
  | t + 1 => by
    have h := Rule30Diagonals.R_one_succ t
    unfold Rule30Diagonals.R at h
    rw [Rule30Diagonals.cell_congr (show ((t + 1 : ℕ) : ℤ) - 1 =
        ((t + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) by omega), h,
      Rule30Diagonals.cell_congr (show (t : ℤ) - ((1 : ℕ) : ℤ) = (t : ℤ) - 1 by omega),
      cell_subdiag t]
    by_cases ht : t % 2 = 1
    · rw [decide_eq_true ht, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false ht, decide_eq_true (by omega)]; rfl

/-- The stripe seed `s_n`: black at the even positions of `[0, n)` and at `n`. For
`n = 0, 1, 2, 3, 4, …` it reads `1, 11, 101, 1011, 10101, …` from position `0`. -/
def stripeSeed (n : ℕ) (p : ℤ) : Bool :=
  decide (0 ≤ p ∧ p < n ∧ p % 2 = 0) || decide (p = n)

/-- The first five stripe seeds on `[0, n]`: `1, 11, 101, 1011, 10101`. -/
theorem stripeSeed_pictures :
    (List.range 5).map (fun n => (List.range (n + 1)).map fun p => stripeSeed n p) =
      [[true], [true, true], [true, false, true], [true, false, true, true],
        [true, false, true, false, true]] := by
  decide

/-- `s_0` is the single black cell. -/
theorem stripeSeed_zero : stripeSeed 0 = Rule30Realization.seed := by
  funext p
  by_cases hp : p = 0
  · subst hp; rfl
  · simp only [stripeSeed, Rule30Realization.seed, Nat.cast_zero, hp,
      decide_eq_false (show ¬ (0 ≤ p ∧ p < 0 ∧ p % 2 = 0) by omega), decide_false, Bool.or_false]

/-- The pattern grown from `stripeSeed n`: the single-seed pattern left of the diagonal `p = t`,
the fixed stripe (black at even positions) on `[t, t + n)`, and the right edge at `t + n`. -/
def stripePattern (n t : ℕ) (p : ℤ) : Bool :=
  if p < t then cell t p
  else if p < (t : ℤ) + n then decide (p % 2 = 0)
  else decide (p = (t : ℤ) + n)

/-- Left of the diagonal the stripe pattern is the single-seed pattern. -/
theorem stripePattern_left {n t : ℕ} {p : ℤ} (h : p < (t : ℤ)) :
    stripePattern n t p = cell t p := by
  unfold stripePattern; rw [ite_eq_left h]

/-- On `[t, t + n)` the stripe pattern is black exactly at even positions. -/
theorem stripePattern_band {n t : ℕ} {p : ℤ} (h1 : (t : ℤ) ≤ p) (h2 : p < (t : ℤ) + n) :
    stripePattern n t p = decide (p % 2 = 0) := by
  unfold stripePattern; rw [ite_eq_right (show ¬ p < (t : ℤ) by omega), ite_eq_left h2]

/-- From `t + n` on, the stripe pattern is black only at `t + n`. -/
theorem stripePattern_edge {n t : ℕ} {p : ℤ} (h : (t : ℤ) + n ≤ p) :
    stripePattern n t p = decide (p = (t : ℤ) + n) := by
  unfold stripePattern
  rw [ite_eq_right (show ¬ p < (t : ℤ) by omega), ite_eq_right (show ¬ p < (t : ℤ) + n by omega)]

/-- **The `or` latch.** Inside the stripe, or at its right end, a cell or its right neighbor is
black. -/
theorem stripePattern_or {n t : ℕ} {p : ℤ} (h1 : (t : ℤ) ≤ p) (h2 : p ≤ (t : ℤ) + n) :
    (stripePattern n t p || stripePattern n t (p + 1)) = true := by
  by_cases hn : p < (t : ℤ) + n
  · rw [stripePattern_band h1 hn]
    by_cases hp : p % 2 = 0
    · rw [decide_eq_true hp]; rfl
    · rw [decide_eq_false hp]
      by_cases hn' : p + 1 < (t : ℤ) + n
      · rw [stripePattern_band (by omega) hn', decide_eq_true (show (p + 1) % 2 = 0 by omega)]
        rfl
      · rw [stripePattern_edge (show (t : ℤ) + n ≤ p + 1 by omega),
          decide_eq_true (show p + 1 = (t : ℤ) + n by omega)]
        rfl
  · rw [stripePattern_edge (show (t : ℤ) + n ≤ p by omega),
      decide_eq_true (show p = (t : ℤ) + n by omega)]
    rfl

/-- **Rule 30 from a stripe seed.** At time `t` the pattern grown from `stripeSeed n` is the
single-seed pattern left of the diagonal `p = t`, the stripe on `[t, t + n)`, black at `t + n`,
and white beyond. -/
theorem evol_stripeSeed (n : ℕ) : ∀ (t : ℕ) (p : ℤ),
    evol (stripeSeed n) t p = stripePattern n t p
  | 0, p => by
    show stripeSeed n p = stripePattern n 0 p
    unfold stripeSeed
    rcases (show p < 0 ∨ (0 ≤ p ∧ p < n) ∨ (n : ℤ) ≤ p by omega) with h | ⟨h1, h2⟩ | h
    · rw [stripePattern_left (show p < ((0 : ℕ) : ℤ) by omega),
        decide_eq_false (show ¬ (0 ≤ p ∧ p < (n : ℤ) ∧ p % 2 = 0) by omega),
        decide_eq_false (show ¬ p = (n : ℤ) by omega)]
      show false = decide (p = 0)
      rw [decide_eq_false (show ¬ p = 0 by omega)]
    · rw [stripePattern_band (show ((0 : ℕ) : ℤ) ≤ p by omega)
          (show p < ((0 : ℕ) : ℤ) + n by omega),
        decide_eq_false (show ¬ p = (n : ℤ) by omega)]
      by_cases hp : p % 2 = 0
      · rw [decide_eq_true (show 0 ≤ p ∧ p < (n : ℤ) ∧ p % 2 = 0 from ⟨h1, h2, hp⟩),
          decide_eq_true hp]; rfl
      · rw [decide_eq_false (show ¬ (0 ≤ p ∧ p < (n : ℤ) ∧ p % 2 = 0) by omega),
          decide_eq_false hp]; rfl
    · rw [stripePattern_edge (show ((0 : ℕ) : ℤ) + n ≤ p by omega),
        decide_eq_false (show ¬ (0 ≤ p ∧ p < (n : ℤ) ∧ p % 2 = 0) by omega)]
      by_cases he : p = (n : ℤ)
      · rw [decide_eq_true he, decide_eq_true (show p = ((0 : ℕ) : ℤ) + n by omega)]; rfl
      · rw [decide_eq_false he, decide_eq_false (show ¬ p = ((0 : ℕ) : ℤ) + n by omega)]; rfl
  | t + 1, p => by
    show rule (evol (stripeSeed n) t (p - 1)) (evol (stripeSeed n) t p)
        (evol (stripeSeed n) t (p + 1)) = stripePattern n (t + 1) p
    rw [evol_stripeSeed n t (p - 1), evol_stripeSeed n t p, evol_stripeSeed n t (p + 1)]
    rcases (show p + 1 < t ∨ p + 1 = t ∨ p = t ∨ ((t : ℤ) + 1 ≤ p ∧ p < (t : ℤ) + 1 + n) ∨
        (t : ℤ) + 1 + n ≤ p by omega) with h | h | h | ⟨h1, h2⟩ | h
    · -- all three neighbors lie left of the diagonal
      rw [stripePattern_left (show p - 1 < (t : ℤ) by omega),
        stripePattern_left (show p < (t : ℤ) by omega),
        stripePattern_left (show p + 1 < (t : ℤ) by omega),
        stripePattern_left (show p < ((t + 1 : ℕ) : ℤ) by omega)]
      rfl
    · -- `p = t - 1`: the right neighbor is on the diagonal
      rw [stripePattern_left (show p - 1 < (t : ℤ) by omega),
        stripePattern_left (show p < (t : ℤ) by omega),
        stripePattern_left (show p < ((t + 1 : ℕ) : ℤ) by omega)]
      have hsub : cell t p = decide (t % 2 = 1) := by
        rw [Rule30Diagonals.cell_congr (show p = (t : ℤ) - 1 by omega), cell_subdiag]
      have hdiag : cell t (p + 1) = true := by
        rw [Rule30Diagonals.cell_congr (show p + 1 = (t : ℤ) by omega), cell_diag]
      have key : (cell t p || stripePattern n t (p + 1)) = (cell t p || cell t (p + 1)) := by
        rw [hdiag, hsub]
        by_cases ht : t % 2 = 1
        · rw [decide_eq_true ht]; rfl
        · rw [decide_eq_false ht]
          by_cases hn : p + 1 < (t : ℤ) + n
          · rw [stripePattern_band (show (t : ℤ) ≤ p + 1 by omega) hn,
              decide_eq_true (show (p + 1) % 2 = 0 by omega)]
          · rw [stripePattern_edge (show (t : ℤ) + n ≤ p + 1 by omega),
              decide_eq_true (show p + 1 = (t : ℤ) + n by omega)]
      show xor (cell t (p - 1)) (cell t p || stripePattern n t (p + 1)) =
        xor (cell t (p - 1)) (cell t p || cell t (p + 1))
      rw [key]
    · -- `p = t`: the cell just left of the stripe
      rw [stripePattern_left (show p - 1 < (t : ℤ) by omega),
        stripePattern_left (show p < ((t + 1 : ℕ) : ℤ) by omega)]
      have hor := stripePattern_or (n := n) (t := t) (p := p) (by omega) (by omega)
      show xor (cell t (p - 1)) (stripePattern n t p || stripePattern n t (p + 1)) = cell (t + 1) p
      rw [hor]
      have hsub : cell t (p - 1) = decide (t % 2 = 1) := by
        rw [Rule30Diagonals.cell_congr (show p - 1 = (t : ℤ) - 1 by omega), cell_subdiag]
      have hsub' : cell (t + 1) p = decide ((t + 1) % 2 = 1) := by
        rw [Rule30Diagonals.cell_congr (show p = ((t + 1 : ℕ) : ℤ) - 1 by omega), cell_subdiag]
      rw [hsub, hsub']
      by_cases ht : t % 2 = 1
      · rw [decide_eq_true ht, decide_eq_false (show ¬ (t + 1) % 2 = 1 by omega)]; rfl
      · rw [decide_eq_false ht, decide_eq_true (show (t + 1) % 2 = 1 by omega)]; rfl
    · -- inside the stripe
      rw [stripePattern_band (show (t : ℤ) ≤ p - 1 by omega) (show p - 1 < (t : ℤ) + n by omega),
        stripePattern_band (show ((t + 1 : ℕ) : ℤ) ≤ p by omega)
          (show p < ((t + 1 : ℕ) : ℤ) + n by omega)]
      have hor := stripePattern_or (n := n) (t := t) (p := p) (by omega) (by omega)
      show xor (decide ((p - 1) % 2 = 0)) (stripePattern n t p || stripePattern n t (p + 1)) =
        decide (p % 2 = 0)
      rw [hor]
      by_cases hp : p % 2 = 0
      · rw [decide_eq_false (show ¬ (p - 1) % 2 = 0 by omega), decide_eq_true hp]; rfl
      · rw [decide_eq_true (show (p - 1) % 2 = 0 by omega), decide_eq_false hp]; rfl
    · -- at or right of the new right edge
      rw [stripePattern_edge (show (t : ℤ) + n ≤ p - 1 by omega),
        stripePattern_edge (show (t : ℤ) + n ≤ p by omega),
        stripePattern_edge (show (t : ℤ) + n ≤ p + 1 by omega),
        stripePattern_edge (show ((t + 1 : ℕ) : ℤ) + n ≤ p by omega),
        decide_eq_false (show ¬ p = (t : ℤ) + n by omega),
        decide_eq_false (show ¬ p + 1 = (t : ℤ) + n by omega)]
      show xor (decide (p - 1 = (t : ℤ) + n)) false = decide (p = ((t + 1 : ℕ) : ℤ) + n)
      by_cases he : p - 1 = (t : ℤ) + n
      · rw [decide_eq_true he, decide_eq_true (show p = ((t + 1 : ℕ) : ℤ) + n by omega)]; rfl
      · rw [decide_eq_false he, decide_eq_false (show ¬ p = ((t + 1 : ℕ) : ℤ) + n by omega)]
        rfl

/-- **Every stripe seed has exactly the center column of the single seed.** -/
theorem stripeSeed_center (n t : ℕ) : evol (stripeSeed n) t 0 = c t := by
  rw [evol_stripeSeed]
  cases t with
  | zero =>
    by_cases hn : (0 : ℤ) < ((0 : ℕ) : ℤ) + n
    · rw [stripePattern_band (by omega) hn]; rfl
    · rw [stripePattern_edge (by omega),
        decide_eq_true (show (0 : ℤ) = ((0 : ℕ) : ℤ) + n by omega)]
      rfl
  | succ t => rw [stripePattern_left (by omega)]; rfl

/-- **Problem 1 for every stripe seed**: for every `n`, Problem 1 holds iff the center column of
rule 30 started from `stripeSeed n` (`1, 11, 101, 1011, 10101, …`) is not eventually periodic. -/
theorem problem1_iff_stripeSeed (n : ℕ) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evol (stripeSeed n) t 0) :=
  problem1_iff_of_eventually_eq (N := 0) fun t _ => stripeSeed_center n t

end StripeSeeds

end TransformsSeeds
end Rule30Equivalents
