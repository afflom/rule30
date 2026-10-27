module

public import Rule30Equivalents.ShiftOrbit
public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Problem 1 in the language of words, symbolic dynamics and finite automata

`Problem1` says that the center column `c` of rule 30 is not eventually periodic. This file proves
it equivalent to statements about the words that occur in `c`, about the orbit of `c` under the
shift `σ` of `ℕ → Bool` (`σ x t = x (t + 1)`, product topology), and about finite automata. Most
statements are proved for every `b : ℕ → Bool` and then specialized to `c`; a few
(`problem1_iff_exists_accPt`, `problem1_iff_frequently_ne`, `problem1_iff_no_eventual_word`,
`problem1_iff_recurrent_right_special_branch`) are proved for `c` directly from general lemmas.

## Statements

Mathlib's vocabulary for eventual periodicity:
* `problem1_iff_filter`: no `P > 0` has `c (t + P) = c t` for all large `t`, written
  `∀ᶠ t in Filter.atTop`. `problem1_iff_frequently_ne`: for every `P > 0`, `c (t + P) ≠ c t` for
  infinitely many `t` (`∃ᶠ`).
* `problem1_iff_no_hasPeriod_tail`: there are no `T` and `P > 0` such that every word
  `c T, c (T + 1), …, c (T + n - 1)` has period `P` (Mathlib's `List.HasPeriod`).

Eventual words:
* `problem1_iff_no_word`, as `Rule30StripCertificates.problem1_iff_no_word`: no nonempty word `w`
  has `c` equal to `w w w …` from some time on. `Rule30StripCertificates.EventuallyWord w` is
  `EventuallyWord c` here (`eventuallyWord_center_iff`), and
  `eventuallyPeriodic_iff_exists_eventuallyWord` is the statement for every `b`.
* `problem1_iff_no_eventual_word`: for every nonempty `w` and every `T`, some `n` has
  `c (T + n) ≠ w[n mod |w|]`.
* `problem1_iff_no_primitive_word`: the same for primitive `w` only (nonempty, and not a proper
  power `u ^ k` with `k ≥ 2`). So Problem 1 is the conjunction, over primitive words `w`, of
  "`c` is not eventually `w w w …`".

Right-special factors and the tail language:
* `problem1_iff_right_special`: for every `n` some word `w` of length `n` is right-special in `c`:
  both `w 0` and `w 1` occur in `c`.
* `problem1_iff_right_special_branch`, the König form: some left-infinite word `… x 2 x 1 x 0` has
  all its suffixes `x (n - 1) … x 1 x 0` right-special in `c`.
* `problem1_iff_recurrent_right_special`, `problem1_iff_recurrent_right_special_branch`: the same
  two statements with "occurs" replaced by "occurs infinitely often", that is, for the tail
  language of `c`.
* `problem1_iff_tail_complexity`: for every `n`, at least `n + 1` words of length `n` occur in `c`
  infinitely often (Morse–Hedlund for the tail language).

The orbit of `c` in `ℕ → Bool`:
* `problem1_iff_orbit_closure_infinite`: the closure of `{σⁿ c : n ∈ ℕ}` is infinite.
  `problem1_iff_exists_accPt`: the orbit `{σⁿ c}` has an accumulation point.
* `problem1_iff_omegaLimit_infinite`: the omega-limit set `ω(c)` is infinite. This is Mathlib's
  `omegaLimit Filter.atTop` for the semiflow `n ↦ σⁿ`.
* `problem1_iff_omegaLimit_not_periodic`: `ω(c)` contains a point that is not periodic under `σ`.
  The proof uses `finite_of_forall_periodic`: a closed shift-invariant subset of `ℕ → Bool` whose
  points are all periodic is finite.

Finite automata:
* `problem1_iff_no_finite_generator`: no finite autonomous machine (finite state type `σ`, start
  `s₀`, transition `F`, output `g`) has `c t = g (F^[t] s₀)` for all large `t`.
* `problem1_iff_unpredictable`: every finite automaton that reads `c 0, c 1, …` and guesses each
  next cell from its current state (`readState`) guesses wrong infinitely often.
* `problem1_iff_no_feedback_shift_register`: no feedback shift register, of any length `k` and with
  any feedback function `f : (Fin k → Bool) → Bool`, has
  `c (t + k) = f (c t, …, c (t + k - 1))` for all large `t`.
* `problem1_iff_no_regular_predictor`: for every regular language `L` (Mathlib's
  `Language.IsRegular`), the prediction "`c n = 1` iff `c 0 … c (n - 1) ∈ L`" is wrong for
  infinitely many `n`.

## Proof

* Filter and `List.HasPeriod` forms: unfolding, with `Filter.eventually_atTop` and
  `List.hasPeriod_iff_getElem?`.
* Words. A period `P` from `T` gives the word `b T … b (T + P - 1)`. A shortest eventual word is
  primitive: if it were `u ^ k` with `k ≥ 2`, the shorter `u` would also be an eventual word.
* Right-special factors (`not_eventuallyPeriodic_iff_rightSpecial`). If no word of length `n` is
  right-special, the letter after each window of length `n` is a function of the window. Two
  windows coincide by pigeonhole, and `b` is periodic from there on
  (`eventuallyPeriodic_of_determined`). Conversely, if `b` is eventually periodic, Morse–Hedlund
  (`ShiftOrbit`) gives `p(n + 1) ≤ p(n)` for some `n`, and then every factor of length `n` has a
  unique right extension (`ShiftOrbit.unique_right_extension`).
* Tail language (`not_eventuallyPeriodic_iff_recurrentRightSpecial`). If no word of length `n` is
  followed infinitely often by both letters, then from some time on each of the finitely many
  windows of length `n` is always followed by the same letter, and the pigeonhole argument above
  applies from that time on. Tail complexity
  (`eventuallyPeriodic_iff_exists_ncard_tailFactors_le`): if `b` has period `P` from `T`, the
  words of length `P` that occur infinitely often are among the `P` windows at `T, …, T + P - 1`.
  Conversely, the words that occur only finitely often have a last occurrence, so a tail of `b`
  has at most `n` factors of length `n`, and Morse–Hedlund applies to it.
* König form (`exists_branch`). Let `R` be a set of words closed under deleting letters on the
  left, such as the right-special or the recurrent right-special words. Call `w` extendable if it
  has left extensions `v w ∈ R` of every length. The empty word is extendable if `R` has words of
  every length, and if `w` is extendable, then so is `0 w` or `1 w` (`Extendable.exists_cons`).
  Adding one letter at a time gives the branch.
* Orbit closure. Finite sets are closed in the Hausdorff space `ℕ → Bool`, so the orbit closure is
  finite iff the orbit is (`ShiftOrbit.eventuallyPeriodic_iff_finite_shifts`). An infinite set has
  an accumulation point because `ℕ → Bool` is compact (`Set.Infinite.exists_accPt_principal`). A set
  with an accumulation point is infinite (`Set.Infinite.of_accPt`).
* Omega-limit set. `ω(b)` lies in the orbit closure, so it is finite when `b` is eventually
  periodic. Conversely, let `ω(b)` have `K` points. The sequences whose first `K` letters are those
  of a point of `ω(b)` form an open set containing `ω(b)`. By compactness, `σⁿ b` lies in it for
  all large `n` (`eventually_mapsTo_of_isOpen_of_omegaLimit_subset`). So a tail of `b` has at most
  `K` factors of length `K`, and Morse–Hedlund makes it eventually periodic.
* Non-periodic points of `ω(b)`. If `b` has period `P` from `T`, every `σⁿ b` with `n ≥ T` is fixed
  by `σ^P`. That is a closed condition, so every point of `ω(b)` is periodic. Conversely, `ω(b)` is
  closed and `σ`-invariant (`shift_mem_omegaLimit`), and infinite when `b` is not eventually
  periodic. So it is enough that a closed invariant set `Ω` of periodic points is finite. Suppose
  `Ω` is infinite. Its accumulation points form a closed set `Y`, nonempty by compactness.
  - `Y` has no isolated point (`accPt_derivedSet_of_periodic`). Let `y ∈ Y` have period `p`. A point
    `x ∈ Ω`, `x ≠ y`, close to `y` first differs from `y` at some `d`. Shifting `x` by a multiple
    of `p` moves this difference into `[m, m + p)`. The shifted point has the periods of `x`, and
    these are large: sequences with periods `p` and `q` that agree on their first `p + q` letters
    are equal (`eq_of_agree_of_periodic`, a weak form of Fine–Wilf). So there are infinitely many
    shifted points. One of their accumulation points lies in `Y`, agrees with `y` on `[0, m)` and
    is not `y`.
  - But `Y` is the countable union of its finite sets of points of period `q`
    (`finite_setOf_isPeriodicPt`). By Baire's theorem in the compact space `Y`, one of these sets
    has an interior point, and that point is isolated in `Y`.
* Automata. A finite autonomous machine repeats a state by pigeonhole, and its output is periodic
  from then on (`eventuallyPeriodic_of_generator`). An eventually periodic `b` is produced, and
  predicted without error, by a counter on `Fin (T + P)` that counts up to `T + P - 1` and jumps
  back to `T` (`counterStep`). A predictor that is always right from time `N` on reads its own
  guesses, so from `N` on it runs autonomously with the transition `s ↦ δ s (g s)`. A feedback
  shift register makes the next letter a function of the window, as in the right-special argument.
  A regular language is accepted by a DFA, which is a predictor with `g s = (s ∈ accept)`.

## Special cases

* `P > 0`. Every list has period `0` (`List.hasPeriod_zero`), and `c (t + 0) = c t` for all `t`. So
  the filter and `List.HasPeriod` forms need `0 < P`, as stated.
* Eventually constant sequences have period `1`; the general statements cover them. At length `0`
  the right-special form only says that `c` takes both values. The center column is not even
  eventually constant (`Rule30Prize.center_not_eventually_constant`).
* No real numbers occur here, so dyadic double expansions play no role.
* The automaton forms ask for infinitely many wrong guesses. Finitely many errors can always be
  avoided, since a finite machine can store any finite prefix of `c`.

## Sources

* Right-special factors: J. Cassaigne, *Complexité et facteurs spéciaux*, Bull. Belg. Math. Soc.
  Simon Stevin 4 (1997) 67–88, §3.1.1: for a factorial, extendable language on two letters,
  `p(n + 1) - p(n)` is the number of right-special factors of length `n`. This file does not count
  them; it proves only that right-special factors of every length exist iff `b` is not eventually
  periodic. Morse–Hedlund is in `ShiftOrbit`, with its sources.
* D. Kőnig, *Über eine Schlussweise aus dem Endlichen ins Unendliche*, Acta Sci. Math. (Szeged) 3
  (1927) 121–130. Mathlib's version is `exists_seq_covby_of_forall_covby_finite`
  (`Mathlib/Order/KonigLemma.lean`); the binary tree here is handled directly.
* Primitive words, in the standard sense: M. Lothaire, *Combinatorics on Words*, Addison-Wesley,
  1983.
* Periods of words: `List.HasPeriod` (`Mathlib/Data/List/PeriodicityLemma.lean`, Š. Holub, 2025),
  which also proves the Fine–Wilf theorem of N. J. Fine and H. S. Wilf, *Uniqueness theorems for
  periodic functions*, Proc. Amer. Math. Soc. 16 (1965) 109–114.
* Omega-limit sets: `Mathlib/Dynamics/OmegaLimit.lean`. T. Meyerovitch and V. Salo, *On pointwise
  periodicity in tilings, cellular automata and subshifts*, arXiv:1703.10013 (2017), state that a
  subshift over a finitely generated group whose orbits are all finite is finite.
  `finite_of_forall_periodic` is a one-sided version, proved here with Baire's theorem.
* Finite-state prediction: M. Feder, N. Merhav and M. Gutman, *Universal prediction of individual
  sequences*, IEEE Trans. Inform. Theory 38 (1992) 1258–1270, study the least error rate of
  finite-state predictors. Here only "infinitely many errors" matters.
* Feedback shift registers with arbitrary feedback functions: C. J. A. Jansen and D. E. Boekee,
  *The shortest feedback shift register that can generate a given sequence*, CRYPTO '89, LNCS 435
  (1990) 90–99.
* DFAs and regular languages: `Mathlib/Computability/DFA.lean`.
-/

@[expose] public section

namespace Rule30Equivalents
namespace WordsAutomata

open Ruliology.CellularAutomata

/-! ### Tools -/

/-- If a tail `fun t => b (N + t)` is eventually periodic, so is `b`. -/
theorem eventuallyPeriodic_of_tail {b : ℕ → Bool} (N : ℕ)
    (h : EventuallyPeriodic fun t => b (N + t)) : EventuallyPeriodic b := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨N + T, P, hP, fun t ht => ?_⟩
  have h1 : b (N + (t - N + P)) = b (N + (t - N)) := hper (t - N) (by omega)
  rwa [show N + (t - N + P) = t + P by omega, show N + (t - N) = t by omega] at h1

/-- If, from position `T` on, the letter after each window of length `n` is a function of the
window, then `b` is eventually periodic: two windows coincide by pigeonhole, and then everything
after them coincides. -/
theorem eventuallyPeriodic_of_determined {b : ℕ → Bool} {n T : ℕ}
    (h : ∀ i i', T ≤ i → T ≤ i' → (∀ j < n, b (i + j) = b (i' + j)) → b (i + n) = b (i' + n)) :
    EventuallyPeriodic b := by
  obtain ⟨k, k', hkk', hw⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => fun j : Fin n => b (T + k + j)) (fun _ => Set.mem_univ _)
  have key : ∀ m, b (T + k + m) = b (T + k' + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < n
      · exact congrFun hw ⟨m, hm⟩
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + n := ⟨m - n, by omega⟩
        have := h (T + k + m') (T + k' + m') (by omega) (by omega) fun j hj => by
          rw [Nat.add_assoc (T + k), Nat.add_assoc (T + k')]
          exact ih (m' + j) (by omega)
        rwa [Nat.add_assoc (T + k), Nat.add_assoc (T + k')] at this
  exact ShiftOrbit.eventuallyPeriodic_of_shift_eq (show T + k < T + k' by omega) key

/-! ### `Filter.atTop` form -/

/-- Eventual periodicity with Mathlib's `∀ᶠ t in atTop`. -/
theorem eventuallyPeriodic_iff_eventually_atTop (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ P > 0, ∀ᶠ t in Filter.atTop, b (t + P) = b t := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨P, hP, Filter.eventually_atTop.2 ⟨T, h⟩⟩
  · rintro ⟨P, hP, h⟩
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 h
    exact ⟨T, P, hP, hT⟩

/-- **Problem 1, filter form**: no `P > 0` has `c (t + P) = c t` for all large `t`. -/
theorem problem1_iff_filter : Rule30Prize.Problem1 ↔
    ¬ ∃ P > 0, ∀ᶠ t in Filter.atTop, c (t + P) = c t :=
  (eventuallyPeriodic_iff_eventually_atTop c).not

/-- **Problem 1, positive filter form**: for every `P > 0`, `c (t + P) ≠ c t` for infinitely
many `t`. -/
theorem problem1_iff_frequently_ne : Rule30Prize.Problem1 ↔
    ∀ P > 0, ∃ᶠ t in Filter.atTop, c (t + P) ≠ c t := by
  rw [problem1_iff_filter]
  constructor
  · intro h P hP
    exact Filter.not_eventually.1 fun he => h ⟨P, hP, he⟩
  · rintro h ⟨P, hP, he⟩
    obtain ⟨t, hne, heq⟩ := ((h P hP).and_eventually he).exists
    exact hne heq

/-! ### `List.HasPeriod` form -/

/-- The word `b T, b (T + 1), …, b (T + n - 1)` has period `P` (Mathlib's `List.HasPeriod`) iff
`b (T + (i + P)) = b (T + i)` whenever `i + P < n`. -/
theorem hasPeriod_range_map_iff (b : ℕ → Bool) (T n P : ℕ) :
    ((List.range n).map fun j => b (T + j)).HasPeriod P ↔
      ∀ i, i + P < n → b (T + (i + P)) = b (T + i) := by
  rw [List.hasPeriod_iff_getElem?, List.length_map, List.length_range]
  constructor
  · intro h i hi
    have := h i (by omega)
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega),
      List.getElem?_range (by omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact this.symm
  · intro h i hi
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega),
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.some.injEq]
    exact (h i (by omega)).symm

/-- `b` is eventually periodic iff for some `T` and `P > 0` every word
`b T, b (T + 1), …, b (T + n - 1)` has period `P`. -/
theorem eventuallyPeriodic_iff_hasPeriod (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ T P : ℕ, 0 < P ∧ ∀ n : ℕ,
      ((List.range n).map fun j => b (T + j)).HasPeriod P := by
  simp only [hasPeriod_range_map_iff]
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, P, hP, fun n i _ => ?_⟩
    rw [← Nat.add_assoc]
    exact h (T + i) (by omega)
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have := h (t - T + P + 1) (t - T) (by omega)
    rwa [show T + (t - T + P) = t + P by omega, show T + (t - T) = t by omega] at this

/-- **Problem 1, `List.HasPeriod` form**: there are no `T` and `P > 0` such that every word
`c T, c (T + 1), …, c (T + n - 1)` has period `P`. -/
theorem problem1_iff_no_hasPeriod_tail : Rule30Prize.Problem1 ↔
    ¬ ∃ T P : ℕ, 0 < P ∧ ∀ n : ℕ, ((List.range n).map fun j => c (T + j)).HasPeriod P :=
  (eventuallyPeriodic_iff_hasPeriod c).not

/-! ### Eventual words -/

/-- `b` is the word `w` repeated forever from some time `T` on: `b t = w[(t - T) mod |w|]` for
`t ≥ T`. For `b = c` this is `Rule30StripCertificates.EventuallyWord`. -/
def EventuallyWord (b : ℕ → Bool) (w : List Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → b t = w.getD ((t - T) % w.length) false

/-- The same with the time measured from `T`: `b (T + n) = w[n mod |w|]` for all `n`. -/
theorem eventuallyWord_iff (b : ℕ → Bool) (w : List Bool) :
    EventuallyWord b w ↔ ∃ T, ∀ n, b (T + n) = w.getD (n % w.length) false := by
  constructor
  · rintro ⟨T, h⟩
    refine ⟨T, fun n => ?_⟩
    rw [h (T + n) (by omega), Nat.add_sub_cancel_left]
  · rintro ⟨T, h⟩
    refine ⟨T, fun t ht => ?_⟩
    have := h (t - T)
    rwa [show T + (t - T) = t by omega] at this

/-- A nonempty eventual word `w` makes `b` eventually periodic, with period `|w|`. -/
theorem eventuallyPeriodic_of_eventuallyWord {b : ℕ → Bool} {w : List Bool} (hw : w ≠ [])
    (h : EventuallyWord b w) : EventuallyPeriodic b := by
  obtain ⟨T, hT⟩ := h
  have hlen : 0 < w.length := List.length_pos_iff.2 hw
  refine ⟨T, w.length, hlen, fun t ht => ?_⟩
  rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = t - T + w.length by omega,
    Nat.add_mod_right]

/-- If `b` has period `P` from `T`, it is eventually the word `b T, …, b (T + P - 1)`. -/
theorem exists_eventuallyWord_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ w : List Bool, w ≠ [] ∧ EventuallyWord b w := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hperk := Rule30Jen.periodic_mul hper
  refine ⟨(List.range P).map (fun i => b (T + i)), ?_, T, fun t ht => ?_⟩
  · intro e
    have := congrArg List.length e
    simp at this
    omega
  · have hlen : ((List.range P).map (fun i => b (T + i))).length = P := by simp
    rw [hlen]
    have hmod : (t - T) % P < P := Nat.mod_lt _ hP
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hmod]
    simp only [Option.map_some, Option.getD_some]
    have e := hperk ((t - T) / P) (T + (t - T) % P) (by omega)
    have hd := Nat.div_add_mod (t - T) P
    rw [show T + (t - T) % P + (t - T) / P * P = t by rw [Nat.mul_comm] at hd; omega] at e
    exact e

/-- `b` is eventually periodic iff it is eventually some nonempty word repeated forever. -/
theorem eventuallyPeriodic_iff_exists_eventuallyWord (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ w : List Bool, w ≠ [] ∧ EventuallyWord b w :=
  ⟨exists_eventuallyWord_of_eventuallyPeriodic,
    fun ⟨_, hw, h⟩ => eventuallyPeriodic_of_eventuallyWord hw h⟩

/-- `Rule30StripCertificates.EventuallyWord` is `EventuallyWord c`. -/
theorem eventuallyWord_center_iff (w : List Bool) :
    Rule30StripCertificates.EventuallyWord w ↔ EventuallyWord c w := Iff.rfl

/-- **Problem 1 as the exclusion of every word**, as in
`Rule30StripCertificates.problem1_iff_no_word`. -/
theorem problem1_iff_no_word : Rule30Prize.Problem1 ↔
    ∀ w : List Bool, w ≠ [] → ¬ Rule30StripCertificates.EventuallyWord w :=
  Rule30StripCertificates.problem1_iff_no_word

/-- **Problem 1, no eventual word**: for every nonempty word `w` and every time `T` there is an
`n` with `c (T + n) ≠ w[n mod |w|]`. -/
theorem problem1_iff_no_eventual_word : Rule30Prize.Problem1 ↔
    ∀ w : List Bool, w ≠ [] → ∀ T, ∃ n, c (T + n) ≠ w.getD (n % w.length) false := by
  constructor
  · intro h w hw T
    by_contra hne
    push Not at hne
    exact h ((eventuallyPeriodic_iff_exists_eventuallyWord c).2
      ⟨w, hw, (eventuallyWord_iff c w).2 ⟨T, hne⟩⟩)
  · intro h hep
    obtain ⟨w, hw, hew⟩ := (eventuallyPeriodic_iff_exists_eventuallyWord c).1 hep
    obtain ⟨T, hT⟩ := (eventuallyWord_iff c w).1 hew
    obtain ⟨n, hn⟩ := h w hw T
    exact hn (hT n)

/-- A word is primitive if it is nonempty and not a proper power `u ^ k`, `k ≥ 2`. -/
def Primitive (w : List Bool) : Prop :=
  w ≠ [] ∧ ∀ (u : List Bool) (k : ℕ), (List.replicate k u).flatten = w → k = 1

/-- Reading `u ^ k` at position `i < k |u|` reads `u` at `i mod |u|`. -/
theorem getD_flatten_replicate (u : List Bool) (k i : ℕ) (hi : i < k * u.length) :
    (List.replicate k u).flatten.getD i false = u.getD (i % u.length) false := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons]
    by_cases h : i < u.length
    · rw [List.getD_append _ _ _ _ h, Nat.mod_eq_of_lt h]
    · rw [List.getD_append_right _ _ _ _ (by omega),
        ih (i - u.length) (by rw [Nat.add_mul, Nat.one_mul] at hi; omega)]
      congr 1
      conv_rhs => rw [show i = i - u.length + u.length by omega]
      rw [Nat.add_mod_right]

/-- `b` is eventually periodic iff it is eventually a primitive word repeated forever. A shortest
eventual word is primitive: if it were `u ^ k` with `k ≥ 2`, the shorter `u` would do. -/
theorem eventuallyPeriodic_iff_exists_primitive (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ w : List Bool, Primitive w ∧ EventuallyWord b w := by
  classical
  constructor
  · intro h
    have hex : ∃ m, ∃ w : List Bool, w ≠ [] ∧ w.length = m ∧ EventuallyWord b w := by
      obtain ⟨w, hw, hew⟩ := exists_eventuallyWord_of_eventuallyPeriodic h
      exact ⟨w.length, w, hw, rfl, hew⟩
    obtain ⟨w, hw, hlen, hew⟩ := Nat.find_spec hex
    refine ⟨w, ⟨hw, fun u k hk => ?_⟩, hew⟩
    by_contra hk1
    have hu : u ≠ [] := by
      rintro rfl
      apply hw
      rw [← hk]
      simp
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hw
      rw [← hk]
      simp
    have hulen : 0 < u.length := List.length_pos_iff.2 hu
    have hwlen : w.length = k * u.length := by
      rw [← hk]
      simp
    have hewu : EventuallyWord b u := by
      obtain ⟨T, hT⟩ := hew
      refine ⟨T, fun t ht => ?_⟩
      rw [hT t ht, hwlen, ← hk, getD_flatten_replicate u k _
        (Nat.mod_lt _ (Nat.mul_pos (Nat.pos_of_ne_zero hk0) hulen)),
        Nat.mod_mod_of_dvd _ (Dvd.intro_left k rfl)]
    have hmin := Nat.find_min' hex ⟨u, hu, rfl, hewu⟩
    have h2 : 2 * u.length ≤ k * u.length := Nat.mul_le_mul_right _ (by omega)
    omega
  · rintro ⟨w, hw, hew⟩
    exact eventuallyPeriodic_of_eventuallyWord hw.1 hew

/-- **Problem 1, primitive words**: for every primitive word `w`, the center column is not
eventually `w w w …`. -/
theorem problem1_iff_no_primitive_word : Rule30Prize.Problem1 ↔
    ∀ w : List Bool, Primitive w → ¬ EventuallyWord c w := by
  constructor
  · intro h w hw hew
    exact h ((eventuallyPeriodic_iff_exists_primitive c).2 ⟨w, hw, hew⟩)
  · intro h hep
    obtain ⟨w, hw, hew⟩ := (eventuallyPeriodic_iff_exists_primitive c).1 hep
    exact h w hw hew

/-! ### Right-special factors -/

/-- The word `w` occurs in `b` at some position `i` and is followed there by the letter `a`. -/
def OccursThen (b : ℕ → Bool) (w : List Bool) (a : Bool) : Prop :=
  ∃ i : ℕ, (∀ j (hj : j < w.length), b (i + j) = w[j]) ∧ b (i + w.length) = a

/-- `w` is a right-special factor of `b`: both `w 0` and `w 1` occur in `b`. -/
def RightSpecial (b : ℕ → Bool) (w : List Bool) : Prop :=
  OccursThen b w false ∧ OccursThen b w true

/-- The window of length `n` at position `i` occurs at `i`, followed by `b (i + n)`. -/
theorem occursThen_ofFn (b : ℕ → Bool) (i n : ℕ) :
    OccursThen b (List.ofFn fun j : Fin n => b (i + j)) (b (i + n)) :=
  ⟨i, fun j hj => by simp, by simp⟩

/-- If no word of length `n` is right-special, the letter after a window of length `n` is a
function of the window. -/
theorem determined_of_not_rightSpecial {b : ℕ → Bool} {n : ℕ}
    (h : ¬ ∃ w : List Bool, w.length = n ∧ RightSpecial b w) {i i' : ℕ}
    (hw : ∀ j < n, b (i + j) = b (i' + j)) : b (i + n) = b (i' + n) := by
  by_contra hne
  apply h
  have e : (List.ofFn fun j : Fin n => b (i + j)) = List.ofFn fun j : Fin n => b (i' + j) :=
    List.ofFn_inj.2 (funext fun j => hw j j.isLt)
  have h1 := occursThen_ofFn b i n
  have h2 := occursThen_ofFn b i' n
  rw [e] at h1
  refine ⟨List.ofFn fun j : Fin n => b (i' + j), List.length_ofFn, ?_⟩
  cases hb : b (i + n) <;> cases hb' : b (i' + n)
  · exact absurd (hb.trans hb'.symm) hne
  · rw [hb] at h1
    rw [hb'] at h2
    exact ⟨h1, h2⟩
  · rw [hb] at h1
    rw [hb'] at h2
    exact ⟨h2, h1⟩
  · exact absurd (hb.trans hb'.symm) hne

/-- **Right-special factors**: `b` is not eventually periodic iff it has a right-special factor
of every length. -/
theorem not_eventuallyPeriodic_iff_rightSpecial (b : ℕ → Bool) :
    ¬ EventuallyPeriodic b ↔ ∀ n, ∃ w : List Bool, w.length = n ∧ RightSpecial b w := by
  constructor
  · intro hep n
    by_contra h
    exact hep (eventuallyPeriodic_of_determined (n := n) (T := 0)
      fun i i' _ _ hw => determined_of_not_rightSpecial h hw)
  · intro h hep
    obtain ⟨n, hn⟩ := (ShiftOrbit.eventuallyPeriodic_iff_exists_ncard_factors_succ_le b).1 hep
    obtain ⟨w, rfl, ⟨i, hi, hia⟩, ⟨i', hi', hia'⟩⟩ := h n
    have := ShiftOrbit.unique_right_extension hn (i := i) (i' := i') fun j hj => by
      rw [hi j hj, hi' j hj]
    rw [hia, hia'] at this
    exact Bool.false_ne_true this

/-- **Problem 1, right-special factors**: for every `n` some word `w` of length `n` is
right-special in the center column: both `w 0` and `w 1` occur in `c`. -/
theorem problem1_iff_right_special : Rule30Prize.Problem1 ↔
    ∀ n, ∃ w : List Bool, w.length = n ∧ RightSpecial c w :=
  not_eventuallyPeriodic_iff_rightSpecial c

/-- An occurrence of `u ++ w` at `i` contains an occurrence of `w` at `i + |u|`. -/
theorem occurrence_of_append {b : ℕ → Bool} {u w : List Bool} {i : ℕ}
    (h : ∀ j (hj : j < (u ++ w).length), b (i + j) = (u ++ w)[j]) :
    ∀ j (hj : j < w.length), b (i + u.length + j) = w[j] := by
  intro j hj
  have h1 := h (u.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at h1
  simpa [Nat.add_assoc] using h1

/-- Right-special words are closed under deleting letters on the left. -/
theorem RightSpecial.of_append {b : ℕ → Bool} {u w : List Bool} (h : RightSpecial b (u ++ w)) :
    RightSpecial b w := by
  have key : ∀ a, OccursThen b (u ++ w) a → OccursThen b w a := by
    rintro a ⟨i, hi, hia⟩
    refine ⟨i + u.length, occurrence_of_append hi, ?_⟩
    rw [Nat.add_assoc, ← List.length_append]
    exact hia
  exact ⟨key _ h.1, key _ h.2⟩

/-- `w` has left extensions `v ++ w` in `R` of every length `|v|`. -/
def Extendable (R : List Bool → Prop) (w : List Bool) : Prop :=
  ∀ m, ∃ v : List Bool, v.length = m ∧ R (v ++ w)

/-- An extendable word lies in `R` (take the empty extension). -/
theorem Extendable.mem {R : List Bool → Prop} {w : List Bool} (h : Extendable R w) : R w := by
  obtain ⟨v, hv, hrs⟩ := h 0
  rw [List.length_eq_zero_iff] at hv
  subst hv
  simpa using hrs

/-- König's step: if `R` is closed under deleting letters on the left, an extendable word stays
extendable after adding one of the two letters on the left. -/
theorem Extendable.exists_cons {R : List Bool → Prop} (hR : ∀ u w, R (u ++ w) → R w)
    {w : List Bool} (hw : Extendable R w) : ∃ a, Extendable R (a :: w) := by
  by_contra hne
  push Not at hne
  have hbad : ∀ a, ∃ m, ∀ v : List Bool, v.length = m → ¬ R (v ++ a :: w) := by
    intro a
    have := hne a
    simp only [Extendable, not_forall, not_exists, not_and] at this
    exact this
  obtain ⟨m0, hm0⟩ := hbad false
  obtain ⟨m1, hm1⟩ := hbad true
  obtain ⟨v, hv, hrs⟩ := hw (max m0 m1 + 1)
  rcases List.eq_nil_or_concat v with rfl | ⟨v', a, rfl⟩
  · simp at hv
  have hrs' : R (v' ++ a :: w) := by simpa using hrs
  have hlen : v'.length = max m0 m1 := by simp at hv; omega
  have hle0 := le_max_left m0 m1
  have hle1 := le_max_right m0 m1
  have hdrop : ∀ m, m ≤ v'.length → R (v'.drop (v'.length - m) ++ a :: w) := by
    intro m _
    apply hR (v'.take (v'.length - m))
    rw [← List.append_assoc, List.take_append_drop]
    exact hrs'
  cases a
  · exact hm0 _ (by simp only [List.length_drop]; omega) (hdrop m0 (by omega))
  · exact hm1 _ (by simp only [List.length_drop]; omega) (hdrop m1 (by omega))

/-- **König's lemma on the binary tree of words, read from the right**: if a set `R` of words is
closed under deleting letters on the left and has words of every length, there is a left-infinite
word `… x 2 x 1 x 0` all of whose suffixes `x (n - 1), …, x 1, x 0` lie in `R`. -/
theorem exists_branch {R : List Bool → Prop} (hR : ∀ u w, R (u ++ w) → R w)
    (h : ∀ n, ∃ w : List Bool, w.length = n ∧ R w) :
    ∃ x : ℕ → Bool, ∀ n, R ((List.range n).reverse.map x) := by
  classical
  have h0 : Extendable R [] := fun m => by
    obtain ⟨w, hw, hrs⟩ := h m
    exact ⟨w, hw, by simpa using hrs⟩
  obtain ⟨step, hstep⟩ : ∃ step : List Bool → List Bool,
      ∀ w, step w = decide (Extendable R (true :: w)) :: w := ⟨_, fun _ => rfl⟩
  have hext : ∀ w, Extendable R w → Extendable R (step w) := by
    intro w hw
    rw [hstep]
    by_cases ht : Extendable R (true :: w)
    · simp [ht]
    · obtain ⟨a, ha⟩ := hw.exists_cons hR
      cases a
      · simpa [ht] using ha
      · exact absurd ha ht
  have hW : ∀ n, Extendable R (step^[n] []) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hext _ ih
  obtain ⟨x, hx⟩ : ∃ x : ℕ → Bool, ∀ n, x n = decide (Extendable R (true :: step^[n] [])) :=
    ⟨_, fun _ => rfl⟩
  have hWx : ∀ n, step^[n] [] = (List.range n).reverse.map x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', hstep, List.range_succ, List.reverse_append,
        List.map_append, ← ih, ← hx]
      simp
  exact ⟨x, fun n => by rw [← hWx]; exact (hW n).mem⟩

/-- **Right-special branches**: `b` is not eventually periodic iff some left-infinite word has
all its suffixes right-special in `b`. -/
theorem not_eventuallyPeriodic_iff_exists_branch (b : ℕ → Bool) :
    ¬ EventuallyPeriodic b ↔
      ∃ x : ℕ → Bool, ∀ n, RightSpecial b ((List.range n).reverse.map x) := by
  rw [not_eventuallyPeriodic_iff_rightSpecial]
  constructor
  · exact exists_branch fun _ _ h => h.of_append
  · rintro ⟨x, hx⟩ n
    exact ⟨_, by simp, hx n⟩

/-- **Problem 1, right-special branch**: some left-infinite word `… x 2 x 1 x 0` has all its
suffixes `x (n - 1) … x 1 x 0` right-special in the center column. -/
theorem problem1_iff_right_special_branch : Rule30Prize.Problem1 ↔
    ∃ x : ℕ → Bool, ∀ n, RightSpecial c ((List.range n).reverse.map x) :=
  not_eventuallyPeriodic_iff_exists_branch c

/-! ### The tail language -/

/-- The word `w` occurs in `b` at infinitely many positions `i` followed by the letter `a`. -/
def OccursThenFrequently (b : ℕ → Bool) (w : List Bool) (a : Bool) : Prop :=
  ∃ᶠ i in Filter.atTop, (∀ j (hj : j < w.length), b (i + j) = w[j]) ∧ b (i + w.length) = a

/-- `w` is right-special in the tail language of `b`: both `w 0` and `w 1` occur in `b`
infinitely often. -/
def RecurrentRightSpecial (b : ℕ → Bool) (w : List Bool) : Prop :=
  OccursThenFrequently b w false ∧ OccursThenFrequently b w true

/-- A right-special word of the tail language is right-special. -/
theorem RecurrentRightSpecial.rightSpecial {b : ℕ → Bool} {w : List Bool}
    (h : RecurrentRightSpecial b w) : RightSpecial b w :=
  ⟨h.1.exists, h.2.exists⟩

/-- Recurrent right-special words are closed under deleting letters on the left. -/
theorem RecurrentRightSpecial.of_append {b : ℕ → Bool} {u w : List Bool}
    (h : RecurrentRightSpecial b (u ++ w)) : RecurrentRightSpecial b w := by
  have key : ∀ a, OccursThenFrequently b (u ++ w) a → OccursThenFrequently b w a := by
    intro a ha
    rw [OccursThenFrequently, Filter.frequently_atTop] at ha ⊢
    intro N
    obtain ⟨i, hi, hocc, hia⟩ := ha N
    refine ⟨i + u.length, by omega, occurrence_of_append hocc, ?_⟩
    rw [Nat.add_assoc, ← List.length_append]
    exact hia
  exact ⟨key _ h.1, key _ h.2⟩

/-- **Right-special factors of the tail language**: `b` is not eventually periodic iff for every
`n` some word `w` of length `n` has both `w 0` and `w 1` occurring infinitely often in `b`. If no
word of length `n` is, then after some time each window of length `n` is always followed by the
same letter, and `b` is eventually periodic. -/
theorem not_eventuallyPeriodic_iff_recurrentRightSpecial (b : ℕ → Bool) :
    ¬ EventuallyPeriodic b ↔
      ∀ n, ∃ w : List Bool, w.length = n ∧ RecurrentRightSpecial b w := by
  constructor
  · intro hep n
    by_contra h
    apply hep
    -- from some time on, each window `u` of length `n` is always followed by the same letter
    have hev : ∀ u : Fin n → Bool, ∃ a : Bool, ∀ᶠ i in Filter.atTop,
        (fun j : Fin n => b (i + j)) = u → b (i + n) = a := by
      intro u
      by_contra hu
      have hfreq : ∀ a, OccursThenFrequently b (List.ofFn u) (!a) := by
        intro a
        refine (Filter.not_eventually.1 (not_exists.1 hu a)).mono fun i hi => ?_
        rw [Classical.not_imp] at hi
        obtain ⟨hw, hb⟩ := hi
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [List.getElem_ofFn]
          exact congrFun hw ⟨j, by simpa using hj⟩
        · rw [List.length_ofFn]
          cases a <;> simpa using hb
      exact h ⟨List.ofFn u, List.length_ofFn, hfreq true, hfreq false⟩
    choose a ha using hev
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 ha)
    refine eventuallyPeriodic_of_determined (n := n) (T := N) fun i i' hi hi' hw => ?_
    have e : (fun j : Fin n => b (i + j)) = fun j : Fin n => b (i' + j) :=
      funext fun j => hw j j.isLt
    rw [hN i hi _ rfl, hN i' hi' _ rfl, e]
  · intro h
    refine (not_eventuallyPeriodic_iff_rightSpecial b).2 fun n => ?_
    obtain ⟨w, hw, hrs⟩ := h n
    exact ⟨w, hw, hrs.rightSpecial⟩

/-- **Problem 1, recurrent right-special factors**: for every `n` some word `w` of length `n` has
both `w 0` and `w 1` occurring infinitely often in the center column. -/
theorem problem1_iff_recurrent_right_special : Rule30Prize.Problem1 ↔
    ∀ n, ∃ w : List Bool, w.length = n ∧ RecurrentRightSpecial c w :=
  not_eventuallyPeriodic_iff_recurrentRightSpecial c

/-- **Problem 1, recurrent right-special branch**: some left-infinite word `… x 2 x 1 x 0` has all
its suffixes right-special in the tail language of the center column. -/
theorem problem1_iff_recurrent_right_special_branch : Rule30Prize.Problem1 ↔
    ∃ x : ℕ → Bool, ∀ n, RecurrentRightSpecial c ((List.range n).reverse.map x) := by
  rw [problem1_iff_recurrent_right_special]
  constructor
  · exact exists_branch fun _ _ h => h.of_append
  · rintro ⟨x, hx⟩ n
    exact ⟨_, by simp, hx n⟩

/-- The words of length `n` that occur in `b` infinitely often: the tail language of `b`. -/
def tailFactors (b : ℕ → Bool) (n : ℕ) : Set (Fin n → Bool) :=
  {w | ∃ᶠ i in Filter.atTop, (fun j : Fin n => b (i + j)) = w}

/-- **Morse–Hedlund for the tail language**: `b` is eventually periodic iff for some `n` at most
`n` words of length `n` occur in `b` infinitely often. If `b` has period `P` from `T`, the words of
length `P` that occur infinitely often occur at positions `≥ T` and so are among the `P` windows at
`T, …, T + P - 1`. Conversely, the finitely many words that occur only finitely often have a last
occurrence, so a tail of `b` has at most `n` factors of length `n`. -/
theorem eventuallyPeriodic_iff_exists_ncard_tailFactors_le (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ n, (tailFactors b n).ncard ≤ n := by
  constructor
  · rintro ⟨T, P, hP, hper⟩
    refine ⟨P, ?_⟩
    have hperk := Rule30Jen.periodic_mul hper
    have hsub : tailFactors b P ⊆
        (((Finset.range P).image fun r => fun j : Fin P => b (T + r + j)) :
          Set (Fin P → Bool)) := by
      intro w hw
      obtain ⟨i, hi, hiw⟩ := Filter.frequently_atTop.1 hw T
      rw [Finset.coe_image]
      refine ⟨(i - T) % P, Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hP)), ?_⟩
      rw [← hiw]
      funext j
      have e := hperk ((i - T) / P) (T + (i - T) % P + j) (by omega)
      have hd := Nat.div_add_mod (i - T) P
      rw [show T + (i - T) % P + j + (i - T) / P * P = i + j by
        rw [Nat.mul_comm] at hd; omega] at e
      exact e.symm
    calc (tailFactors b P).ncard
        ≤ (((Finset.range P).image fun r => fun j : Fin P => b (T + r + j)) :
            Set (Fin P → Bool)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((Finset.range P).image fun r => fun j : Fin P => b (T + r + j)).card :=
          Set.ncard_coe_finset _
      _ ≤ (Finset.range P).card := Finset.card_image_le
      _ = P := Finset.card_range P
  · rintro ⟨n, hn⟩
    -- from some time on, every window of length `n` occurs infinitely often
    have hev : ∀ u : Fin n → Bool, ∀ᶠ i in Filter.atTop,
        (fun j : Fin n => b (i + j)) = u → u ∈ tailFactors b n := by
      intro u
      by_cases hu : u ∈ tailFactors b n
      · exact Filter.Eventually.of_forall fun _ _ => hu
      · have hu' : ¬ ∃ᶠ i in Filter.atTop, (fun j : Fin n => b (i + j)) = u := hu
        exact (Filter.not_frequently.1 hu').mono fun i hi he => absurd he hi
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hev)
    apply eventuallyPeriodic_of_tail N
    rw [ShiftOrbit.eventuallyPeriodic_iff_exists_ncard_factors_le]
    refine ⟨n, le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) hn⟩
    rintro _ ⟨i, rfl⟩
    have := hN (N + i) (by omega) _ rfl
    simpa only [Nat.add_assoc] using this

/-- **Problem 1, tail complexity**: for every `n`, at least `n + 1` words of length `n` occur in
the center column infinitely often. -/
theorem problem1_iff_tail_complexity : Rule30Prize.Problem1 ↔
    ∀ n, n + 1 ≤ (tailFactors c n).ncard := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_ncard_tailFactors_le]
  push Not
  rfl

/-! ### The orbit closure in `ℕ → Bool` -/

/-- The closure of the shift orbit of `b` in `ℕ → Bool` (product topology) is infinite iff `b`
is not eventually periodic. -/
theorem infinite_closure_shifts_iff (b : ℕ → Bool) :
    (closure (Set.range fun n : ℕ => fun t => b (n + t))).Infinite ↔ ¬ EventuallyPeriodic b := by
  rw [ShiftOrbit.eventuallyPeriodic_iff_finite_shifts]
  constructor
  · intro h hfin
    exact h (by rw [hfin.isClosed.closure_eq]; exact hfin)
  · intro h
    exact Set.Infinite.mono subset_closure h

/-- **Problem 1, orbit closure**: the closure of `{σⁿ c : n ∈ ℕ}` in `ℕ → Bool` is infinite. -/
theorem problem1_iff_orbit_closure_infinite : Rule30Prize.Problem1 ↔
    (closure (Set.range fun n : ℕ => fun t => c (n + t))).Infinite :=
  (infinite_closure_shifts_iff c).symm

/-- **Problem 1, accumulation point**: the shift orbit of `c` has an accumulation point in
`ℕ → Bool`. -/
theorem problem1_iff_exists_accPt : Rule30Prize.Problem1 ↔
    ∃ x : ℕ → Bool, AccPt x (Filter.principal (Set.range fun n : ℕ => fun t => c (n + t))) := by
  rw [ShiftOrbit.problem1_iff_infinite_shifts]
  exact ⟨fun h => h.exists_accPt_principal, fun ⟨_, hx⟩ => Set.Infinite.of_accPt hx⟩

/-! ### The omega-limit set -/

/-- The first `n` letters of `x`, as a word `Fin n → Bool`. -/
def prefixWord (n : ℕ) (x : ℕ → Bool) : Fin n → Bool := fun j => x j

/-- Taking the first `n` letters is continuous for the product topology. -/
theorem continuous_prefixWord (n : ℕ) : Continuous (prefixWord n) :=
  continuous_pi fun j => continuous_apply (j : ℕ)

/-- The omega-limit set of `b` under the shift lies in the closure of its orbit. -/
theorem omegaLimit_subset_closure_shifts (b : ℕ → Bool) :
    omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b} ⊆
      closure (Set.range fun n : ℕ => fun t => b (n + t)) := by
  refine (omegaLimit_subset_closure_image2 _ _ _ Filter.univ_mem).trans (closure_mono ?_)
  rintro _ ⟨n, -, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨n, rfl⟩

/-- A finite omega-limit set forces eventual periodicity. Let `K` be its size. Eventually every
shift of `b` lies in the open set of sequences whose first `K` letters are those of a point of
the omega-limit set (`eventually_mapsTo_of_isOpen_of_omegaLimit_subset`, by compactness). So a
tail of `b` has at most `K` factors of length `K`, and Morse–Hedlund applies. -/
theorem eventuallyPeriodic_of_finite_omegaLimit {b : ℕ → Bool}
    (h : (omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b}).Finite) :
    EventuallyPeriodic b := by
  set Ω := omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b}
  have hV : IsOpen (prefixWord Ω.ncard ⁻¹' (prefixWord Ω.ncard '' Ω)) :=
    (isOpen_discrete _).preimage (continuous_prefixWord _)
  have hev := eventually_mapsTo_of_isOpen_of_omegaLimit_subset Filter.atTop
    (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b} hV
    (Set.subset_preimage_image (prefixWord Ω.ncard) Ω)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  apply eventuallyPeriodic_of_tail N
  rw [ShiftOrbit.eventuallyPeriodic_iff_exists_ncard_factors_le]
  refine ⟨Ω.ncard, ?_⟩
  have hsub : ShiftOrbit.factors (fun t => b (N + t)) Ω.ncard ⊆ prefixWord Ω.ncard '' Ω := by
    rintro _ ⟨i, rfl⟩
    have hmem : prefixWord Ω.ncard (fun t => b (N + i + t)) ∈ prefixWord Ω.ncard '' Ω :=
      hN (N + i) (by omega) (Set.mem_singleton b)
    obtain ⟨z, hz, hzeq⟩ := hmem
    refine ⟨z, hz, ?_⟩
    rw [hzeq]
    funext j
    simp only [prefixWord, Nat.add_assoc]
  calc (ShiftOrbit.factors (fun t => b (N + t)) Ω.ncard).ncard
      ≤ (prefixWord Ω.ncard '' Ω).ncard := Set.ncard_le_ncard hsub (h.image _)
    _ ≤ Ω.ncard := Set.ncard_image_le h

/-- The omega-limit set of `b` under the shift is infinite iff `b` is not eventually periodic. -/
theorem infinite_omegaLimit_iff (b : ℕ → Bool) :
    (omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b}).Infinite ↔
      ¬ EventuallyPeriodic b := by
  constructor
  · intro h hep
    apply h
    have hfin := (ShiftOrbit.eventuallyPeriodic_iff_finite_shifts b).1 hep
    refine Set.Finite.subset ?_ (omegaLimit_subset_closure_shifts b)
    rw [hfin.isClosed.closure_eq]
    exact hfin
  · exact fun h hfin => h (eventuallyPeriodic_of_finite_omegaLimit hfin)

/-- **Problem 1, omega-limit set**: the omega-limit set of `c` under the shift
`n ↦ (x ↦ fun t => x (n + t))` on `ℕ → Bool` is infinite. -/
theorem problem1_iff_omegaLimit_infinite : Rule30Prize.Problem1 ↔
    (omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {c}).Infinite :=
  (infinite_omegaLimit_iff c).symm

/-! ### Non-periodic points of the omega-limit set -/

/-- The one-step shift is continuous on `ℕ → Bool`. -/
theorem continuous_shift : Continuous ShiftOrbit.shift :=
  continuous_pi fun t => continuous_apply (t + 1)

/-- A point of period `q` under the shift repeats with period `q`. -/
theorem apply_add_of_isPeriodicPt {x : ℕ → Bool} {q : ℕ}
    (h : Function.IsPeriodicPt ShiftOrbit.shift q x) (t : ℕ) : x (q + t) = x t := by
  have h' : ShiftOrbit.shift^[q] x = x := h
  rw [ShiftOrbit.shift_iterate] at h'
  exact congrFun h' t

/-- A point of period `p` repeats with every multiple of `p`. -/
theorem apply_mul_add_of_isPeriodicPt {x : ℕ → Bool} {p : ℕ}
    (h : Function.IsPeriodicPt ShiftOrbit.shift p x) (k t : ℕ) : x (p * k + t) = x t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show p * (k + 1) + t = p + (p * k + t) by rw [Nat.mul_add, Nat.mul_one]; omega,
      apply_add_of_isPeriodicPt h, ih]

/-- Two sequences with periods `q > 0` and `p > 0` that agree on the first `p + q` letters are
equal. -/
theorem eq_of_agree_of_periodic {x y : ℕ → Bool} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hx : ∀ t, x (q + t) = x t) (hy : ∀ t, y (p + t) = y t) (h : ∀ i < p + q, x i = y i) :
    x = y := by
  funext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < p + q
    · exact h i hi
    · have e1 : y i = x (i - p) := by
        rw [ih (i - p) (by omega), ← hy (i - p), show p + (i - p) = i by omega]
      have e2 : x i = x (i - p) := by
        calc x i = x (i - q) := by rw [← hx (i - q), show q + (i - q) = i by omega]
          _ = y (i - q) := ih (i - q) (by omega)
          _ = y (i - q - p) := by rw [← hy (i - q - p), show p + (i - q - p) = i - q by omega]
          _ = x (i - q - p) := (ih (i - q - p) (by omega)).symm
          _ = x (i - p) := by rw [← hx (i - q - p), show q + (i - q - p) = i - p by omega]
      rw [e2, e1]

/-- There are only finitely many points of period `q > 0`: such a point is fixed by its first
`q` letters. -/
theorem finite_setOf_isPeriodicPt {q : ℕ} (hq : 0 < q) :
    {x : ℕ → Bool | Function.IsPeriodicPt ShiftOrbit.shift q x}.Finite := by
  refine Set.Finite.of_finite_image (f := prefixWord q) (Set.toFinite _) ?_
  intro x hx x' hx' he
  funext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < q
    · exact congrFun he ⟨i, hi⟩
    · have e1 := apply_add_of_isPeriodicPt hx (i - q)
      have e2 := apply_add_of_isPeriodicPt hx' (i - q)
      rw [show q + (i - q) = i by omega] at e1 e2
      rw [e1, e2]
      exact ih (i - q) (by omega)

/-- The sequences that agree with `y` on `[0, m)` form a neighborhood of `y`. -/
theorem cylinder_mem_nhds (y : ℕ → Bool) (m : ℕ) :
    {x : ℕ → Bool | ∀ i < m, x i = y i} ∈ nhds y := by
  have e : {x : ℕ → Bool | ∀ i < m, x i = y i} = prefixWord m ⁻¹' {prefixWord m y} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff, prefixWord]
    exact ⟨fun h j => h j j.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [e]
  exact ((isOpen_discrete _).preimage (continuous_prefixWord m)).mem_nhds rfl

/-- Every neighborhood of `y` contains the sequences that agree with `y` on some `[0, m)`. -/
theorem exists_cylinder_subset {y : ℕ → Bool} {U : Set (ℕ → Bool)} (hU : U ∈ nhds y) :
    ∃ m, {x : ℕ → Bool | ∀ i < m, x i = y i} ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨m, hm⟩ := hI.bddAbove
  refine ⟨m + 1, fun x hx => hsub fun i hi => ?_⟩
  have e : x i = y i := hx i (Nat.lt_succ_of_le (hm hi))
  rw [e]
  exact mem_of_mem_nhds (ht i)

/-- The defect argument. Let `Ω` be a closed shift-invariant set of periodic points and `y` an
accumulation point of `Ω`, of period `p`. Points `x ∈ Ω` close to `y` differ from `y` somewhere;
shifting `x` by a multiple of `p` moves its first difference into `[m, m + p)`. These shifted
points have arbitrarily large periods, so they are infinitely many, and they accumulate at a point
of `Ω` that agrees with `y` on `[0, m)` but is not `y`. So `y` is an accumulation point of the
accumulation points of `Ω`. -/
theorem accPt_derivedSet_of_periodic {Ω : Set (ℕ → Bool)} (hc : IsClosed Ω)
    (hinv : ∀ x ∈ Ω, ShiftOrbit.shift x ∈ Ω)
    (hper : ∀ x ∈ Ω, x ∈ Function.periodicPts ShiftOrbit.shift) {y : ℕ → Bool}
    (hy : AccPt y (Filter.principal Ω)) : AccPt y (Filter.principal (derivedSet Ω)) := by
  have hyΩ : y ∈ Ω := (isClosed_iff_derivedSet_subset Ω).1 hc hy
  obtain ⟨p, hp, hpy⟩ := Function.mem_periodicPts.1 (hper y hyΩ)
  have hiter : ∀ n, ∀ x ∈ Ω, ShiftOrbit.shift^[n] x ∈ Ω := by
    intro n
    induction n with
    | zero => exact fun x hx => hx
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hinv _ (ih x hx)
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨m, hm⟩ := exists_cylinder_subset hU
  -- the points of `Ω` that agree with `y` on `[0, m)` and differ from it on `[m, m + p)`
  set S : Set (ℕ → Bool) := Ω ∩ prefixWord (m + p) ⁻¹'
    {w | (∀ i : Fin (m + p), (i : ℕ) < m → w i = y i) ∧ ∃ i, w i ≠ y i}
  have hSc : IsClosed S := hc.inter ((isClosed_discrete _).preimage (continuous_prefixWord _))
  have hSinf : S.Infinite := by
    intro hfin
    -- a common bound `Q` for the least periods of the points of `S`
    obtain ⟨Q, hQ⟩ : ∃ Q, ∀ z ∈ S, ∃ r, 0 < r ∧ r ≤ Q ∧
        Function.IsPeriodicPt ShiftOrbit.shift r z := by
      refine ⟨hfin.toFinset.sup (Function.minimalPeriod ShiftOrbit.shift), fun z hz => ?_⟩
      exact ⟨_, Function.minimalPeriod_pos_of_mem_periodicPts (hper z hz.1),
        Finset.le_sup (hfin.mem_toFinset.2 hz), Function.isPeriodicPt_minimalPeriod _ _⟩
    -- a point `x ∈ Ω`, `x ≠ y`, that agrees with `y` on `[0, m + p + Q)`
    obtain ⟨x, ⟨hxcyl, hxΩ⟩, hxy⟩ := (accPt_iff_nhds.1 hy) _ (cylinder_mem_nhds y (m + p + Q))
    have hex : ∃ d, x d ≠ y d := by
      by_contra hall
      push Not at hall
      exact hxy (funext hall)
    classical
    set d := Nat.find hex
    have hdne : x d ≠ y d := Nat.find_spec hex
    have hbefore : ∀ i < d, x i = y i := fun i hi => by
      have := Nat.find_min hex hi
      push Not at this
      exact this
    have hdge : m + p + Q ≤ d := by
      by_contra hlt
      push Not at hlt
      exact hdne (hxcyl d hlt)
    -- shift `x` by a multiple `j` of `p`, moving the first difference to `d - j ∈ [m, m + p)`
    set j := p * ((d - m) / p) with hj
    have hjle : j ≤ d - m := Nat.mul_div_le (d - m) p
    have hdj : d - j = m + (d - m) % p := by
      have := Nat.div_add_mod (d - m) p
      omega
    have hmodlt : (d - m) % p < p := Nat.mod_lt _ hp
    set z := ShiftOrbit.shift^[j] x with hz
    have hzapp : ∀ t, z t = x (j + t) := fun t => by rw [hz, ShiftOrbit.shift_iterate]
    have hzS : z ∈ S := by
      refine ⟨hiter j x hxΩ, fun i hi => ?_, ⟨d - j, by omega⟩, ?_⟩
      · show z i = y i
        rw [hzapp, hbefore (j + i) (by omega), hj, apply_mul_add_of_isPeriodicPt hpy]
      · show z (d - j) ≠ y (d - j)
        rw [hzapp, show j + (d - j) = d by omega]
        intro h
        apply hdne
        rw [h, ← apply_mul_add_of_isPeriodicPt hpy ((d - m) / p) (d - j), ← hj,
          show j + (d - j) = d by omega]
    obtain ⟨r, hr, hrQ, hrz⟩ := hQ z hzS
    -- `x` is in the periodic orbit of `z`, so it has period `r` too
    obtain ⟨r₀, hr₀, hr₀x⟩ := Function.mem_periodicPts.1 (hper x hxΩ)
    have hxr : Function.IsPeriodicPt ShiftOrbit.shift r x := by
      have e : ShiftOrbit.shift^[r₀ * j - j] z = x := by
        rw [hz, ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left j hr₀)]
        exact hr₀x.mul_const j
      rw [← e]
      exact hrz.apply_iterate _
    -- so `x = y`, a contradiction
    exact hxy (eq_of_agree_of_periodic hp hr (apply_add_of_isPeriodicPt hxr)
      (apply_add_of_isPeriodicPt hpy) fun i hi => hxcyl i (by omega))
  -- an accumulation point of `S`
  obtain ⟨z, hzS, hzacc⟩ := hSinf.exists_accPt_of_subset_isCompact hSc.isCompact subset_rfl
  refine ⟨z, ⟨hm fun i hi => ?_, hzacc.mono (Filter.principal_mono.2 Set.inter_subset_left)⟩, ?_⟩
  · exact hzS.2.1 ⟨i, by omega⟩ hi
  · rintro rfl
    obtain ⟨i, hi⟩ := hzS.2.2
    exact hi rfl

/-- **A closed shift-invariant set of periodic points is finite.** Otherwise its accumulation
points form a nonempty compact set without isolated points (`accPt_derivedSet_of_periodic`),
which is a countable union of the finite sets of points of period `q`; Baire's theorem gives one
of these sets an interior point, and that point is isolated. -/
theorem finite_of_forall_periodic {Ω : Set (ℕ → Bool)} (hc : IsClosed Ω)
    (hinv : ∀ x ∈ Ω, ShiftOrbit.shift x ∈ Ω)
    (hper : ∀ x ∈ Ω, x ∈ Function.periodicPts ShiftOrbit.shift) : Ω.Finite := by
  by_contra hinf
  have hYc : IsClosed (derivedSet Ω) := isClosed_derivedSet Ω
  obtain ⟨y₀, hy₀⟩ := (show Ω.Infinite from hinf).exists_accPt_principal
  have hYΩ : derivedSet Ω ⊆ Ω := (isClosed_iff_derivedSet_subset Ω).1 hc
  have : CompactSpace (derivedSet Ω) := isCompact_iff_compactSpace.mp hYc.isCompact
  have : Nonempty (derivedSet Ω) := ⟨⟨y₀, hy₀⟩⟩
  obtain ⟨q, hq⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun q : ℕ => {y : derivedSet Ω |
      Function.IsPeriodicPt ShiftOrbit.shift (q + 1) (y : ℕ → Bool)})
    (fun q => isClosed_eq ((continuous_shift.iterate (q + 1)).comp continuous_subtype_val)
      continuous_subtype_val)
    (by
      refine Set.eq_univ_of_forall fun y => ?_
      obtain ⟨n, hn, hny⟩ := Function.mem_periodicPts.1 (hper y (hYΩ y.2))
      refine Set.mem_iUnion.2 ⟨n - 1, ?_⟩
      show Function.IsPeriodicPt ShiftOrbit.shift (n - 1 + 1) (y : ℕ → Bool)
      rwa [Nat.sub_add_cancel hn])
  obtain ⟨y, hy⟩ := hq
  set U := interior {y : derivedSet Ω |
    Function.IsPeriodicPt ShiftOrbit.shift (q + 1) (y : ℕ → Bool)}
  have hUfin : U.Finite := by
    refine Set.Finite.subset ?_ interior_subset
    exact (finite_setOf_isPeriodicPt (Nat.succ_pos q)).preimage Subtype.val_injective.injOn
  -- `{y}` is open in the derived set
  have hyopen : IsOpen ({y} : Set (derivedSet Ω)) := by
    have e : ({y} : Set (derivedSet Ω)) = U ∩ (U \ {y})ᶜ := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
        not_and, not_not]
      constructor
      · rintro rfl
        exact ⟨hy, fun _ => rfl⟩
      · rintro ⟨hw, h⟩
        exact h hw
    rw [e]
    exact isOpen_interior.inter (hUfin.sdiff.isClosed.isOpen_compl)
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hyopen
  have hyV : (y : ℕ → Bool) ∈ V := by
    have : y ∈ Subtype.val ⁻¹' V := by rw [hV]; rfl
    exact this
  obtain ⟨w, ⟨hwV, hwY⟩, hwy⟩ := (accPt_iff_nhds.1
    (accPt_derivedSet_of_periodic hc hinv hper y.2)) V (hVo.mem_nhds hyV)
  have : (⟨w, hwY⟩ : derivedSet Ω) ∈ Subtype.val ⁻¹' V := hwV
  rw [hV, Set.mem_singleton_iff] at this
  exact hwy (congrArg Subtype.val this)

/-- The omega-limit set of `b` is mapped into itself by the shift. -/
theorem shift_mem_omegaLimit {b z : ℕ → Bool}
    (hz : z ∈ omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b}) :
    ShiftOrbit.shift z ∈
      omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b} := by
  rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hz ⊢
  have h1 := hz.continuousAt_comp continuous_shift.continuousAt
  have e : (ShiftOrbit.shift ∘ fun (n : ℕ) => fun t => b (n + t)) =
      (fun (n : ℕ) => fun t => b (n + t)) ∘ (· + 1) := by
    funext n t
    show b (n + (t + 1)) = b (n + 1 + t)
    rw [show n + (t + 1) = n + 1 + t by omega]
  rw [e] at h1
  exact h1.of_comp (Filter.tendsto_add_atTop_nat 1)

/-- If `b` is eventually periodic, every point of its omega-limit set is periodic. -/
theorem mem_periodicPts_of_mem_omegaLimit {b : ℕ → Bool} (h : EventuallyPeriodic b)
    {z : ℕ → Bool}
    (hz : z ∈ omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b}) :
    z ∈ Function.periodicPts ShiftOrbit.shift := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hclosed : IsClosed {x : ℕ → Bool | ShiftOrbit.shift^[P] x = x} :=
    isClosed_eq (continuous_shift.iterate P) continuous_id
  have hsub := omegaLimit_subset_closure_image2 Filter.atTop
    (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b} (Filter.Ici_mem_atTop T)
  refine Function.mk_mem_periodicPts hP (closure_minimal ?_ hclosed (hsub hz))
  rintro _ ⟨n, hn, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  show ShiftOrbit.shift^[P] (fun t => x (n + t)) = fun t => x (n + t)
  rw [ShiftOrbit.shift_iterate]
  funext t
  show x (n + (P + t)) = x (n + t)
  rw [show n + (P + t) = n + t + P by omega]
  exact hper (n + t) (by simp only [Set.mem_Ici] at hn; omega)

/-- **Non-periodic points of the omega-limit set**: `b` is not eventually periodic iff its
omega-limit set under the shift contains a point that is not periodic. -/
theorem not_eventuallyPeriodic_iff_exists_nonperiodic (b : ℕ → Bool) :
    ¬ EventuallyPeriodic b ↔
      ∃ z ∈ omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {b},
        z ∉ Function.periodicPts ShiftOrbit.shift := by
  constructor
  · intro hep
    by_contra hall
    push Not at hall
    exact (infinite_omegaLimit_iff b).2 hep
      (finite_of_forall_periodic (isClosed_omegaLimit _ _ _) (fun x hx => shift_mem_omegaLimit hx)
        hall)
  · rintro ⟨z, hz, hnp⟩ hep
    exact hnp (mem_periodicPts_of_mem_omegaLimit hep hz)

/-- **Problem 1, non-periodic limit point**: the omega-limit set of the center column under the
shift contains a point that is not periodic. -/
theorem problem1_iff_omegaLimit_not_periodic : Rule30Prize.Problem1 ↔
    ∃ z ∈ omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t)) {c},
      z ∉ Function.periodicPts ShiftOrbit.shift :=
  not_eventuallyPeriodic_iff_exists_nonperiodic c

/-! ### Finite automata -/

/-- The state of the automaton with start state `s₀` and transition `δ` after it has read
`b 0, b 1, …, b (n - 1)`. -/
def readState {σ : Type*} (b : ℕ → Bool) (s₀ : σ) (δ : σ → Bool → σ) : ℕ → σ
  | 0 => s₀
  | n + 1 => δ (readState b s₀ δ n) (b n)

/-- An automaton that ignores its input runs autonomously. -/
theorem readState_const {σ : Type*} (b : ℕ → Bool) (s₀ : σ) (F : σ → σ) (n : ℕ) :
    readState b s₀ (fun s _ => F s) n = F^[n] s₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

/-- A counter on `Fin (T + P)`: count up, and from `T + P - 1` jump back to `T`. -/
def counterStep {T P : ℕ} (hP : 0 < P) (s : Fin (T + P)) : Fin (T + P) :=
  if h : s.val + 1 < T + P then ⟨s.val + 1, h⟩ else ⟨T, by omega⟩

/-- One step of the counter keeps it in step with `b`: if the shift of `b` by the counter value
`s` is the shift by `n`, the shift by the next value is the shift by `n + 1`. -/
theorem counterStep_shift {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (hper : ∀ t, T ≤ t → b (t + P) = b t) {s : Fin (T + P)} {n : ℕ}
    (hs : ∀ t, b (s + t) = b (n + t)) (t : ℕ) : b (counterStep hP s + t) = b (n + 1 + t) := by
  unfold counterStep
  split_ifs with h
  · show b (s.val + 1 + t) = b (n + 1 + t)
    rw [Nat.add_assoc, hs, ← Nat.add_assoc]
  · have := s.isLt
    show b (T + t) = b (n + 1 + t)
    rw [← hper (T + t) (by omega), show T + t + P = s.val + (1 + t) by omega, hs,
      ← Nat.add_assoc]

/-- If `b` has transient `T` and period `P`, the counter started at `0` reads `b` correctly. -/
theorem counterStep_iterate {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (hper : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) :
    b ((counterStep (T := T) hP)^[n] ⟨0, by omega⟩) = b n := by
  have key : ∀ n t, b ((counterStep (T := T) hP)^[n] ⟨0, by omega⟩ + t) = b (n + t) := by
    intro n
    induction n with
    | zero => intro t; rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact counterStep_shift hP hper ih
  simpa using key n 0

/-- A sequence produced from some time on by a finite autonomous machine is eventually
periodic: the states repeat by pigeonhole. -/
theorem eventuallyPeriodic_of_generator {σ : Type*} [Finite σ] {b : ℕ → Bool} {s₀ : σ}
    {F : σ → σ} {g : σ → Bool} {T : ℕ} (h : ∀ t, T ≤ t → b t = g (F^[t] s₀)) :
    EventuallyPeriodic b := by
  have key : ∀ i j, i < j → F^[i] s₀ = F^[j] s₀ → EventuallyPeriodic b := by
    intro i j hij he
    refine ⟨max T i, j - i, by omega, fun t ht => ?_⟩
    have hTt : T ≤ t := le_trans (le_max_left _ _) ht
    have hit : i ≤ t := le_trans (le_max_right _ _) ht
    rw [h t hTt, h (t + (j - i)) (by omega), show t + (j - i) = t - i + j by omega,
      Function.iterate_add_apply, ← he, ← Function.iterate_add_apply, Nat.sub_add_cancel hit]
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => F^[n] s₀)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt he
  · exact key j i hlt he.symm

/-- **Finite generators**: `b` is eventually periodic iff, from some time on, it is the output
`g (F^[t] s₀)` of a finite autonomous machine. -/
theorem eventuallyPeriodic_iff_finite_generator (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ (σ : Type) (_ : Finite σ) (s₀ : σ) (F : σ → σ) (g : σ → Bool) (T : ℕ),
      ∀ t, T ≤ t → b t = g (F^[t] s₀) := by
  constructor
  · rintro ⟨T, P, hP, hper⟩
    exact ⟨Fin (T + P), inferInstance, ⟨0, by omega⟩, counterStep hP, fun s => b s, 0,
      fun t _ => (counterStep_iterate hP hper t).symm⟩
  · rintro ⟨σ, _, s₀, F, g, T, h⟩
    exact eventuallyPeriodic_of_generator h

/-- **Problem 1, no finite generator**: no finite autonomous machine (states `σ`, start `s₀`,
transition `F`, output `g`) produces the center column from some time on. -/
theorem problem1_iff_no_finite_generator : Rule30Prize.Problem1 ↔
    ¬ ∃ (σ : Type) (_ : Finite σ) (s₀ : σ) (F : σ → σ) (g : σ → Bool) (T : ℕ),
      ∀ t, T ≤ t → c t = g (F^[t] s₀) :=
  (eventuallyPeriodic_iff_finite_generator c).not

/-- A finite automaton that reads `b` and, from time `N` on, always guesses the next letter
correctly forces `b` to be eventually periodic: feeding it its own guesses makes it autonomous. -/
theorem eventuallyPeriodic_of_eventually_predicted {σ : Type*} [Finite σ] {b : ℕ → Bool}
    {s₀ : σ} {δ : σ → Bool → σ} {g : σ → Bool} {N : ℕ}
    (h : ∀ n, N ≤ n → g (readState b s₀ δ n) = b n) : EventuallyPeriodic b := by
  have hstate : ∀ k, readState b s₀ δ (N + k) =
      (fun s => δ s (g s))^[k] (readState b s₀ δ N) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih, ← Nat.add_assoc]
      show δ (readState b s₀ δ (N + k)) (b (N + k)) =
        δ (readState b s₀ δ (N + k)) (g (readState b s₀ δ (N + k)))
      rw [h (N + k) (by omega)]
  apply eventuallyPeriodic_of_tail N
  refine eventuallyPeriodic_of_generator (T := 0) (s₀ := readState b s₀ δ N)
    (F := fun s => δ s (g s)) (g := g) fun k _ => ?_
  show b (N + k) = _
  rw [← hstate k, h (N + k) (by omega)]

/-- **Finite-state unpredictability**: `b` is not eventually periodic iff every finite automaton
that reads `b` and guesses each next letter (`g` of its state) guesses wrong infinitely often. -/
theorem not_eventuallyPeriodic_iff_unpredictable (b : ℕ → Bool) :
    ¬ EventuallyPeriodic b ↔
      ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
        ∀ N, ∃ n, N ≤ n ∧ g (readState b s₀ δ n) ≠ b n := by
  constructor
  · intro hep σ _ s₀ δ g N
    by_contra hne
    push Not at hne
    exact hep (eventuallyPeriodic_of_eventually_predicted hne)
  · intro h hep
    obtain ⟨T, P, hP, hper⟩ := hep
    obtain ⟨n, -, hn⟩ := h (Fin (T + P)) ⟨0, by omega⟩ (fun s _ => counterStep hP s)
      (fun s => b s) 0
    apply hn
    rw [readState_const]
    exact counterStep_iterate hP hper n

/-- **Problem 1, finite-state unpredictability**: every finite automaton that reads the center
column and guesses each next cell from its state guesses wrong infinitely often. -/
theorem problem1_iff_unpredictable : Rule30Prize.Problem1 ↔
    ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
      ∀ N, ∃ n, N ≤ n ∧ g (readState c s₀ δ n) ≠ c n :=
  not_eventuallyPeriodic_iff_unpredictable c

/-- **Feedback shift registers**: `b` is eventually periodic iff from some time on each letter is
a fixed Boolean function of the `k` letters before it. -/
theorem eventuallyPeriodic_iff_feedback (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ (k : ℕ) (f : (Fin k → Bool) → Bool) (T : ℕ),
      ∀ t, T ≤ t → b (t + k) = f fun j => b (t + j) := by
  constructor
  · rintro ⟨T, P, hP, hper⟩
    exact ⟨P, fun w => w ⟨0, hP⟩, T, fun t ht => by simpa using hper t ht⟩
  · rintro ⟨k, f, T, h⟩
    refine eventuallyPeriodic_of_determined (n := k) (T := T) fun i i' hi hi' hw => ?_
    rw [h i hi, h i' hi']
    congr 1
    funext j
    exact hw j j.isLt

/-- **Problem 1, no feedback shift register**: no (nonlinear) feedback shift register, of any
length `k` and with any feedback function `f`, produces the center column from some time on. -/
theorem problem1_iff_no_feedback_shift_register : Rule30Prize.Problem1 ↔
    ¬ ∃ (k : ℕ) (f : (Fin k → Bool) → Bool) (T : ℕ),
      ∀ t, T ≤ t → c (t + k) = f fun j => c (t + j) :=
  (eventuallyPeriodic_iff_feedback c).not

/-- The automaton state after reading `n` letters is `DFA.eval` of the prefix of length `n`. -/
theorem readState_eq_eval {σ : Type*} (b : ℕ → Bool) (M : DFA Bool σ) (n : ℕ) :
    readState b M.start M.step n = M.eval ((List.range n).map b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, DFA.eval_append_singleton, ← ih]
    rfl

/-- **Regular predictors**: `b` is not eventually periodic iff every regular language `L` errs
infinitely often as a predictor, where `L` predicts `b n = true` exactly when the prefix
`b 0, …, b (n - 1)` lies in `L`. -/
theorem not_eventuallyPeriodic_iff_regular (b : ℕ → Bool) :
    ¬ EventuallyPeriodic b ↔ ∀ L : Language Bool, L.IsRegular →
      ∀ N, ∃ n, N ≤ n ∧ ((List.range n).map b ∈ L ↔ b n = false) := by
  classical
  constructor
  · rintro hep L ⟨σ, _, M, rfl⟩ N
    obtain ⟨n, hn, hne⟩ := (not_eventuallyPeriodic_iff_unpredictable b).1 hep σ M.start M.step
      (fun s => decide (s ∈ M.accept)) N
    refine ⟨n, hn, ?_⟩
    rw [readState_eq_eval] at hne
    rw [DFA.mem_accepts]
    cases hb : b n <;> simp_all
  · intro h hep
    obtain ⟨T, P, hP, hper⟩ := hep
    let M : DFA Bool (Fin (T + P)) :=
      ⟨fun s _ => counterStep hP s, ⟨0, by omega⟩, {s | b s = true}⟩
    obtain ⟨n, -, hn⟩ := h M.accepts ⟨Fin (T + P), inferInstance, M, rfl⟩ 0
    rw [DFA.mem_accepts, ← readState_eq_eval] at hn
    have e : readState b M.start M.step n = (counterStep hP)^[n] ⟨0, by omega⟩ :=
      readState_const b _ (counterStep hP) n
    rw [e] at hn
    have hc := counterStep_iterate hP hper n
    change b ((counterStep hP)^[n] ⟨0, by omega⟩) = true ↔ b n = false at hn
    rw [hc] at hn
    cases hb : b n <;> simp_all

/-- **Problem 1, regular predictors**: for every regular language `L` over `{0, 1}` there are
infinitely many `n` at which the prediction "`c n = 1` iff `c 0 … c (n - 1) ∈ L`" is wrong. -/
theorem problem1_iff_no_regular_predictor : Rule30Prize.Problem1 ↔
    ∀ L : Language Bool, L.IsRegular →
      ∀ N, ∃ n, N ≤ n ∧ ((List.range n).map c ∈ L ↔ c n = false) :=
  not_eventuallyPeriodic_iff_regular c

/-! ### Maximum-order complexity -/

/-- An eventually periodic sequence is generated from the start by a feedback shift register: with
transient `T` and period `P`, the window of length `T + P` at `i` determines the letter after it,
since that letter and the one at `i + T` lie in the periodic part at the same phase. -/
theorem windowDetermined_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ m, ∀ i j, (∀ k < m, b (i + k) = b (j + k)) → b (i + m) = b (j + m) := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T + P, fun i j hw => ?_⟩
  rw [show i + (T + P) = i + T + P by omega, show j + (T + P) = j + T + P by omega,
    hper _ (by omega), hper _ (by omega)]
  exact hw T (by omega)

/-- **Feedback from the start**: `b` is eventually periodic iff some feedback shift register
generates it from position `0`. -/
theorem eventuallyPeriodic_iff_feedback_from_zero (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ (m : ℕ) (F : (Fin m → Bool) → Bool),
      ∀ i, b (i + m) = F fun k => b (i + k) := by
  classical
  constructor
  · intro h
    obtain ⟨m, hm⟩ := windowDetermined_of_eventuallyPeriodic h
    -- the feedback reads the successor of any position with the given window
    refine ⟨m, fun w => if hw : ∃ i, ∀ k : Fin m, b (i + k) = w k then b (hw.choose + m) else false,
      fun i => ?_⟩
    have hex : ∃ i', ∀ k : Fin m, b (i' + k) = b (i + k) := ⟨i, fun _ => rfl⟩
    simp only [dite_eq_left hex]
    exact hm i hex.choose fun k hk => (hex.choose_spec ⟨k, hk⟩).symm
  · rintro ⟨m, F, hF⟩
    exact (eventuallyPeriodic_iff_feedback b).2 ⟨m, F, 0, fun t _ => hF t⟩

/-- Inside the prefix of length `n`, equal windows of length `m` have equal successors. -/
def PrefixConsistent (b : ℕ → Bool) (n m : ℕ) : Prop :=
  ∀ i j, i + m < n → j + m < n → (∀ k < m, b (i + k) = b (j + k)) → b (i + m) = b (j + m)

theorem prefixConsistent_self (b : ℕ → Bool) (n : ℕ) : PrefixConsistent b n n :=
  fun i _ hi _ _ => absurd hi (by omega)

/-- Consistency at order `m` gives consistency at every larger order. -/
theorem PrefixConsistent.mono {b : ℕ → Bool} {n m m' : ℕ} (h : PrefixConsistent b n m)
    (hm : m ≤ m') : PrefixConsistent b n m' := by
  intro i j hi hj hw
  have := h (i + (m' - m)) (j + (m' - m)) (by omega) (by omega) fun k hk => by
    rw [Nat.add_assoc, Nat.add_assoc]
    exact hw _ (by omega)
  rwa [show i + (m' - m) + m = i + m' by omega, show j + (m' - m) + m = j + m' by omega] at this

/-- **Maximum-order complexity** of the prefix of length `n`: the length of the shortest feedback
shift register that generates it, the least `m` at which the prefix is consistent. -/
noncomputable def maxOrderComplexity (b : ℕ → Bool) (n : ℕ) : ℕ := by
  classical exact Nat.find ⟨n, prefixConsistent_self b n⟩

theorem lt_maxOrderComplexity_iff (b : ℕ → Bool) (n m : ℕ) :
    m < maxOrderComplexity b n ↔ ¬ PrefixConsistent b n m := by
  classical
  unfold maxOrderComplexity
  rw [Nat.lt_find_iff]
  constructor
  · intro h hc
    exact h m le_rfl hc
  · intro h m' hm' hc
    exact h (hc.mono hm')

/-- **Problem 1, maximum-order complexity**: Problem 1 holds iff the maximum-order
complexity of the prefixes of the center column tends to infinity. -/
theorem problem1_iff_maxOrderComplexity_tendsto : Rule30Prize.Problem1 ↔
    Filter.Tendsto (maxOrderComplexity c) Filter.atTop Filter.atTop := by
  rw [problem1_iff_not_eventuallyPeriodic]
  constructor
  · intro hne
    refine Filter.tendsto_atTop.2 fun m => ?_
    -- some equal windows of length `m` have different successors
    have hnd : ¬ ∀ i j, (∀ k < m, c (i + k) = c (j + k)) → c (i + m) = c (j + m) :=
      fun hd => hne (eventuallyPeriodic_of_determined (n := m) (T := 0) fun i j _ _ hw => hd i j hw)
    push Not at hnd
    obtain ⟨i, j, hw, hne'⟩ := hnd
    refine Filter.eventually_atTop.2 ⟨i + j + m + 1, fun n hn => ?_⟩
    by_contra hlt
    push Not at hlt
    have hc : PrefixConsistent c n m := by
      by_contra hc
      exact absurd ((lt_maxOrderComplexity_iff c n m).2 hc) (by omega)
    exact hne' (hc i j (by omega) (by omega) hw)
  · intro htend hep
    obtain ⟨m, hm⟩ := windowDetermined_of_eventuallyPeriodic hep
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 htend (m + 1))
    have := (lt_maxOrderComplexity_iff c n m).1 (by have := hn n le_rfl; omega)
    exact this fun i j _ _ hw => hm i j hw

/-- **Problem 1, no feedback shift register from the start**. -/
theorem problem1_iff_no_feedback_from_zero : Rule30Prize.Problem1 ↔
    ∀ m, ¬ ∃ F : (Fin m → Bool) → Bool, ∀ i, c (i + m) = F fun k => c (i + k) := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_feedback_from_zero]
  push Not
  rfl

end WordsAutomata
end Rule30Equivalents
