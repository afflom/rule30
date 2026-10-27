module

public import Rule30Equivalents.Genericity
public import Rule30Equivalents.BlackTimes
public import Rule30Equivalents.RandomConfigurations
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
# Bounded remainder

Let `N(n)` be the number of black cells among the first `n` cells of a bit
sequence. An eventually periodic sequence has a *bounded remainder*: `N(n) = α n + O(1)`, with
`α` the density of black cells in a period (`exists_abs_ones_sub_le_of_eventuallyPeriodic`).

* `problem1_of_unbounded_remainder`: **if the number of black cells among the first `n` cells of
  the center column is not `α n + O(1)` for any real `α`, Problem 1 holds.** This is strictly
  stronger than Problem 1: Sturmian sequences are not eventually periodic and have bounded
  remainder. The same holds for the occurrences of any word `w`
  (`problem1_of_unbounded_word_remainder`).
* `unbounded_remainder_of_disjunctive`: a disjunctive sequence (every word occurs) has unbounded
  remainder for every `α`: a run of `m` black cells raises `N(n) - α n` by `(1 - α) m`, and a run
  of `m` white cells lowers it by `α m`. So the new statement sits between "c is disjunctive" and
  Problem 1, and it holds for almost every configuration (`ae_unbounded_remainder_trace`).
* `problem1_of_problem2_of_unbounded_discrepancy`: **if Problem 2 holds and the discrepancy
  `N(n) - n/2` of the center column is unbounded, Problem 1 holds**, since an eventually periodic
  sequence with density `1/2` has bounded discrepancy.
* `problem1_of_oscillating_discrepancy`: **if the discrepancy is unbounded above and below,
  Problem 1 holds**, with no assumption on the density: an eventually periodic sequence has
  bounded discrepancy on the side of its density. The hypothesis holds for almost every
  configuration (`Fluctuations.ae_oscillating_discrepancy_trace`).
* `problem1_of_unpredictable_half`, `problem2_of_unpredictable_half`: **if every finite-state
  predictor errs on half of the center column, Problems 1 and 2 hold.** An eventually periodic
  column has a predictor that is eventually always right; the predictor that always guesses white
  errs exactly on the black cells. The hypothesis holds for almost every configuration
  (`ae_predictsAtHalf_trace`): the errors of a fixed predictor on a random trace are again fair
  coins (`measurePreserving_errors`, since they are adapted to the left coins), and the predictors
  are countably many up to relabeling the states.
-/

@[expose] public section

namespace Rule30Equivalents.BoundedRemainder

open Filter Topology Ruliology.CellularAutomata Genericity

/-- The number of black cells among the first `n` cells of `b`. -/
def ones (b : ℕ → Bool) (n : ℕ) : ℕ := Nat.count (fun t => b t = true) n

theorem ones_add (b : ℕ → Bool) (a m : ℕ) :
    ones b (a + m) = ones b a + ones (fun j => b (a + j)) m :=
  Nat.count_add _ _ _

theorem ones_le (b : ℕ → Bool) (n : ℕ) : ones b n ≤ n := Nat.count_le _

theorem ones_of_forall_true {g : ℕ → Bool} : ∀ {m : ℕ}, (∀ j < m, g j = true) → ones g m = m
  | 0, _ => by simp [ones]
  | m + 1, h => by
    rw [ones, Nat.count_succ, ← ones, ones_of_forall_true fun j hj => h j (by omega),
      ite_eq_left (h m (by omega))]

theorem ones_of_forall_false {g : ℕ → Bool} : ∀ {m : ℕ}, (∀ j < m, g j = false) → ones g m = 0
  | 0, _ => by simp [ones]
  | m + 1, h => by
    rw [ones, Nat.count_succ, ← ones, ones_of_forall_false fun j hj => h j (by omega),
      ite_eq_right (by simp [h m (by omega)])]

/-- Along a sequence that is periodic from the start, `q` full periods contribute `q` times the
black cells of one period. -/
theorem ones_mul_add {g : ℕ → Bool} {P : ℕ} (hg : ∀ j, g (P + j) = g j) :
    ∀ q r, ones g (q * P + r) = q * ones g P + ones g r
  | 0, r => by simp
  | q + 1, r => by
    rw [show (q + 1) * P + r = P + (q * P + r) by ring, ones_add, show (fun j => g (P + j)) = g
      from funext hg, ones_mul_add hg q r]
    ring

/-- **An eventually periodic sequence has bounded remainder**: `N(n) = α n + O(1)`, with `α` the
density of black cells in one period. -/
theorem exists_abs_ones_sub_le_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ α C : ℝ, ∀ n, |(ones b n : ℝ) - α * n| ≤ C := by
  obtain ⟨T, P, hP, hper⟩ := h
  set g : ℕ → Bool := fun j => b (T + j) with hgdef
  have hg : ∀ j, g (P + j) = g j := fun j => by
    simp only [hgdef]
    rw [show T + (P + j) = T + j + P by ring]
    exact hper (T + j) (by omega)
  have hkP : ones g P ≤ P := ones_le g P
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  refine ⟨(ones g P : ℝ) / P, 2 * (T + P), fun n => ?_⟩
  have hα0 : 0 ≤ (ones g P : ℝ) / P := by positivity
  have hα1 : (ones g P : ℝ) / P ≤ 1 := by
    rw [div_le_one hP']
    exact_mod_cast hkP
  rcases Nat.lt_or_ge n T with hn | hn
  · -- before the periodic part both terms are at most `T`
    have h1 : (ones b n : ℝ) ≤ n := by exact_mod_cast ones_le b n
    have h2 : (n : ℝ) < T := by exact_mod_cast hn
    have h3 : (ones g P : ℝ) / P * n ≤ n := by nlinarith
    have h4 : 0 ≤ (ones g P : ℝ) / P * n := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  · -- `n = T + q P + r` with `r < P`
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hdecomp := Nat.div_add_mod m P
    set q := m / P
    set r := m % P
    have hr : r < P := Nat.mod_lt m hP
    have hcount : ones b (T + m) = ones b T + q * ones g P + ones g r := by
      rw [ones_add, ← hdecomp, show P * q + r = q * P + r by ring, ones_mul_add hg, add_assoc]
    have hrT : (ones b T : ℝ) ≤ T := by exact_mod_cast ones_le b T
    have hrr : (ones g r : ℝ) ≤ r := by exact_mod_cast ones_le g r
    have hr' : (r : ℝ) < P := by exact_mod_cast hr
    have hm : (m : ℝ) = q * P + r := by exact_mod_cast (by rw [← hdecomp]; ring : m = q * P + r)
    have key : (ones b (T + m) : ℝ) - (ones g P : ℝ) / P * ((T + m : ℕ) : ℝ) =
        ones b T + ones g r - (ones g P : ℝ) / P * (T + r) := by
      rw [hcount]
      push_cast
      rw [hm]
      field_simp
      ring
    rw [key, abs_le]
    have h5 : (ones g P : ℝ) / P * (T + r) ≤ T + r := by
      have : (0 : ℝ) ≤ T + r := by positivity
      nlinarith
    have h6 : 0 ≤ (ones g P : ℝ) / P * (T + r) := by positivity
    have h7 : (0 : ℝ) ≤ ones b T := by positivity
    have h8 : (0 : ℝ) ≤ ones g r := by positivity
    constructor <;> nlinarith

/-- **Problem 1 from an unbounded remainder**: if the number of black cells among the first `n`
cells of the center column is not `α n + O(1)` for any real `α`, Problem 1 holds. -/
theorem problem1_of_unbounded_remainder
    (h : ∀ α C : ℝ, ∃ n, C < |(ones Rule30Prize.center n : ℝ) - α * n|) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨α, C, hC⟩ := exists_abs_ones_sub_le_of_eventuallyPeriodic hep
  obtain ⟨n, hn⟩ := h α C
  exact absurd (hC n) (not_le.2 hn)

/-- The occurrences of a word `w` in an eventually periodic sequence form an eventually periodic
sequence. -/
theorem eventuallyPeriodic_occurs {b : ℕ → Bool} (h : EventuallyPeriodic b) {m : ℕ}
    (w : Fin m → Bool) : EventuallyPeriodic fun i => decide (∀ j : Fin m, b (i + j) = w j) := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T, P, hP, fun i hi => ?_⟩
  have : ∀ j : Fin m, b (i + P + j) = b (i + j) := fun j => by
    rw [show i + P + j = i + j + P by ring]
    exact hper (i + j) (by omega)
  simp only [this]

/-- **Problem 1 from an unbounded word count**: if for some word `w` the number of its occurrences
among the first `n` positions of the center column is not `α n + O(1)` for any real `α`,
Problem 1 holds. The case of the one-letter word `1` is `problem1_of_unbounded_remainder`. -/
theorem problem1_of_unbounded_word_remainder {m : ℕ} (w : Fin m → Bool)
    (h : ∀ α C : ℝ, ∃ n, C < |(ones (fun i => decide (∀ j : Fin m, Rule30Prize.center (i + j) =
      w j)) n : ℝ) - α * n|) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨α, C, hC⟩ :=
    exists_abs_ones_sub_le_of_eventuallyPeriodic (eventuallyPeriodic_occurs hep w)
  obtain ⟨n, hn⟩ := h α C
  exact absurd (hC n) (not_le.2 hn)

/-- **A disjunctive sequence has unbounded remainder** for every `α`: a run of `m` black cells
raises `N(n) - α n` by `(1 - α) m`, a run of `m` white cells lowers it by `α m`, and one of the two
changes is at least `m/2`. -/
theorem unbounded_remainder_of_disjunctive {v : ℕ → Bool} (hv : Disjunctive v) (α C : ℝ) :
    ∃ n, C < |(ones v n : ℝ) - α * n| := by
  by_contra hcon
  push Not at hcon
  -- a run of `m` equal cells changes the remainder by `(1 - α) m` or by `-α m`
  set m := ⌈4 * C⌉₊ + 1
  have hm : 4 * C < m := by
    have := Nat.le_ceil (4 * C)
    push_cast [m]
    linarith
  obtain ⟨i, hi⟩ := hv m fun _ => true
  obtain ⟨i', hi'⟩ := hv m fun _ => false
  have h1 : ones v (i + m) = ones v i + m := by
    rw [ones_add, ones_of_forall_true fun j hj => hi ⟨j, hj⟩]
  have h0 : ones v (i' + m) = ones v i' := by
    rw [ones_add, ones_of_forall_false fun j hj => hi' ⟨j, hj⟩, add_zero]
  have e1 := abs_le.1 (hcon (i + m))
  have e2 := abs_le.1 (hcon i)
  have e3 := abs_le.1 (hcon (i' + m))
  have e4 := abs_le.1 (hcon i')
  rw [h1] at e1
  rw [h0] at e3
  push_cast at e1 e2 e3 e4
  -- `|1 - α| m ≤ 2C` and `|α| m ≤ 2C`, so `m ≤ 4C`
  have hA : (1 - α) * m ≤ 2 * C := by linarith
  have hB : -((1 - α) * m) ≤ 2 * C := by linarith
  have hC' : α * m ≤ 2 * C := by linarith
  have hD : -(α * m) ≤ 2 * C := by linarith
  have hmpos : (0 : ℝ) ≤ m := by positivity
  rcases le_total α (1 / 2) with hα | hα
  · nlinarith
  · nlinarith

/-- **Problem 1 from Problem 2 and an unbounded discrepancy**: if the center column has density
`1/2` and `N(n) - n/2` is unbounded, Problem 1 holds. An eventually periodic sequence has
`N(n) = α n + O(1)`, and density `1/2` forces `α = 1/2`. -/
theorem problem1_of_problem2_of_unbounded_discrepancy (h2 : Rule30Prize.Problem2)
    (h : ∀ C : ℝ, ∃ n, C < |(ones Rule30Prize.center n : ℝ) - n / 2|) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨α, C, hC⟩ := exists_abs_ones_sub_le_of_eventuallyPeriodic hep
  -- the density is `α`
  have hlim : Tendsto (fun n : ℕ => (ones Rule30Prize.center n : ℝ) / n) atTop (𝓝 α) := by
    have hbound : Tendsto (fun n : ℕ => ((ones Rule30Prize.center n : ℝ) - α * n) / n) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hn']
      exact div_le_div_of_nonneg_right (hC n) hn'.le
    have hadd := hbound.add_const α
    rw [zero_add] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  have h2' := ProblemTwo.problem2_iff_tendsto.1 h2
  have hα : α = 1 / 2 := by
    refine tendsto_nhds_unique hlim (h2'.congr fun n => ?_)
    rw [show (Rule30Prize.blackCount n : ℝ) = (ones Rule30Prize.center n : ℝ) by
      rw [ones, ← BlackTimes.length_filter_eq_count]
      rfl]
  obtain ⟨n, hn⟩ := h C
  have := hC n
  rw [hα, show (1 / 2 : ℝ) * n = n / 2 by ring] at this
  exact absurd this (not_le.2 hn)

/-- **If the discrepancy `N(n) - n/2` of the center column is unbounded above and below, Problem 1
holds.** An eventually periodic sequence has `N(n) = α n + O(1)`, so its discrepancy is bounded
below if `α ≥ 1/2` and above if `α ≤ 1/2`. Unlike `problem1_of_problem2_of_unbounded_discrepancy`
this assumes nothing about the density. -/
theorem problem1_of_oscillating_discrepancy
    (hhi : ∀ C : ℝ, ∃ n, C < (ones Rule30Prize.center n : ℝ) - n / 2)
    (hlo : ∀ C : ℝ, ∃ n, (ones Rule30Prize.center n : ℝ) - n / 2 < -C) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨α, C, hC⟩ := exists_abs_ones_sub_le_of_eventuallyPeriodic hep
  rcases le_total (1 / 2) α with hα | hα
  · obtain ⟨n, hn⟩ := hlo C
    have h1 := (abs_le.1 (hC n)).1
    have h2 : (1 / 2 : ℝ) * n ≤ α * n := mul_le_mul_of_nonneg_right hα n.cast_nonneg
    linarith
  · obtain ⟨n, hn⟩ := hhi C
    have h1 := (abs_le.1 (hC n)).2
    have h2 : α * n ≤ (1 / 2 : ℝ) * n := mul_le_mul_of_nonneg_right hα n.cast_nonneg
    linarith

/-! ### Unpredictability at error rate `1/2` -/

/-- The error rate on `b` of the finite-state predictor that reads `b(0), …, b(n-1)` and then
guesses `g` of its state for `b(n)` tends to `1/2`. -/
def PredictsAtHalf (b : ℕ → Bool) (σ : Type) (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool) : Prop :=
  Tendsto (fun N : ℕ => (((Finset.range N).filter fun n =>
    g (WordsAutomata.readState b s₀ δ n) ≠ b n).card : ℝ) / N) atTop (𝓝 (1 / 2))

/-- **Problem 1 from unpredictability at rate `1/2`**: if every finite-state predictor errs on
half of the center column, Problem 1 holds. An eventually periodic column has a predictor that is
eventually always right (`WordsAutomata.problem1_iff_unpredictable`), whose error rate is `0`. -/
theorem problem1_of_unpredictable_half
    (h : ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
      PredictsAtHalf Rule30Prize.center σ s₀ δ g) : Rule30Prize.Problem1 := by
  by_contra hP
  rw [WordsAutomata.problem1_iff_unpredictable] at hP
  push Not at hP
  obtain ⟨σ, hσ, s₀, δ, g, N, hN⟩ := hP
  -- the errors happen before `N`
  have hle : ∀ M : ℕ, (((Finset.range M).filter fun n =>
      g (WordsAutomata.readState Rule30Prize.center s₀ δ n) ≠ Rule30Prize.center n).card : ℝ) ≤
        N := fun M => by
    have : ((Finset.range M).filter fun n =>
        g (WordsAutomata.readState Rule30Prize.center s₀ δ n) ≠ Rule30Prize.center n) ⊆
          Finset.range N := fun n hn => by
      rw [Finset.mem_filter] at hn
      by_contra hnN
      exact hn.2 (hN n (by simpa using hnN))
    exact_mod_cast (Finset.card_le_card this).trans (Finset.card_range N).le
  have h0 : Tendsto (fun M : ℕ => (((Finset.range M).filter fun n =>
      g (WordsAutomata.readState Rule30Prize.center s₀ δ n) ≠ Rule30Prize.center n).card : ℝ) /
        M) atTop (𝓝 0) := by
    refine squeeze_zero (fun M => by positivity) (fun M => div_le_div_of_nonneg_right (hle M)
      (Nat.cast_nonneg M)) (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ))
  have := tendsto_nhds_unique h0 (h σ s₀ δ g)
  norm_num at this

/-- **Problem 2 from unpredictability at rate `1/2`**: the predictor that always guesses white
errs exactly on the black cells, so its error rate is the density of black cells. -/
theorem problem2_of_unpredictable_half
    (h : ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
      PredictsAtHalf Rule30Prize.center σ s₀ δ g) : Rule30Prize.Problem2 := by
  have h0 := h Unit () (fun _ _ => ()) fun _ => false
  rw [ProblemTwo.problem2_iff_tendsto]
  refine h0.congr fun N => ?_
  congr 2
  rw [show Rule30Prize.blackCount N = ((List.range N).filter c).length from rfl,
    BlackTimes.length_filter_eq_count, Nat.count_eq_card_filter_range]
  congr 1
  refine Finset.filter_congr fun n _ => ?_
  simp only [c]
  cases Rule30Prize.center n <;> decide

/-- The errors of a finite-state predictor on `b`: `true` at `n` when its guess for `b n`, made
after reading `b(0), …, b(n-1)`, is wrong. -/
def errors {σ : Type} (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool) (b : ℕ → Bool) (n : ℕ) : Bool :=
  xor (g (WordsAutomata.readState b s₀ δ n)) (b n)

/-- The state after `n` letters depends only on those letters. -/
theorem readState_congr {σ : Type} {s₀ : σ} {δ : σ → Bool → σ} {b b' : ℕ → Bool} :
    ∀ {n : ℕ}, (∀ i < n, b i = b' i) →
      WordsAutomata.readState b s₀ δ n = WordsAutomata.readState b' s₀ δ n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [WordsAutomata.readState]
    rw [readState_congr fun i hi => h i (by omega), h n (by omega)]

/-- Relabeling the states does not change the run. -/
theorem readState_equiv {σ τ : Type} (e : σ ≃ τ) (s₀ : σ) (δ : σ → Bool → σ) (b : ℕ → Bool) :
    ∀ n, WordsAutomata.readState b (e s₀) (fun i c => e (δ (e.symm i) c)) n =
      e (WordsAutomata.readState b s₀ δ n)
  | 0 => rfl
  | n + 1 => by
    simp only [WordsAutomata.readState]
    rw [readState_equiv e s₀ δ b n, Equiv.symm_apply_apply]

theorem measurable_errors {σ : Type} (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool) (n : ℕ) :
    Measurable fun x : ℤ → Bool => errors s₀ δ g (trace x) n := by
  have h : (fun x : ℤ → Bool => errors s₀ δ g (trace x) n) =
      (fun v : Fin (n + 1) → Bool =>
        errors s₀ δ g (fun i => if h : i < n + 1 then v ⟨i, h⟩ else false) n) ∘
        fun x (i : Fin (n + 1)) => trace x i := by
    funext x
    show xor (g (WordsAutomata.readState (trace x) s₀ δ n)) (trace x n) =
      xor (g (WordsAutomata.readState (fun i => if h : i < n + 1 then trace x i else false) s₀ δ n))
        (if h : n < n + 1 then trace x n else false)
    rw [dite_eq_left (Nat.lt_succ_self n),
      readState_congr (b' := fun i => if h : i < n + 1 then trace x i else false)
        fun i hi => by simp [show i < n + 1 by omega]]
  rw [h]
  exact (measurable_of_finite _).comp (Measurable.of_eval fun i =>
    RandomConfigurations.measurable_evol (i : ℕ) 0)

/-- The errors of a predictor on the trace are adapted: flipping the coin at `-n` flips the trace
at `n` and nothing before, so it leaves the state after `n` letters alone and flips the error at
`n`. -/
theorem adapted_errors {σ : Type} (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool) :
    RandomConfigurations.Adapted fun x n => errors s₀ δ g (trace x) n := fun x n => by
  have ht := RandomConfigurations.adapted_trace_of_flipsLeft RandomConfigurations.flipsLeft_id x n
  simp only [id] at ht
  constructor
  · simp only [errors]
    rw [readState_congr fun i hi => ht.2 i hi, ht.1]
    cases g (WordsAutomata.readState (trace x) s₀ δ n) <;> cases trace x n <;> rfl
  · intro t htn
    simp only [errors]
    rw [readState_congr fun i hi => ht.2 i (by omega), ht.2 t htn]

/-- **A predictor's errors on a random trace are fair coins**: for each finite-state predictor,
`x ↦ errors (trace x)` carries `coins ℤ` to `coins ℕ`. -/
theorem measurePreserving_errors {σ : Type} (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool) :
    MeasureTheory.MeasurePreserving (fun x : ℤ → Bool => errors s₀ δ g (trace x))
      (RandomConfigurations.coins ℤ) (RandomConfigurations.coins ℕ) :=
  RandomConfigurations.measurePreserving_of_measure_prefix
    (Measurable.of_eval (measurable_errors s₀ δ g))
    (RandomConfigurations.measure_prefix_of_adapted (measurable_errors s₀ δ g)
      (adapted_errors s₀ δ g))

/-- **Random center columns are unpredictable**: for almost every configuration, every
finite-state predictor errs on half of the center trace in the limit. For each predictor the
errors are fair coins (`measurePreserving_errors`), so they have density `1/2` almost surely;
the predictors are countably many up to relabeling the states. -/
theorem ae_predictsAtHalf_trace : ∀ᵐ x ∂(RandomConfigurations.coins ℤ),
    ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
      PredictsAtHalf (trace x) σ s₀ δ g := by
  have hall : ∀ᵐ x ∂(RandomConfigurations.coins ℤ),
      ∀ p : (Σ k : ℕ, Fin k × (Fin k → Bool → Fin k) × (Fin k → Bool)),
        Symmetry.HalfDensity (errors p.2.1 p.2.2.1 p.2.2.2 (trace x)) :=
    MeasureTheory.ae_all_iff.2 fun p =>
      (measurePreserving_errors p.2.1 p.2.2.1 p.2.2.2).quasiMeasurePreserving.ae
        (RandomConfigurations.ae_isNormal.mono fun v hv => ProblemTwo.halfDensity_of_isNormal hv)
  filter_upwards [hall] with x hx σ _ s₀ δ g
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have h := hx ⟨k, e s₀, fun i c => e (δ (e.symm i) c), fun i => g (e.symm i)⟩
  rw [ProblemTwo.halfDensity_iff_tendsto] at h
  refine h.congr fun N => ?_
  congr 2
  rw [BlackTimes.length_filter_eq_count, Nat.count_eq_card_filter_range]
  congr 1
  refine Finset.filter_congr fun n _ => ?_
  simp only [errors, readState_equiv, Equiv.symm_apply_apply]
  cases g (WordsAutomata.readState (trace x) s₀ δ n) <;> cases trace x n <;> decide

/-- **Random configurations have unbounded remainder**: for almost every configuration, the
number of black cells among the first `n` cells of the center trace is not `α n + O(1)` for any
`α`, since the trace is disjunctive (`RandomConfigurations.ae_disjunctive_trace`). -/
theorem ae_unbounded_remainder_trace :
    ∀ᵐ x ∂(RandomConfigurations.coins ℤ), ∀ α C : ℝ, ∃ n,
      C < |(ones (trace x) n : ℝ) - α * n| := by
  filter_upwards [RandomConfigurations.ae_disjunctive_trace] with x hx
  exact unbounded_remainder_of_disjunctive hx

end Rule30Equivalents.BoundedRemainder
