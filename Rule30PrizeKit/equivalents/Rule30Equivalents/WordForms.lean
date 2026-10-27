module

public import Rule30Equivalents.ShiftOrbit
public import Rule30Equivalents.TransformsSeeds
public import Rule30Equivalents.Symmetry
public import Rule30Equivalents.Lyndon
public import Rule30Equivalents.GoldenPowers
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Real.GoldenRatio
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
# Problem 1 for words: certificates, gaps, run lengths, repetitions and borders

* `problem1_iff_prefix_certificates`: for every `N` some finite prefix has more than
  `N` distinct factors of one length. For a fixed `N` the condition is a finite search
  (`prefixFactors` is a `Finset`); `Rule30FactorWindow` is the kernel-checked instance
  `N = 16358`.
* `problem1_iff_black_gaps`, `problem1_iff_white_gaps`, `problem1_iff_run_lengths`:
  the gaps between consecutive black cells, the gaps between consecutive white cells, and the
  lengths of the runs are not eventually periodic. The general fact is
  `eventuallyPeriodic_iff_gap`: a `Bool` sequence with infinitely many `true` values is eventually
  periodic iff the gaps between its `true` values are.

* `problem1_iff_late_long_unbordered_factors`: Problem 1 holds iff every tail has
  unbordered factors of unbounded length. The sufficient direction is
  `problem1_of_late_long_unbordered_factors`. The converse is the Ehrenfeucht–Silberger theorem for
  infinite words, `Lyndon.eventuallyPeriodic_of_bordered`, proved through the Lyndon factorization.

* `problem1_iff_infinitely_many_prefixes_without_golden_power`: Problem 1 holds iff
  infinitely many prefixes end with no repetition of exponent at least `φ²`. The sufficient
  direction is `problem1_of_infinitely_many_prefixes_without_golden_power`. The converse is the
  theorem of Mignosi, Restivo and Salemi (1998), `GoldenPowers.eventuallyPeriodic_of_gp`.

One sufficient condition:
* `problem1_of_lz_unbounded`: if the Lempel–Ziv (1976) complexity of the prefixes is
  unbounded, Problem 1 holds (`lzComplexity_le_of_eventuallyPeriodic`). The equivalence is proved in
  `LempelZiv`.
-/

@[expose] public section

namespace Rule30Equivalents.WordForms

open Ruliology.CellularAutomata

/-! ### Finite certificates -/

/-- The distinct factors of length `n` that start below `M`, as lists. -/
def prefixFactors (b : ℕ → Bool) (n M : ℕ) : Finset (List Bool) :=
  (Finset.range M).image fun i => List.ofFn fun j : Fin n => b (i + j)

theorem card_prefixFactors (b : ℕ → Bool) (n M : ℕ) :
    (prefixFactors b n M).card =
      ((Finset.range M).image fun i => fun j : Fin n => b (i + j)).card := by
  have : prefixFactors b n M =
      ((Finset.range M).image fun i => fun j : Fin n => b (i + j)).image List.ofFn := by
    rw [prefixFactors, Finset.image_image]; rfl
  rw [this, Finset.card_image_of_injective _ List.ofFn_injective]

theorem card_prefixFactors_le (b : ℕ → Bool) (n M : ℕ) :
    (prefixFactors b n M).card ≤ (ShiftOrbit.factors b n).ncard := by
  rw [card_prefixFactors, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun w hw => ?_) (ShiftOrbit.factors_finite b n)
  rw [Finset.coe_image] at hw
  obtain ⟨i, -, rfl⟩ := hw
  exact ⟨i, rfl⟩

theorem exists_card_prefixFactors (b : ℕ → Bool) (n : ℕ) :
    ∃ M, (ShiftOrbit.factors b n).ncard ≤ (prefixFactors b n M).card := by
  classical
  let idx : (Fin n → Bool) → ℕ := fun w =>
    if h : ∃ i, (fun j : Fin n => b (i + j)) = w then Classical.choose h else 0
  refine ⟨Finset.univ.sup idx + 1, ?_⟩
  rw [card_prefixFactors, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun w hw => ?_) (Finset.finite_toSet _)
  have hw' : ∃ i, (fun j : Fin n => b (i + j)) = w := hw
  have e : idx w = Classical.choose hw' := dite_eq_left hw'
  have hle : idx w ≤ Finset.univ.sup idx := Finset.le_sup (Finset.mem_univ w)
  rw [Finset.coe_image]
  exact ⟨Classical.choose hw', Finset.mem_coe.2 (Finset.mem_range.2 (by omega)),
    Classical.choose_spec hw'⟩

/-- Unbounded factor complexity, with the factors found in finite prefixes. -/
theorem unbounded_iff_prefix_certificates (b : ℕ → Bool) :
    (∀ C, ∃ n, C < (ShiftOrbit.factors b n).ncard) ↔
      ∀ N, ∃ n M, N < (prefixFactors b n M).card := by
  constructor
  · intro h N
    obtain ⟨n, hn⟩ := h N
    obtain ⟨M, hM⟩ := exists_card_prefixFactors b n
    exact ⟨n, M, lt_of_lt_of_le hn hM⟩
  · intro h C
    obtain ⟨n, M, hM⟩ := h C
    exact ⟨n, lt_of_lt_of_le hM (card_prefixFactors_le b n M)⟩

/-- **Problem 1 by finite certificates**: for every `N`, some prefix has more than
`N` distinct factors of one length. -/
theorem problem1_iff_prefix_certificates : Rule30Prize.Problem1 ↔
    ∀ N : ℕ, ∃ n M : ℕ, N < ((Finset.range M).image
      fun i => List.ofFn fun j : Fin n => Rule30Prize.center (i + j)).card :=
  ShiftOrbit.problem1_iff_ncard_factors_unbounded.trans (unbounded_iff_prefix_certificates c)

/-! ### Gaps and run lengths -/

/-- The `k`-th time, counting from `0`, at which `b` is `true`. -/
noncomputable def trueTime (b : ℕ → Bool) (k : ℕ) : ℕ := Nat.nth (fun t => b t = true) k

/-- The gap between the `k`-th `true` time of `b` and the next one. -/
noncomputable def gap (b : ℕ → Bool) (k : ℕ) : ℕ := trueTime b (k + 1) - trueTime b k

/-- An `ℕ`-valued sequence is eventually periodic. -/
def EventuallyPeriodicNat (g : ℕ → ℕ) : Prop := ∃ T P, 0 < P ∧ ∀ k, T ≤ k → g (k + P) = g k

/-- On the periodic part, every window of length `P` holds the same number of `true` values. -/
theorem window_count {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (h : ∀ t, T ≤ t → b (t + P) = b t) : ∀ d,
    Nat.count (fun j => b (T + d + j) = true) P = Nat.count (fun j => b (T + j) = true) P := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  intro d
  induction d with
  | zero => simp only [Nat.add_zero]
  | succ d ih =>
    rw [← ih, Nat.count_succ, Nat.count_succ' (fun j => b (T + d + j) = true)]
    have e2 : b (T + (d + 1) + Q) = b (T + d + 0) := by
      rw [show T + (d + 1) + Q = T + d + (Q + 1) by omega, h _ (by omega)]; rfl
    rw [e2]
    simp only [show ∀ k, T + (d + 1) + k = T + d + (k + 1) from fun k => by omega]

theorem trueTime_add_of_periodic {b : ℕ → Bool} (hinf : {t | b t = true}.Infinite) {T P : ℕ}
    (hP : 0 < P) (h : ∀ t, T ≤ t → b (t + P) = b t) (k : ℕ) (hk : T ≤ trueTime b k) :
    trueTime b (k + Nat.count (fun j => b (T + j) = true) P) = trueTime b k + P := by
  have hy : b (trueTime b k) = true := Nat.nth_mem_of_infinite hinf k
  have hyP : b (trueTime b k + P) = true := by rw [h _ hk]; exact hy
  have hc : Nat.count (fun t => b t = true) (trueTime b k + P) =
      k + Nat.count (fun j => b (T + j) = true) P := by
    rw [Nat.count_add, show Nat.count (fun t => b t = true) (trueTime b k) = k from
      Nat.count_nth_of_infinite hinf k]
    have := window_count hP h (trueTime b k - T)
    simp only [show T + (trueTime b k - T) = trueTime b k by omega] at this
    rw [this]
  rw [← hc]
  exact Nat.nth_count (p := fun t => b t = true) hyP

/-- **A sequence with infinitely many `true` values is eventually periodic iff the gaps between
them are.** -/
theorem eventuallyPeriodic_iff_gap {b : ℕ → Bool} (hinf : {t | b t = true}.Infinite) :
    EventuallyPeriodic b ↔ EventuallyPeriodicNat (gap b) := by
  have hmono : StrictMono (trueTime b) := Nat.nth_strictMono hinf
  constructor
  · rintro ⟨T, P, hP, h⟩
    let K := Nat.count (fun t => b t = true) T
    have hK : ∀ k, K ≤ k → T ≤ trueTime b k := fun k hk =>
      (Nat.le_nth_count hinf T).trans (hmono.monotone hk)
    have key : ∀ k, K ≤ k →
        trueTime b (k + Nat.count (fun j => b (T + j) = true) P) = trueTime b k + P :=
      fun k hk => trueTime_add_of_periodic hinf hP h k (hK k hk)
    have hm : 0 < Nat.count (fun j => b (T + j) = true) P := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      have := key K (Nat.le_refl K)
      rw [h0, Nat.add_zero] at this
      omega
    refine ⟨K, _, hm, fun k hk => ?_⟩
    unfold gap
    rw [show k + Nat.count (fun j => b (T + j) = true) P + 1 =
      (k + 1) + Nat.count (fun j => b (T + j) = true) P by omega, key (k + 1) (by omega), key k hk]
    omega
  · rintro ⟨K, Q, hQ, h⟩
    have hKQ : trueTime b K < trueTime b (K + Q) := hmono (by omega)
    have key : ∀ k, K ≤ k →
        trueTime b (k + Q) = trueTime b k + (trueTime b (K + Q) - trueTime b K) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => omega
      | succ k hk ih =>
        have g := h k hk
        unfold gap at g
        have m1 : trueTime b (k + Q) < trueTime b (k + Q + 1) := hmono (by omega)
        have m2 : trueTime b k < trueTime b (k + 1) := hmono (by omega)
        rw [show k + 1 + Q = k + Q + 1 by omega]
        omega
    refine ⟨trueTime b K, trueTime b (K + Q) - trueTime b K, by omega, fun t ht => ?_⟩
    have hcount : ∀ y, trueTime b K ≤ y → K ≤ Nat.count (fun t => b t = true) y := fun y hy => by
      have := Nat.count_monotone (fun t => b t = true) hy
      rwa [show trueTime b K = Nat.nth (fun t => b t = true) K from rfl,
        Nat.count_nth_of_infinite hinf] at this
    cases hb : b t with
    | true =>
      have ht' : trueTime b (Nat.count (fun t => b t = true) t) = t := Nat.nth_count hb
      have := key _ (hcount t ht)
      rw [ht'] at this
      rw [← this]
      exact Nat.nth_mem_of_infinite hinf _
    | false =>
      by_contra hne
      have hbD : b (t + (trueTime b (K + Q) - trueTime b K)) = true := by
        revert hne; cases b (t + (trueTime b (K + Q) - trueTime b K)) <;> simp
      have hk'eq := Nat.nth_count (p := fun t => b t = true) hbD
      have hk2 : K + Q ≤ Nat.count (fun t => b t = true) (t + (trueTime b (K + Q) - trueTime b K)) := by
        have := Nat.count_monotone (fun t => b t = true)
          (show trueTime b (K + Q) ≤ t + (trueTime b (K + Q) - trueTime b K) by omega)
        rwa [show trueTime b (K + Q) = Nat.nth (fun t => b t = true) (K + Q) from rfl,
          Nat.count_nth_of_infinite hinf] at this
      set k' := Nat.count (fun t => b t = true) (t + (trueTime b (K + Q) - trueTime b K))
      have e := key (k' - Q) (by omega)
      rw [show k' - Q + Q = k' by omega, show trueTime b k' = Nat.nth (fun t => b t = true) k' from rfl,
        hk'eq] at e
      have ht2 : trueTime b (k' - Q) = t := by omega
      have hmem : b (trueTime b (k' - Q)) = true := Nat.nth_mem_of_infinite hinf _
      rw [ht2, hb] at hmem
      exact absurd hmem (by decide)

/-- From some time on, the sequence is `true` again later: infinitely many `true` values. -/
theorem infinite_of_frequently {b : ℕ → Bool} (h : ∀ a, ∃ t, a < t ∧ b t = true) :
    {t | b t = true}.Infinite :=
  Set.infinite_of_forall_exists_gt fun a => by
    obtain ⟨t, hat, ht⟩ := h a
    exact ⟨t, ht, hat⟩

theorem infinite_black : {t | c t = true}.Infinite := by
  refine infinite_of_frequently fun a => Classical.byContradiction fun hne => ?_
  refine Rule30Prize.center_not_eventually_constant ⟨a + 1, false, fun t ht => ?_⟩
  cases hc : c t
  · exact hc
  · exact absurd ⟨t, by omega, hc⟩ hne

theorem infinite_white : {t | (!c t) = true}.Infinite := by
  refine infinite_of_frequently fun a => Classical.byContradiction fun hne => ?_
  refine Rule30Prize.center_not_eventually_constant ⟨a + 1, true, fun t ht => ?_⟩
  cases hc : c t
  · exact absurd ⟨t, by omega, by rw [hc]; rfl⟩ hne
  · exact hc

theorem infinite_changes : {t | TransformsSeeds.xorDeriv c t = true}.Infinite := by
  refine infinite_of_frequently fun a => Classical.byContradiction fun hne => ?_
  have hconst : ∀ t, a + 1 ≤ t → c t = c (a + 1) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      rw [← ih]
      have : TransformsSeeds.xorDeriv c t = false := by
        cases hx : TransformsSeeds.xorDeriv c t
        · rfl
        · exact absurd ⟨t, by omega, hx⟩ hne
      unfold TransformsSeeds.xorDeriv at this
      revert this; cases c t <;> cases c (t + 1) <;> simp
  exact Rule30Prize.center_not_eventually_constant ⟨a + 1, c (a + 1), hconst⟩

/-- The gap between the `n`-th black cell of the center column and the next. -/
noncomputable def blackGap (n : ℕ) : ℕ :=
  Nat.nth (fun t => Rule30Prize.center t = true) (n + 1) -
    Nat.nth (fun t => Rule30Prize.center t = true) n

/-- **Problem 1 ⟺ the gaps between black cells are not eventually periodic**. -/
theorem problem1_iff_black_gaps : Rule30Prize.Problem1 ↔
    ¬ ∃ T P, 0 < P ∧ ∀ n, T ≤ n → blackGap (n + P) = blackGap n :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_gap infinite_black))

/-- **Problem 1 ⟺ the gaps between white cells are not eventually periodic.** -/
theorem problem1_iff_white_gaps : Rule30Prize.Problem1 ↔
    ¬ EventuallyPeriodicNat (gap fun t => !c t) :=
  Symmetry.problem1_iff_complement.trans (not_congr (eventuallyPeriodic_iff_gap infinite_white))

/-- The length of the `k`-th run of the center column after the first color change. -/
noncomputable def runLength (k : ℕ) : ℕ :=
  Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) (k + 1) -
    Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) k

theorem runLength_eq : runLength = gap (TransformsSeeds.xorDeriv c) := by
  have hp : (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) =
      fun t => TransformsSeeds.xorDeriv c t = true := by
    funext t
    apply propext
    show (Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) ↔
      xor (Rule30Prize.center t) (Rule30Prize.center (t + 1)) = true
    cases Rule30Prize.center t <;> cases Rule30Prize.center (t + 1) <;> decide
  funext k
  unfold runLength gap trueTime
  rw [hp]

/-- **Problem 1 ⟺ the run lengths are not eventually periodic**. -/
theorem problem1_iff_run_lengths : Rule30Prize.Problem1 ↔
    ¬ ∃ T P, 0 < P ∧ ∀ k, T ≤ k → runLength (k + P) = runLength k := by
  rw [runLength_eq]
  exact TransformsSeeds.problem1_iff_xor_derivative.trans
    (not_congr (eventuallyPeriodic_iff_gap infinite_changes))

/-! ### Repetitions of exponent `φ²`: the sufficient direction -/

/-- The prefix of length `n` ends with a repetition of exponent at least `φ²`: a suffix of length
`ℓ ≥ φ² p` with period `p`. -/
def EndsWithGoldenPower (b : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ p ℓ : ℕ, 0 < p ∧ ℓ ≤ n ∧ Real.goldenRatio ^ 2 * (p : ℝ) ≤ ℓ ∧
    ∀ i, n - ℓ ≤ i → i + p < n → b (i + p) = b i

/-- An eventually periodic sequence: every long prefix ends with a repetition of exponent `≥ 3`. -/
theorem eventually_endsWithGoldenPower {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ N, ∀ n, N ≤ n → EndsWithGoldenPower b n := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T + 3 * P, fun n hn => ⟨P, n - T, hP, by omega, ?_, fun i hi _ => hper i (by omega)⟩⟩
  have h1 : Real.goldenRatio ^ 2 < 3 := by
    rw [Real.goldenRatio_sq]; linarith [Real.goldenRatio_lt_two]
  have h2 : (3 : ℝ) * P ≤ ((n - T : ℕ) : ℝ) := by exact_mod_cast (show 3 * P ≤ n - T by omega)
  have h3 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  nlinarith

/-- **A sufficient condition**: if infinitely many prefixes of the center column end
with no repetition of exponent at least `φ²`, Problem 1 holds. -/
theorem problem1_of_infinitely_many_prefixes_without_golden_power :
    (∀ N, ∃ n, N ≤ n ∧ ¬ EndsWithGoldenPower c n) → Rule30Prize.Problem1 := by
  intro h hep
  obtain ⟨N, hN⟩ := eventually_endsWithGoldenPower hep
  obtain ⟨n, hn, hne⟩ := h N
  exact hne (hN n hn)

theorem gp_of_endsWithGoldenPower {b : ℕ → Bool} {n : ℕ} (h : EndsWithGoldenPower b n) :
    ∃ d, GoldenPowers.GP b n d := by
  obtain ⟨p, ℓ, hp, hℓn, hφ, hper⟩ := h
  have hneed : GoldenPowers.need p ≤ ℓ := Nat.ceil_le.2 hφ
  exact ⟨p, hp, by omega, fun i h1 h2 => hper i (by omega) h2⟩

/-- **Problem 1 ⟺ infinitely many prefixes end with no repetition of exponent `φ²`**. The
converse direction is the theorem of Mignosi, Restivo and Salemi
(`GoldenPowers.eventuallyPeriodic_of_gp`). -/
theorem problem1_iff_infinitely_many_prefixes_without_golden_power : Rule30Prize.Problem1 ↔
    ∀ N, ∃ n, N ≤ n ∧ ¬ EndsWithGoldenPower c n := by
  refine ⟨fun hP N => ?_, problem1_of_infinitely_many_prefixes_without_golden_power⟩
  by_contra hall
  push Not at hall
  exact hP (GoldenPowers.eventuallyPeriodic_of_gp fun n hn => gp_of_endsWithGoldenPower (hall n hn))

/-! ### Unbordered factors: the sufficient direction -/

open Lyndon (Bordered)

/-- In a purely periodic stretch with period `P`, every factor longer than `P` is bordered. -/
theorem bordered_of_periodic {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (h : ∀ t, T ≤ t → b (t + P) = b t) {i ℓ : ℕ} (hi : T ≤ i) (hℓ : P < ℓ) :
    Bordered ((List.range ℓ).map fun j => b (i + j)) := by
  refine ⟨ℓ - P, by omega, by simp; omega, ?_⟩
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range]
    rw [show ℓ - (ℓ - P) + j = j + P by omega, show i + (j + P) = i + j + P by omega,
      h _ (by omega)]

/-- **A sufficient condition**: if every tail of the center column has unbordered
factors of unbounded length, Problem 1 holds. -/
theorem problem1_of_late_long_unbordered_factors :
    (∀ n L : ℕ, ∃ i ℓ : ℕ, n ≤ i ∧ L ≤ ℓ ∧
      ¬ Bordered ((List.range ℓ).map fun j => Rule30Prize.center (i + j))) →
      Rule30Prize.Problem1 := by
  rintro h ⟨T, P, hP, hper⟩
  obtain ⟨i, ℓ, hi, hℓ, hnb⟩ := h T (P + 1)
  exact hnb (bordered_of_periodic hP hper hi (by omega))

/-- **Problem 1 ⟺ every tail has unbordered factors of unbounded length**. The
converse direction is the Ehrenfeucht–Silberger theorem for infinite words. -/
theorem problem1_iff_late_long_unbordered_factors : Rule30Prize.Problem1 ↔
    ∀ n L : ℕ, ∃ i ℓ : ℕ, n ≤ i ∧ L ≤ ℓ ∧
      ¬ Bordered ((List.range ℓ).map fun j => Rule30Prize.center (i + j)) := by
  refine ⟨fun hP n L => ?_, problem1_of_late_long_unbordered_factors⟩
  by_contra hall
  push Not at hall
  obtain ⟨T, P, hP0, hper⟩ := Lyndon.eventuallyPeriodic_of_bordered
    (x := fun t => Rule30Prize.center (n + t)) (L := L) fun i ℓ hℓ => by
      have := hall (n + i) ℓ (by omega) hℓ
      simpa [Lyndon.factor, Nat.add_assoc] using this
  exact hP ⟨n + T, P, hP0, fun t ht => by
    have := hper (t - n) (by omega)
    simpa [show n + (t - n + P) = t + P by omega, show n + (t - n) = t by omega] using this⟩

/-! ### Lempel–Ziv complexity: the sufficient direction -/

/-- A Lempel–Ziv (1976) history of the prefix of length `n` of `b`: cut points
`0 = x₀ < x₁ < ⋯ < x_r = n`, where each component `[xᵢ, xᵢ₊₁)` is a single letter or, apart from its
last letter, a copy of a stretch that starts earlier. -/
def IsLZHistory (b : ℕ → Bool) (n : ℕ) (cuts : List ℕ) : Prop :=
  cuts.head? = some 0 ∧ cuts.getLast? = some n ∧ List.IsChain (· < ·) cuts ∧
    ∀ p ∈ cuts.zip cuts.tail, p.2 = p.1 + 1 ∨
      ∃ s < p.1, ∀ j, p.1 + j + 1 < p.2 → b (s + j) = b (p.1 + j)

/-- The Lempel–Ziv complexity of the prefix of length `n`: the fewest components of a history. -/
noncomputable def lzComplexity (b : ℕ → Bool) (n : ℕ) : ℕ :=
  sInf {k | ∃ cuts, IsLZHistory b n cuts ∧ cuts.length = k + 1}

theorem mem_zip_tail_concat {l : List ℕ} {a : ℕ} {p : ℕ × ℕ} :
    p ∈ (l ++ [a]).zip (l ++ [a]).tail → p ∈ l.zip l.tail ∨ p = (l.getLast?.getD 0, a) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      intro hp
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · left; simp
      · rcases ih (by simpa using hp) with h | h
        · left
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
          right; simpa using h
        · right; rw [h]; simp [List.getLast?_cons_cons]

/-- A history extends by one component. -/
theorem isLZHistory_concat {b : ℕ → Bool} {m n : ℕ} {cuts : List ℕ} (h : IsLZHistory b m cuts)
    (hmn : m < n) (hc : n = m + 1 ∨ ∃ s < m, ∀ j, m + j + 1 < n → b (s + j) = b (m + j)) :
    IsLZHistory b n (cuts ++ [n]) := by
  obtain ⟨h0, hl, hch, hz⟩ := h
  refine ⟨?_, List.getLast?_concat, hch.append (List.isChain_singleton n) ?_, fun p hp => ?_⟩
  · rw [List.head?_append, h0]; rfl
  · intro x hx y hy
    rw [hl] at hx
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
    omega
  · rcases mem_zip_tail_concat hp with h | rfl
    · exact hz p h
    · simp only [hl, Option.getD_some]
      exact hc

theorem isLZHistory_range (b : ℕ → Bool) : ∀ n, IsLZHistory b n (List.range (n + 1))
  | 0 => ⟨rfl, rfl, List.isChain_singleton 0, fun p hp => by simp at hp⟩
  | n + 1 => by
    rw [List.range_succ]
    exact isLZHistory_concat (isLZHistory_range b n) (by omega) (Or.inl rfl)

/-- An eventually periodic sequence has bounded Lempel–Ziv complexity: single letters up to the
end of the first period, then one long overlapping copy. -/
theorem lzComplexity_le_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ K, ∀ n, lzComplexity b n ≤ K := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T + P + 1, fun n => ?_⟩
  by_cases hn : n ≤ T + P
  · have hle : lzComplexity b n ≤ n :=
      Nat.sInf_le ⟨List.range (n + 1), isLZHistory_range b n, by simp⟩
    omega
  · have hist := isLZHistory_concat (isLZHistory_range b (T + P)) (by omega : T + P < n)
      (Or.inr ⟨T, by omega, fun j _ => by
        rw [show T + P + j = (T + j) + P by omega, hper _ (by omega)]⟩)
    exact Nat.sInf_le ⟨_, hist, by simp⟩

/-- **A sufficient condition**: if the Lempel–Ziv complexity of the prefixes of the
center column is unbounded, Problem 1 holds. -/
theorem problem1_of_lz_unbounded :
    (∀ K, ∃ n, K < lzComplexity c n) → Rule30Prize.Problem1 := by
  intro h hep
  obtain ⟨K, hK⟩ := lzComplexity_le_of_eventuallyPeriodic (b := c) hep
  obtain ⟨n, hn⟩ := h K
  exact absurd (hK n) (by omega)

/-! ### Return words and the derived sequence -/

/-- `u` occurs in `b` at position `t`. -/
def OccursAt (b : ℕ → Bool) (u : List Bool) (t : ℕ) : Prop :=
  ∀ j (hj : j < u.length), b (t + j) = u[j]

instance (b : ℕ → Bool) (u : List Bool) : DecidablePred (OccursAt b u) := fun _ =>
  Nat.decidableBallLT _ _

/-- The occurrences of `u` in `b`, as a `Bool` sequence. -/
def occInd (b : ℕ → Bool) (u : List Bool) (t : ℕ) : Bool := decide (OccursAt b u t)

/-- The `k`-th return word to `u`: the factor of `b` from the `k`-th occurrence of `u` to the
next. The derived sequence of `b` codes these words. -/
noncomputable def returnWord (b : ℕ → Bool) (u : List Bool) (k : ℕ) : List Bool :=
  (List.range (gap (occInd b u) k)).map fun j => b (trueTime (occInd b u) k + j)

/-- A sequence in any type is eventually periodic. -/
def EventuallyPeriodicSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∃ T P, 0 < P ∧ ∀ k, T ≤ k → s (k + P) = s k

theorem getElem_returnWord (b : ℕ → Bool) (u : List Bool) (k j : ℕ)
    (hj : j < (returnWord b u k).length) :
    (returnWord b u k)[j] = b (trueTime (occInd b u) k + j) := by
  simp [returnWord]

theorem length_returnWord (b : ℕ → Bool) (u : List Bool) (k : ℕ) :
    (returnWord b u k).length = gap (occInd b u) k := by
  simp [returnWord]

/-- **Return words** (Durand): for a word `u` that occurs infinitely often in `b`, the sequence `b`
is eventually periodic iff the sequence of its return words to `u` is. -/
theorem eventuallyPeriodic_iff_returnWord {b : ℕ → Bool} {u : List Bool}
    (hinf : {t | occInd b u t = true}.Infinite) :
    EventuallyPeriodic b ↔ EventuallyPeriodicSeq (returnWord b u) := by
  have hmono : StrictMono (trueTime (occInd b u)) := Nat.nth_strictMono hinf
  constructor
  · rintro ⟨T, P, hP, h⟩
    -- the occurrences are periodic from `T` on
    have hocc : ∀ t, T ≤ t → occInd b u (t + P) = occInd b u t := fun t ht => by
      unfold occInd OccursAt
      congr 1
      refine propext (forall_congr' fun j => forall_congr' fun hj => ?_)
      rw [show t + P + j = (t + j) + P by omega, h _ (by omega)]
    set N := Nat.count (fun j => occInd b u (T + j) = true) P
    let K := Nat.count (fun t => occInd b u t = true) T
    have hK : ∀ k, K ≤ k → T ≤ trueTime (occInd b u) k := fun k hk =>
      (Nat.le_nth_count hinf T).trans (hmono.monotone hk)
    have key : ∀ k, K ≤ k → trueTime (occInd b u) (k + N) = trueTime (occInd b u) k + P :=
      fun k hk => trueTime_add_of_periodic hinf hP hocc k (hK k hk)
    have hN : 0 < N := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      have := key K le_rfl
      rw [h0, Nat.add_zero] at this
      omega
    refine ⟨K, N, hN, fun k hk => ?_⟩
    have hlen : gap (occInd b u) (k + N) = gap (occInd b u) k := by
      unfold gap
      rw [show k + N + 1 = (k + 1) + N by omega, key (k + 1) (by omega), key k hk]
      omega
    apply List.ext_getElem (by rw [length_returnWord, length_returnWord, hlen])
    intro j hj hj'
    rw [getElem_returnWord, getElem_returnWord, key k hk, show
      trueTime (occInd b u) k + P + j = (trueTime (occInd b u) k + j) + P by omega,
      h _ (by have := hK k hk; omega)]
  · rintro ⟨K, Q, hQ, h⟩
    set occ := trueTime (occInd b u)
    have hgap : ∀ k, K ≤ k → gap (occInd b u) (k + Q) = gap (occInd b u) k := fun k hk => by
      rw [← length_returnWord, ← length_returnWord, h k hk]
    set L := occ (K + Q) - occ K
    have hL : 0 < L := by have := hmono (show K < K + Q by omega); omega
    have hshift : ∀ k, K ≤ k → occ (k + Q) = occ k + L := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => have := hmono (show K < K + Q by omega); omega
      | succ k hk ih =>
        have g := hgap k hk
        unfold gap at g
        have m1 : occ (k + Q) < occ (k + Q + 1) := hmono (by omega)
        have m2 : occ k < occ (k + 1) := hmono (by omega)
        rw [show k + 1 + Q = k + Q + 1 by omega]
        show occ (k + Q + 1) = occ (k + 1) + L
        have : occ (k + Q + 1) - occ (k + Q) = occ (k + 1) - occ k := g
        omega
    -- inside the `k`-th return word, `b` repeats after `L`
    have hword : ∀ k, K ≤ k → ∀ j, j < gap (occInd b u) k →
        b (occ k + j + L) = b (occ k + j) := by
      intro k hk j hj
      have hw := h k hk
      have hj1 : j < (returnWord b u (k + Q)).length := by
        rw [length_returnWord, hgap k hk]; exact hj
      have hj2 : j < (returnWord b u k).length := by rw [length_returnWord]; exact hj
      have := congrArg (fun l : List Bool => l[j]?) hw
      simp only [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2, Option.some.injEq,
        getElem_returnWord] at this
      rw [← this, show trueTime (occInd b u) (k + Q) = occ k + L from hshift k hk]
      congr 1
      omega
    refine ⟨occ K, L, hL, fun t ht => ?_⟩
    -- the return word around `t`
    have hex : ∃ k, t < occ (k + 1) := ⟨t, by
      have := hmono.id_le (t + 1)
      simp only [id] at this
      omega⟩
    set k := Nat.find hex
    have hk1 : t < occ (k + 1) := Nat.find_spec hex
    have hk0 : occ k ≤ t := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0]; exact le_trans (hmono.monotone (Nat.zero_le K)) ht
      · have := Nat.find_min hex (show k - 1 < k by omega)
        rw [show k - 1 + 1 = k by omega] at this
        omega
    have hkK : K ≤ k := by
      by_contra hlt
      push Not at hlt
      have := hmono.monotone (show k + 1 ≤ K by omega)
      omega
    have := hword k hkK (t - occ k) (by show t - occ k < occ (k + 1) - occ k; omega)
    rwa [show occ k + (t - occ k) = t by omega] at this

/-- **Return words.** For a word `u` that occurs infinitely often in the center column,
Problem 1 holds iff the sequence of return words to `u` is not eventually periodic. -/
theorem problem1_iff_returnWords {u : List Bool} (hu : {t | occInd c u t = true}.Infinite) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodicSeq (returnWord c u) :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_returnWord hu))

theorem occInd_single_true (b : ℕ → Bool) (t : ℕ) : occInd b [true] t = b t := by
  unfold occInd OccursAt
  cases hb : b t <;> simp [hb]

/-- **Return words, for some word**: Problem 1 holds iff for some word that occurs infinitely
often (equivalently, for every one) the sequence of return words is not eventually periodic. -/
theorem problem1_iff_returnWords_exists : Rule30Prize.Problem1 ↔
    ∃ u : List Bool, {t | occInd c u t = true}.Infinite ∧
      ¬ EventuallyPeriodicSeq (returnWord c u) := by
  have hone : {t | occInd c [true] t = true}.Infinite := by
    simpa only [occInd_single_true] using infinite_black
  exact ⟨fun h => ⟨[true], hone, (problem1_iff_returnWords hone).1 h⟩,
    fun ⟨u, hu, h⟩ => (problem1_iff_returnWords hu).2 h⟩

end Rule30Equivalents.WordForms
