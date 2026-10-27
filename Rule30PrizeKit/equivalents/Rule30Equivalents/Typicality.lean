module

public import Rule30Equivalents.Autocorrelation
public import Rule30Equivalents.Mixing
public import Rule30Equivalents.LinearComplexity
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
# The stronger statements hold for almost every configuration

Problem 1 follows from many stronger statements about the center column
(`StrongerStatements.problem1_of_*`). Eighteen of them hold for almost every configuration, with
the seed replaced by the configuration (`ae_strongerStatements_trace`); in particular none of them
is vacuous.

* **Words.** Most of them hold for every disjunctive sequence: the effective boundary
  `t ↦ b(t) ∧ b(t + 1)` is not eventually periodic (`not_eventuallyPeriodic_and_of_disjunctive`),
  runs of every length occur in both colors, no residue class `k ↦ b(r + kP)` is eventually
  constant (`antiToeplitz_of_disjunctive`), every lag disagrees infinitely often, and `b` differs
  infinitely often from every periodic sequence. All rest on `eq_of_periodic_of_window`: a
  sequence with period `P` from `T` that is constant on `P` consecutive positions after `T` is
  constant from `T` on. Moreover the orbit closure is all of `{0,1}^ℕ`, hence uncountable
  (`closure_shifts_of_disjunctive`, `not_countable_univ`); there are `2ⁿ` factors of length `n`
  (`ncard_factors_of_disjunctive`) and `n + 1` abelian classes
  (`abelianComplexity_of_disjunctive`); and `b` is recurrent and not purely periodic.
* **Numbers.** In every base `B ≥ 2` the value `0.b(0) b(1) …` separates the sequences with
  infinitely many ones (`baseValue_injOn`, reading the digits off the tail values), the algebraic
  numbers are countable, and the fair-coin measure has no atoms
  (`RandomConfigurations.coins_singleton`). So almost every
  sequence has a transcendental value (`ae_transcendental_baseValue`), of irrationality exponent at
  least `2` by Dirichlet's theorem (`StrongerStatements.irrExponentGE_two_of_irrational`).
* **Morphic sequences** are countably many (`StrongerStatements.countable_setOf_isMorphic`), so
  almost every sequence is not morphic (`ae_not_isMorphic`); so are the `k`-Mahler series with
  `0/1` coefficients for `k ≥ 2` (`StrongerStatements.countable_setOf_isMahler`), so almost every
  generating function is not `k`-Mahler (`ae_not_isMahler`).
* **Expansion complexity.** A nonzero `g(X, Y)` over `𝔽₂` vanishes at finitely many generating
  functions (`finite_roots_series`, its roots over the domain `𝔽₂⟦X⟧`), and the `g` of degree at
  most `D` in each variable are finitely many, so the expansion complexity is unbounded almost
  surely (`ae_expansionComplexity_unbounded`).
* No line inside the light cone is eventually periodic (`Mixing.ae_every_line`), and the linear
  complexity satisfies `Lₙ/n → 1/2` (`LinearComplexity.ae_tendsto_linComplexity_trace`).

Not every stronger statement is typical: the defect bound fails with probability at least `1/32`,
when the first five cells of the column agree (`measure_not_defectBound_trace`), and `H_m ≠ 0` for
all `m ≥ 9` fails with probability at least `2^-9`, when the first nine cells are white
(`measure_hankel_det_eq_zero_trace`).
-/

@[expose] public section

namespace Rule30Equivalents.Typicality

open MeasureTheory Filter Topology Ruliology.CellularAutomata Rule30Realization Genericity
  RandomConfigurations StrongerStatements

/-! ### Words -/

/-- A sequence with period `P` from `T` that takes the value `β` on `P` consecutive positions from
`T` on takes it everywhere from `T` on. -/
theorem eq_of_periodic_of_window {f : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (hper : ∀ t, T ≤ t → f (t + P) = f t) {i : ℕ} (hi : T ≤ i) {β : Bool}
    (hw : ∀ j < P, f (i + j) = β) {t : ℕ} (ht : T ≤ t) : f t = β := by
  have hk : ∀ q s, T ≤ s → f (s + P * q) = f s := by
    intro q
    induction q with
    | zero => intro s _; simp
    | succ q ih =>
      intro s hs
      rw [Nat.mul_succ, ← add_assoc, hper _ (by omega), ih s hs]
  have hiP : i ≤ P * i := Nat.le_mul_of_pos_left i hP
  obtain ⟨q, ρ, hρ, hqρ⟩ : ∃ q ρ, ρ < P ∧ t + P * i - i = P * q + ρ :=
    ⟨_, _, Nat.mod_lt _ hP, (Nat.div_add_mod _ P).symm⟩
  have e : t + P * i = i + ρ + P * q := by omega
  rw [← hk i t ht, e, hk q _ (by omega), hw ρ hρ]

/-- **The effective boundary of a disjunctive sequence is not eventually periodic.** With period
`P` from `T`, a run of `P + 1` ones after `T` would make `t ↦ b(t) ∧ b(t + 1)` equal to `1` from
`T` on, and a later `0` contradicts it. -/
theorem not_eventuallyPeriodic_and_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) :
    ¬ EventuallyPeriodic fun t => b t && b (t + 1) := by
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨i, hi, hw⟩ := Mixing.exists_ge_of_disjunctive hb (fun _ : Fin (P + 1) => true) T
  obtain ⟨i', hi', hw'⟩ := Mixing.exists_ge_of_disjunctive hb (fun _ : Fin 1 => false) T
  have h := eq_of_periodic_of_window (f := fun t => b t && b (t + 1)) hP hper hi (β := true)
    (fun j hj => by
      have h1 := hw ⟨j, by omega⟩
      have h2 := hw ⟨j + 1, by omega⟩
      simp only at h1 h2 ⊢
      rw [h1, show i + j + 1 = i + (j + 1) by omega, h2]
      rfl) hi'
  have h0 := hw' 0
  simp only [Fin.val_zero, add_zero] at h0
  simp [h0] at h

/-- **A disjunctive sequence is anti-Toeplitz**: no residue class `k ↦ b(r + kP)` is eventually
constant, since a run of `P` cells of the other color after `r + KP` meets the class. -/
theorem antiToeplitz_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) {P : ℕ} (hP : 0 < P)
    (r : ℕ) : ¬ ∃ K β, ∀ k, K ≤ k → b (r + k * P) = β := by
  rintro ⟨K, β, hK⟩
  obtain ⟨i, hi, hw⟩ := Mixing.exists_ge_of_disjunctive hb (fun _ : Fin P => !β) (r + K * P)
  obtain ⟨q, ρ, hρ, hqρ⟩ : ∃ q ρ, ρ < P ∧ i - r = P * q + ρ :=
    ⟨_, _, Nat.mod_lt _ hP, (Nat.div_add_mod _ P).symm⟩
  have hKP : K * P = P * K := Nat.mul_comm K P
  have hqP : q * P = P * q := Nat.mul_comm q P
  have hKq : K ≤ q := by
    by_contra h
    have h1 : P * (q + 1) ≤ P * K := Nat.mul_le_mul_left P (by omega)
    rw [Nat.mul_succ] at h1
    omega
  -- the class meets the run at `r + kP`, with `k = q` or `k = q + 1`
  rcases Nat.eq_zero_or_pos ρ with h0 | h0
  · have hk := hK q hKq
    have hwi := hw ⟨0, hP⟩
    simp only [add_zero] at hwi
    rw [show r + q * P = i by omega, hwi] at hk
    cases β <;> simp at hk
  · have hk := hK (q + 1) (by omega)
    have hwi := hw ⟨P - ρ, by omega⟩
    simp only at hwi
    rw [show r + (q + 1) * P = i + (P - ρ) by rw [add_mul, one_mul]; omega, hwi] at hk
    cases β <;> simp at hk

/-- In a disjunctive sequence every lag `τ ≥ 1` disagrees infinitely often. -/
theorem infinite_disagreements_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) {τ : ℕ}
    (hτ : 0 < τ) : {t | b t ≠ b (t + τ)}.Infinite := fun hfin => by
  obtain ⟨T, hT⟩ := hfin.bddAbove
  refine not_eventuallyPeriodic_of_disjunctive hb ⟨T + 1, τ, hτ, fun t ht => ?_⟩
  by_contra h
  have := hT (show t ∈ {t | b t ≠ b (t + τ)} from fun h' => h h'.symm)
  omega

/-- A disjunctive sequence differs infinitely often from every periodic sequence. -/
theorem infinite_ne_periodic_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) {y : ℕ → Bool}
    {P : ℕ} (hP : 0 < P) (hy : ∀ t, y (t + P) = y t) : {t | b t ≠ y t}.Infinite := fun hfin => by
  obtain ⟨T, hT⟩ := hfin.bddAbove
  have hbT : ∀ t, T < t → b t = y t := fun t ht => by
    by_contra h
    have := hT h
    omega
  refine not_eventuallyPeriodic_of_disjunctive hb ⟨T + 1, P, hP, fun t ht => ?_⟩
  rw [hbT (t + P) (by omega), hbT t (by omega), hy]

/-- **The orbit closure of a disjunctive sequence is everything**: every cylinder contains a
shift. -/
theorem closure_shifts_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) :
    closure (Set.range fun n : ℕ => fun t => b (n + t)) = Set.univ := by
  refine Set.eq_univ_of_forall fun v => mem_closure_iff_nhds.2 fun U hU => ?_
  obtain ⟨L, hL⟩ := exists_prefix_subset hU
  obtain ⟨i, hi⟩ := hb L fun j => v j
  exact ⟨fun t => b (i + t), hL fun t ht => hi ⟨t, ht⟩, i, rfl⟩

/-- `{0,1}^ℕ` is uncountable (Cantor's diagonal argument). -/
theorem not_countable_univ : ¬ (Set.univ : Set (ℕ → Bool)).Countable := by
  intro h
  have := Set.countable_univ_iff.1 h
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨m, hm⟩ := hf fun n => !f n n
  have := congrFun hm m
  cases hfm : f m m <;> simp [hfm] at this

/-- The factors of a disjunctive sequence are all the words. -/
theorem factors_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) (n : ℕ) :
    ShiftOrbit.factors b n = Set.univ :=
  Set.eq_univ_of_forall fun w => let ⟨i, hi⟩ := hb n w; ⟨i, funext hi⟩

/-- A disjunctive sequence has `2ⁿ` factors of length `n`. -/
theorem ncard_factors_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) (n : ℕ) :
    (ShiftOrbit.factors b n).ncard = 2 ^ n := by
  rw [factors_of_disjunctive hb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- **A disjunctive sequence has abelian complexity `n + 1`**: its factors of length `n` have every
number of ones from `0` to `n`. -/
theorem abelianComplexity_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) (n : ℕ) :
    abelianComplexity b n = n + 1 := by
  unfold abelianComplexity
  rw [factors_of_disjunctive hb, Set.image_univ]
  have h : Set.range (fun w : Fin n → Bool => (Finset.univ.filter fun i => w i = true).card) =
      ↑(Finset.range (n + 1)) := by
    ext m
    simp only [Set.mem_range, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨w, rfl⟩
      exact Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))
    · intro hm
      refine ⟨fun i => decide ((i : ℕ) < m), ?_⟩
      simp only [decide_eq_true_eq]
      rw [Fin.card_filter_val_lt]
      omega
  rw [h, Set.ncard_coe_finset, Finset.card_range]

/-- A disjunctive sequence is recurrent: its prefix of length `n` occurs again. -/
theorem isRecurrent_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) : IsRecurrent b :=
  fun n => by
    obtain ⟨s, hs, hw⟩ := Mixing.exists_ge_of_disjunctive hb (fun j : Fin n => b j) 1
    exact ⟨s, hs, fun i hi => hw ⟨i, hi⟩⟩

/-- **A disjunctive sequence is not uniformly recurrent**: the factor `1` misses the long white
blocks. -/
theorem not_uniformlyRecurrent_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) :
    ¬ IsUniformlyRecurrent b := by
  intro hur
  obtain ⟨i, hi⟩ := hb 1 fun _ => true
  obtain ⟨L, hL⟩ := hur 1 i
  obtain ⟨s, hs⟩ := hb (L + 1) fun _ => false
  obtain ⟨k, hk, hkj⟩ := hL s
  have h1 := hkj 0 one_pos
  have h2 := hs ⟨k, by omega⟩
  have h3 := hi 0
  simp only [Fin.val_zero, add_zero] at h1 h2 h3
  rw [h2, h3] at h1
  exact Bool.false_ne_true h1

/-- A disjunctive sequence is not purely periodic. -/
theorem not_purelyPeriodic_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) :
    ¬ ∃ P, 0 < P ∧ ∀ t, b (t + P) = b t :=
  fun ⟨P, hP, h⟩ => not_eventuallyPeriodic_of_disjunctive hb ⟨0, P, hP, fun t _ => h t⟩

/-- **The center column of almost every configuration is recurrent but not uniformly
recurrent**: every prefix occurs again, but not within bounded gaps. -/
theorem ae_recurrent_not_uniformlyRecurrent_trace : ∀ᵐ x ∂(coins ℤ),
    IsRecurrent (trace x) ∧ ¬ IsUniformlyRecurrent (trace x) :=
  ae_disjunctive_trace.mono fun _ hd =>
    ⟨isRecurrent_of_disjunctive hd, not_uniformlyRecurrent_of_disjunctive hd⟩

/-! ### Numbers -/

/-- **The value separates the sequences with infinitely many ones**, in every base `B ≥ 2`: the
digits are read off the tail values (`BinaryIrrational.digit_iff`), and the tail values of equal
values agree at every time (`BinaryIrrational.baseValue_tail_succ`). -/
theorem baseValue_injOn {B : ℕ} (hB : 2 ≤ B) :
    Set.InjOn (BinaryIrrational.baseValue B) {b | ∀ T, ∃ s, T ≤ s ∧ b s = true} := by
  intro b hb b' hb' h
  have hdig : ∀ t, BinaryIrrational.baseValue B (BinaryIrrational.tail b t) =
      BinaryIrrational.baseValue B (BinaryIrrational.tail b' t) → b t = b' t := fun t ht =>
    Bool.eq_iff_iff.2 (by
      rw [BinaryIrrational.digit_iff hB b hb, BinaryIrrational.digit_iff hB b' hb', ht])
  have hval : ∀ t, BinaryIrrational.baseValue B (BinaryIrrational.tail b t) =
      BinaryIrrational.baseValue B (BinaryIrrational.tail b' t) := by
    intro t
    induction t with
    | zero =>
      have e : ∀ v : ℕ → Bool, BinaryIrrational.tail v 0 = v := fun v =>
        funext fun s => by simp [BinaryIrrational.tail]
      rw [e, e]
      exact h
    | succ t ih =>
      rw [BinaryIrrational.baseValue_tail_succ hB, BinaryIrrational.baseValue_tail_succ hB, ih,
        hdig t ih]
  funext t
  exact hdig t (hval t)

/-- **Almost every fair-coin sequence has a transcendental value**, in every base `B ≥ 2`: the
sequences with infinitely many ones and an algebraic value are countably many (`baseValue_injOn`
and the countability of the algebraic numbers), and almost every sequence has infinitely many
ones. -/
theorem ae_transcendental_baseValue {B : ℕ} (hB : 2 ≤ B) :
    ∀ᵐ v ∂(coins ℕ), Transcendental ℚ (BinaryIrrational.baseValue B v) := by
  have hcount : {v : ℕ → Bool | (∀ T, ∃ s, T ≤ s ∧ v s = true) ∧
      IsAlgebraic ℚ (BinaryIrrational.baseValue B v)}.Countable :=
    Set.MapsTo.countable_of_injOn (f := BinaryIrrational.baseValue B) (fun _ hv => hv.2)
      ((baseValue_injOn hB).mono fun _ hv => hv.1) (Algebraic.countable ℚ ℝ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hcount.measure_zero (coins ℕ)), ae_isNormal]
    with v hv hn halg
  refine hv ⟨fun T => ?_, halg⟩
  obtain ⟨i, hi, hw⟩ := Mixing.exists_ge_of_disjunctive (fun n w => disjunctive_of_isNormal hn n w)
    (fun _ : Fin 1 => true) T
  exact ⟨i, hi, by simpa using hw 0⟩

/-- For almost every configuration, `x₂ = 0.c(0)c(1)…₂` of the center column is transcendental. -/
theorem ae_transcendental_trace :
    ∀ᵐ x ∂(coins ℤ), Transcendental ℚ (BinaryIrrational.baseValue 2 (trace x)) :=
  measurePreserving_trace.quasiMeasurePreserving.ae (ae_transcendental_baseValue le_rfl)

/-- **Almost every fair-coin sequence is not morphic**: morphic sequences are countably many. -/
theorem ae_not_isMorphic : ∀ᵐ v ∂(coins ℕ), ¬ IsMorphic v :=
  measure_eq_zero_iff_ae_notMem.1 (countable_setOf_isMorphic.measure_zero _)

/-- For almost every configuration, the center column is not morphic. -/
theorem ae_not_isMorphic_trace : ∀ᵐ x ∂(coins ℤ), ¬ IsMorphic (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_not_isMorphic

/-- **Almost every generating function is not `k`-Mahler**, for any `k ≥ 2`. -/
theorem ae_not_isMahler : ∀ᵐ v ∂(coins ℕ), ∀ k (hk : k ≠ 0), 2 ≤ k →
    ¬ IsMahler k hk (LinearRelations.series ℚ v) :=
  ae_all_iff.2 fun k => by
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · exact Eventually.of_forall fun _ _ h => absurd h (by omega)
    · exact (measure_eq_zero_iff_ae_notMem.1
        ((countable_setOf_isMahler h2 (by omega)).measure_zero _)).mono fun _ hv _ _ => hv

theorem ae_not_isMahler_trace : ∀ᵐ x ∂(coins ℤ), ∀ k (hk : k ≠ 0), 2 ≤ k →
    ¬ IsMahler k hk (LinearRelations.series ℚ (trace x)) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_not_isMahler

/-! ### Algebraic relations over `𝔽₂[X]` -/

/-- Different bit sequences have different generating functions, over a nontrivial ring. -/
theorem injective_series (K : Type*) [CommRing K] [Nontrivial K] :
    Function.Injective (LinearRelations.series K) := by
  intro b b' h
  funext t
  have := congrArg (PowerSeries.coeff t) h
  simp only [LinearRelations.coeff_series, LinearRelations.toK] at this
  cases hb : b t <;> cases hb' : b' t <;> simp_all

/-- **A nonzero `g(X, Y)` over `𝔽₂` vanishes at finitely many generating functions**: they are
roots of `g` over the domain `𝔽₂⟦X⟧`. -/
theorem finite_roots_series {g : Polynomial (Polynomial (ZMod 2))} (hg : g ≠ 0) :
    {b : ℕ → Bool | g.eval₂ Polynomial.coeToPowerSeries.ringHom
      (LinearRelations.series (ZMod 2) b) = 0}.Finite := by
  classical
  set G := g.map Polynomial.coeToPowerSeries.ringHom with hGdef
  have hG : G ≠ 0 := (Polynomial.map_ne_zero_iff (Polynomial.coe_injective (ZMod 2))).2 hg
  refine (G.roots.toFinset.finite_toSet.preimage (injective_series (ZMod 2)).injOn).subset
    fun b hb => ?_
  simp only [Set.mem_ofPred_eq] at hb
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hG, Polynomial.IsRoot, hGdef, Polynomial.eval_map]
  exact hb

/-- **Almost every generating function over `𝔽₂` is a root of no nonzero `g(X, Y)`**. -/
theorem ae_not_root_series : ∀ᵐ v ∂(coins ℕ), ∀ g : Polynomial (Polynomial (ZMod 2)), g ≠ 0 →
    g.eval₂ Polynomial.coeToPowerSeries.ringHom (LinearRelations.series (ZMod 2) v) ≠ 0 := by
  have : Countable (AddMonoidAlgebra (ZMod 2) ℕ) :=
    (AddMonoidAlgebra.coeffEquiv (R := ZMod 2) (M := ℕ)).injective.countable
  have : Countable (Polynomial (ZMod 2)) := Polynomial.toFinsupp_injective.countable
  have : Countable (AddMonoidAlgebra (Polynomial (ZMod 2)) ℕ) :=
    (AddMonoidAlgebra.coeffEquiv (R := Polynomial (ZMod 2)) (M := ℕ)).injective.countable
  have : Countable (Polynomial (Polynomial (ZMod 2))) :=
    Polynomial.toFinsupp_injective.countable
  refine ae_all_iff.2 fun g => ?_
  by_cases hg : g = 0
  · exact Eventually.of_forall fun _ h => absurd hg h
  · exact (measure_eq_zero_iff_ae_notMem.1 ((finite_roots_series hg).countable.measure_zero _)).mono
      fun _ hv _ => hv

/-- The polynomials over `𝔽₂` of degree at most `D` in each variable are finitely many. -/
theorem finite_bounded_polys (D : ℕ) : {g : Polynomial (Polynomial (ZMod 2)) |
    g.natDegree ≤ D ∧ ∀ i, (g.coeff i).natDegree ≤ D}.Finite := by
  refine Set.Finite.of_finite_image (f := fun g (i j : Fin (D + 1)) => (g.coeff i).coeff j)
    (Set.toFinite _) fun g hg g' hg' h => ?_
  ext i j
  by_cases hi : i ≤ D
  · by_cases hj : j ≤ D
    · exact congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hg.2 i; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hg'.2 i; omega)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := g) (n := i) (by have := hg.1; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (p := g') (n := i) (by have := hg'.1; omega)]

/-- **The expansion complexity of almost every generating function over `𝔽₂` is unbounded**: no
nonzero `g` vanishes at it, and the `g` of degree at most `D` in each variable are finitely many,
so one precision `n` sees all of them. -/
theorem ae_expansionComplexity_unbounded : ∀ᵐ v ∂(coins ℕ), ∀ D : ℕ, ∃ n : ℕ,
    ∀ g : Polynomial (Polynomial (ZMod 2)), g ≠ 0 → g.natDegree ≤ D →
      (∀ i, (g.coeff i).natDegree ≤ D) →
        PowerSeries.trunc n (g.eval₂ Polynomial.coeToPowerSeries.ringHom
          (LinearRelations.series (ZMod 2) v)) ≠ 0 := by
  filter_upwards [ae_not_root_series] with v hv D
  classical
  set F := (finite_bounded_polys D).toFinset
  -- a nonzero coefficient of each `g(X, v)`
  have hk : ∀ g : Polynomial (Polynomial (ZMod 2)), g ≠ 0 → ∃ k, PowerSeries.coeff k
      (g.eval₂ Polynomial.coeToPowerSeries.ringHom (LinearRelations.series (ZMod 2) v)) ≠ 0 :=
    fun g hg => by
      by_contra h
      push Not at h
      exact hv g hg (PowerSeries.ext fun k => by simpa using h k)
  let k : Polynomial (Polynomial (ZMod 2)) → ℕ := fun g =>
    if hg : g = 0 then 0 else (hk g hg).choose
  refine ⟨F.sup k + 1, fun g hg hdeg hcoeff => ?_⟩
  have hgF : g ∈ F := (Set.Finite.mem_toFinset _).2 ⟨hdeg, hcoeff⟩
  have hkg : k g ≤ F.sup k := Finset.le_sup hgF
  intro htrunc
  have := congrArg (Polynomial.coeff · (k g)) htrunc
  simp only [PowerSeries.coeff_trunc, Polynomial.coeff_zero] at this
  rw [ite_eq_left (by omega)] at this
  have hspec := (hk g hg).choose_spec
  simp only [k, dite_eq_right hg] at this
  exact hspec this

theorem ae_expansionComplexity_unbounded_trace : ∀ᵐ x ∂(coins ℤ), ∀ D : ℕ, ∃ n : ℕ,
    ∀ g : Polynomial (Polynomial (ZMod 2)), g ≠ 0 → g.natDegree ≤ D →
      (∀ i, (g.coeff i).natDegree ≤ D) →
        PowerSeries.trunc n (g.eval₂ Polynomial.coeToPowerSeries.ringHom
          (LinearRelations.series (ZMod 2) (trace x))) ≠ 0 :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_expansionComplexity_unbounded

/-! ### The stronger statements, almost surely -/

/-- **The stronger statements hold for almost every configuration.** For almost every
configuration `x`, the center column `trace x` satisfies, with `c` replaced by `trace x`, the
hypotheses of `StrongerStatements.problem1_of_effective_boundary`, `problem1_of_every_line`,
`problem1_of_unbounded_runs` (in both colors), `problem1_of_anti_toeplitz`,
`problem1_of_infinite_disagreements`, `problem1_of_far_from_periodic`,
`problem1_of_uncountable_orbit_closure`, `problem1_of_exponential_complexity`,
`problem1_of_disjunctive`, `problem1_of_isNormal`, `problem1_of_transcendental_binary`,
`problem1_of_irrExponentGE`, `problem1_of_unbounded_abelianComplexity`, `problem1_of_not_isMorphic`,
`problem1_of_recurrent_not_purelyPeriodic`, `problem1_of_linComplexity_tendsto`,
`problem1_of_not_isMahler` (for every `k ≥ 2`) and `problem1_of_expansionComplexity_unbounded`. -/
theorem ae_strongerStatements_trace : ∀ᵐ x ∂(coins ℤ),
    (¬ EventuallyPeriodic fun t => trace x t && trace x (t + 1)) ∧
    (∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), 0 < q → |p| < q →
      ¬ EventuallyPeriodic fun t => evol x (q * t + t₀) (p * t + x₀)) ∧
    (∀ (β : Bool) (n : ℕ), ∃ t, ∀ i < n, trace x (t + i) = β) ∧
    (∀ P, 0 < P → ∀ r, ¬ ∃ K β, ∀ k, K ≤ k → trace x (r + k * P) = β) ∧
    (∀ τ, 0 < τ → {t | trace x t ≠ trace x (t + τ)}.Infinite) ∧
    (∀ (y : ℕ → Bool) (P : ℕ), 0 < P → (∀ t, y (t + P) = y t) →
      {t | trace x t ≠ y t}.Infinite) ∧
    ¬ (closure (Set.range fun n : ℕ => fun t => trace x (n + t))).Countable ∧
    (∃ a : ℝ, 1 < a ∧ ∀ n, a ^ n ≤ ((ShiftOrbit.factors (trace x) n).ncard : ℝ)) ∧
    Disjunctive (trace x) ∧ IsNormal (trace x) ∧
    Transcendental ℚ (BinaryIrrational.baseValue 2 (trace x)) ∧
    IrrExponentGE (BinaryIrrational.baseValue 2 (trace x)) 2 ∧
    (∀ C, ∃ n, C < abelianComplexity (trace x) n) ∧
    ¬ IsMorphic (trace x) ∧
    IsRecurrent (trace x) ∧ (¬ ∃ P, 0 < P ∧ ∀ t, trace x (t + P) = trace x t) ∧
    Tendsto (fun n : ℕ => (linComplexity (trace x) n : ℝ) / n) atTop (𝓝 (1 / 2)) ∧
    (∀ k (hk : k ≠ 0), 2 ≤ k → ¬ IsMahler k hk (LinearRelations.series ℚ (trace x))) ∧
    ∀ D : ℕ, ∃ n : ℕ, ∀ g : Polynomial (Polynomial (ZMod 2)), g ≠ 0 → g.natDegree ≤ D →
      (∀ i, (g.coeff i).natDegree ≤ D) →
        PowerSeries.trunc n (g.eval₂ Polynomial.coeToPowerSeries.ringHom
          (LinearRelations.series (ZMod 2) (trace x))) ≠ 0 := by
  filter_upwards [ae_isNormal_trace, Mixing.ae_every_line, ae_transcendental_trace,
    ae_not_isMorphic_trace, LinearComplexity.ae_tendsto_linComplexity_trace, ae_not_isMahler_trace,
    ae_expansionComplexity_unbounded_trace] with x hn hline htr hmor hlin hmah hexp
  have hd : Disjunctive (trace x) := fun n w => disjunctive_of_isNormal hn n w
  refine ⟨not_eventuallyPeriodic_and_of_disjunctive hd, hline, fun β n => ?_,
    fun P hP r => antiToeplitz_of_disjunctive hd hP r,
    fun τ hτ => infinite_disagreements_of_disjunctive hd hτ,
    fun y P hP hy => infinite_ne_periodic_of_disjunctive hd hP hy, ?_,
    ⟨2, one_lt_two, fun n => le_of_eq (by rw [ncard_factors_of_disjunctive hd n]; push_cast; rfl)⟩,
    hd, hn, htr, irrExponentGE_two_of_irrational
      ((BinaryIrrational.irrational_iff_not_eventuallyPeriodic le_rfl (trace x)).2
        (not_eventuallyPeriodic_of_disjunctive hd)),
    fun C => ⟨C, by rw [abelianComplexity_of_disjunctive hd]; omega⟩, hmor,
    isRecurrent_of_disjunctive hd, not_purelyPeriodic_of_disjunctive hd, hlin, hmah, hexp⟩
  · obtain ⟨t, ht⟩ := hd n fun _ => β
    exact ⟨t, fun i hi => ht ⟨i, hi⟩⟩
  · rw [closure_shifts_of_disjunctive hd]
    exact not_countable_univ

/-- **The defect bound is not typical**: it fails, at `T = 0` and `P = 1`, for every configuration
whose center column starts with five white cells, so with probability at least `2^-5`. -/
theorem measure_not_defectBound_trace :
    (2⁻¹ : ENNReal) ^ 5 ≤ coins ℤ {x | ¬ ∀ T P, 0 < P → ∃ t, T ≤ t ∧
      t ≤ T + 3 * Nat.log 2 (T + P + 1) ∧ trace x (t + P) ≠ trace x t} := by
  rw [← measure_prefix (fun _ => false) 4]
  refine measure_mono fun x hx h => ?_
  obtain ⟨t, -, ht, hne⟩ := h 0 1 one_pos
  have hlog : Nat.log 2 (0 + 1 + 1) = 1 := by decide
  rw [hlog] at ht
  exact hne (by rw [hx (t + 1) (by omega), hx t (by omega)])

/-- **Nonvanishing Hankel determinants are not typical**: `H_m ≠ 0` for every `m ≥ 9` fails for
every configuration whose center column starts with nine white cells, since then the first row of
`H_9` vanishes, so it fails with probability at least `2^-9`. -/
theorem measure_hankel_det_eq_zero_trace : (2⁻¹ : ENNReal) ^ 9 ≤
    coins ℤ {x | ¬ ∀ m, 9 ≤ m → (LinearRelations.hankel ℤ (trace x) m).det ≠ 0} := by
  rw [← measure_prefix (fun _ => false) 8]
  refine measure_mono fun x hx h => h 9 le_rfl (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_)
  simp only [LinearRelations.hankel, Matrix.of_apply, LinearRelations.toK, Fin.val_zero, zero_add]
  rw [hx j (by omega)]
  rfl

end Rule30Equivalents.Typicality
