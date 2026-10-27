module

public import Rule30Equivalents.LongestRuns
public import Rule30Equivalents.WordsAutomata
public import Rule30Equivalents.Mixing
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
# The maximum-order complexity of a random center column

The maximum-order complexity `M_n` of a sequence (`WordsAutomata.maxOrderComplexity`) is the least
`m` such that, among the first `n` letters, equal windows of length `m` are always followed by
equal letters: the length of the shortest feedback shift register that generates the prefix of
length `n`. Problem 1 holds iff `M_n → ∞` for the center column
(`WordsAutomata.problem1_iff_maxOrderComplexity_tendsto`).

* `ae_tendsto_maxOrderComplexity_trace`: **for almost every configuration, the maximum-order
  complexity of the center column is `2 log₂ n (1 + o(1))`**, like that of fair coins
  (`ae_tendsto_maxOrderComplexity`), and so along every line of rational velocity other than `1`
  (`Lines.ae_tendsto_maxOrderComplexity_lines`).
* The upper bound (`measure_lt_maxOrderComplexity_le`): `M_n > L` needs two equal windows of length
  `L` among the first `n` letters, and each of the `n²` pairs of windows agrees with probability
  `2^-L` (`measure_windows_eq`), even when they overlap.
* The lower bound (`measureReal_maxOrderComplexity_lt_le`) is the birthday paradox: cut the first
  `2KB` letters into `2K` blocks of length `B`. A block of the first half and a block of the second
  half that agree in their first `B - 1` letters and differ in the last (`GoodPair`) force
  `M_n ≥ B` (`le_maxOrderComplexity_of_goodPair`). Each of the `K²` pairs does so with probability
  `2^-B`, and any two of these events are independent (`measure_goodPair_inter`, flipping coins of
  a block that only one of them sees), so by the second-moment method
  (`measureReal_forall_notMem_le`) none does with probability at most `2^B/K²`.

Sources: C. J. A. Jansen and D. E. Boekee, *The shortest feedback shift register that can generate
a given sequence*, CRYPTO '89, LNCS 435 (1990) 90–99; R. Arratia and M. S. Waterman, *An
Erdős–Rényi law with shifts*, Adv. Math. 55 (1985) 13–23.
-/

@[expose] public section

namespace Rule30Equivalents.MaxOrderComplexity

open MeasureTheory Filter Topology Genericity RandomConfigurations WordsAutomata

/-! ### Triangular events and the second-moment method -/

/-- **Triangular events, finitely many**: as `RandomConfigurations.measure_triangular`, with the
flip conditions required only for the first `M` events. -/
theorem measure_triangular_lt {ι : Type*} [DecidableEq ι] (M : ℕ) (g : ℕ → (ι → Bool) → Bool)
    (hg : ∀ j < M, Measurable (g j)) (p : ℕ → ι)
    (hflip : ∀ j < M, ∀ v, g j (Function.update v (p j) (!v (p j))) = !g j v)
    (hfix : ∀ j < M, ∀ v, ∀ i < j, g i (Function.update v (p j) (!v (p j))) = g i v)
    (β : ℕ → Bool) : ∀ m ≤ M, coins ι {v | ∀ j < m, g j v = β j} = 2⁻¹ ^ m
  | 0, _ => by simp
  | m + 1, hm => by
    set E := {v : ι → Bool | ∀ j < m, g j v = β j} with hEdef
    have hE : MeasurableSet E := by
      simp only [hEdef, Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
        hg j (by omega) (measurableSet_singleton _)
    have hinv : ∀ v, Function.update v (p m) (!v (p m)) ∈ E ↔ v ∈ E := fun v => by
      simp only [hEdef, Set.mem_ofPred_eq]
      exact forall₂_congr fun j hj => by rw [hfix m (by omega) v j hj]
    have h := two_mul_measure_flip hE (hg m (by omega)) (p m) hinv
      (fun v _ => hflip m (by omega) v) (β m)
    have hset : {v : ι → Bool | ∀ j < m + 1, g j v = β j} = E ∩ {v | g m v = β m} := by
      ext v
      simp only [hEdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hv
        exact ⟨fun j hj => hv j (by omega), hv m (by omega)⟩
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_or_ge j m with h' | h'
        · exact h1 j h'
        · obtain rfl : j = m := by omega
          exact h2
    rw [hset, eq_mul_inv_of_two_mul h,
      measure_triangular_lt M g hg p hflip hfix β m (by omega), pow_succ]

/-- **The second-moment method**: if `N` events have probability `p` each and are pairwise
independent, then none of them occurs with probability at most `1/(N p)`. With `Z` the number of
events that occur, `E Z = N p` and `E Z² ≤ N p + (N p)²`, and `(Z - N p)² = (N p)²` where
`Z = 0`. -/
theorem measureReal_forall_notMem_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : Finset ι) {G : ι → Set Ω} (hG : ∀ s, MeasurableSet (G s))
    {p : ℝ} (hp : 0 < p) (h1 : ∀ s ∈ S, μ.real (G s) = p)
    (h2 : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → μ.real (G s ∩ G t) = p ^ 2) (hS : S.Nonempty) :
    μ.real {ω | ∀ s ∈ S, ω ∉ G s} ≤ 1 / (S.card * p) := by
  classical
  set Z : Ω → ℝ := fun ω => ∑ s ∈ S, (G s).indicator 1 ω with hZ
  set m : ℝ := S.card * p with hm
  have hm0 : 0 < m := by
    have : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    positivity
  have hint1 : ∀ s, Integrable ((G s).indicator (1 : Ω → ℝ)) μ := fun s =>
    (integrable_const (1 : ℝ)).indicator (hG s)
  have hint2 : ∀ s t, Integrable ((G s ∩ G t).indicator (1 : Ω → ℝ)) μ := fun s t =>
    (integrable_const (1 : ℝ)).indicator ((hG s).inter (hG t))
  have hZint : Integrable Z μ := integrable_finsetSum S fun s _ => hint1 s
  have hEZ : ∫ ω, Z ω ∂μ = m := by
    rw [hZ, integral_finsetSum S fun s _ => hint1 s]
    simp_rw [integral_indicator_one (hG _)]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  have hZ2 : ∀ ω, Z ω ^ 2 = ∑ s ∈ S, ∑ t ∈ S, (G s ∩ G t).indicator 1 ω := fun ω => by
    rw [sq, hZ, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Set.inter_indicator_one]
    rfl
  have hZ2int : Integrable (fun ω => Z ω ^ 2) μ := by
    simp_rw [hZ2]
    exact integrable_finsetSum S fun s _ => integrable_finsetSum S fun t _ => hint2 s t
  have hEZ2 : ∫ ω, Z ω ^ 2 ∂μ ≤ m + m ^ 2 := by
    simp_rw [hZ2]
    rw [integral_finsetSum S fun s _ => integrable_finsetSum S fun t _ => hint2 s t]
    simp_rw [integral_finsetSum S fun t _ => hint2 _ t,
      integral_indicator_one ((hG _).inter (hG _))]
    calc ∑ s ∈ S, ∑ t ∈ S, μ.real (G s ∩ G t) ≤ ∑ s ∈ S, (p + S.card * p ^ 2) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [← Finset.add_sum_erase S _ hs, Set.inter_self, h1 s hs]
          refine add_le_add le_rfl ?_
          calc ∑ t ∈ S.erase s, μ.real (G s ∩ G t) = ∑ t ∈ S.erase s, p ^ 2 :=
                Finset.sum_congr rfl fun t ht =>
                  h2 s hs t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht).symm
            _ ≤ S.card * p ^ 2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le)
                  (sq_nonneg p)
      _ = m + m ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, hm]; ring
  set E := {ω | ∀ s ∈ S, ω ∉ G s} with hEdef
  have hE : MeasurableSet E := by
    have : E = ⋂ s ∈ S, (G s)ᶜ := by
      ext ω
      simp [hEdef]
    rw [this]
    exact Finset.measurableSet_biInter S fun s _ => (hG s).compl
  have hpt : ∀ ω, m ^ 2 * E.indicator 1 ω ≤ Z ω ^ 2 - 2 * m * Z ω + m ^ 2 := fun ω => by
    by_cases hω : ω ∈ E
    · have hZ0 : Z ω = 0 := Finset.sum_eq_zero fun s hs => Set.indicator_of_notMem (hω s hs) _
      rw [Set.indicator_of_mem hω, Pi.one_apply, hZ0]
      ring_nf
      rfl
    · rw [Set.indicator_of_notMem hω, mul_zero]
      nlinarith [sq_nonneg (Z ω - m)]
  have hL : Integrable (fun ω => m ^ 2 * E.indicator (1 : Ω → ℝ) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hE).const_mul (m ^ 2)
  have hB : Integrable (fun ω => 2 * m * Z ω) μ := hZint.const_mul (2 * m)
  have hA : Integrable (fun ω => Z ω ^ 2 - 2 * m * Z ω) μ := hZ2int.sub hB
  have hR : Integrable (fun ω => Z ω ^ 2 - 2 * m * Z ω + m ^ 2) μ :=
    hA.add (integrable_const (m ^ 2))
  have hmono := integral_mono hL hR hpt
  rw [integral_const_mul, integral_indicator_one hE, integral_add hA (integrable_const _),
    integral_sub hZ2int hB, integral_const_mul, hEZ, integral_const] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  rw [le_div_iff₀ hm0]
  nlinarith

/-! ### Monotonicity and the upper bound -/

theorem prefixConsistent_maxOrderComplexity (b : ℕ → Bool) (n : ℕ) :
    PrefixConsistent b n (maxOrderComplexity b n) := by
  by_contra h
  exact lt_irrefl _ ((lt_maxOrderComplexity_iff b n _).2 h)

/-- The maximum-order complexity of the prefixes increases with their length. -/
theorem maxOrderComplexity_mono (b : ℕ → Bool) {n n' : ℕ} (hn : n ≤ n') :
    maxOrderComplexity b n ≤ maxOrderComplexity b n' := by
  by_contra h
  push Not at h
  exact (lt_maxOrderComplexity_iff b n _).1 h fun i j hi hj hw =>
    prefixConsistent_maxOrderComplexity b n' i j (by omega) (by omega) hw

theorem measurable_decide_eq (x y : ℕ) : Measurable fun v : ℕ → Bool => decide (v x = v y) :=
  measurable_of_forall_lt (max x y + 1) fun v w h => by
    simp only [h x (by omega), h y (by omega)]

/-- Two windows of length `L` starting at `i < j` agree with probability `2^-L`, also when they
overlap: the coins `j, j + 1, …` decide the tests one after the other. -/
theorem measure_windows_eq {i j : ℕ} (hij : i < j) (L : ℕ) :
    coins ℕ {v | ∀ k < L, v (i + k) = v (j + k)} = 2⁻¹ ^ L := by
  have h := measure_triangular (ι := ℕ) (fun k v => decide (v (j + k) = v (i + k)))
    (fun k => measurable_decide_eq _ _) (fun k => j + k)
    (fun k v => by
      simp only [Function.update_self, Function.update_of_ne (show i + k ≠ j + k by omega)]
      cases v (j + k) <;> cases v (i + k) <;> rfl)
    (fun k v k' hk' => by
      simp only [Function.update_of_ne (show j + k' ≠ j + k by omega),
        Function.update_of_ne (show i + k' ≠ j + k by omega)])
    (fun _ => true) L
  rw [← h]
  congr 1
  ext v
  simp [eq_comm]

/-- **A high maximum-order complexity is rare**: it exceeds `L` among the first `n` letters with
probability at most `n² 2^-L`, since two windows of length `L` must agree. -/
theorem measure_lt_maxOrderComplexity_le (n L : ℕ) :
    coins ℕ {v | L < maxOrderComplexity v n} ≤ (n : ENNReal) ^ 2 * 2⁻¹ ^ L := by
  classical
  let A : ℕ → ℕ → Set (ℕ → Bool) := fun i j => {v | i < j ∧ ∀ k < L, v (i + k) = v (j + k)}
  have hsub : {v | L < maxOrderComplexity v n} ⊆
      ⋃ i ∈ Finset.range n, ⋃ j ∈ Finset.range n, A i j := by
    intro v hv
    have h := (lt_maxOrderComplexity_iff v n L).1 hv
    simp only [PrefixConsistent] at h
    push Not at h
    obtain ⟨i, j, hi, hj, hw, hne⟩ := h
    simp only [Set.mem_iUnion, Finset.mem_range, A, Set.mem_ofPred_eq]
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact ⟨i, by omega, j, by omega, hij, hw⟩
    · exact absurd rfl hne
    · exact ⟨j, by omega, i, by omega, hij, fun k hk => (hw k hk).symm⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ i ∈ Finset.range n, coins ℕ (⋃ j ∈ Finset.range n, A i j)
      ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (2⁻¹ : ENNReal) ^ L :=
        Finset.sum_le_sum fun i _ => (measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun j _ => by
            by_cases hij : i < j
            · exact (measure_mono fun v hv => hv.2).trans (measure_windows_eq hij L).le
            · have : A i j = ∅ := Set.eq_empty_of_forall_notMem fun v hv => hij hv.1
              rw [this, measure_empty]
              exact zero_le)
    _ = (n : ENNReal) ^ 2 * 2⁻¹ ^ L := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
        ring

/-! ### Good pairs of blocks and the lower bound -/

/-- In blocks of length `B`, letter `k < B` of block `x` sits at `x B + k`, and different
(block, letter) pairs sit at different places. -/
theorem block_ne {B x y k k' : ℕ} (hk : k < B) (hk' : k' < B) (h : x ≠ y ∨ k ≠ k') :
    x * B + k ≠ y * B + k' := by
  intro heq
  have hB : 0 < B := by omega
  have hx : (x * B + k) / B = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hk, zero_add]
  have hy : (y * B + k') / B = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hk', zero_add]
  have hxy : x = y := by rw [← hx, ← hy, heq]
  subst hxy
  rcases h with h | h
  · exact h rfl
  · exact h (by omega)

/-- Blocks `a` and `b` of length `B` agree in their first `B - 1` letters and differ in the last
one. -/
def GoodPair (B a b : ℕ) : Set (ℕ → Bool) :=
  {v | ∀ k < B, decide (v (a * B + k) = v (b * B + k)) = decide (k + 1 < B)}

theorem goodPair_comm (B a b : ℕ) : GoodPair B a b = GoodPair B b a := by
  ext v
  simp only [GoodPair, Set.mem_ofPred_eq]
  refine forall₂_congr fun k _ => ?_
  rw [decide_eq_decide.2 eq_comm]

theorem measurableSet_goodPair (B a b : ℕ) : MeasurableSet (GoodPair B a b) := by
  have : GoodPair B a b = ⋂ k ∈ Finset.range B,
      {v | decide (v (a * B + k) = v (b * B + k)) = decide (k + 1 < B)} := by
    ext v
    simp [GoodPair]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ =>
    measurable_decide_eq _ _ (measurableSet_singleton _)

/-- **A good pair forces a high complexity**: if blocks `a` and `b` of length `B ≥ 1` lie in the
first `n` letters and form a good pair, then `M_n ≥ B`. -/
theorem le_maxOrderComplexity_of_goodPair {B a b n : ℕ} (hB : 0 < B)
    (ha : (a + 1) * B ≤ n) (hb : (b + 1) * B ≤ n) {v : ℕ → Bool} (hv : v ∈ GoodPair B a b) :
    B ≤ maxOrderComplexity v n := by
  have ha' : (a + 1) * B = a * B + B := by ring
  have hb' : (b + 1) * B = b * B + B := by ring
  have hlast : v (a * B + (B - 1)) ≠ v (b * B + (B - 1)) := by
    intro heq
    have h := hv (B - 1) (by omega)
    rw [decide_eq_true heq] at h
    exact absurd (of_decide_eq_true h.symm) (by omega)
  have h := (lt_maxOrderComplexity_iff v n (B - 1)).2 fun hc =>
    hlast (hc (a * B) (b * B) (by omega) (by omega) fun k hk => by
      have h := hv k (by omega)
      rw [decide_eq_true (show k + 1 < B by omega)] at h
      exact of_decide_eq_true h)
  omega

/-- **A good pair has probability `2^-B`**: the coins of the later block decide its `B` tests one
after the other. -/
theorem measure_goodPair {B a b : ℕ} (hab : a < b) :
    coins ℕ (GoodPair B a b) = 2⁻¹ ^ B := by
  have h := measure_triangular_lt B (fun k v => decide (v (a * B + k) = v (b * B + k)))
    (fun k _ => measurable_decide_eq _ _) (fun k => b * B + k)
    (fun k hk v => by
      simp only [Function.update_self, Function.update_of_ne (block_ne hk hk (Or.inl hab.ne))]
      cases v (a * B + k) <;> cases v (b * B + k) <;> rfl)
    (fun k hk v i hi => by
      simp only [Function.update_of_ne (block_ne (hi.trans hk) hk (Or.inl hab.ne)),
        Function.update_of_ne (block_ne (hi.trans hk) hk (Or.inr hi.ne))])
    (fun k => decide (k + 1 < B)) B le_rfl
  rw [← h]
  rfl

/-- **Two different good pairs are independent**: the coins of a block of the second pair that the
first pair does not use decide the tests of the second pair. -/
theorem measure_goodPair_inter {B a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (hne : (a, b) ≠ (c, d)) :
    coins ℕ (GoodPair B a b ∩ GoodPair B c d) = 2⁻¹ ^ (2 * B) := by
  have hne' : ¬ (a = c ∧ b = d) := fun h => hne (by rw [h.1, h.2])
  -- a block `e` of the second pair outside the first, and its partner `f`
  obtain ⟨e, f, hea, heb, hef, hset⟩ : ∃ e f, e ≠ a ∧ e ≠ b ∧ e ≠ f ∧
      GoodPair B c d = GoodPair B f e := by
    by_cases hd : d = a ∨ d = b
    · refine ⟨c, d, ?_, ?_, hcd.ne, goodPair_comm B c d⟩ <;> rintro rfl <;> rcases hd with rfl | rfl
      · omega
      · exact hne' ⟨rfl, rfl⟩
      · omega
      · omega
    · push Not at hd
      exact ⟨d, c, hd.1, hd.2, hcd.ne', rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → (ℕ → Bool) → Bool, g = fun j =>
      if j < B then fun v => decide (v (a * B + j) = v (b * B + j))
      else fun v => decide (v (f * B + (j - B)) = v (e * B + (j - B))) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℕ, p = fun j => if j < B then b * B + j else e * B + (j - B) :=
    ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → Bool, β = fun j =>
      if j < B then decide (j + 1 < B) else decide (j - B + 1 < B) := ⟨_, rfl⟩
  have h := measure_triangular_lt (2 * B) g
    (fun j _ => by
      simp only [hg]
      split_ifs <;> exact measurable_decide_eq _ _)
    p
    (fun j hj v => by
      simp only [hg, hp]
      split_ifs with hjB
      · simp only [Function.update_self,
          Function.update_of_ne (block_ne hjB hjB (Or.inl hab.ne))]
        cases v (a * B + j) <;> cases v (b * B + j) <;> rfl
      · have hk : j - B < B := by omega
        simp only [Function.update_self, Function.update_of_ne (block_ne hk hk (Or.inl hef.symm))]
        cases v (f * B + (j - B)) <;> cases v (e * B + (j - B)) <;> rfl)
    (fun j hj v i hi => by
      rw [hg, hp]
      by_cases hjB : j < B
      · have hiB : i < B := hi.trans hjB
        simp only [hjB, hiB, ite_true]
        simp only [Function.update_of_ne (block_ne hiB hjB (Or.inl hab.ne)),
          Function.update_of_ne (block_ne hiB hjB (Or.inr hi.ne))]
      · have hk : j - B < B := by omega
        simp only [hjB, ite_false]
        by_cases hiB : i < B
        · simp only [hiB, ite_true]
          simp only [Function.update_of_ne (block_ne hiB hk (Or.inl (Ne.symm hea))),
            Function.update_of_ne (block_ne hiB hk (Or.inl (Ne.symm heb)))]
        · have hk' : i - B < B := by omega
          have hik : i - B ≠ j - B := by omega
          simp only [hiB, ite_false]
          simp only [Function.update_of_ne (block_ne hk' hk (Or.inl hef.symm)),
            Function.update_of_ne (block_ne hk' hk (Or.inr hik))])
    β (2 * B) le_rfl
  rw [hset, ← h]
  congr 1
  ext v
  simp only [Set.mem_inter_iff, GoodPair, Set.mem_ofPred_eq, hg, hβ]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjB : j < B
    · simpa [hjB] using h1 j hjB
    · obtain ⟨k, rfl⟩ : ∃ k, j = B + k := ⟨j - B, by omega⟩
      simpa [hjB] using h2 k (by omega)
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simpa [hk] using h k (by omega)
    · simpa [show ¬ B + k < B by omega] using h (B + k) (by omega)

/-- **The birthday bound**: if `2 K B ≤ n` with `B, K ≥ 1`, then `M_n < B` with probability at
most `2^B/K²`. Each of the `K²` pairs of a block among the first `K` and a block among the next
`K` is good with probability `2^-B`, independently in pairs. -/
theorem measureReal_maxOrderComplexity_lt_le {B K n : ℕ} (hB : 0 < B) (hK : 0 < K)
    (hn : 2 * K * B ≤ n) :
    (coins ℕ).real {v | maxOrderComplexity v n < B} ≤ 2 ^ B / K ^ 2 := by
  classical
  let S := Finset.range K ×ˢ Finset.Ico K (2 * K)
  have hS : S.Nonempty := ⟨(0, K), by simp [S, hK]⟩
  have hcard : S.card = K * K := by
    simp only [S, Finset.card_product, Finset.card_range, Nat.card_Ico,
      show 2 * K - K = K by omega]
  have hmem : ∀ s ∈ S, s.1 < K ∧ K ≤ s.2 ∧ s.2 < 2 * K := fun s hs => by
    simp only [S, Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hs
    omega
  have hsub : {v | maxOrderComplexity v n < B} ⊆
      {v | ∀ s ∈ S, v ∉ GoodPair B s.1 s.2} := by
    intro v hv s hs hgood
    obtain ⟨h1, h2, h3⟩ := hmem s hs
    have hle1 : (s.1 + 1) * B ≤ n :=
      (Nat.mul_le_mul_right B (show s.1 + 1 ≤ 2 * K by omega)).trans hn
    have hle2 : (s.2 + 1) * B ≤ n :=
      (Nat.mul_le_mul_right B (show s.2 + 1 ≤ 2 * K by omega)).trans hn
    exact absurd hv (not_lt.2 (le_maxOrderComplexity_of_goodPair hB hle1 hle2 hgood))
  have hp : (0 : ℝ) < 2⁻¹ ^ B := by positivity
  refine (measureReal_mono hsub).trans ((measureReal_forall_notMem_le S
    (G := fun s => GoodPair B s.1 s.2) (fun s => measurableSet_goodPair B _ _) hp
    (fun s hs => ?_) (fun s hs t ht hst => ?_) hS).trans (le_of_eq ?_))
  · obtain ⟨h1, h2, -⟩ := hmem s hs
    rw [measureReal_def, measure_goodPair (show s.1 < s.2 by omega)]
    simp
  · obtain ⟨h1, h2, -⟩ := hmem s hs
    obtain ⟨h1', h2', -⟩ := hmem t ht
    rw [measureReal_def, measure_goodPair_inter (show s.1 < s.2 by omega)
      (show t.1 < t.2 by omega) hst, pow_mul]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    rw [← pow_mul, mul_comm, pow_mul]
  · rw [hcard]
    push_cast
    field_simp
    rw [← mul_pow]
    norm_num

/-! ### Almost surely -/

/-- The lower events are summable: at `n = 2^(q(j+4))`, `M_n < (2q - 2) j` has probability at
most `q² j² 4^-j`. -/
theorem measureReal_maxOrderComplexity_lt_pow_le {q : ℕ} (hq : 2 ≤ q) (j : ℕ) :
    (coins ℕ).real {v | maxOrderComplexity v (2 ^ (q * (j + 4))) < (2 * q - 2) * j} ≤
      (q : ℝ) ^ 2 * ((j : ℝ) ^ 2 * (1 / 4) ^ j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  obtain ⟨B, hBdef⟩ : ∃ B, B = (2 * q - 2) * j := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 ^ (q * (j + 4)) := ⟨_, rfl⟩
  rw [← hBdef, ← hNdef]
  have hB : 0 < B := hBdef ▸ Nat.mul_pos (by omega) hj
  have hB2 : B + 2 * j = 2 * q * j := by
    rw [hBdef, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  -- `N² = 2^B 4^j 2^(8q)` and `N ≥ 4B`
  have hN2 : N ^ 2 = 2 ^ B * 4 ^ j * 2 ^ (8 * q) := by
    rw [hNdef, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    nlinarith [hB2]
  have hN4 : 4 * B ≤ N := by
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 8 * q ≤ 2 ^ (4 * q) := by
      have := Nat.lt_two_pow_self (n := q)
      calc 8 * q ≤ 2 ^ 3 * 2 ^ q := by omega
        _ = 2 ^ (q + 3) := by rw [← pow_add, add_comm]
        _ ≤ 2 ^ (4 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ j ≤ 2 ^ (q * j) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    calc 4 * B ≤ 8 * q * j := by rw [hBdef]; nlinarith
      _ ≤ 2 ^ (4 * q) * 2 ^ (q * j) := Nat.mul_le_mul h2 (h1.le.trans h3)
      _ = N := by rw [hNdef, ← pow_add]; ring_nf
  obtain ⟨K, hKdef⟩ : ∃ K, K = N / (2 * B) := ⟨_, rfl⟩
  have hK : 0 < K := hKdef ▸ Nat.div_pos (by omega) (by omega)
  have hKB : 2 * K * B ≤ N := by
    have := Nat.div_mul_le_self N (2 * B)
    rw [← hKdef] at this
    calc 2 * K * B = K * (2 * B) := by ring
      _ ≤ N := this
  refine (measureReal_maxOrderComplexity_lt_le hB hK hKB).trans ?_
  -- `K ≥ N/(4B)`
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hKr : (N : ℝ) / (4 * B) ≤ K := by
    have h := Nat.lt_div_mul_add (a := N) (b := 2 * B) (by omega)
    rw [← hKdef] at h
    have h' : (N : ℝ) < K * (2 * B) + 2 * B := by exact_mod_cast h
    have h4 : (4 * B : ℝ) ≤ N := by exact_mod_cast hN4
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hN2r : (N : ℝ) ^ 2 = 2 ^ B * 4 ^ j * 2 ^ (8 * q) := by exact_mod_cast hN2
  have hBq : (B : ℝ) ≤ 2 * q * j := by
    have : B ≤ 2 * q * j := by omega
    exact_mod_cast this
  have h64 : (64 : ℝ) ≤ 2 ^ (8 * q) := by
    have : (2 : ℝ) ^ 6 ≤ 2 ^ (8 * q) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this
    exact this
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  calc (2 : ℝ) ^ B / (K : ℝ) ^ 2 ≤ (2 : ℝ) ^ B / ((N : ℝ) / (4 * B)) ^ 2 := by
        gcongr
    _ = 16 * (B : ℝ) ^ 2 / ((4 : ℝ) ^ j * 2 ^ (8 * q)) := by
        rw [div_pow, div_div_eq_mul_div, hN2r]
        field_simp
        ring
    _ ≤ 64 * (q : ℝ) ^ 2 * (j : ℝ) ^ 2 / ((4 : ℝ) ^ j * 64) := by
        apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
        · have := mul_le_mul hBq hBq hBr.le (by positivity : (0 : ℝ) ≤ 2 * q * j)
          nlinarith
        · exact mul_le_mul_of_nonneg_left h64 (by positivity)
    _ = (q : ℝ) ^ 2 * ((j : ℝ) ^ 2 * (1 / 4) ^ j) := by
        rw [one_div, inv_pow]
        field_simp

/-- **The maximum-order complexity, in bounds**: for almost every fair-coin sequence and every
`q ≥ 2`, `(2q - 2)(⌊⌊log₂ n⌋/q⌋ - 4) ≤ M_n ≤ (2q + 1)(⌊⌊log₂ n⌋/q⌋ + 1)` from some `n` on. -/
theorem ae_eventually_maxOrderComplexity :
    ∀ᵐ v ∂(coins ℕ), ∀ q : ℕ, 2 ≤ q → ∀ᶠ n in atTop,
      (2 * q - 2) * (Nat.log 2 n / q - 4) ≤ maxOrderComplexity v n ∧
        maxOrderComplexity v n ≤ (2 * q + 1) * (Nat.log 2 n / q + 1) := by
  refine ae_all_iff.2 fun q => ?_
  rcases Nat.lt_or_ge q 2 with hq | hq
  · exact Eventually.of_forall fun _ h => absurd h (by omega)
  -- the upper events along `2^(q(j+1))`
  have hup : ∑' j : ℕ, coins ℕ {v | (2 * q + 1) * (j + 1) <
      maxOrderComplexity v (2 ^ (q * (j + 1)))} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) ?_
      (ENNReal.tsum_le_tsum fun j => ?_)
    · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    · refine (measure_lt_maxOrderComplexity_le _ _).trans ?_
      calc ((2 ^ (q * (j + 1)) : ℕ) : ENNReal) ^ 2 * 2⁻¹ ^ ((2 * q + 1) * (j + 1))
          = (2 ^ (2 * q * (j + 1)) * 2⁻¹ ^ (2 * q * (j + 1))) * 2⁻¹ ^ (j + 1) := by
            rw [show (2 * q + 1) * (j + 1) = 2 * q * (j + 1) + (j + 1) by ring, pow_add,
              Nat.cast_pow, Nat.cast_ofNat, ← pow_mul,
              show q * (j + 1) * 2 = 2 * q * (j + 1) by ring]
            ring
        _ = 2⁻¹ ^ (j + 1) := by
            rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow,
              one_mul]
        _ ≤ 2⁻¹ ^ j := pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ j)
  -- the lower events along `2^(q(j+4))`
  have hlow : ∑' j : ℕ, coins ℕ {v | maxOrderComplexity v (2 ^ (q * (j + 4))) <
      (2 * q - 2) * j} ≠ ⊤ := by
    have hsumm : Summable fun j : ℕ => (q : ℝ) ^ 2 * ((j : ℝ) ^ 2 * (1 / 4) ^ j) :=
      (summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, (q : ℝ) ^ 2 * ((j : ℝ) ^ 2 * (1 / 4) ^ j))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (measureReal_maxOrderComplexity_lt_pow_le hq j)
  filter_upwards [ae_eventually_notMem hup, ae_eventually_notMem hlow] with v hv1 hv2 _
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hv1.and hv2)
  filter_upwards [eventually_ge_atTop (2 ^ (q * (J + 4)))] with n hn
  set L := Nat.log 2 n with hL
  set j := L / q with hj
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := q * (J + 4))
    omega
  have hLJ : q * (J + 4) ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hJj : J + 4 ≤ j := by
    rw [hj, Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact hLJ
  constructor
  · -- `2^(q j) ≤ n`, and `j - 4 ≥ J`
    have hlo : 2 ^ (q * (j - 4 + 4)) ≤ n := by
      rw [Nat.sub_add_cancel (by omega)]
      refine (Nat.pow_le_pow_right (by norm_num) ?_).trans (Nat.pow_log_le_self 2 hn0)
      rw [hj, mul_comm]
      exact Nat.div_mul_le_self _ _
    have h2 := (hJ (j - 4) (by omega)).2
    simp only [not_lt] at h2
    exact h2.trans (maxOrderComplexity_mono v hlo)
  · -- `n ≤ 2^(q(j+1))`
    have hhi : n ≤ 2 ^ (q * (j + 1)) := by
      refine (Nat.lt_pow_succ_log_self (by norm_num) n).le.trans
        (Nat.pow_le_pow_right (by norm_num) ?_)
      have := Nat.lt_div_mul_add (a := L) (b := q) (by omega)
      rw [← hj] at this
      rw [Nat.succ_le_iff]
      nlinarith
    have h1 := (hJ j (by omega)).1
    simp only [not_lt] at h1
    exact (maxOrderComplexity_mono v hhi).trans h1

/-- **The maximum-order complexity of fair coins**: for almost every fair-coin sequence,
`M_n = 2 log₂ n (1 + o(1))`. -/
theorem ae_tendsto_maxOrderComplexity :
    ∀ᵐ v ∂(coins ℕ),
      Tendsto (fun n : ℕ => (maxOrderComplexity v n : ℝ) / Nat.log 2 n) atTop (𝓝 2) := by
  filter_upwards [ae_eventually_maxOrderComplexity] with v hv
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- `Q ≥ 2` with `(2 - a) Q > 4`, then `log₂ n` large
    obtain ⟨q, hq⟩ := exists_nat_gt (4 / (2 - a))
    have h2a : 0 < 2 - a := by linarith
    have hQa : 4 < (2 - a) * ((q + 2 : ℕ) : ℝ) := by
      have : 4 / (2 - a) < ((q + 2 : ℕ) : ℝ) := by push_cast; linarith
      rwa [div_lt_iff₀ h2a, mul_comm] at this
    obtain ⟨C, hC⟩ := exists_nat_gt (20 * ((q + 2 : ℕ) : ℝ) / (2 - a) + 5 * (q + 2 : ℕ))
    filter_upwards [hv (q + 2) (by omega), eventually_ge_atTop (2 ^ C)] with n hn hnC
    obtain ⟨h1, -⟩ := hn
    have hLC : C ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hnC
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = q + 2 := ⟨_, rfl⟩
    rw [← hQ] at h1 hQa hC
    obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 n := ⟨_, rfl⟩
    rw [← hL] at h1 hLC ⊢
    have hQr : (2 : ℝ) ≤ Q := by rw [hQ]; push_cast; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    have hCr : 20 * (Q : ℝ) / (2 - a) + 5 * Q < L := hC.trans_le (by exact_mod_cast hLC)
    have h5Q : 5 * Q ≤ L := by
      have : (5 * Q : ℝ) < L := by
        have : (0 : ℝ) ≤ 20 * (Q : ℝ) / (2 - a) := by positivity
        linarith
      exact_mod_cast this.le
    have hx5 : 5 ≤ L / Q := (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)
    have hxQ' : (L : ℝ) < ((L / Q : ℕ) + 1) * Q := by
      have := Nat.lt_div_mul_add (a := L) (b := Q) (by omega)
      have : L < (L / Q + 1) * Q := by rw [add_mul, one_mul]; exact this
      exact_mod_cast this
    have hM : ((2 * Q - 2 : ℕ) : ℝ) * ((L / Q - 4 : ℕ) : ℝ) ≤ maxOrderComplexity v n := by
      exact_mod_cast h1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hM
    push_cast at hM
    have hLpos : (0 : ℝ) < L := by linarith [(by positivity : (0 : ℝ) ≤ 20 * (Q : ℝ) / (2 - a))]
    rw [lt_div_iff₀ hLpos]
    -- `Q M ≥ (2Q - 2)(L - 5Q)` and `((2 - a) Q - 2) L > (2Q - 2) 5Q`
    have hL20 : 20 * (Q : ℝ) < (2 - a) * L := by
      have := (div_lt_iff₀ h2a).1 (show 20 * (Q : ℝ) / (2 - a) < L by linarith)
      linarith
    have hx : (L : ℝ) - 5 * Q < ((L / Q : ℕ) - 4) * Q := by nlinarith
    have hQM : (2 * Q - 2) * ((L : ℝ) - 5 * Q) ≤ Q * maxOrderComplexity v n := by
      nlinarith
    nlinarith
  · -- `Q ≥ 2` with `(b - 2) Q > 4`, then `log₂ n` large
    obtain ⟨q, hq⟩ := exists_nat_gt (4 / (b - 2))
    have hb2 : 0 < b - 2 := by linarith
    have hQb : 4 < (b - 2) * ((q + 2 : ℕ) : ℝ) := by
      have : 4 / (b - 2) < ((q + 2 : ℕ) : ℝ) := by push_cast; linarith
      rwa [div_lt_iff₀ hb2, mul_comm] at this
    obtain ⟨C, hC⟩ := exists_nat_gt (4 * (2 * ((q + 2 : ℕ) : ℝ) + 1) / (b - 2) + 1)
    filter_upwards [hv (q + 2) (by omega), eventually_ge_atTop (2 ^ C)] with n hn hnC
    obtain ⟨-, h2⟩ := hn
    have hLC : C ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hnC
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = q + 2 := ⟨_, rfl⟩
    rw [← hQ] at h2 hQb hC
    obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 n := ⟨_, rfl⟩
    rw [← hL] at h2 hLC ⊢
    have hQr : (2 : ℝ) ≤ Q := by rw [hQ]; push_cast; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    have hCr : 4 * (2 * (Q : ℝ) + 1) / (b - 2) + 1 < L := hC.trans_le (by exact_mod_cast hLC)
    have hLpos : (0 : ℝ) < L := by
      linarith [(by positivity : (0 : ℝ) ≤ 4 * (2 * (Q : ℝ) + 1) / (b - 2))]
    have hxQ : ((L / Q : ℕ) : ℝ) * Q ≤ L := by exact_mod_cast Nat.div_mul_le_self L Q
    have hM : (maxOrderComplexity v n : ℝ) ≤ (2 * Q + 1) * ((L / Q : ℕ) + 1) := by
      exact_mod_cast h2
    rw [div_lt_iff₀ hLpos]
    have hL4 : 4 * (2 * (Q : ℝ) + 1) < (b - 2) * L := by
      have := (div_lt_iff₀ hb2).1 (show 4 * (2 * (Q : ℝ) + 1) / (b - 2) < L by linarith)
      linarith
    -- `Q M ≤ (2Q + 1)(L + Q)` and `((b - 2) Q - 1) L > (2Q + 1) Q`
    have hQM : (Q : ℝ) * maxOrderComplexity v n ≤ (2 * Q + 1) * (L + Q) := by nlinarith
    nlinarith

/-- **The maximum-order complexity of random center columns**: for almost every configuration the
center column has `M_n = 2 log₂ n (1 + o(1))`. -/
theorem ae_tendsto_maxOrderComplexity_trace :
    ∀ᵐ x ∂(coins ℤ), Tendsto (fun n : ℕ => (maxOrderComplexity (trace x) n : ℝ) / Nat.log 2 n)
      atTop (𝓝 2) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_tendsto_maxOrderComplexity

end Rule30Equivalents.MaxOrderComplexity
