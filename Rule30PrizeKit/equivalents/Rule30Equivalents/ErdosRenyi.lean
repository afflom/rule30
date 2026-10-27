module

public import Rule30Equivalents.LargeDeviations
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
# The Erdős–Rényi law for the center column

How dense is the densest window of the center column of a random configuration? Among the first
`n` cells, the windows of length `L(n) = ⌊log n / I(α)⌋`, where `I(α) = log 2 - H(α)` and `H` is
the binary entropy, are at most a fraction `α` black, in the limit:

* `ae_tendsto_maxWindow_trace`: **for `1/2 < α < 1` and almost every configuration, the largest
  number of black cells in a window of length `L(n)` inside the first `n` cells of the center
  column, divided by `L(n)`, tends to `α`** (Erdős and Rényi). The longest runs of
  `LongestRuns` are the limiting case `α = 1`.

Write `N(L) = ⌈e^(L I(α))⌉`, so that `N(L(n)) ≤ n < N(L(n) + 1)`.
* From above (`ae_eventually_windows_lt`): for `β > α` a given window of length `L` is at least a
  fraction `β` black with probability at most `e^(-L I(β))` (Chernoff,
  `LargeDeviations.measureReal_le_exp`), and the windows starting before `N(L + 1)` number about
  `e^((L + 1) I(α))`. Since `I(β) > I(α)` these probabilities are summable in `L`.
* From below (`ae_eventually_exists_window_ge`): for `1/2 ≤ γ < α` the `N(L)/L` disjoint windows of
  length `L` are independent (`measureReal_all_windows_lt`), and each is at least a fraction `γ`
  black with probability at least `e^(-L I(γ'))/(L + 1)`, `γ' = (γ + α)/2`
  (`LargeDeviations.log_measureReal_ge`). So all of them fail with probability at most `e^(-L)`
  for large `L`.
-/

@[expose] public section

namespace Rule30Equivalents.ErdosRenyi

open MeasureTheory Filter Topology Genericity RandomConfigurations

/-- The number of black coins in the window `k, …, k + L - 1`. -/
noncomputable def windowOnes (v : ℕ → Bool) (k L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L, black (v (k + j))

/-- The largest number of black coins in a window of length `L` starting at `0, …, n - L`. -/
noncomputable def maxWindow (v : ℕ → Bool) (n L : ℕ) : ℝ :=
  (Finset.range (n - L + 1)).sup' Finset.nonempty_range_add_one fun k => windowOnes v k L

theorem windowOnes_eq (v : ℕ → Bool) (k L : ℕ) :
    windowOnes v k L = ∑ j : Fin L, black (v (k + j)) :=
  (Fin.sum_univ_eq_sum_range (fun j => black (v (k + j))) L).symm

/-- A window of a fair-coin sequence is a fair word. -/
theorem map_window (k L : ℕ) :
    (coins ℕ).map (fun v (j : Fin L) => v (k + j)) = coins (Fin L) := by
  have hinj : Function.Injective fun j : Fin L => k + (j : ℕ) :=
    fun i j h => Fin.ext (Nat.add_left_cancel h)
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

/-- A window is at least `x` black with the probability of a fair word of its length. -/
theorem measureReal_windowOnes_ge (k L : ℕ) (x : ℝ) :
    (coins ℕ).real {v | x ≤ windowOnes v k L} =
      (coins (Fin L)).real {w | x ≤ ∑ j, black (w j)} := by
  have hm : Measurable fun (v : ℕ → Bool) (j : Fin L) => v (k + j) := by fun_prop
  rw [← map_window k L, measureReal_def, measureReal_def,
    Measure.map_apply hm (Set.toFinite _).measurableSet]
  congr 2
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, windowOnes_eq]

/-- **Disjoint windows are independent**: the windows `iL, …, iL + L - 1`, `i < m`, all have fewer
than `x` black coins with probability `qᵐ`, `q` the probability for one fair word of length `L`. -/
theorem measureReal_all_windows_lt {L : ℕ} (hL : 0 < L) (m : ℕ) (x : ℝ) :
    (coins ℕ).real {v | ∀ i < m, windowOnes v (i * L) L < x} =
      ((coins (Fin L)).real {w | ∑ j, black (w j) < x}) ^ m := by
  have hΦ : Measurable fun (v : ℕ → Bool) k (j : Fin L) => v (0 + k * L + j) := by fun_prop
  have hT : MeasurableSet {w : Fin L → Bool | ∑ j, black (w j) < x} :=
    (Set.toFinite _).measurableSet
  have hset : {v : ℕ → Bool | ∀ i < m, windowOnes v (i * L) L < x} =
      (fun (v : ℕ → Bool) k (j : Fin L) => v (0 + k * L + j)) ⁻¹'
        Set.pi (Finset.range m : Set ℕ) fun _ => {w | ∑ j, black (w j) < x} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      windowOnes_eq, zero_add]
  rw [hset, measureReal_def,
    ← Measure.map_apply hΦ (MeasurableSet.pi (Set.to_countable _) fun _ _ => hT), map_blocks hL 0,
    Measure.infinitePi_pi _ fun _ _ => hT, Finset.prod_const, Finset.card_range, ENNReal.toReal_pow,
    ← measureReal_def]

/-- **The windows are not too dense**: for `1/2 < α < β < 1` and almost every fair-coin sequence,
for all large `L` every window of length `L` starting before `⌈e^((L + 1) I(α))⌉` is less than a
fraction `β` black. -/
theorem ae_eventually_windows_lt {α β : ℝ} (hα : 1 / 2 < α) (hαβ : α < β) (hβ : β < 1) :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ L : ℕ in atTop,
      ∀ k < ⌈Real.exp (((L : ℝ) + 1) * (Real.log 2 - Real.binEntropy α))⌉₊,
        windowOnes v k L < β * L := by
  set I := Real.log 2 - Real.binEntropy α with hI
  set J := Real.log 2 - Real.binEntropy β with hJ
  have hIJ : I < J := by
    have := Real.binEntropy_strictAntiOn (show α ∈ Set.Icc 2⁻¹ 1 by constructor <;> linarith)
      (show β ∈ Set.Icc 2⁻¹ 1 by constructor <;> linarith) hαβ
    rw [hI, hJ]
    linarith
  have hI0 : 0 < I := by
    have := Real.binEntropy_lt_log_two.2 (show α ≠ 2⁻¹ by intro h; rw [h] at hα; norm_num at hα)
    rw [hI]
    linarith
  set E : ℕ → Set (ℕ → Bool) := fun L =>
    {v | ∃ k < ⌈Real.exp (((L : ℝ) + 1) * I)⌉₊, β * L ≤ windowOnes v k L} with hE
  set r := Real.exp (-(J - I)) with hr
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hbound : ∀ L : ℕ, (coins ℕ).real (E L) ≤ 2 * Real.exp I * r ^ L := by
    intro L
    have hsub : E L ⊆ ⋃ k ∈ Finset.range ⌈Real.exp (((L : ℝ) + 1) * I)⌉₊,
        {v | β * L ≤ windowOnes v k L} := by
      rintro v ⟨k, hk, hv⟩
      exact Set.mem_biUnion (Finset.mem_range.2 hk) hv
    have hone : ∀ k, (coins ℕ).real {v | β * L ≤ windowOnes v k L} ≤
        Real.exp (L * (Real.binEntropy β - Real.log 2)) := fun k => by
      rw [measureReal_windowOnes_ge]
      exact LargeDeviations.measureReal_le_exp L (by linarith) hβ
    have hN : (⌈Real.exp (((L : ℝ) + 1) * I)⌉₊ : ℝ) ≤ 2 * Real.exp (((L : ℝ) + 1) * I) := by
      have h1 := Nat.ceil_lt_add_one (Real.exp_pos (((L : ℝ) + 1) * I)).le
      have h2 : 1 ≤ Real.exp (((L : ℝ) + 1) * I) := Real.one_le_exp (by positivity)
      linarith
    have e : ((L : ℝ) + 1) * I + L * (Real.binEntropy β - Real.log 2) = I + L * (-(J - I)) := by
      rw [hJ]
      ring
    calc (coins ℕ).real (E L)
        ≤ ∑ k ∈ Finset.range ⌈Real.exp (((L : ℝ) + 1) * I)⌉₊,
            (coins ℕ).real {v | β * L ≤ windowOnes v k L} :=
          (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
      _ ≤ ∑ _k ∈ Finset.range ⌈Real.exp (((L : ℝ) + 1) * I)⌉₊,
            Real.exp (L * (Real.binEntropy β - Real.log 2)) :=
          Finset.sum_le_sum fun k _ => hone k
      _ = ⌈Real.exp (((L : ℝ) + 1) * I)⌉₊ * Real.exp (L * (Real.binEntropy β - Real.log 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 2 * Real.exp (((L : ℝ) + 1) * I) * Real.exp (L * (Real.binEntropy β - Real.log 2)) :=
          mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
      _ = 2 * Real.exp I * r ^ L := by
          rw [hr, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add, e]
  have hsum : ∑' L, coins ℕ (E L) ≠ ⊤ := by
    have hsumm : Summable fun L : ℕ => 2 * Real.exp I * r ^ L :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left _
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' L : ℕ, 2 * Real.exp I * r ^ L)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun L => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun L => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hbound L)
  filter_upwards [ae_eventually_notMem hsum] with v hv
  filter_upwards [hv] with L hL k hk
  by_contra h
  exact hL ⟨k, hk, not_lt.1 h⟩

/-- **Some window is dense enough**: for `1/2 ≤ γ < α < 1` and almost every fair-coin sequence,
for all large `L` one of the disjoint windows `iL, …, iL + L - 1`, `i < ⌈e^(L I(α))⌉/L`, is at least
a fraction `γ` black. -/
theorem ae_eventually_exists_window_ge {α γ : ℝ} (hα : α < 1) (hγ : 1 / 2 ≤ γ) (hγα : γ < α) :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ L : ℕ in atTop,
      ∃ i < ⌈Real.exp (L * (Real.log 2 - Real.binEntropy α))⌉₊ / L,
        γ * L ≤ windowOnes v (i * L) L := by
  set I := Real.log 2 - Real.binEntropy α with hI
  set γ' := (γ + α) / 2 with hγ'
  set K := Real.log 2 - Real.binEntropy γ' with hK
  have hKI : K < I := by
    have := Real.binEntropy_strictAntiOn (show γ' ∈ Set.Icc 2⁻¹ 1 by constructor <;> linarith)
      (show α ∈ Set.Icc 2⁻¹ 1 by constructor <;> linarith) (by linarith)
    rw [hI, hK]
    linarith
  set δ := I - K with hδ
  have hδ0 : 0 < δ := by linarith
  -- from some `L₀` on: `1/L ≤ (α - γ)/2` and `(L + 1)³ ≤ e^(δ L)`
  have hev : ∀ᶠ L : ℕ in atTop, 1 ≤ L ∧ 2 / (α - γ) ≤ L ∧
      ((L : ℝ) + 1) ^ 3 ≤ Real.exp (δ * L) := by
    have h1 : ∀ᶠ L : ℕ in atTop, ((L : ℝ) + 1) ^ 3 / Real.exp δ ^ (L + 1) ≤ Real.exp (-δ) := by
      have := (tendsto_pow_const_div_const_pow_of_one_lt 3
        (Real.one_lt_exp_iff.2 hδ0)).comp (tendsto_add_atTop_nat 1)
      filter_upwards [this.eventually (ge_mem_nhds (Real.exp_pos (-δ)))] with L hL
      simpa using hL
    filter_upwards [h1, eventually_ge_atTop 1,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / (α - γ))] with L hL h2 h3
    refine ⟨h2, h3, ?_⟩
    have hpos : 0 < Real.exp δ ^ (L + 1) := by positivity
    rw [div_le_iff₀ hpos, ← Real.exp_nat_mul, ← Real.exp_add] at hL
    calc ((L : ℝ) + 1) ^ 3 ≤ Real.exp (-δ + ((L + 1 : ℕ) : ℝ) * δ) := hL
      _ = Real.exp (δ * L) := by congr 1; push_cast; ring
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hev
  -- the events: every window fails
  set D : ℕ → Set (ℕ → Bool) := fun j =>
    {v | ∀ i < ⌈Real.exp (((j + L₀ : ℕ) : ℝ) * I)⌉₊ / (j + L₀),
      windowOnes v (i * (j + L₀)) (j + L₀) < γ * ((j + L₀ : ℕ) : ℝ)} with hD
  have hbound : ∀ j : ℕ, (coins ℕ).real (D j) ≤ Real.exp (-1) ^ j := by
    intro j
    set L := j + L₀ with hLdef
    obtain ⟨hL1, hLγ, hLexp⟩ := hL₀ L (by omega)
    have hL0 : 0 < L := by omega
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    set p := (coins (Fin L)).real {w | γ * L ≤ ∑ j, black (w j)} with hp
    set m := ⌈Real.exp ((L : ℝ) * I)⌉₊ / L with hm
    -- the probability of one success
    have hp1 : p ≤ 1 := measureReal_le_one
    have hplow : Real.exp (-(K * L)) / (L + 1) ≤ p := by
      have h := LargeDeviations.log_measureReal_ge hL0 (show γ ≤ 1 by linarith)
      have hpos : 0 < p := LargeDeviations.measureReal_pos L (by linarith)
      have hc : γ ≤ (⌈γ * L⌉₊ : ℝ) / L := by
        rw [le_div_iff₀ (by positivity)]
        exact Nat.le_ceil _
      have hc' : (⌈γ * L⌉₊ : ℝ) / L ≤ γ' := by
        rw [div_le_iff₀ (by positivity)]
        have := Nat.ceil_lt_add_one (show 0 ≤ γ * L by positivity)
        have h2 : 2 ≤ (α - γ) * L := by
          rw [div_le_iff₀ (by linarith)] at hLγ
          linarith
        rw [hγ']
        nlinarith
      have hH : Real.binEntropy γ' ≤ Real.binEntropy ((⌈γ * L⌉₊ : ℝ) / L) :=
        Real.binEntropy_strictAntiOn.antitoneOn
          (show (⌈γ * L⌉₊ : ℝ) / L ∈ Set.Icc 2⁻¹ 1 by constructor <;> linarith)
          (show γ' ∈ Set.Icc 2⁻¹ 1 by constructor <;> linarith) hc'
      have h2 : -(K * L) - Real.log (L + 1) ≤ Real.log p := by
        have : (L : ℝ) * (Real.binEntropy γ' - Real.log 2) ≤
            (L : ℝ) * (Real.binEntropy ((⌈γ * L⌉₊ : ℝ) / L) - Real.log 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        rw [hK]
        linarith
      have h3 := Real.exp_le_exp.2 h2
      rw [Real.exp_log hpos, Real.exp_sub, Real.exp_log (by positivity)] at h3
      exact h3
    -- the number of windows
    have hmlow : Real.exp ((L : ℝ) * I) / L - 1 ≤ m := by
      have h1 : ((⌈Real.exp ((L : ℝ) * I)⌉₊ : ℕ) : ℝ) < ((m : ℝ) + 1) * L := by
        have h := Nat.lt_div_mul_add (a := ⌈Real.exp ((L : ℝ) * I)⌉₊) hL0
        rw [← hm] at h
        have h' : ⌈Real.exp ((L : ℝ) * I)⌉₊ < (m + 1) * L := by
          rw [add_one_mul]
          exact h
        exact_mod_cast h'
      have h2 : Real.exp ((L : ℝ) * I) ≤ ⌈Real.exp ((L : ℝ) * I)⌉₊ := Nat.le_ceil _
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      linarith
    -- `p m ≥ L`
    have hpm : (L : ℝ) ≤ p * m := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have h1 : p * (Real.exp ((L : ℝ) * I) / L - 1) ≤ p * m :=
        mul_le_mul_of_nonneg_left hmlow (by positivity)
      have h2 : Real.exp (-(K * L)) / (L + 1) * (Real.exp ((L : ℝ) * I) / L) ≤
          p * (Real.exp ((L : ℝ) * I) / L) :=
        mul_le_mul_of_nonneg_right hplow (by positivity)
      have h3 : Real.exp (-(K * L)) / (L + 1) * (Real.exp ((L : ℝ) * I) / L) =
          Real.exp (δ * L) / (L * (L + 1)) := by
        rw [hδ, div_mul_div_comm, ← Real.exp_add,
          show -(K * L) + (L : ℝ) * I = (I - K) * L by ring, mul_comm ((L : ℝ) + 1)]
      have h4 : (L : ℝ) + 1 ≤ Real.exp (δ * L) / (L * (L + 1)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
    -- all windows fail with probability `(1 - p)^m ≤ e^(-p m) ≤ e^(-L) ≤ e^(-j)`
    have hfail : (coins (Fin L)).real {w | ∑ j, black (w j) < γ * L} = 1 - p := by
      have hc : {w : Fin L → Bool | ∑ j, black (w j) < γ * L} =
          {w | γ * L ≤ ∑ j, black (w j)}ᶜ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      rw [hc, probReal_compl_eq_one_sub₀ (Set.toFinite _).measurableSet.nullMeasurableSet]
    have hDm : (coins ℕ).real (D j) = (1 - p) ^ m := by
      rw [show D j = {v | ∀ i < m, windowOnes v (i * L) L < γ * L} from rfl,
        measureReal_all_windows_lt hL0, hfail]
    calc (coins ℕ).real (D j) = (1 - p) ^ m := hDm
      _ ≤ Real.exp (-p) ^ m := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) m
      _ = Real.exp (-(p * m)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
      _ ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
      _ ≤ Real.exp (-1) ^ j := by
          rw [← Real.exp_nat_mul]
          refine Real.exp_le_exp.2 ?_
          have : (j : ℝ) ≤ L := by exact_mod_cast (show j ≤ L by omega)
          linarith
  have hsum : ∑' j, coins ℕ (D j) ≠ ⊤ := by
    have hr1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have hsumm : Summable fun j : ℕ => Real.exp (-1) ^ j :=
      summable_geometric_of_lt_one (Real.exp_pos _).le hr1
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' j : ℕ, Real.exp (-1) ^ j)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  filter_upwards [ae_eventually_notMem hsum] with v hv
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hv
  filter_upwards [eventually_ge_atTop (J + L₀)] with L hL
  obtain ⟨j, rfl⟩ : ∃ j, L = j + L₀ := ⟨L - L₀, by omega⟩
  have h := hJ j (by omega)
  simp only [hD, Set.mem_ofPred_eq, not_forall, not_lt, exists_prop] at h
  exact h

/-- **The Erdős–Rényi law for fair coins**: for `1/2 < α < 1`, `I(α) = log 2 - H(α)` and almost
every fair-coin sequence, the largest number of ones in a window of length
`L(n) = ⌊log n / I(α)⌋` starting at `0, …, n - L(n)`, divided by `L(n)`, tends to `α`. -/
theorem ae_tendsto_maxWindow {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) :
    ∀ᵐ v ∂(coins ℕ), Tendsto (fun n : ℕ =>
      maxWindow v n ⌊Real.log n / (Real.log 2 - Real.binEntropy α)⌋₊ /
        ⌊Real.log n / (Real.log 2 - Real.binEntropy α)⌋₊) atTop (𝓝 α) := by
  set I := Real.log 2 - Real.binEntropy α with hI
  have hI0 : 0 < I := by
    have := Real.binEntropy_lt_log_two.2 (show α ≠ 2⁻¹ by intro h; rw [h] at hα; norm_num at hα)
    rw [hI]
    linarith
  set ε₀ := min (α - 1 / 2) (1 - α) / 2 with hε₀
  have hε₀pos : 0 < ε₀ := by
    have : 0 < min (α - 1 / 2) (1 - α) := lt_min (by linarith) (by linarith)
    positivity
  have hε₀a : ε₀ < α - 1 / 2 := by
    have := min_le_left (α - 1 / 2) (1 - α)
    rw [hε₀]
    linarith
  have hε₀b : ε₀ < 1 - α := by
    have := min_le_right (α - 1 / 2) (1 - α)
    rw [hε₀]
    linarith
  have hεk : ∀ k : ℕ, 0 < ε₀ / ((k : ℝ) + 1) ∧ ε₀ / ((k : ℝ) + 1) ≤ ε₀ := fun k =>
    ⟨by positivity, div_le_self hε₀pos.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])⟩
  have hU := ae_all_iff.2 fun k : ℕ => ae_eventually_windows_lt (β := α + ε₀ / ((k : ℝ) + 1)) hα
    (by linarith [(hεk k).1]) (by linarith [(hεk k).2])
  have hD := ae_all_iff.2 fun k : ℕ => ae_eventually_exists_window_ge
    (γ := α - ε₀ / ((k : ℝ) + 1)) hα1 (by linarith [(hεk k).2]) (by linarith [(hεk k).1])
  simp only [← hI] at hU hD
  filter_upwards [hU, hD] with v hU hD
  have hLtop : Tendsto (fun n : ℕ => ⌊Real.log n / I⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hI0)
  -- `N(L(n)) ≤ n < N(L(n) + 1)`
  have hN : ∀ n : ℕ, 0 < n → ⌈Real.exp ((⌊Real.log n / I⌋₊ : ℝ) * I)⌉₊ ≤ n ∧
      n < ⌈Real.exp (((⌊Real.log n / I⌋₊ : ℝ) + 1) * I)⌉₊ := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · refine Nat.ceil_le.2 ?_
      calc Real.exp ((⌊Real.log n / I⌋₊ : ℝ) * I) ≤ Real.exp (Real.log n) :=
            Real.exp_le_exp.2 (by
              have := Nat.floor_le (div_nonneg (Real.log_natCast_nonneg n) hI0.le)
              rwa [le_div_iff₀ hI0] at this)
        _ = n := Real.exp_log hn'
    · refine Nat.lt_ceil.2 ?_
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn').symm
        _ < Real.exp (((⌊Real.log n / I⌋₊ : ℝ) + 1) * I) := Real.exp_lt_exp.2 (by
            have := Nat.lt_floor_add_one (Real.log n / I)
            rwa [div_lt_iff₀ hI0] at this)
  have hpick : ∀ c : ℝ, 0 < c → ∃ k : ℕ, ε₀ / ((k : ℝ) + 1) < c := fun c hc => by
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hc hε₀pos)
    refine ⟨k, ?_⟩
    calc ε₀ / ((k : ℝ) + 1) = ε₀ * (1 / ((k : ℝ) + 1)) := by ring
      _ < ε₀ * (c / ε₀) := mul_lt_mul_of_pos_left hk hε₀pos
      _ = c := by field_simp
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- from below: a dense disjoint window
    obtain ⟨k, hk⟩ := hpick (α - a) (by linarith)
    filter_upwards [hLtop.eventually (hD k), hLtop.eventually (eventually_ge_atTop 1),
      eventually_gt_atTop 0] with n hn hL1 hn0
    have hN1 := (hN n hn0).1
    obtain ⟨L, hL⟩ : ∃ L, ⌊Real.log n / I⌋₊ = L := ⟨_, rfl⟩
    simp only [hL] at hn hL1 hN1 ⊢
    obtain ⟨i, hi, hw⟩ := hn
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have hmem : i * L ∈ Finset.range (n - L + 1) := by
      have h2 := Nat.div_mul_le_self ⌈Real.exp ((L : ℝ) * I)⌉₊ L
      have h3 := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at h3
      rw [Finset.mem_range]
      omega
    have hle : windowOnes v (i * L) L ≤ maxWindow v n L :=
      Finset.le_sup' (fun k => windowOnes v k L) hmem
    rw [lt_div_iff₀ hLpos]
    nlinarith
  · -- from above: no window is too dense
    obtain ⟨k, hk⟩ := hpick (b - α) (by linarith)
    filter_upwards [hLtop.eventually (hU k), hLtop.eventually (eventually_ge_atTop 1),
      eventually_gt_atTop 0] with n hn hL1 hn0
    have hN2 := (hN n hn0).2
    obtain ⟨L, hL⟩ : ∃ L, ⌊Real.log n / I⌋₊ = L := ⟨_, rfl⟩
    simp only [hL] at hn hL1 hN2 ⊢
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have hmax : maxWindow v n L < (α + ε₀ / ((k : ℝ) + 1)) * L := by
      rw [maxWindow, Finset.sup'_lt_iff]
      intro k' hk'
      refine hn k' ?_
      rw [Finset.mem_range] at hk'
      omega
    rw [div_lt_iff₀ hLpos]
    nlinarith

/-- **The Erdős–Rényi law for the center column**: for `1/2 < α < 1` and almost every
configuration, the densest window of length `L(n) = ⌊log n / (log 2 - H(α))⌋` among the first `n`
cells of the center column is a fraction `α + o(1)` black. -/
theorem ae_tendsto_maxWindow_trace {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) :
    ∀ᵐ x ∂(coins ℤ), Tendsto (fun n : ℕ =>
      maxWindow (trace x) n ⌊Real.log n / (Real.log 2 - Real.binEntropy α)⌋₊ /
        ⌊Real.log n / (Real.log 2 - Real.binEntropy α)⌋₊) atTop (𝓝 α) :=
  measurePreserving_trace.quasiMeasurePreserving.ae (ae_tendsto_maxWindow hα hα1)

end Rule30Equivalents.ErdosRenyi
