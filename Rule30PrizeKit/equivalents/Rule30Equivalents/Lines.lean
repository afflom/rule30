module

public import Rule30Equivalents.Mixing
public import Rule30Equivalents.IteratedLogarithm
public import Rule30Equivalents.ErdosRenyi
public import Rule30Equivalents.ReturnTimes
public import Rule30Equivalents.RandomNaturalBoundary
public import Rule30Equivalents.MaxOrderComplexity
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
# Laws along every line of the spacetime diagram

For a random configuration the cells along a line `k ↦ (q k + t₀, p k + x₀)` of rational velocity
`p/q ≠ 1` are independent fair coins (`Mixing.measurePreserving_line`), so every almost-sure law
of fair-coin sequences holds along all of these countably many lines at once
(`Mixing.ae_lines_of_ae`). For almost every configuration, along every such line:

* `ae_lil_lines`: the walk `W(n)`, black minus white among the first `n` cells, has
  `limsup W(n)/√(2 n log log n) = 1` and `liminf W(n)/√(2 n log log n) = -1`, and the limit points
  of `W(n)/√(2 n log log n)` form exactly `[-1, 1]` (`IteratedLogarithm`);
* `ae_longestRun_lines`: the longest run of either color among the first `n` cells has length
  `log₂ n + o(log n)` (`LongestRuns`);
* `ae_returnTime_lines`: the first `n` cells recur after `2^(n + o(n))` steps (`ReturnTimes`);
* `ae_linComplexity_lines`: the linear complexity of the first `n` cells is `n/2 + o(n)`
  (`LinearComplexity`);
* `ae_maxWindow_lines`: for each `1/2 < α < 1`, the Erdős–Rényi law (`ErdosRenyi`);
* `ae_circleIsNaturalBoundary_lines`: the generating function of the cells has the unit circle as
  a natural boundary (`RandomNaturalBoundary`);
* `ae_tendsto_maxOrderComplexity_lines`: the maximum-order complexity of the first `n` cells is
  `2 log₂ n + o(log n)` (`MaxOrderComplexity`).

The center column is the line `p = 0`, `q = 1`. Lines of velocity `1` are not fair coins
(`Mixing.measure_diag_eq`).
-/

@[expose] public section

namespace Rule30Equivalents.Lines

open MeasureTheory Filter Topology Ruliology.CellularAutomata Rule30Realization Genericity
  RandomConfigurations

/-- **The law of the iterated logarithm along every line.** -/
theorem ae_lil_lines :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q →
      limsup (fun n : ℕ => (Fluctuations.walk (fun k => evol x (q * k + t₀) (p * k + x₀)) n : ℝ) /
        √(2 * n * Real.log (Real.log n))) atTop = 1 ∧
      liminf (fun n : ℕ => (Fluctuations.walk (fun k => evol x (q * k + t₀) (p * k + x₀)) n : ℝ) /
        √(2 * n * Real.log (Real.log n))) atTop = -1 ∧
      {y | MapClusterPt y atTop fun n : ℕ =>
        (Fluctuations.walk (fun k => evol x (q * k + t₀) (p * k + x₀)) n : ℝ) /
          √(2 * n * Real.log (Real.log n))} = Set.Icc (-1) 1 :=
  (Mixing.ae_lines_of_ae (IteratedLogarithm.ae_limsup_liminf_walk.and
    IteratedLogarithm.ae_clusterPt_walk)).mono fun _ h p q t₀ x₀ hpq =>
      ⟨(h p q t₀ x₀ hpq).1.1, (h p q t₀ x₀ hpq).1.2, (h p q t₀ x₀ hpq).2⟩

/-- **The longest runs along every line** have length `log₂ n + o(log n)`, in both colors. -/
theorem ae_longestRun_lines :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q → ∀ β : Bool,
      Tendsto (fun n : ℕ => (LongestRuns.longestRun (fun k => evol x (q * k + t₀) (p * k + x₀))
        β n : ℝ) / Nat.log 2 n) atTop (𝓝 1) :=
  Mixing.ae_lines_of_ae (ae_all_iff.2 LongestRuns.ae_tendsto_longestRun)

/-- **Return times along every line**: the first `n` cells recur after `2^(n + o(n))` steps. -/
theorem ae_returnTime_lines :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q →
      Tendsto (fun n : ℕ => Real.logb 2 (ReturnTimes.returnTime
        (fun k => evol x (q * k + t₀) (p * k + x₀)) n) / n) atTop (𝓝 1) :=
  Mixing.ae_lines_of_ae ReturnTimes.ae_tendsto_logb_returnTime

/-- **Linear complexity along every line**: `Lₙ/n → 1/2`. -/
theorem ae_linComplexity_lines :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q →
      Tendsto (fun n : ℕ => (StrongerStatements.linComplexity
        (fun k => evol x (q * k + t₀) (p * k + x₀)) n : ℝ) / n) atTop (𝓝 (1 / 2)) :=
  Mixing.ae_lines_of_ae LinearComplexity.ae_tendsto_linComplexity

/-- **The Erdős–Rényi law along every line**, for each `1/2 < α < 1`. -/
theorem ae_maxWindow_lines {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q →
      Tendsto (fun n : ℕ => ErdosRenyi.maxWindow (fun k => evol x (q * k + t₀) (p * k + x₀)) n
          ⌊Real.log n / (Real.log 2 - Real.binEntropy α)⌋₊ /
        ⌊Real.log n / (Real.log 2 - Real.binEntropy α)⌋₊) atTop (𝓝 α) :=
  Mixing.ae_lines_of_ae (ErdosRenyi.ae_tendsto_maxWindow hα hα1)

/-- **A natural boundary along every line**: the generating function of the cells along the line
has the unit circle as a natural boundary. -/
theorem ae_circleIsNaturalBoundary_lines :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q →
      RandomNaturalBoundary.CircleIsNaturalBoundary fun k => evol x (q * k + t₀) (p * k + x₀) :=
  Mixing.ae_lines_of_ae RandomNaturalBoundary.ae_circleIsNaturalBoundary

/-- **The maximum-order complexity along every line**: `M_n/log₂ n → 2`. -/
theorem ae_tendsto_maxOrderComplexity_lines :
    ∀ᵐ x ∂(coins ℤ), ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), p ≠ q →
      Tendsto (fun n : ℕ => (WordsAutomata.maxOrderComplexity
        (fun k => evol x (q * k + t₀) (p * k + x₀)) n : ℝ) / Nat.log 2 n) atTop (𝓝 2) :=
  Mixing.ae_lines_of_ae MaxOrderComplexity.ae_tendsto_maxOrderComplexity

end Rule30Equivalents.Lines
