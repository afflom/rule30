module

public import Rule30Equivalents.LinearRelations
public import Mathlib.RingTheory.LaurentSeries
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
# Transcendence of the generating function: sufficient conditions

Let `C(X) = ∑ c(t) Xᵗ`, read over a field `K` as a Laurent series. If the center column were
eventually periodic, `C(X)` would be a rational function, hence algebraic over `K(X)`.

* `isAlgebraic_of_eventuallyPeriodic`: for every field `K`, an eventually periodic `b` has a
  generating function that is algebraic (indeed of degree `1`) over `K(X)`.
* `problem1_of_transcendental`: if `C(X)` is transcendental over `ℚ(X)`, or over
  `K(X)` for any field `K`, Problem 1 holds. The converse over `ℚ` is Fatou's theorem (1906); the
  library proves it instead through "algebraic ⟹ D-finite" and `DFinite`, in `AlgebraicDFinite`.
* `problem1_of_transcendental_F2_or_F3`: the same if `C(X)` is transcendental over
  `F₂(X)` or over `F₃(X)`. By Christol's theorem the converse needs Cobham's theorem.

Over `F_p`, algebraic means p-automatic (Christol), so transcendence over `F_p(X)` is strictly
stronger than Problem 1; over `ℚ` it is equivalent (Fatou).

Sources: P. Fatou, *Séries trigonométriques et séries de Taylor*, Acta Math. 30 (1906) 335–400;
G. Christol, *Ensembles presque périodiques k-reconnaissables*, Theoret. Comput. Sci. 9 (1979)
141–145.
-/

@[expose] public section

namespace Rule30Equivalents.Transcendence

open Ruliology.CellularAutomata Polynomial
open scoped LaurentSeries RatFunc

/-- **An eventually periodic sequence has an algebraic generating function**, over every field. -/
theorem isAlgebraic_of_eventuallyPeriodic {K : Type*} [Field K] {b : ℕ → Bool}
    (h : EventuallyPeriodic b) :
    IsAlgebraic (RatFunc K) ((LinearRelations.series K b : PowerSeries K) : K⸨X⸩) := by
  obtain ⟨P, Q, hQ, hPQ⟩ := (LinearRelations.eventuallyPeriodic_iff_rational (K := K) b).1 h
  refine ⟨C (Q : RatFunc K) * X - C (P : RatFunc K), fun h0 => ?_, ?_⟩
  · have h1 := congrArg (fun p : (RatFunc K)[X] => p.coeff 1) h0
    simp only [coeff_sub, coeff_C_mul_X, coeff_C, coeff_zero, ite_eq_right one_ne_zero,
        sub_zero] at h1
    exact hQ ((RatFunc.algebraMap_injective K).eq_iff.1 (by simpa using h1))
  · simp only [map_sub, map_mul, aeval_C, aeval_X]
    rw [show algebraMap (RatFunc K) K⸨X⸩ (Q : RatFunc K) = ((Q : PowerSeries K) : K⸨X⸩) from
        (RatFunc.coe_coe Q).symm,
      show algebraMap (RatFunc K) K⸨X⸩ (P : RatFunc K) = ((P : PowerSeries K) : K⸨X⸩) from
        (RatFunc.coe_coe P).symm,
      ← map_mul, hPQ, sub_self]

/-- **A sufficient condition**: if the generating function of the center column is
transcendental over `K(X)` for some field `K`, for example `ℚ`, Problem 1 holds. -/
theorem problem1_of_transcendental {K : Type*} [Field K]
    (h : Transcendental (RatFunc K) ((LinearRelations.series K c : PowerSeries K) : K⸨X⸩)) :
    Rule30Prize.Problem1 :=
  fun hep => h (isAlgebraic_of_eventuallyPeriodic hep)

/-- **A sufficient condition**: if the generating function of the center column is
transcendental over `F₂(X)` or over `F₃(X)`, Problem 1 holds. -/
theorem problem1_of_transcendental_F2_or_F3
    (h : Transcendental (RatFunc (ZMod 2))
        ((LinearRelations.series (ZMod 2) c : PowerSeries (ZMod 2)) : (ZMod 2)⸨X⸩) ∨
      Transcendental (RatFunc (ZMod 3))
        ((LinearRelations.series (ZMod 3) c : PowerSeries (ZMod 3)) : (ZMod 3)⸨X⸩)) :
    Rule30Prize.Problem1 := by
  rcases h with h | h
  · exact problem1_of_transcendental h
  · exact problem1_of_transcendental h

end Rule30Equivalents.Transcendence
