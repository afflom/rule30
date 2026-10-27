module

public import Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterion

@[expose] public section

/-! Small concrete applications of the arbitrary-tail vacuum criterion.
The two five-bit tails require only a width-five strip (32 states).
The bound 61 comes from the analytic pulse estimate, not from a search over r. -/
namespace Ruliology.CellularAutomata.Rule30VacuumExample
open Rule30Jen Rule30StripCertificates Rule30WhitePadding
open Rule30WhitePaddingVacuumCriterion

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def G : Nat := 2875964011
def tailA : List Bool := [true,true,false,true,true]
def tailB : List Bool := [true,false,false,true,true]

theorem reached : zeros 5 2 (fullSet 5) = G := by decide +kernel
theorem stable : image 5 false G = G := by decide +kernel
theorem safeA : (applyWord 5 tailA G).testBit 0 = false := by decide +kernel
theorem safeB : (applyWord 5 tailB G).testBit 0 = false := by decide +kernel

/-- No column of a configuration with a leftmost black cell eventually repeats `0^r 11011`,
for any r at least 61. -/
theorem no_paddingA {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 61 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailA) := by
  exact no_padding_of_vacuum_avoidance hlo hzero i tailA 5 2 G reached stable safeA r
    (by omega) (by simp [tailA]; omega) (by simp [tailA]; omega)

/-- No column of a configuration with a leftmost black cell eventually repeats `0^r 10011`,
for any r at least 61. -/
theorem no_paddingB {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 61 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailB) := by
  exact no_padding_of_vacuum_avoidance hlo hzero i tailB 5 2 G reached stable safeB r
    (by omega) (by simp [tailB]; omega) (by simp [tailB]; omega)

theorem no_paddingA_seed (r : Nat) (hr : 61 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ tailA) := by
  exact no_padding_seed_of_vacuum_avoidance tailA 5 2 G reached stable safeA r
    (by omega) (by simp [tailA]; omega) (by simp [tailA]; omega)

theorem no_paddingB_seed (r : Nat) (hr : 61 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ tailB) := by
  exact no_padding_seed_of_vacuum_avoidance tailB 5 2 G reached stable safeB r
    (by omega) (by simp [tailB]; omega) (by simp [tailB]; omega)

end Ruliology.CellularAutomata.Rule30VacuumExample
