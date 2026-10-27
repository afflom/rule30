module

public import Ruliology.CellularAutomata.Rule30FiveTailReduction
public import Ruliology.CellularAutomata.Rule30Certificates.FiveTailTube
public import Ruliology.CellularAutomata.Rule30VacuumExample
public import Ruliology.CellularAutomata.Rule30WhitePadding10101

@[expose] public section

/-!
Exclude sufficiently white-padded repetition of every Boolean tail of
length at most five, in every column of every nonzero left-finite start.
The reduction to black-ended cores combines the shorter-tail theorem,
finite vacuum-avoidance certificates, and the endpoint-conditioned tube.
-/
namespace Ruliology.CellularAutomata.Rule30FiveTail
open Rule30Jen Rule30Realization Rule30FiveTailReduction

theorem no_five_core {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (hv : v ∈ fiveCores) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v) := by
  simp only [fiveCores,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding10001 hlo hzero i r (by omega)
  · simpa only [Rule30VacuumExample.tailB] using
      Rule30VacuumExample.no_paddingB hlo hzero i r (by omega)
  · exact Rule30WhitePadding10101.no_padding_10101_leftFinite hlo hzero i r hr
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding10111 hlo hzero i r (by omega)
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding11001 hlo hzero i r (by omega)
  · simpa only [Rule30VacuumExample.tailA] using
      Rule30VacuumExample.no_paddingA hlo hzero i r (by omega)
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding11101 hlo hzero i r (by omega)
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding11111 hlo hzero i r (by omega)

/-- No column of any configuration with a leftmost black cell eventually repeats
`0^r u` when r≥69 and u has at most five bits. -/
theorem no_five_tail_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) :=
  no_five_tail_of_cores hlo hzero i (no_five_core hlo hzero i) u hu r hr

theorem no_five_tail_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_five_tail_leftFinite hlo hzero i u hu r hr

theorem no_five_tail_seed (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed,show p ≠ 0 by omega]
  have h := no_five_tail_leftFinite (x:=seed) (lo:=0) (by decide) hzero 0 u hu r hr
  simpa only [Rule30FiniteStrips.EventuallyWord,Rule30StripCertificates.EventuallyWord,
    evol_seed] using h

end Ruliology.CellularAutomata.Rule30FiveTail
