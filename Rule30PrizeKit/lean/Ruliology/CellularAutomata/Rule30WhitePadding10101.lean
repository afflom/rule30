module

public import Ruliology.CellularAutomata.Rule30RestrictedBackwardTube
public import Ruliology.CellularAutomata.Rule30Certificates.FiveTailTube

/-!
Exclude sufficiently white-padded repetition of the five-bit tail
10101. The finite endpoint-conditioned tube certifies the backward
implications, then the analytic white-pulse bound handles all padding lengths.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WhitePadding10101
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30RestrictedBackwardTube

/-- The first five-bit exceptional tail, proved with an endpoint-conditioned tube. -/
theorem no_padding_10101_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ [true,false,true,false,true]) := by
  apply no_padding_of_endpoint_tube hlo hzero i Rule30Certificates.FiveTailTube.Tube10101.tail
    16 24 Rule30Certificates.FiveTailTube.Tube10101.Z Rule30Certificates.FiveTailTube.Tube10101.Q
    Rule30Certificates.FiveTailTube.Tube10101.P Rule30Certificates.FiveTailTube.Tube10101.S
    (fun d => decide (d ≤ 8)) (fun _ => false) (by decide)
    Rule30Certificates.FiveTailTube.Tube10101.Zzero Rule30Certificates.FiveTailTube.Tube10101.Zfixed
    Rule30Certificates.FiveTailTube.Tube10101.Szero Rule30Certificates.FiveTailTube.Tube10101.Pend
    Rule30Certificates.FiveTailTube.Tube10101.Qstart Rule30Certificates.FiveTailTube.Tube10101.Qend
  · intro d hd
    exact Rule30Certificates.FiveTailTube.Tube10101.Qstep d hd
  · intro j hj
    exact Rule30Certificates.FiveTailTube.Tube10101.Pstep j hj
  · intro j hj
    exact Rule30Certificates.FiveTailTube.Tube10101.Sstep j hj
  · exact Rule30Certificates.FiveTailTube.Tube10101.Qforce
  · exact Rule30Certificates.FiveTailTube.Tube10101.Pforce
  · simpa only [Rule30Certificates.FiveTailTube.Tube10101.tail, List.length_cons, List.length_nil] using
      (show 10*5+11 ≤ r by omega)
  · simpa only [Rule30Certificates.FiveTailTube.Tube10101.tail, List.length_cons, List.length_nil] using
      (show 16-1+9*(5+1) ≤ r by omega)
  · omega

theorem no_padding_10101 (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ [true,false,true,false,true]) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_10101_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 r hr
  simpa only [Rule30FiniteStrips.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h

theorem no_padding_10101_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ [true,false,true,false,true]) := by
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_10101_leftFinite hlo hzero i r hr

end Ruliology.CellularAutomata.Rule30WhitePadding10101
