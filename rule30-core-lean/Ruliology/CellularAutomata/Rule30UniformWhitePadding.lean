module

public import Ruliology.CellularAutomata.Rule30Certificates.WhitePaddingFamilies
public import Ruliology.CellularAutomata.Rule30FiniteStrips

@[expose] public section

/-!
The five pumping certificate families hold in every column of every
nonzero left-finite Rule 30 configuration. The certificate payloads are
combined with the uniform masked-Jen strip soundness theorem.
-/
namespace Ruliology.CellularAutomata.Rule30UniformWhitePadding
open Rule30StripCertificates Rule30WhitePadding Rule30Certificates.WhitePaddingFamilies.Data

theorem certificateA (r : Nat) (hr : 13 ≤ r) :
    stripCert (List.replicate r false ++ tailA) 6 2 = true := by
  apply padding_strip tailA 6 13 S1A S2A
  · rw [reachedFullA]; exact firstTailA
  · rw [reachedS1A]; exact secondTailA
  · exact stableFullA
  · exact stableS1A
  · exact stableS2A
  · rw [reachedS2A]; exact returnCheckA
  · exact prefixCheckA
  · rw [reachedS2A]; exact tailCheckA
  · exact hr

/-- Family A excludes its repeating words in any column with a leftmost black cell. -/
theorem no_paddingA_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (r : Nat) (hr : 13 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailA) := by
  exact Rule30FiniteStrips.not_eventually_word_strip hlo hzero i _ 6 2
    (by decide) (by simp; omega) (certificateA r hr)

theorem certificateB (r : Nat) (hr : 14 ≤ r) :
    stripCert (List.replicate r false ++ tailB) 7 2 = true := by
  apply padding_strip tailB 7 14 S1B S2B
  · rw [reachedFullB]; exact firstTailB
  · rw [reachedS1B]; exact secondTailB
  · exact stableFullB
  · exact stableS1B
  · exact stableS2B
  · rw [reachedS2B]; exact returnCheckB
  · exact prefixCheckB
  · rw [reachedS2B]; exact tailCheckB
  · exact hr

/-- Family B excludes its repeating words in any column with a leftmost black cell. -/
theorem no_paddingB_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (r : Nat) (hr : 14 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailB) := by
  exact Rule30FiniteStrips.not_eventually_word_strip hlo hzero i _ 7 2
    (by decide) (by simp; omega) (certificateB r hr)

theorem certificateC (r : Nat) (hr : 23 ≤ r) :
    stripCert (List.replicate r false ++ tailC) 9 2 = true := by
  apply padding_strip tailC 9 23 S1C S2C
  · rw [reachedFullC]; exact firstTailC
  · rw [reachedS1C]; exact secondTailC
  · exact stableFullC
  · exact stableS1C
  · exact stableS2C
  · rw [reachedS2C]; exact returnCheckC
  · exact prefixCheckC
  · rw [reachedS2C]; exact tailCheckC
  · exact hr

/-- Family C excludes its repeating words in any column with a leftmost black cell. -/
theorem no_paddingC_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (r : Nat) (hr : 23 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailC) := by
  exact Rule30FiniteStrips.not_eventually_word_strip hlo hzero i _ 9 2
    (by decide) (by simp; omega) (certificateC r hr)

theorem certificateD (r : Nat) (hr : 23 ≤ r) :
    stripCert (List.replicate r false ++ tailD) 9 2 = true := by
  apply padding_strip tailD 9 23 S1D S2D
  · rw [reachedFullD]; exact firstTailD
  · rw [reachedS1D]; exact secondTailD
  · exact stableFullD
  · exact stableS1D
  · exact stableS2D
  · rw [reachedS2D]; exact returnCheckD
  · exact prefixCheckD
  · rw [reachedS2D]; exact tailCheckD
  · exact hr

/-- Family D excludes its repeating words in any column with a leftmost black cell. -/
theorem no_paddingD_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (r : Nat) (hr : 23 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailD) := by
  exact Rule30FiniteStrips.not_eventually_word_strip hlo hzero i _ 9 2
    (by decide) (by simp; omega) (certificateD r hr)

theorem certificateE (r : Nat) (hr : 31 ≤ r) :
    stripCert (List.replicate r false ++ tailE) 10 2 = true := by
  apply padding_strip tailE 10 31 S1E S2E
  · rw [reachedFullE]; exact firstTailE
  · rw [reachedS1E]; exact secondTailE
  · exact stableFullE
  · exact stableS1E
  · exact stableS2E
  · rw [reachedS2E]; exact returnCheckE
  · exact prefixCheckE
  · rw [reachedS2E]; exact tailCheckE
  · exact hr

/-- Family E excludes its repeating words in any column with a leftmost black cell. -/
theorem no_paddingE_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (r : Nat) (hr : 31 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tailE) := by
  exact Rule30FiniteStrips.not_eventually_word_strip hlo hzero i _ 10 2
    (by decide) (by simp; omega) (certificateE r hr)

end Ruliology.CellularAutomata.Rule30UniformWhitePadding
