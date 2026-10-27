module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-!
# The stripe-prefix family: front-window cycles (six cycles of length `4096` or `16384`)

Data for `Rule30ZeroBoundaryStripeFamily`: kernel-checked front-window cycles (window `32`,
post-arrival horizon `31`), as `Rule30ZeroBoundaryStripeFront.Cycle` certificates whose
segments are checked by `seg` with `decide +kernel` and joined by `seg_sound` and `path_append`:
`cyc_0_1`, `cyc_1_0`, `cyc_6_1` (length `4096`) and `cyc_2_1`, `cyc_3_0`, `cyc_7_0` (length
`16384`), one `seg` check each.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles0

open Rule30ZeroBoundaryStripeFront

theorem seg_0_1_0 : seg 32 31 0 0 1 4096 0 0 1 = true := by decide +kernel

theorem cyc_0_1 : Cycle 32 31 0 1 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 0 1 4096 0 0 1 seg_0_1_0)⟩

theorem seg_1_0_0 : seg 32 31 1 1 0 4096 0 1 0 = true := by decide +kernel

theorem cyc_1_0 : Cycle 32 31 1 0 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 1 0 4096 0 1 0 seg_1_0_0)⟩

theorem seg_2_1_0 : seg 32 31 0 2 1 16384 0 2 1 = true := by decide +kernel

theorem cyc_2_1 : Cycle 32 31 2 1 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 2 1 16384 0 2 1 seg_2_1_0)⟩

theorem seg_3_0_0 : seg 32 31 1 3 0 16384 0 3 0 = true := by decide +kernel

theorem cyc_3_0 : Cycle 32 31 3 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 3 0 16384 0 3 0 seg_3_0_0)⟩

theorem seg_6_1_0 : seg 32 31 0 6 1 4096 0 6 1 = true := by decide +kernel

theorem cyc_6_1 : Cycle 32 31 6 1 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 6 1 4096 0 6 1 seg_6_1_0)⟩

theorem seg_7_0_0 : seg 32 31 1 7 0 16384 0 7 0 = true := by decide +kernel

theorem cyc_7_0 : Cycle 32 31 7 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 7 0 16384 0 7 0 seg_7_0_0)⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles0
