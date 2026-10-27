module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-!
# The stripe-prefix family: front-window cycles (the cycle `cyc_4_1`, length `65536`)

Data for `Rule30ZeroBoundaryStripeFamily`: kernel-checked front-window cycles (window `32`,
post-arrival horizon `31`), as `Rule30ZeroBoundaryStripeFront.Cycle` certificates whose
segments are checked by `seg` with `decide +kernel` and joined by `seg_sound` and `path_append`:
`cyc_4_1` (length `65536`), in four `seg` checks of `16384` steps.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles1

open Rule30ZeroBoundaryStripeFront

theorem seg_4_1_0 : seg 32 31 0 536870916 1 16384 0 4 1 = true := by decide +kernel
theorem seg_4_1_1 : seg 32 31 0 1073741828 1 16384 16384 536870916 1 = true := by decide +kernel
theorem seg_4_1_2 : seg 32 31 0 1610612740 1 16384 32768 1073741828 1 = true := by decide +kernel
theorem seg_4_1_3 : seg 32 31 0 4 1 16384 49152 1610612740 1 = true := by decide +kernel

theorem cyc_4_1 : Cycle 32 31 4 1 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 0 536870916 1 16384 0 4 1 seg_4_1_0) (seg_sound 32 31 0 1073741828 1 16384 16384 536870916 1 seg_4_1_1)) (seg_sound 32 31 0 1610612740 1 16384 32768 1073741828 1 seg_4_1_2)) (seg_sound 32 31 0 4 1 16384 49152 1610612740 1 seg_4_1_3))⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles1
