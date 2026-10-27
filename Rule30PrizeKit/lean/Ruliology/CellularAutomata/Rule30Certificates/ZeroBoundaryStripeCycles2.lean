module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-!
# The stripe-prefix family: front-window cycles (the cycle `cyc_5_0`, length `65536`)

Data for `Rule30ZeroBoundaryStripeFamily`: kernel-checked front-window cycles (window `32`,
post-arrival horizon `31`), as `Rule30ZeroBoundaryStripeFront.Cycle` certificates whose
segments are checked by `seg` with `decide +kernel` and joined by `seg_sound` and `path_append`:
`cyc_5_0` (length `65536`), in four `seg` checks of `16384` steps.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles2

open Rule30ZeroBoundaryStripeFront

theorem seg_5_0_0 : seg 32 31 1 1073741829 0 16384 0 5 0 = true := by decide +kernel
theorem seg_5_0_1 : seg 32 31 1 2147483653 0 16384 16384 1073741829 0 = true := by decide +kernel
theorem seg_5_0_2 : seg 32 31 1 3221225477 0 16384 32768 2147483653 0 = true := by decide +kernel
theorem seg_5_0_3 : seg 32 31 1 5 0 16384 49152 3221225477 0 = true := by decide +kernel

theorem cyc_5_0 : Cycle 32 31 5 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 1073741829 0 16384 0 5 0 seg_5_0_0) (seg_sound 32 31 1 2147483653 0 16384 16384 1073741829 0 seg_5_0_1)) (seg_sound 32 31 1 3221225477 0 16384 32768 2147483653 0 seg_5_0_2)) (seg_sound 32 31 1 5 0 16384 49152 3221225477 0 seg_5_0_3))⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles2
