import Rule30PrizeKit
-- Fails: `native_decide` trusts the compiler.
namespace Rule30Submission
open Ruliology.CellularAutomata.Rule30Prize
theorem first_bits : (List.range 8).map center = [true, true, false, true, true, true, false, false] := by
  native_decide
end Rule30Submission
