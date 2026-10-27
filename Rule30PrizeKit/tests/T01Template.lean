import Rule30PrizeKit
-- Passes: a known partial result with standard axioms.
namespace Rule30Submission
open Ruliology.CellularAutomata.Rule30Prize
theorem no_period_one : ¬ ∃ N, ∀ t, N ≤ t → center (t + 1) = center t :=
  center_not_eventually_period_one
/-- The first eight cells of the center column, by kernel evaluation (`decide`). -/
theorem first_bits : (List.range 8).map center = [true, true, false, true, true, true, false, false] := by
  decide
end Rule30Submission
