-- Fails: the module does not import the kit. It declares a `Problem1` of its own, with the official
-- name and the statement `True`, and proves that. Its type is the official constant's name, so only
-- the check that `Problem1` comes from the kit's statement module rejects it.
namespace Ruliology.CellularAutomata.Rule30Prize

def Problem1 : Prop := True

end Ruliology.CellularAutomata.Rule30Prize

namespace Rule30Submission

theorem problem1 : Ruliology.CellularAutomata.Rule30Prize.Problem1 := trivial

end Rule30Submission
