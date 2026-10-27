import Ruliology.CellularAutomata.Rule30Prize

/-!
# Challenge statements for Lean's comparator

The official targets with `sorry` in place of proofs. A maintainer gives this module and the
submission module `Rule30Submission` to [comparator](https://github.com/leanprover/comparator), with
one of the configs in this folder. Comparator rebuilds the submission in a sandbox, exports it,
replays it through the kernel and checks that each named theorem has the challenge's statement.

Never import this module from a submission: its theorems are unproved.
-/

namespace Rule30Submission

open Ruliology.CellularAutomata.Rule30Prize

theorem problem1 : Problem1 := sorry
theorem not_problem1 : ¬ Problem1 := sorry
theorem problem2 : Problem2 := sorry
theorem not_problem2 : ¬ Problem2 := sorry

end Rule30Submission
