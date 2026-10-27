import Rule30PrizeKit

/-!
# Rule 30 Prize submission (template)

Replace the body of this file with your proof, and keep these rules:

* This one file holds the whole proof. It may import the kit (`Rule30PrizeKit`), the catalog
  (`Ruliology.*`), `Rule30Equivalents.*`, Mathlib, Batteries and Lean.
* The headline theorem lives in `namespace Rule30Submission` and has an official name and type:

  | claim                          | theorem        | type           |
  |--------------------------------|----------------|----------------|
  | Problem 1 holds                | `problem1`     | `Problem1`     |
  | Problem 1 fails                | `not_problem1` | `¬ Problem1`   |
  | Problem 2 holds                | `problem2`     | `Problem2`     |
  | Problem 2 fails                | `not_problem2` | `¬ Problem2`   |
  | a partial result               | any name       | any statement  |

  Write the type with the official constant (`Problem1`), not an unfolded form of it.
* No `sorry`, no `native_decide`, `decide +native` or `bv_decide`, and no `axiom`.

Check it the way the verifier does:

```
lake build Rule30Submission
lake env lean --run Check.lean Rule30Submission --claim partial --headline Rule30Submission.no_period_one
```

As it stands, the template proves a known partial result, the period-1 case of Problem 1.
-/

namespace Rule30Submission

open Ruliology.CellularAutomata.Rule30Prize

/-- The center column is not eventually constant: Problem 1 for period 1, a consequence of Jen's
theorem that no two columns are both eventually periodic. -/
theorem no_period_one : ¬ ∃ N, ∀ t, N ≤ t → center (t + 1) = center t :=
  center_not_eventually_period_one

-- The prize: replace `sorry` with a proof, and delete this comment.
-- theorem problem1 : Problem1 := by
--   sorry

end Rule30Submission
