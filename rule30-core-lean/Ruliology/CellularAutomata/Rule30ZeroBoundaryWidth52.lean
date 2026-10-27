module

public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks0
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks1
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks2
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks3

/-!
# `Q01` for every start of width at most `52` (kernel-checked)

Every start of the zero-boundary left half supported at depths `1, …, 52` has a white cell at
depth `1` (column `-1`) at some even time `≤ 96`. The 256 chunk checks are in the namespaces
`Rule30ZeroBoundaryWidth52.C0` – `C15`, in the modules
`Rule30Certificates.ZeroBoundaryWidth52Chunks0` – `ZeroBoundaryWidth52Chunks3` (64 chunks each);
soundness is `Rule30ZeroBoundaryLanes.q01_of_chunks`.

* `q01_width_le_52`: the bound `96`, which is `D(52)` of the death-time table (its
  tightness is observed, not proved).
* `q01_width_le_52_linear`: the bound `2 W + 8`.
* `not_inX_of_width_le_52`: `Q01` restricted to widths `≤ 52` (`¬ Rule30ZeroBoundary.InX x`).

`W ≤ 56` was also kernel-checked (`KC.Q01W56.q01_width_le_56`, bound `100`; `1024` chunks in `64`
files, about `345` s of kernel time). It is not part of this kit because of
its build cost.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryWidth52

open Rule30ZeroBoundaryLanes Rule30ZeroBoundary

theorem all_chunks : ChunksOK 52 97 18 0 256 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C0.range C1.range) (chunksOK_append C2.range C3.range)) (chunksOK_append (chunksOK_append C4.range C5.range) (chunksOK_append C6.range C7.range))) (chunksOK_append (chunksOK_append (chunksOK_append C8.range C9.range) (chunksOK_append C10.range C11.range)) (chunksOK_append (chunksOK_append C12.range C13.range) (chunksOK_append C14.range C15.range))))

/-- **`Q01` for widths `≤ 52`**: every start supported at depths `≤ 52` has a white cell at
depth `1` at some even time `≤ 96`. -/
theorem q01_width_le_52 (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) :
    ∃ t, t ≤ 96 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_of_chunks 52 97 18 (by decide) all_chunks x hx
  exact ⟨t, by omega, he, hz⟩

/-- The same with the bound `2 W + 8`. -/
theorem q01_width_le_52_linear (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) :
    ∃ t, t ≤ 2 * 52 + 8 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_width_le_52 x hx
  exact ⟨t, by omega, he, hz⟩

/-- **`Q01` restricted to widths `≤ 52`**: no start supported at depths `≤ 52` is constrained. -/
theorem not_inX_of_width_le_52 (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) : ¬ InX x := by
  intro hX
  obtain ⟨t, _, he, hz⟩ := q01_width_le_52 x hx
  have := hX (t / 2)
  rw [show 2 * (t / 2) = t by omega, hz] at this
  exact absurd this (by decide)

end Rule30ZeroBoundaryWidth52
end Ruliology.CellularAutomata
