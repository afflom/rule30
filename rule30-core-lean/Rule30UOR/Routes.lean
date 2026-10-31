module
public import Rule30UOR.Interfaces
public import Rule30UOR.WittDefect
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Proposed routes, decided

Conceptual proposals for the endgame are decided here by the kernel against
the theorems they cite. Route B claimed that between the doubling diagonal
`z + 1` at time `t` and the reset diagonal `z + 3` at time `t + 1`, which
share the arrival time `2t - z - 2`, the sum `diagonalPhase + diagonalFlux`
changes by `±1`, contradicting the common import balance. It does not: the
phase negates (`diagonal_reset_phase`) and the flux jumps by twice the
phase (`diagonal_reset_flux_jump`), so the sum is invariant. -/

@[expose] public section

namespace Rule30UOR.Routes

open Rule30UOR.WittDefect

/-- The phase-plus-flux sum is the same on the doubling diagonal at `t` and on
the reset diagonal at `t + 1`: Route B's mismatch is `−φ + 2φ = φ`, not `±1`. -/
theorem diagonal_reset_sum_invariant (Q z t : Nat)
    (hz : Rule30UOR.ZeroDiagonals.IsZeroDiag z)
    (hs : Rule30UOR.Interfaces.SettledBy (z + 2) t) (ht : z + 3 ≤ t) :
    diagonalPhase Q (z + 3) (t + 1) + diagonalFlux Q (z + 3) (t + 1) 1 =
      diagonalPhase Q (z + 1) t + diagonalFlux Q (z + 1) t 1 := by
  rw [diagonal_reset_phase Q z t hz hs, diagonal_reset_flux_jump Q z t hz hs ht]
  cfomega

end Rule30UOR.Routes
