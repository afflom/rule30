module
public import Rule30UOR.Antidiagonal
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Every left diagonal is eventually periodic

The left step `ldiag (k+2) (s+1) = ldiag k s ⊕ (ldiag (k+1) s ∨ ldiag (k+2) s)` is a one-bit
system driven by the two lower diagonals. If the drivers are `p`-periodic from time `T`, the
state map over one period is a map `Bool → Bool`, and every such map `G` satisfies `G³ = G`;
hence diagonal `k+2` is `2p`-periodic from time `T + p`. Induction gives period `2^j` from
time `2^j` for diagonal `j` (`ldiag_eventually_periodic`). -/

@[expose] public section

namespace Rule30UOR.LeftTower

open Rule30UOR.Core

/-- Diagonal `j` of the left table is `p`-periodic from time `T`. -/
def LeftPeriodic (j T p : Nat) : Prop := ∀ s, T ≤ s → ldiag j (s + p) = ldiag j s

theorem leftPeriodic_zero : LeftPeriodic 0 0 1 := by
  intro s _
  cases s with
  | zero => rfl
  | succ s => rfl

theorem leftPeriodic_one : LeftPeriodic 1 1 1 := by
  intro s hs
  cases s with
  | zero => exact absurd hs (by cfomega)
  | succ s => rfl

theorem leftPeriodic_mono (j T T' p : Nat) (h : LeftPeriodic j T p) (hT : T ≤ T') :
    LeftPeriodic j T' p :=
  fun s hs => h s (by cfomega)

theorem leftPeriodic_mul (j T p n : Nat) (h : LeftPeriodic j T p) :
    LeftPeriodic j T (n * p) := by
  intro s hs
  induction n with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ n ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h (s + n * p) (by cfomega), ih]

/-- The forced one-bit left system: the state after `n` steps from state `v` at time `s`,
driven by diagonals `k` and `k+1`. -/
def leftRun (k s : Nat) : Nat → Bool → Bool
  | 0, v => v
  | n + 1, v => bxor (ldiag k (s + n)) (ldiag (k + 1) (s + n) || leftRun k s n v)

theorem leftRun_zero (k s : Nat) (v : Bool) : leftRun k s 0 v = v := rfl

theorem leftRun_succ (k s n : Nat) (v : Bool) :
    leftRun k s (n + 1) v = bxor (ldiag k (s + n)) (ldiag (k + 1) (s + n) || leftRun k s n v) :=
  rfl

/-- Diagonal `k+2` is the run of the forced system from its own value. -/
theorem ldiag_eq_leftRun (k s n : Nat) : ldiag (k + 2) (s + n) = leftRun k s n (ldiag (k + 2) s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [leftRun_succ, ← ih, ← Nat.add_assoc]
    exact ldiag_step k (s + n)

/-- Runs compose. -/
theorem leftRun_add (k s n m : Nat) (v : Bool) :
    leftRun k s (n + m) v = leftRun k (s + n) m (leftRun k s n v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, leftRun_succ, leftRun_succ, ih, Nat.add_assoc s n m]

/-- With `p`-periodic drivers, the run from time `s + p` equals the run from time `s`. -/
theorem leftRun_shift (k T p s n : Nat) (v : Bool) (ha : LeftPeriodic k T p)
    (hb : LeftPeriodic (k + 1) T p) (hs : T ≤ s) :
    leftRun k (s + p) n v = leftRun k s n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [leftRun_succ, leftRun_succ, ih,
      show s + p + n = (s + n) + p by cfomega, ha (s + n) (by cfomega), hb (s + n) (by cfomega)]

/-- Every map `Bool → Bool` satisfies `G³ = G`; here for the one-period run. -/
theorem leftRun_three (k s p : Nat) (v : Bool) :
    leftRun k s p (leftRun k s p (leftRun k s p v)) = leftRun k s p v := by
  cases v <;> cases h0 : leftRun k s p false <;> cases h1 : leftRun k s p true <;>
    simp only [h0, h1]

/-- **Step**: if diagonals `k` and `k+1` are `p`-periodic from `T`, diagonal `k+2` is
`2p`-periodic from `T + p`. -/
theorem leftPeriodic_step (k T p : Nat) (ha : LeftPeriodic k T p) (hb : LeftPeriodic (k + 1) T p) :
    LeftPeriodic (k + 2) (T + p) (2 * p) := by
  intro u hu
  have hs : T ≤ u - p := by cfomega
  have hu' : u = (u - p) + p := by cfomega
  have h1 : ldiag (k + 2) ((u - p) + p) = leftRun k (u - p) p (ldiag (k + 2) (u - p)) :=
    ldiag_eq_leftRun k (u - p) p
  have h2 : ldiag (k + 2) ((u - p) + (p + p)) =
      leftRun k (u - p) p (leftRun k (u - p) p (ldiag (k + 2) (u - p))) := by
    rw [ldiag_eq_leftRun, leftRun_add, leftRun_shift k T p (u - p) p _ ha hb hs]
  have h3 : ldiag (k + 2) ((u - p) + (p + p + p)) =
      leftRun k (u - p) p (leftRun k (u - p) p (leftRun k (u - p) p (ldiag (k + 2) (u - p)))) := by
    rw [ldiag_eq_leftRun, leftRun_add, leftRun_add,
      leftRun_shift k T p (u - p) p _ ha hb hs,
      show u - p + (p + p) = (u - p + p) + p by cfomega,
      leftRun_shift k T p (u - p + p) p _ ha hb (by cfomega),
      leftRun_shift k T p (u - p) p _ ha hb hs]
  rw [leftRun_three] at h3
  rw [show u + 2 * p = (u - p) + (p + p + p) by cfomega, h3, ← h1, ← hu']

/-- The period of diagonal `j` given by the step: `2^j`. -/
def leftPeriod : Nat → Nat
  | 0 => 1
  | j + 1 => 2 * leftPeriod j

/-- The transient of diagonal `j` given by the step: `2^j`. -/
def leftTransient (j : Nat) : Nat := leftPeriod j

theorem leftPeriod_eq_twopow (j : Nat) : leftPeriod j = twopow j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show 2 * leftPeriod j = twopow j + twopow j
    rw [ih]; cfomega

/-- Diagonals `j` and `j+1` are both `2^j`-periodic from time `2^j`. -/
theorem leftPeriodic_pair (j : Nat) :
    LeftPeriodic j (leftPeriod j) (leftPeriod j) ∧ LeftPeriodic (j + 1) (leftPeriod j) (leftPeriod j) := by
  induction j with
  | zero => exact ⟨leftPeriodic_mono 0 0 1 1 leftPeriodic_zero (by cfomega), leftPeriodic_one⟩
  | succ j ih =>
    obtain ⟨ha, hb⟩ := ih
    refine ⟨?_, ?_⟩
    · have h := leftPeriodic_mul (j + 1) (leftPeriod j) (leftPeriod j) 2 hb
      exact leftPeriodic_mono (j + 1) (leftPeriod j) (2 * leftPeriod j) (2 * leftPeriod j) h
        (by cfomega)
    · have h := leftPeriodic_step j (leftPeriod j) (leftPeriod j) ha hb
      exact leftPeriodic_mono (j + 2) (leftPeriod j + leftPeriod j) (2 * leftPeriod j)
        (2 * leftPeriod j) h (by cfomega)

/-- **Every left diagonal is eventually periodic**: diagonal `j` is `2^j`-periodic from `2^j`. -/
theorem ldiag_eventually_periodic (j : Nat) : LeftPeriodic j (leftTransient j) (leftPeriod j) :=
  (leftPeriodic_pair j).1

/-- The center is the anti-diagonal of the left table. -/
theorem center_eq_ldiag_self (t : Nat) : center t = ldiag t t := by
  have h := Rule30UOR.Interfaces.ldiag_eq_cell_neg t 0
  rw [Nat.add_zero] at h
  exact h.symm

/-- Under a center period, the anti-diagonal readout of the left table is periodic. -/
theorem ldiag_self_periodic_of_centerPeriodic (T P t : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    ldiag (t + P) (t + P) = ldiag t t := by
  rw [← center_eq_ldiag_self, ← center_eq_ldiag_self]
  exact hc t ht

end Rule30UOR.LeftTower
