module
public import Rule30UOR.Automatic
public import Rule30UOR.EdgeParity
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The 2-kernel and the parity of time

Adding the parity of `t` to a sequence does not change whether its 2-kernel
is finite. The kernel subsequence `t ↦ f (2^k t + r)` picks up, for `k ≥ 1`,
the constant `r mod 2`, and for `k = 0` the parity of `t` itself; so a finite
family for `f` yields a finite family for `f ⊕ parity`, four times as large,
and conversely. This is the host lemma that lets the edge-sourced diagonal,
which is the parity of `t`, be cancelled from the center before the kernel
is examined. -/

@[expose] public section

namespace Rule30UOR.KernelParity

open Rule30UOR.Core
open Rule30UOR.Automatic
open Rule30UOR.EdgeSplit Rule30UOR.EdgeParity

/-- Kernel finiteness transfers along pointwise equality. -/
theorem kernel2Finite_congr (f g : Nat → Bool) (h : ∀ t, f t = g t)
    (hf : Kernel2Finite f) : Kernel2Finite g := by
  obtain ⟨n, G, hG⟩ := hf
  refine ⟨n, G, fun k r hr => ?_⟩
  obtain ⟨i, hi, hit⟩ := hG k r hr
  exact ⟨i, hi, fun t => by rw [← h, hit]⟩

/-- For `k ≥ 1`, `2^k` is twice `2^(k-1)`. -/
theorem twopow_eq_two_mul (k : Nat) (hk : 1 ≤ k) : twopow k = 2 * twopow (k - 1) := by
  cases k with
  | zero => cfomega
  | succ j =>
    rw [twopow_succ, Nat.add_sub_cancel]
    cfomega

/-- For `k ≥ 1` the parity of `2^k t + r` is the parity of `r`. -/
theorem parity_twopow_mul_add (k r t : Nat) (hk : 1 ≤ k) :
    decide ((twopow k * t + r) % 2 = 1) = decide (r % 2 = 1) := by
  rw [twopow_eq_two_mul k hk, Nat.mul_assoc]
  generalize twopow (k - 1) * t = y
  have h : (2 * y + r) % 2 = r % 2 := by cfomega
  rw [h]

/-- The family indexing the kernel of `f ⊕ parity` from a family `g` for the
kernel of `f`: index `4 i + c` carries the base sequence `g i`, the constant
bit `c / 2`, and whether the parity of `t` is added (`c` odd). -/
def parityKernel (g : Nat → Nat → Bool) (i : Nat) (t : Nat) : Bool :=
  bxor (bxor (g (i / 4) t) (decide (i % 4 / 2 = 1)))
    (if i % 2 = 1 then decide (t % 2 = 1) else false)

theorem bxor_bxor_self (a b : Bool) : bxor (bxor a b) b = a := by
  cases a <;> cases b <;> rfl

/-- A finite 2-kernel survives adding the parity of time. -/
theorem kernel2Finite_xor_parity_of (f : Nat → Bool) (hf : Kernel2Finite f) :
    Kernel2Finite (fun t => bxor (f t) (decide (t % 2 = 1))) := by
  obtain ⟨n, g, hg⟩ := hf
  refine ⟨4 * n, parityKernel g, fun k r hr => ?_⟩
  obtain ⟨i, hi, hit⟩ := hg k r hr
  cases k with
  | zero =>
    have hr0 : r = 0 := by
      have h1 : twopow 0 = 1 := rfl
      cfomega
    refine ⟨4 * i + 1, by cfomega, fun t => ?_⟩
    have ht : twopow 0 * t + r = t := by
      rw [hr0]
      show 1 * t + 0 = t
      cfomega
    show bxor (f (twopow 0 * t + r)) (decide ((twopow 0 * t + r) % 2 = 1)) =
      parityKernel g (4 * i + 1) t
    rw [hit t, ht, parityKernel]
    have h1 : (4 * i + 1) / 4 = i := by cfomega
    have h2 : decide ((4 * i + 1) % 4 / 2 = 1) = false := decide_eq_false (by cfomega)
    have h3 : (4 * i + 1) % 2 = 1 := by cfomega
    rw [h1, h2, if_pos h3]
    cases g i t <;> rfl
  | succ j =>
    have hp : ∀ t, decide ((twopow (j + 1) * t + r) % 2 = 1) = decide (r % 2 = 1) :=
      fun t => parity_twopow_mul_add (j + 1) r t (by cfomega)
    rcases Nat.mod_two_eq_zero_or_one r with hr2 | hr2
    · refine ⟨4 * i, by cfomega, fun t => ?_⟩
      show bxor (f (twopow (j + 1) * t + r)) (decide ((twopow (j + 1) * t + r) % 2 = 1)) =
        parityKernel g (4 * i) t
      rw [hit t, hp t, parityKernel]
      have h1 : (4 * i) / 4 = i := by cfomega
      have h2 : decide ((4 * i) % 4 / 2 = 1) = false := decide_eq_false (by cfomega)
      have h3 : ¬ ((4 * i) % 2 = 1) := by cfomega
      have h4 : decide (r % 2 = 1) = false := decide_eq_false (by cfomega)
      rw [h1, h2, if_neg h3, h4]
      cases g i t <;> rfl
    · refine ⟨4 * i + 2, by cfomega, fun t => ?_⟩
      show bxor (f (twopow (j + 1) * t + r)) (decide ((twopow (j + 1) * t + r) % 2 = 1)) =
        parityKernel g (4 * i + 2) t
      rw [hit t, hp t, parityKernel]
      have h1 : (4 * i + 2) / 4 = i := by cfomega
      have h2 : decide ((4 * i + 2) % 4 / 2 = 1) = true := decide_eq_true (by cfomega)
      have h3 : ¬ ((4 * i + 2) % 2 = 1) := by cfomega
      have h4 : decide (r % 2 = 1) = true := decide_eq_true hr2
      rw [h1, h2, if_neg h3, h4]
      cases g i t <;> rfl

/-- The 2-kernel of `f` is finite exactly when that of `f ⊕ parity` is. -/
theorem kernel2Finite_xor_parity (f : Nat → Bool) :
    Kernel2Finite f ↔ Kernel2Finite (fun t => bxor (f t) (decide (t % 2 = 1))) := by
  refine ⟨kernel2Finite_xor_parity_of f, fun h => ?_⟩
  have h2 := kernel2Finite_xor_parity_of (fun t => bxor (f t) (decide (t % 2 = 1))) h
  exact kernel2Finite_congr _ f (fun t => bxor_bxor_self (f t) (decide (t % 2 = 1))) h2


/-- A finite 2-kernel is closed under negation. -/
theorem kernel2Finite_not_of (f : Nat → Bool) (hf : Kernel2Finite f) : Kernel2Finite (fun t => !(f t)) := by
  obtain ⟨n, g, hg⟩ := hf
  refine ⟨n, fun i t => !(g i t), ?_⟩
  intro k r hr
  obtain ⟨i, hi, hit⟩ := hg k r hr
  exact ⟨i, hi, fun t => by show (!(f (twopow k * t + r))) = (!(g i t)); rw [hit t]⟩

/-- The interior diagonal has a finite 2-kernel. -/
def InteriorKernelFinite : Prop := Kernel2Finite interiorDiagonal

/-- **The center is 2-automatic exactly when the interior diagonal is**: the edge background
is the time parity, and a finite 2-kernel is closed under negation and under XOR with it. -/
theorem centerKernelFinite_iff_interior : CenterKernelFinite ↔ InteriorKernelFinite := by
  unfold CenterKernelFinite InteriorKernelFinite
  constructor
  · intro h
    have h1 := kernel2Finite_not_of _ (kernel2Finite_xor_parity_of center h)
    refine kernel2Finite_congr _ _ (fun t => ?_) h1
    show (!(bxor (center t) (decide (t % 2 = 1)))) = interiorDiagonal t
    rw [interiorDiagonal_eq_center t]
    show (!(bxor (center t) (decide (t % 2 = 1)))) = bxor (!(center t)) (decide (t % 2 = 1))
    cases center t <;> cases decide (t % 2 = 1) <;> rfl
  · intro h
    have h1 := kernel2Finite_xor_parity_of _ (kernel2Finite_not_of interiorDiagonal h)
    refine kernel2Finite_congr _ _ (fun t => ?_) h1
    show bxor (!(interiorDiagonal t)) (decide (t % 2 = 1)) = center t
    rw [center_eq_not_timeParity_xor_interior t]
    show bxor (!(interiorDiagonal t)) (decide (t % 2 = 1)) = (!(bxor (decide (t % 2 = 1)) (interiorDiagonal t)))
    cases interiorDiagonal t <;> cases decide (t % 2 = 1) <;> rfl

/-- The center is not 2-automatic exactly when the interior diagonal is not. -/
theorem centerInfiniteKernel_iff_interior : CenterInfiniteKernel ↔ ¬ InteriorKernelFinite := by
  unfold CenterInfiniteKernel
  constructor
  · intro h hi; exact h (centerKernelFinite_iff_interior.2 hi)
  · intro h hc; exact h (centerKernelFinite_iff_interior.1 hc)

/-- Problem 1 follows if the interior diagonal is not 2-automatic. -/
theorem problem1_of_interior_infinite_kernel (h : ¬ InteriorKernelFinite) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_infinite_kernel (centerInfiniteKernel_iff_interior.2 h)

end Rule30UOR.KernelParity
