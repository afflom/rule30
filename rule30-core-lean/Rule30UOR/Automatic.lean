module
public import Rule30UOR.Interfaces.Part01
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The 2-kernel of the center

A sequence `f : Nat → Bool` is 2-automatic exactly when its 2-kernel, the family
of subsequences `t ↦ f (2^k t + r)` with `r < 2^k`, is finite (Eilenberg;
Allouche–Shallit, *Automatic Sequences*, Thm. 6.6.2). An eventually periodic
sequence is `k`-automatic for every `k` (ibid., Thm. 5.4.2). Hence a periodic
center has a finite 2-kernel, and Problem 1 follows from the stronger statement
that the center column is not 2-automatic: its 2-kernel is infinite. The
2-kernel is the natural object of the scale machinery (`scale_center`:
`center (t + 2^k)` in terms of `center t`, the cell at depth `2^k` and the window
response), which is why this reduction is recorded here.

The finiteness is stated constructively: a finite family `g 0, …, g (n-1)` of
sequences such that every kernel subsequence equals one of them. Under
`CenterPeriodic T P` the family is explicit: the kernel subsequences with
`2^k < T + P`, indexed directly, and for `2^k ≥ T + P` the sequences
`t ↦ if t = 0 then b else center (T + (u t + v) % P)` with `u, v < P`. -/

@[expose] public section

namespace Rule30UOR.Automatic

open Rule30UOR.Core

/-- The 2-kernel of `f` is finite: every subsequence `t ↦ f (2^k t + r)`,
`r < 2^k`, is one of `n` listed sequences. -/
def Kernel2Finite (f : Nat → Bool) : Prop :=
  ∃ n : Nat, ∃ g : Nat → Nat → Bool,
    ∀ k r, r < twopow k → ∃ i, i < n ∧ ∀ t, f (twopow k * t + r) = g i t

/-- The center column has a finite 2-kernel (is 2-automatic). -/
def CenterKernelFinite : Prop := Kernel2Finite center

/-- The center column is not 2-automatic. -/
def CenterInfiniteKernel : Prop := ¬ Kernel2Finite center

theorem twopow_ge_succ : ∀ k, k + 1 ≤ twopow k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Rule30UOR.Core.twopow]
    have := twopow_ge_succ k
    cfomega

theorem twopow_mono {a b : Nat} (h : a ≤ b) : twopow a ≤ twopow b := by
  induction b with
  | zero =>
    have : a = 0 := by cfomega
    subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h1 | h1
    · have := ih (by cfomega)
      rw [Rule30UOR.Core.twopow]
      cfomega
    · have : a = b + 1 := by cfomega
      subst this; exact Nat.le_refl _

/-- The family for the large scales: `t ↦ if t = 0 then b else center (T + (u t + v) % P)`. -/
def largeScale (T P : Nat) (i : Nat) (t : Nat) : Bool :=
  if t = 0 then decide (i % 2 = 1) else center (T + ((i / 2 / P % P) * t + i / 2 % P) % P)

/-- The family for the small scales, indexed by `k * 2^K + r`. -/
def smallScale (K : Nat) (i : Nat) (t : Nat) : Bool :=
  center (twopow (i / twopow K) * t + i % twopow K)

def kernelFamily (T P K : Nat) (i : Nat) : Nat → Bool :=
  if i < K * twopow K then smallScale K i else largeScale T P (i - K * twopow K)

theorem mod_eq_of_periodic_shift {T P : Nat} (hP : 0 < P) (hc : Rule30UOR.Scale.CenterPeriodic T P)
    (s : Nat) (hs : T ≤ s) : center s = center (T + (s - T) % P) := by
  have := Rule30UOR.Scale.center_mod hP hc T (s - T) (Nat.le_refl T)
  rw [show T + (s - T) = s by cfomega] at this
  exact this

theorem residue_eq (P T : Nat) (hP : 0 < P) (a r : Nat) (t : Nat) (h : T ≤ a * t + r) :
    (a * t + r - T) % P = ((a % P) * t + (r + (P - T % P)) % P) % P := by
  have h1 : (a * t + r - T) % P = (a * t + r + (P - T % P)) % P := by
    have hd := Nat.div_add_mod T P
    have hm : T % P < P := Nat.mod_lt T hP
    have e : a * t + r + (P - T % P) = (a * t + r - T) + P * (T / P + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; cfomega
    rw [e, Nat.add_mul_mod_self_left]
  rw [h1]
  symm
  rw [Nat.add_mod (a % P * t) ((r + (P - T % P)) % P) P, Nat.mod_mod, Nat.mul_mod (a % P) t P,
    Nat.mod_mod a P, ← Nat.mul_mod a t P, ← Nat.add_mod (a * t) (r + (P - T % P)) P, Nat.add_assoc]

/-- **A periodic center has a finite 2-kernel.** -/
theorem kernel2Finite_of_centerPeriodic (T P : Nat) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : Kernel2Finite center := by
  refine ⟨(T + P) * twopow (T + P) + 2 * (P * P), kernelFamily T P (T + P), ?_⟩
  intro k r hr
  rcases Nat.lt_or_ge k (T + P) with hk | hk
  · -- small scale: index directly
    refine ⟨k * twopow (T + P) + r, ?_, ?_⟩
    · have h1 : r < twopow (T + P) := Nat.lt_of_lt_of_le hr (twopow_mono (Nat.le_of_lt hk))
      have h2 : (k + 1) * twopow (T + P) ≤ (T + P) * twopow (T + P) :=
        Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at h2
      cfomega
    · intro t
      have h1 : r < twopow (T + P) := Nat.lt_of_lt_of_le hr (twopow_mono (Nat.le_of_lt hk))
      have hlt : k * twopow (T + P) + r < (T + P) * twopow (T + P) := by
        have h2 : (k + 1) * twopow (T + P) ≤ (T + P) * twopow (T + P) :=
          Nat.mul_le_mul_right _ hk
        rw [Nat.succ_mul] at h2
        cfomega
      unfold kernelFamily
      rw [if_pos hlt]
      unfold smallScale
      have hpos : 0 < twopow (T + P) := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (twopow_ge_succ _)
      rw [Nat.mul_comm k, Nat.mul_add_div hpos, Nat.div_eq_of_lt h1, Nat.add_zero, Nat.mul_add_mod,
        Nat.mod_eq_of_lt h1]
  · -- large scale: residues
    have hbig : T + P ≤ twopow k :=
      Nat.le_trans (by have := twopow_ge_succ (T + P); cfomega) (twopow_mono hk)
    let u := twopow k % P
    let v := (r + (P - T % P)) % P
    let b := if center r then 1 else 0
    refine ⟨(T + P) * twopow (T + P) + ((u * P + v) * 2 + b), ?_, ?_⟩
    · have hu : u < P := Nat.mod_lt _ hP
      have hv : v < P := Nat.mod_lt _ hP
      have hb : b ≤ 1 := by show (if center r then 1 else 0) ≤ 1; cases center r <;> decide
      have h1 : (u + 1) * P ≤ P * P := Nat.mul_le_mul_right _ hu
      rw [Nat.succ_mul] at h1
      cfomega
    · intro t
      unfold kernelFamily
      rw [if_neg (by cfomega), Nat.add_sub_cancel_left]
      unfold largeScale
      have hu : u < P := Nat.mod_lt _ hP
      have hv : v < P := Nat.mod_lt _ hP
      have hb : b ≤ 1 := by show (if center r then 1 else 0) ≤ 1; cases center r <;> decide
      have hdiv : ((u * P + v) * 2 + b) / 2 = u * P + v := by cfomega
      have hmod : ((u * P + v) * 2 + b) % 2 = b := by cfomega
      rw [hdiv, hmod]
      have hv' : (u * P + v) % P = v := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
      have hu' : (u * P + v) / P % P = u := by
        rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hv, Nat.add_zero, Nat.mod_eq_of_lt hu]
      rw [hv', hu']
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0
        simp only [Nat.mul_zero, Nat.zero_add, if_true]
        show center r = decide (b = 1)
        show center r = decide ((if center r then 1 else 0) = 1)
        rcases Bool.eq_false_or_eq_true (center r) with h | h <;> simp [h]
      · rw [if_neg (by cfomega)]
        have hle : T ≤ twopow k * t + r := by
          have : twopow k * 1 ≤ twopow k * t := Nat.mul_le_mul_left _ htpos
          cfomega
        rw [mod_eq_of_periodic_shift hP hc _ hle, residue_eq P T hP (twopow k) r t hle]

/-- Paper form of the finiteness. -/
theorem centerKernelFinite_of_centerPeriodic (T P : Nat) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : CenterKernelFinite :=
  kernel2Finite_of_centerPeriodic T P hP hc

/-- **Problem 1 follows from an infinite 2-kernel.** -/
theorem no_period_of_infinite_kernel (h : CenterInfiniteKernel) :
    ∀ T P, 0 < P → ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  fun T P hP hc => h (kernel2Finite_of_centerPeriodic T P hP hc)

/-- Paper form: no center period at all once the 2-kernel is infinite. -/
theorem not_centerPeriodic_of_infinite_kernel (T P : Nat) (h : CenterInfiniteKernel) (hP : 0 < P) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  no_period_of_infinite_kernel h T P hP

theorem problem1_of_infinite_kernel (h : CenterInfiniteKernel) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  Rule30UOR.Scale.problem1_iff.2 (no_period_of_infinite_kernel h)

end Rule30UOR.Automatic
