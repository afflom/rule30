module
public import Rule30UOR.Interfaces.Part01
public import Rule30UOR.Horizon
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

/-! ## The kernel subsequences and their differences

`kernelSeq k r t = center (2^k t + r)`. The scale identity gives each kernel
subsequence as a running XOR of a difference sequence built from the cell at
depth `2^k` and the window response; in the cone (`t < 2^k`) the response is
the center's own lag-`2^k` difference. The kernel is a binary tree: the
children of `(k, r)` are `(k+1, r)` and `(k+1, r + 2^k)`, the even and odd
subsequences. -/

/-- The kernel subsequence `t ↦ center (2^k t + r)`. -/
def kernelSeq (k r t : Nat) : Bool := center (twopow k * t + r)

theorem kernelSeq_step (k r t : Nat) :
    kernelSeq k r (t + 1) =
      bxor (bxor (kernelSeq k r t) (cell (twopow k * t + r) (Rule30UOR.Scale.negpow k)))
        (Rule30UOR.Scale.response (twopow k * t + r) k) := by
  unfold kernelSeq
  rw [show twopow k * (t + 1) + r = (twopow k * t + r) + twopow k by rw [Nat.mul_succ]; cfomega]
  exact Rule30UOR.Scale.scale_center_paper (twopow k * t + r) k

/-- In the cone the window response is the center's lag-`2^k` difference. -/
theorem response_cone (t k : Nat) (hk : t < twopow k) :
    Rule30UOR.Scale.response t k = bxor (center t) (center (t + twopow k)) := by
  have h := Rule30UOR.Scale.scale_center_paper t k
  rw [show Rule30UOR.Scale.negpow k = -((twopow k : Nat) : Int) from rfl,
    Rule30UOR.Scale.cell_left_white t _ (by cfomega)] at h
  rw [h]
  cases center t <;> cases Rule30UOR.Scale.response t k <;> rfl

/-- Out of the cone the step of a kernel subsequence is the symmetric pair of
cells at distance `2^k` XOR the symmetric (Witt) window response:
`E = cell(s, −2^k) ⊕ cell(s, 2^k) ⊕ wittRespBool s k`. -/
theorem kernelSeq_step_late (k r t : Nat) (hs : twopow k ≤ twopow k * t + r) :
    kernelSeq k r (t + 1) =
      bxor (kernelSeq k r t)
        (bxor (bxor (cell (twopow k * t + r) (Rule30UOR.Scale.negpow k))
          (rdiag (twopow k * t + r - twopow k) (twopow k * t + r)))
          (Rule30UOR.Interfaces.wittRespBool (twopow k * t + r) k)) := by
  rw [kernelSeq_step]
  have h := Rule30UOR.Interfaces.wittRespBool_xor_response_ge (twopow k * t + r) k hs
  rw [← h]
  cases kernelSeq k r t <;> cases cell (twopow k * t + r) (Rule30UOR.Scale.negpow k) <;>
    cases Rule30UOR.Interfaces.wittRespBool (twopow k * t + r) k <;>
    cases Rule30UOR.Scale.response (twopow k * t + r) k <;> rfl

/-- The center's past is recovered from late responses (`center_from_late_responses`):
the value at `d` is the XOR of the two window responses at time `d + 2^k`, for
every `k ≥ d`. -/
theorem center_recovered_at_scale (d k : Nat) (hk : d ≤ k) :
    center d = bxor (Rule30UOR.Interfaces.wittRespBool (d + twopow k) k)
      (Rule30UOR.Scale.response (d + twopow k) k) :=
  Rule30UOR.Interfaces.center_from_late_responses d k hk

theorem kernelSeq_even (k r t : Nat) : kernelSeq (k + 1) r t = kernelSeq k r (2 * t) := by
  unfold kernelSeq
  rw [Rule30UOR.Core.twopow]
  congr 2
  rw [Nat.two_mul, Nat.mul_add, Nat.add_mul]

theorem kernelSeq_odd (k r t : Nat) : kernelSeq (k + 1) (r + twopow k) t = kernelSeq k r (2 * t + 1) := by
  unfold kernelSeq
  rw [Rule30UOR.Core.twopow]
  congr 1
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.two_mul]
  cfomega

/-! ## Dyadic self-similarity

Along the zero path of the kernel tree, `(k, 0) ↦ t ↦ center (2^k t)`, a finite
kernel forces two scales to carry the same subsequence: `center (2^k' t) =
center (2^k t)` for all `t`, some `k < k'`. So Problem 1 follows from the
absence of any dyadic self-similarity of the center. -/

/-- Injective on `[0, n]` forces a value `≥ n`. -/
theorem exists_ge_of_injective_on : ∀ (n : Nat) (f : Nat → Nat),
    (∀ i j, i ≤ n → j ≤ n → f i = f j → i = j) → ∃ i, i ≤ n ∧ n ≤ f i
  | 0, f, _ => ⟨0, Nat.le_refl 0, Nat.zero_le _⟩
  | n + 1, f, hinj => by
    obtain ⟨i, hi, hfi⟩ := exists_ge_of_injective_on n f
      (fun a b ha hb h => hinj a b (by cfomega) (by cfomega) h)
    rcases Nat.lt_or_ge n (f i) with h1 | h1
    · exact ⟨i, by cfomega, h1⟩
    · have hfi' : f i = n := by cfomega
      rcases Nat.lt_or_ge n (f (n + 1)) with h2 | h2
      · exact ⟨n + 1, Nat.le_refl _, h2⟩
      · have hne : f (n + 1) ≠ n := fun h => by
          have := hinj (n + 1) i (Nat.le_refl _) (by cfomega) (by rw [h, hfi'])
          cfomega
        have hlt : f (n + 1) < n := by cfomega
        let g : Nat → Nat := fun j => if j = i then f (n + 1) else f j
        have hg : ∀ a b, a ≤ n → b ≤ n → g a = g b → a = b := by
          intro a b ha hb hab
          have hab' : (if a = i then f (n + 1) else f a) = (if b = i then f (n + 1) else f b) := hab
          by_cases hai : a = i <;> by_cases hbi : b = i
          · rw [hai, hbi]
          · rw [if_pos hai, if_neg hbi] at hab'
            have := hinj (n + 1) b (Nat.le_refl _) (by cfomega) hab'
            cfomega
          · rw [if_neg hai, if_pos hbi] at hab'
            have := hinj a (n + 1) (by cfomega) (Nat.le_refl _) hab'
            cfomega
          · rw [if_neg hai, if_neg hbi] at hab'
            exact hinj a b (by cfomega) (by cfomega) hab'
        obtain ⟨j, hj, hgj⟩ := exists_ge_of_injective_on n g hg
        by_cases hji : j = i
        · have : g j = f (n + 1) := by show (if j = i then f (n + 1) else f j) = _; rw [if_pos hji]
          cfomega
        · have hgj' : g j = f j := by show (if j = i then f (n + 1) else f j) = _; rw [if_neg hji]
          have hne' : f j ≠ n := fun h => hji (hinj j i (by cfomega) (by cfomega) (by rw [h, hfi']))
          exact ⟨j, by cfomega, by cfomega⟩

/-- Pigeonhole on `[0, n]` into `[0, n)`, with a decidable search. -/
theorem pigeon (n : Nat) (f : Nat → Nat) (hf : ∀ i, i ≤ n → f i < n) :
    ∃ a b, a < b ∧ b ≤ n ∧ f a = f b := by
  have hd : Decidable (∃ a, 0 ≤ a ∧ a ≤ n ∧ ∃ b, a < b ∧ b ≤ n ∧ f a = f b) := inferInstance
  rcases hd with hno | hyes
  · exfalso
    have hinj : ∀ i j, i ≤ n → j ≤ n → f i = f j → i = j := by
      intro i j hi hj h
      rcases Nat.lt_trichotomy i j with hlt | heq | hgt
      · exact absurd ⟨i, Nat.zero_le i, hi, j, hlt, hj, h⟩ hno
      · exact heq
      · exact absurd ⟨j, Nat.zero_le j, hj, i, hgt, hi, h.symm⟩ hno
    obtain ⟨i, hi, hfi⟩ := exists_ge_of_injective_on n f hinj
    have := hf i hi
    cfomega
  · obtain ⟨a, -, -, b, hab, hb, h⟩ := hyes
    exact ⟨a, b, hab, hb, h⟩

/-- A finite kernel forces a dyadic self-similarity along the zero path. -/
theorem dyadic_self_similar_of_kernel2Finite (h : Kernel2Finite center) :
    ∃ k k', k < k' ∧ ∀ t, center (twopow k' * t) = center (twopow k * t) := by
  obtain ⟨n, g, hg⟩ := h
  have hpos : ∀ k, 0 < twopow k := fun k => Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) (twopow_ge_succ k)
  have hl : ∀ m, ∃ f : Nat → Nat, ∀ k, k ≤ m → f k < n ∧ ∀ t, center (twopow k * t) = g (f k) t := by
    intro m
    induction m with
    | zero =>
      obtain ⟨i, hi, hP⟩ := hg 0 0 (hpos 0)
      refine ⟨fun _ => i, fun k hk => ?_⟩
      have hk0 : k = 0 := by cfomega
      subst hk0
      exact ⟨hi, fun t => by have := hP t; rwa [Nat.add_zero] at this⟩
    | succ m ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨i, hi, hP⟩ := hg (m + 1) 0 (hpos (m + 1))
      refine ⟨fun k => if k ≤ m then f k else i, fun k hk => ?_⟩
      by_cases hkm : k ≤ m
      · simp only [if_pos hkm]
        exact hf k hkm
      · simp only [if_neg hkm]
        have hk1 : k = m + 1 := by cfomega
        subst hk1
        exact ⟨hi, fun t => by have := hP t; rwa [Nat.add_zero] at this⟩
  obtain ⟨f, hf⟩ := hl n
  obtain ⟨a, b, hab, hb, heq⟩ := pigeon n f (fun i hi => (hf i hi).1)
  refine ⟨a, b, hab, fun t => ?_⟩
  rw [(hf b hb).2 t, (hf a (by cfomega)).2 t, heq]

/-- The simplest column of the kernel tree, `k ↦ center (2^k)`: it flips exactly
when the late Witt response `wittRespBool (2^k) k` is set, because at time `2^k`
the two cells at distance `2^k` are the black edges. -/
theorem center_twopow_succ (k : Nat) :
    center (twopow (k + 1)) = bxor (center (twopow k)) (Rule30UOR.Interfaces.wittRespBool (twopow k) k) := by
  have h := kernelSeq_step_late k 0 1 (by rw [Nat.mul_one, Nat.add_zero]; exact Nat.le_refl _)
  unfold kernelSeq at h
  rw [Nat.mul_one, Nat.add_zero, Nat.mul_add, Nat.mul_one, Nat.add_zero] at h
  have hl : cell (twopow k) (Rule30UOR.Scale.negpow k) = true := by
    show cell (twopow k) (-((twopow k : Nat) : Int)) = true
    rw [Rule30UOR.Scale.cell_eq_kit]
    exact Ruliology.CellularAutomata.Rule30Jen.cell_left_edge (twopow k)
  have hr : rdiag (twopow k - twopow k) (twopow k) = true := by
    rw [Nat.sub_self, Rule30UOR.Right.rdiag_eq_R]
    exact Ruliology.CellularAutomata.Rule30Diagonals.R_zero (twopow k)
  rw [hl, hr] at h
  rw [show twopow (k + 1) = twopow k + twopow k from rfl, h]
  cases center (twopow k) <;> cases Rule30UOR.Interfaces.wittRespBool (twopow k) k <;> rfl

/-- The center is not self-similar under any dyadic dilation. -/
def NoDyadicSelfSimilarity : Prop :=
  ∀ k k', k < k' → ∃ t, ¬ center (twopow k' * t) = center (twopow k * t)

theorem centerInfiniteKernel_of_no_dyadic_self_similarity (h : NoDyadicSelfSimilarity) :
    CenterInfiniteKernel := fun hfin => by
  obtain ⟨k, k', hkk, hs⟩ := dyadic_self_similar_of_kernel2Finite hfin
  obtain ⟨t, ht⟩ := h k k' hkk
  exact ht (hs t)

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

/-! ## Dilation sequences

A dyadic self-similarity `center (2^k' t) = center (2^k t)` for all `t` makes
every dilation sequence `j ↦ center (2^j t)` periodic with period `k' − k`
from `j = k` (substitute `2^j t` for `t`). So a finite kernel makes every
dilation sequence eventually periodic, with one period for all `t`; and
Problem 1 follows if a single dilation sequence, for instance the dyadic
column `j ↦ center (2^j)`, is not eventually periodic. -/

/-- The dilation sequence `j ↦ center (2^j t)` has period `d` from `K`. -/
def DilationPeriodic (t K d : Nat) : Prop := ∀ j, K ≤ j → center (twopow (j + d) * t) = center (twopow j * t)

theorem twopow_add (a b : Nat) : twopow (a + b) = twopow a * twopow b := by
  induction b with
  | zero => rw [Nat.add_zero, Rule30UOR.Core.twopow, Nat.mul_one]
  | succ b ih =>
    rw [Nat.add_succ, Rule30UOR.Core.twopow, Rule30UOR.Core.twopow, ih, Nat.mul_add]

/-- A finite kernel makes every dilation sequence periodic with a common period. -/
theorem dilationPeriodic_of_kernel2Finite (h : Kernel2Finite center) :
    ∃ K d, 0 < d ∧ ∀ t, DilationPeriodic t K d := by
  obtain ⟨k, k', hkk, hs⟩ := dyadic_self_similar_of_kernel2Finite h
  refine ⟨k, k' - k, by cfomega, fun t j hj => ?_⟩
  have h1 := hs (twopow (j - k) * t)
  rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← twopow_add, ← twopow_add,
    show k' + (j - k) = j + (k' - k) by cfomega, show k + (j - k) = j by cfomega] at h1
  exact h1

/-- Some dilation sequence is not eventually periodic. -/
def SomeDilationAperiodic : Prop := ∃ t, ∀ K d, 0 < d → ¬ DilationPeriodic t K d

theorem centerInfiniteKernel_of_dilation_aperiodic (h : SomeDilationAperiodic) :
    CenterInfiniteKernel := fun hfin => by
  obtain ⟨K, d, hd, hall⟩ := dilationPeriodic_of_kernel2Finite hfin
  obtain ⟨t, ht⟩ := h
  exact ht K d hd (hall t)

/-- **Problem 1 follows if some dilation sequence `j ↦ center (2^j t)` is not
eventually periodic**, for instance the dyadic column `j ↦ center (2^j)`. -/
theorem problem1_of_dilation_aperiodic (h : SomeDilationAperiodic) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_infinite_kernel (centerInfiniteKernel_of_dilation_aperiodic h)

/-- The dyadic column `j ↦ center (2^j)` is not eventually periodic. -/
def DyadicColumnAperiodic : Prop := ∀ K d, 0 < d → ¬ DilationPeriodic 1 K d

theorem problem1_of_dyadic_column_aperiodic (h : DyadicColumnAperiodic) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_dilation_aperiodic ⟨1, h⟩

/-! ## Every base

Nothing above used that the base is `2` except the arithmetic of `twopow`.
The same reductions hold in every base `b ≥ 2`: an eventually periodic
sequence is `b`-automatic for every `b` (Allouche–Shallit Thm. 5.4.2), so a
periodic center has a finite `b`-kernel, a finite `b`-kernel forces a
`b`-adic self-similarity, and that makes every `b`-dilation sequence
`j ↦ center (b^j t)` eventually periodic. Problem 1 therefore follows from the
aperiodicity of a single dilation sequence in a single base. The bases are
orthogonal in Cobham's sense (a sequence automatic in two multiplicatively
independent bases is eventually periodic), and the orbit's exact structure is
`2`-adic (the Witt tower), so a base `b` that is not a power of `2` is a
direction in which the orbit carries no built-in self-similarity. -/

/-- `b ^ k`, as a function (LexLean states powers through a named function). -/
def bpow (b k : Nat) : Nat := b ^ k

/-- The `b`-kernel of `f` is finite. -/
def KernelFiniteIn (b : Nat) (f : Nat → Bool) : Prop :=
  ∃ n : Nat, ∃ g : Nat → Nat → Bool,
    ∀ k r, r < bpow b k → ∃ i, i < n ∧ ∀ t, f (bpow b k * t + r) = g i t

theorem bpow_ge_succ (b : Nat) (hb : 2 ≤ b) (k : Nat) : k + 1 ≤ bpow b k :=
  Nat.lt_pow_self (by cfomega)

theorem bpow_mono (b : Nat) (hb : 2 ≤ b) {a c : Nat} (h : a ≤ c) : bpow b a ≤ bpow b c :=
  Nat.pow_le_pow_right (by cfomega) h

theorem bpow_add (b a c : Nat) : bpow b (a + c) = bpow b a * bpow b c := Nat.pow_add b a c

theorem bpow_pos (b : Nat) (hb : 2 ≤ b) (k : Nat) : 0 < bpow b k :=
  Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) (bpow_ge_succ b hb k)

def largeScaleIn (T P : Nat) (i : Nat) (t : Nat) : Bool :=
  if t = 0 then decide (i % 2 = 1) else center (T + ((i / 2 / P % P) * t + i / 2 % P) % P)

def smallScaleIn (b K : Nat) (i : Nat) (t : Nat) : Bool :=
  center (bpow b (i / bpow b K) * t + i % bpow b K)

def kernelFamilyIn (b T P K : Nat) (i : Nat) : Nat → Bool :=
  if i < K * bpow b K then smallScaleIn b K i else largeScaleIn T P (i - K * bpow b K)

/-- **A periodic center has a finite `b`-kernel, for every base `b ≥ 2`.** -/
theorem kernelFiniteIn_of_centerPeriodic (b : Nat) (hb : 2 ≤ b) (T P : Nat) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : KernelFiniteIn b center := by
  refine ⟨(T + P) * bpow b (T + P) + 2 * (P * P), kernelFamilyIn b T P (T + P), ?_⟩
  intro k r hr
  rcases Nat.lt_or_ge k (T + P) with hk | hk
  · refine ⟨k * bpow b (T + P) + r, ?_, ?_⟩
    · have h1 : r < bpow b (T + P) := Nat.lt_of_lt_of_le hr (bpow_mono b hb (Nat.le_of_lt hk))
      have h2 : (k + 1) * bpow b (T + P) ≤ (T + P) * bpow b (T + P) := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at h2
      cfomega
    · intro t
      have h1 : r < bpow b (T + P) := Nat.lt_of_lt_of_le hr (bpow_mono b hb (Nat.le_of_lt hk))
      have hlt : k * bpow b (T + P) + r < (T + P) * bpow b (T + P) := by
        have h2 : (k + 1) * bpow b (T + P) ≤ (T + P) * bpow b (T + P) := Nat.mul_le_mul_right _ hk
        rw [Nat.succ_mul] at h2
        cfomega
      unfold kernelFamilyIn
      rw [if_pos hlt]
      unfold smallScaleIn
      have hpos := bpow_pos b hb (T + P)
      rw [Nat.mul_comm k, Nat.mul_add_div hpos, Nat.div_eq_of_lt h1, Nat.add_zero, Nat.mul_add_mod,
        Nat.mod_eq_of_lt h1]
  · have hbig : T + P ≤ bpow b k :=
      Nat.le_trans (by have := bpow_ge_succ b hb (T + P); cfomega) (bpow_mono b hb hk)
    let u := bpow b k % P
    let v := (r + (P - T % P)) % P
    let bb := if center r then 1 else 0
    refine ⟨(T + P) * bpow b (T + P) + ((u * P + v) * 2 + bb), ?_, ?_⟩
    · have hu : u < P := Nat.mod_lt _ hP
      have hv : v < P := Nat.mod_lt _ hP
      have hbb : bb ≤ 1 := by show (if center r then 1 else 0) ≤ 1; cases center r <;> decide
      have h1 : (u + 1) * P ≤ P * P := Nat.mul_le_mul_right _ hu
      rw [Nat.succ_mul] at h1
      cfomega
    · intro t
      unfold kernelFamilyIn
      rw [if_neg (by cfomega), Nat.add_sub_cancel_left]
      unfold largeScaleIn
      have hu : u < P := Nat.mod_lt _ hP
      have hv : v < P := Nat.mod_lt _ hP
      have hbb : bb ≤ 1 := by show (if center r then 1 else 0) ≤ 1; cases center r <;> decide
      have hdiv : ((u * P + v) * 2 + bb) / 2 = u * P + v := by cfomega
      have hmod : ((u * P + v) * 2 + bb) % 2 = bb := by cfomega
      rw [hdiv, hmod]
      have hv' : (u * P + v) % P = v := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
      have hu' : (u * P + v) / P % P = u := by
        rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hv, Nat.add_zero, Nat.mod_eq_of_lt hu]
      rw [hv', hu']
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0
        simp only [Nat.mul_zero, Nat.zero_add, if_true]
        show center r = decide (bb = 1)
        show center r = decide ((if center r then 1 else 0) = 1)
        rcases Bool.eq_false_or_eq_true (center r) with h | h <;> simp [h]
      · rw [if_neg (by cfomega)]
        have hle : T ≤ bpow b k * t + r := by
          have : bpow b k * 1 ≤ bpow b k * t := Nat.mul_le_mul_left _ htpos
          cfomega
        rw [mod_eq_of_periodic_shift hP hc _ hle, residue_eq P T hP (bpow b k) r t hle]

/-- The center has a finite `b`-kernel (is `b`-automatic). -/
def CenterKernelFiniteIn (b : Nat) : Prop := KernelFiniteIn b center

theorem centerKernelFiniteIn_of_centerPeriodic (b : Nat) (hb : 2 ≤ b) (T P : Nat) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : CenterKernelFiniteIn b :=
  kernelFiniteIn_of_centerPeriodic b hb T P hP hc

/-- The center has an infinite `b`-kernel: it is not `b`-automatic. -/
def CenterInfiniteKernelIn (b : Nat) : Prop := ¬ KernelFiniteIn b center

theorem no_period_of_infinite_kernel_in (b : Nat) (hb : 2 ≤ b) (h : CenterInfiniteKernelIn b) :
    ∀ T P, 0 < P → ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  fun T P hP hc => h (kernelFiniteIn_of_centerPeriodic b hb T P hP hc)

theorem problem1_of_infinite_kernel_in (b : Nat) (hb : 2 ≤ b) (h : CenterInfiniteKernelIn b) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  Rule30UOR.Scale.problem1_iff.2 (no_period_of_infinite_kernel_in b hb h)

/-- A finite `b`-kernel forces a `b`-adic self-similarity along the zero path. -/
theorem self_similar_of_kernelFiniteIn (b : Nat) (hb : 2 ≤ b) (h : KernelFiniteIn b center) :
    ∃ k k', k < k' ∧ ∀ t, center (bpow b k' * t) = center (bpow b k * t) := by
  obtain ⟨n, g, hg⟩ := h
  have hl : ∀ m, ∃ f : Nat → Nat, ∀ k, k ≤ m → f k < n ∧ ∀ t, center (bpow b k * t) = g (f k) t := by
    intro m
    induction m with
    | zero =>
      obtain ⟨i, hi, hP⟩ := hg 0 0 (bpow_pos b hb 0)
      refine ⟨fun _ => i, fun k hk => ?_⟩
      have hk0 : k = 0 := by cfomega
      subst hk0
      exact ⟨hi, fun t => by have := hP t; rwa [Nat.add_zero] at this⟩
    | succ m ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨i, hi, hP⟩ := hg (m + 1) 0 (bpow_pos b hb (m + 1))
      refine ⟨fun k => if k ≤ m then f k else i, fun k hk => ?_⟩
      by_cases hkm : k ≤ m
      · simp only [if_pos hkm]
        exact hf k hkm
      · simp only [if_neg hkm]
        have hk1 : k = m + 1 := by cfomega
        subst hk1
        exact ⟨hi, fun t => by have := hP t; rwa [Nat.add_zero] at this⟩
  obtain ⟨f, hf⟩ := hl n
  obtain ⟨a, c, hac, hc, heq⟩ := pigeon n f (fun i hi => (hf i hi).1)
  refine ⟨a, c, hac, fun t => ?_⟩
  rw [(hf c hc).2 t, (hf a (by cfomega)).2 t, heq]

/-- The `b`-dilation sequence `j ↦ center (b^j t)` has period `d` from `K`. -/
def DilationPeriodicIn (b t K d : Nat) : Prop :=
  ∀ j, K ≤ j → center (bpow b (j + d) * t) = center (bpow b j * t)

theorem dilationPeriodicIn_of_kernelFiniteIn (b : Nat) (hb : 2 ≤ b) (h : KernelFiniteIn b center) :
    ∃ K d, 0 < d ∧ ∀ t, DilationPeriodicIn b t K d := by
  obtain ⟨k, k', hkk, hs⟩ := self_similar_of_kernelFiniteIn b hb h
  refine ⟨k, k' - k, by cfomega, fun t j hj => ?_⟩
  have h1 := hs (bpow b (j - k) * t)
  rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← bpow_add, ← bpow_add,
    show k' + (j - k) = j + (k' - k) by cfomega, show k + (j - k) = j by cfomega] at h1
  exact h1

/-- The `b`-dilation sequence of `t` is not eventually periodic. -/
def DilationAperiodicIn (b t : Nat) : Prop := ∀ K d, 0 < d → ¬ DilationPeriodicIn b t K d

theorem centerInfiniteKernelIn_of_dilation_aperiodic (b : Nat) (hb : 2 ≤ b) (t : Nat)
    (h : DilationAperiodicIn b t) : CenterInfiniteKernelIn b := fun hfin => by
  obtain ⟨K, d, hd, hall⟩ := dilationPeriodicIn_of_kernelFiniteIn b hb hfin
  exact h K d hd (hall t)

/-- **Problem 1 follows from the aperiodicity of one dilation sequence in one base.** -/
theorem problem1_of_dilation_aperiodic_in (b : Nat) (hb : 2 ≤ b) (t : Nat)
    (h : DilationAperiodicIn b t) : Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_infinite_kernel_in b hb (centerInfiniteKernelIn_of_dilation_aperiodic b hb t h)

/-! ### Paper forms (variables before hypotheses) -/

theorem bpow_ge_succ_paper (b k : Nat) (hb : 2 ≤ b) : k + 1 ≤ bpow b k := bpow_ge_succ b hb k

theorem centerKernelFiniteIn_of_centerPeriodic_paper (b T P : Nat) (hb : 2 ≤ b) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : CenterKernelFiniteIn b :=
  kernelFiniteIn_of_centerPeriodic b hb T P hP hc

theorem centerInfiniteKernelIn_of_dilation_aperiodic_paper (b t : Nat) (hb : 2 ≤ b)
    (h : DilationAperiodicIn b t) : CenterInfiniteKernelIn b :=
  centerInfiniteKernelIn_of_dilation_aperiodic b hb t h

/-- **Problem 1 follows from the aperiodicity of one dilation sequence in one base** (paper form). -/
theorem problem1_of_dilation_aperiodic_in_paper (b t : Nat) (hb : 2 ≤ b) (h : DilationAperiodicIn b t) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_dilation_aperiodic_in b hb t h

/-! ## κ-collapse

The carries are the whole nonlinearity (`Ledger`), and in the cone the window
response is the carry contribution to the center at scale `k`:
`response r k = center r ⊕ center (r + 2^k)` for `r < 2^k`. Call the uniform
vanishing of these responses from scale `K` on a *κ-collapse at scale `K`*: the
carries no longer reach the center at any scale `≥ K`. A κ-collapse is exactly
a center period `2^K` from time `0`: the collapse of the leaves is the root.
The horizon certificate refutes it for every `K ≤ 7`. -/

/-- κ-collapse at scale `K`: every cone response at scales `≥ K` vanishes. -/
def KappaCollapse (K : Nat) : Prop :=
  ∀ k r, K ≤ k → r < twopow k → Rule30UOR.Scale.response r k = false

theorem twopow_dvd_of_le {K k : Nat} (h : K ≤ k) : ∃ m, twopow k = twopow K * m :=
  ⟨twopow (k - K), by rw [← twopow_add, Nat.add_sub_cancel' h]⟩

theorem center_mod_of_kappaCollapse (K : Nat) (h : KappaCollapse K) :
    ∀ k n, K ≤ k → n < twopow k → center n = center (n % twopow K) := by
  intro k
  induction k with
  | zero =>
    intro n hK hn
    have hK0 : K = 0 := by cfomega
    subst hK0
    have : n = 0 := by
      have := hn; rw [Rule30UOR.Core.twopow] at this; cfomega
    subst this; rfl
  | succ k ih =>
    intro n hK hn
    rcases Nat.lt_or_ge n (twopow k) with hlt | hge
    · rcases Nat.lt_or_ge k K with hkK | hkK
      · have hkK' : K = k + 1 := by cfomega
        rw [hkK', Nat.mod_eq_of_lt hn]
      · exact ih n hkK hlt
    · have hk2 : twopow (k + 1) = twopow k + twopow k := rfl
      have hr : n - twopow k < twopow k := by cfomega
      have hn' : n = (n - twopow k) + twopow k := by cfomega
      rcases Nat.lt_or_ge k K with hkK | hkK
      · have hkK' : K = k + 1 := by cfomega
        rw [hkK', Nat.mod_eq_of_lt hn]
      · have hc := response_cone (n - twopow k) k hr
        rw [h k (n - twopow k) hkK hr] at hc
        have hc' : center (n - twopow k + twopow k) = center (n - twopow k) := by
          rcases Bool.eq_false_or_eq_true (center (n - twopow k)) with hx | hx <;>
            rcases Bool.eq_false_or_eq_true (center (n - twopow k + twopow k)) with hy | hy <;>
            rw [hx, hy] at hc ⊢ <;> first | rfl | exact absurd hc (by decide)
        obtain ⟨m, hm⟩ := twopow_dvd_of_le hkK
        have e : (n - twopow k + twopow k) % twopow K = (n - twopow k) % twopow K := by
          rw [hm, Nat.add_mul_mod_self_left]
        calc center n = center (n - twopow k + twopow k) := by rw [← hn']
          _ = center (n - twopow k) := hc'
          _ = center ((n - twopow k) % twopow K) := ih (n - twopow k) hkK hr
          _ = center ((n - twopow k + twopow k) % twopow K) := by rw [e]
          _ = center (n % twopow K) := by rw [← hn']

/-- A κ-collapse at scale `K` is a center period `2^K` from time `0`. -/
theorem centerPeriodic_of_kappaCollapse (K : Nat) (h : KappaCollapse K) :
    Rule30UOR.Scale.CenterPeriodic 0 (twopow K) := by
  intro t _
  have hb : ∀ n, center n = center (n % twopow K) := by
    intro n
    have hk : n < twopow (n + K) := by
      have := twopow_ge_succ (n + K); cfomega
    exact center_mod_of_kappaCollapse K h (n + K) n (by cfomega) hk
  rw [hb (t + twopow K), hb t, Nat.add_mod_right]

/-- Conversely a center period `2^K` from `0` collapses every cone response at scales `≥ K`. -/
theorem kappaCollapse_of_centerPeriodic (K : Nat) (h : Rule30UOR.Scale.CenterPeriodic 0 (twopow K)) :
    KappaCollapse K := by
  intro k r hK hr
  rw [response_cone r k hr]
  obtain ⟨m, hm⟩ := twopow_dvd_of_le hK
  have := Rule30UOR.Scale.center_mul h m r (Nat.zero_le r)
  rw [Nat.mul_comm, ← hm] at this
  rw [this]
  cases center r <;> rfl

/-- **κ-collapse is the period.** -/
theorem kappaCollapse_iff (K : Nat) : KappaCollapse K ↔ Rule30UOR.Scale.CenterPeriodic 0 (twopow K) :=
  ⟨centerPeriodic_of_kappaCollapse K, kappaCollapse_of_centerPeriodic K⟩

/-- No κ-collapse at any scale `K ≤ 7` (from the horizon certificate). -/
theorem no_kappaCollapse_small (K : Nat) (hK : K ≤ 7) : ¬ KappaCollapse K := fun h =>
  Rule30UOR.Horizon.no_center_period_512_128 0 (twopow K) (Nat.zero_le _)
    (Nat.lt_of_lt_of_le (Nat.zero_lt_succ K) (twopow_ge_succ K))
    (Nat.le_trans (twopow_mono hK) (by decide)) (centerPeriodic_of_kappaCollapse K h)

/-- Problem 1 is exactly: no κ-collapse at any scale and no period that is not a power of two. -/
theorem no_kappaCollapse_of_problem1 (h : Ruliology.CellularAutomata.Rule30Prize.Problem1) (K : Nat) :
    ¬ KappaCollapse K := fun hc =>
  Rule30UOR.Scale.problem1_iff.1 h 0 (twopow K)
    (Nat.lt_of_lt_of_le (Nat.zero_lt_succ K) (twopow_ge_succ K)) (centerPeriodic_of_kappaCollapse K hc)

theorem no_kappaCollapse_of_problem1_paper (K : Nat) (h : Ruliology.CellularAutomata.Rule30Prize.Problem1) :
    ¬ KappaCollapse K := no_kappaCollapse_of_problem1 h K

/-- **Problem 1 follows from the absence of dyadic self-similarity.** -/
theorem problem1_of_no_dyadic_self_similarity (h : NoDyadicSelfSimilarity) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_infinite_kernel (centerInfiniteKernel_of_no_dyadic_self_similarity h)

end Rule30UOR.Automatic
