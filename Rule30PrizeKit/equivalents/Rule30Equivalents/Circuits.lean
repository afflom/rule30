module

public import Rule30Equivalents.RandomConfigurations
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Circuit lower bounds for a random center column

Prize Problem 3 asks that computing `c(n)` take effort about `n`. A non-uniform relative asks for
large Boolean circuits: the restriction of `c` to the times `t < 2ᵏ`, as a Boolean function of the
`k` binary digits of `t`, should need circuits of size near `2ᵏ`. For an explicit function no
lower bound beyond a constant times `k` is known; for a random configuration Shannon's counting
argument gives size `2ᵏ/(8k)`.

* `ae_circuit_lower_bound_trace`: **for almost every configuration and all large `k`, no circuit
  with at most `2ᵏ/(8k)` binary gates computes `t ↦ c(t)`, `t < 2ᵏ`, from the binary digits of
  `t`** (least significant first, `index_apply`).

A circuit is a straight-line program (`Prog`): gate `i` applies one of the sixteen binary Boolean
functions to two of the `k + i` earlier wires. There are at most `(16 (k + s)²)^s` programs with `s`
gates (`card_prog_le`), and a given program computes the random function with probability
`2^(-2ᵏ)` (`measure_computes_le`). By the union bound some program with at most `2ᵏ/(8k)` gates
succeeds with probability at most `2⁻ᵏ` for `k ≥ 5` (`measure_exists_small_circuit_le`), and the
Borel–Cantelli lemma applies (`ae_eventually_no_small_circuit`).
-/

@[expose] public section

namespace Rule30Equivalents.Circuits

open MeasureTheory Filter Topology Genericity RandomConfigurations

/-- Straight-line programs on `k` input bits with `s` binary gates: gate `i` applies a Boolean
function to two of the `k + i` earlier wires, the inputs and then the earlier gates. -/
def Prog (k : ℕ) : ℕ → Type
  | 0 => Unit
  | s + 1 => Prog k s × (Bool → Bool → Bool) × Fin (k + s) × Fin (k + s)

instance Prog.instFintype (k : ℕ) : (s : ℕ) → Fintype (Prog k s)
  | 0 => inferInstanceAs (Fintype Unit)
  | s + 1 =>
    letI := Prog.instFintype k s
    inferInstanceAs (Fintype (Prog k s × (Bool → Bool → Bool) × Fin (k + s) × Fin (k + s)))

/-- The values of the `k + s` wires of a program on the input `x`. -/
def Prog.wire {k : ℕ} : {s : ℕ} → Prog k s → (Fin k → Bool) → Fin (k + s) → Bool
  | 0, _, x, w => x w
  | s + 1, P, x, w =>
    if h : (w : ℕ) < k + s then Prog.wire P.1 x ⟨w, h⟩
    else P.2.1 (Prog.wire P.1 x P.2.2.1) (Prog.wire P.1 x P.2.2.2)

/-- A program with `s + 1` gates computes `f` if its last gate agrees with `f` on every input. -/
def Prog.Computes {k s : ℕ} (P : Prog k (s + 1)) (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ x, P.wire x ⟨k + s, by omega⟩ = f x

/-- There are at most `(16 (k + s)²)^s` programs with `s` gates: gate `i` has sixteen functions and
`(k + i)²` pairs of earlier wires to choose from. -/
theorem card_prog_le (k : ℕ) : ∀ s, Fintype.card (Prog k s) ≤ (16 * (k + s) ^ 2) ^ s
  | 0 => by
    show Fintype.card Unit ≤ _
    simp
  | s + 1 => by
    have ih := card_prog_le k s
    have hcard : Fintype.card (Prog k (s + 1)) =
        Fintype.card (Prog k s) * (16 * (k + s) ^ 2) := by
      show Fintype.card (Prog k s × (Bool → Bool → Bool) × Fin (k + s) × Fin (k + s)) = _
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      ring
    have h1 : 16 * (k + s) ^ 2 ≤ 16 * (k + (s + 1)) ^ 2 :=
      Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by omega) 2)
    rw [hcard, pow_succ]
    exact Nat.mul_le_mul (ih.trans (Nat.pow_le_pow_left h1 s)) h1

/-- The index of an input: `x` read as a binary numeral, least significant digit first. -/
def index (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) finTwoEquiv.symm).trans finFunctionFinEquiv

theorem index_apply (k : ℕ) (x : Fin k → Bool) :
    (index k x : ℕ) = ∑ i, (if x i then 1 else 0) * 2 ^ (i : ℕ) := by
  rw [index, Equiv.trans_apply, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply]
  cases x i <;> rfl

/-- A given program computes `x ↦ v(index x)` with probability at most `2^(-2ᵏ)`: it fixes the
first `2ᵏ` coins. -/
theorem measure_computes_le {k s : ℕ} (P : Prog k (s + 1)) :
    coins ℕ {v | P.Computes fun x => v (index k x)} ≤ 2⁻¹ ^ 2 ^ k := by
  calc coins ℕ {v | P.Computes fun x => v (index k x)}
      ≤ coins ℕ (Set.pi (Finset.range (2 ^ k) : Set ℕ) fun n =>
          {if h : n < 2 ^ k then P.wire ((index k).symm ⟨n, h⟩) ⟨k + s, by omega⟩ else false}) :=
        measure_mono fun v hv => by
          simp only [Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff]
          intro n hn
          rw [dite_eq_left hn]
          have := hv ((index k).symm ⟨n, hn⟩)
          simp only [Equiv.apply_symm_apply] at this
          exact this.symm
    _ = 2⁻¹ ^ 2 ^ k := by
        rw [coins_pi, Finset.prod_congr rfl fun n _ => coin_singleton _, Finset.prod_const,
          Finset.card_range]

/-- `2k ≤ 2^(k - 1)` for `k ≥ 5`. -/
theorem two_mul_le_two_pow {k : ℕ} (hk : 5 ≤ k) : 2 * k ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 - 1 = k - 1 + 1 by omega, pow_succ]
    omega

/-- The counting: `S (16 (k + S)²)^S ≤ 2^(2ᵏ - k)` for `S = 2ᵏ/(8k)` and `k ≥ 5`. -/
theorem count_le {k : ℕ} (hk : 5 ≤ k) :
    2 ^ k / (8 * k) * (16 * (k + 2 ^ k / (8 * k)) ^ 2) ^ (2 ^ k / (8 * k)) ≤ 2 ^ (2 ^ k - k) := by
  set S := 2 ^ k / (8 * k) with hS
  have h8 : S * (8 * k) ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have hpk := two_mul_le_two_pow hk
  have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hS2 : S ≤ 2 ^ (k - 1) := by nlinarith
  have hkS : k + S ≤ 2 ^ k := by omega
  -- the base is at most `2^(2k + 4)`
  have hbase : 16 * (k + S) ^ 2 ≤ 2 ^ (2 * k + 4) := by
    calc 16 * (k + S) ^ 2 ≤ 16 * (2 ^ k) ^ 2 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hkS 2)
      _ = 2 ^ (2 * k + 4) := by rw [← pow_mul, show 2 * k + 4 = k * 2 + 4 by ring, pow_add]; ring
  -- the exponent: `(2k + 4) S ≤ 2^(k - 1)`
  have hexp : (2 * k + 4) * S ≤ 2 ^ (k - 1) := by nlinarith
  have hfin : k + 2 ^ (k - 1) ≤ 2 ^ k - k := by omega
  calc S * (16 * (k + S) ^ 2) ^ S ≤ 2 ^ k * (2 ^ (2 * k + 4)) ^ S :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hbase S)
    _ = 2 ^ (k + (2 * k + 4) * S) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (2 ^ k - k) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Shannon's counting bound**: some circuit with at most `2ᵏ/(8k)` gates computes
`x ↦ v(index x)` with probability at most `2⁻ᵏ`, for `k ≥ 5`. -/
theorem measure_exists_small_circuit_le {k : ℕ} (hk : 5 ≤ k) :
    coins ℕ {v | ∃ s, s + 1 ≤ 2 ^ k / (8 * k) ∧ ∃ P : Prog k (s + 1),
      P.Computes fun x => v (index k x)} ≤ 2⁻¹ ^ k := by
  classical
  set S := 2 ^ k / (8 * k) with hS
  have hsub : {v : ℕ → Bool | ∃ s, s + 1 ≤ S ∧ ∃ P : Prog k (s + 1),
      P.Computes fun x => v (index k x)} ⊆ ⋃ s ∈ Finset.range S, ⋃ P : Prog k (s + 1),
        {v | P.Computes fun x => v (index k x)} := by
    rintro v ⟨s, hs, P, hP⟩
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact ⟨s, by omega, P, hP⟩
  have hcard : ∀ s ∈ Finset.range S, Fintype.card (Prog k (s + 1)) ≤ (16 * (k + S) ^ 2) ^ S :=
    fun s hs => by
      have hs' := Finset.mem_range.1 hs
      refine (card_prog_le k (s + 1)).trans ((Nat.pow_le_pow_left (Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (by omega) 2)) _).trans (Nat.pow_le_pow_right ?_ (by omega)))
      have : 0 < k + S := by omega
      positivity
  have hN : ((S * (16 * (k + S) ^ 2) ^ S : ℕ) : ENNReal) ≤ 2 ^ (2 ^ k - k) := by
    exact_mod_cast count_le hk
  calc coins ℕ {v | ∃ s, s + 1 ≤ S ∧ ∃ P : Prog k (s + 1), P.Computes fun x => v (index k x)}
      ≤ coins ℕ (⋃ s ∈ Finset.range S, ⋃ P : Prog k (s + 1),
          {v | P.Computes fun x => v (index k x)}) := measure_mono hsub
    _ ≤ ∑ s ∈ Finset.range S, coins ℕ (⋃ P : Prog k (s + 1),
          {v | P.Computes fun x => v (index k x)}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ Finset.range S, ∑ P : Prog k (s + 1),
          coins ℕ {v | P.Computes fun x => v (index k x)} :=
        Finset.sum_le_sum fun s _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ s ∈ Finset.range S, ∑ _P : Prog k (s + 1), (2⁻¹ : ENNReal) ^ 2 ^ k :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun P _ => measure_computes_le P
    _ = ∑ s ∈ Finset.range S, (Fintype.card (Prog k (s + 1)) : ENNReal) * 2⁻¹ ^ 2 ^ k := by
        simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ ∑ _s ∈ Finset.range S, (((16 * (k + S) ^ 2) ^ S : ℕ) : ENNReal) * 2⁻¹ ^ 2 ^ k :=
        Finset.sum_le_sum fun s hs => by gcongr; exact_mod_cast hcard s hs
    _ = ((S * (16 * (k + S) ^ 2) ^ S : ℕ) : ENNReal) * 2⁻¹ ^ 2 ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        push_cast
        ring
    _ ≤ 2 ^ (2 ^ k - k) * 2⁻¹ ^ 2 ^ k := by gcongr
    _ = 2⁻¹ ^ k := by
        have hk' : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
        set N := 2 ^ k - k with hN
        rw [show 2 ^ k = N + k by omega, pow_add, ← mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- **For almost every fair-coin sequence `v` and all large `k`, no circuit with at most
`2ᵏ/(8k)` gates computes `x ↦ v(index x)`**: the probabilities `2⁻ᵏ` are summable. -/
theorem ae_eventually_no_small_circuit :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ k in atTop, ∀ s, s + 1 ≤ 2 ^ k / (8 * k) →
      ∀ P : Prog k (s + 1), ¬ P.Computes fun x => v (index k x) := by
  set E : ℕ → Set (ℕ → Bool) := fun i => {v | ∃ s, s + 1 ≤ 2 ^ (i + 5) / (8 * (i + 5)) ∧
    ∃ P : Prog (i + 5) (s + 1), P.Computes fun x => v (index (i + 5) x)} with hE
  have hsum : ∑' i, coins ℕ (E i) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' i : ℕ, (2⁻¹ : ENNReal) ^ i) ?_
      (ENNReal.tsum_le_tsum fun i => (measure_exists_small_circuit_le (by omega)).trans
        (pow_le_pow_right_of_le_one' (by norm_num) (by omega)))
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_eventually_notMem hsum] with v hv
  obtain ⟨I, hI⟩ := eventually_atTop.1 hv
  filter_upwards [eventually_ge_atTop (I + 5)] with k hk s hs P hP
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 5 := ⟨k - 5, by omega⟩
  exact hI i (by omega) ⟨s, hs, P, hP⟩

/-- **Circuit lower bounds for the center column of a random configuration**: for almost every
configuration and all large `k`, no circuit with at most `2ᵏ/(8k)` binary gates computes
`t ↦ c(t)` on the times `t < 2ᵏ` from the binary digits of `t`. -/
theorem ae_circuit_lower_bound_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ᶠ k in atTop, ∀ s, s + 1 ≤ 2 ^ k / (8 * k) →
      ∀ P : Prog k (s + 1), ¬ P.Computes fun y => trace x (index k y) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_eventually_no_small_circuit

end Rule30Equivalents.Circuits
