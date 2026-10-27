module

public import Rule30Equivalents.TFunction
public import Mathlib.Logic.Function.Iterate
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
# The cycles of an invertible T-function

A T-function `f` on the natural numbers is *invertible* in the sense of Klimov and Shamir when
bit `i` of `f x` is `x_i ⊕ ψ_i(x mod 2^i)`. Bit `i` of the argument enters bit `i` of the image
through `xor`, and the rest depends only on the lower bits. Klimov and Shamir, and Anashin for the
2-adic integers, determined the cycles of such maps modulo `2^n` one level at a time. This file
proves that description for every such `f`, and applies it to rule 30's `Φ`.

* `mod_eq`, `iterate_mod_eq`: `f` and its iterates are T-functions: bits below `n` of the image
  depend only on bits below `n` of the argument.
* `testBit_iterate`: bit `i` of `f^L(x)` is `x_i` plus `par f ψ i x L`, the parity of `ψ_i`
  along the first `L` points of the orbit of `x`, read modulo `2^i`.
* `lift_iff`, `iterate_two_mul_mod`: **lifting a cycle by one level.** If `f^L(x) ≡ x mod 2^i`,
  then `f^L(x) ≡ x mod 2^(i+1)` iff that parity is even, and `f^(2L)(x) ≡ x mod 2^(i+1)` always.
* `per f ψ x n`: the cycle length built level by level. It starts at `1` and doubles at level `i`
  exactly when the parity of `ψ_i` around the cycle modulo `2^i` is odd.
  `iterate_mod_iff_dvd`: `f^m(x) ≡ x mod 2^n` iff `per f ψ x n ∣ m`, so `per f ψ x n` is the cycle
  length of `x` modulo `2^n`. `per_eq_two_pow`: it is a power of two, at most `2^n`.
  `per_eq_two_pow_iff`: it equals `2^n` (the cycle of `x` contains every residue) iff the parity is
  odd at every level, which is Klimov and Shamir's single-cycle criterion.
* `diagonal_exact_death`, `eq_of_diagonal_eq`, `exists_diagonal_prefix`: **diagonal readouts.**
  - A seed is determined by its residue modulo `2^d` and its readout `t ↦ bit (t + d)` of `fᵗ(x)`.
  - Seeds that first differ at bit `d + m` have readouts that first differ at time `m`.
  - Every residue together with every readout prefix of length `m` is realized below `2^(d + m)`.
  - So on the 2-adic integers, `x ↦ (x mod 2^d, readout d)` is a bijection onto
    `ℤ/2^d × {0,1}^ℕ`. The Lean states its finite levels.
  - For the frozen-boundary steps, see `FrozenBoundaryPeriodTwo`.
* `Phi_bit`, `Phi_cycle`: for `Φ(x) = x ⊕ (2x ∨ 4x)`, `ψ_i(y) = y_{i-1} ∨ y_{i-2}`.
  `seed_rows_return_iff`: the first `j + 1` right diagonals of rule 30 return to their values at
  time `0` exactly at the multiples of `per Φ ψΦ 1 (j + 1)`.
* `per_unbounded`: for every `a ≠ 0` the cycle length of `a` modulo `2^n` is unbounded, because
  `Φ` raises the top bit of every nonzero number by two (`lt_Phi`). So every nonzero finite
  configuration, not only the seed, has an infinite cycle structure in the frame of its right
  edge.

None of this reaches the center column. It reads bit `t` of `Φ^t(1)`, and the cycle structure
describes each bit for all times, not the bit that moves with `t`.

Sources: A. Klimov, A. Shamir, *A new class of invertible mappings*, CHES 2002, LNCS 2523,
470–483, and *Cryptographic applications of T-functions*, SAC 2003, LNCS 3006; V. Anashin,
*Non-Archimedean analysis, T-functions, and cryptography*, arXiv:cs/0612038; V. Anashin,
A. Khrennikov, E. Yurova, *T-functions revisited: new criteria for bijectivity/transitivity*,
arXiv:1111.3093.
-/

@[expose] public section

namespace Rule30Equivalents.TFunctionCycles

open Rule30Equivalents.TFunction (Phi orbit low testBit_Phi low_congr orbit_one_eq_a)

/-- Two numbers agree modulo `2^n` iff their bits below `n` agree. -/
theorem mod_two_pow_eq_iff (a b n : ℕ) :
    a % 2 ^ n = b % 2 ^ n ↔ ∀ i, i < n → a.testBit i = b.testBit i := by
  constructor
  · intro h i hi
    have := congrArg (fun z => z.testBit i) h
    simpa [Nat.testBit_mod_two_pow, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · rw [h i hi]
    · simp [hi]

/-- Two numbers agree modulo `2^(i+1)` iff they agree modulo `2^i` and in bit `i`. -/
theorem mod_two_pow_succ_iff (a b i : ℕ) :
    a % 2 ^ (i + 1) = b % 2 ^ (i + 1) ↔ a % 2 ^ i = b % 2 ^ i ∧ a.testBit i = b.testBit i := by
  rw [mod_two_pow_eq_iff, mod_two_pow_eq_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h i (by omega)⟩
  · rintro ⟨h, hi⟩ k hk
    rcases Nat.lt_or_ge k i with hlt | hge
    · exact h k hlt
    · rw [show k = i by omega]; exact hi

/-- The parity of `ψ_i` along the first `L` points of the orbit of `x`, read modulo `2^i`. -/
def par (f : ℕ → ℕ) (ψ : ℕ → ℕ → Bool) (i x : ℕ) : ℕ → Bool
  | 0 => false
  | L + 1 => xor (par f ψ i x L) (ψ i (f^[L] x % 2 ^ i))

/-- The cycle length of `x` modulo `2^n`, built level by level: it doubles at level `i` exactly
when the parity of `ψ_i` around the cycle modulo `2^i` is odd. -/
def per (f : ℕ → ℕ) (ψ : ℕ → ℕ → Bool) (x : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => if par f ψ i x (per f ψ x i) then 2 * per f ψ x i else per f ψ x i

/-- Every cycle length is a power of two, at most `2^n`. -/
theorem per_eq_two_pow (f : ℕ → ℕ) (ψ : ℕ → ℕ → Bool) (x : ℕ) :
    ∀ n, ∃ k, k ≤ n ∧ per f ψ x n = 2 ^ k
  | 0 => ⟨0, Nat.le_refl 0, rfl⟩
  | n + 1 => by
    obtain ⟨k, hk, he⟩ := per_eq_two_pow f ψ x n
    show ∃ k, k ≤ n + 1 ∧
      (if par f ψ n x (per f ψ x n) then 2 * per f ψ x n else per f ψ x n) = 2 ^ k
    split
    · exact ⟨k + 1, by omega, by rw [he, Nat.pow_succ, Nat.mul_comm]⟩
    · exact ⟨k, by omega, he⟩

/-- **Single-cycle criterion.** The cycle length is `2^n` iff the parity is odd at every
level. -/
theorem per_eq_two_pow_iff (f : ℕ → ℕ) (ψ : ℕ → ℕ → Bool) (x : ℕ) :
    ∀ n, per f ψ x n = 2 ^ n ↔ ∀ i, i < n → par f ψ i x (per f ψ x i) = true
  | 0 => by simp [per]
  | n + 1 => by
    have ih := per_eq_two_pow_iff f ψ x n
    obtain ⟨k, hk, he⟩ := per_eq_two_pow f ψ x n
    have hle : per f ψ x n ≤ 2 ^ n := by rw [he]; exact Nat.pow_le_pow_right (by omega) hk
    have hlt : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    show (if par f ψ n x (per f ψ x n) then 2 * per f ψ x n else per f ψ x n) = 2 ^ (n + 1) ↔ _
    split
    · next hp =>
      constructor
      · intro h i hi
        have hn : per f ψ x n = 2 ^ n := by omega
        rcases Nat.lt_or_ge i n with hin | hin
        · exact ih.1 hn i hin
        · rw [show i = n by omega]; exact hp
      · intro h
        rw [ih.2 (fun i hi => h i (by omega)), hpow]
    · next hp =>
      constructor
      · intro h
        omega
      · intro h
        exact absurd (h n (by omega)) hp

section
variable {f : ℕ → ℕ} {ψ : ℕ → ℕ → Bool}
  (hf : ∀ i x, (f x).testBit i = xor (x.testBit i) (ψ i (x % 2 ^ i)))
include hf

/-- **`f` is a T-function**: the bits of `f x` below `n` depend only on those of `x`. -/
theorem mod_eq {n x y : ℕ} (h : x % 2 ^ n = y % 2 ^ n) : f x % 2 ^ n = f y % 2 ^ n := by
  rw [mod_two_pow_eq_iff] at h ⊢
  intro i hi
  have hm : x % 2 ^ i = y % 2 ^ i := (mod_two_pow_eq_iff _ _ _).2 fun k hk => h k (by omega)
  rw [hf, hf, h i hi, hm]

theorem iterate_mod_eq {n x y : ℕ} (h : x % 2 ^ n = y % 2 ^ n) :
    ∀ m, f^[m] x % 2 ^ n = f^[m] y % 2 ^ n
  | 0 => h
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact mod_eq hf (iterate_mod_eq h m)

/-- **Bit `i` of `f^L(x)` accumulates the parity of `ψ_i` along the orbit.** -/
theorem testBit_iterate (i x : ℕ) :
    ∀ L, (f^[L] x).testBit i = xor (x.testBit i) (par f ψ i x L)
  | 0 => by simp [par]
  | L + 1 => by
    rw [Function.iterate_succ_apply', hf, testBit_iterate i x L]
    simp only [par, Bool.xor_assoc]

/-- Repeating a cycle modulo `2^n` stays on it. -/
theorem iterate_mul_mod {n x L : ℕ} (hL : f^[L] x % 2 ^ n = x % 2 ^ n) :
    ∀ q, f^[L * q] x % 2 ^ n = x % 2 ^ n
  | 0 => by simp
  | q + 1 => by
    rw [Nat.mul_succ, Function.iterate_add_apply]
    exact (iterate_mod_eq hf hL (L * q)).trans (iterate_mul_mod hL q)

/-- Along a cycle modulo `2^i`, the parities of consecutive blocks add. -/
theorem par_add {i x L : ℕ} (hL : f^[L] x % 2 ^ i = x % 2 ^ i) :
    ∀ M, par f ψ i x (L + M) = xor (par f ψ i x L) (par f ψ i x M)
  | 0 => by simp [par]
  | M + 1 => by
    have e : f^[L + M] x % 2 ^ i = f^[M] x % 2 ^ i := by
      rw [show L + M = M + L by omega, Function.iterate_add_apply]
      exact iterate_mod_eq hf hL M
    show xor (par f ψ i x (L + M)) (ψ i (f^[L + M] x % 2 ^ i)) =
      xor (par f ψ i x L) (xor (par f ψ i x M) (ψ i (f^[M] x % 2 ^ i)))
    rw [par_add hL M, e, Bool.xor_assoc]

/-- Going `q` times around a cycle modulo `2^i` adds `q` times its parity. -/
theorem par_mul {i x L : ℕ} (hL : f^[L] x % 2 ^ i = x % 2 ^ i) :
    ∀ q, par f ψ i x (L * q) = (decide (q % 2 = 1) && par f ψ i x L)
  | 0 => by simp [par]
  | q + 1 => by
    rw [Nat.mul_succ, par_add hf (iterate_mul_mod hf hL q) L, par_mul hL q]
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have h' : (q + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (q + 1) % 2 = 0 := by omega
      simp [h, h']

/-- **Lifting a cycle by one level** (Klimov–Shamir). If `f^L(x) ≡ x mod 2^i`, then
`f^L(x) ≡ x mod 2^(i+1)` iff the parity of `ψ_i` along the cycle is even. -/
theorem lift_iff {i x L : ℕ} (hL : f^[L] x % 2 ^ i = x % 2 ^ i) :
    f^[L] x % 2 ^ (i + 1) = x % 2 ^ (i + 1) ↔ par f ψ i x L = false := by
  rw [mod_two_pow_succ_iff, testBit_iterate hf]
  constructor
  · rintro ⟨-, h⟩
    revert h
    cases x.testBit i <;> cases par f ψ i x L <;> simp
  · intro h
    exact ⟨hL, by rw [h, Bool.xor_false]⟩

/-- Twice around a cycle modulo `2^i` closes it modulo `2^(i+1)`. -/
theorem iterate_two_mul_mod {i x L : ℕ} (hL : f^[L] x % 2 ^ i = x % 2 ^ i) :
    f^[2 * L] x % 2 ^ (i + 1) = x % 2 ^ (i + 1) := by
  rw [show 2 * L = L * 2 by omega, lift_iff hf (iterate_mul_mod hf hL 2), par_mul hf hL 2]
  simp

/-- `per f ψ x n` steps close the cycle of `x` modulo `2^n`. -/
theorem iterate_per_mod (x : ℕ) : ∀ n, f^[per f ψ x n] x % 2 ^ n = x % 2 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    have ih := iterate_per_mod x n
    show f^[if par f ψ n x (per f ψ x n) then 2 * per f ψ x n else per f ψ x n] x % 2 ^ (n + 1) =
      x % 2 ^ (n + 1)
    split
    · exact iterate_two_mul_mod hf ih
    · next h => exact (lift_iff hf ih).2 (by simpa using h)

/-- **`per f ψ x n` is the cycle length of `x` modulo `2^n`**: `f^m(x) ≡ x mod 2^n` iff
`per f ψ x n ∣ m`. -/
theorem iterate_mod_iff_dvd (x : ℕ) :
    ∀ n m, f^[m] x % 2 ^ n = x % 2 ^ n ↔ per f ψ x n ∣ m := by
  intro n
  induction n with
  | zero => intro m; simp [per, Nat.mod_one]
  | succ n ih =>
    intro m
    constructor
    · intro h
      have hn : f^[m] x % 2 ^ n = x % 2 ^ n := ((mod_two_pow_succ_iff _ _ n).1 h).1
      obtain ⟨q, rfl⟩ := (ih m).1 hn
      have hbit := ((mod_two_pow_succ_iff _ _ n).1 h).2
      rw [testBit_iterate hf, par_mul hf (iterate_per_mod hf x n) q] at hbit
      show (if par f ψ n x (per f ψ x n) then 2 * per f ψ x n else per f ψ x n) ∣
        per f ψ x n * q
      split
      · next hp =>
        rw [hp, Bool.and_true] at hbit
        have hd : decide (q % 2 = 1) = false := by
          revert hbit
          cases x.testBit n <;> cases decide (q % 2 = 1) <;> simp
        have hq : q % 2 = 0 := by
          have := of_decide_eq_false hd
          omega
        obtain ⟨r, rfl⟩ : ∃ r, q = 2 * r := ⟨q / 2, by omega⟩
        exact ⟨r, by rw [Nat.mul_comm 2 (per f ψ x n), Nat.mul_assoc]⟩
      · exact Nat.dvd_mul_right _ _
    · rintro ⟨q, rfl⟩
      exact iterate_mul_mod hf (iterate_per_mod hf x (n + 1)) q

/-! ### Diagonal readouts -/

/-- The parity of `ψ_i` along the orbit depends only on the start modulo `2^i`. -/
theorem par_congr {i x y : ℕ} (h : x % 2 ^ i = y % 2 ^ i) : ∀ L, par f ψ i x L = par f ψ i y L
  | 0 => rfl
  | L + 1 => by
    simp only [par]
    rw [par_congr h L, iterate_mod_eq hf h L]

/-- **Exact death for diagonal readouts.** If `x, y` agree below bit `d + m` and differ at bit
`d + m`, their readouts `t ↦ bit (t + d)` of `fᵗ` agree before time `m` and differ at time `m`. -/
theorem diagonal_exact_death {x y d m : ℕ} (h : x % 2 ^ (d + m) = y % 2 ^ (d + m))
    (hne : x.testBit (d + m) ≠ y.testBit (d + m)) :
    (∀ t, t < m → (f^[t] x).testBit (t + d) = (f^[t] y).testBit (t + d)) ∧
      (f^[m] x).testBit (m + d) ≠ (f^[m] y).testBit (m + d) := by
  refine ⟨fun t ht => (mod_two_pow_eq_iff _ _ _).1 (iterate_mod_eq hf h t) (t + d) (by omega), ?_⟩
  rw [Nat.add_comm m d, testBit_iterate hf (d + m) x m, testBit_iterate hf (d + m) y m,
    par_congr hf h]
  intro heq
  apply hne
  revert heq
  cases x.testBit (d + m) <;> cases y.testBit (d + m) <;> cases par f ψ (d + m) y m <;> simp

/-- **A seed is determined by its residue modulo `2^d` and its diagonal readout `d`.** -/
theorem eq_of_diagonal_eq {x y d : ℕ} (hlow : x % 2 ^ d = y % 2 ^ d)
    (hr : ∀ t, (f^[t] x).testBit (t + d) = (f^[t] y).testBit (t + d)) : x = y := by
  have key : ∀ m, x % 2 ^ (d + m) = y % 2 ^ (d + m) := by
    intro m
    induction m with
    | zero => exact hlow
    | succ m ih =>
      rw [← Nat.add_assoc, mod_two_pow_succ_iff]
      exact ⟨ih, Classical.byContradiction fun hne => (diagonal_exact_death hf ih hne).2 (hr m)⟩
  apply Nat.eq_of_testBit_eq
  intro i
  exact (mod_two_pow_eq_iff _ _ _).1 (key (i + 1)) i (by omega)

/-- **Every readout prefix is realized**: for every residue `r < 2^d`, every target `w` and every
`m`, some `x < 2^(d + m)` with `x ≡ r mod 2^d` has readout `w` before time `m`. -/
theorem exists_diagonal_prefix {d r : ℕ} (hr : r < 2 ^ d) (w : ℕ → Bool) :
    ∀ m, ∃ x, x < 2 ^ (d + m) ∧ x % 2 ^ d = r ∧ ∀ t, t < m → (f^[t] x).testBit (t + d) = w t
  | 0 => ⟨r, hr, Nat.mod_eq_of_lt hr, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | m + 1 => by
    obtain ⟨x, hx, hxr, hxw⟩ := exists_diagonal_prefix hr w m
    have hpow : 2 ^ (d + (m + 1)) = 2 ^ (d + m) * 2 := by rw [← Nat.add_assoc, Nat.pow_succ]
    by_cases hm : (f^[m] x).testBit (m + d) = w m
    · refine ⟨x, by omega, hxr, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t m with h | h
      · exact hxw t h
      · rw [show t = m by omega]; exact hm
    · have hmod : (2 ^ (d + m) + x) % 2 ^ (d + m) = x % 2 ^ (d + m) := Nat.add_mod_left _ _
      have hbit : (2 ^ (d + m) + x).testBit (d + m) ≠ x.testBit (d + m) := by
        rw [Nat.testBit_two_pow_add_eq]
        cases x.testBit (d + m) <;> simp
      obtain ⟨h1, h2⟩ := diagonal_exact_death hf hmod hbit
      refine ⟨2 ^ (d + m) + x, by omega, ?_, fun t ht => ?_⟩
      · rw [Nat.add_comm (2 ^ (d + m)) x, Nat.pow_add, Nat.add_mul_mod_self_left]
        exact hxr
      · rcases Nat.lt_or_ge t m with h | h
        · rw [h1 t h]; exact hxw t h
        · rw [show t = m by omega]
          revert h2 hm
          cases (f^[m] (2 ^ (d + m) + x)).testBit (m + d) <;> cases (f^[m] x).testBit (m + d) <;>
            cases w m <;> simp

end

/-! ### Rule 30's `Φ` -/

/-- The bit function of `Φ`: `ψ_i(y) = y_{i-1} ∨ y_{i-2}`. -/
def ψΦ (i y : ℕ) : Bool := low y i

theorem Phi_bit (i x : ℕ) : (Phi x).testBit i = xor (x.testBit i) (ψΦ i (x % 2 ^ i)) := by
  rw [testBit_Phi, ψΦ, low_congr (x := x) (y := x % 2 ^ i) (j := i) (fun k hk => by
    rw [Nat.testBit_mod_two_pow]; simp [hk])]

/-- **The cycles of `Φ` modulo `2^n`.** `Φ^m(a) ≡ a mod 2^n` iff `per Φ ψΦ a n ∣ m`; the cycle
length is a power of two (`per_eq_two_pow`), doubling at the levels where the parity of
`a_{i-1} ∨ a_{i-2}` around the cycle is odd. -/
theorem Phi_cycle (a n m : ℕ) : Phi^[m] a % 2 ^ n = a % 2 ^ n ↔ per Phi ψΦ a n ∣ m :=
  iterate_mod_iff_dvd Phi_bit a n m

theorem orbit_eq_iterate (a : ℕ) : ∀ t, orbit a t = Phi^[t] a
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', ← orbit_eq_iterate a t]
    rfl

/-- **The right diagonals of the seed.** The first `j + 1` right diagonals of rule 30 (rows
`0, …, j` of `IntegerRows.diagArray`) are back at their values at time `0` exactly at the multiples
of `per Φ ψΦ 1 (j + 1)`. -/
theorem seed_rows_return_iff (j P : ℕ) :
    (∀ i, i ≤ j → IntegerRows.diagArray i P = IntegerRows.diagArray i 0) ↔
      per Phi ψΦ 1 (j + 1) ∣ P := by
  rw [← Phi_cycle, mod_two_pow_eq_iff]
  have e : ∀ t i, IntegerRows.diagArray i t = (Phi^[t] 1).testBit i := fun t i => by
    rw [IntegerRows.diagArray, ← orbit_one_eq_a, orbit_eq_iterate]
  simp only [e, Function.iterate_zero, id_eq]
  constructor
  · intro h i hi; exact h i (by omega)
  · intro h i hi; exact h i (by omega)

/-! ### Every nonzero orbit is infinite -/

/-- `Φ` moves every nonzero number up: its top bit rises by two. -/
theorem lt_Phi {x : ℕ} (hx : x ≠ 0) : x < Phi x := by
  have h1 : x < 2 ^ (x.log2 + 1) := Nat.lt_log2_self
  have hz : x.testBit (x.log2 + 2) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega)))
  have hb : (Phi x).testBit (x.log2 + 2) = true := by
    rw [testBit_Phi, hz]
    have hl : low x (x.log2 + 2) = true := by
      unfold low
      rw [show x.log2 + 2 - 2 = x.log2 by omega, Nat.testBit_log2 hx,
        decide_eq_true (show 2 ≤ x.log2 + 2 by omega)]
      simp
    rw [hl]
    rfl
  have h2 := Nat.ge_two_pow_of_testBit hb
  have h3 : 2 ^ (x.log2 + 1) ≤ 2 ^ (x.log2 + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem lt_iterate_Phi {x : ℕ} (hx : x ≠ 0) : ∀ t, 1 ≤ t → x < Phi^[t] x
  | 0, h => absurd h (by omega)
  | t + 1, _ => by
    rw [Function.iterate_succ_apply']
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      exact lt_Phi hx
    · exact Nat.lt_trans (lt_iterate_Phi hx t hpos) (lt_Phi (by have := lt_iterate_Phi hx t hpos; omega))

/-- **Every nonzero orbit of `Φ` is 2-adically infinite**: for `a ≠ 0` the cycle length of `a`
modulo `2^n` is unbounded in `n`. In the frame of its right edge, every nonzero finite
configuration (`TFunction.row a`) has an infinite cycle structure, as the seed `a = 1` does. -/
theorem per_unbounded {a : ℕ} (ha : a ≠ 0) (K : ℕ) : ∃ n, K < per Phi ψΦ a n := by
  refine Classical.byContradiction fun hcon => ?_
  have hle : ∀ n, per Phi ψΦ a n ≤ K := fun n => Nat.le_of_not_lt fun h => hcon ⟨n, h⟩
  -- every cycle length is a power of two at most `K`, so it divides `2^K`
  have hdvd : ∀ n, per Phi ψΦ a n ∣ 2 ^ K := by
    intro n
    obtain ⟨k, -, he⟩ := per_eq_two_pow Phi ψΦ a n
    have hk := hle n
    rw [he] at hk ⊢
    have : k < 2 ^ k := Nat.lt_two_pow_self
    exact Nat.pow_dvd_pow 2 (by omega)
  -- so `Φ^(2^K)` fixes `a` modulo every `2^n`, hence fixes `a`, but it moves `a` up
  have hmod : ∀ n, Phi^[2 ^ K] a % 2 ^ n = a % 2 ^ n :=
    fun n => (Phi_cycle a n (2 ^ K)).2 (hdvd n)
  have hlt := lt_iterate_Phi ha (2 ^ K) Nat.one_le_two_pow
  have h := hmod (Phi^[2 ^ K] a)
  rw [Nat.mod_eq_of_lt Nat.lt_two_pow_self,
    Nat.mod_eq_of_lt (Nat.lt_trans hlt Nat.lt_two_pow_self)] at h
  omega

end Rule30Equivalents.TFunctionCycles
