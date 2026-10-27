module

public import Rule30Equivalents.LinearRelations
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Periodic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Periods that are prime powers: the p-adic and Mahler forms

The statement that the center column has no eventual period `2^k` follows from Problem 1 and
includes periods `2` and `4`, so it is open. Two equivalent forms of it are proved here, for every
bit sequence and every prime `p` in place of `2`.

* **p-adic continuity** (`exists_continuous_extension_iff`): `u : ℕ → Bool` has a period `p^k` iff
  it extends to a continuous function `ℤ_p → Bool`. On the compact `ℤ_p` such a function is
  constant on all balls of some radius `δ` (Lebesgue's number lemma), so it reads only `α mod p^k`
  once `p^-k < δ`. Conversely `α ↦ u (α mod p^k)` is locally constant.
* **Mahler coefficients over `𝔽_p`** (`exists_fwdDiff_eq_zero_iff`): `u : ℕ → 𝔽_p` has a period
  `p^k` iff its forward differences `Δⁿu(0) = ∑_{j ≤ n} (-1)^(n-j) C(n, j) u(j)`, its Mahler
  coefficients, vanish for all large `n`. In characteristic `p` the binomial coefficients `C(p, j)`
  with `0 < j < p` vanish, so `Δ^(p^k) u (t) = u (t + p^k) - u t` (`fwdDiff_iter_prime_pow`), and
  Newton's forward formula (Mathlib's `shift_eq_sum_fwdDiff_iter`) writes `Δ^(p^k) u (t)` through
  the coefficients `Δ^(j + p^k) u (0)`. For `p = 2` the signs disappear: `fwdDiff_iter_zero`.

For the center column (`noPrimePowPeriod_iff_not_continuous`, `noPrimePowPeriod_iff_fwdDiff`, and
for `p = 2` `noTwoPowPeriod_iff_not_continuous`, `noTwoPowPeriod_iff_fwdDiff`): `c` has no eventual
period `p^k` iff no tail of `c` extends continuously to `ℤ_p`, iff the `𝔽_p` Mahler coefficients of
every tail are not eventually `0`.
-/

@[expose] public section

namespace Rule30Equivalents.TwoAdicPeriods

open Ruliology.CellularAutomata LinearRelations
open scoped fwdDiff

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### p-adic continuity -/

/-- A continuous function on `ℤ_p` with values in `Bool` restricts to a sequence with a period
`p^k`. -/
theorem exists_period_of_continuous {u : ℕ → Bool} {F : ℤ_[p] → Bool} (hF : Continuous F)
    (hFu : ∀ n : ℕ, F n = u n) : ∃ k, ∀ t, u (t + p ^ k) = u t := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun b : Bool => F ⁻¹' {b}) isCompact_univ
    (fun b => hF.isOpen_preimage _ (isOpen_discrete _))
    (fun α _ => Set.mem_iUnion.2 ⟨F α, rfl⟩)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (show (1 / p : ℝ) < 1 by
    rw [div_lt_one (by linarith)]; exact hp1)
  refine ⟨k, fun t => ?_⟩
  obtain ⟨b, hb⟩ := hball (t : ℤ_[p]) (Set.mem_univ _)
  have h1 : (t : ℤ_[p]) ∈ Metric.ball (t : ℤ_[p]) δ := Metric.mem_ball_self hδ
  have h2 : ((t + p ^ k : ℕ) : ℤ_[p]) ∈ Metric.ball (t : ℤ_[p]) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have e : ((t + p ^ k : ℕ) : ℤ_[p]) - (t : ℤ_[p]) = (p : ℤ_[p]) ^ k := by
      push_cast
      ring
    rw [e, PadicInt.norm_p_pow]
    calc (p : ℝ) ^ (-(k : ℤ)) = (1 / p : ℝ) ^ k := by
          rw [zpow_neg, zpow_natCast, one_div, inv_pow]
      _ < δ := hk
  have e1 := hb h1
  have e2 := hb h2
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at e1 e2
  rw [← hFu, ← hFu, e1, e2]

/-- A sequence with period `p^k` extends to the locally constant `α ↦ u (α mod p^k)` on `ℤ_p`. -/
theorem exists_continuous_of_period {u : ℕ → Bool} {k : ℕ} (hk : ∀ t, u (t + p ^ k) = u t) :
    ∃ F : ℤ_[p] → Bool, Continuous F ∧ ∀ n : ℕ, F n = u n := by
  refine ⟨fun α => u (PadicInt.toZModPow k α).val, IsLocallyConstant.continuous ?_, fun n => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro α
    filter_upwards [Metric.closedBall_mem_nhds α
      (zpow_pos (by exact_mod_cast hp.out.pos : (0 : ℝ) < p) (-(k : ℤ)))] with β hβ
    have hmem : β - α ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [Metric.mem_closedBall, dist_eq_norm] at hβ
      exact_mod_cast hβ
    have h0 : PadicInt.toZModPow k (β - α) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact_mod_cast hmem
    rw [map_sub, sub_eq_zero] at h0
    simp only [h0]
  · show u (PadicInt.toZModPow k (n : ℤ_[p])).val = u n
    rw [map_natCast, ZMod.val_natCast]
    exact Function.Periodic.map_mod_nat (f := u) hk n

/-- **p-adic form.** A bit sequence has a period that is a power of `p` iff it extends to a
continuous function on the `p`-adic integers. -/
theorem exists_continuous_extension_iff (u : ℕ → Bool) :
    (∃ F : ℤ_[p] → Bool, Continuous F ∧ ∀ n : ℕ, F n = u n) ↔ ∃ k, ∀ t, u (t + p ^ k) = u t :=
  ⟨fun ⟨_, hF, hFu⟩ => exists_period_of_continuous hF hFu,
    fun ⟨_, hk⟩ => exists_continuous_of_period hk⟩

/-! ### Mahler coefficients over `𝔽_p` -/

/-- In characteristic `p`, the `p`-th forward difference with step `h` is the difference at
distance `p h`: the binomial coefficients `C(p, j)`, `0 < j < p`, vanish. -/
theorem fwdDiff_iter_prime (h : ℕ) (f : ℕ → ZMod p) (y : ℕ) :
    Δ_[h]^[p] f y = f (y + p * h) - f y := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_eq_add p 0 hp.out.ne_zero (fun j hj hj' => ?_)
    (fun h' => absurd (Finset.self_mem_range_succ p) h')
    (fun h' => absurd (Finset.mem_range.2 (Nat.succ_pos p)) h')]
  · rw [Nat.sub_self, Nat.choose_self, Nat.sub_zero, Nat.choose_zero_right, zsmul_eq_mul,
      zsmul_eq_mul, smul_eq_mul, smul_eq_mul, zero_mul, add_zero]
    push_cast
    rw [neg_one_pow_char (ZMod p) p]
    ring
  · rw [Finset.mem_range] at hj
    have hdvd : ((p.choose j : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (Nat.Prime.dvd_choose_self hp.out hj'.2 (by omega))
    rw [zsmul_eq_mul]
    push_cast
    rw [hdvd, mul_zero, zero_mul]

/-- In characteristic `p`, the `p^k`-th forward difference is the difference at distance `p^k`. -/
theorem fwdDiff_iter_prime_pow (k : ℕ) :
    ∀ (u : ℕ → ZMod p) (t : ℕ), Δ_[1]^[p ^ k] u t = u (t + p ^ k) - u t := by
  induction k with
  | zero => intro u t; simp [fwdDiff]
  | succ k ih =>
    intro u t
    have hfun : (fwdDiff (1 : ℕ) : (ℕ → ZMod p) → ℕ → ZMod p)^[p ^ k] = fwdDiff (p ^ k) :=
      funext fun u => funext fun t => by rw [ih]; rfl
    rw [pow_succ, Function.iterate_mul, hfun, fwdDiff_iter_prime, mul_comm]

/-- **Mahler form.** A sequence in `𝔽_p` has a period that is a power of `p` iff its Mahler
coefficients `Δⁿu(0)` vanish for all large `n`. -/
theorem exists_fwdDiff_eq_zero_iff (u : ℕ → ZMod p) :
    (∃ N, ∀ n, N ≤ n → Δ_[1]^[n] u 0 = 0) ↔ ∃ k, ∀ t, u (t + p ^ k) = u t := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun t => ?_⟩
    have hN2 : N ≤ p ^ N := (Nat.lt_pow_self hp.out.one_lt).le
    rw [← sub_eq_zero, ← fwdDiff_iter_prime_pow]
    have hnewton := shift_eq_sum_fwdDiff_iter 1 (Δ_[1]^[p ^ N] u) t 0
    rw [smul_eq_mul, mul_one, zero_add] at hnewton
    rw [hnewton]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Function.iterate_add_apply, hN _ (by omega), smul_zero]
  · rintro ⟨k, hk⟩
    refine ⟨p ^ k, fun n hn => ?_⟩
    have h0 : Δ_[1]^[p ^ k] u = 0 := funext fun t => by
      rw [fwdDiff_iter_prime_pow, hk, sub_self, Pi.zero_apply]
    have hfix : fwdDiff 1 (0 : ℕ → ZMod p) = 0 := funext fun _ => sub_self _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + p ^ k := ⟨n - p ^ k, by omega⟩
    rw [Function.iterate_add_apply, h0, Function.iterate_fixed hfix, Pi.zero_apply]

/-- Over `𝔽₂` the signs disappear: the `n`-th Mahler coefficient is `∑_{j ≤ n} C(n, j) u(j)`. -/
theorem fwdDiff_iter_zero (u : ℕ → ZMod 2) (n : ℕ) :
    Δ_[1]^[n] u 0 = ∑ j ∈ Finset.range (n + 1), (n.choose j : ZMod 2) * u j := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zero_add, smul_eq_mul, mul_one, zsmul_eq_mul]
  push_cast
  rw [show (-1 : ZMod 2) = 1 by decide, one_pow, one_mul]

/-! ### The center column -/

variable (p) in
/-- `c` has no eventual period that is a power of `p`. Problem 1 implies it; for `p = 2` it
includes the periods `2` and `4`, so it is open. -/
def NoPrimePowPeriod : Prop := ∀ T k : ℕ, ¬ ∀ t, T ≤ t → c (t + p ^ k) = c t

/-- No eventual period `2^k`. -/
abbrev NoTwoPowPeriod : Prop := NoPrimePowPeriod 2

theorem noPrimePowPeriod_of_problem1 (h : Rule30Prize.Problem1) : NoPrimePowPeriod p :=
  fun T k hk => h ⟨T, p ^ k, pow_pos hp.out.pos k, hk⟩

omit hp in
/-- A period `p^k` of the tail from `T` is an eventual period from `T`. -/
theorem tail_period_iff (T k : ℕ) :
    (∀ t, c (T + (t + p ^ k)) = c (T + t)) ↔ ∀ t, T ≤ t → c (t + p ^ k) = c t := by
  constructor
  · intro h t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = T + s := ⟨t - T, by omega⟩
    rw [add_assoc]
    exact h s
  · intro h s
    rw [← add_assoc]
    exact h (T + s) (by omega)

variable (p) in
/-- **No eventual period `p^k`, p-adic form**: no tail of `c` extends continuously to `ℤ_p`. -/
theorem noPrimePowPeriod_iff_not_continuous : NoPrimePowPeriod p ↔
    ∀ T, ¬ ∃ F : ℤ_[p] → Bool, Continuous F ∧ ∀ n : ℕ, F n = c (T + n) := by
  refine forall_congr' fun T => ?_
  rw [exists_continuous_extension_iff (fun n => c (T + n)), not_exists]
  exact forall_congr' fun k => not_congr (tail_period_iff T k).symm

variable (p) in
/-- **No eventual period `p^k`, Mahler form**: for every tail of `c`, read in `𝔽_p`, the Mahler
coefficients are not eventually `0`. -/
theorem noPrimePowPeriod_iff_fwdDiff : NoPrimePowPeriod p ↔
    ∀ T N, ∃ n, N ≤ n ∧ Δ_[1]^[n] (fun t => toK (ZMod p) c (T + t)) 0 ≠ 0 := by
  refine forall_congr' fun T => ?_
  have h := exists_fwdDiff_eq_zero_iff (fun t => toK (ZMod p) c (T + t))
  simp only [toK_eq_toK_iff] at h
  have h' : (∀ N, ∃ n, N ≤ n ∧ Δ_[1]^[n] (fun t => toK (ZMod p) c (T + t)) 0 ≠ 0) ↔
      ¬ ∃ N, ∀ n, N ≤ n → Δ_[1]^[n] (fun t => toK (ZMod p) c (T + t)) 0 = 0 :=
    ⟨fun H ⟨N, hN⟩ => by
      obtain ⟨n, hn, hne⟩ := H N
      exact hne (hN n hn),
     fun H N => by
      by_contra hc
      push Not at hc
      exact H ⟨N, hc⟩⟩
  rw [h', h, not_exists]
  exact forall_congr' fun k => not_congr (tail_period_iff T k).symm

/-- **No eventual period `2^k`, 2-adic form**: no tail of `c` extends continuously to `ℤ₂`. -/
theorem noTwoPowPeriod_iff_not_continuous : NoTwoPowPeriod ↔
    ∀ T, ¬ ∃ F : ℤ_[2] → Bool, Continuous F ∧ ∀ n : ℕ, F n = c (T + n) :=
  noPrimePowPeriod_iff_not_continuous 2

/-- **No eventual period `2^k`, Mahler form**: for every tail of `c`, read in `𝔽₂`, the Mahler
coefficients `Δⁿ(0) = ∑_{j ≤ n} C(n, j) c(T + j)` are not eventually `0`. -/
theorem noTwoPowPeriod_iff_fwdDiff : NoTwoPowPeriod ↔
    ∀ T N, ∃ n, N ≤ n ∧ Δ_[1]^[n] (fun t => toK (ZMod 2) c (T + t)) 0 ≠ 0 :=
  noPrimePowPeriod_iff_fwdDiff 2

end Rule30Equivalents.TwoAdicPeriods
