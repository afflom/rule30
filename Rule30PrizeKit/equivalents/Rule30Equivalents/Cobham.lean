module

public import Rule30Equivalents.Automatic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Zify

/-!
# Cobham's theorem

**Cobham's theorem** (1969): if `a, b ≥ 2` are multiplicatively independent
(`aᵐ ≠ bⁿ` for all `m, n ≥ 1`), a sequence that is both `a`-automatic and `b`-automatic is
eventually periodic. So Problem 1 holds iff the center column is not both 2-automatic and
3-automatic, iff it is not `k`-automatic for some `k ≥ 2`.

The proof follows T. J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), with
automaticity as finiteness of the `k`-kernel (`Automatic.IsAutomatic`).
* `sig c f x`: the values of the `c`-kernel at `x`, `x + 1` and `x + 2`. It takes finitely many
  values, and equal signatures give `f(x cⁿ + z) = f(y cⁿ + z)` for every `z ≤ 2cⁿ`
  (`eq_of_sig_eq`). This replaces the automata over the digits `0, …, 2c` of Krebs' Lemma 5.
* `exists_close_powers` (Krebs' Lemma 6, Dirichlet): `M |aᵐ − bⁿ| < bⁿ` for some `m, n ≥ 1`, by
  pigeonhole on `⌊M aˣ / b^{⌊log_b aˣ⌋}⌋`.
* `LocPer.glue` (Lemma 7): local periods on two intervals that overlap in at least `p + q` places
  combine.
* `locPer_of_pair`: let `u ≠ v` have the same `b`-signature `s` and the same `a`-signature, and
  `p = (u − v)(aᵐ − bⁿ) > 0`. Then `f` has local period `p` around `x bⁿ + bⁿ` for every `x` with
  signature `s`, by `x bⁿ + z ~ v bⁿ + z = v aᵐ + z' ~ u aᵐ + z' = u bⁿ + z + p ~ x bⁿ + z + p`.
* `eventuallyPeriodic_of_isAutomatic`: every large `x` has a signature shared by infinitely many
  numbers. These local periods are at most `bⁿ / 6` on intervals of radius `2bⁿ/3` around
  consecutive multiples of `bⁿ`, so they glue into one period.
* `problem1_iff_not_two_three_automatic`, `problem1_iff_exists_not_automatic`.

Sources: A. Cobham, *On the base-dependence of sets of numbers recognizable by finite automata*,
Math. Systems Theory 3 (1969) 186–192; T. J. P. Krebs, arXiv:1801.06704 (2018).
-/

@[expose] public section

namespace Rule30Equivalents.Cobham

open Ruliology.CellularAutomata Automatic

/-! ### Signatures -/

/-- The signature of `x` in base `c`: the values of the `c`-kernel at `x`, `x + 1` and `x + 2`. -/
def sig (c : ℕ) (f : ℕ → Bool) (x : ℕ) : kernel c f → Fin 3 → Bool :=
  fun g j => (g : ℕ → Bool) (x + j)

/-- Numbers with the same signature behave alike after any `n` digits `≤ 2cⁿ`. -/
theorem eq_of_sig_eq {c : ℕ} (hc : 0 < c) {f : ℕ → Bool} {x y : ℕ} (h : sig c f x = sig c f y)
    (n z : ℕ) (hz : z ≤ 2 * c ^ n) : f (x * c ^ n + z) = f (y * c ^ n + z) := by
  have hpos : 0 < c ^ n := pow_pos hc n
  have hj : z / c ^ n < 3 := (Nat.div_lt_iff_lt_mul hpos).2 (by omega)
  have hr : z % c ^ n < c ^ n := Nat.mod_lt _ hpos
  have hg : (fun t => f (c ^ n * t + z % c ^ n)) ∈ kernel c f := ⟨n, _, hr, rfl⟩
  have h1 := congrFun (congrFun h ⟨_, hg⟩) ⟨_, hj⟩
  simp only [sig] at h1
  have hz' := Nat.div_add_mod z (c ^ n)
  have ex : x * c ^ n + z = c ^ n * (x + z / c ^ n) + z % c ^ n := by
    conv_lhs => rw [← hz']
    ring
  have ey : y * c ^ n + z = c ^ n * (y + z / c ^ n) + z % c ^ n := by
    conv_lhs => rw [← hz']
    ring
  rw [ex, ey]
  exact h1

/-! ### Close powers -/

/-- **Close powers** (Krebs, Lemma 6): for bases `a, b ≥ 2` and `M ≥ 1` there are `m, n ≥ 1` with
`M |aᵐ − bⁿ| < bⁿ`. -/
theorem exists_close_powers {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) {M : ℕ} (hM : 0 < M) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (M : ℤ) * |(a : ℤ) ^ m - (b : ℤ) ^ n| < (b : ℤ) ^ n := by
  set e : ℕ → ℕ := fun x => Nat.log b (a ^ x)
  have he1 : ∀ x, b ^ e x ≤ a ^ x := fun x => Nat.pow_log_le_self b (pow_ne_zero _ (by omega))
  have he2 : ∀ x, a ^ x < b ^ (e x + 1) := fun x => Nat.lt_pow_succ_log_self (by omega) _
  have hbe : ∀ x, 0 < b ^ e x := fun x => pow_pos (by omega) _
  set β : ℕ → ℕ := fun x => M * a ^ x / b ^ e x
  have hβ : ∀ x, β x < b * M := fun x => by
    refine (Nat.div_lt_iff_lt_mul (hbe x)).2 ?_
    have := he2 x
    rw [pow_succ] at this
    nlinarith
  obtain ⟨x, hx, y, hy, hxy, hβxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (b * M + 1)) (t := Finset.range (b * M)) (by simp)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_range.2 (hβ x)))
  -- the bucket of `x`: `q b^{e x} ≤ M aˣ < (q + 1) b^{e x}`
  have hbucket : ∀ x, β x * b ^ e x ≤ M * a ^ x ∧ M * a ^ x < (β x + 1) * b ^ e x := fun x => by
    have h1 := Nat.div_add_mod (M * a ^ x) (b ^ e x)
    have h2 := Nat.mod_lt (M * a ^ x) (hbe x)
    show M * a ^ x / b ^ e x * b ^ e x ≤ M * a ^ x ∧ M * a ^ x < (M * a ^ x / b ^ e x + 1) * b ^ e x
    exact ⟨Nat.div_mul_le_self _ _, by nlinarith⟩
  have hβM : ∀ x, M ≤ β x := fun x => (Nat.le_div_iff_mul_le (hbe x)).2 (by nlinarith [he1 x])
  -- order the pair
  wlog hlt : x < y generalizing x y
  · exact this y hy x hx hxy.symm hβxy.symm (by omega)
  have hpow : a ^ y = a ^ x * a ^ (y - x) := by rw [← pow_add]; congr 1; omega
  have hay : 2 * a ^ x ≤ a ^ y := by
    rw [hpow]
    have : 2 ≤ a ^ (y - x) := le_trans ha (Nat.le_self_pow (by omega) a)
    nlinarith [Nat.one_le_pow x a (by omega)]
  -- the exponents are ordered too
  have hexy : e x < e y := by
    by_contra hle
    have hle : b ^ e y ≤ b ^ e x := Nat.pow_le_pow_right (by omega) (not_lt.1 hle)
    have h1 := (hbucket x).1
    have h2 := (hbucket y).2
    rw [← hβxy] at h2
    have hq := hβM x
    have i1 : M * (2 * a ^ x) ≤ M * a ^ y := Nat.mul_le_mul_left _ hay
    have i2 : (β x + 1) * b ^ e y ≤ (β x + 1) * b ^ e x := Nat.mul_le_mul_left _ hle
    have i3 : 1 * b ^ e x ≤ β x * b ^ e x := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  refine ⟨y - x, e y - e x, by omega, by omega, ?_⟩
  obtain ⟨h1, h2⟩ := hbucket x
  obtain ⟨h3, h4⟩ := hbucket y
  rw [← hβxy] at h3 h4
  have hBy : b ^ e y = b ^ e x * b ^ (e y - e x) := by rw [← pow_add]; congr 1; omega
  rw [hBy, hpow] at h3 h4
  have hax : 0 < a ^ x := pow_pos (by omega) _
  have hN : 0 < b ^ (e y - e x) := pow_pos (by omega) _
  have h1' := Nat.mul_le_mul_right (b ^ (e y - e x)) h1
  have h2' := Nat.mul_lt_mul_of_pos_right h2 hN
  have hBx := Nat.mul_le_mul_right (b ^ (e y - e x)) (he1 x)
  zify at h1' h2' h3 h4 hBx hax
  have k1 : (M : ℤ) * (a : ℤ) ^ x * ((a : ℤ) ^ (y - x) - (b : ℤ) ^ (e y - e x)) <
      (b : ℤ) ^ e x * (b : ℤ) ^ (e y - e x) := by nlinarith
  have k2 : (M : ℤ) * (a : ℤ) ^ x * ((b : ℤ) ^ (e y - e x) - (a : ℤ) ^ (y - x)) <
      (b : ℤ) ^ e x * (b : ℤ) ^ (e y - e x) := by nlinarith
  have k3 : (a : ℤ) ^ x * ((M : ℤ) * |(a : ℤ) ^ (y - x) - (b : ℤ) ^ (e y - e x)|) <
      (a : ℤ) ^ x * (b : ℤ) ^ (e y - e x) := by
    rcases abs_cases ((a : ℤ) ^ (y - x) - (b : ℤ) ^ (e y - e x)) with ⟨habs, _⟩ | ⟨habs, _⟩ <;>
      rw [habs] <;> nlinarith
  exact lt_of_mul_lt_mul_left k3 hax.le

/-! ### Local periods -/

/-- `f` has local period `p` on `[l, r]`. -/
def LocPer (f : ℕ → Bool) (p l r : ℕ) : Prop := ∀ w, l ≤ w → w + p ≤ r → f (w + p) = f w

theorem LocPer.eq_of_modEq {f : ℕ → Bool} {q l r : ℕ} (h : LocPer f q l r) {u v : ℕ} (hu : l ≤ u)
    (hv : v ≤ r) (huv : u ≤ v) (hmod : u % q = v % q) : f u = f v := by
  obtain ⟨k, hk⟩ : q ∣ v - u := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
  have hv' : v = u + q * k := by omega
  subst hv'
  have key : ∀ k, u + q * k ≤ r → f u = f (u + q * k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk'
      rw [ih (by nlinarith)]
      have := h (u + q * k) (by omega) (by nlinarith)
      rw [← this]
      congr 1
      ring
  exact key k hv

/-- **Gluing local periods** (Krebs, Lemma 7). -/
theorem LocPer.glue {f : ℕ → Bool} {p q l₁ r₁ l₂ r₂ : ℕ} (h₁ : LocPer f p l₁ r₁)
    (h₂ : LocPer f q l₂ r₂) (hl : l₁ ≤ l₂) (hov : l₂ + p + q ≤ r₁ + 1)
    (hq : 0 < q) : LocPer f p l₁ r₂ := by
  intro w hw hwr
  by_cases hw1 : w + p ≤ r₁
  · exact h₁ w hw hw1
  · have hwl : l₂ ≤ w := by omega
    set y := l₂ + (w - l₂) % q
    have hyq : (w - l₂) % q < q := Nat.mod_lt _ hq
    have hyw : y ≤ w := by have := Nat.mod_le (w - l₂) q; omega
    have hmod : y % q = w % q := by
      have : w = l₂ + (w - l₂) := by omega
      conv_rhs => rw [this]
      simp only [y, Nat.add_mod, Nat.mod_mod]
    have hmodp : (y + p) % q = (w + p) % q := by rw [Nat.add_mod, hmod, ← Nat.add_mod]
    rw [← h₂.eq_of_modEq (by omega) hwr (by omega) hmodp, h₁ y (by omega) (by omega),
      h₂.eq_of_modEq (by omega) (by omega) hyw hmod]

/-- **One local period** (the heart of Krebs' proof). -/
theorem locPer_of_pair {a b : ℕ} {f : ℕ → Bool} (ha : 0 < a) (hb : 0 < b) {m n x u v p ξ : ℕ}
    (hxu : sig b f x = sig b f u) (hxv : sig b f x = sig b f v) (huv : sig a f u = sig a f v)
    (hvξ : v < ξ) (hp : ((u : ℤ) - v) * ((a : ℤ) ^ m - (b : ℤ) ^ n) = p)
    (hclose : 6 * (ξ : ℤ) * |(a : ℤ) ^ m - (b : ℤ) ^ n| < (b : ℤ) ^ n) :
    LocPer f p (x * b ^ n + b ^ n - 2 * b ^ n / 3) (x * b ^ n + b ^ n + 2 * b ^ n / 3) := by
  intro w hw hwp
  set N := b ^ n
  set A := a ^ m
  set R := 2 * N / 3
  have hR : 3 * R ≤ 2 * N := Nat.mul_div_le (2 * N) 3
  obtain ⟨z, rfl⟩ : ∃ z, w = x * N + z := ⟨w - x * N, by omega⟩
  have hz1 : N ≤ z + R := by omega
  have hz2 : z + p ≤ N + R := by omega
  have hAc : ((A : ℕ) : ℤ) = (a : ℤ) ^ m := by push_cast [A]; rfl
  have hNc : ((N : ℕ) : ℤ) = (b : ℤ) ^ n := by push_cast [N]; rfl
  set d : ℤ := (A : ℤ) - N with hd
  set D : ℤ := |d|
  have hdD : d ≤ D := le_abs_self d
  have hdD' : -d ≤ D := neg_le_abs d
  have hD : 0 ≤ D := abs_nonneg d
  have hclose' : 6 * (ξ : ℤ) * D < N := by
    rw [hNc]
    simpa [D, hd, hAc, hNc] using hclose
  have hvD : (v : ℤ) * d ≤ v * D := mul_le_mul_of_nonneg_left hdD (by positivity)
  have hvD' : -((v : ℤ) * d) ≤ v * D := by nlinarith
  have hvξD : ((v : ℤ) + 1) * D ≤ ξ * D := mul_le_mul_of_nonneg_right (by exact_mod_cast hvξ) hD
  have hz' : (0 : ℤ) ≤ z - v * d := by
    have : (6 : ℤ) * R ≤ 4 * N := by exact_mod_cast (by omega : 6 * R ≤ 4 * N)
    nlinarith
  obtain ⟨z', hz'eq⟩ : ∃ z' : ℕ, (z' : ℤ) = z - v * d := ⟨_, Int.toNat_of_nonneg hz'⟩
  have hz'le : z' ≤ 2 * A := by
    have : (6 : ℤ) * R ≤ 4 * N := by exact_mod_cast (by omega : 6 * R ≤ 4 * N)
    have hA : (5 : ℤ) * N < 6 * A := by nlinarith
    zify
    nlinarith
  have e1 : v * N + z = v * A + z' := by
    zify
    rw [hz'eq]
    ring
  have e2 : u * A + z' = u * N + (z + p) := by
    zify
    rw [hz'eq, ← hp, ← hAc, ← hNc]
    ring
  calc f (x * N + z + p) = f (x * N + (z + p)) := by rw [add_assoc]
    _ = f (u * N + (z + p)) := eq_of_sig_eq hb hxu n (z + p) (by omega)
    _ = f (u * A + z') := by rw [e2]
    _ = f (v * A + z') := eq_of_sig_eq ha huv m z' hz'le
    _ = f (v * N + z) := by rw [e1]
    _ = f (x * N + z) := (eq_of_sig_eq hb hxv n z (by omega)).symm

/-! ### Cobham's theorem -/

/-- **Cobham's theorem**: a sequence that is `a`-automatic and `b`-automatic for multiplicatively
independent `a, b ≥ 2` is eventually periodic. -/
theorem eventuallyPeriodic_of_isAutomatic {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ m n, 0 < m → 0 < n → a ^ m ≠ b ^ n) {f : ℕ → Bool} (hfa : IsAutomatic a f)
    (hfb : IsAutomatic b f) : EventuallyPeriodic f := by
  classical
  have : Finite (kernel a f) := hfa.to_subtype
  have : Finite (kernel b f) := hfb.to_subtype
  have : Fintype (kernel b f → Fin 3 → Bool) := Fintype.ofFinite _
  -- for each `b`-signature shared by infinitely many numbers, two of them with one `a`-signature
  have hpair : ∀ s : kernel b f → Fin 3 → Bool, {x | sig b f x = s}.Infinite →
      ∃ xy : ℕ × ℕ, xy.1 ≠ xy.2 ∧ sig b f xy.1 = s ∧ sig b f xy.2 = s ∧
        sig a f xy.1 = sig a f xy.2 := by
    intro s hs
    obtain ⟨x, hx, y, hy, hxy, he⟩ := hs.exists_ne_map_eq_of_mapsTo (f := sig a f)
      (Set.mapsTo_univ _ _) Set.finite_univ
    exact ⟨(x, y), hxy, hx, hy, he⟩
  choose! P hPne hP1 hP2 hPa using hpair
  -- the signatures shared by finitely many numbers are all used below `x₀`
  have hbd : ∀ s : kernel b f → Fin 3 → Bool, ∃ B, ¬ {x | sig b f x = s}.Infinite →
      ∀ x, sig b f x = s → x < B := fun s => by
    by_cases hs : {x | sig b f x = s}.Infinite
    · exact ⟨0, fun h => absurd hs h⟩
    · have hfin := Set.not_infinite.1 hs
      exact ⟨hfin.toFinset.sup id + 1, fun _ x hx => Nat.lt_succ_of_le
        (Finset.le_sup (f := id) (hfin.mem_toFinset.2 hx))⟩
  choose Bd hBd using hbd
  set x₀ := Finset.univ.sup Bd
  have hinf : ∀ y, x₀ ≤ y → {x | sig b f x = sig b f y}.Infinite := fun y hy => by
    by_contra h
    have h1 := hBd (sig b f y) h y rfl
    have h2 := Finset.le_sup (f := Bd) (Finset.mem_univ (sig b f y))
    omega
  -- a bound on the chosen pairs, and close powers
  set ξ := Finset.univ.sup (fun s => (P s).1 + (P s).2) + 1
  have hξ : ∀ s, (P s).1 < ξ ∧ (P s).2 < ξ := fun s => by
    have := Finset.le_sup (f := fun s => (P s).1 + (P s).2) (Finset.mem_univ s)
    constructor <;> omega
  obtain ⟨m, n, hm, hn, hclose⟩ := exists_close_powers ha hb (M := 6 * ξ) (by omega)
  push_cast at hclose
  have hd : (a : ℤ) ^ m - (b : ℤ) ^ n ≠ 0 := fun h =>
    hab m n hm hn (by exact_mod_cast sub_eq_zero.1 h)
  have hD := abs_nonneg ((a : ℤ) ^ m - (b : ℤ) ^ n)
  -- for each such signature, an ordered pair and its local period
  have hord : ∀ s : kernel b f → Fin 3 → Bool, {x | sig b f x = s}.Infinite → ∃ u v p : ℕ,
      sig b f u = s ∧ sig b f v = s ∧ sig a f u = sig a f v ∧ v < ξ ∧ 0 < p ∧ 6 * p < b ^ n ∧
        ((u : ℤ) - v) * ((a : ℤ) ^ m - (b : ℤ) ^ n) = p := by
    intro s hs
    obtain ⟨hξ1, hξ2⟩ := hξ s
    have hne : ((P s).1 : ℤ) - (P s).2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hPne s hs)
    have hxyξ : |((P s).1 : ℤ) - (P s).2| ≤ ξ := by
      rw [abs_le]
      constructor <;> omega
    have hbound : |((P s).1 : ℤ) - (P s).2| * |(a : ℤ) ^ m - (b : ℤ) ^ n| * 6 < (b : ℤ) ^ n := by
      nlinarith [mul_le_mul_of_nonneg_right hxyξ hD]
    rcases lt_or_gt_of_ne (mul_ne_zero hne hd) with hneg | hpos
    · refine ⟨(P s).2, (P s).1, ((((P s).2 : ℤ) - (P s).1) * ((a : ℤ) ^ m - (b : ℤ) ^ n)).toNat,
        hP2 s hs, hP1 s hs, (hPa s hs).symm, hξ1, ?_, ?_, ?_⟩
      · rw [Int.lt_toNat]; push_cast; nlinarith
      · zify
        rw [Int.toNat_of_nonneg (by nlinarith)]
        rw [abs_sub_comm] at hbound
        nlinarith [le_abs_self ((((P s).2 : ℤ) - (P s).1) * ((a : ℤ) ^ m - (b : ℤ) ^ n)),
          abs_mul (((P s).2 : ℤ) - (P s).1) ((a : ℤ) ^ m - (b : ℤ) ^ n)]
      · rw [Int.toNat_of_nonneg (by nlinarith)]
    · refine ⟨(P s).1, (P s).2, ((((P s).1 : ℤ) - (P s).2) * ((a : ℤ) ^ m - (b : ℤ) ^ n)).toNat,
        hP1 s hs, hP2 s hs, hPa s hs, hξ2, ?_, ?_, ?_⟩
      · rw [Int.lt_toNat]; push_cast; exact hpos
      · zify
        rw [Int.toNat_of_nonneg hpos.le]
        nlinarith [le_abs_self ((((P s).1 : ℤ) - (P s).2) * ((a : ℤ) ^ m - (b : ℤ) ^ n)),
          abs_mul (((P s).1 : ℤ) - (P s).2) ((a : ℤ) ^ m - (b : ℤ) ^ n)]
      · rw [Int.toNat_of_nonneg hpos.le]
  choose! U V Pp hU hV hUVa hVξ hPp hPp6 hPpeq using hord
  -- local periods around consecutive multiples of `bⁿ`
  have hloc : ∀ y, x₀ ≤ y → LocPer f (Pp (sig b f y))
      (y * b ^ n + b ^ n - 2 * b ^ n / 3) (y * b ^ n + b ^ n + 2 * b ^ n / 3) := fun y hy => by
    have hs := hinf y hy
    exact locPer_of_pair (by omega) (by omega) (hU _ hs).symm (hV _ hs).symm (hUVa _ hs)
      (hVξ _ hs) (hPpeq _ hs) hclose
  -- glue them
  set N := b ^ n
  have hN : 0 < N := pow_pos (by omega) n
  set P0 := Pp (sig b f x₀)
  have hP0 : 0 < P0 := hPp _ (hinf x₀ le_rfl)
  have hP06 : 6 * P0 < N := hPp6 _ (hinf x₀ le_rfl)
  have hglue : ∀ k, LocPer f P0 (x₀ * N + N - 2 * N / 3) ((x₀ + k) * N + N + 2 * N / 3) := by
    intro k
    induction k with
    | zero => simpa using hloc x₀ le_rfl
    | succ k ih =>
      have hs := hinf (x₀ + k + 1) (by omega)
      have hq := hPp _ hs
      have hq6 := hPp6 _ hs
      have hk : (x₀ + k + 1) * N = (x₀ + k) * N + N := by ring
      have hx : x₀ * N ≤ (x₀ + k) * N := Nat.mul_le_mul_right _ (by omega)
      have := ih.glue (hloc (x₀ + k + 1) (by omega)) (by rw [hk]; omega) (by rw [hk]; omega) hq
      rwa [show x₀ + (k + 1) = x₀ + k + 1 by ring]
  refine ⟨x₀ * N + N - 2 * N / 3, P0, hP0, fun t ht => hglue (t + P0) t ht ?_⟩
  have : t + P0 ≤ (x₀ + (t + P0)) * N := by nlinarith
  omega

/-! ### The center column -/

theorem two_pow_ne_three_pow {m n : ℕ} (hm : 0 < m) : (2 : ℕ) ^ m ≠ 3 ^ n := by
  intro h
  have h1 : (3 : ℕ) ^ n % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : (2 : ℕ) ^ m % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hm.ne')
  rw [h] at h2
  omega

/-- A sequence is eventually periodic iff it is both 2-automatic and 3-automatic. -/
theorem eventuallyPeriodic_iff_isAutomatic_two_three (f : ℕ → Bool) :
    EventuallyPeriodic f ↔ IsAutomatic 2 f ∧ IsAutomatic 3 f :=
  ⟨fun h => ⟨isAutomatic_of_eventuallyPeriodic h le_rfl,
      isAutomatic_of_eventuallyPeriodic h (by norm_num)⟩,
    fun ⟨h2, h3⟩ => eventuallyPeriodic_of_isAutomatic le_rfl (by norm_num)
      (fun _ _ hm _ => two_pow_ne_three_pow hm) h2 h3⟩

/-- **Problem 1 ⟺ the center column is not both 2-automatic and 3-automatic**. -/
theorem problem1_iff_not_two_three_automatic : Rule30Prize.Problem1 ↔
    ¬ (IsAutomatic 2 Rule30Prize.center ∧ IsAutomatic 3 Rule30Prize.center) :=
  not_congr (eventuallyPeriodic_iff_isAutomatic_two_three _)

/-- **Problem 1 ⟺ the center column is not `k`-automatic for some `k ≥ 2`**. -/
theorem problem1_iff_exists_not_automatic : Rule30Prize.Problem1 ↔
    ∃ k, 2 ≤ k ∧ ¬ IsAutomatic k c := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    exact h (eventuallyPeriodic_of_isAutomatic le_rfl (by norm_num)
      (fun _ _ hm _ => two_pow_ne_three_pow hm) (hall 2 le_rfl) (hall 3 (by norm_num)))
  · rintro ⟨k, hk, h⟩
    exact problem1_of_not_automatic hk h

end Rule30Equivalents.Cobham
