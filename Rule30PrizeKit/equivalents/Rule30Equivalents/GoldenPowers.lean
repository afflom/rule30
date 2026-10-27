module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Linarith

/-!
# The Mignosi–Restivo–Salemi theorem: prefixes ending in `φ²`-repetitions

An infinite word is eventually periodic iff every sufficiently long prefix ends with a repetition
of exponent at least `φ² = φ + 1 ≈ 2.618`, where `φ` is the golden ratio. The constant is sharp:
the Fibonacci word has, for each `ε > 0`, every long prefix ending in a `(φ² - ε)`-repetition.

* `PerOn b d lo hi`: the word has period `d` on the positions `lo, …, hi - 1`.
* `need d = ⌈φ² d⌉`, and `GP b n d`: the prefix of length `n` ends with a `φ²`-repetition of period
  `d`. `pmin b n` is the least such `d`, the `φ`-local period.
* `PerOn.glue` (Lemma 2), `perOn_sub` (Lemma 1), `gp_sub` (Lemma 4): a window of length `⌈φ P⌉`
  with periods `P` and `Q`, `φ Q ≥ P`, ends with a `φ²`-repetition of period `P - Q`.
* `first_lt` and `period_until` (Theorem 1): in a stretch where every prefix ends with a
  `φ²`-repetition, the first index `Z` where the local period reaches its maximum `P` is less than
  `k + P`, and the word has period `P` from `Z - ⌈φ² P⌉` to every later index with local period
  `P`.
* `eventuallyPeriodic_of_gp` (Theorem 2): if every prefix of length at least `k` ends with a
  `φ²`-repetition, the word is eventually periodic. The local periods are bounded by `k`
  (`first_lt`), and an induction on that bound finishes: either the bound is attained infinitely
  often, and `period_until` gives a period, or not, and the bound drops.

Source: F. Mignosi, A. Restivo, S. Salemi, *Periodicity and the golden ratio*, Theoret. Comput.
Sci. 204 (1998) 153–167 (Lemmas 1–4, Theorems 1 and 2). The conjecture is J. Shallit's.
-/

@[expose] public section

namespace Rule30Equivalents.GoldenPowers

open Real (goldenRatio)

variable {α : Type*} (b : ℕ → α)

/-- The word `b` has period `d` on the positions `lo, …, hi - 1`. -/
def PerOn (d lo hi : ℕ) : Prop := ∀ i, lo ≤ i → i + d < hi → b (i + d) = b i

/-- The length a stretch with period `d` needs to be a `φ²`-repetition: `⌈φ² d⌉`. -/
noncomputable def need (d : ℕ) : ℕ := ⌈goldenRatio ^ 2 * d⌉₊

/-- The prefix of length `n` ends with a `φ²`-repetition of period `d`. -/
def GP (n d : ℕ) : Prop := 0 < d ∧ need d ≤ n ∧ PerOn b d (n - need d) n

variable {b}

theorem PerOn.mono {d lo hi lo' hi' : ℕ} (h : PerOn b d lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    PerOn b d lo' hi' := fun i h1 h2 => h i (le_trans hlo h1) (by omega)

/-- **Lemma 2**: two stretches with period `d` that overlap in at least `d` positions glue. -/
theorem PerOn.glue {d lo m0 m1 hi : ℕ} (h1 : PerOn b d lo m1) (h2 : PerOn b d m0 hi)
    (hov : m0 + d ≤ m1) : PerOn b d lo hi := by
  intro i hi1 hi2
  by_cases h : m0 ≤ i
  · exact h2 i h hi2
  · exact h1 i hi1 (by omega)

/-! ### The numbers -/

theorem need_eq (P : ℕ) : need P = P + ⌈goldenRatio * P⌉₊ := by
  unfold need
  rw [Real.goldenRatio_sq, add_mul, one_mul, Nat.ceil_add_natCast (by positivity), Nat.add_comm]

theorem le_ceil_phi (P : ℕ) : P ≤ ⌈goldenRatio * P⌉₊ := by
  have h1 : (P : ℝ) ≤ goldenRatio * P := by
    nlinarith [Real.one_lt_goldenRatio, (Nat.cast_nonneg P : (0 : ℝ) ≤ P)]
  exact_mod_cast h1.trans (Nat.le_ceil _)

theorem lt_ceil_phi {P : ℕ} (hP : 0 < P) : P < ⌈goldenRatio * P⌉₊ := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  rw [Nat.lt_ceil]
  nlinarith [Real.one_lt_goldenRatio]

/-- `φ Q ≥ P` gives `⌈φ P⌉ - Q ≥ ⌈φ² (P - Q)⌉` (Lemma 3). -/
theorem need_sub_le {P Q : ℕ} (hQP : Q < P) (hφ : (P : ℝ) ≤ goldenRatio * Q) :
    need (P - Q) + Q ≤ ⌈goldenRatio * P⌉₊ := by
  have hle : need (P - Q) ≤ ⌈goldenRatio * P⌉₊ - Q := by
    unfold need
    rw [Nat.ceil_le]
    have hcast : ((P - Q : ℕ) : ℝ) = P - Q := by rw [Nat.cast_sub hQP.le]
    have hQc : Q ≤ ⌈goldenRatio * P⌉₊ := le_trans hQP.le (le_ceil_phi P)
    rw [hcast, Nat.cast_sub hQc]
    have h1 : goldenRatio * P ≤ ⌈goldenRatio * P⌉₊ := Nat.le_ceil _
    rw [Real.goldenRatio_sq]
    nlinarith
  have hQc : Q ≤ ⌈goldenRatio * P⌉₊ := le_trans hQP.le (le_ceil_phi P)
  omega

theorem ceil_phi_le_need {P Q : ℕ} (hφ : (P : ℝ) ≤ goldenRatio * Q) :
    ⌈goldenRatio * P⌉₊ ≤ need Q := by
  unfold need
  apply Nat.ceil_mono
  have h1 : goldenRatio * P ≤ goldenRatio * (goldenRatio * Q) :=
    mul_le_mul_of_nonneg_left hφ Real.goldenRatio_pos.le
  have h2 : goldenRatio * (goldenRatio * Q) = goldenRatio ^ 2 * Q := by ring
  linarith

theorem need_le_ceil_phi {P Q : ℕ} (hφ : goldenRatio * Q < P) : need Q ≤ ⌈goldenRatio * P⌉₊ := by
  unfold need
  apply Nat.ceil_mono
  have h1 : goldenRatio * (goldenRatio * Q) ≤ goldenRatio * P :=
    mul_le_mul_of_nonneg_left hφ.le Real.goldenRatio_pos.le
  have h2 : goldenRatio * (goldenRatio * Q) = goldenRatio ^ 2 * Q := by ring
  linarith

theorem lt_two_mul {P Q : ℕ} (hQ : 0 < Q) (hφ : (P : ℝ) ≤ goldenRatio * Q) : P < 2 * Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have : (P : ℝ) < 2 * Q := by nlinarith [Real.goldenRatio_lt_two]
  exact_mod_cast this

/-! ### Lemmas 1 and 4 -/

/-- **Lemma 1**: if `w = v u` has periods `P > Q` and `|u| = Q`, then `v` has period `P - Q`. -/
theorem perOn_sub {lo hi P Q : ℕ} (hQP : Q < P) (hP : PerOn b P lo hi) (hQ : PerOn b Q lo hi) :
    PerOn b (P - Q) lo (hi - Q) := by
  intro i h1 h2
  have e1 := hP i h1 (by omega)
  have e2 := hQ (i + (P - Q)) (by omega) (by omega)
  rw [show i + (P - Q) + Q = i + P by omega] at e2
  rw [← e2, e1]

/-- A stretch long enough for a `φ²`-repetition, ending at `hi`. -/
theorem gp_of_perOn {d lo hi : ℕ} (hd : 0 < d) (hlen : need d + lo ≤ hi) (h : PerOn b d lo hi) :
    GP b hi d :=
  ⟨hd, by omega, h.mono (by omega) le_rfl⟩

/-- **Lemma 4**: a window of length at least `⌈φ P⌉` with periods `P` and `Q`, where `φ Q ≥ P`,
ends with a `φ²`-repetition of period `P - Q`. -/
theorem gp_sub {lo hi P Q : ℕ} (hQP : Q < P) (hφ : (P : ℝ) ≤ goldenRatio * Q)
    (hlen : ⌈goldenRatio * P⌉₊ + lo ≤ hi) (hP : PerOn b P lo hi) (hQ : PerOn b Q lo hi) :
    GP b hi (P - Q) := by
  have hv := perOn_sub hQP hP hQ
  -- the prefix `v` is also a suffix, by period `Q`
  have hsuf : PerOn b (P - Q) (lo + Q) hi := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + Q := ⟨i - Q, by omega⟩
    have a1 := hQ j (by omega) (by omega)
    have a2 := hQ (j + (P - Q)) (by omega) (by omega)
    have a3 := hv j (by omega) (by omega)
    rw [show j + Q + (P - Q) = j + (P - Q) + Q by omega, a2, a3, a1]
  have hn := need_sub_le hQP hφ
  exact gp_of_perOn (by omega) (by omega) hsuf

/-! ### The `φ`-local period -/

open Classical in
/-- The `φ`-local period: the least `d` such that the prefix of length `n` ends with a
`φ²`-repetition of period `d` (or `0` if there is none). -/
noncomputable def pmin (b : ℕ → α) (n : ℕ) : ℕ := if h : ∃ d, GP b n d then Nat.find h else 0

theorem gp_pmin {n : ℕ} (h : ∃ d, GP b n d) : GP b n (pmin b n) := by
  classical
  unfold pmin
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem pmin_le {n d : ℕ} (h : GP b n d) : pmin b n ≤ d := by
  classical
  unfold pmin
  rw [dite_eq_left ⟨d, h⟩]
  exact Nat.find_min' _ h

/-! ### Theorem 1 -/

/-- **Theorem 1, the bound**: if every prefix of length in `[k, Z]` ends with a `φ²`-repetition, the
local periods there are at most `P`, and `Z` is the first index in `[k, Z]` where the local period is
`P`, then `Z < k + P`. -/
theorem first_lt {k Z P : ℕ} (hgp : ∀ n, k ≤ n → n ≤ Z → ∃ d, GP b n d)
    (hle : ∀ n, k ≤ n → n ≤ Z → pmin b n ≤ P) (hkZ : k ≤ Z) (hZ : pmin b Z = P)
    (hfirst : ∀ n, k ≤ n → n < Z → pmin b n ≠ P) : Z < k + P := by
  by_contra hcon
  rw [not_lt] at hcon
  have gZ := gp_pmin (hgp Z hkZ le_rfl)
  rw [hZ] at gZ
  obtain ⟨hP0, hneedZ, hperZ⟩ := gZ
  have hn := need_eq P
  have hkhi : k ≤ Z - P := by omega
  have ghi := gp_pmin (hgp (Z - P) hkhi (by omega))
  have hQP : pmin b (Z - P) ≤ P := hle (Z - P) hkhi (by omega)
  have hQne : pmin b (Z - P) ≠ P := hfirst (Z - P) hkhi (by omega)
  obtain ⟨hQ0, hneedhi, hperhi⟩ := ghi
  set Q := pmin b (Z - P) with hQdef
  have hQlt : Q < P := lt_of_le_of_ne hQP hQne
  set c := ⌈goldenRatio * P⌉₊ with hc
  -- the window `[Z - P - c, Z - P)` has period `P`
  have hwP : PerOn b P (Z - P - c) (Z - P) := hperZ.mono (by omega) (by omega)
  by_cases hφ : (P : ℝ) ≤ goldenRatio * Q
  · have h2 := ceil_phi_le_need (Q := Q) hφ
    have hwQ : PerOn b Q (Z - P - c) (Z - P) := hperhi.mono (by omega) le_rfl
    have hg := gp_sub hQlt hφ (by omega) hwP hwQ
    have h3 := pmin_le hg
    have h4 := lt_two_mul hQ0 hφ
    omega
  · rw [not_le] at hφ
    have h3 := need_le_ceil_phi hφ
    -- shift the `Q`-repetition at `Z - P` forward by `P`
    have hZQ : GP b Z Q := by
      refine ⟨hQ0, by omega, fun i h1 h2 => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = j + P := ⟨i - P, by omega⟩
      have a1 := hperhi j (by omega) (by omega)
      have a2 := hperZ j (by omega) (by omega)
      have a3 := hperZ (j + Q) (by omega) (by omega)
      rw [show j + P + Q = j + Q + P by omega, a3, a1, a2]
    have := pmin_le hZQ
    omega

/-- **Theorem 1, the period**: if `Z` has local period `P`, the maximum on `[k, t]`, the word has
period `P` from `Z - ⌈φ² P⌉` to every later index `n ≤ t` whose local period is `P`. -/
theorem period_until {k t Z P : ℕ} (hgp : ∀ n, k ≤ n → n ≤ t → ∃ d, GP b n d)
    (hle : ∀ n, k ≤ n → n ≤ t → pmin b n ≤ P) (hkZ : k ≤ Z) (hZt : Z ≤ t) (hZ : pmin b Z = P) :
    ∀ n, Z ≤ n → n ≤ t → pmin b n = P → PerOn b P (Z - need P) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hZn hnt hn
    rcases Nat.eq_or_lt_of_le hZn with rfl | hlt
    · have gZ := gp_pmin (hgp Z hkZ hZt)
      rw [hZ] at gZ
      exact gZ.2.2
    · classical
      set nh := Nat.findGreatest (fun m => Z ≤ m ∧ pmin b m = P) (n - 1) with hnh
      have hspec : Z ≤ nh ∧ pmin b nh = P :=
        Nat.findGreatest_spec (P := fun m => Z ≤ m ∧ pmin b m = P) (m := Z) (by omega) ⟨le_rfl, hZ⟩
      have hnh1 : nh ≤ n - 1 := Nat.findGreatest_le _
      have ih' := ih nh (by omega) hspec.1 (by omega) hspec.2
      have hfl := first_lt (b := b) (k := nh + 1) (Z := n) (P := P)
        (fun m h1 h2 => hgp m (by omega) (by omega)) (fun m h1 h2 => hle m (by omega) (by omega))
        (by omega) hn (fun m h1 h2 h3 =>
          Nat.findGreatest_is_greatest (P := fun m => Z ≤ m ∧ pmin b m = P) (n := n - 1)
            (show Nat.findGreatest (fun m => Z ≤ m ∧ pmin b m = P) (n - 1) < m by rw [← hnh]; omega)
            (by omega) ⟨by omega, h3⟩)
      have gn := gp_pmin (hgp n (by omega) hnt)
      rw [hn] at gn
      have hcP := le_ceil_phi P
      have hneq := need_eq P
      have hZneed : need P ≤ Z := by
        have gZ := gp_pmin (hgp Z hkZ hZt)
        rw [hZ] at gZ
        exact gZ.2.1
      exact ih'.glue gn.2.2 (by omega)

/-! ### Theorem 2 -/

/-- **Mignosi–Restivo–Salemi**: if every prefix of length at least `k` ends with a repetition of
exponent at least `φ²`, the word is eventually periodic. -/
theorem eventuallyPeriodic_of_gp {k : ℕ} (h : ∀ n, k ≤ n → ∃ d, GP b n d) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → b (t + P) = b t := by
  -- the local periods are at most `k`
  have hbound : ∀ n, k ≤ n → pmin b n ≤ k := by
    intro n hn
    by_contra hgt
    rw [not_le] at hgt
    classical
    have hex : ∃ m, k ≤ m ∧ k < pmin b m := ⟨n, hn, hgt⟩
    obtain ⟨hkZ, hZgt⟩ := Nat.find_spec hex
    set Z := Nat.find hex with hZdef
    have hfl := first_lt (b := b) (k := k) (Z := Z) (P := pmin b Z) (fun m h1 h2 => h m h1)
      (fun m h1 h2 => by
        rcases Nat.lt_or_ge m Z with hm | hm
        · have := Nat.find_min hex hm
          push Not at this
          have := this h1
          omega
        · rw [show m = Z by omega])
      hkZ rfl (fun m h1 h2 => by
        have := Nat.find_min hex h2
        push Not at this
        have := this h1
        omega)
    have gZ := gp_pmin (h Z hkZ)
    have hn' := need_eq (pmin b Z)
    have hc := lt_ceil_phi gZ.1
    have := gZ.2.1
    omega
  -- induction on a bound for the local periods
  suffices key : ∀ M k, (∀ n, k ≤ n → ∃ d, GP b n d) → (∀ n, k ≤ n → pmin b n ≤ M) →
      ∃ T P, 0 < P ∧ ∀ t, T ≤ t → b (t + P) = b t from key k k h hbound
  intro M
  induction M with
  | zero =>
    intro k h hb
    have := (gp_pmin (h k le_rfl)).1
    have := hb k le_rfl
    omega
  | succ M ih =>
    intro k h hb
    by_cases hinf : ∀ N, ∃ n, N ≤ n ∧ k ≤ n ∧ pmin b n = M + 1
    · classical
      have hex : ∃ n, k ≤ n ∧ pmin b n = M + 1 := by
        obtain ⟨n, -, h1, h2⟩ := hinf 0
        exact ⟨n, h1, h2⟩
      obtain ⟨hkZ, hZ⟩ := Nat.find_spec hex
      refine ⟨Nat.find hex - need (M + 1), M + 1, by omega, fun t ht => ?_⟩
      obtain ⟨S, hS, hkS, hpS⟩ := hinf (t + M + 2 + Nat.find hex)
      have hper := period_until (b := b) (k := k) (t := S) (Z := Nat.find hex) (P := M + 1)
        (fun n h1 _ => h n h1) (fun n h1 _ => hb n h1) hkZ (by omega) hZ S (by omega) le_rfl hpS
      exact hper t ht (by omega)
    · push Not at hinf
      obtain ⟨N, hN⟩ := hinf
      exact ih (max N k) (fun n hn => h n (by omega)) fun n hn => by
        have h1 := hb n (by omega)
        have h2 := hN n (by omega) (by omega)
        omega

end Rule30Equivalents.GoldenPowers
