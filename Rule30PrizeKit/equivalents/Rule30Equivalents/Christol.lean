module

public import Rule30Equivalents.Cobham
public import Rule30Equivalents.AlgebraicDFinite
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Christol's theorem: `p`-automatic iff algebraic over `𝔽_p(X)`

Let `p` be a prime. If the generating function
`∑ b(n) Xⁿ` of a `Bool` sequence `b`, read in `𝔽_p`, is algebraic over `𝔽_p(X)`, then `b` is
`p`-automatic. With Cobham's theorem (`Cobham`), Problem 1 holds iff `∑ c(t) Xᵗ` is transcendental
over `F₂(X)` or over `F₃(X)`.

* `pow_eq_expand`: over `𝔽_p`, `h^p = h(X^p)` (Mathlib's `map_frobenius_expand`).
* `cartier r`: the Cartier operator `Λ_r (∑ aₙ Xⁿ) = ∑ a_{pn+r} Xⁿ`, with `Λ_r (h^p g) = h Λ_r g`
  (`cartier_pow_mul`).
* `exists_ore_relation` (Ore): an algebraic `F` satisfies `∑_{i ≤ d} cᵢ F^{pⁱ} = 0` with polynomial
  `cᵢ` and `c₀ ≠ 0`. The powers `F, F^p, …, F^{p^d}` are dependent over `𝔽_p[X]`
  (`AlgebraicDFinite.mul_aeval_mem_span`). If the lowest nonzero coefficient sits at `k > 0`, a
  suitable `Λ_r` moves it to `k − 1` (`exists_ore`).
* `isAutomatic_of_isAlgebraic` (Christol): the set `T` of `g` with
  `c₀ g = ∑ hᵢ F^{pⁱ}`, `deg hᵢ ≤ D`, is finite, contains `F` and is closed under every `Λ_r`,
  since `c₀ Λ_r g = Λ_r (c₀^{p−1} · c₀ g)` and `c₀ F` is a combination of higher powers. The
  `p`-kernel of `b` is its image under the iterated Cartier operators, so it is finite.
* `isAlgebraic_of_isAutomatic` (the converse): the `𝔽_p(X)`-span of the kernel series lies in the
  span of their `p`-th powers, since `g = ∑_{r < p} X^r (Λ_r g)^p` (`eq_sum_cartier`), and the
  latter has no larger dimension; so the span is closed under `p`-th powers, and
  `F, F^p, …, F^(p^d)` are dependent. Together: `isAutomatic_iff_isAlgebraic`, and for the center
  column `not_isAutomatic_iff_transcendental`.
* `problem1_iff_transcendental_F2_or_F3`.

Sources: G. Christol, *Ensembles presque périodiques k-reconnaissables*, Theoret. Comput. Sci. 9
(1979) 141–145; G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates
et substitutions*, Bull. Soc. Math. France 108 (1980) 401–419; J.-P. Allouche, J. Shallit,
*Automatic Sequences* (2003), Theorem 12.2.5.
-/

@[expose] public section

namespace Rule30Equivalents.Christol

open Polynomial Automatic Ruliology.CellularAutomata
open scoped LaurentSeries RatFunc

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Frobenius and the Cartier operators -/

/-- Over `𝔽_p`, `h^p = h(X^p)`. -/
theorem pow_eq_expand (h : PowerSeries (ZMod p)) :
    h ^ p = PowerSeries.expand p hp.out.ne_zero h := by
  have := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) p hp.out.ne_zero (f := h)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at this
  exact this.symm

theorem coeff_pow_p (h : PowerSeries (ZMod p)) (n : ℕ) :
    PowerSeries.coeff n (h ^ p) = if p ∣ n then PowerSeries.coeff (n / p) h else 0 := by
  rw [pow_eq_expand, PowerSeries.coeff_expand]

/-- The Cartier operator `Λ_r (∑ aₙ Xⁿ) = ∑ a_{pn+r} Xⁿ`. -/
noncomputable def cartier (p r : ℕ) (g : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  PowerSeries.mk fun n => PowerSeries.coeff (p * n + r) g

@[simp] theorem coeff_cartier (r n : ℕ) (g : PowerSeries (ZMod p)) :
    PowerSeries.coeff n (cartier p r g) = PowerSeries.coeff (p * n + r) g := by
  simp [cartier]

theorem cartier_add (r : ℕ) (g h : PowerSeries (ZMod p)) :
    cartier p r (g + h) = cartier p r g + cartier p r h := by
  ext n; simp

theorem cartier_sub (r : ℕ) (g h : PowerSeries (ZMod p)) :
    cartier p r (g - h) = cartier p r g - cartier p r h := by
  ext n; simp

theorem cartier_zero (r : ℕ) : cartier p r (0 : PowerSeries (ZMod p)) = 0 := by
  ext n; simp

theorem cartier_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries (ZMod p)) (r : ℕ) :
    cartier p r (∑ i ∈ s, g i) = ∑ i ∈ s, cartier p r (g i) := by
  ext n; simp [map_sum]

/-- `Λ_r (h^p g) = h Λ_r g`. -/
theorem cartier_pow_mul {r : ℕ} (hr : r < p) (h g : PowerSeries (ZMod p)) :
    cartier p r (h ^ p * g) = h * cartier p r g := by
  have hp0 := hp.out.pos
  ext n
  rw [coeff_cartier, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  simp only [coeff_pow_p, coeff_cartier, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun y _ => (p * y.1, p * y.2 + r)) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by rw [← hy]; ring, dvd_mul_right _ _⟩
  · intro y₁ _ y₂ _ he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hp0 he.1)
      (Nat.eq_of_mul_eq_mul_left hp0 (by omega))
  · intro x hx
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    obtain ⟨hsum, k, hk⟩ := hx
    have hkn : k ≤ n := by
      by_contra hkn
      have : p * (n + 1) ≤ p * k := Nat.mul_le_mul_left p (by omega)
      rw [Nat.mul_succ] at this
      omega
    refine ⟨(k, n - k), by simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega, ?_⟩
    have h2 : x.2 = p * (n - k) + r := by
      rw [Nat.mul_sub]
      have : p * k ≤ p * n := Nat.mul_le_mul_left p hkn
      omega
    exact Prod.ext hk.symm h2.symm
  · intro y _
    simp [Nat.mul_div_cancel_left _ hp0]

/-- The iterated Cartier operator `g ↦ ∑ a_{pᵉ n + r} Xⁿ`. -/
noncomputable def cartierPow (p e r : ℕ) (g : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  PowerSeries.mk fun n => PowerSeries.coeff (p ^ e * n + r) g

theorem cartierPow_succ (e r : ℕ) (g : PowerSeries (ZMod p)) :
    cartierPow p (e + 1) r g = cartier p (r / p ^ e) (cartierPow p e (r % p ^ e) g) := by
  ext n
  simp only [cartierPow, cartier, PowerSeries.coeff_mk]
  congr 2
  rw [pow_succ, mul_add, add_assoc, Nat.div_add_mod, mul_assoc]

/-! ### Bounded degree -/

/-- `g` has no coefficients beyond `N`. -/
def BddDeg (N : ℕ) (g : PowerSeries (ZMod p)) : Prop := ∀ n, N < n → PowerSeries.coeff n g = 0

theorem BddDeg.mono {N M : ℕ} {g : PowerSeries (ZMod p)} (h : BddDeg N g) (hNM : N ≤ M) :
    BddDeg M g := fun n hn => h n (by omega)

theorem bddDeg_zero (N : ℕ) : BddDeg N (0 : PowerSeries (ZMod p)) := fun n _ => by simp

theorem BddDeg.sub {N : ℕ} {g h : PowerSeries (ZMod p)} (hg : BddDeg N g) (hh : BddDeg N h) :
    BddDeg N (g - h) := fun n hn => by simp [hg n hn, hh n hn]

theorem BddDeg.mul {N M : ℕ} {g h : PowerSeries (ZMod p)} (hg : BddDeg N g) (hh : BddDeg M h) :
    BddDeg (N + M) (g * h) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : N < x.1
  · rw [hg _ h1, zero_mul]
  · rw [hh _ (by omega), mul_zero]

theorem BddDeg.pow {N : ℕ} {g : PowerSeries (ZMod p)} (hg : BddDeg N g) :
    ∀ k : ℕ, BddDeg (k * N) (g ^ k)
  | 0 => fun n hn => by simp [PowerSeries.coeff_one, show n ≠ 0 by omega]
  | k + 1 => by
    rw [pow_succ, show (k + 1) * N = k * N + N by ring]
    exact (hg.pow k).mul hg

theorem BddDeg.cartier {N : ℕ} {g : PowerSeries (ZMod p)} (hg : BddDeg N g) (r : ℕ) :
    BddDeg (N / p) (cartier p r g) := by
  intro n hn
  rw [coeff_cartier]
  refine hg _ ?_
  have := (Nat.div_lt_iff_lt_mul hp.out.pos).1 hn
  nlinarith

theorem bddDeg_coe (c : (ZMod p)[X]) : BddDeg c.natDegree (c : PowerSeries (ZMod p)) :=
  fun n hn => by rw [Polynomial.coeff_coe]; exact Polynomial.coeff_eq_zero_of_natDegree_lt hn

theorem finite_bddDeg (N : ℕ) : {g : PowerSeries (ZMod p) | BddDeg N g}.Finite := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine Set.Finite.of_finite_image (f := fun g (i : Fin (N + 1)) => PowerSeries.coeff i g)
    (Set.toFinite _) ?_
  intro g hg h hh he
  ext n
  by_cases hn : n ≤ N
  · exact congrFun he ⟨n, by omega⟩
  · rw [hg n (by omega), hh n (by omega)]

/-! ### Ore's relation -/

/-- The powers `F, F^p, …` of an algebraic power series are dependent over `𝔽_p[X]`. -/
theorem exists_relation {F : PowerSeries (ZMod p)} (hF : IsAlgebraic (ZMod p)[X] F) :
    ∃ (d D : ℕ) (c : ℕ → PowerSeries (ZMod p)), (∃ i, c i ≠ 0) ∧ (∀ i, BddDeg D (c i)) ∧
      (∀ i, d < i → c i = 0) ∧ ∑ i ∈ Finset.range (d + 1), c i * F ^ (p ^ i) = 0 := by
  classical
  have hinj : Function.Injective (algebraMap (ZMod p)[X] (PowerSeries (ZMod p))) := fun a b h => by
    rw [AlgebraicDFinite.algebraMap_eq_coe, AlgebraicDFinite.algebraMap_eq_coe] at h
    exact Polynomial.coe_inj.1 h
  obtain ⟨P, hP0, hPF⟩ := hF
  have hd0 : P.natDegree ≠ 0 := by
    intro h0
    have hc := hPF
    rw [eq_C_of_natDegree_eq_zero h0, aeval_C] at hc
    exact hP0 (by rw [eq_C_of_natDegree_eq_zero h0, hinj (hc.trans (map_zero _).symm), map_zero])
  set d := P.natDegree
  set w : Fin (d + 1) → PowerSeries (ZMod p) := fun i =>
    algebraMap (ZMod p)[X] (PowerSeries (ZMod p)) (P.leadingCoeff ^ (p ^ (i : ℕ))) * F ^ (p ^ (i : ℕ))
  have hmem : ∀ i, w i ∈ Submodule.span (ZMod p)[X] (Set.range fun j : Fin d => F ^ (j : ℕ)) :=
    fun i => by
      have := AlgebraicDFinite.mul_aeval_mem_span hPF hd0 (X ^ (p ^ (i : ℕ)))
      simpa [w, natDegree_X_pow] using this
  have hdep : ¬ LinearIndependent (ZMod p)[X] w := by
    intro hli
    have h₁ := linearIndependent_le_span' _ hli _ (Set.range_subset_iff.2 hmem)
    have h₂ := Fintype.card_range_le fun j : Fin d => F ^ (j : ℕ)
    rw [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_le] at h₁
    rw [Fintype.card_fin] at h₂
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  set c : ℕ → PowerSeries (ZMod p) := fun j =>
    if h : j < d + 1 then ((g ⟨j, h⟩ * P.leadingCoeff ^ (p ^ j) : (ZMod p)[X]) : PowerSeries (ZMod p))
    else 0
  refine ⟨d, Finset.univ.sup fun j : Fin (d + 1) => (g j * P.leadingCoeff ^ (p ^ (j : ℕ))).natDegree,
    c, ⟨i₀, ?_⟩, fun j => ?_, fun j hj => by simp only [c]; rw [dite_eq_right (by omega)], ?_⟩
  · simp only [c, dite_eq_left i₀.isLt]
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact mul_ne_zero hi₀ (pow_ne_zero _ (leadingCoeff_ne_zero.2 hP0))
  · by_cases hj : j < d + 1
    · simp only [c, dite_eq_left hj]
      exact (bddDeg_coe _).mono (Finset.le_sup (f := fun j : Fin (d + 1) =>
        (g j * P.leadingCoeff ^ (p ^ (j : ℕ))).natDegree) (Finset.mem_univ (⟨j, hj⟩ : Fin (d + 1))))
    · simp only [c, dite_eq_right hj]
      exact bddDeg_zero _
  · rw [← hg, ← Fin.sum_univ_eq_sum_range (fun j => c j * F ^ (p ^ j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c, dite_eq_left j.isLt, w, Algebra.smul_def, Polynomial.coe_mul,
      AlgebraicDFinite.algebraMap_eq_coe, Fin.eta]
    ring

/-- **Ore's descent**: if the lowest nonzero coefficient sits at `k`, a Cartier operator moves it
down to `0`. -/
theorem exists_ore {F : PowerSeries (ZMod p)} {d D : ℕ} : ∀ (k : ℕ) (c : ℕ → PowerSeries (ZMod p)),
    (∀ i, i < k → c i = 0) → c k ≠ 0 → (∀ i, BddDeg D (c i)) → (∀ i, d < i → c i = 0) →
    ∑ i ∈ Finset.range (d + 1), c i * F ^ (p ^ i) = 0 →
    ∃ c' : ℕ → PowerSeries (ZMod p), c' 0 ≠ 0 ∧ (∀ i, BddDeg D (c' i)) ∧
      (∀ i, d < i → c' i = 0) ∧ ∑ i ∈ Finset.range (d + 1), c' i * F ^ (p ^ i) = 0
  | 0, c, _, h0, hD, hd, hrel => ⟨c, h0, hD, hd, hrel⟩
  | k + 1, c, hlow, hk, hD, hd, hrel => by
    obtain ⟨m, hm⟩ : ∃ m, PowerSeries.coeff m (c (k + 1)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (PowerSeries.ext fun n => by simp [h n])
    have hr : m % p < p := Nat.mod_lt _ hp.out.pos
    have hcr : cartier p (m % p) (c (k + 1)) ≠ 0 := fun h0 => hm (by
      have := congrArg (PowerSeries.coeff (m / p)) h0
      rwa [coeff_cartier, Nat.div_add_mod, map_zero] at this)
    refine exists_ore k (fun i => cartier p (m % p) (c (i + 1)))
      (fun i hi => show cartier p (m % p) (c (i + 1)) = 0 by rw [hlow (i + 1) (by omega), cartier_zero])
      hcr (fun i => ((hD (i + 1)).cartier _).mono (Nat.div_le_self _ _))
      (fun i hi => show cartier p (m % p) (c (i + 1)) = 0 by rw [hd (i + 1) (by omega), cartier_zero])
      ?_
    show ∑ i ∈ Finset.range (d + 1), cartier p (m % p) (c (i + 1)) * F ^ (p ^ i) = 0
    have h0 : c 0 = 0 := hlow 0 (by omega)
    have := congrArg (cartier p (m % p)) hrel
    rw [cartier_sum, cartier_zero, Finset.sum_range_succ', h0, zero_mul, cartier_zero,
      add_zero] at this
    rw [Finset.sum_range_succ, hd (d + 1) (by omega), cartier_zero, zero_mul, add_zero]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ, pow_mul, mul_comm (c (i + 1)), cartier_pow_mul hr, mul_comm]

/-- **Ore's lemma**: `∑_{i ≤ d} cᵢ F^{pⁱ} = 0` with `c₀ ≠ 0`. -/
theorem exists_ore_relation {F : PowerSeries (ZMod p)} (hF : IsAlgebraic (ZMod p)[X] F) :
    ∃ (d D : ℕ) (c : ℕ → PowerSeries (ZMod p)), c 0 ≠ 0 ∧ (∀ i, BddDeg D (c i)) ∧
      (∀ i, d < i → c i = 0) ∧ ∑ i ∈ Finset.range (d + 1), c i * F ^ (p ^ i) = 0 := by
  classical
  obtain ⟨d, D, c, hc, hD, hd, hrel⟩ := exists_relation hF
  obtain ⟨c', h0, hD', hd', hrel'⟩ := exists_ore (Nat.find hc) c
    (fun i hi => by simpa using Nat.find_min hc hi) (Nat.find_spec hc) hD hd hrel
  exact ⟨d, D, c', h0, hD', hd', hrel'⟩

/-! ### Christol's theorem -/

/-- **Christol's theorem** (one direction): a `Bool` sequence whose generating function over `𝔽_p`
is algebraic over `𝔽_p[X]` is `p`-automatic. -/
theorem isAutomatic_of_isAlgebraic {f : ℕ → Bool}
    (hF : IsAlgebraic (ZMod p)[X] (LinearRelations.series (ZMod p) f)) : IsAutomatic p f := by
  classical
  set F := LinearRelations.series (ZMod p) f
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨d, D, c, hc0, hD, hd, hrel⟩ := exists_ore_relation hF
  -- `S`: the combinations `∑ hᵢ F^{pⁱ}` with `deg hᵢ ≤ D`
  set S : Set (PowerSeries (ZMod p)) := {s | ∃ h : ℕ → PowerSeries (ZMod p),
    (∀ i, BddDeg D (h i)) ∧ s = ∑ i ∈ Finset.range (d + 1), h i * F ^ (p ^ i)}
  have hS : S.Finite := by
    refine ((Set.Finite.pi (t := fun _ : Fin (d + 1) => {g : PowerSeries (ZMod p) | BddDeg D g})
      fun _ => finite_bddDeg D).image fun h : Fin (d + 1) → PowerSeries (ZMod p) =>
        ∑ i, h i * F ^ (p ^ (i : ℕ))).subset ?_
    rintro s ⟨h, hh, rfl⟩
    exact ⟨fun i => h i, fun i _ => hh i, Fin.sum_univ_eq_sum_range (fun i => h i * F ^ (p ^ i)) _⟩
  -- `T`: the `g` with `c₀ g ∈ S`
  set T : Set (PowerSeries (ZMod p)) := {g | c 0 * g ∈ S}
  have hT : T.Finite := Set.Finite.preimage (mul_right_injective₀ hc0).injOn hS
  have hFT : F ∈ T := by
    refine ⟨fun i => if i = 0 then c 0 else 0, fun i => ?_, ?_⟩
    · by_cases hi : i = 0
      · simp only [ite_eq_left hi]; exact hD 0
      · simp only [ite_eq_right hi]; exact bddDeg_zero D
    · rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (by simp)]
      simp
  -- `T` is closed under the Cartier operators
  have hclosed : ∀ r, r < p → ∀ g ∈ T, cartier p r g ∈ T := by
    intro r hr g hg
    obtain ⟨h, hh, hgh⟩ := hg
    set k : ℕ → PowerSeries (ZMod p) := fun i => c 0 ^ (p - 1) * h i - c 0 ^ (p - 2) * h 0 * c i
    have hk0 : k 0 = 0 := by
      simp only [k]
      rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
      ring
    have hkD : ∀ i, BddDeg (p * D) (k i) := fun i => by
      have h1 := ((hD 0).pow (p - 1)).mul (hh i)
      have h2 := (((hD 0).pow (p - 2)).mul (hh 0)).mul (hD i)
      have e1 : (p - 1) * D + D = p * D := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.out.one_le]
      have e2 : (p - 2) * D + D + D = p * D := by
        rw [add_assoc, ← two_mul, ← add_mul, Nat.sub_add_cancel hp2]
      exact (h1.mono e1.le).sub (h2.mono e2.le)
    have hsum : c 0 ^ (p - 1) * (c 0 * g) = ∑ i ∈ Finset.range (d + 1), k i * F ^ (p ^ i) := by
      have e : ∑ i ∈ Finset.range (d + 1), k i * F ^ (p ^ i) =
          c 0 ^ (p - 1) * ∑ i ∈ Finset.range (d + 1), h i * F ^ (p ^ i) -
            c 0 ^ (p - 2) * h 0 * ∑ i ∈ Finset.range (d + 1), c i * F ^ (p ^ i) := by
        simp only [k, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, hrel, mul_zero, sub_zero, hgh]
    refine ⟨fun j => if j < d then cartier p r (k (j + 1)) else 0, fun j => ?_, ?_⟩
    · by_cases hj : j < d
      · simp only [ite_eq_left hj]
        exact ((hkD (j + 1)).cartier r).mono (by rw [Nat.mul_div_cancel_left _ hp.out.pos])
      · simp only [ite_eq_right hj]
        exact bddDeg_zero D
    · show c 0 * cartier p r g = ∑ j ∈ Finset.range (d + 1),
        (if j < d then cartier p r (k (j + 1)) else 0) * F ^ (p ^ j)
      rw [← cartier_pow_mul hr, show c 0 ^ p * g = c 0 ^ (p - 1) * (c 0 * g) by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.one_le],
        hsum, cartier_sum, Finset.sum_range_succ', hk0, zero_mul, cartier_zero, add_zero,
        Finset.sum_range_succ, ite_eq_right (lt_irrefl d), zero_mul, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ite_eq_left (Finset.mem_range.1 hi), pow_succ, pow_mul, mul_comm (k (i + 1)),
        cartier_pow_mul hr, mul_comm]
  -- every iterated Cartier image of `F` lies in `T`
  have hiter : ∀ e r, r < p ^ e → cartierPow p e r F ∈ T := by
    intro e
    induction e with
    | zero =>
      intro r hr
      obtain rfl : r = 0 := by simpa using hr
      have : cartierPow p 0 0 F = F := by ext n; simp [cartierPow]
      rwa [this]
    | succ e ih =>
      intro r hr
      rw [cartierPow_succ]
      exact hclosed _ ((Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos e)).2 (by rwa [← pow_succ']))
        _ (ih _ (Nat.mod_lt _ (pow_pos hp.out.pos e)))
  -- the kernel injects into `T`
  refine (Set.Finite.preimage (f := fun g : ℕ → Bool => LinearRelations.series (ZMod p) g)
    (fun g₁ _ g₂ _ he => ?_) hT).subset ?_
  · funext n
    have := congrArg (PowerSeries.coeff n) he
    simp only [LinearRelations.coeff_series] at this
    exact LinearRelations.toK_eq_toK_iff.1 this
  · rintro g ⟨e, r, hr, rfl⟩
    show LinearRelations.series (ZMod p) (fun n => f (p ^ e * n + r)) ∈ T
    have : LinearRelations.series (ZMod p) (fun n => f (p ^ e * n + r)) = cartierPow p e r F := by
      ext n
      simp [cartierPow, F, LinearRelations.toK]
    rw [this]
    exact hiter e r hr

/-! ### The converse: `p`-automatic implies algebraic -/

/-- Every power series splits along residues mod `p`: `g = ∑_{r < p} X^r (Λ_r g)^p`. -/
theorem eq_sum_cartier (g : PowerSeries (ZMod p)) :
    g = ∑ r ∈ Finset.range p, PowerSeries.X ^ r * cartier p r g ^ p := by
  ext n
  rw [map_sum]
  simp only [PowerSeries.coeff_X_pow_mul', coeff_pow_p, coeff_cartier]
  have hp0 : 0 < p := hp.out.pos
  rw [Finset.sum_eq_single (n % p)]
  · rw [ite_eq_left (Nat.mod_le n p), ite_eq_left (Nat.dvd_sub_mod n),
      Nat.mul_div_cancel' (Nat.dvd_sub_mod n),
      Nat.sub_add_cancel (Nat.mod_le n p)]
  · intro r hr hne
    split_ifs with h1 h2
    · exfalso
      apply hne
      have := (Nat.modEq_iff_dvd' h1).2 h2
      rw [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)] at this
      exact this
    · rfl
    · rfl
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.mod_lt n hp0)) h

theorem cartier_series (g : ℕ → Bool) (r : ℕ) :
    cartier p r (LinearRelations.series (ZMod p) g) =
      LinearRelations.series (ZMod p) fun n => g (p * n + r) := by
  ext n
  simp [LinearRelations.toK]

/-- Over `𝔽_p`, `v ↦ v^p` maps the span of `S` into the span of the `p`-th powers. -/
theorem pow_mem_span_pow {K V : Type*} [Field K] [CommRing V] [Algebra K V] [CharP V p]
    {S : Set V} {v : V} (hv : v ∈ Submodule.span K S) :
    v ^ p ∈ Submodule.span K ((· ^ p) '' S) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [zero_pow hp.out.ne_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_pow_char]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_pow, ← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

/-- **Christol's theorem, converse**: a `p`-automatic sequence has an algebraic generating
function over `𝔽_p(X)`. The `𝔽_p(X)`-span `U` of the kernel series lies in the span of their
`p`-th powers, which has no larger dimension; so the two are equal, `U` is closed under `p`-th
powers, and `F, F^p, …, F^(p^d)` are `d + 1` elements of a space of dimension `d`. -/
theorem isAlgebraic_of_isAutomatic {f : ℕ → Bool} (hf : IsAutomatic p f) :
    IsAlgebraic (RatFunc (ZMod p))
      ((LinearRelations.series (ZMod p) f : PowerSeries (ZMod p)) : (ZMod p)⸨X⸩) := by
  classical
  have : CharP (ZMod p)⸨X⸩ p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (ZMod p)⸨X⸩).injective p
  let ser : (ℕ → Bool) → (ZMod p)⸨X⸩ := fun g =>
    ((LinearRelations.series (ZMod p) g : PowerSeries (ZMod p)) : (ZMod p)⸨X⸩)
  let T : Set (ZMod p)⸨X⸩ := ser '' kernel p f
  have hT : T.Finite := Set.Finite.image ser hf
  let U := Submodule.span (RatFunc (ZMod p)) T
  let U' := Submodule.span (RatFunc (ZMod p)) ((· ^ p) '' T)
  -- each kernel series is a combination of `p`-th powers of kernel series
  have hTU' : T ⊆ U' := by
    rintro _ ⟨g, hg, rfl⟩
    have hdec : ser g = ∑ r ∈ Finset.range p,
        HahnSeries.ofPowerSeries ℤ (ZMod p) (PowerSeries.X ^ r) *
          ser (fun n => g (p * n + r)) ^ p := by
      show HahnSeries.ofPowerSeries ℤ (ZMod p) (LinearRelations.series (ZMod p) g) = _
      conv_lhs => rw [eq_sum_cartier (LinearRelations.series (ZMod p) g)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]
      congr 1
      rw [map_pow, cartier_series]
    rw [hdec]
    refine Submodule.sum_mem _ fun r hr => ?_
    have hX : HahnSeries.ofPowerSeries ℤ (ZMod p) (PowerSeries.X ^ r) =
        algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
          ((Polynomial.X ^ r : (ZMod p)[X]) : RatFunc (ZMod p)) := by
      rw [← Polynomial.coe_X, ← Polynomial.coe_pow]
      exact RatFunc.coe_coe _
    rw [hX, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, ⟨_, mem_kernel_step hg (Finset.mem_range.1 hr), rfl⟩, rfl⟩)
  have hle : U ≤ U' := Submodule.span_le.2 hTU'
  -- the span of the `p`-th powers has no larger dimension
  obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent (RatFunc (ZMod p)) T
  have hbfin : b.Finite := hT.subset hbT
  have : Fintype b := hbfin.fintype
  have : FiniteDimensional (RatFunc (ZMod p)) U := FiniteDimensional.span_of_finite _ hT
  have : FiniteDimensional (RatFunc (ZMod p)) U' :=
    FiniteDimensional.span_of_finite _ (hT.image _)
  have : FiniteDimensional (RatFunc (ZMod p)) (Submodule.span (RatFunc (ZMod p)) ((· ^ p) '' b)) :=
    FiniteDimensional.span_of_finite _ (hbfin.image _)
  have hrankU : Module.finrank (RatFunc (ZMod p)) U = b.toFinset.card := by
    rw [show U = Submodule.span (RatFunc (ZMod p)) b from hbspan.symm]
    exact finrank_span_set_eq_card hbli
  have hU'b : U' ≤ Submodule.span (RatFunc (ZMod p)) ((· ^ p) '' b) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ Submodule.span (RatFunc (ZMod p)) b := hbspan ▸ Submodule.subset_span hv
    exact pow_mem_span_pow this
  have hrank : Module.finrank (RatFunc (ZMod p)) U' ≤ Module.finrank (RatFunc (ZMod p)) U := by
    calc Module.finrank (RatFunc (ZMod p)) U'
        ≤ Module.finrank (RatFunc (ZMod p)) (Submodule.span (RatFunc (ZMod p)) ((· ^ p) '' b)) :=
          Submodule.finrank_mono hU'b
      _ ≤ ((· ^ p) '' b).toFinset.card := finrank_span_le_card _
      _ ≤ b.toFinset.card := by
          rw [Set.toFinset_image]
          exact Finset.card_image_le
      _ = Module.finrank (RatFunc (ZMod p)) U := hrankU.symm
  have hUU' : U = U' := Submodule.eq_of_le_of_finrank_le hle hrank
  -- so every `F^(p^m)` lies in `U`
  have hF : ser f ∈ U := Submodule.subset_span ⟨f, ⟨0, 0, by simp, by simp⟩, rfl⟩
  have hpow : ∀ m : ℕ, ser f ^ (p ^ m) ∈ U := by
    intro m
    induction m with
    | zero => simpa using hF
    | succ m ih =>
      rw [pow_succ, pow_mul]
      have := pow_mem_span_pow (K := RatFunc (ZMod p)) ih
      rw [show Submodule.span (RatFunc (ZMod p)) ((· ^ p) '' T) = U from hUU'.symm] at this
      exact this
  -- and `d + 1` of them are dependent
  set d := Module.finrank (RatFunc (ZMod p)) U
  have hdep : ¬ LinearIndependent (RatFunc (ZMod p))
      (fun m : Fin (d + 1) => ser f ^ (p ^ (m : ℕ))) := by
    intro hli
    have hli' : LinearIndependent (RatFunc (ZMod p))
        (fun m : Fin (d + 1) => (⟨ser f ^ (p ^ (m : ℕ)), hpow m⟩ : U)) :=
      LinearIndependent.of_comp U.subtype hli
    have := hli'.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    exact absurd this (by omega)
  obtain ⟨c, hc, m₀, hm₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  refine ⟨∑ m : Fin (d + 1), Polynomial.C (c m) * Polynomial.X ^ (p ^ (m : ℕ)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun q : (RatFunc (ZMod p))[X] => q.coeff (p ^ (m₀ : ℕ))) h0
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single m₀ (fun m _ hm => ite_eq_right fun heq =>
        hm (Fin.ext (Nat.pow_right_injective hp.out.two_le heq.symm)))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl] at h1
    exact hm₀ h1
  · simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, ← Algebra.smul_def]
    exact hc

/-- **Christol's theorem**: a `Bool` sequence is `p`-automatic iff its generating function, read
in `𝔽_p`, is algebraic over `𝔽_p(X)`. -/
theorem isAutomatic_iff_isAlgebraic (f : ℕ → Bool) : IsAutomatic p f ↔
    IsAlgebraic (RatFunc (ZMod p))
      ((LinearRelations.series (ZMod p) f : PowerSeries (ZMod p)) : (ZMod p)⸨X⸩) :=
  ⟨isAlgebraic_of_isAutomatic, fun h =>
    isAutomatic_of_isAlgebraic (AlgebraicDFinite.isAlgebraic_polynomial_of_isAlgebraic h)⟩

/-- For the center column: `c` is not `p`-automatic iff `∑ c(t) Xᵗ` is
transcendental over `𝔽_p(X)`. -/
theorem not_isAutomatic_iff_transcendental :
    ¬ IsAutomatic p c ↔ Transcendental (RatFunc (ZMod p))
      ((LinearRelations.series (ZMod p) c : PowerSeries (ZMod p)) : (ZMod p)⸨X⸩) :=
  not_congr (isAutomatic_iff_isAlgebraic c)

/-! ### Problem 1 over `F₂` and `F₃` -/

/-- **Problem 1 ⟺ `∑ c(t) Xᵗ` is transcendental over `F₂(X)` or over `F₃(X)`**:
Christol's theorem and Cobham's theorem. -/
theorem problem1_iff_transcendental_F2_or_F3 : Rule30Prize.Problem1 ↔
    Transcendental (RatFunc (ZMod 2))
        ((LinearRelations.series (ZMod 2) c : PowerSeries (ZMod 2)) : (ZMod 2)⸨X⸩) ∨
      Transcendental (RatFunc (ZMod 3))
        ((LinearRelations.series (ZMod 3) c : PowerSeries (ZMod 3)) : (ZMod 3)⸨X⸩) := by
  refine ⟨fun h => ?_, Transcendence.problem1_of_transcendental_F2_or_F3⟩
  by_contra hn
  simp only [Transcendental, not_or, not_not] at hn
  obtain ⟨h2, h3⟩ := hn
  exact h (Cobham.eventuallyPeriodic_of_isAutomatic le_rfl (by norm_num)
    (fun _ _ hm _ => Cobham.two_pow_ne_three_pow hm)
    (isAutomatic_of_isAlgebraic (p := 2)
      (AlgebraicDFinite.isAlgebraic_polynomial_of_isAlgebraic h2))
    (isAutomatic_of_isAlgebraic (p := 3)
      (AlgebraicDFinite.isAlgebraic_polynomial_of_isAlgebraic h3)))

end Rule30Equivalents.Christol
