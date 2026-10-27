module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Strassmann's theorem

A power series `f(x) = ∑ bⱼ xʲ` over `ℚ_[p]` whose coefficients tend to `0` converges on the closed
unit ball. If some coefficient is nonzero, `f` has only finitely many zeros there: at most `N`,
where `N` is the last index of a coefficient of largest norm. This is the analytic input of the
`p`-adic proof of the Skolem–Mahler–Lech theorem (`SkolemMahlerLech`).

* `psum b x`: the sum `∑' j, b j * x ^ j`.
* `psum_sub_psum`: `f(x) − f(α) = (x − α) · g(x)`, where `g = quot b α` has coefficients
  `gᵢ = ∑_{j ≥ 0} b_{i+1+j} αʲ`.
* `exists_zeros_subset`: if the coefficients tend to `0` and `N` is the last index of largest norm,
  the zeros in the closed unit ball lie in a finite set of size at most `N`. By induction on `N`:
  for `N = 0` the constant term dominates; otherwise divide by `x − α` at a zero `α`, which lowers
  the index by one.
* `strassmann`, `eq_zero_of_infinite_natCast_zeros`.

Sources: R. Strassmann, *Über den Wertevorrat von Potenzreihen im Gebiet der p-adischen Zahlen*,
J. Reine Angew. Math. 159 (1928) 13–28; F. Q. Gouvêa, *p-adic Numbers*, Theorem 4.4.6.
-/

@[expose] public section

namespace Rule30Equivalents.Strassmann

open Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

/-! ### Ultrametric summation -/

/-- An ultrametric `tsum` is bounded by any bound on its terms. -/
theorem norm_tsum_le {ι : Type*} {f : ι → ℚ_[p]} (hf : Summable f) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖f i‖ ≤ C) : ‖∑' i, f i‖ ≤ C := by
  have hs : ∀ s : Finset ι, ‖∑ i ∈ s, f i‖ ≤ C := fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp hf.hasSum) hs

/-- A family on `ℕ × ℕ`, zero above the diagonal and bounded in row `j` by a sequence tending to
`0`, is summable. -/
theorem summable_of_rows {ψ : ℕ × ℕ → ℚ_[p]} {g : ℕ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (h : ∀ j i, ‖ψ (j, i)‖ ≤ g j) (hz : ∀ j i, j < i → ψ (j, i) = 0) : Summable ψ := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 hg) ε hε
  rw [Filter.eventually_cofinite]
  refine ((Finset.range J ×ˢ Finset.range J : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).toFinite.subset ?_
  rintro ⟨j, i⟩ hji
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hji
  have hj : j < J := by
    by_contra hj
    have := hJ j (not_lt.1 hj)
    rw [Real.dist_eq, sub_zero] at this
    linarith [h j i, le_abs_self (g j)]
  have hi : i ≤ j := by
    by_contra hi
    rw [hz j i (not_le.1 hi), norm_zero] at hji
    linarith
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  omega

/-! ### Power series on the unit ball -/

/-- The value `∑' j, b j * x ^ j` of a power series. -/
noncomputable def psum (b : ℕ → ℚ_[p]) (x : ℚ_[p]) : ℚ_[p] := ∑' j, b j * x ^ j

theorem summable_psum {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    Summable fun j => b j * x ^ j := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun j => ?_) (tendsto_zero_iff_norm_tendsto_zero.1 hb)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)

/-- The coefficients of `(f(x) − f(α)) / (x − α)`. -/
noncomputable def quot (b : ℕ → ℚ_[p]) (α : ℚ_[p]) (i : ℕ) : ℚ_[p] :=
  ∑' j, b (i + 1 + j) * α ^ j

theorem tendsto_shift {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) (i : ℕ) :
    Tendsto (fun j => b (i + 1 + j)) atTop (𝓝 0) :=
  hb.comp (tendsto_atTop_atTop.2 fun J => ⟨J, fun j hj => by omega⟩)

theorem norm_quot_le {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) {α : ℚ_[p]} (hα : ‖α‖ ≤ 1)
    {i : ℕ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ j, i < j → ‖b j‖ ≤ C) : ‖quot b α i‖ ≤ C := by
  refine norm_tsum_le (summable_psum (tendsto_shift hb i) hα) hC fun j => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hα)).trans
    (h _ (by omega))

theorem tendsto_quot {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) {α : ℚ_[p]} (hα : ‖α‖ ≤ 1) :
    Tendsto (quot b α) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 (tendsto_zero_iff_norm_tendsto_zero.1 hb)) (ε / 2)
    (by linarith)
  refine ⟨J, fun i hi => ?_⟩
  have := norm_quot_le hb hα (i := i) (C := ε / 2) (by linarith) fun j hj => by
    have := hJ j (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- **Division by `x − α`**: `f(x) − f(α) = (x − α) · ∑ᵢ gᵢ xⁱ`. -/
theorem psum_sub_psum {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) {x α : ℚ_[p]}
    (hx : ‖x‖ ≤ 1) (hα : ‖α‖ ≤ 1) :
    psum b x - psum b α = (x - α) * psum (quot b α) x := by
  set ψ : ℕ → ℕ → ℚ_[p] := fun j i => if i < j then b j * (x ^ i * α ^ (j - 1 - i)) else 0
  have hψ : ∀ j i, ‖ψ j i‖ ≤ ‖b j‖ := fun j i => by
    simp only [ψ]
    split_ifs
    · rw [norm_mul, norm_mul, norm_pow, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _)
        ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
          (pow_le_one₀ (norm_nonneg _) hx)).trans (pow_le_one₀ (norm_nonneg _) hα))
    · rw [norm_zero]; exact norm_nonneg _
  have hsum : Summable (Function.uncurry ψ) :=
    summable_of_rows (tendsto_zero_iff_norm_tendsto_zero.1 hb) (fun j i => hψ j i)
      fun j i hji => by simp only [Function.uncurry_apply_pair, ψ,
          ite_eq_right (by omega : ¬ i < j)]
  have hrow : ∀ j, ∑' i, ψ j i = b j * ∑ i ∈ range j, x ^ i * α ^ (j - 1 - i) := fun j => by
    rw [tsum_eq_sum (s := range j) fun i hi => by
      simp only [ψ, ite_eq_right (by simpa using hi : ¬ i < j)], Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by simp [ψ, Finset.mem_range.1 hi]
  have hcol : ∀ i, ∑' j, ψ j i = x ^ i * quot b α i := fun i => by
    have hc : Summable fun j => ψ j i := hsum.prod_symm.prod_factor i
    rw [← hc.sum_add_tsum_nat_add (i + 1)]
    rw [Finset.sum_eq_zero fun j hj => by
      simp only [ψ, ite_eq_right (by simp at hj; omega : ¬ i < j)], zero_add, quot,
      ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [ψ, ite_eq_left (by omega : i < j + (i + 1)),
      show j + (i + 1) - 1 - i = j by omega, show i + 1 + j = j + (i + 1) by omega]
    ring
  have hleft : psum b x - psum b α = (x - α) * ∑' j, ∑' i, ψ j i := by
    rw [psum, psum, ← (summable_psum hb hx).tsum_sub (summable_psum hb hα), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hrow, mul_left_comm, mul_comm (x - α), geom_sum₂_mul, mul_sub]
  rw [hleft, ← hsum.tsum_comm' (fun j => hsum.prod_factor j) fun i => hsum.prod_symm.prod_factor i]
  simp only [hcol, psum]
  congr 1
  exact tsum_congr fun i => mul_comm _ _

/-! ### Counting zeros -/

/-- A sequence tending to `0` and staying below `c > 0` past `N` stays below some `c' < c`. -/
theorem exists_lt_bound {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) {N : ℕ} {c : ℝ} (hc : 0 < c)
    (h : ∀ j, N < j → ‖b j‖ < c) : ∃ c', c' < c ∧ 0 ≤ c' ∧ ∀ j, N < j → ‖b j‖ ≤ c' := by
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 (tendsto_zero_iff_norm_tendsto_zero.1 hb)) (c / 2)
    (by linarith)
  have hJ' : ∀ j, J ≤ j → ‖b j‖ < c / 2 := fun j hj => by
    have := hJ j hj
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  set m := (range (J + 1)).sup' nonempty_range_add_one fun j => ‖b (N + 1 + j)‖
  refine ⟨max (c / 2) m, max_lt (by linarith) ((Finset.sup'_lt_iff _).2 fun j _ => h _ (by omega)),
    le_max_of_le_left (by linarith), fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = N + 1 + k := ⟨j - (N + 1), by omega⟩
  by_cases hk : k ≤ J
  · exact le_max_of_le_right (Finset.le_sup' (fun j => ‖b (N + 1 + j)‖)
      (Finset.mem_range.2 (by omega)))
  · exact le_max_of_le_left (hJ' _ (by omega)).le

/-- The last index of a coefficient of largest norm. -/
theorem exists_max_index {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) (h0 : ∃ j, b j ≠ 0) :
    ∃ N, b N ≠ 0 ∧ (∀ j, ‖b j‖ ≤ ‖b N‖) ∧ ∀ j, N < j → ‖b j‖ < ‖b N‖ := by
  obtain ⟨j₀, hj₀⟩ := h0
  have hε : 0 < ‖b j₀‖ := norm_pos_iff.2 hj₀
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 (tendsto_zero_iff_norm_tendsto_zero.1 hb)) _ hε
  have hJ' : ∀ j, J ≤ j → ‖b j‖ < ‖b j₀‖ := fun j hj => by
    have := hJ j hj
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  have hj₀J : j₀ < J := by
    by_contra h
    exact lt_irrefl _ (hJ' j₀ (not_lt.1 h))
  have hne : (range J).Nonempty := ⟨j₀, Finset.mem_range.2 hj₀J⟩
  set M := (range J).sup' hne fun j => ‖b j‖
  have hM : ∀ j, ‖b j‖ ≤ M := fun j => by
    by_cases hj : j < J
    · exact Finset.le_sup' (fun j => ‖b j‖) (Finset.mem_range.2 hj)
    · exact ((hJ' j (not_lt.1 hj)).trans_le (Finset.le_sup' (fun j => ‖b j‖)
        (Finset.mem_range.2 hj₀J))).le
  obtain ⟨j₁, hj₁, hj₁M⟩ := Finset.exists_mem_eq_sup' hne fun j => ‖b j‖
  set U := (range J).filter fun j => ‖b j‖ = M
  have hU : U.Nonempty := ⟨j₁, Finset.mem_filter.2 ⟨hj₁, hj₁M.symm⟩⟩
  set N := U.max' hU
  have hN : ‖b N‖ = M := (Finset.mem_filter.1 (U.max'_mem hU)).2
  have hMpos : 0 < M := hε.trans_le (hM j₀)
  refine ⟨N, norm_pos_iff.1 (hN ▸ hMpos), fun j => hN ▸ hM j, fun j hj => ?_⟩
  rw [hN]
  refine lt_of_le_of_ne (hM j) fun hjM => ?_
  have hjJ : j < J := by
    by_contra h
    exact absurd ((hJ' j (not_lt.1 h)).trans_le (hM j₀)) (by rw [hjM]; exact lt_irrefl _)
  exact absurd (U.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjJ, hjM⟩)) (not_le.2 hj)

/-- If the constant term dominates, the series has the norm of its constant term on the unit
ball. -/
theorem norm_psum_eq {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) {c' : ℝ} (hc' : 0 ≤ c')
    (hlt : c' < ‖b 0‖) (h : ∀ j, 0 < j → ‖b j‖ ≤ c') {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    ‖psum b x‖ = ‖b 0‖ := by
  have hs := summable_psum hb hx
  rw [psum, hs.tsum_eq_zero_add, pow_zero, mul_one]
  have ht : ‖∑' j, b (j + 1) * x ^ (j + 1)‖ ≤ c' :=
    norm_tsum_le ((summable_nat_add_iff 1).2 hs) hc' fun j => by
      rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)).trans
        (h _ (by omega))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by linarith), max_eq_left (by linarith)]

/-- **Zeros of a power series**: if `N` is the last index of a coefficient of largest norm, the
zeros in the closed unit ball lie in a set of at most `N` points. -/
theorem exists_zeros_subset (N : ℕ) : ∀ b : ℕ → ℚ_[p], Tendsto b atTop (𝓝 0) →
    (∀ j, ‖b j‖ ≤ ‖b N‖) → (∀ j, N < j → ‖b j‖ < ‖b N‖) → b N ≠ 0 →
    ∃ Z : Finset ℚ_[p], Z.card ≤ N ∧ ∀ x, ‖x‖ ≤ 1 → psum b x = 0 → x ∈ Z := by
  classical
  induction N with
  | zero =>
    intro b hb _ hlt h0
    obtain ⟨c', hc'lt, hc'0, hc'⟩ := exists_lt_bound hb (norm_pos_iff.2 h0) hlt
    refine ⟨∅, by simp, fun x hx hfx => ?_⟩
    have := norm_psum_eq hb hc'0 hc'lt hc' hx
    rw [hfx, norm_zero] at this
    exact absurd this.symm (norm_ne_zero_iff.2 h0)
  | succ N ih =>
    intro b hb hle hlt h0
    by_cases hz : ∃ α, ‖α‖ ≤ 1 ∧ psum b α = 0
    · obtain ⟨α, hα, hfα⟩ := hz
      obtain ⟨c', hc'lt, hc'0, hc'⟩ := exists_lt_bound hb (norm_pos_iff.2 h0) hlt
      have hqN : ‖quot b α N‖ = ‖b (N + 1)‖ :=
        norm_psum_eq (b := fun j => b (N + 1 + j)) (tendsto_shift hb N) hc'0 hc'lt
          (fun j hj => hc' _ (by omega)) hα
      have hqle : ∀ i, ‖quot b α i‖ ≤ ‖quot b α N‖ := fun i =>
        (norm_quot_le hb hα (norm_nonneg _) fun j _ => hle j).trans_eq hqN.symm
      have hqlt : ∀ i, N < i → ‖quot b α i‖ < ‖quot b α N‖ := fun i hi =>
        hqN ▸ (norm_quot_le hb hα hc'0 fun j hj => hc' j (by omega)).trans_lt hc'lt
      have hq0 : quot b α N ≠ 0 := by
        rw [← norm_ne_zero_iff, hqN]
        exact norm_ne_zero_iff.2 h0
      obtain ⟨Z, hZ, hZx⟩ := ih _ (tendsto_quot hb hα) hqle hqlt hq0
      refine ⟨insert α Z, (Finset.card_insert_le _ _).trans (by omega), fun x hx hfx => ?_⟩
      have := psum_sub_psum hb hx hα
      rw [hfx, hfα, sub_zero, eq_comm, mul_eq_zero, sub_eq_zero] at this
      rcases this with rfl | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hZx x hx h)
    · push Not at hz
      exact ⟨∅, by simp, fun x hx hfx => absurd hfx (hz x hx)⟩

/-- **Strassmann's theorem**: a nonzero power series over `ℚ_[p]` with coefficients tending to
`0` has finitely many zeros in the closed unit ball. -/
theorem strassmann {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0)) (h0 : ∃ j, b j ≠ 0) :
    {x : ℚ_[p] | ‖x‖ ≤ 1 ∧ psum b x = 0}.Finite := by
  obtain ⟨N, hN0, hle, hlt⟩ := exists_max_index hb h0
  obtain ⟨Z, -, hZ⟩ := exists_zeros_subset N b hb hle hlt hN0
  exact Z.finite_toSet.subset fun x hx => hZ x hx.1 hx.2

/-- A power series with coefficients tending to `0` that vanishes at infinitely many natural
numbers is zero. -/
theorem eq_zero_of_infinite_natCast_zeros {b : ℕ → ℚ_[p]} (hb : Tendsto b atTop (𝓝 0))
    (h : {n : ℕ | psum b n = 0}.Infinite) (j : ℕ) : b j = 0 := by
  by_contra hj
  refine h (((strassmann hb ⟨j, hj⟩).preimage Nat.cast_injective.injOn).subset fun n hn => ?_)
  refine ⟨?_, hn⟩
  simpa using Padic.norm_int_le_one (p := p) n

end Rule30Equivalents.Strassmann
