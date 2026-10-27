module

public import Rule30Equivalents.TFunctionCycles
public import Ruliology.CellularAutomata.Rule30RightPeriods
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The right edge of rule 30 is a 2-adic odometer

In the frame of the right edge, the orbit closure of the single seed is the 2-adic odometer
(E. M. Coven, M. Pivato and R. Yassawi, *Prevalence of odometers in cellular automata*, Proc.
Amer. Math. Soc. 135 (2007) 815–821). This holds for every nonzero finite configuration, not only the seed.

`TFunction` writes rule 30 on finite configurations, in the frame of the right edge, as the map
`Φ` on `ℕ`: row `t` of `TFunction.row a`, read leftward from its right edge, is the binary
expansion of `Φ^t(a)` (`TFunction.testBit_orbit`).

* `G_bits`: on binary expansions `Φ` is `G(y)_j = y_j ⊕ (y_{j-1} ∨ y_{j-2})`, with
  `y_{-1} = y_{-2} = 0`.
* `G_bijective`, `agree_G_iff`: `G` is a bijection, and `G y`, `G y'` agree below `n` iff `y`, `y'`
  do. So `G` is an isometry of `{0,1}^ℕ` for the metric `2^-(first difference)`.
* `ψ a α j` is bit `j` of `Φ^(α mod 2^j)(a)`, for a 2-adic integer `α` (bit `j` of `Φ^t(a)` has
  period dividing `2^j` in `t`): `ψ_natCast` (`ψ a t` is the expansion of `Φ^t(a)`), `ψ_add_one`
  (`ψ a (α + 1) = G (ψ a α)`), `continuous_ψ`, `range_ψ` (the image is the orbit closure),
  `ψ_injective` and `isClosedEmbedding_ψ` for `a ≠ 0`. **So for every nonzero finite
  configuration `ψ a` is a homeomorphism from `ℤ₂` onto the orbit closure of its right-edge
  reading that conjugates `α ↦ α + 1` to rule 30.** Injectivity: if `ψ a α = ψ a β` with
  `α - β ∉ 2^m ℤ₂`, every bit of `Φ^t(a)` would repeat with period `2^(m-1)`, so
  `Φ^(2^(m-1))(a) = a`; but `Φ` strictly increases every nonzero number (`TFunctionCycles.lt_Phi`).
* The single seed (`a = 1`): `row t j = R j t`, `isClosedEmbedding_seed`, `range_seed`.

The finite levels are in `TFunctionCycles` (`seed_rows_return_iff`, `per_unbounded`). None of this
reaches the center column, which reads the moving coordinate `row t t`.
-/

@[expose] public section

namespace Rule30Equivalents.Odometer

open Ruliology.CellularAutomata

/-! ### Rule 30 in the frame of the right edge -/

/-- Rule 30 in the frame of its right edge: `G(y)_j = y_j ⊕ (y_{j-1} ∨ y_{j-2})`. -/
def G (y : ℕ → Bool) : ℕ → Bool
  | 0 => y 0
  | 1 => xor (y 1) (y 0)
  | j + 2 => xor (y (j + 2)) (y (j + 1) || y j)

/-- The inverse of `G`, solved from the lowest coordinate up. -/
def Ginv (z : ℕ → Bool) : ℕ → Bool
  | 0 => z 0
  | 1 => xor (z 1) (Ginv z 0)
  | j + 2 => xor (z (j + 2)) (Ginv z (j + 1) || Ginv z j)

theorem Ginv_one (z : ℕ → Bool) : Ginv z 1 = xor (z 1) (z 0) := rfl

theorem Ginv_add_two (z : ℕ → Bool) (j : ℕ) :
    Ginv z (j + 2) = xor (z (j + 2)) (Ginv z (j + 1) || Ginv z j) := rfl

theorem G_Ginv (z : ℕ → Bool) : G (Ginv z) = z := by
  funext j
  match j with
  | 0 => rfl
  | 1 => simp [G, Ginv]
  | j + 2 => simp [G, Ginv]

theorem Ginv_G_apply (y : ℕ → Bool) : ∀ j, Ginv (G y) j = y j
  | 0 => rfl
  | 1 => by rw [Ginv, Ginv_G_apply y 0]; simp [G]
  | j + 2 => by rw [Ginv, Ginv_G_apply y (j + 1), Ginv_G_apply y j]; simp [G]

theorem G_bijective : Function.Bijective G :=
  Function.bijective_iff_has_inverse.2
    ⟨Ginv, fun y => funext (Ginv_G_apply y), G_Ginv⟩

theorem Ginv_agree {z z' : ℕ → Bool} {n : ℕ} (h : ∀ j < n, z j = z' j) :
    ∀ j < n, Ginv z j = Ginv z' j
  | 0, hj => h 0 hj
  | 1, hj => by rw [Ginv_one, Ginv_one, h 1 hj, h 0 (by omega)]
  | j + 2, hj => by
    rw [Ginv_add_two, Ginv_add_two, h _ hj, Ginv_agree h (j + 1) (by omega),
      Ginv_agree h j (by omega)]

/-- **`G` is an isometry**: `G y` and `G y'` agree below `n` iff `y` and `y'` do. -/
theorem agree_G_iff (y y' : ℕ → Bool) (n : ℕ) :
    (∀ j < n, G y j = G y' j) ↔ ∀ j < n, y j = y' j := by
  constructor
  · intro h j hj
    have := Ginv_agree h j hj
    rwa [Ginv_G_apply, Ginv_G_apply] at this
  · intro h j hj
    match j with
    | 0 => exact h 0 hj
    | 1 => simp only [G]; rw [h 1 hj, h 0 (by omega)]
    | j + 2 => simp only [G]; rw [h _ hj, h (j + 1) (by omega), h j (by omega)]

/-! ### Binary expansions -/

/-- The binary expansion of `x`, least significant bit first. -/
def bits (x : ℕ) : ℕ → Bool := fun j => x.testBit j

/-- **On binary expansions, `Φ` is `G`.** -/
theorem G_bits (x : ℕ) : G (bits x) = bits (TFunction.Phi x) := by
  funext j
  simp only [bits, TFunction.testBit_Phi, TFunction.low]
  match j with
  | 0 => simp [G, bits, Nat.testBit_zero]
  | 1 => simp [G, bits, Nat.testBit_zero]
  | j + 2 => simp [G, bits]

/-- Bit `j` of `Φ^t(a)` only sees `t mod 2^j`. -/
theorem testBit_orbit_mod (a j n : ℕ) :
    (TFunction.orbit a (n % 2 ^ j)).testBit j = (TFunction.orbit a n).testBit j := by
  have h := TFunction.testBit_orbit_periodic_mul a j (n / 2 ^ j) (n % 2 ^ j)
  rw [mul_comm, Nat.mod_add_div] at h
  exact h.symm

theorem testBit_val_eq (a : ℕ) {j : ℕ} {x : ZMod (2 ^ j)} {y : ℕ} (h : x = y) :
    (TFunction.orbit a x.val).testBit j = (TFunction.orbit a y).testBit j := by
  rw [h, ZMod.val_natCast, testBit_orbit_mod]

theorem val_toZModPow_mod {m n : ℕ} (h : m ≤ n) (α : ℤ_[2]) :
    (PadicInt.toZModPow m α).val = (PadicInt.toZModPow n α).val % 2 ^ m := by
  rw [← PadicInt.cast_toZModPow m n h, ZMod.cast_eq_val, ZMod.val_natCast]

/-! ### The 2-adic parametrization -/

/-- The point of the orbit closure of `a` at the 2-adic time `α`: bit `j` of `Φ^(α mod 2^j)(a)`. -/
noncomputable def ψ (a : ℕ) (α : ℤ_[2]) : ℕ → Bool :=
  fun j => (TFunction.orbit a (PadicInt.toZModPow j α).val).testBit j

/-- At natural times `ψ a` is the orbit of `a`. -/
theorem ψ_natCast (a t : ℕ) : ψ a (t : ℤ_[2]) = bits (TFunction.orbit a t) := by
  funext j
  simp only [ψ, bits, map_natCast, ZMod.val_natCast, testBit_orbit_mod]

/-- **`ψ a` conjugates `α ↦ α + 1` to rule 30.** -/
theorem ψ_add_one (a : ℕ) (α : ℤ_[2]) : ψ a (α + 1) = G (ψ a α) := by
  funext j
  set A := (PadicInt.toZModPow j α).val with hA
  have h1 : ψ a (α + 1) j = (TFunction.orbit a (A + 1)).testBit j :=
    testBit_val_eq a (by rw [map_add, map_one, Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one])
  -- `ψ a α` agrees with the expansion of `Φ^A(a)` up to bit `j`
  have hag : ∀ i < j + 1, ψ a α i = bits (TFunction.orbit a A) i := fun i hi => by
    simp only [ψ, bits, hA]
    rw [val_toZModPow_mod (show i ≤ j by omega), testBit_orbit_mod]
  rw [h1, (agree_G_iff _ _ (j + 1)).2 hag j (by omega), G_bits]
  rfl

theorem continuous_ψ (a : ℕ) : Continuous (ψ a) := by
  refine continuous_pi fun j => IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro α
  filter_upwards [Metric.closedBall_mem_nhds α (zpow_pos (by norm_num : (0 : ℝ) < 2) (-(j : ℤ)))]
    with β hβ
  have hmem : β - α ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ j} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [Metric.mem_closedBall, dist_eq_norm] at hβ
    exact_mod_cast hβ
  have h0 : PadicInt.toZModPow j (β - α) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact_mod_cast hmem
  rw [map_sub, sub_eq_zero] at h0
  simp only [ψ, h0]

/-- **`ψ a` is injective for `a ≠ 0`**: `Φ` strictly increases every nonzero number, so no bit
pattern of `Φ^t(a)` can repeat with a bounded period. -/
theorem ψ_injective {a : ℕ} (ha : a ≠ 0) : Function.Injective (ψ a) := by
  intro α β hαβ
  by_contra hne
  have hn : ∀ n : ℕ, ψ a (α + n) = ψ a (β + n) := by
    intro n
    induction n with
    | zero => simpa using hαβ
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, ← add_assoc, ψ_add_one, ψ_add_one, ih]
  -- a level `2^m` that separates `α` and `β`
  obtain ⟨m, hm⟩ : ∃ m, α - β ∉ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ m} := by
    by_contra hall
    push Not at hall
    apply hne
    have hle : ∀ m : ℕ, ‖α - β‖ ≤ (1 / 2 : ℝ) ^ m := fun m => by
      have := (PadicInt.norm_le_pow_iff_mem_span_pow (α - β) m).2 (hall m)
      rw [zpow_neg, zpow_natCast] at this
      rw [one_div, inv_pow]
      exact_mod_cast this
    have h0 : ‖α - β‖ = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
      linarith [hle m]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm
    · exact h
  -- every bit of `Φ^t(a)` repeats with period `2^(m - 1)`
  have hper : ∀ j, Rule30RightPeriods.PerF (fun t => (TFunction.orbit a t).testBit j)
      (2 ^ (m - 1)) := by
    intro j
    by_cases hj : m ≤ j
    · set A := PadicInt.toZModPow j α with hA
      set B := PadicInt.toZModPow j β with hB
      set D := PadicInt.toZModPow j (α - β) with hD
      have hDAB : D = A - B := by rw [hD, map_sub]
      have hBlt : B.val < 2 ^ j := ZMod.val_lt B
      have h2j : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self _
      have hinv : Rule30RightPeriods.PerF (fun t => (TFunction.orbit a t).testBit j) D.val := by
        intro t
        have h := congrFun (hn (t + (2 ^ j - B.val))) j
        simp only [ψ, map_add, map_natCast] at h
        rw [← hA, ← hB] at h
        rw [testBit_val_eq a (y := t + D.val) (by
            rw [hDAB, Nat.cast_add, Nat.cast_sub hBlt.le, h2j, Nat.cast_add,
              ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
            ring),
          testBit_val_eq a (y := t + 2 ^ j) (by
            rw [Nat.cast_add, Nat.cast_sub hBlt.le, h2j, Nat.cast_add, h2j, ZMod.natCast_zmod_val]
            ring)] at h
        simp only
        rw [h, TFunction.testBit_orbit_periodic]
      have hg := Rule30RightPeriods.PerF.gcd D.val (2 ^ j) hinv
        (fun t => TFunction.testBit_orbit_periodic a j t)
      obtain ⟨w, hwj, hw⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_right D.val (2 ^ j))
      have hwm : w ≤ m - 1 := by
        by_contra hwm
        apply hm
        have hdvd : 2 ^ m ∣ D.val :=
          (pow_dvd_pow 2 (by omega)).trans (hw ▸ Nat.gcd_dvd_left D.val (2 ^ j))
        have h0 : PadicInt.toZModPow m (α - β) = 0 := by
          rw [← PadicInt.cast_toZModPow m j hj, ← hD, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
          exact_mod_cast hdvd
        rw [← PadicInt.ker_toZModPow]
        exact h0
      rw [hw] at hg
      have := hg.mul (2 ^ (m - 1 - w))
      rwa [← pow_add, Nat.sub_add_cancel hwm] at this
    · have := Rule30RightPeriods.PerF.mul (f := fun t => (TFunction.orbit a t).testBit j)
        (p := 2 ^ j) (fun t => TFunction.testBit_orbit_periodic a j t) (2 ^ (m - 1 - j))
      rwa [← pow_add, Nat.sub_add_cancel (by omega)] at this
  -- so `Φ^(2^(m-1))(a) = a`, against `a < Φ^(2^(m-1))(a)`
  have heq : TFunction.orbit a (2 ^ (m - 1)) = a :=
    Nat.eq_of_testBit_eq fun j => by simpa [TFunction.orbit] using hper j 0
  have hlt := TFunctionCycles.lt_iterate_Phi ha (2 ^ (m - 1)) Nat.one_le_two_pow
  rw [← TFunctionCycles.orbit_eq_iterate, heq] at hlt
  exact lt_irrefl a hlt

/-- **The orbit closure.** The image of `ψ a` is the closure of the orbit of `a`. -/
theorem range_ψ (a : ℕ) :
    Set.range (ψ a) = closure (Set.range fun t => bits (TFunction.orbit a t)) := by
  apply le_antisymm
  · rintro _ ⟨α, rfl⟩
    have hd := PadicInt.denseRange_natCast (p := 2)
    have : ψ a α ∈ closure (ψ a '' Set.range (Nat.cast : ℕ → ℤ_[2])) :=
      image_closure_subset_closure_image (continuous_ψ a)
        ⟨α, by rw [hd.closure_eq]; exact Set.mem_univ α, rfl⟩
    rwa [← Set.range_comp, show ψ a ∘ (Nat.cast : ℕ → ℤ_[2]) = fun t => bits (TFunction.orbit a t)
      from funext (ψ_natCast a)] at this
  · refine closure_minimal ?_ (isCompact_range (continuous_ψ a)).isClosed
    rintro _ ⟨t, rfl⟩
    exact ⟨t, ψ_natCast a t⟩

/-- **The 2-adic odometer**: for every nonzero finite configuration, `ψ a` is a closed embedding
of `ℤ₂` onto the orbit closure of its right-edge reading, conjugating `α ↦ α + 1` to rule 30. -/
theorem isClosedEmbedding_ψ {a : ℕ} (ha : a ≠ 0) : Topology.IsClosedEmbedding (ψ a) :=
  (continuous_ψ a).isClosedEmbedding (ψ_injective ha)

/-! ### The single seed -/

/-- Row `t` of the single seed, read leftward from its right edge. -/
def row (t : ℕ) : ℕ → Bool := fun j => Rule30Diagonals.R j t

theorem bits_orbit_one (t : ℕ) : bits (TFunction.orbit 1 t) = row t := by
  have hseed : TFunction.row 1 = Rule30Realization.seed := by
    funext p
    simp only [TFunction.row, Rule30Realization.seed]
    by_cases hp : p ≤ 0
    · rw [ite_eq_left hp]
      by_cases hp0 : p = 0
      · subst hp0
        rfl
      · rw [decide_eq_false hp0]
        obtain ⟨n, hn⟩ : ∃ n, (-p).toNat = n + 1 := ⟨(-p).toNat - 1, by omega⟩
        rw [hn, Nat.testBit_succ]
        simp
    · rw [ite_eq_right hp, decide_eq_false (by omega)]
  funext j
  simp only [bits, row, TFunction.testBit_orbit, hseed, Rule30Realization.evol_seed,
    Rule30Diagonals.R]

/-- Rule 30 acts on the rows of the seed as `G`. -/
theorem G_row (t : ℕ) : G (row t) = row (t + 1) := by
  rw [← bits_orbit_one, ← bits_orbit_one, G_bits]
  rfl

theorem isClosedEmbedding_seed : Topology.IsClosedEmbedding (ψ 1) :=
  isClosedEmbedding_ψ one_ne_zero

theorem range_seed : Set.range (ψ 1) = closure (Set.range row) := by
  rw [range_ψ]
  simp only [bits_orbit_one]

end Rule30Equivalents.Odometer
