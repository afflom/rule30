module

public import Rule30Equivalents.Cobham

/-!
# Automatic sequences are the uniformly morphic ones

Cobham's "little" theorem (1972): `f` is `k`-automatic iff it is
a coding `τ ∘ x` of a fixed point `x` of a `k`-uniform morphism `σ` of a finite alphabet, that is
`x (k n + d) = σ (x n) d` (`isAutomatic_iff_isUniformMorphic`).

* From an automatic `f`: the alphabet is `kernel → Bool`, the letter at `n` is the column
  `g ↦ g n` of the kernel, and `σ a d = (g ↦ a (Λ_d g))` with `Λ_d g = (m ↦ g (k m + d))`.
* From a morphism: `x (kᵉ n + r) = σᵉ(x n)_r` (`apply_pow_mul_add`), so every kernel element is
  `h ∘ x` for some `h : A → Bool`, and there are finitely many of those.

With Cobham's theorem, **Problem 1 holds iff `c` is not both a `2`-uniformly morphic and a
`3`-uniformly morphic sequence** (`problem1_iff_not_uniformMorphic_two_three`), and likewise for
any multiplicatively independent `a, b ≥ 2` (`problem1_iff_not_uniformMorphic`). This is the
uniform case of the statement for substitutions with multiplicatively independent Perron numbers;
the general case needs Durand's theorem.
-/

@[expose] public section

namespace Rule30Equivalents.UniformMorphic

open Ruliology.CellularAutomata Automatic

/-- `f` is `k`-uniformly morphic: `f = τ ∘ x` for a fixed point `x` of a `k`-uniform morphism `σ` of
a finite alphabet, `x (k n + d) = σ (x n) d`. -/
def IsUniformMorphic (k : ℕ) (f : ℕ → Bool) : Prop :=
  ∃ (A : Type) (_ : Finite A) (σ : A → Fin k → A) (x : ℕ → A) (τ : A → Bool),
    (∀ n (d : Fin k), x (k * n + d) = σ (x n) d) ∧ ∀ n, f n = τ (x n)

variable {k : ℕ}

/-- `σᵉ(a)_r`: the letter at `r < kᵉ` of the `e`-th image of `a`. -/
def iter {A : Type} (hk : 0 < k) (σ : A → Fin k → A) : ℕ → A → ℕ → A
  | 0, a, _ => a
  | e + 1, a, r => σ (iter hk σ e a (r / k)) ⟨r % k, Nat.mod_lt _ hk⟩

theorem apply_pow_mul_add {A : Type} (hk : 0 < k) {σ : A → Fin k → A} {x : ℕ → A}
    (hx : ∀ n (d : Fin k), x (k * n + d) = σ (x n) d) :
    ∀ e n r, r < k ^ e → x (k ^ e * n + r) = iter hk σ e (x n) r
  | 0, n, r, hr => by
    rw [pow_zero] at hr
    obtain rfl : r = 0 := by omega
    simp [iter]
  | e + 1, n, r, hr => by
    have hrk : r / k < k ^ e := by
      rw [Nat.div_lt_iff_lt_mul hk]
      rwa [pow_succ] at hr
    have e1 : k ^ (e + 1) * n + r =
        k * (k ^ e * n + r / k) + (⟨r % k, Nat.mod_lt _ hk⟩ : Fin k) := by
      have := Nat.div_add_mod r k
      simp only [pow_succ]
      rw [mul_add, ← mul_assoc, mul_comm k (k ^ e)]
      omega
    rw [e1, hx, apply_pow_mul_add hk hx e n (r / k) hrk]
    rfl

/-- **Cobham's little theorem.** -/
theorem isAutomatic_iff_isUniformMorphic (hk : 2 ≤ k) (f : ℕ → Bool) :
    IsAutomatic k f ↔ IsUniformMorphic k f := by
  constructor
  · intro hf
    have : Finite (kernel k f) := hf.to_subtype
    -- the letter at `n` is the column of the kernel at `n`
    refine ⟨kernel k f → Bool, inferInstance,
      fun a d g => a ⟨fun m => g.1 (k * m + d), mem_kernel_step g.2 d.2⟩,
      fun n g => g.1 n, fun a => a ⟨f, self_mem_kernel k f⟩, fun n d => rfl, fun n => rfl⟩
  · rintro ⟨A, _, σ, x, τ, hx, hf⟩
    have hk0 : 0 < k := by omega
    refine (Set.finite_range fun h : A → Bool => h ∘ x).subset ?_
    rintro _ ⟨e, r, hr, rfl⟩
    refine ⟨fun a => τ (iter hk0 σ e a r), ?_⟩
    funext n
    simp only [Function.comp]
    rw [hf, apply_pow_mul_add hk0 hx e n r hr]

/-- **Cobham's theorem for uniform morphisms.** A sequence that is `a`-uniformly and `b`-uniformly
morphic, for multiplicatively independent `a, b ≥ 2`, is eventually periodic. -/
theorem eventuallyPeriodic_of_isUniformMorphic {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ m n, 0 < m → 0 < n → a ^ m ≠ b ^ n) {f : ℕ → Bool} (hfa : IsUniformMorphic a f)
    (hfb : IsUniformMorphic b f) : EventuallyPeriodic f :=
  Cobham.eventuallyPeriodic_of_isAutomatic ha hb hab
    ((isAutomatic_iff_isUniformMorphic ha f).2 hfa) ((isAutomatic_iff_isUniformMorphic hb f).2 hfb)

/-- **Uniform substitutions, any pair of bases.** For multiplicatively independent
`a, b ≥ 2`, Problem 1 holds iff the center column is not both `a`- and `b`-uniformly morphic. -/
theorem problem1_iff_not_uniformMorphic {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ m n, 0 < m → 0 < n → a ^ m ≠ b ^ n) : Rule30Prize.Problem1 ↔
    ¬ (IsUniformMorphic a Rule30Prize.center ∧ IsUniformMorphic b Rule30Prize.center) :=
  ⟨fun h1 h => h1 (eventuallyPeriodic_of_isUniformMorphic ha hb hab h.1 h.2),
    fun h hep => h ⟨(isAutomatic_iff_isUniformMorphic ha _).1
      (isAutomatic_of_eventuallyPeriodic hep ha),
      (isAutomatic_iff_isUniformMorphic hb _).1 (isAutomatic_of_eventuallyPeriodic hep hb)⟩⟩

/-- **Uniform substitutions.** Problem 1 holds iff the center column is not both a
`2`-uniformly morphic and a `3`-uniformly morphic sequence. -/
theorem problem1_iff_not_uniformMorphic_two_three : Rule30Prize.Problem1 ↔
    ¬ (IsUniformMorphic 2 Rule30Prize.center ∧ IsUniformMorphic 3 Rule30Prize.center) := by
  rw [Cobham.problem1_iff_not_two_three_automatic, isAutomatic_iff_isUniformMorphic le_rfl,
    isAutomatic_iff_isUniformMorphic (by norm_num)]

end Rule30Equivalents.UniformMorphic
