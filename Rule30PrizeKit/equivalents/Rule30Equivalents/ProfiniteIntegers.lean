module

public import Rule30Equivalents.ShiftOrbit
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Periodic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions

/-!
# The profinite integers

In the 2-adic form of "no eventual period `2^k`" (`TwoAdicPeriods`), replacing `ℤ₂` by the
profinite integers `Ẑ` gives
back Problem 1. Mathlib has no `Ẑ`, so here it is the inverse limit of the rings `ℤ/(k+1)!ℤ`
(`Zhat`), a cofinal subsystem of all `ℤ/nℤ`: compatible sequences `x k < (k+1)!` with
`x (k+1) ≡ x k mod (k+1)!`, inside the product of the finite discrete spaces `Fin (k+1)!`. The
natural numbers embed by `n ↦ (n mod (k+1)!)ₖ` (`Zhat.ofNat`).

* `exists_continuous_extension_iff`: `u : ℕ → Bool` extends to a continuous function `Ẑ → Bool`
  iff it is periodic. A continuous function to `Bool` is constant on a neighbourhood of each point,
  which contains a cylinder over finitely many coordinates, hence over one coordinate `k` (the
  system is a chain). By compactness one `K` works everywhere, so the function reads only
  `x K`, and `u` has period `(K+1)!`. Conversely `x ↦ u (x k)` is continuous for `(k+1)!` a
  multiple of the period.
* **Problem 1 holds iff no tail of `c` extends to a continuous function on `Ẑ`**
  (`problem1_iff_no_continuous_extension`).
-/

@[expose] public section

namespace Rule30Equivalents.ProfiniteIntegers

open Ruliology.CellularAutomata Topology

/-- The profinite integers, as compatible sequences of residues modulo `(k+1)!`. -/
def Zhat : Set ((k : ℕ) → Fin (k + 1).factorial) :=
  {x | ∀ k, ((x (k + 1) : ℕ)) % (k + 1).factorial = x k}

namespace Zhat

/-- Compatibility between any two levels `j ≤ k`. -/
theorem mod_eq {x : (k : ℕ) → Fin (k + 1).factorial} (hx : x ∈ Zhat) {j k : ℕ} (hjk : j ≤ k) :
    (x k : ℕ) % (j + 1).factorial = x j := by
  induction k, hjk using Nat.le_induction with
  | base => exact Nat.mod_eq_of_lt (x j).2
  | succ k hjk ih =>
    rw [← ih, ← hx k, Nat.mod_mod_of_dvd _ (Nat.factorial_dvd_factorial (by omega))]

theorem isClosed : IsClosed Zhat := by
  rw [Zhat, Set.ofPred_forall]
  refine isClosed_iInter fun k => isClosed_eq
    (f := fun x : (k : ℕ) → Fin (k + 1).factorial => (x (k + 1) : ℕ) % (k + 1).factorial)
    (g := fun x => (x k : ℕ)) ?_ ?_
  · exact (continuous_of_discreteTopology (f := fun i : Fin (k + 1 + 1).factorial =>
      (i : ℕ) % (k + 1).factorial)).comp (continuous_apply (k + 1))
  · exact (continuous_of_discreteTopology (f := fun i : Fin (k + 1).factorial => (i : ℕ))).comp
      (continuous_apply k)

instance : CompactSpace Zhat := isCompact_iff_compactSpace.1 isClosed.isCompact

/-- The natural number `n` in `Ẑ`. -/
def ofNat (n : ℕ) : Zhat :=
  ⟨fun k => ⟨n % (k + 1).factorial, Nat.mod_lt _ (Nat.factorial_pos _)⟩, fun k =>
    Nat.mod_mod_of_dvd _ (Nat.factorial_dvd_factorial (by omega))⟩

end Zhat

/-- A continuous function on `Ẑ` with values in `Bool` reads one coordinate. -/
theorem exists_level {F : Zhat → Bool} (hF : Continuous F) :
    ∃ K, ∀ x y : Zhat, x.1 K = y.1 K → F x = F y := by
  classical
  -- around each point, `F` is constant on a cylinder over one coordinate
  have hloc : ∀ x : Zhat, ∃ k, ∀ y : Zhat, y.1 k = x.1 k → F y = F x := by
    intro x
    have hU : F ⁻¹' {F x} ∈ 𝓝 x :=
      hF.continuousAt.preimage_mem_nhds ((isOpen_discrete _).mem_nhds rfl)
    rw [mem_nhds_subtype] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    rw [nhds_pi, Filter.mem_pi] at hV
    obtain ⟨I, hI, t, ht, hIt⟩ := hV
    obtain ⟨k, hk⟩ := hI.bddAbove
    refine ⟨k, fun y hy => hVU (hIt fun i hi => ?_)⟩
    have hyi : y.1 i = x.1 i := by
      apply Fin.ext
      rw [← Zhat.mod_eq y.2 (hk hi), ← Zhat.mod_eq x.2 (hk hi), hy]
    rw [hyi]
    exact mem_of_mem_nhds (ht i)
  choose k hk using hloc
  -- finitely many cylinders cover `Ẑ`
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover
    (fun x : Zhat => {y : Zhat | y.1 (k x) = x.1 (k x)}) fun x _ => by
      have hc : Continuous fun y : Zhat => y.1 (k x) :=
        (continuous_apply (k x)).comp continuous_subtype_val
      exact IsOpen.mem_nhds ((isOpen_discrete {x.1 (k x)}).preimage hc) rfl
  obtain ⟨K, hK⟩ : ∃ K, ∀ x ∈ s, k x ≤ K := ⟨s.sup k, fun x hx => Finset.le_sup hx⟩
  refine ⟨K, fun y y' hyy' => ?_⟩
  obtain ⟨x, hxs, hyx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  have hy'x : y'.1 (k x) = x.1 (k x) := by
    rw [← hyx]
    apply Fin.ext
    rw [← Zhat.mod_eq y.2 (hK x hxs), ← Zhat.mod_eq y'.2 (hK x hxs), hyy']
  rw [hk x y hyx, hk x y' hy'x]

/-- **Continuous on `Ẑ` ⟺ periodic.** A bit sequence extends to a continuous function on the
profinite integers iff it is periodic. -/
theorem exists_continuous_extension_iff (u : ℕ → Bool) :
    (∃ F : Zhat → Bool, Continuous F ∧ ∀ n, F (Zhat.ofNat n) = u n) ↔
      ∃ P, 0 < P ∧ ∀ t, u (t + P) = u t := by
  constructor
  · rintro ⟨F, hF, hFu⟩
    obtain ⟨K, hK⟩ := exists_level hF
    refine ⟨(K + 1).factorial, Nat.factorial_pos _, fun t => ?_⟩
    rw [← hFu, ← hFu]
    refine hK _ _ (Fin.ext ?_)
    show (t + (K + 1).factorial) % (K + 1).factorial = t % (K + 1).factorial
    exact Nat.add_mod_right _ _
  · rintro ⟨P, hP, hper⟩
    refine ⟨fun x => u (x.1 (P - 1)), ?_, fun n => ?_⟩
    · exact (continuous_of_discreteTopology (f := fun i : Fin (P - 1 + 1).factorial =>
        u i)).comp ((continuous_apply (P - 1)).comp continuous_subtype_val)
    · show u (n % (P - 1 + 1).factorial) = u n
      have hmul : ∀ m t, u (t + P * m) = u t := by
        intro m
        induction m with
        | zero => intro t; simp
        | succ m ih => intro t; rw [Nat.mul_succ, ← add_assoc, hper, ih]
      have hper' : Function.Periodic u (P - 1 + 1).factorial := by
        rw [Nat.sub_add_cancel hP]
        obtain ⟨m, hm⟩ := Nat.dvd_factorial hP le_rfl
        intro t
        rw [hm]
        exact hmul m t
      exact hper'.map_mod_nat n

/-- **Problem 1 in `Ẑ`.** Problem 1 holds iff no tail of the center column extends to a continuous
function on the profinite integers. -/
theorem problem1_iff_no_continuous_extension : Rule30Prize.Problem1 ↔
    ∀ T, ¬ ∃ F : Zhat → Bool, Continuous F ∧ ∀ n, F (Zhat.ofNat n) = c (T + n) := by
  rw [problem1_iff_not_eventuallyPeriodic]
  refine (not_congr ?_).trans not_exists
  constructor
  · rintro ⟨T, P, hP, hper⟩
    refine ⟨T, (exists_continuous_extension_iff fun n => c (T + n)).2 ⟨P, hP, fun t => ?_⟩⟩
    show c (T + (t + P)) = c (T + t)
    rw [← add_assoc]
    exact hper _ (by omega)
  · rintro ⟨T, h⟩
    obtain ⟨P, hP, hper⟩ := (exists_continuous_extension_iff fun n => c (T + n)).1 h
    refine ⟨T, P, hP, fun t ht => ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = T + s := ⟨t - T, by omega⟩
    have := hper s
    rwa [add_assoc]

end Rule30Equivalents.ProfiniteIntegers
