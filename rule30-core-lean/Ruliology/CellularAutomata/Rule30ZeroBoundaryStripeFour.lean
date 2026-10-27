module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles3

/-!
# Stripe prefixes with four tail cells: death within `31` steps of arrival

For every `m` and every four-bit tail `v`, read from the boundary outwards (`tail4`), the start
`row4 m v` (the stripe at depths `1, …, m`, then `v`, then white) has its first deviation from the
stripe at some depth `d ≤ m + 6`, and depth `1` is white at some even time `≤ d - 1 + 31`. Every
class `(m mod 2, v)` is covered except `v = 13` with `m` odd. This carries `stripe_prefix_family`
(`Rule30ZeroBoundaryStripeFamily`) from tails of length at most `3` to length `4`, by the same
route: `family4_of_class`, the four-bit form of `family_of_class`, with one kernel-checked periodic
front-window orbit per class, from `Rule30Certificates.ZeroBoundaryStripeCycles0` – `3`. The
theorems live in the namespace `Rule30ZeroBoundaryStripeFront`.

* `stripe_four_tail`: the family, for `v : Fin 16` with `v ≠ 13` or `m` even.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeFront

open Rule30ZeroBoundaryStripeFront.StripeCycles0
open Rule30ZeroBoundaryStripeFront.StripeCycles1
open Rule30ZeroBoundaryStripeFront.StripeCycles2
open Rule30ZeroBoundaryStripeFront.StripeCycles3
open Rule30ZeroBoundary

/-- Four tail bits, read from the boundary outwards. -/
def tail4 (v i : Nat) : Bool := if i < 4 then v.testBit i else false

/-- A stripe prefix, four extra cells, and an infinite white tail. -/
def row4 (m v k : Nat) : Bool :=
  if k ≤ m then stripe k else tail4 v (k - m - 1)

def dev4 (q δ v : Nat) : Bool :=
  (List.range δ).all (fun j => j == 0 || tail4 v (j - 1) == stripe (q + j)) &&
    tail4 v (δ - 1) != stripe (q + δ)

theorem family4_of_class (m q δ lam v : Nat) (hq : m % 2 = q) (hδ : 1 ≤ δ)
    (hdev : dev4 q δ v = true)
    (hcyc : Cycle 32 31 (pk (fun i => tail4 v (δ - 1 + i)) 32) ((q + δ) % 2) lam) :
    (∀ k, 1 ≤ k → k < m + δ → row4 m v k = stripe k) ∧
      row4 m v (m + δ) ≠ stripe (m + δ) ∧
      ∃ t, t ≤ m + δ - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row4 m v) t 1 = false := by
  simp only [dev4, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hdev
  obtain ⟨hall, hne⟩ := hdev
  have hag : ∀ k, 1 ≤ k → k < m + δ → row4 m v k = stripe k := by
    intro k hk1 hk2
    unfold row4
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
    · rw [ite_eq_right hkm]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      rw [stripe_add_mod m q j hq, show m + j - m - 1 = j - 1 by omega]
      rcases hall j (by omega) with h | h
      · omega
      · exact h
  refine ⟨hag, ?_, ?_⟩
  · unfold row4
    rw [ite_eq_right (by omega), show m + δ - m - 1 = δ - 1 by omega,
      stripe_add_mod m q δ hq]
    exact hne
  · have hw : pk (fun i => row4 m v (m + δ + i)) 32 =
        pk (fun i => tail4 v (δ - 1 + i)) 32 :=
      pk_congr _ _ _ fun i _ => by
        unfold row4
        rw [ite_eq_right (by omega), show m + δ + i - m - 1 = δ - 1 + i by omega]
    have hp : (m + δ) % 2 = (q + δ) % 2 := by omega
    rw [← hw, ← hp] at hcyc
    obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m v) (m + δ) 32 31 lam
      (by omega) hag (by omega) hcyc
    exact ⟨m + δ - 1 + s, by omega, he, hz⟩

private theorem lt_sixteen_cases : ∀ v, v < 16 →
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨
      v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 := by
  decide

/-- **Stripe prefixes with four tail cells die.** For every `m` and every four-bit tail `v` but
`13` with `m` odd, the first deviation `d` of `S[1..m] · v · 0^∞` from the stripe satisfies
`d ≤ m + 6`, and depth `1` is white at some even time `t ≤ d - 1 + 31`. -/
theorem stripe_four_tail (m : Nat) (v : Fin 16) (hv : v.val ≠ 13 ∨ m % 2 = 0) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 6 ∧
      (∀ k, 1 ≤ k → k < d → row4 m v.val k = stripe k) ∧
      row4 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row4 m v.val) t 1 = false := by
  obtain ⟨v, hv16⟩ := v
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;>
    rcases lt_sixteen_cases v hv16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 4096 0 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 3 4096 1 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 16384 2 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_2_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 4096 3 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 65536 4 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_4_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 5 4096 5 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 5, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 4096 6 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_6_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 16384 7 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_3_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 32768 8 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_8)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 3 16384 9 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_2_1)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 8192 10 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_10)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 65536 11 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_5_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 16384 12 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_12)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 4 4096 13 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 65536 14 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_14)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 16384 15 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_7_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 4096 0 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 4096 1 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 4 4096 2 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 16384 3 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_3_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 16384 4 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_2_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 65536 5 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_5_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 3 4096 6 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 16384 7 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_7_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 65536 8 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_4_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 4096 9 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_9)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 6 4096 10 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 6, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 65536 11 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_11)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 4096 12 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_6_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · simp at hv
    omega
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 3 16384 14 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_3_0)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 16384 15 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_15)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩

end Rule30ZeroBoundaryStripeFront
end Ruliology.CellularAutomata
