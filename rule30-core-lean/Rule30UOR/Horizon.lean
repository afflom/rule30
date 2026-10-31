module
public import Rule30UOR.Interfaces.Part01
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Finite horizon certificates

`horizon-criterion` asks for an explicit `H(T, P)` such that `CenterPeriodic T P`
already fails on the window `[T, T + H)`. The rows are `Nat` bit-vectors
(`row`, `rowCenter`), so the kernel can evaluate the center column directly and
`decide` can certify a horizon for every transient and period below given
bounds. This module states the checker, proves it sound against
`CenterPeriodic`, and records the certificate `H = 32` for all `T ≤ 512` and
`0 < P ≤ 128`. Nothing here depends on an experiment: the certificate is a
kernel-checked theorem under `propext` and `Quot.sound` only. -/

@[expose] public section

namespace Rule30UOR.Horizon

open Rule30UOR.Core

/-- The center disagrees with its lag-`P` shift at some time in `[T, T + H)`. -/
def centerDisagreesWithin (T P H : Nat) : Bool :=
  (List.range H).any fun i => rowCenter (T + i + P) != rowCenter (T + i)

/-- Every transient `T ≤ T0` and every period `0 < P ≤ P0` is refuted on a
window of length `H`. -/
def shortPeriodsFail (T0 P0 H : Nat) : Bool :=
  (List.range (T0 + 1)).all fun T =>
    (List.range P0).all fun p => centerDisagreesWithin T (p + 1) H

theorem rowCenter_eq_center (t : Nat) : rowCenter t = if center t then 1 else 0 := by
  have h : center t = rcenter t := by
    rw [Rule30UOR.Scale.center_eq_kit, Rule30UOR.Right.center_eq_rcenter]
  rw [rowCenter, Rule30UOR.Interfaces.bit_row_eq_rdiag, h]
  rfl

theorem rowCenter_congr {s t : Nat} (h : center s = center t) : rowCenter s = rowCenter t := by
  rw [rowCenter_eq_center, rowCenter_eq_center, h]

/-- Soundness of the window checker: a disagreement in the window is a witness
against the period, with its time in `[T, T + H)`. -/
theorem disagreement_of_checker (T P H : Nat) (h : centerDisagreesWithin T P H = true) :
    ∃ t, T ≤ t ∧ t < T + H ∧ ¬ center (t + P) = center t := by
  unfold centerDisagreesWithin at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi, hne⟩ := h
  rw [List.mem_range] at hi
  refine ⟨T + i, Nat.le_add_right T i, by cfomega, fun he => ?_⟩
  rw [bne_iff_ne] at hne
  exact hne (rowCenter_congr he)

theorem not_centerPeriodic_of_checker (T P H : Nat) (h : centerDisagreesWithin T P H = true) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P := by
  intro hc
  obtain ⟨t, ht, -, hne⟩ := disagreement_of_checker T P H h
  exact hne (hc t ht)

theorem checker_of_certificate (T0 P0 H T P : Nat) (hcert : shortPeriodsFail T0 P0 H = true)
    (hT : T ≤ T0) (hP0 : 0 < P) (hP : P ≤ P0) : centerDisagreesWithin T P H = true := by
  unfold shortPeriodsFail at hcert
  rw [List.all_eq_true] at hcert
  have h1 := hcert T (List.mem_range.2 (by cfomega))
  rw [List.all_eq_true] at h1
  have h2 := h1 (P - 1) (List.mem_range.2 (by cfomega))
  have : P - 1 + 1 = P := by cfomega
  rwa [this] at h2

/-- The kernel-checked certificate: horizon `32` for every transient up to `512`
and every period up to `128`. -/
theorem certificate_512_128_32 : shortPeriodsFail 512 128 32 = true := by
  decide

/-- An explicit horizon: for `T ≤ 512` and `0 < P ≤ 128`, the center disagrees
with its lag-`P` shift at a time in `[T, T + 32)`. -/
theorem horizon_thirty_two (T P : Nat) (hT : T ≤ 512) (hP0 : 0 < P) (hP : P ≤ 128) :
    ∃ t, T ≤ t ∧ t < T + 32 ∧ ¬ center (t + P) = center t :=
  disagreement_of_checker T P 32 (checker_of_certificate 512 128 32 T P certificate_512_128_32 hT hP0 hP)

/-- No center period up to `128` with transient up to `512`. -/
theorem no_center_period_512_128 (T P : Nat) (hT : T ≤ 512) (hP0 : 0 < P) (hP : P ≤ 128) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  not_centerPeriodic_of_checker T P 32 (checker_of_certificate 512 128 32 T P certificate_512_128_32 hT hP0 hP)

end Rule30UOR.Horizon
