module
public import Rule30UOR.KernelLaw
public import Rule30UOR.LeftBand
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The class obligation of a periodic center

On the residue class `t = 2^k u + r` (`k ≥ 3`, `r < 2^k`, `u ≥ 1`) the ruler background
`rulerBackground t` of the left band depends on `u` only through `trailingParity (u − 1)`,
and only on the residues `r = 1` and `r = 2`:

`rulerBackground (2^k u + r) = rulerBackground (2^k + r) ⊕ (trailingParity (u − 1) ∧ [r = 1 ∨ r = 2])`.

So under a center period `P`, the deep bulk `interiorEightDiagonal` is `P`-periodic in `u` on
every class except `r = 1` and `r = 2`, where it must reproduce the ruler one scale up. The
same bookkeeping on the kernel law gives the obligation of the late tail: its lag-`P`
difference is the ruler difference times the second prefix. -/

@[expose] public section

namespace Rule30UOR.ClassObligation

open Rule30UOR.Core Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Automatic
  Rule30UOR.Band Rule30UOR.LeftBand Rule30UOR.DyadicRow Rule30UOR.KernelLaw

/-! ## Dyadic bookkeeping -/

theorem twopow_add_three (j : Nat) : twopow (j + 3) = twopow (j + 2) + twopow (j + 2) := rfl

theorem twopow_add_two (j : Nat) : twopow (j + 2) = twopow (j + 1) + twopow (j + 1) := rfl

theorem twopow_add_one (j : Nat) : twopow (j + 1) = twopow j + twopow j := rfl

theorem two_le_twopow_add_one (j : Nat) : 2 ≤ twopow (j + 1) := by
  rw [twopow_add_one]
  have := Rule30UOR.Scale.twopow_pos j
  cfomega

theorem four_le_twopow_add_two (j : Nat) : 4 ≤ twopow (j + 2) := by
  rw [twopow_add_two]
  have := two_le_twopow_add_one j
  cfomega

theorem eight_le_twopow_add_three (j : Nat) : 8 ≤ twopow (j + 3) := by
  rw [twopow_add_three]
  have := four_le_twopow_add_two j
  cfomega

theorem trailingParity_zero : trailingParity 0 = false := rfl

/-! ## The ruler terms on each residue class

With `t = 2^k u + r` the three rulers of `rulerBackground` read `t − 2`, `t − 4` and
`(t − 4) / 2`. Each is constant in `u` except on one or two residues, where it is the
ruler one scale up, `trailingParity (u − 1)`, twisted by a parity of `k`. -/

/-- `r = 0`: `t − 2 = 2 (2^(k−1) u − 1)` is even. -/
theorem lag2_zero (j u : Nat) : trailingParity (twopow (j + 3) * u - 2) = false := by
  rw [show twopow (j + 3) * u - 2 = 2 * (twopow (j + 2) * u - 1) by
      rw [twopow_add_three, Nat.add_mul]; cfomega,
    trailingParity_even]

/-- `r ≥ 2`: `t − 2 = (r − 2) + 2^k u` and `2^k ∤ r − 1`. -/
theorem lag2_ge_two (k r u : Nat) (hr : r < twopow k) (h2 : 2 ≤ r) :
    trailingParity (twopow k * u + r - 2) = trailingParity (r - 2) := by
  rw [show twopow k * u + r - 2 = (r - 2) + twopow k * u by cfomega]
  exact trailingParity_add_twopow_mul k (r - 2) u
    (by rw [show r - 2 + 1 = r - 1 by cfomega, Nat.mod_eq_of_lt (by cfomega : r - 1 < twopow k)]; cfomega)

/-- `r = 0`: `t − 4 = 2 (2^(k−1) u − 2)` is even. -/
theorem lag4_zero (j u : Nat) : trailingParity (twopow (j + 3) * u - 4) = false := by
  rw [show twopow (j + 3) * u - 4 = 2 * (twopow (j + 2) * u - 2) by
      rw [twopow_add_three, Nat.add_mul]; cfomega,
    trailingParity_even]

/-- `r = 1`: `t − 4 = (2^k − 3) + 2^k (u − 1)` and `2^k ∤ 2^k − 2`: constant. -/
theorem lag4_one (j u : Nat) (hu : 1 ≤ u) :
    trailingParity (twopow (j + 3) * u + 1 - 4) = trailingParity (twopow (j + 3) - 3) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by cfomega⟩
  have h8 := eight_le_twopow_add_three j
  rw [Nat.mul_add, Nat.mul_one,
    show twopow (j + 3) * v + twopow (j + 3) + 1 - 4 = (twopow (j + 3) - 3) + twopow (j + 3) * v by cfomega]
  exact trailingParity_add_twopow_mul (j + 3) (twopow (j + 3) - 3) v
    (by rw [show twopow (j + 3) - 3 + 1 = twopow (j + 3) - 2 by cfomega, Nat.mod_eq_of_lt (by cfomega)]; cfomega)

/-- `r = 2`: `t − 4 = 2 (2^(k−1) u − 1)` is even. -/
theorem lag4_two (j u : Nat) : trailingParity (twopow (j + 3) * u + 2 - 4) = false := by
  rw [show twopow (j + 3) * u + 2 - 4 = 2 * (twopow (j + 2) * u - 1) by
      rw [twopow_add_three, Nat.add_mul]; cfomega,
    trailingParity_even]

/-- `r ≥ 4`: `t − 4 = (r − 4) + 2^k u` and `2^k ∤ r − 3`. -/
theorem lag4_ge_four (k r u : Nat) (hr : r < twopow k) (h4 : 4 ≤ r) :
    trailingParity (twopow k * u + r - 4) = trailingParity (r - 4) := by
  rw [show twopow k * u + r - 4 = (r - 4) + twopow k * u by cfomega]
  exact trailingParity_add_twopow_mul k (r - 4) u
    (by rw [show r - 4 + 1 = r - 3 by cfomega, Nat.mod_eq_of_lt (by cfomega : r - 3 < twopow k)]; cfomega)

/-- `r = 0`: `(t − 4) / 2 = 2 (2^(k−2) u − 1)` is even. -/
theorem half_zero (j u : Nat) : trailingParity ((twopow (j + 3) * u - 4) / 2) = false := by
  rw [show (twopow (j + 3) * u - 4) / 2 = 2 * (twopow (j + 1) * u - 1) by
      rw [twopow_add_three, twopow_add_two]; simp only [Nat.add_mul]; cfomega,
    trailingParity_even]

/-- `r = 1`: `(t − 4) / 2 = 2 (2^(k−2) u − 1)` is even. -/
theorem half_one (j u : Nat) : trailingParity ((twopow (j + 3) * u + 1 - 4) / 2) = false := by
  rw [show (twopow (j + 3) * u + 1 - 4) / 2 = 2 * (twopow (j + 1) * u - 1) by
      rw [twopow_add_three, twopow_add_two]; simp only [Nat.add_mul]; cfomega,
    trailingParity_even]

/-- `r ≥ 4`: `(t − 4) / 2 = (r − 4) / 2 + 2^(k−1) u` and `2^(k−1) ∤ (r − 4) / 2 + 1`. -/
theorem half_ge_four (j r u : Nat) (hr : r < twopow (j + 3)) (h4 : 4 ≤ r) :
    trailingParity ((twopow (j + 3) * u + r - 4) / 2) = trailingParity ((r - 4) / 2) := by
  have hK := twopow_add_three j
  have h4' := four_le_twopow_add_two j
  rw [show (twopow (j + 3) * u + r - 4) / 2 = (r - 4) / 2 + twopow (j + 2) * u by
      rw [twopow_add_three, Nat.add_mul]; cfomega]
  exact trailingParity_add_twopow_mul (j + 2) ((r - 4) / 2) u
    (by rw [Nat.mod_eq_of_lt (by cfomega : (r - 4) / 2 + 1 < twopow (j + 2))]; cfomega)

/-! ## The ruler coefficient and the frozen background -/

/-- The residues on which the ruler background moves with `u`: `r = 1` and `r = 2`. -/
def rulerCoefficient (r : Nat) : Bool :=
  match r with
  | 1 => true
  | 2 => true
  | _ => false

theorem rulerCoefficient_zero : rulerCoefficient 0 = false := rfl

theorem rulerCoefficient_one : rulerCoefficient 1 = true := rfl

theorem rulerCoefficient_two : rulerCoefficient 2 = true := rfl

theorem rulerCoefficient_three : rulerCoefficient 3 = false := rfl

theorem rulerCoefficient_of_ge_four (r : Nat) (h4 : 4 ≤ r) : rulerCoefficient r = false := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by cfomega⟩
  rfl

theorem rulerCoefficient_eq_true (r : Nat) (h : r = 1 ∨ r = 2) : rulerCoefficient r = true := by
  rcases h with rfl | rfl <;> rfl

theorem rulerCoefficient_eq_false (r : Nat) (h1 : r ≠ 1) (h2 : r ≠ 2) : rulerCoefficient r = false := by
  rcases Nat.lt_or_ge r 4 with h4 | h4
  · rcases Nat.lt_or_ge r 2 with hl | hl
    · rcases Nat.lt_or_ge r 1 with hm | hm
      · obtain rfl : r = 0 := by cfomega
        rfl
      · obtain rfl : r = 1 := by cfomega
        exact absurd rfl h1
    · rcases Nat.lt_or_ge r 3 with hm | hm
      · obtain rfl : r = 2 := by cfomega
        exact absurd rfl h2
      · obtain rfl : r = 3 := by cfomega
        rfl
  · exact rulerCoefficient_of_ge_four r h4

/-- The frozen ruler background of the class `r` at scale `k`: its value at `u = 1`. -/
def frozenRuler (k r : Nat) : Bool := rulerBackground (twopow k + r)

/-- **The ruler background on the residue classes.** For `k ≥ 3`, `r < 2^k`, `u ≥ 1`:
`rulerBackground (2^k u + r) = frozenRuler k r ⊕ (trailingParity (u − 1) ∧ rulerCoefficient r)`.
Only the residues `1` and `2` move with `u`; on `r = 3` the two moving rulers cancel. -/
theorem rulerBackground_kernel (k r u : Nat) (hk : 3 ≤ k) (hr : r < twopow k) (hu : 1 ≤ u) :
    rulerBackground (twopow k * u + r) = bxor (frozenRuler k r) (trailingParity (u - 1) && rulerCoefficient r) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by cfomega⟩
  have hk1 : 1 ≤ j + 3 := by cfomega
  unfold frozenRuler rulerBackground
  rw [show twopow (j + 3) + r = twopow (j + 3) * 1 + r by rw [Nat.mul_one],
    timeParity_twopow_mul_add (j + 3) u r hk1, timeParity_twopow_mul_add (j + 3) 1 r hk1]
  rcases Nat.lt_or_ge r 4 with h4 | h4
  · rcases Nat.lt_or_ge r 2 with hl | hl
    · rcases Nat.lt_or_ge r 1 with hm | hm
      · obtain rfl : r = 0 := by cfomega
        simp only [Nat.add_zero]
        rw [lag2_zero, lag2_zero, lag4_zero, lag4_zero, half_zero, half_zero, rulerCoefficient_zero]
        cases timeParity 0 <;> cases trailingParity (u - 1) <;> rfl
      · obtain rfl : r = 1 := by cfomega
        rw [show twopow (j + 3) * u + 1 - 2 = twopow (j + 3) * u - 1 by cfomega,
          show twopow (j + 3) * 1 + 1 - 2 = twopow (j + 3) * 1 - 1 by cfomega,
          trailingParity_twopow_mul_sub_one (j + 3) u hu, trailingParity_twopow_mul_sub_one (j + 3) 1 (Nat.le_refl 1),
          lag4_one j u hu, lag4_one j 1 (Nat.le_refl 1), half_one, half_one, rulerCoefficient_one,
          Nat.sub_self 1, trailingParity_zero]
        cases decide ((j + 3) % 2 = 1) <;> cases timeParity 1 <;> cases trailingParity (twopow (j + 3) - 3) <;>
          cases trailingParity (u - 1) <;> rfl
    · rcases Nat.lt_or_ge r 3 with hm | hm
      · obtain rfl : r = 2 := by cfomega
        rw [lag2_ge_two (j + 3) 2 u hr hl, lag2_ge_two (j + 3) 2 1 hr hl, lag4_two, lag4_two,
          show (twopow (j + 3) * u + 2 - 4) / 2 = twopow (j + 2) * u - 1 by
            rw [twopow_add_three, Nat.add_mul]; cfomega,
          show (twopow (j + 3) * 1 + 2 - 4) / 2 = twopow (j + 2) * 1 - 1 by
            rw [twopow_add_three, Nat.add_mul]; cfomega,
          trailingParity_twopow_mul_sub_one (j + 2) u hu, trailingParity_twopow_mul_sub_one (j + 2) 1 (Nat.le_refl 1),
          rulerCoefficient_two, Nat.sub_self 1, trailingParity_zero]
        cases decide ((j + 2) % 2 = 1) <;> cases timeParity 2 <;> cases trailingParity (2 - 2) <;>
          cases trailingParity (u - 1) <;> rfl
      · obtain rfl : r = 3 := by cfomega
        rw [lag2_ge_two (j + 3) 3 u hr hl, lag2_ge_two (j + 3) 3 1 hr hl,
          show (twopow (j + 3) * u + 3 - 4) / 2 = twopow (j + 2) * u - 1 by
            rw [twopow_add_three, Nat.add_mul]; cfomega,
          show (twopow (j + 3) * 1 + 3 - 4) / 2 = twopow (j + 2) * 1 - 1 by
            rw [twopow_add_three, Nat.add_mul]; cfomega,
          trailingParity_twopow_mul_sub_one (j + 2) u hu, trailingParity_twopow_mul_sub_one (j + 2) 1 (Nat.le_refl 1),
          show twopow (j + 3) * u + 3 - 4 = twopow (j + 3) * u - 1 by cfomega,
          show twopow (j + 3) * 1 + 3 - 4 = twopow (j + 3) * 1 - 1 by cfomega,
          trailingParity_twopow_mul_sub_one (j + 3) u hu, trailingParity_twopow_mul_sub_one (j + 3) 1 (Nat.le_refl 1),
          rulerCoefficient_three, Nat.sub_self 1, trailingParity_zero]
        cases decide ((j + 3) % 2 = 1) <;> cases decide ((j + 2) % 2 = 1) <;> cases timeParity 3 <;>
          cases trailingParity (3 - 2) <;> cases trailingParity (u - 1) <;> rfl
  · rw [lag2_ge_two (j + 3) r u hr (by cfomega), lag2_ge_two (j + 3) r 1 hr (by cfomega),
      lag4_ge_four (j + 3) r u hr h4, lag4_ge_four (j + 3) r 1 hr h4,
      half_ge_four j r u hr h4, half_ge_four j r 1 hr h4, rulerCoefficient_of_ge_four r h4]
    cases timeParity r <;> cases trailingParity (r - 2) <;> cases trailingParity (r - 4) <;>
      cases trailingParity ((r - 4) / 2) <;> cases trailingParity (u - 1) <;> rfl

/-! ## The class obligation of the deep bulk -/

/-- The deep bulk on the class `r` at scale `k` is `P`-periodic in `u` from `T`. -/
def EightClassPeriodic (k r T P : Nat) : Prop :=
  ∀ u, T ≤ u → interiorEightDiagonal (twopow k * (u + P) + r) = interiorEightDiagonal (twopow k * u + r)

/-- The deep bulk on the class `r` at scale `k` reproduces the ruler one scale up across `P`. -/
def EightClassAgainstRuler (k r T P : Nat) : Prop :=
  ∀ u, T ≤ u → bxor (interiorEightDiagonal (twopow k * (u + P) + r)) (interiorEightDiagonal (twopow k * u + r)) =
    bxor (trailingParity (u + P - 1)) (trailingParity (u - 1))

theorem bxor_class_aux (F a' E' a E : Bool)
    (h : bxor (bxor F (a' && true)) E' = bxor (bxor F (a && true)) E) : bxor E' E = bxor a' a := by
  cases F <;> cases a' <;> cases E' <;> cases a <;> cases E <;> first | rfl | exact absurd h (by decide)

theorem bxor_offClass_aux (F a' E' a E : Bool)
    (h : bxor (bxor F (a' && false)) E' = bxor (bxor F (a && false)) E) : E' = E := by
  cases F <;> cases a' <;> cases E' <;> cases a <;> cases E <;> first | rfl | exact absurd h (by decide)

/-- The period `2^k P` of the center, read on the class `r` at scale `k`, in the ruler
background and the deep bulk. -/
theorem center_class_eq (T P k r u : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (hk : 3 ≤ k)
    (hr : r < twopow k) (hu : T + 1 ≤ u) :
    bxor (bxor (frozenRuler k r) (trailingParity (u + P - 1) && rulerCoefficient r))
        (interiorEightDiagonal (twopow k * (u + P) + r)) =
      bxor (bxor (frozenRuler k r) (trailingParity (u - 1) && rulerCoefficient r))
        (interiorEightDiagonal (twopow k * u + r)) := by
  have hu1 : 1 ≤ u := by cfomega
  have h8 : 8 ≤ twopow k := twopow_mono hk
  have hle : u ≤ twopow k * u := Nat.le_mul_of_pos_left u (Rule30UOR.Scale.twopow_pos k)
  have hle' : twopow k ≤ twopow k * (u + P) := Nat.le_mul_of_pos_right _ (by cfomega)
  have hle'' : twopow k ≤ twopow k * u := Nat.le_mul_of_pos_right _ hu1
  have h := centerPeriodic_twopow_mul T P k hc (twopow k * u + r) (by cfomega)
  rw [show twopow k * u + r + twopow k * P = twopow k * (u + P) + r by rw [Nat.mul_add]; cfomega,
    center_eq_rulerBackground_bxor_eight _ (by cfomega), center_eq_rulerBackground_bxor_eight _ (by cfomega),
    rulerBackground_kernel k r (u + P) hk hr (by cfomega), rulerBackground_kernel k r u hk hr hu1] at h
  exact h

/-- **The on-class obligation.** Under a center period `P`, on the residues `r = 1` and `r = 2`
at every scale `k ≥ 3`, the deep bulk reproduces the ruler one scale up with the same period. -/
theorem eightClass_of_centerPeriodic (T P k r : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (hk : 3 ≤ k)
    (hr : r < twopow k) (hr12 : r = 1 ∨ r = 2) : EightClassAgainstRuler k r (T + 1) P := by
  intro u hu
  have h := center_class_eq T P k r u hc hk hr hu
  rw [rulerCoefficient_eq_true r hr12] at h
  exact bxor_class_aux _ _ _ _ _ h

/-- **The off-class periodicity.** Under a center period `P`, on every residue other than `1`
and `2` at every scale `k ≥ 3`, the deep bulk is `P`-periodic in `u`. -/
theorem eightOffClass_of_centerPeriodic (T P k r : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (hk : 3 ≤ k)
    (hr : r < twopow k) (hnot : r ≠ 1) (hnot2 : r ≠ 2) : EightClassPeriodic k r (T + 1) P := by
  intro u hu
  have h := center_class_eq T P k r u hc hk hr hu
  rw [rulerCoefficient_eq_false r hnot hnot2] at h
  exact bxor_offClass_aux _ _ _ _ _ h

/-! ## The late-tail obligation -/

theorem bxor_lateTail_aux (p F a' S L' a L : Bool)
    (h : (!(bxor p (bxor (bxor F (a' && S)) L'))) = !(bxor p (bxor (bxor F (a && S)) L))) :
    bxor L' L = ((bxor a' a) && S) := by
  cases p <;> cases F <;> cases a' <;> cases S <;> cases L' <;> cases a <;> cases L <;>
    first | rfl | exact absurd h (by decide)

/-- **The kernel law under a period.** Under a center period `P`, the lag-`P` difference of the
late tail on the class `r` at scale `k` is the ruler difference times the second prefix. -/
theorem lateTail_obligation (T P k r u : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (hk : 1 ≤ k)
    (hr : r < twopow k) (hu : 1 ≤ u) (ht : T ≤ twopow k * u + r) :
    bxor (lateTail k r (u + P)) (lateTail k r u) =
      ((bxor (trailingParity (u + P - 1)) (trailingParity (u - 1))) && secondPrefix k r) := by
  have h1 := kernelSeq_explicit k r u hr hu hk
  have h2 := kernelSeq_explicit k r (u + P) hr (by cfomega) hk
  have h := centerPeriodic_twopow_mul T P k hc (twopow k * u + r) ht
  rw [show twopow k * u + r + twopow k * P = twopow k * (u + P) + r by rw [Nat.mul_add]; cfomega] at h
  unfold Rule30UOR.Automatic.kernelSeq at h1 h2
  rw [h1, h2] at h
  exact bxor_lateTail_aux _ _ _ _ _ _ _ h

/-! ## The late tail across one scale -/

theorem bxor_scale_zero_aux (C L2 B L1 : Bool) (h : bxor C L2 = bxor (bxor C B) L1) : L2 = bxor L1 B := by
  cases C <;> cases L2 <;> cases B <;> cases L1 <;> first | rfl | exact absurd h (by decide)

/-- **The late tail of the class `0` across one scale**: for `k ≥ 1`, `v ≥ 1`,
`lateTail k 0 (2v) = lateTail (k+1) 0 v ⊕ blockParity k`. -/
theorem lateTail_scale_zero (k v : Nat) (hk : 1 ≤ k) (hv : 1 ≤ v) :
    lateTail k 0 (2 * v) = bxor (lateTail (k + 1) 0 v) (blockParity k) := by
  have h1 := center_twopow_mul k (2 * v) hk (by cfomega)
  have h2 := center_twopow_mul (k + 1) v (by cfomega) hv
  have h3 := center_twopow_succ_eq k hk
  have he : twopow (k + 1) * v = twopow k * (2 * v) := by
    rw [twopow_succ, Nat.add_mul, Nat.mul_comm 2 v, ← Nat.mul_assoc]
    cfomega
  rw [he, h1, h3] at h2
  exact bxor_scale_zero_aux _ _ _ _ h2

theorem bxor_scale_aux (p F1 a S1 L1 F0 S0 L0 : Bool)
    (h : (!(bxor p (bxor (bxor F1 (a && S1)) L1))) = !(bxor p (bxor (bxor F0 ((!a) && S0)) L0))) :
    bxor L1 L0 = bxor (bxor F1 F0) (bxor (a && S1) ((!a) && S0)) := by
  cases p <;> cases F1 <;> cases a <;> cases S1 <;> cases L1 <;> cases F0 <;> cases S0 <;> cases L0 <;>
    first | rfl | exact absurd h (by decide)

/-- **The late tail across one scale, general residue**: for `k ≥ 1`, `r < 2^k`, `v ≥ 1`, the
late tails of `(k+1, r, v)` and `(k, r, 2v)` differ by the frozen prefixes and the second
prefixes read against the ruler `trailingParity (v − 1)` and its complement. -/
theorem lateTail_scale (k r v : Nat) (hk : 1 ≤ k) (hr : r < twopow k) (hv : 1 ≤ v) :
    bxor (lateTail (k + 1) r v) (lateTail k r (2 * v)) =
      bxor (bxor (frozenPrefix (k + 1) r) (frozenPrefix k r))
        (bxor (trailingParity (v - 1) && secondPrefix (k + 1) r)
          ((!(trailingParity (v - 1))) && secondPrefix k r)) := by
  have hr' : r < twopow (k + 1) := by rw [twopow_succ]; cfomega
  have h1 := kernelSeq_explicit (k + 1) r v hr' hv (by cfomega)
  have h2 := kernelSeq_explicit k r (2 * v) hr (by cfomega) hk
  have he := kernelSeq_even k r v
  rw [h1, h2, show 2 * v - 1 = 2 * (v - 1) + 1 by cfomega, trailingParity_odd] at he
  exact bxor_scale_aux _ _ _ _ _ _ _ _ he

/-! ## The second-order term on the residues `2` and `3`

`second k r m = bit (2^(k+1) + r) of Y ⊕ bit r of Y` with `Y = q^(2^k + r − 1 − m) · (interior m <<< 1)`.
For `m = 0` both bits are coefficients of `q^(2^k + r − 1)` mirrored by palindromy, so they cancel.
For `m ≥ 1` the interior mask has bits `0, 1` empty and bits `2m − 2 .. 2m` empty, so `Y` lives
below bit `2^(k+1) + 2r − 3` (the high bit vanishes for `r ≤ 3`) and the low bit `r ≤ 3` of `Y`
is bit `r` of `interior m <<< 1`: empty for `r = 2`, and the diagonal-`2` pair `[m odd, m ≥ 3]`
for `r = 3`. -/

/-- Below a zero band of `y` the bits of `q^n · y` stay zero, and the first bit above it is frozen. -/
theorem phiLinearPow_testBit_low (y d : Nat) (hy : ∀ i, i ≤ d → y.testBit i = false) : ∀ n,
    (∀ i, i ≤ d → (phiLinearPow n y).testBit i = false) ∧ (phiLinearPow n y).testBit (d + 1) = y.testBit (d + 1)
  | 0 => ⟨hy, rfl⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := phiLinearPow_testBit_low y d hy n
    rw [phiLinearPow_step]
    constructor
    · intro i hi
      show ((phiLinearPow n y ^^^ (phiLinearPow n y <<< 1)) ^^^ (phiLinearPow n y <<< 2)).testBit i = false
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, ih1 i hi,
        ih1 (i - 1) (by cfomega), ih1 (i - 2) (by cfomega)]
      cases decide (i ≥ 1) <;> cases decide (i ≥ 2) <;> rfl
    · show ((phiLinearPow n y ^^^ (phiLinearPow n y <<< 1)) ^^^ (phiLinearPow n y <<< 2)).testBit (d + 1) = _
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, ih2,
        Nat.add_sub_cancel, ih1 d (Nat.le_refl d), ih1 (d + 1 - 2) (by cfomega)]
      cases decide (d + 1 ≥ 1) <;> cases decide (d + 1 ≥ 2) <;> cases y.testBit (d + 1) <;> rfl

/-- The low three bits of `Y` vanish for `m ≥ 1`, and bit `3` of `Y` is bit `2` of `interior m`. -/
theorem shiftedRow_low (k r m : Nat) (hm : 1 ≤ m) :
    (∀ i, i ≤ 2 → (shiftedRow k r m).testBit i = false) ∧
      (shiftedRow k r m).testBit 3 = decide (2 ≤ m ∧ m % 2 = 1) := by
  have hy : ∀ i, i ≤ 2 → (interior m <<< 1).testBit i = false := by
    intro i hi
    rw [Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge i 1 with h0 | h0
    · rw [decide_eq_false (by cfomega : ¬ (i ≥ 1))]; rfl
    · rcases Nat.lt_or_ge i 2 with h1 | h1
      · obtain rfl : i = 1 := by cfomega
        rw [Nat.sub_self, interior_testBit_zero, decide_eq_false (by cfomega : ¬ (m = 0)), Bool.and_false]
      · obtain rfl : i = 2 := by cfomega
        rw [show 2 - 1 = 1 from rfl, interior_testBit_one, Bool.and_false]
  unfold shiftedRow
  obtain ⟨h1, h2⟩ := phiLinearPow_testBit_low (interior m <<< 1) 2 hy (twopow k + r - 1 - m)
  refine ⟨h1, ?_⟩
  rw [h2, Nat.testBit_shiftLeft, decide_eq_true (by cfomega : 3 ≥ 1), Bool.true_and, show 3 - 1 = 2 from rfl,
    interior_testBit_two]

/-- Between bit `2` and the left edge, the interior mask is the carry itself. -/
theorem interior_testBit_mid (m i : Nat) (h2 : 2 ≤ i) (hm : i < 2 * m) :
    (interior m).testBit i = (carry (row m)).testBit i := by
  unfold interior edgeSource
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, decide_eq_false (by cfomega : ¬ (i ≥ 2 * m)),
    Bool.false_and]
  have h : (if rdiag 1 m then 2 else 0).testBit i = false := by
    cases rdiag 1 m
    · exact Nat.zero_testBit i
    · show (2 : Nat).testBit i = false
      rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]
      exact decide_eq_false (by cfomega)
  rw [h]
  cases (carry (row m)).testBit i <;> rfl

/-- Bits `2m − 1` and `2m − 2` of `interior m` vanish for `m ≥ 3` (`ldiag 2 = false`). -/
theorem interior_testBit_top_two (v : Nat) :
    (interior (v + 3)).testBit (2 * v + 5) = false ∧ (interior (v + 3)).testBit (2 * v + 4) = false := by
  have h5 : (carry (row (v + 3))).testBit (2 * v + 5) = (rdiag (2 * v + 5) (v + 3) && rdiag (2 * v + 4) (v + 3)) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ (v + 3) (2 * v + 4)
  have h4 : (carry (row (v + 3))).testBit (2 * v + 4) = (rdiag (2 * v + 4) (v + 3) && rdiag (2 * v + 3) (v + 3)) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ (v + 3) (2 * v + 3)
  rw [interior_testBit_mid _ _ (by cfomega) (by cfomega), interior_testBit_mid _ _ (by cfomega) (by cfomega),
    h5, h4, rdiag_eq_ldiag 2 (v + 1) (2 * v + 4) (v + 3) (by cfomega) (by cfomega), ldiag_two_eq _ (by cfomega),
    Bool.and_false, Bool.false_and]
  exact ⟨rfl, rfl⟩

/-- For `m ≥ 1` the interior mask lives below bit `2m − 2`. -/
theorem interior_lt_sub_two (m : Nat) (hm : 1 ≤ m) : interior m < 2 ^ (2 * m - 2) := by
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · rcases Nat.lt_or_ge m 2 with h2 | h2
    · obtain rfl : m = 1 := by cfomega
      decide
    · obtain rfl : m = 2 := by cfomega
      decide
  · obtain ⟨v, rfl⟩ : ∃ v, m = v + 3 := ⟨m - 3, by cfomega⟩
    obtain ⟨h5, h4⟩ := interior_testBit_top_two v
    have h0 := interior_lt_of_pos (v + 3) (by cfomega)
    rw [show 2 * (v + 3) = 2 * v + 5 + 1 by cfomega] at h0
    have h1 := lt_two_pow_of_testBit _ _ h0 h5
    rw [show 2 * v + 5 = 2 * v + 4 + 1 by cfomega] at h1
    rw [show 2 * (v + 3) - 2 = 2 * v + 4 by cfomega]
    exact lt_two_pow_of_testBit _ _ h1 h4

/-- For `1 ≤ m < 2^k`, `Y` lives below bit `2^(k+1) + 2r − 3`. -/
theorem shiftedRow_lt_of_pos (k r m : Nat) (hm : 1 ≤ m) (hmk : m < twopow k) :
    shiftedRow k r m < 2 ^ (twopow (k + 1) + 2 * r - 3) := by
  unfold shiftedRow
  have hw : interior m <<< 1 < 2 ^ (2 * m - 2 + 1) := shiftLeft_lt_two_pow _ _ 1 (interior_lt_sub_two m hm)
  have h := phiLinearPow_lt_of_lt (twopow k + r - 1 - m) _ _ hw
  rw [show 2 * (twopow k + r - 1 - m) + (2 * m - 2 + 1) = twopow (k + 1) + 2 * r - 3 by
      rw [twopow_succ]; cfomega] at h
  exact h

/-- The row `m = 0`: `Y = q^(2^k + r − 1) <<< 1`. -/
theorem shiftedRow_zero_testBit (k r i : Nat) :
    (shiftedRow k r 0).testBit (i + 1) = trinomialParity (twopow k + r - 1) i := by
  unfold shiftedRow
  rw [Nat.sub_zero, interior_zero, phiLinearPow_eq_phiLinPow, phiLinPow_shiftLeft, Nat.testBit_shiftLeft,
    decide_eq_true (by cfomega : i + 1 ≥ 1), Bool.true_and, Nat.add_sub_cancel,
    testBit_phiLinPow_eq_trinomialParity]

theorem second_two_zero (k : Nat) : second k 2 0 = false := by
  show bxor ((shiftedRow k 2 0).testBit (twopow (k + 1) + 1 + 1)) ((shiftedRow k 2 0).testBit (1 + 1)) = false
  rw [shiftedRow_zero_testBit, shiftedRow_zero_testBit, trinomialParity_palindrome (twopow k + 2 - 1) 1 (by cfomega),
    show 2 * (twopow k + 2 - 1) - 1 = twopow (k + 1) + 1 by rw [twopow_succ]; cfomega]
  cases trinomialParity (twopow k + 2 - 1) (twopow (k + 1) + 1) <;> rfl

theorem second_three_zero (k : Nat) : second k 3 0 = false := by
  show bxor ((shiftedRow k 3 0).testBit (twopow (k + 1) + 2 + 1)) ((shiftedRow k 3 0).testBit (2 + 1)) = false
  rw [shiftedRow_zero_testBit, shiftedRow_zero_testBit, trinomialParity_palindrome (twopow k + 3 - 1) 2 (by cfomega),
    show 2 * (twopow k + 3 - 1) - 2 = twopow (k + 1) + 2 by rw [twopow_succ]; cfomega]
  cases trinomialParity (twopow k + 3 - 1) (twopow (k + 1) + 2) <;> rfl

/-- **The class `r = 2` has no second-order term on any row.** -/
theorem second_two (k m : Nat) (hm : m < twopow k) : second k 2 m = false := by
  rcases Nat.lt_or_ge m 1 with h0 | h0
  · obtain rfl : m = 0 := by cfomega
    exact second_two_zero k
  · show bxor ((shiftedRow k 2 m).testBit (twopow (k + 1) + 2)) ((shiftedRow k 2 m).testBit 2) = false
    obtain ⟨hlow, -⟩ := shiftedRow_low k 2 m h0
    have hh : (shiftedRow k 2 m).testBit (twopow (k + 1) + 2) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (shiftedRow_lt_of_pos k 2 m h0 hm)
        (Nat.pow_le_pow_right (by decide) (by cfomega)))
    rw [hh, hlow 2 (Nat.le_refl 2)]
    rfl

theorem secondPrefix_two (k : Nat) : secondPrefix k 2 = false :=
  (xorBelow_congr _ (fun _ => false) _ (fun m hm => second_two k m hm)).trans (xorBelow_false _)

/-- The rows carrying the diagonal-`2` pair: the odd rows `m ≥ 3` (`lowSource m = 4`). -/
def pairRow (m : Nat) : Bool :=
  match m with
  | 0 => false
  | 1 => false
  | _ => timeParity m

theorem pairRow_eq (m : Nat) : pairRow m = decide (2 ≤ m ∧ m % 2 = 1) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · rcases Nat.lt_or_ge m 1 with h1 | h1
    · obtain rfl : m = 0 := by cfomega
      decide
    · obtain rfl : m = 1 := by cfomega
      decide
  · obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by cfomega⟩
    show timeParity (s + 2) = decide (2 ≤ s + 2 ∧ (s + 2) % 2 = 1)
    unfold timeParity
    rcases Nat.mod_two_eq_zero_or_one (s + 2) with hp | hp
    · rw [decide_eq_false (by cfomega : ¬ ((s + 2) % 2 = 1)), decide_eq_false (fun hc => by cfomega)]
    · rw [decide_eq_true hp, decide_eq_true ⟨by cfomega, hp⟩]

/-- **The class `r = 3`: the second-order term of row `m` is the diagonal-`2` pair of row `m`.** -/
theorem second_three (k m : Nat) (hm : m < twopow k) : second k 3 m = pairRow m := by
  rw [pairRow_eq]
  rcases Nat.lt_or_ge m 1 with h0 | h0
  · obtain rfl : m = 0 := by cfomega
    rw [second_three_zero k]
    decide
  · show bxor ((shiftedRow k 3 m).testBit (twopow (k + 1) + 3)) ((shiftedRow k 3 m).testBit 3) = _
    obtain ⟨-, hlow⟩ := shiftedRow_low k 3 m h0
    have hh : (shiftedRow k 3 m).testBit (twopow (k + 1) + 3) = false := by
      have h := shiftedRow_lt_of_pos k 3 m h0 hm
      rw [show twopow (k + 1) + 2 * 3 - 3 = twopow (k + 1) + 3 by cfomega] at h
      exact Nat.testBit_lt_two_pow h
    rw [hh, hlow]
    cases decide (2 ≤ m ∧ m % 2 = 1) <;> rfl

/-- `⊕_{m < 2(n+1)} pairRow m = [n odd]`: the odd rows `3, 5, …, 2n + 1` number `n`. -/
theorem xorBelow_pairRow : ∀ n, xorBelow pairRow (2 * (n + 1)) = decide (n % 2 = 1)
  | 0 => by decide
  | n + 1 => by
    rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 1 + 1 by cfomega]
    show bxor (bxor (xorBelow pairRow (2 * (n + 1))) (pairRow (2 * (n + 1)))) (pairRow (2 * (n + 1) + 1)) = _
    rw [xorBelow_pairRow n, pairRow_eq, pairRow_eq,
      decide_eq_false (fun hc => by cfomega : ¬ (2 ≤ 2 * (n + 1) ∧ 2 * (n + 1) % 2 = 1)),
      decide_eq_true (⟨by cfomega, by cfomega⟩ : 2 ≤ 2 * (n + 1) + 1 ∧ (2 * (n + 1) + 1) % 2 = 1)]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [decide_eq_false (by cfomega : ¬ (n % 2 = 1)), decide_eq_true (by cfomega : (n + 1) % 2 = 1)]; rfl
    · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ ((n + 1) % 2 = 1))]; rfl

/-- **The second prefix of the class `r = 3` is `1` at every scale `k ≥ 2`**: the odd rows
`3 ≤ m < 2^k` number `2^(k−1) − 1`, an odd count. -/
theorem secondPrefix_three (k : Nat) (hk : 2 ≤ k) : secondPrefix k 3 = true := by
  unfold secondPrefix
  rw [xorBelow_congr _ pairRow _ (fun m hm => second_three k m hm)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by cfomega⟩
  have hB := two_le_twopow_add_one j
  have hA := Rule30UOR.Scale.twopow_pos j
  rw [show twopow (j + 2) = 2 * (twopow (j + 1) - 1 + 1) by rw [twopow_add_two]; cfomega, xorBelow_pairRow]
  exact decide_eq_true (by rw [twopow_add_one]; cfomega)

/-! ## The late tail of the class `1` at `u = 1` -/

/-- At `u = 1` the late tail of the class `1` is the single row `2^k`. -/
theorem lateTail_one_at_one (k : Nat) : lateTail k 1 1 = rowTerm (twopow k + 1) (twopow k) := by
  unfold lateTail
  rw [Nat.mul_one, show twopow k + 1 - twopow k = 1 by cfomega]
  show bxor false (rowTerm (twopow k + 1) (twopow k + 0)) = _
  rw [Nat.add_zero]
  cases rowTerm (twopow k + 1) (twopow k) <;> rfl

/-- **The row `2^k` read at time `2^k + 1`** is the carry at the center of row `2^k`: the center
cell and its right neighbour, both black. -/
theorem rowTerm_twopow_add_one (k : Nat) (hk : 1 ≤ k) :
    rowTerm (twopow k + 1) (twopow k) = (center (twopow k) && cell (twopow k) 1) := by
  have h2 : 2 ≤ twopow k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by cfomega⟩
    exact two_le_twopow_add_one j
  unfold rowTerm Rule30UOR.WittDefect.rowBit
  rw [show twopow k + 1 - 1 - twopow k = 0 by cfomega]
  show (interior (twopow k) <<< 1).testBit (twopow k + 1) = _
  rw [Nat.testBit_shiftLeft, decide_eq_true (by cfomega : twopow k + 1 ≥ 1), Bool.true_and, Nat.add_sub_cancel,
    interior_testBit_mid _ _ h2 (by cfomega)]
  have hc : (carry (row (twopow k))).testBit (twopow k - 1 + 1) =
      (rdiag (twopow k - 1 + 1) (twopow k) && rdiag (twopow k - 1) (twopow k)) :=
    Rule30UOR.Interfaces.carry_row_testBit_succ _ _
  rw [show twopow k - 1 + 1 = twopow k by cfomega] at hc
  rw [hc, ← cell_eq_rdiag (twopow k) (twopow k) 0 (by cfomega),
    ← cell_eq_rdiag (twopow k) (twopow k - 1) 1 (by cfomega)]
  rfl

/-- `lateTail k 1 1 = center (2^k) ∧ cell (2^k) 1` for `k ≥ 1`. -/
theorem lateTail_one_at_one_cell (k : Nat) (hk : 1 ≤ k) :
    lateTail k 1 1 = (center (twopow k) && cell (twopow k) 1) := by
  rw [lateTail_one_at_one, rowTerm_twopow_add_one k hk]

/-! ## The residue `3` across one scale and at the first index -/

/-- **The residue-`3` tails of consecutive scales agree on the even indices up to a constant**:
for `k ≥ 2`, `v ≥ 1`, `lateTail (k+1) 3 v = lateTail k 3 (2v) ⊕ frozenPrefix (k+1) 3 ⊕ frozenPrefix k 3 ⊕ 1`
(the two second prefixes are `1`, so the ruler terms `a ∧ 1` and `¬a ∧ 1` sum to `1`). -/
theorem lateTail_three_scale (k v : Nat) (hk : 2 ≤ k) (hv : 1 ≤ v) :
    lateTail (k + 1) 3 v = bxor (lateTail k 3 (2 * v)) (bxor (bxor (frozenPrefix (k + 1) 3) (frozenPrefix k 3)) true) := by
  have h4 : 4 ≤ twopow k := twopow_mono hk
  have h := lateTail_scale k 3 v (by cfomega) (by cfomega) hv
  rw [secondPrefix_three k hk, secondPrefix_three (k + 1) (by cfomega), Bool.and_true, Bool.and_true] at h
  revert h
  cases lateTail (k + 1) 3 v <;> cases lateTail k 3 (2 * v) <;> cases frozenPrefix (k + 1) 3 <;>
    cases frozenPrefix k 3 <;> cases trailingParity (v - 1) <;> intro h <;> first | rfl | exact absurd h (by decide)

/-- **The residue-`3` obligation at the first index**: under a center period `P`,
`lateTail k 3 (1 + P) = lateTail k 3 1 ⊕ trailingParity P` for `k ≥ 2`. -/
theorem lateTail_three_obligation_one (T P k : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (hk : 2 ≤ k)
    (ht : T ≤ twopow k + 3) : lateTail k 3 (1 + P) = bxor (lateTail k 3 1) (trailingParity P) := by
  have h4 : 4 ≤ twopow k := twopow_mono hk
  have h := lateTail_obligation T P k 3 1 hc (by cfomega) (by cfomega) (Nat.le_refl 1) (by rw [Nat.mul_one]; exact ht)
  rw [show 1 + P - 1 = P by cfomega, Nat.sub_self, trailingParity_zero, secondPrefix_three k hk, Bool.and_true] at h
  revert h
  cases lateTail k 3 (1 + P) <;> cases lateTail k 3 1 <;> cases trailingParity P <;> intro h <;>
    first | rfl | exact absurd h (by decide)

/-! ## The three rows of `lateTail k 3 1` as cells

Bit `b` of `row t` is the cell at position `t − b` (`rdiag b t`), so the carry bit `b` of row `t`
is the pair of black cells at positions `t − b` and `t − b + 1`. -/

/-- Carry bit `i + 1` of row `t` is the black pair at positions `t − (i+1)`, `t − i`. -/
theorem carry_testBit_cells (t i : Nat) (p q : Int) (hp : (t : Int) - ((i + 1 : Nat) : Int) = p)
    (hq : (t : Int) - (i : Int) = q) : (carry (row t)).testBit (i + 1) = (cell t p && cell t q) := by
  rw [Rule30UOR.Interfaces.carry_row_testBit_succ t i, ← cell_eq_rdiag t (i + 1) p hp, ← cell_eq_rdiag t i q hq]

/-- Bit `i + 2` of `interior t <<< 1`, away from both edges, is the carry pair at positions
`t − (i+1)`, `t − i`. -/
theorem interior_shift_testBit_cells (t i : Nat) (p q : Int) (hi : 1 ≤ i) (hj : i + 1 < 2 * t)
    (hp : (t : Int) - ((i + 1 : Nat) : Int) = p) (hq : (t : Int) - (i : Int) = q) :
    (interior t <<< 1).testBit (i + 2) = (cell t p && cell t q) := by
  rw [Nat.testBit_shiftLeft, decide_eq_true (by cfomega : i + 2 ≥ 1), Bool.true_and,
    show i + 2 - 1 = i + 1 by cfomega, interior_testBit_mid t (i + 1) (by cfomega) hj]
  exact carry_testBit_cells t i p q hp hq

/-- Row `2^k + 2` at time `2^k + 3`: the carry at the center. -/
theorem rowTerm_three_row_two (K : Nat) (hK : 4 ≤ K) :
    rowTerm (K + 3) (K + 2) = (cell (K + 2) 0 && cell (K + 2) 1) := by
  unfold rowTerm Rule30UOR.WittDefect.rowBit
  rw [show K + 3 - 1 - (K + 2) = 0 by cfomega]
  show (interior (K + 2) <<< 1).testBit (K + 1 + 2) = _
  exact interior_shift_testBit_cells (K + 2) (K + 1) 0 1 (by cfomega) (by cfomega) (by cfomega) (by cfomega)

/-- Row `2^k + 1` at time `2^k + 3`: `q` spreads one step, three carries around the center. -/
theorem rowTerm_three_row_one (K : Nat) (hK : 4 ≤ K) :
    rowTerm (K + 3) (K + 1) =
      bxor (bxor (cell (K + 1) (-1) && cell (K + 1) 0) (cell (K + 1) 0 && cell (K + 1) 1))
        (cell (K + 1) 1 && cell (K + 1) 2) := by
  unfold rowTerm Rule30UOR.WittDefect.rowBit
  rw [show K + 3 - 1 - (K + 1) = 1 by cfomega]
  show ((interior (K + 1) <<< 1 ^^^ (interior (K + 1) <<< 1 <<< 1)) ^^^ (interior (K + 1) <<< 1 <<< 2)).testBit (K + 3) = _
  have e1 : (interior (K + 1) <<< 1 <<< 1).testBit (K + 3) =
      (decide (K + 3 ≥ 1) && (interior (K + 1) <<< 1).testBit (K + 3 - 1)) := Nat.testBit_shiftLeft _
  have e2 : (interior (K + 1) <<< 1 <<< 2).testBit (K + 3) =
      (decide (K + 3 ≥ 2) && (interior (K + 1) <<< 1).testBit (K + 3 - 2)) := Nat.testBit_shiftLeft _
  rw [Nat.testBit_xor, Nat.testBit_xor, e1, e2, decide_eq_true (by cfomega : K + 3 ≥ 1),
    decide_eq_true (by cfomega : K + 3 ≥ 2), Bool.true_and, Bool.true_and,
    show K + 3 - 1 = K + 2 by cfomega, show K + 3 - 2 = K - 1 + 2 by cfomega, show K + 3 = K + 1 + 2 by cfomega,
    interior_shift_testBit_cells (K + 1) (K + 1) (-1) 0 (by cfomega) (by cfomega) (by cfomega) (by cfomega),
    interior_shift_testBit_cells (K + 1) K 0 1 (by cfomega) (by cfomega) (by cfomega) (by cfomega),
    interior_shift_testBit_cells (K + 1) (K - 1) 1 2 (by cfomega) (by cfomega) (by cfomega) (by cfomega)]
  cases cell (K + 1) (-1) <;> cases cell (K + 1) 0 <;> cases cell (K + 1) 1 <;> cases cell (K + 1) 2 <;> rfl

/-- Row `2^k` at time `2^k + 3`: `q² = 1 + X² + X⁴` spreads two steps, three carries at
distances `−2, 0, 2` from the center. -/
theorem rowTerm_three_row_zero (K : Nat) (hK : 4 ≤ K) :
    rowTerm (K + 3) K =
      bxor (bxor (cell K (-2) && cell K (-1)) (cell K 0 && cell K 1)) (cell K 2 && cell K 3) := by
  unfold rowTerm Rule30UOR.WittDefect.rowBit
  rw [show K + 3 - 1 - K = 2 by cfomega, phiLinearPow_eq_phiLinPow]
  have h := phiLinPow_two_mul 1 (interior K <<< 1)
  rw [Nat.mul_one] at h
  rw [h]
  show (phiLin 2 (interior K <<< 1)).testBit (K + 3) = _
  rw [testBit_phiLin, decide_eq_true (by cfomega : K + 3 ≥ 2), decide_eq_true (by cfomega : K + 3 ≥ 2 * 2),
    Bool.true_and, Bool.true_and, show K + 3 - 2 = K - 1 + 2 by cfomega, show K + 3 - 2 * 2 = K - 3 + 2 by cfomega,
    show K + 3 = K + 1 + 2 by cfomega,
    interior_shift_testBit_cells K (K + 1) (-2) (-1) (by cfomega) (by cfomega) (by cfomega) (by cfomega),
    interior_shift_testBit_cells K (K - 1) 0 1 (by cfomega) (by cfomega) (by cfomega) (by cfomega),
    interior_shift_testBit_cells K (K - 3) 2 3 (by cfomega) (by cfomega) (by cfomega) (by cfomega)]
  cases cell K (-2) <;> cases cell K (-1) <;> cases cell K 0 <;> cases cell K 1 <;> cases cell K 2 <;>
    cases cell K 3 <;> rfl

theorem bxor_false_left (a : Bool) : bxor false a = a := rfl

/-- **`lateTail k 3 1` in cells**, for `k ≥ 2`: the three rows `2^k, 2^k + 1, 2^k + 2` read at time
`2^k + 3`, each a sum of black pairs within distance `3` of the center. -/
theorem lateTail_three_at_one_cells (k : Nat) (hk : 2 ≤ k) :
    lateTail k 3 1 =
      bxor (bxor
          (bxor (bxor (cell (twopow k) (-2) && cell (twopow k) (-1)) (cell (twopow k) 0 && cell (twopow k) 1))
            (cell (twopow k) 2 && cell (twopow k) 3))
          (bxor (bxor (cell (twopow k + 1) (-1) && cell (twopow k + 1) 0)
              (cell (twopow k + 1) 0 && cell (twopow k + 1) 1))
            (cell (twopow k + 1) 1 && cell (twopow k + 1) 2)))
        (cell (twopow k + 2) 0 && cell (twopow k + 2) 1) := by
  have h4 : 4 ≤ twopow k := twopow_mono hk
  unfold lateTail
  rw [Nat.mul_one, show twopow k + 3 - twopow k = 3 by cfomega]
  show bxor (bxor (bxor false (rowTerm (twopow k + 3) (twopow k))) (rowTerm (twopow k + 3) (twopow k + 1)))
    (rowTerm (twopow k + 3) (twopow k + 2)) = _
  rw [rowTerm_three_row_zero _ h4, rowTerm_three_row_one _ h4, rowTerm_three_row_two _ h4,
    bxor_false_left]

theorem bxor_cancel_right_aux (E a : Bool) : bxor (bxor E a) E = a := by
  cases E <;> cases a <;> rfl

/-- **The three rows against the ruler**: under a center period `P`, for `k ≥ 2`, the residue-`3`
tail at index `1 + P` differs from the three-row cell expression at scale `k` by `trailingParity P`. -/
theorem three_rows_against_ruler (T P k : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) (hk : 2 ≤ k)
    (ht : T ≤ twopow k + 3) :
    bxor (lateTail k 3 (1 + P))
      (bxor (bxor
          (bxor (bxor (cell (twopow k) (-2) && cell (twopow k) (-1)) (cell (twopow k) 0 && cell (twopow k) 1))
            (cell (twopow k) 2 && cell (twopow k) 3))
          (bxor (bxor (cell (twopow k + 1) (-1) && cell (twopow k + 1) 0)
              (cell (twopow k + 1) 0 && cell (twopow k + 1) 1))
            (cell (twopow k + 1) 1 && cell (twopow k + 1) 2)))
        (cell (twopow k + 2) 0 && cell (twopow k + 2) 1)) = trailingParity P := by
  rw [lateTail_three_obligation_one T P k hc hk ht, lateTail_three_at_one_cells k hk]
  exact bxor_cancel_right_aux _ _

/-! ## The residue-`3` tail under a dyadic period -/

theorem bxor_eq_true_aux (a b : Bool) (h : bxor a b = true) : a = !b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **Under a dyadic center period `2^m` the residue-`3` late tail flips between the scale indices
`2^m` and `2^(m+1)`**: the ruler `trailingParity (2^j − 1) = [j odd]` changes between consecutive
`j`, and the second prefix of the class `3` is `1`. -/
theorem lateTail_three_dyadic_flip (T k m : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T (twopow m)) (hk : 2 ≤ k)
    (ht : T ≤ twopow k * twopow m + 3) : lateTail k 3 (twopow m + twopow m) = !(lateTail k 3 (twopow m)) := by
  have h4 : 4 ≤ twopow k := twopow_mono hk
  have hpos : 1 ≤ twopow m := Rule30UOR.Scale.twopow_pos m
  have h := lateTail_obligation T (twopow m) k 3 (twopow m) hc (by cfomega) (by cfomega) hpos ht
  rw [secondPrefix_three k hk, Bool.and_true, show twopow m + twopow m - 1 = twopow (m + 1) - 1 by rw [twopow_succ],
    trailingParity_twopow_sub_one, trailingParity_twopow_sub_one] at h
  apply bxor_eq_true_aux
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [decide_eq_true (by cfomega : (m + 1) % 2 = 1), decide_eq_false (by cfomega : ¬ (m % 2 = 1))]; rfl
  · rw [decide_eq_true hm, decide_eq_false (by cfomega : ¬ ((m + 1) % 2 = 1))]; rfl

/-- The same under a `κ`-collapse at scale `K` (a center period `2^K` from time `0`). -/
theorem kappaCollapse_lateTail_flip (K k : Nat) (hK : Rule30UOR.Automatic.KappaCollapse K) (hk : 2 ≤ k) :
    lateTail k 3 (twopow K + twopow K) = !(lateTail k 3 (twopow K)) :=
  lateTail_three_dyadic_flip 0 k K ((Rule30UOR.Automatic.kappaCollapse_iff K).1 hK) hk (Nat.zero_le _)

/-! ## The polarity of the ruler on each class -/

/-- The ruler coefficient supplied by the frozen rows `m < 2^k`: the second prefix. -/
def earlyRuler (k r : Nat) : Bool := secondPrefix k r

/-- The ruler coefficient the late tail must supply: the background's minus the frozen rows'. -/
def lateRuler (k r : Nat) : Bool := bxor (rulerCoefficient r) (secondPrefix k r)

/-- On the classes `0 .. 3` at every scale `k ≥ 2` the late tail owes the ruler on `1`, `2`, `3`
and nothing on `0`: the class `3` inverts the polarity of the background. -/
theorem lateRuler_values (k : Nat) (hk : 2 ≤ k) :
    lateRuler k 0 = false ∧ lateRuler k 1 = true ∧ lateRuler k 2 = true ∧ lateRuler k 3 = true := by
  unfold lateRuler
  rw [secondPrefix_zero, secondPrefix_one k (by cfomega), secondPrefix_two, secondPrefix_three k hk,
    rulerCoefficient_zero, rulerCoefficient_one, rulerCoefficient_two, rulerCoefficient_three]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Rule30UOR.ClassObligation
