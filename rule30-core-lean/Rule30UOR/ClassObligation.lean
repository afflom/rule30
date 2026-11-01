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

end Rule30UOR.ClassObligation
