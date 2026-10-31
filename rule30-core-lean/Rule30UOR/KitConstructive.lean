module

public import Rule30UOR.Constructive
public import Ruliology.CellularAutomata.Rule30Jen
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30RightPeriods

/-!
# Choice-free proofs of the kit results used here

The Rule 30 Prize kit is the reference statement of the problem and is kept
unchanged. A few of its proofs use `Classical.choice`. This module reproves
exactly the kit theorems that the research modules use, under the kit's own
definitions, so the statements are the kit's statements. Only the proofs differ:
each depends at most on `propext` and `Quot.sound`.
-/

@[expose] public section

namespace Rule30UOR.KitConstructive

open Ruliology.CellularAutomata Rule30Jen

/-! ### Pigeonhole -/

private def eraseOne {α : Type} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: l => if y = x then l else y :: eraseOne x l

private theorem length_eraseOne {α : Type} [DecidableEq α] (x : α) :
    ∀ l : List α, x ∈ l → (eraseOne x l).length + 1 = l.length
  | [], h => nomatch h
  | y :: l, h => by
    unfold eraseOne
    by_cases hy : y = x
    · simp [hy]
    · have hx : x ∈ l := by
        cases h with
        | head => exact absurd rfl hy
        | tail _ h => exact h
      simp only [hy, if_false, List.length_cons]
      rw [length_eraseOne x l hx]

private theorem mem_eraseOne {α : Type} [DecidableEq α] (x z : α) (hz : z ≠ x) :
    ∀ l : List α, z ∈ l → z ∈ eraseOne x l
  | [], h => nomatch h
  | y :: l, h => by
    unfold eraseOne
    by_cases hy : y = x
    · simp only [hy, if_true]
      cases h with
      | head => exact absurd hy.symm (fun e => hz (e ▸ rfl))
      | tail _ h => exact h
    · simp only [hy, if_false]
      cases h with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (mem_eraseOne x z hz l h)

/-- A duplicate-free list inside another is no longer. -/
theorem length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l₁, l₂, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ l₂ := hs x (List.Mem.head _)
    have := length_le_of_subset (l₂ := eraseOne x l₂) hn.2 fun y hy =>
      mem_eraseOne x y (fun e => hn.1 (e ▸ hy)) l₂ (hs y (List.Mem.tail _ hy))
    have hl := length_eraseOne x l₂ hx
    simp only [List.length_cons]
    omega

private theorem pigeonhole_iff (w : Nat) (a : Nat → List Bool) :
    (∃ m n, m < n ∧ n ≤ 2 ^ w ∧ a m = a n) ↔
      ∃ n, n ≤ 2 ^ w ∧ ∃ m, m < n ∧ a m = a n := by
  constructor
  · rintro ⟨m, n, h1, h2, h3⟩
    exact ⟨n, h2, m, h1, h3⟩
  · rintro ⟨n, h2, m, h1, h3⟩
    exact ⟨m, n, h1, h2, h3⟩

/-- **Pigeonhole**: among `2 ^ w + 1` lists of length `w`, two are equal. -/
theorem pigeonhole (w : Nat) (a : Nat → List Bool) (ha : ∀ m, (a m).length = w) :
    ∃ m n, m < n ∧ n ≤ 2 ^ w ∧ a m = a n := by
  haveI : Decidable (∃ m n, m < n ∧ n ≤ 2 ^ w ∧ a m = a n) :=
    decidable_of_iff _ (pigeonhole_iff w a).symm
  refine Decidable.byContradiction fun hne => ?_
  have hinj : ∀ m ∈ List.range (2 ^ w + 1), ∀ n ∈ List.range (2 ^ w + 1), a m = a n → m = n := by
    intro m hm n hn e
    rw [List.mem_range] at hm hn
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd ⟨m, n, h, by omega, e⟩ hne
    · exact h
    · exact absurd ⟨n, m, h, by omega, e.symm⟩ hne
  have hnd := nodup_map_of_inj a (Rule30UOR.Constructive.nodup_range _) hinj
  have := length_le_of_subset hnd fun x hx => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    have := mem_allLists (a m)
    rwa [ha m] at this
  rw [List.length_map, List.length_range, length_allLists] at this
  omega

/-! ### Jen's theorem -/

/-- Between two eventually periodic columns, the next column is eventually periodic. -/
theorem between_periodic {j k : Int} (hjk : j + 1 < k)
    (hj : EventuallyPeriodic fun t => cell t j) (hk : EventuallyPeriodic fun t => cell t k) :
    EventuallyPeriodic fun t => cell t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have key := strip_agree (by omega) he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1) (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by
        rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => cell t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => cell t k) hpk (n - m) _ (by omega)).symm

/-- **Jen's theorem.** No two different columns are both eventually periodic. -/
theorem jen (j k : Int) (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => cell t j) ∧ EventuallyPeriodic (fun t => cell t k)) := by
  have lt_case : ∀ a b : Int, a < b → (EventuallyPeriodic fun t => cell t a) →
      (EventuallyPeriodic fun t => cell t b) → False := by
    intro a b hab ha hb
    by_cases hadj : b = a + 1
    · subst hadj; exact not_adjacent a ha hb
    · exact not_adjacent a ha (between_periodic (by omega) ha hb)
  rintro ⟨hj, hk⟩
  rcases Int.lt_or_gt_of_ne hjk with h | h
  · exact lt_case j k h hj hk
  · exact lt_case k j h hk hj

/-! ### No eventually constant column -/

/-- **No column of rule 30 is eventually constant.** The monotone neighbour is
handled by the two cases of its colour, without extracting a settling time. -/
theorem no_column_eventually_constant (i : Int) : ¬ ∃ T b, ∀ t, T ≤ t → cell t i = b := by
  rintro ⟨T, b, h⟩
  cases b
  · have hmono : ∀ t, T ≤ t → cell t (i + 1) = true → cell (t + 1) (i + 1) = true := by
      intro t ht h1
      show rule (cell t (i + 1 - 1)) (cell t (i + 1)) (cell t (i + 1 + 1)) = true
      rw [show i + 1 - 1 = i by omega, h t ht, h1]
      rfl
    have hi := Rule30Prize.eventuallyPeriodic_of_const h
    have hblack : ¬ ∃ t₀, T ≤ t₀ ∧ cell t₀ (i + 1) = true := by
      rintro ⟨t₀, ht₀, hf⟩
      have hk : ∀ k, cell (t₀ + k) (i + 1) = true := by
        intro k
        induction k with
        | zero => exact hf
        | succ k ih => exact hmono (t₀ + k) (by omega) ih
      refine not_adjacent i hi (Rule30Prize.eventuallyPeriodic_of_const (T := t₀) (b := true) ?_)
      intro t ht
      have := hk (t - t₀)
      rwa [show t₀ + (t - t₀) = t by omega] at this
    refine not_adjacent i hi (Rule30Prize.eventuallyPeriodic_of_const (T := T) (b := false) ?_)
    intro t ht
    cases hft : cell t (i + 1)
    · rfl
    · exact absurd ⟨t, ht, hft⟩ hblack
  · have hleft : ∀ t, T ≤ t → cell t (i - 1) = false := by
      intro t ht
      have e := h (t + 1) (by omega)
      have hc : cell (t + 1) i = rule (cell t (i - 1)) (cell t i) (cell t (i + 1)) := rfl
      rw [hc, h t ht] at e
      revert e
      cases cell t (i - 1) <;> cases cell t (i + 1) <;> decide
    refine not_adjacent (i - 1) (Rule30Prize.eventuallyPeriodic_of_const hleft) ?_
    rw [show i - 1 + 1 = i by omega]
    exact Rule30Prize.eventuallyPeriodic_of_const h

/-- **The center column is not eventually constant.** -/
theorem center_not_eventually_constant :
    ¬ ∃ T b, ∀ t, T ≤ t → Rule30Prize.center t = b :=
  no_column_eventually_constant 0

/-! ### Periods of the right diagonals

`R j` has period `2 ^ j` from time zero (`per_R_periodic`), so a period is
checked on one period of `R j` and `Per j H` is decidable. With that instance
the kit's search for the last diagonal of period `2 ^ k` is a bounded search.
These are the kit's statements under the kit's definitions. -/

section RightPeriods

open Rule30Diagonals Rule30RightPeriods

theorem per_iff_bounded (j H : Nat) :
    Per j H ↔ ∀ t, t < 2 ^ j → R j (t + H) = R j t := by
  constructor
  · exact fun h t _ => h t
  · intro h t
    have hp := per_R_periodic j
    have hr := (Per.mul hp (t / 2 ^ j)) (t % 2 ^ j)
    have hr' := (Per.mul hp (t / 2 ^ j)) (t % 2 ^ j + H)
    have ht : t % 2 ^ j + (t / 2 ^ j) * 2 ^ j = t := by
      have := Nat.mod_add_div t (2 ^ j)
      rw [Nat.mul_comm] at this
      omega
    rw [ht] at hr
    rw [show t % 2 ^ j + H + (t / 2 ^ j) * 2 ^ j = t + H by omega] at hr'
    rw [hr', hr]
    exact h _ (Nat.mod_lt _ (Nat.two_pow_pos j))

instance (j H : Nat) : Decidable (Per j H) :=
  decidable_of_iff _ (per_iff_bounded j H).symm

theorem R_one_eq : ∀ t, R 1 t = (t % 2 == 1)
  | 0 => R_init (by omega)
  | t + 1 => by
    rw [R_one_succ, Rule30UOR.KitConstructive.R_one_eq t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      rw [h, h']; rfl
    · have h' : (t + 1) % 2 = 0 := by omega
      rw [h, h']; rfl

theorem mod2_add (a b : Nat) : ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have h : (a + b) % 2 = 0 := by omega
    rw [h, ha, hb]; rfl
  · have h : (a + b) % 2 = 1 := by omega
    rw [h, ha, hb]; rfl
  · have h : (a + b) % 2 = 1 := by omega
    rw [h, ha, hb]; rfl
  · have h : (a + b) % 2 = 0 := by omega
    rw [h, ha, hb]; rfl

/-- From the white strip, every diagonal `i ≤ n + 2` has period `H`. -/
theorem halve_of_Z {H n : Nat} (hZ : Z H (n + 1) ((n + 2) / 2)) :
    ∀ i, i ≤ n + 2 → Per i H := by
  have hb := Z_bottom hZ
  have hH : H % 2 = 0 := by
    have h2 := hb 2 (by omega) (by omega)
    rw [R_two_eq_one, Rule30UOR.KitConstructive.R_one_eq] at h2
    rcases Nat.mod_two_eq_zero_or_one H with h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (by decide)
  have pair : ∀ m, (m ≤ n + 2 → Per m H) ∧ (m + 1 ≤ n + 2 → Per (m + 1) H) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => per_zero H, fun _ => ?_⟩
      intro t
      show R 1 (t + H) = R 1 t
      rw [Rule30UOR.KitConstructive.R_one_eq, Rule30UOR.KitConstructive.R_one_eq, show (t + H) % 2 = t % 2 by omega]
    | succ m ih =>
      refine ⟨ih.2, fun hm => ?_⟩
      have pa : Per m H := ih.1 (by omega)
      have pb : Per (m + 1) H := ih.2 (by omega)
      have sh := accum_shift (x := R (m + 2)) (g := fun t => R (m + 1) t || R m t) (L := H)
        (fun t => R_step m t)
        (fun t => by
          show (R (m + 1) (t + H) || R m (t + H)) = (R (m + 1) t || R m t)
          rw [pa t, pb t])
      intro t
      show R (m + 2) (t + H) = R (m + 2) t
      rw [sh t, R_lt (show 2 * 0 < m + 2 by omega), hb (m + 2) (by omega) (by omega)]
      cases R (m + 2) t <;> rfl
  exact fun i hi => (pair i).1 hi

/-- **Halving lemma**: a period `H` of diagonal `n + 3` is a period of every diagonal up to
`n + 2`. -/
theorem halve {H n : Nat} (h : Per (n + 3) H) : ∀ i, i ≤ n + 2 → Per i H :=
  Rule30UOR.KitConstructive.halve_of_Z (Z_of_per h)


/-- **Monotonicity**: if diagonal `j + 1` repeats with period `H`, so do all diagonals up to
`j`. In particular `e_j ≤ e_{j+1}`. -/
theorem per_mono_all {j H : Nat} (h : Per (j + 1) H) : ∀ i, i ≤ j → Per i H := by
  rcases j with _ | _ | n
  · intro i hi
    rw [show i = 0 by omega]; exact per_zero H
  · intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact per_zero H
    · intro t
      have := h t
      rw [R_two_eq_one, R_two_eq_one] at this
      exact this
  · exact Rule30UOR.KitConstructive.halve h

theorem per_mono {j H : Nat} (h : Per (j + 1) H) : Per j H :=
  Rule30UOR.KitConstructive.per_mono_all h j (Nat.le_refl j)

theorem per_mono_le {i j H : Nat} (hij : i ≤ j) (h : Per j H) : Per i H := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact Rule30UOR.KitConstructive.per_mono_all h i (by omega)

theorem shift_formula {j H : Nat} (h : Per j H) :
    ∀ t, R (j + 1) (t + H) = xor (R (j + 1) t) (R (j + 1) H) := by
  rcases j with _ | j
  · intro t
    show R 1 (t + H) = xor (R 1 t) (R 1 H)
    rw [Rule30UOR.KitConstructive.R_one_eq, Rule30UOR.KitConstructive.R_one_eq, Rule30UOR.KitConstructive.R_one_eq, Rule30UOR.KitConstructive.mod2_add]
  · have hj : Per j H := Rule30UOR.KitConstructive.per_mono_all h j (Nat.le_refl j)
    have sh := accum_shift (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t) (L := H)
      (fun t => R_step j t)
      (fun t => by
        show (R (j + 1) (t + H) || R j (t + H)) = (R (j + 1) t || R j t)
        rw [h t, hj t])
    rw [R_lt (show 2 * 0 < j + 2 by omega)] at sh
    intro t
    show R (j + 2) (t + H) = xor (R (j + 2) t) (R (j + 2) H)
    rw [sh t]; cases R (j + 2) H <;> cases R (j + 2) t <;> rfl

/-- **Doubling criterion**: given period `H` on diagonal `j`, diagonal `j + 1` keeps the period
`H` exactly when its cell at time `H` is white. -/
theorem per_succ_iff {j H : Nat} (h : Per j H) :
    Per (j + 1) H ↔ R (j + 1) H = false := by
  constructor
  · intro hp
    have := hp 0
    rwa [Nat.zero_add, R_init (by omega)] at this
  · intro h0 t
    rw [Rule30UOR.KitConstructive.shift_formula h t, h0]; cases R (j + 1) t <;> rfl

/-- When the cell at time `H` is black, a shift by `H` complements diagonal `j + 1`. -/
theorem antiperiod_of_black {j H : Nat} (h : Per j H) (hb : R (j + 1) H = true) :
    ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
  intro t; rw [Rule30UOR.KitConstructive.shift_formula h t, hb]; cases R (j + 1) t <;> rfl

/-- When the period doubles, the diagonal is complemented by a shift of half its period. -/
theorem antiperiod {j H : Nat} (h : Per j H) (hn : ¬ Per (j + 1) H) :
    ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
  have h1 : R (j + 1) H = true := by
    cases h' : R (j + 1) H
    · exact absurd ((Rule30UOR.KitConstructive.per_succ_iff h).2 h') hn
    · rfl
  exact Rule30UOR.KitConstructive.antiperiod_of_black h h1

/-- **The last cell of every period is black**: if diagonal `j` has period `2^k`, then
`R j (2^k - 1)` is black. So row `2^k - 1` ends in `J + 1` black cells. -/
theorem last_one : ∀ j k, Per j (2 ^ k) → R j (2 ^ k - 1) = true
  | 0, _, _ => R_zero _
  | 1, k, h => by
    rcases k with _ | k
    · exact absurd h (not_per_one (by omega))
    · rw [Rule30UOR.KitConstructive.R_one_eq]
      have : (2 ^ (k + 1) - 1) % 2 = 1 := by
        have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega
      rw [this]; rfl
  | j + 2, k, h => by
    have hp := Nat.two_pow_pos k
    have hj1 := Rule30UOR.KitConstructive.last_one (j + 1) k (Rule30UOR.KitConstructive.per_mono h)
    have s := R_step j (2 ^ k - 1)
    rw [show 2 ^ k - 1 + 1 = 0 + 2 ^ k by omega, h 0, R_init (by omega), hj1] at s
    revert s; cases R (j + 2) (2 ^ k - 1) <;> simp

theorem last_search {k : Nat} : ∀ d n, Per n (2 ^ k) → ¬ Per (n + d) (2 ^ k) →
    ∃ J, n ≤ J ∧ Per J (2 ^ k) ∧ ¬ Per (J + 1) (2 ^ k)
  | 0, n, h, hn => absurd h (by simpa using hn)
  | d + 1, n, h, hn => by
    by_cases h1 : Per (n + 1) (2 ^ k)
    · obtain ⟨J, hJ, hJ', hJ''⟩ := Rule30UOR.KitConstructive.last_search d (n + 1) h1
        (by rw [show n + 1 + d = n + (d + 1) by omega]; exact hn)
      exact ⟨J, by omega, hJ', hJ''⟩
    · exact ⟨n, Nat.le_refl _, h, h1⟩

/-- The last diagonal `J_k` of period `2^k` exists and satisfies `k ≤ J_k`. -/
theorem exists_last (k : Nat) : ∃ J, Per J (2 ^ k) ∧ ¬ Per (J + 1) (2 ^ k) ∧ k ≤ J := by
  have hk := lt_two_pow' (k + 1)
  have hnot : ¬ Per (k + (2 ^ (k + 1) - k)) (2 ^ k) := by
    rw [show k + (2 ^ (k + 1) - k) = 2 ^ (k + 1) by omega]
    exact not_per_small (by omega) (Nat.le_refl _)
  obtain ⟨J, h1, h2, h3⟩ := Rule30UOR.KitConstructive.last_search (2 ^ (k + 1) - k) k (per_R_periodic k) hnot
  exact ⟨J, h2, h3, h1⟩

/-- Any diagonal with period `2^k` has index at most `2^(k+1) - 2`. -/
theorem per_bound {J k : Nat} (hJ : Per J (2 ^ k)) : J ≤ 2 ^ (k + 1) - 2 := by
  apply Nat.le_of_not_lt
  intro hcon
  have hp := Nat.two_pow_pos k
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hi : Per (2 ^ (k + 1) - 1) (2 ^ k) := Rule30UOR.KitConstructive.per_mono_le (by omega) hJ
  have e := hi.at_mul 1
  rw [Nat.mul_one, R_init (by omega)] at e
  have hD : R (2 ^ (k + 1) - 1) (2 ^ k) = D 1 (2 ^ k) := by
    unfold R D; exact cell_congr (by omega)
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hD, hm, D_one] at e
  exact absurd e (by decide)


end RightPeriods

end Rule30UOR.KitConstructive
