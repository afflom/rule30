module

public import Rule30Equivalents.OneTapeGap
public import Rule30Equivalents.Cobham
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Nat.Digits.Defs

/-!
# One-tape time `o(n log n)` decides only regular languages

The Hennie–Trakhtenbrot gap theorem for every finite input alphabet; `OneTapeGap` proves the unary
case. A one-tape machine reads its input word `w ∈ α*`, written on the cells `0, …, |w| - 1`
(`runW`), and decides `L` in time `T` (`DecidesLang`).

* `DecidesLang.splice`: cutting two runs at boundaries with equal crossing sequences and gluing
  gives the run on the glued input (from the general `OneTapeGap.splice`); it ends on the side
  given by the parity of the crossing sequence.
* `DecidesLang.time_lower_bound`, `DecidesLang.bounded`: in a shortest input with a crossing
  sequence longer than `K`, the crossing sequences on each side of it are pairwise distinct, so the
  time is at least `(n/4) log_{q+1}(n/4)`. Hence time `o(n log n)` bounds the crossing sequences.
* `DecidesLang.isRegular_of_finite`, `DecidesLang.isRegular_of_bounded`: with finitely many (for
  example bounded) crossing sequences, a prefix `u` has a finite type, the set of crossing
  sequences it shows at its right end together with the outcome for the even ones; equal types
  give equal left quotients (splice), so `L` is regular (Myhill–Nerode).
* `isRegular_iff_exists_fast_decider`: `L` is regular iff some one-tape machine decides it in time
  `o(n log n)`; a finite automaton is a machine that runs in time `n + 1`.

For Rule 30 (`problem1_iff_no_fast_digit_deciders`): the black times read in base `k`, least
significant digit first (`digitLang`), form a regular language iff `c` is `k`-automatic
(`isRegular_digitLang_iff`). With Cobham's theorem, **Problem 1 holds iff no one-tape machines
decide `c(n)` from the base-`2` and the base-`3` digits of `n` in time `o(ℓ log ℓ)`**, where `ℓ`
is the number of digits. This is the analogue for digit input of
`OneTapeGap.problem1_iff_no_fast_one_tape_decider`.
-/

@[expose] public section

namespace Rule30Equivalents.OneTapeRegular

open Filter OneTapeGap Ruliology.CellularAutomata

variable {M : Machine} {α : Type*}

/-! ### Splicing runs on words -/

/-- Splicing runs on words: the run on `u ++ v'` follows the run on `u ++ v` left of `|u|`, and the
run on `u' ++ v'` right of `|u'|`; it passes through every state those runs have there. -/
theorem splice_word (enc : α → M.Γ) {u v u' v' : List α} (hu : 1 ≤ u.length)
    (hu' : 1 ≤ u'.length) {TX TY : ℕ} (hXT : M.halt (runW M enc (u ++ v) TX).q = true)
    (hYT : M.halt (runW M enc (u' ++ v') TY).q = true)
    (hC : cs (runW M enc (u ++ v)) u.length TX = cs (runW M enc (u' ++ v')) u'.length TY) :
    ∃ T, M.halt (runW M enc (u ++ v') T).q = true ∧
      (∀ b : ℤ, b ≤ u.length → cs (runW M enc (u ++ v')) b T = cs (runW M enc (u ++ v)) b TX) ∧
      (∀ b : ℤ, u.length ≤ b → cs (runW M enc (u ++ v')) b T =
        cs (runW M enc (u' ++ v')) (b + ((u'.length : ℤ) - u.length)) TY) ∧
      (runW M enc (u ++ v') T).q = (if Even (cs (runW M enc (u ++ v)) u.length TX).length then
        (runW M enc (u ++ v) TX).q else (runW M enc (u' ++ v') TY).q) ∧
      (∀ t, t ≤ TX → (runW M enc (u ++ v) t).h < u.length →
        ∃ σ, (runW M enc (u ++ v') σ).q = (runW M enc (u ++ v) t).q) ∧
      (∀ t, t ≤ TY → (u'.length : ℤ) ≤ (runW M enc (u' ++ v') t).h →
        ∃ σ, (runW M enc (u ++ v') σ).q = (runW M enc (u' ++ v') t).q) := by
  have htL : ∀ i : ℤ, i < u.length → (runW M enc (u ++ v') 0).tape i =
      (runW M enc (u ++ v) 0).tape i := by
    intro i hi
    simp only [runW_zero, initW]
    by_cases h0 : 0 ≤ i
    · rw [dite_eq_left ⟨h0, by simp; omega⟩, dite_eq_left ⟨h0, by simp; omega⟩]
      congr 1
      rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
    · rw [dite_eq_right (fun h => h0 h.1), dite_eq_right (fun h => h0 h.1)]
  have htR : ∀ i : ℤ, (u.length : ℤ) ≤ i → (runW M enc (u ++ v') 0).tape i =
      (runW M enc (u' ++ v') 0).tape (i + ((u'.length : ℤ) - u.length)) := by
    intro i hi
    simp only [runW_zero, initW, List.length_append]
    by_cases hlt : i < (u.length : ℤ) + v'.length
    · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, by omega⟩]
      congr 1
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      congr 1
      omega
    · rw [dite_eq_right (fun h => hlt h.2), dite_eq_right (fun h => by omega)]
  exact splice (isRun_runW enc (u ++ v)) (isRun_runW enc (u' ++ v'))
    (isRun_runW enc (u ++ v')) hXT hYT hC rfl rfl (by simp only [runW_zero, initW]; omega)
    (by simp only [runW_zero, initW]; omega) htL htR

/-! ### Deciders on words -/

/-- `M` decides `L ⊆ α*` in time `T`: on the input `w` it has halted by step `T |w|`, in an
accepting state iff `w ∈ L`. -/
def DecidesLang (M : Machine) (enc : α → M.Γ) (L : Language α) (T : ℕ → ℕ) : Prop :=
  ∀ w : List α, M.halt (runW M enc w (T w.length)).q = true ∧
    (M.accept (runW M enc w (T w.length)).q = true ↔ w ∈ L)

section Decider

variable {enc : α → M.Γ} {L : Language α} {T : ℕ → ℕ}

/-- Splicing for a decider on words. -/
theorem DecidesLang.splice (hM : DecidesLang M enc L T) {u v u' v' : List α} (hu : 1 ≤ u.length)
    (hu' : 1 ≤ u'.length)
    (hC : cs (runW M enc (u ++ v)) u.length (T (u ++ v).length) =
      cs (runW M enc (u' ++ v')) u'.length (T (u' ++ v').length)) :
    (∀ b : ℤ, b ≤ u.length → cs (runW M enc (u ++ v')) b (T (u ++ v').length) =
      cs (runW M enc (u ++ v)) b (T (u ++ v).length)) ∧
    (∀ b : ℤ, u.length ≤ b → cs (runW M enc (u ++ v')) b (T (u ++ v').length) =
      cs (runW M enc (u' ++ v')) (b + ((u'.length : ℤ) - u.length)) (T (u' ++ v').length)) ∧
    (u ++ v' ∈ L ↔ if Even (cs (runW M enc (u ++ v)) u.length (T (u ++ v).length)).length
      then u ++ v ∈ L else u' ++ v' ∈ L) := by
  obtain ⟨T', hT', hL, hR, hq, -, -⟩ := splice_word enc hu hu' (hM (u ++ v)).1 (hM (u' ++ v')).1 hC
  have heq := cs_eq_of_halt (isRun_runW enc (u ++ v')) hT' (hM (u ++ v')).1
  refine ⟨fun b hb => (heq b).symm.trans (hL b hb), fun b hb => (heq b).symm.trans (hR b hb), ?_⟩
  rw [← (hM (u ++ v')).2, ← eq_of_halt' (isRun_runW enc (u ++ v')) hT' (hM (u ++ v')).1, hq]
  split_ifs
  · exact (hM (u ++ v)).2
  · exact (hM (u' ++ v')).2

/-- Splicing for a decider on words: the spliced run passes through every state of the left run on
the left of `|u|`, and of the right run from `|u'|` on. -/
theorem DecidesLang.splice_visit (hM : DecidesLang M enc L T) {u v u' v' : List α}
    (hu : 1 ≤ u.length) (hu' : 1 ≤ u'.length)
    (hC : cs (runW M enc (u ++ v)) u.length (T (u ++ v).length) =
      cs (runW M enc (u' ++ v')) u'.length (T (u' ++ v').length)) :
    (∀ t, t ≤ T (u ++ v).length → (runW M enc (u ++ v) t).h < u.length →
      ∃ σ, (runW M enc (u ++ v') σ).q = (runW M enc (u ++ v) t).q) ∧
    (∀ t, t ≤ T (u' ++ v').length → (u'.length : ℤ) ≤ (runW M enc (u' ++ v') t).h →
      ∃ σ, (runW M enc (u ++ v') σ).q = (runW M enc (u' ++ v') t).q) := by
  obtain ⟨-, -, -, -, -, hvL, hvR⟩ :=
    splice_word enc hu hu' (hM (u ++ v)).1 (hM (u' ++ v')).1 hC
  exact ⟨hvL, hvR⟩

/-- **Hennie's bound for words.** In a shortest input with a crossing sequence longer than `K`,
the crossing sequences on each side of it are pairwise distinct, so the time is at least
`ℓ · (n / 4)` with `ℓ = log_{q+1}(n / 4)`. -/
theorem DecidesLang.time_lower_bound [Fintype M.Q] (hM : DecidesLang M enc L T) {K : ℕ}
    {w : List α} {p : ℤ}
    (hmin : ∀ w' : List α, w'.length < w.length → ∀ b : ℤ,
      (cs (runW M enc w') b (T w'.length)).length ≤ K)
    (hp : K < (cs (runW M enc w) p (T w.length)).length) :
    Nat.log (Fintype.card M.Q + 1) (w.length / 4) * (w.length / 4) ≤ T w.length := by
  classical
  set n := w.length with hn
  set g : ℕ → List M.Q := fun b => cs (runW M enc w) (b : ℤ) (T n)
  -- equal crossing sequences on one side of `p` would give a shorter input
  have hdist : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ((j : ℤ) ≤ p ∨ p ≤ i) → g i ≠ g j := by
    intro i j hi hij hjn hside hC
    have e1 : w.take i ++ w.drop i = w := List.take_append_drop i w
    have e2 : w.take j ++ w.drop j = w := List.take_append_drop j w
    have li : (w.take i).length = i := by simp; omega
    have lj : (w.take j).length = j := by simp; omega
    have hsp := hM.splice (u := w.take i) (v := w.drop i) (u' := w.take j) (v' := w.drop j)
      (by omega) (by omega) (by rw [e1, e2, li, lj]; exact hC)
    rw [e1, e2, li, lj, ← hn] at hsp
    have hlen : (w.take i ++ w.drop j).length < n := by simp; omega
    rcases hside with h | h
    · have e := hsp.2.1 (p - ((j : ℤ) - i)) (by omega)
      rw [show p - ((j : ℤ) - i) + ((j : ℤ) - i) = p by ring] at e
      have := hmin _ hlen (p - ((j : ℤ) - i))
      rw [e] at this
      omega
    · have e := hsp.1 p h
      have := hmin _ hlen p
      rw [e] at this
      omega
  set BL := (Finset.Icc 1 n).filter fun b : ℕ => (b : ℤ) ≤ p
  set BR := (Finset.Icc 1 n).filter fun b : ℕ => p ≤ (b : ℤ)
  have hinjL : Set.InjOn g BL := by
    intro i hi j hj he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist i j hi.1.1 h hj.1.2 (Or.inl hj.2) he
    · exact hdist j i hj.1.1 h hi.1.2 (Or.inl hi.2) he.symm
  have hinjR : Set.InjOn g BR := by
    intro i hi j hj he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist i j hi.1.1 h hj.1.2 (Or.inr hi.2) he
    · exact hdist j i hj.1.1 h hi.1.2 (Or.inr hj.2) he.symm
  have hcard : n ≤ BL.card + BR.card := by
    have hsub : Finset.Icc 1 n ⊆ BL ∪ BR := by
      intro b hb
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases le_total (b : ℤ) p with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le BL BR)
    simpa using this
  obtain ⟨B, hB, hinj⟩ : ∃ B : Finset ℕ, n ≤ 2 * B.card ∧ Set.InjOn g B := by
    rcases le_total BR.card BL.card with h | h
    · exact ⟨BL, by omega, hinjL⟩
    · exact ⟨BR, by omega, hinjR⟩
  set ℓ := Nat.log (Fintype.card M.Q + 1) (n / 4)
  rcases Nat.eq_zero_or_pos (n / 4) with h0 | h0
  · rw [h0, mul_zero]; exact Nat.zero_le _
  have hpow : (Fintype.card M.Q + 1) ^ ℓ ≤ n / 4 := Nat.pow_log_le_self _ h0.ne'
  have h1 := le_sum_length hinj ℓ
  have h2 : ∑ b ∈ B, (g b).length ≤ T n := sum_length_cs_le (isRun_runW enc w) B (T n)
  have h3 : ℓ * (2 * (n / 4)) ≤ ℓ * B.card := Nat.mul_le_mul_left ℓ (by omega)
  have h4 : ℓ * (Fintype.card M.Q + 1) ^ ℓ ≤ ℓ * (n / 4) := Nat.mul_le_mul_left ℓ hpow
  nlinarith

/-- **Hennie for words: time `o(n log n)` bounds the crossing sequences.** -/
theorem DecidesLang.bounded [Fintype M.Q] (hM : DecidesLang M enc L T)
    (hT : (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ) * Real.log n)) :
    ∃ K, ∀ (w : List α) (b : ℤ), (cs (runW M enc w) b (T w.length)).length ≤ K := by
  classical
  by_contra hne
  push Not at hne
  set q := Fintype.card M.Q
  have hq : 1 ≤ q := Fintype.card_pos_iff.2 ⟨M.start⟩
  set c := Real.log ((q : ℝ) + 1)
  have hc : 0 < c := Real.log_pos (by norm_cast; omega)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hT.def (show (0 : ℝ) < 1 / (64 * c) by positivity))
  set N := max N₀ (max 64 ((q + 1) ^ 4))
  set K := ∑ n ∈ Finset.range N, T n
  have hex : ∃ n, ∃ w : List α, w.length = n ∧ ∃ b : ℤ,
      K < (cs (runW M enc w) b (T w.length)).length := by
    obtain ⟨w, b, h⟩ := hne K
    exact ⟨w.length, w, rfl, b, h⟩
  obtain ⟨w, hwn, p, hp⟩ := Nat.find_spec hex
  set n := Nat.find hex
  have hmin : ∀ w' : List α, w'.length < w.length → ∀ b : ℤ,
      (cs (runW M enc w') b (T w'.length)).length ≤ K := fun w' hw' b =>
    not_lt.1 fun h => Nat.find_min hex (lt_of_lt_of_eq hw' hwn) ⟨w', rfl, b, h⟩
  have hnN : N ≤ w.length := by
    by_contra h
    push Not at h
    have h1 := length_cs_le (runW M enc w) p (T w.length)
    have h2 : T w.length ≤ K :=
      Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 h)
    omega
  set m := w.length with hm
  have h64 : 64 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
  have hq4 : (q + 1) ^ 4 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN
  have hbound : (Nat.log (q + 1) (m / 4) : ℝ) * ((m / 4 : ℕ) : ℝ) ≤ T m := by
    exact_mod_cast hM.time_lower_bound hmin hp
  have hℓ := Nat.lt_pow_succ_log_self (show 1 < q + 1 by omega) (m / 4)
  have e1 := log_bound hq h64 hq4 hℓ
  have hlogpos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have e2 : (T m : ℝ) ≤ 1 / (64 * c) * ((m : ℝ) * Real.log m) := by
    have := hN₀ m (le_trans (le_max_left _ _) hnN)
    simp only [Real.norm_eq_abs] at this
    rwa [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (mul_nonneg hmpos.le hlogpos.le)] at this
  have e3 : 32 * c * (T m : ℝ) ≤ (m : ℝ) * Real.log m / 2 := by
    calc 32 * c * (T m : ℝ) ≤ 32 * c * (1 / (64 * c) * ((m : ℝ) * Real.log m)) := by gcongr
      _ = (m : ℝ) * Real.log m / 2 := by field_simp; ring
  have e4 : 32 * c * ((Nat.log (q + 1) (m / 4) : ℝ) * ((m / 4 : ℕ) : ℝ)) ≤ 32 * c * (T m : ℝ) := by
    gcongr
  nlinarith [mul_pos hmpos hlogpos]

end Decider

/-! ### Bounded crossing sequences give a regular language -/

section Regular

variable {enc : α → M.Γ} {L : Language α} {T : ℕ → ℕ}

/-- The type of a prefix `u`: the crossing sequences that the runs on the inputs `u ++ v` show at
the boundary `|u|`, and those of even length whose run accepts. -/
def ctype (M : Machine) (enc : α → M.Γ) (L : Language α) (T : ℕ → ℕ) (u : List α) :
    Set (List M.Q) × Set (List M.Q) :=
  ({C | ∃ v, cs (runW M enc (u ++ v)) u.length (T (u ++ v).length) = C},
    {C | ∃ v, cs (runW M enc (u ++ v)) u.length (T (u ++ v).length) = C ∧ Even C.length ∧
      u ++ v ∈ L})

/-- Continuations that show the same even crossing sequence have the same outcome: the run ends
on the left side. -/
theorem DecidesLang.mem_iff_of_even (hM : DecidesLang M enc L T) {u v v' : List α}
    (hu : 1 ≤ u.length)
    (hC : cs (runW M enc (u ++ v)) u.length (T (u ++ v).length) =
      cs (runW M enc (u ++ v')) u.length (T (u ++ v').length))
    (he : Even (cs (runW M enc (u ++ v)) u.length (T (u ++ v).length)).length) :
    u ++ v' ∈ L ↔ u ++ v ∈ L := by
  have := (hM.splice (u := u) (v := v) (u' := u) (v' := v') hu hu hC).2.2
  rwa [ite_eq_left he] at this

/-- **Equal types give equal left quotients.** -/
theorem DecidesLang.leftQuotient_eq_of_ctype_eq (hM : DecidesLang M enc L T) {u u' : List α}
    (hu : 1 ≤ u.length) (hu' : 1 ≤ u'.length) (h : ctype M enc L T u = ctype M enc L T u') :
    L.leftQuotient u = L.leftQuotient u' := by
  suffices key : ∀ u u' : List α, 1 ≤ u.length → 1 ≤ u'.length →
      ctype M enc L T u = ctype M enc L T u' → ∀ v, u ++ v ∈ L → u' ++ v ∈ L by
    ext v
    exact ⟨key u u' hu hu' h v, key u' u hu' hu h.symm v⟩
  intro u u' hu hu' h v hv
  set C := cs (runW M enc (u ++ v)) u.length (T (u ++ v).length) with hCdef
  have hC1 : C ∈ (ctype M enc L T u).1 := ⟨v, rfl⟩
  rw [h] at hC1
  obtain ⟨v', hv'⟩ := hC1
  -- splice: left of `|u'|` from the run on `u' ++ v'`, right of `|u|` from the run on `u ++ v`
  have hsp := (hM.splice (u := u') (v := v') (u' := u) (v' := v) hu' hu hv').2.2
  rw [hv'] at hsp
  by_cases he : Even C.length
  · rw [ite_eq_left he] at hsp
    apply hsp.2
    have hC2 : C ∈ (ctype M enc L T u).2 := ⟨v, rfl, he, hv⟩
    rw [h] at hC2
    obtain ⟨v'', hv'', -, hv''L⟩ := hC2
    exact (hM.mem_iff_of_even hu' (hv''.trans hv'.symm) (by rw [hv'']; exact he)).2 hv''L
  · rw [ite_eq_right he] at hsp
    exact hsp.2 hv

/-- **Finitely many crossing sequences give a regular language** (Myhill–Nerode): the types of the
nonempty prefixes take finitely many values. -/
theorem DecidesLang.isRegular_of_finite (hM : DecidesLang M enc L T)
    (hfin : {C | ∃ (w : List α) (b : ℤ), cs (runW M enc w) b (T w.length) = C}.Finite) :
    L.IsRegular := by
  classical
  apply Language.IsRegular.of_finite_range_leftQuotient
  set S := {C | ∃ (w : List α) (b : ℤ), cs (runW M enc w) b (T w.length) = C}
  set Types := {τ : Set (List M.Q) × Set (List M.Q) | τ.1 ⊆ S ∧ τ.2 ⊆ S}
  have hTypes : Types.Finite :=
    (hfin.finite_subsets.prod hfin.finite_subsets).subset fun τ hτ => hτ
  -- a language for each type
  let G : Set (List M.Q) × Set (List M.Q) → Language α := fun τ =>
    if h : ∃ u : List α, 1 ≤ u.length ∧ ctype M enc L T u = τ then L.leftQuotient h.choose
    else 0
  refine ((hTypes.image G).insert (L.leftQuotient [])).subset ?_
  rintro _ ⟨u, rfl⟩
  rcases Nat.eq_zero_or_pos u.length with h0 | h0
  · left
    rw [List.length_eq_zero_iff.1 h0]
  · right
    refine ⟨ctype M enc L T u, ⟨fun C hC => ?_, fun C hC => ?_⟩, ?_⟩
    · obtain ⟨v, hv⟩ := hC
      exact ⟨u ++ v, u.length, hv⟩
    · obtain ⟨v, hv, -⟩ := hC
      exact ⟨u ++ v, u.length, hv⟩
    have h : ∃ u' : List α, 1 ≤ u'.length ∧ ctype M enc L T u' = ctype M enc L T u := ⟨u, h0, rfl⟩
    simp only [G, dite_eq_left h]
    exact hM.leftQuotient_eq_of_ctype_eq h.choose_spec.1 h0 h.choose_spec.2

/-- **Bounded crossing sequences give a regular language.** -/
theorem DecidesLang.isRegular_of_bounded [Finite M.Q] (hM : DecidesLang M enc L T) {K : ℕ}
    (hK : ∀ (w : List α) (b : ℤ), (cs (runW M enc w) b (T w.length)).length ≤ K) :
    L.IsRegular :=
  hM.isRegular_of_finite ((List.finite_length_le M.Q K).subset fun _ ⟨w, b, hC⟩ => hC ▸ hK w b)

/-- **The Hennie–Trakhtenbrot theorem.** A language decided by a one-tape machine in time
`o(n log n)` is regular. -/
theorem DecidesLang.isRegular [Fintype M.Q] (hM : DecidesLang M enc L T)
    (hT : (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ) * Real.log n)) : L.IsRegular :=
  let ⟨_, hK⟩ := hM.bounded hT
  hM.isRegular_of_bounded hK

end Regular

/-! ### Regular languages are decided in real time -/

section DFA

variable {β σ : Type} [Fintype β] [Fintype σ] (D : DFA β σ)

/-- The machine of a finite automaton: it reads the input left to right, and answers at the first
blank. -/
noncomputable def dfaTM : TM where
  Q := σ ⊕ Bool
  Γ := Option β
  blank := none
  one := none
  start := Sum.inl D.start
  halt := Sum.isRight
  accept := Sum.elim (fun _ => false) id
  δ := fun s x => match s, x with
    | Sum.inl g, some a => (Sum.inl (D.step g a), some a, Move.right)
    | Sum.inl g, none => (Sum.inr (@decide (g ∈ D.accept) (Classical.dec _)), none, Move.right)
    | Sum.inr b, x => (Sum.inr b, x, Move.right)

theorem runW_dfaTM (w : List β) {t : ℕ} (ht : t ≤ w.length) :
    runW (dfaTM D).toMachine some w t =
      ⟨Sum.inl (D.evalFrom D.start (w.take t)), t, (initW (dfaTM D).toMachine some w).tape⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [(isRun_runW (M := (dfaTM D).toMachine) some w) t, ih (by omega), step_eq rfl]
    have htape : (initW (dfaTM D).toMachine some w).tape (t : ℤ) = some (w[t]'(by omega)) := by
      simp only [initW]
      erw [dite_eq_left (by simp; omega)]
      simp only [Int.toNat_natCast]; rfl
    refine Cfg.ext' ?_ ?_ ?_
    · dsimp only
      rw [htape]
      show Sum.inl _ = Sum.inl _
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        DFA.evalFrom_append_singleton]
    · dsimp only
      rw [htape]
      push_cast
      rfl
    · dsimp only
      rw [htape]
      exact Function.update_eq_self_iff.2 htape.symm

/-- **A finite automaton is a machine that runs in time `n + 1`.** -/
theorem decidesLang_dfaTM : DecidesLang (dfaTM D).toMachine some D.accepts fun n => n + 1 := by
  intro w
  dsimp only
  rw [(isRun_runW (M := (dfaTM D).toMachine) some w) w.length, runW_dfaTM D w le_rfl,
    step_eq rfl]
  have htape : (initW (dfaTM D).toMachine some w).tape (w.length : ℤ) = none := by
    simp only [initW]
    erw [dite_eq_right (by simp)]
    rfl
  dsimp only
  rw [htape]
  refine ⟨rfl, ?_⟩
  show (@decide (D.evalFrom D.start (w.take w.length) ∈ D.accept) (Classical.dec _)) = true ↔ _
  rw [List.take_length, DFA.mem_accepts]
  exact ⟨@of_decide_eq_true _ (Classical.dec _), @decide_eq_true _ (Classical.dec _)⟩

end DFA

/-- **Regular ⟺ decided by a one-tape machine in time `o(n log n)`.** -/
theorem isRegular_iff_exists_fast_decider {β : Type} [Fintype β] (L : Language β) :
    L.IsRegular ↔ ∃ (M : TM) (enc : β → M.Γ) (T : ℕ → ℕ),
      (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ) * Real.log n) ∧
        DecidesLang M.toMachine enc L T := by
  constructor
  · rintro ⟨σ, _, D, rfl⟩
    exact ⟨dfaTM D, some, fun n => n + 1, isLittleO_succ_mul_log, decidesLang_dfaTM D⟩
  · rintro ⟨M, enc, T, hT, hM⟩
    have := M.instFintype
    exact hM.isRegular hT

/-! ### Digit input for Rule 30 -/

section Digits

variable {k : ℕ}

/-- The words of base-`k` digits, least significant first, whose value is a time where `f` is
`true`. Every representation counts, with any number of trailing zeros. -/
def digitLang (k : ℕ) (f : ℕ → Bool) : Language (Fin k) :=
  {w | f (Nat.ofDigits k (w.map Fin.val)) = true}

theorem mem_digitLang (f : ℕ → Bool) (w : List (Fin k)) :
    w ∈ digitLang k f ↔ f (Nat.ofDigits k (w.map Fin.val)) = true := Iff.rfl

/-- The left quotients of `digitLang k f` are the digit languages of the `k`-kernel of `f`. -/
theorem leftQuotient_digitLang (f : ℕ → Bool) (u : List (Fin k)) :
    (digitLang k f).leftQuotient u =
      digitLang k (fun n => f (k ^ u.length * n + Nat.ofDigits k (u.map Fin.val))) := by
  ext v
  rw [Language.mem_leftQuotient, mem_digitLang, mem_digitLang, List.map_append,
    Nat.ofDigits_append, List.length_map, add_comm]

/-- `r` written with exactly `e` digits in base `k`, least significant first. -/
def padDigits (hk : 0 < k) (e r : ℕ) : List (Fin k) :=
  List.ofFn fun i : Fin e => ⟨r / k ^ (i : ℕ) % k, Nat.mod_lt _ hk⟩

theorem length_padDigits (hk : 0 < k) (e r : ℕ) : (padDigits hk e r).length = e :=
  List.length_ofFn

theorem ofDigits_padDigits (hk : 0 < k) :
    ∀ e r, Nat.ofDigits k ((padDigits hk e r).map Fin.val) = r % k ^ e
  | 0, r => by simp [padDigits, Nat.mod_one]
  | e + 1, r => by
    have htail : (List.ofFn fun i : Fin e =>
        (⟨r / k ^ ((i.succ : Fin (e + 1)) : ℕ) % k, Nat.mod_lt _ hk⟩ : Fin k)) =
        padDigits hk e (r / k) := by
      unfold padDigits
      congr 1
      funext i
      ext
      simp only [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
    rw [padDigits, List.ofFn_succ, List.map_cons, Nat.ofDigits_cons, htail,
      ofDigits_padDigits hk e (r / k), pow_succ', Nat.mod_mul]
    simp

theorem digitLang_injective (hk : 2 ≤ k) : Function.Injective (digitLang k) := by
  intro g g' h
  funext n
  have hn : n < k ^ (n + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_self (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
  have hk0 : 0 < k := by omega
  have hval : Nat.ofDigits k ((padDigits hk0 (n + 1) n).map Fin.val) = n := by
    rw [ofDigits_padDigits, Nat.mod_eq_of_lt hn]
  have := congrArg (fun L => padDigits hk0 (n + 1) n ∈ L) h
  simp only [mem_digitLang, hval, eq_iff_iff] at this
  cases hg : g n <;> cases hg' : g' n <;> simp_all

/-- **The digit language of `f` is regular iff `f` is `k`-automatic.** -/
theorem isRegular_digitLang_iff (hk : 2 ≤ k) (f : ℕ → Bool) :
    (digitLang k f).IsRegular ↔ Automatic.IsAutomatic k f := by
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  have hrange : Set.range (digitLang k f).leftQuotient = digitLang k '' Automatic.kernel k f := by
    ext L
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨_, ⟨u.length, Nat.ofDigits k (u.map Fin.val), ?_, rfl⟩,
        (leftQuotient_digitLang f u).symm⟩
      have := Nat.ofDigits_lt_base_pow_length (b := k) (l := u.map Fin.val) (by omega)
        (fun x hx => by
          obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
          exact d.2)
      rwa [List.length_map] at this
    · rintro ⟨g, ⟨e, r, hr, rfl⟩, rfl⟩
      have hk0 : 0 < k := by omega
      refine ⟨padDigits hk0 e r, ?_⟩
      rw [leftQuotient_digitLang, length_padDigits, ofDigits_padDigits, Nat.mod_eq_of_lt hr]
  rw [hrange, Set.finite_image_iff (digitLang_injective hk).injOn]
  rfl

end Digits

/-- **Problem 1 as a lower bound for digit input.** Problem 1 holds iff `c(n)` cannot be decided
both from the base-`2` and from the base-`3` digits of `n`, least significant first, by one-tape
machines in time `o(ℓ log ℓ)`, where `ℓ` is the number of digits. -/
theorem problem1_iff_no_fast_digit_deciders : Rule30Prize.Problem1 ↔
    ¬ ((∃ (M : TM) (enc : Fin 2 → M.Γ) (T : ℕ → ℕ),
        (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ) * Real.log n) ∧
          DecidesLang M.toMachine enc (digitLang 2 c) T) ∧
      (∃ (M : TM) (enc : Fin 3 → M.Γ) (T : ℕ → ℕ),
        (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ) * Real.log n) ∧
          DecidesLang M.toMachine enc (digitLang 3 c) T)) := by
  rw [Cobham.problem1_iff_not_two_three_automatic, ← isRegular_digitLang_iff le_rfl,
    ← isRegular_digitLang_iff (by norm_num), isRegular_iff_exists_fast_decider,
    isRegular_iff_exists_fast_decider]

end Rule30Equivalents.OneTapeRegular
