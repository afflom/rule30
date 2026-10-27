module

public import Rule30Equivalents.Cobham
public import Rule30Equivalents.LogicAutomata

/-!
# Büchi arithmetic

`(ℕ, 0, 1, +, V_k)`, where `V_k x` is the largest
power of `k` dividing `x`, defines exactly the `k`-automatic sets (Büchi; Bruyère). With Cobham's
theorem, Problem 1 holds iff the black times are not definable both in `(ℕ, +, V₂)` and in
`(ℕ, +, V₃)` (`problem1_iff_not_buchi_definable`).

The direction needed here, "definable ⇒ `k`-automatic", is proved without automata, by kernels of
relations:
* `sect R e r = {v | kᵉ v + r ∈ R}` and `rker R`, the sections with `r < kᵉ`; `R` is
  `Recognizable` when `rker R` is finite.
* Recognizable relations are closed under complement, finite intersection, reindexing and
  projection (`Recognizable.exists`): a section of `{w | ∃ u, (w, u) ∈ R}` is the union, over the
  low digits `s` of `u`, of projections of sections of `R`, so it is determined by a subset of
  `rker R`.
* The graphs of `x = y`, `x + y = z`, `V_k x = y` and `x = c` have finitely many sections
  (`recognizable_eqRel`, `recognizable_addRel`, `recognizable_vkRel`, `recognizable_constRel`).
* By induction, the graph of every term (`recognizable_termGraph`) and the relation of every
  formula (`recognizable_formRel`) of `(buchi k)[[A]]` is recognizable; for a set `S ⊆ ℕ` this is
  `isAutomatic_of_definable`.
* Conversely, eventually periodic sets are Presburger-definable, hence definable in the expansion.
-/

@[expose] public section

namespace Rule30Equivalents.BuchiArithmetic

open FirstOrder Language Structure Ruliology.CellularAutomata Automatic

/-! ### The function `V_k` -/

/-- `V_k x`: the largest power of `k` dividing `x`, and `V_k 0 = 0` (for `k ≥ 2`). -/
def vk (k : ℕ) (x : ℕ) : ℕ :=
  if _h : 2 ≤ k ∧ 0 < x ∧ k ∣ x then k * vk k (x / k) else if x = 0 then 0 else 1
termination_by x
decreasing_by exact Nat.div_lt_self _h.2.1 (by omega)

variable {k : ℕ}

theorem vk_zero (k : ℕ) : vk k 0 = 0 := by
  rw [vk]; simp

theorem vk_mul (hk : 2 ≤ k) (x : ℕ) : vk k (k * x) = k * vk k x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [mul_zero, vk_zero, mul_zero]
  · rw [vk, dite_eq_left ⟨hk, by positivity, dvd_mul_right k x⟩,
      Nat.mul_div_cancel_left _ (by omega)]

theorem vk_of_not_dvd {x : ℕ} (hx : 0 < x) (hkx : ¬ k ∣ x) : vk k x = 1 := by
  rw [vk, dite_eq_right (fun h => hkx h.2.2), ite_eq_right (by omega)]

theorem vk_pow_mul (hk : 2 ≤ k) (e x : ℕ) : vk k (k ^ e * x) = k ^ e * vk k x := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, mul_comm (k ^ e) k, mul_assoc, vk_mul hk, ih, mul_assoc]

/-- The lowest nonzero digits decide `V_k`. -/
theorem vk_add (hk : 2 ≤ k) : ∀ (e : ℕ) {x r : ℕ}, 0 < r → r < k ^ e →
    vk k (k ^ e * x + r) = vk k r
  | 0, _, _, hr, hre => by simp at hre; omega
  | e + 1, x, r, hr, hre => by
    by_cases hkr : k ∣ r
    · obtain ⟨r', rfl⟩ := hkr
      have hr' : 0 < r' := by
        rcases Nat.eq_zero_or_pos r' with h | h
        · subst h; simp at hr
        · exact h
      have hre' : r' < k ^ e := by
        rw [pow_succ'] at hre
        exact Nat.lt_of_mul_lt_mul_left hre
      rw [show k ^ (e + 1) * x + k * r' = k * (k ^ e * x + r') by ring, vk_mul hk, vk_mul hk,
        vk_add hk e hr' hre']
    · have h1 : ¬ k ∣ k ^ (e + 1) * x + r := by
        rw [Nat.dvd_add_right (Dvd.dvd.mul_right (dvd_pow_self k (Nat.succ_ne_zero e)) x)]
        exact hkr
      rw [vk_of_not_dvd (by positivity) h1, vk_of_not_dvd hr hkr]

theorem vk_le (hk : 2 ≤ k) : ∀ x, vk k x ≤ x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [vk_zero]
    · by_cases hkx : k ∣ x
      · obtain ⟨y, rfl⟩ := hkx
        rw [vk_mul hk]
        have hy : 0 < y := Nat.pos_of_mul_pos_left hx
        exact Nat.mul_le_mul_left k (ih y (by nlinarith))
      · rw [vk_of_not_dvd hx hkx]
        exact hx

/-! ### Relations with finitely many sections -/

variable (k) {ι : Type*}

/-- The `(e, r)`-section of a relation on `ι → ℕ`: the `v` with `kᵉ v + r ∈ R`. -/
def sect (R : Set (ι → ℕ)) (e : ℕ) (r : ι → ℕ) : Set (ι → ℕ) :=
  {v | (fun i => k ^ e * v i + r i) ∈ R}

/-- The `k`-kernel of a relation: its sections with all `r i < kᵉ`. -/
def rker (R : Set (ι → ℕ)) : Set (Set (ι → ℕ)) :=
  {S | ∃ e r, (∀ i, r i < k ^ e) ∧ S = sect k R e r}

/-- A relation is `k`-recognizable when its `k`-kernel is finite. -/
def Recognizable (R : Set (ι → ℕ)) : Prop := (rker k R).Finite

variable {k}

theorem Recognizable.compl {R : Set (ι → ℕ)} (h : Recognizable k R) : Recognizable k Rᶜ :=
  (h.image fun S => Sᶜ).subset <| by
    rintro _ ⟨e, r, hr, rfl⟩
    exact ⟨sect k R e r, ⟨e, r, hr, rfl⟩, rfl⟩

theorem Recognizable.inter {R S : Set (ι → ℕ)} (hR : Recognizable k R) (hS : Recognizable k S) :
    Recognizable k (R ∩ S) :=
  (hR.image2 (· ∩ ·) hS).subset <| by
    rintro _ ⟨e, r, hr, rfl⟩
    exact ⟨_, ⟨e, r, hr, rfl⟩, _, ⟨e, r, hr, rfl⟩, rfl⟩

theorem Recognizable.iInter {κ : Type*} [Finite κ] {R : κ → Set (ι → ℕ)}
    (h : ∀ j, Recognizable k (R j)) : Recognizable k (⋂ j, R j) :=
  ((Set.Finite.pi fun j => h j).image fun F => ⋂ j, F j).subset <| by
    rintro _ ⟨e, r, hr, rfl⟩
    refine ⟨fun j => sect k (R j) e r, fun j _ => ⟨e, r, hr, rfl⟩, ?_⟩
    ext v
    simp [sect]

theorem Recognizable.comap {ι' : Type*} (σ : ι → ι') {R : Set (ι → ℕ)} (h : Recognizable k R) :
    Recognizable k {w : ι' → ℕ | w ∘ σ ∈ R} :=
  (h.image fun S => {w : ι' → ℕ | w ∘ σ ∈ S}).subset <| by
    rintro _ ⟨e, r, hr, rfl⟩
    exact ⟨sect k R e (r ∘ σ), ⟨e, r ∘ σ, fun i => hr (σ i), rfl⟩, rfl⟩

theorem Recognizable.congr {R S : Set (ι → ℕ)} (h : Recognizable k R) (hRS : R = S) :
    Recognizable k S := hRS ▸ h

/-- **Projection.** A section of `{w | ∃ u, (w, u) ∈ R}` is the union, over the low digits `s` of
`u`, of the projections of the sections of `R` at `(r, s)`. -/
theorem Recognizable.exists (hk : 0 < k) {κ : Type*} {R : Set (ι ⊕ κ → ℕ)}
    (h : Recognizable k R) : Recognizable k {w : ι → ℕ | ∃ u : κ → ℕ, Sum.elim w u ∈ R} := by
  refine (h.powerset.image fun T => {w : ι → ℕ | ∃ S ∈ T, ∃ u : κ → ℕ, Sum.elim w u ∈ S}).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  have hK : 0 < k ^ e := pow_pos hk e
  refine ⟨{S | ∃ s : κ → ℕ, (∀ j, s j < k ^ e) ∧ S = sect k R e (Sum.elim r s)}, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨e, Sum.elim r s, fun x => by cases x <;> simp [hr, hs], rfl⟩
  · ext w
    simp only [sect, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨S, ⟨s, hs, rfl⟩, u, hu⟩
      refine ⟨fun j => k ^ e * u j + s j, ?_⟩
      have he : Sum.elim (fun i => k ^ e * w i + r i) (fun j => k ^ e * u j + s j) =
          fun x => k ^ e * Sum.elim w u x + Sum.elim r s x := by
        funext x
        cases x <;> rfl
      rw [he]
      exact hu
    · rintro ⟨u, hu⟩
      refine ⟨_, ⟨fun j => u j % k ^ e, fun j => Nat.mod_lt _ hK, rfl⟩, fun j => u j / k ^ e, ?_⟩
      have he : (fun x => k ^ e * Sum.elim w (fun j => u j / k ^ e) x +
          Sum.elim r (fun j => u j % k ^ e) x) = Sum.elim (fun i => k ^ e * w i + r i) u := by
        funext x
        cases x with
        | inl i => rfl
        | inr j => exact Nat.div_add_mod (u j) (k ^ e)
      show (fun x => k ^ e * Sum.elim w (fun j => u j / k ^ e) x +
          Sum.elim r (fun j => u j % k ^ e) x) ∈ R
      rw [he]
      exact hu

/-! ### The basic relations -/

/-- `K a + b = K c + d` with `b, d < K` means `a = c` and `b = d`. -/
theorem affine_eq_iff {K a b c d : ℕ} (hK : 0 < K) (hb : b < K) (hd : d < K) :
    K * a + b = K * c + d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 : (K * a + b) % K = b := by rw [Nat.mul_comm, Nat.mul_add_mod_of_lt hb]
    have h2 : (K * c + d) % K = d := by rw [Nat.mul_comm, Nat.mul_add_mod_of_lt hd]
    have hbd : b = d := by rw [← h1, ← h2, h]
    subst hbd
    exact ⟨Nat.eq_of_mul_eq_mul_left hK (by omega), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The graph of equality. -/
def eqRel : Set (Fin 2 → ℕ) := {v | v 0 = v 1}

theorem recognizable_eqRel (hk : 0 < k) : Recognizable k eqRel := by
  refine (Set.toFinite {eqRel, ∅}).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  have hK : 0 < k ^ e := pow_pos hk e
  by_cases h : r 0 = r 1
  · left
    ext v
    show k ^ e * v 0 + r 0 = k ^ e * v 1 + r 1 ↔ v 0 = v 1
    rw [affine_eq_iff hK (hr 0) (hr 1)]
    tauto
  · right
    ext v
    show k ^ e * v 0 + r 0 = k ^ e * v 1 + r 1 ↔ False
    rw [affine_eq_iff hK (hr 0) (hr 1)]
    tauto

/-- The graph of addition. -/
def addRel : Set (Fin 3 → ℕ) := {v | v 0 + v 1 = v 2}

theorem recognizable_addRel (hk : 0 < k) : Recognizable k addRel := by
  refine (Set.toFinite {addRel, {v : Fin 3 → ℕ | v 0 + v 1 + 1 = v 2}, ∅}).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  set K := k ^ e with hKdef
  have hK : 0 < K := pow_pos hk e
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have hmem : ∀ v : Fin 3 → ℕ,
      v ∈ sect k addRel e r ↔ K * (v 0 + v 1) + (r 0 + r 1) = K * v 2 + r 2 := fun v => by
    show K * v 0 + r 0 + (K * v 1 + r 1) = K * v 2 + r 2 ↔ _
    rw [mul_add]
    constructor <;> intro h <;> omega
  by_cases hs : r 0 + r 1 < K
  · by_cases hr2 : r 0 + r 1 = r 2
    · left
      ext v
      rw [hmem, affine_eq_iff hK hs h2]
      simp [addRel, hr2]
    · right; right
      ext v
      rw [hmem, affine_eq_iff hK hs h2]
      simp [hr2]
  · have hs' : r 0 + r 1 - K < K := by omega
    have hmem' : ∀ v : Fin 3 → ℕ, v ∈ sect k addRel e r ↔
        K * (v 0 + v 1 + 1) + (r 0 + r 1 - K) = K * v 2 + r 2 := fun v => by
      rw [hmem, mul_add K (v 0 + v 1) 1, mul_one]
      constructor <;> intro h <;> omega
    by_cases hr2 : r 0 + r 1 - K = r 2
    · right; left
      ext v
      rw [hmem', affine_eq_iff hK hs' h2]
      simp [hr2]
    · right; right
      ext v
      rw [hmem', affine_eq_iff hK hs' h2]
      simp [hr2]

/-- The graph of `V_k`. -/
def vkRel (k : ℕ) : Set (Fin 2 → ℕ) := {v | vk k (v 0) = v 1}

theorem recognizable_vkRel (hk : 2 ≤ k) : Recognizable k (vkRel k) := by
  refine (Set.toFinite {vkRel k, {v : Fin 2 → ℕ | 0 = v 1}, ∅}).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  have hK : 0 < k ^ e := pow_pos (by omega) e
  have hmem : ∀ v : Fin 2 → ℕ,
      v ∈ sect k (vkRel k) e r ↔ vk k (k ^ e * v 0 + r 0) = k ^ e * v 1 + r 1 := fun _ => Iff.rfl
  rcases Nat.eq_zero_or_pos (r 0) with h0 | h0
  · have hmem0 : ∀ v : Fin 2 → ℕ, v ∈ sect k (vkRel k) e r ↔ vk k (v 0) = v 1 ∧ 0 = r 1 :=
      fun v => by
        rw [hmem, h0, add_zero, vk_pow_mul hk, ← add_zero (k ^ e * vk k (v 0)),
          affine_eq_iff hK hK (hr 1)]
    by_cases h1 : 0 = r 1
    · left
      ext v
      rw [hmem0]
      simp [vkRel, h1]
    · right; right
      ext v
      rw [hmem0]
      simp [h1]
  · have hc : vk k (r 0) < k ^ e := lt_of_le_of_lt (vk_le hk _) (hr 0)
    have hmem1 : ∀ v : Fin 2 → ℕ, v ∈ sect k (vkRel k) e r ↔ 0 = v 1 ∧ vk k (r 0) = r 1 :=
      fun v => by
        rw [hmem, vk_add hk e h0 (hr 0)]
        rw [show vk k (r 0) = k ^ e * 0 + vk k (r 0) by ring, affine_eq_iff hK hc (hr 1)]
        simp only [mul_zero, zero_add]
    by_cases h1 : vk k (r 0) = r 1
    · right; left
      ext v
      rw [hmem1]
      simp [h1]
    · right; right
      ext v
      rw [hmem1]
      simp [h1]

/-- The graph of a constant. -/
def constRel (c : ℕ) : Set (Fin 1 → ℕ) := {v | v 0 = c}

theorem recognizable_constRel (hk : 0 < k) (c : ℕ) : Recognizable k (constRel c) := by
  refine ((Set.finite_Iic c).image constRel |>.insert ∅).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  have hK : 0 < k ^ e := pow_pos hk e
  have hmem : ∀ v : Fin 1 → ℕ,
      v ∈ sect k (constRel c) e r ↔ v 0 = c / k ^ e ∧ r 0 = c % k ^ e := fun v => by
    show k ^ e * v 0 + r 0 = c ↔ _
    conv_lhs => rw [← Nat.div_add_mod c (k ^ e)]
    exact affine_eq_iff hK (hr 0) (Nat.mod_lt _ hK)
  by_cases h : r 0 = c % k ^ e
  · right
    exact ⟨c / k ^ e, Nat.div_le_self _ _, Set.ext fun v => by rw [hmem]; simp [constRel, h]⟩
  · left
    exact Set.ext fun v => by rw [hmem]; simp [h]

/-! ### The language -/

/-- The function symbols of Büchi arithmetic: `0`, `1`, `+` and `V_k`. -/
inductive BuchiFunc : ℕ → Type
  | zero : BuchiFunc 0
  | one : BuchiFunc 0
  | add : BuchiFunc 2
  | v : BuchiFunc 1

/-- The language of Büchi arithmetic `(ℕ, 0, 1, +, V_k)`; the base `k` selects the structure. -/
def buchi (_k : ℕ) : Language := ⟨BuchiFunc, fun _ => Empty⟩

instance (k : ℕ) : (buchi k).Structure ℕ where
  funMap
  | .zero, _ => 0
  | .one, _ => 1
  | .add, x => x 0 + x 1
  | .v, x => vk k (x 0)
  RelMap R _ := Empty.elim R

/-- The graph of a function symbol of `(buchi k)[[A]]`, with the value in an extra coordinate. -/
def funGraph {A : Set ℕ} {l : ℕ} (f : (buchi k)[[A]].Functions l) : Set (Fin l ⊕ Unit → ℕ) :=
  {z | z (Sum.inr ()) = funMap f (z ∘ Sum.inl)}

theorem recognizable_funGraph (hk : 2 ≤ k) {A : Set ℕ} {l : ℕ} (f : (buchi k)[[A]].Functions l) :
    Recognizable k (funGraph f) := by
  rcases f with f | c
  · cases f with
    | zero =>
      refine ((recognizable_constRel (by omega) 0).comap fun _ => Sum.inr ()).congr ?_
      ext z
      simp only [funGraph, constRel, Set.mem_ofPred_eq, Function.comp_apply]
      rfl
    | one =>
      refine ((recognizable_constRel (by omega) 1).comap fun _ => Sum.inr ()).congr ?_
      ext z
      simp only [funGraph, constRel, Set.mem_ofPred_eq, Function.comp_apply]
      rfl
    | add =>
      refine ((recognizable_addRel (by omega)).comap
        ![Sum.inl 0, Sum.inl 1, Sum.inr ()]).congr ?_
      ext z
      simp only [funGraph, addRel, Set.mem_ofPred_eq, Function.comp_apply]
      exact eq_comm
    | v =>
      refine ((recognizable_vkRel hk).comap ![Sum.inl 0, Sum.inr ()]).congr ?_
      ext z
      simp only [funGraph, vkRel, Set.mem_ofPred_eq, Function.comp_apply]
      exact eq_comm
  · cases l with
    | zero =>
      refine ((recognizable_constRel (by omega) (c : ℕ)).comap fun _ => Sum.inr ()).congr ?_
      ext z
      simp only [funGraph, constRel, Set.mem_ofPred_eq, Function.comp_apply]
      rfl
    | succ l => exact c.elim

/-- The graph of a term, with the value in an extra coordinate. -/
def termGraph {A : Set ℕ} {β : Type*} (t : (buchi k)[[A]].Term β) : Set (β ⊕ Unit → ℕ) :=
  {w | w (Sum.inr ()) = t.realize (w ∘ Sum.inl)}

theorem recognizable_termGraph (hk : 2 ≤ k) {A : Set ℕ} {β : Type*} (t : (buchi k)[[A]].Term β) :
    Recognizable k (termGraph t) := by
  induction t with
  | var b =>
    refine ((recognizable_eqRel (by omega)).comap ![Sum.inr (), Sum.inl b]).congr ?_
    ext w
    simp only [termGraph, eqRel, Set.mem_ofPred_eq, Function.comp_apply]
    rfl
  | @func l f ts ih =>
    let σ : Fin l → β ⊕ Unit → (β ⊕ Unit) ⊕ Fin l := fun j =>
      Sum.elim (fun b => Sum.inl (Sum.inl b)) (fun _ => Sum.inr j)
    let τ : Fin l ⊕ Unit → (β ⊕ Unit) ⊕ Fin l := Sum.elim Sum.inr (fun _ => Sum.inl (Sum.inr ()))
    have hR : Recognizable k ((⋂ j, {z | z ∘ σ j ∈ termGraph (ts j)}) ∩
        {z | z ∘ τ ∈ funGraph f}) :=
      (Recognizable.iInter fun j => (ih j).comap (σ j)).inter
        ((recognizable_funGraph hk f).comap τ)
    refine (hR.exists (by omega)).congr ?_
    ext w
    simp only [termGraph, funGraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Term.realize_func]
    constructor
    · rintro ⟨u, hu, hf⟩
      have hu' : u = fun j => (ts j).realize (w ∘ Sum.inl) := funext fun j => hu j
      subst hu'
      exact hf
    · intro h
      exact ⟨fun j => (ts j).realize (w ∘ Sum.inl), fun j => rfl, h⟩

/-- The relation of a formula, on its free and bound variables together. -/
def formRel {A : Set ℕ} {α : Type*} {n : ℕ} (φ : (buchi k)[[A]].BoundedFormula α n) :
    Set (α ⊕ Fin n → ℕ) :=
  {w | φ.Realize (w ∘ Sum.inl) (w ∘ Sum.inr)}

theorem recognizable_formRel (hk : 2 ≤ k) {A : Set ℕ} {α : Type*} {n : ℕ}
    (φ : (buchi k)[[A]].BoundedFormula α n) : Recognizable k (formRel φ) := by
  have hk0 : 0 < k := by omega
  induction φ with
  | falsum =>
    refine Recognizable.congr (R := ∅) ((Set.toFinite {(∅ : Set (α ⊕ Fin _ → ℕ))}).subset ?_) ?_
    · rintro _ ⟨e, r, hr, rfl⟩
      exact Set.mem_singleton_iff.2 (Set.eq_empty_of_forall_notMem fun v hv => hv)
    · ext w
      simp [formRel, BoundedFormula.Realize]
  | equal t₁ t₂ =>
    refine (((recognizable_termGraph hk t₁).inter (recognizable_termGraph hk t₂)).exists
      (κ := Unit) hk0).congr ?_
    ext w
    simp only [termGraph, formRel, Set.mem_ofPred_eq, Set.mem_inter_iff, BoundedFormula.Realize,
      Sum.elim_comp_inl_inr]
    constructor
    · rintro ⟨u, h₁, h₂⟩
      simp only [Sum.elim_inr, Sum.elim_comp_inl] at h₁ h₂
      rw [← h₁, ← h₂]
    · intro h
      exact ⟨fun _ => t₁.realize w, by simp, by simp [h]⟩
  | rel R ts =>
    rcases R with R | R <;> exact R.elim
  | imp φ ψ ihφ ihψ =>
    refine (ihφ.inter ihψ.compl).compl.congr ?_
    ext w
    simp only [formRel, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      BoundedFormula.Realize]
    tauto
  | @all n φ ih =>
    let σ : α ⊕ Fin (n + 1) → (α ⊕ Fin n) ⊕ Unit :=
      Sum.elim (fun a => Sum.inl (Sum.inl a))
        (fun i => Fin.lastCases (Sum.inr ()) (fun j => Sum.inl (Sum.inr j)) i)
    have hσ : ∀ (w : α ⊕ Fin n → ℕ) (x : ℕ),
        (Sum.elim w (fun _ : Unit => x) ∘ σ) ∘ Sum.inr = Fin.snoc (w ∘ Sum.inr) x := by
      intro w x
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [σ]
      · simp [σ]
    refine ((ih.comap σ).compl.exists (κ := Unit) hk0).compl.congr ?_
    ext w
    simp only [formRel, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not,
      BoundedFormula.realize_all]
    constructor
    · intro h x
      have := h fun _ => x
      rw [show (Sum.elim w (fun _ : Unit => x) ∘ σ) ∘ Sum.inl = w ∘ Sum.inl from rfl, hσ] at this
      exact this
    · intro h u
      have := h (u ())
      rw [show (Sum.elim w u ∘ σ) ∘ Sum.inl = w ∘ Sum.inl from rfl,
        show u = fun _ => u () from funext fun _ => rfl, hσ]
      exact this

/-! ### Definable sets -/

/-- **Definable in `(ℕ, +, V_k)` ⟹ `k`-automatic** (the direction of the Büchi–Bruyère theorem
that Problem 1 needs), with any parameters. -/
theorem isAutomatic_of_definable (hk : 2 ≤ k) {A : Set ℕ} {f : ℕ → Bool}
    (h : A.Definable₁ (buchi k) {t | f t = true}) : IsAutomatic k f := by
  classical
  obtain ⟨φ, hφ⟩ := h
  refine ((recognizable_formRel hk φ).image fun Q n => decide ((fun _ => n) ∈ Q)).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  refine ⟨sect k (formRel φ) e (fun _ => r), ⟨e, fun _ => r, fun _ => hr, rfl⟩, ?_⟩
  funext n
  have hmem := congrArg (fun s : Set (Fin 1 → ℕ) => (fun _ => k ^ e * n + r) ∈ s) hφ
  simp only [Set.mem_ofPred_eq, eq_iff_iff] at hmem
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hmem]
  exact Iff.of_eq (congrArg (BoundedFormula.Realize φ (fun _ => k ^ e * n + r))
    (Subsingleton.elim _ _))

/-- The inclusion of Presburger arithmetic into Büchi arithmetic. -/
def presburgerToBuchi (k : ℕ) : presburger →ᴸ buchi k where
  onFunction
  | _, .zero => .zero
  | _, .one => .one
  | _, .add => .add
  onRelation _ R := Empty.elim R

instance (k : ℕ) : (presburgerToBuchi k).IsExpansionOn ℕ where
  map_onFunction f x := by cases f <;> rfl
  map_onRelation R := Empty.elim R

/-- Eventually periodic sets are definable in `(ℕ, +, V_k)`: they are already
Presburger-definable. -/
theorem definable_of_eventuallyPeriodic {f : ℕ → Bool} (hf : EventuallyPeriodic f) (k : ℕ)
    (A : Set ℕ) : A.Definable₁ (buchi k) {t | f t = true} := by
  have h : A.Definable₁ presburger {t | f t = true} :=
    presburger.definable₁_iff_ultimately_periodic.2
      ((LogicAutomata.eventuallyPeriodic_iff_ultimately_periodic f).1 hf)
  exact Set.Definable.map_expansion h (presburgerToBuchi k)

/-- **Cobham–Semenov for sets of naturals.** For multiplicatively independent `a, b ≥ 2`, a set
definable both in `(ℕ, +, V_a)` and in `(ℕ, +, V_b)` is eventually periodic. -/
theorem eventuallyPeriodic_of_definable {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ m n, 0 < m → 0 < n → a ^ m ≠ b ^ n) {f : ℕ → Bool} {A : Set ℕ}
    (hfa : A.Definable₁ (buchi a) {t | f t = true})
    (hfb : A.Definable₁ (buchi b) {t | f t = true}) :
    EventuallyPeriodic f :=
  Cobham.eventuallyPeriodic_of_isAutomatic ha hb hab (isAutomatic_of_definable ha hfa)
    (isAutomatic_of_definable hb hfb)

/-! ### Problem 1 in Büchi arithmetic -/

/-- A sequence is eventually periodic iff its set of `true` times is definable both in
`(ℕ, +, V₂)` and in `(ℕ, +, V₃)`, with any parameters. -/
theorem eventuallyPeriodic_iff_buchi_definable (f : ℕ → Bool) (A : Set ℕ) :
    EventuallyPeriodic f ↔
      A.Definable₁ (buchi 2) {t | f t = true} ∧ A.Definable₁ (buchi 3) {t | f t = true} :=
  ⟨fun hf => ⟨definable_of_eventuallyPeriodic hf 2 A, definable_of_eventuallyPeriodic hf 3 A⟩,
    fun ⟨h2, h3⟩ => eventuallyPeriodic_of_definable le_rfl (by norm_num)
      (fun _ _ hm _ => Cobham.two_pow_ne_three_pow hm) h2 h3⟩

/-- **Büchi arithmetic.** Problem 1 holds iff the black times are not definable both in
`(ℕ, +, V₂)` and in `(ℕ, +, V₃)`, with any parameters `A`. -/
theorem problem1_iff_not_buchi_definable (A : Set ℕ) : Rule30Prize.Problem1 ↔
    ¬ (A.Definable₁ (buchi 2) {t | c t = true} ∧ A.Definable₁ (buchi 3) {t | c t = true}) := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_buchi_definable]

end Rule30Equivalents.BuchiArithmetic
