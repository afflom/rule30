module

public import Ruliology.CellularAutomata.Rule30Predecessors

/-!
# Rule 30 on a cyclic register: how many configurations have 0, 1, 2 or 3 predecessors

Companion to `Ruliology.CellularAutomata.Rule30Predecessors` (the corrected Feynman theorem).
Let `numWithPreds k N` be the number of registers of length `N` with exactly `k` predecessors.

* `sum_predCount`: the predecessor counts add up to `2 ^ N`, since every register has exactly
  one successor.
* `numWithPreds_three`: exactly one register has three predecessors when `3 ∣ N` (all `1`s), and
  none otherwise.
* `numWithPreds_total` and `numWithPreds_weighted`: `c₀ + c₁ + c₂ + c₃ = 2 ^ N` and
  `c₁ + 2 c₂ + 3 c₃ = 2 ^ N`.
* `numWithPreds_zero`: `c₀ = c₂ + 2 · [3 ∣ N]`. There are as many configurations without
  predecessors (Garden-of-Eden states) as with two, plus two when `3 ∣ N`.

`hasPreds_iff` connects `predCount` with the predecessor count `HasPreds` of the main file.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30

/-! ### All registers of a given length -/

/-- All Boolean lists of length `n`. -/
def regs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (regs n).map (false :: ·) ++ (regs n).map (true :: ·)

theorem mem_regs : ∀ {n : Nat} {x : List Bool}, x ∈ regs n ↔ x.length = n
  | 0, x => by cases x <;> simp [regs]
  | n + 1, [] => by simp [regs]
  | n + 1, b :: x => by
    cases b <;> simp [regs, mem_regs]

theorem nodup_regs : ∀ n, (regs n).Nodup
  | 0 => by simp [regs]
  | n + 1 => by
    rw [regs, List.nodup_append]
    refine ⟨List.Pairwise.map _ (fun a b hab e => hab (List.cons.inj e).2) (nodup_regs n),
      List.Pairwise.map _ (fun a b hab e => hab (List.cons.inj e).2) (nodup_regs n), ?_⟩
    intro a ha b hb hab
    simp only [List.mem_map] at ha hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    exact absurd (List.cons.inj hab).1 (by decide)

theorem length_regs : ∀ n, (regs n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by simp [regs, length_regs n, Nat.pow_succ]; omega

/-! ### Rule 30 preserves length -/

theorem length_lin : ∀ w : List Bool, (lin w).length = w.length - 2
  | a :: b :: c :: rest => by
    simp only [lin, List.length_cons, length_lin (b :: c :: rest)]
    omega
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl

theorem length_step (x : List Bool) : (step x).length = x.length := by
  simp [step, ext, length_lin]

/-! ### Predecessor counts as counts over all registers -/

/-- `predCount y` is the number of registers of length `y.length` that step to `y`. -/
theorem predCount_eq_countP (y : List Bool) (hy : y ≠ []) :
    predCount y = (regs y.length).countP (fun x => step x == y) := by
  obtain ⟨L, hL, hlen, hmem⟩ := hasPreds y hy
  rw [← hlen, List.countP_eq_length_filter]
  apply length_eq_of_nodup hL ((nodup_regs _).sublist List.filter_sublist)
  intro x
  rw [hmem, List.mem_filter, mem_regs, beq_iff_eq]

/-- `HasPreds y k` holds exactly for `k = predCount y`. -/
theorem hasPreds_iff (y : List Bool) (hy : y ≠ []) (k : Nat) : HasPreds y k ↔ predCount y = k :=
  ⟨fun h => (hasPreds y hy).unique h, fun h => h ▸ hasPreds y hy⟩

/-! ### Double counting -/

theorem sum_map_zero {β : Type} : ∀ (Y : List β), (Y.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: Y => by simp [sum_map_zero Y]

theorem sum_map_add {β : Type} (f g : β → Nat) :
    ∀ Y : List β, (Y.map fun y => f y + g y).sum = (Y.map f).sum + (Y.map g).sum
  | [] => rfl
  | y :: Y => by simp only [List.map_cons, List.sum_cons, sum_map_add f g Y]; omega

theorem sum_map_ite {β : Type} (p : β → Bool) :
    ∀ Y : List β, (Y.map fun y => if p y then 1 else 0).sum = Y.countP p
  | [] => rfl
  | y :: Y => by
    simp only [List.map_cons, List.sum_cons, List.countP_cons, sum_map_ite p Y]
    omega

/-- Swap the order of a double count. -/
theorem sum_countP_swap {α β : Type} (p : α → β → Bool) :
    ∀ (X : List α) (Y : List β),
      (Y.map fun y => X.countP fun x => p x y).sum = (X.map fun x => Y.countP fun y => p x y).sum
  | [], Y => by simp [sum_map_zero]
  | x :: X, Y => by
    have e1 : (Y.map fun y => (x :: X).countP fun x' => p x' y) =
        Y.map fun y => X.countP (fun x' => p x' y) + (if p x y then 1 else 0) := by
      apply List.map_congr_left
      intro y _
      rw [List.countP_cons]
    rw [e1, sum_map_add (fun y => X.countP fun x' => p x' y) (fun y => if p x y then 1 else 0),
      sum_countP_swap p X Y, sum_map_ite (fun y => p x y), List.map_cons, List.sum_cons,
      Nat.add_comm]

/-- Every register has exactly one successor, so the predecessor counts add up to `2 ^ N`. -/
theorem sum_predCount (N : Nat) (hN : 1 ≤ N) : ((regs N).map predCount).sum = 2 ^ N := by
  have h1 : ((regs N).map predCount).sum =
      ((regs N).map fun y => (regs N).countP fun x => step x == y).sum := by
    congr 1
    apply List.map_congr_left
    intro y hy
    have hl := mem_regs.1 hy
    rw [predCount_eq_countP y (by intro h; rw [h] at hl; simp at hl; omega), hl]
  rw [h1, sum_countP_swap, ← length_regs N]
  -- each register has exactly one successor among the registers
  have h2 : ∀ x ∈ regs N, ((regs N).countP fun y => step x == y) = 1 := by
    intro x hx
    have hs : step x ∈ regs N := mem_regs.2 (by rw [length_step]; exact mem_regs.1 hx)
    rw [List.countP_eq_length_filter]
    have := (nodup_regs N).count (a := step x)
    rw [ite_eq_left hs, List.count_eq_length_filter] at this
    rw [← this]
    congr 1
    apply List.filter_congr
    intro y _
    by_cases e : step x = y
    · subst e
      simp
    · have e' : y ≠ step x := fun h => e h.symm
      rw [beq_eq_false_iff_ne.2 e, beq_eq_false_iff_ne.2 e']
  rw [List.map_congr_left h2]
  clear h1 h2
  generalize regs N = R
  induction R with
  | nil => rfl
  | cons _ R ih => simp [ih]; omega

/-! ### The counts -/

/-- The number of registers of length `N` with exactly `k` predecessors. -/
def numWithPreds (k N : Nat) : Nat := (regs N).countP fun y => predCount y == k

theorem predCount_le_three (y : List Bool) (hy : y ≠ []) : predCount y ≤ 3 := by
  rcases predCount_cases y hy with h | h | h | h <;> omega

theorem ne_nil_of_mem_regs {N : Nat} (hN : 1 ≤ N) {y : List Bool} (hy : y ∈ regs N) : y ≠ [] := by
  intro h
  have := mem_regs.1 hy
  rw [h] at this
  simp at this
  omega

theorem sum_eq_counts {β : Type} (f : β → Nat) : ∀ Y : List β, (∀ y ∈ Y, f y ≤ 3) →
    (Y.map f).sum = Y.countP (fun y => f y == 1) + 2 * Y.countP (fun y => f y == 2) +
      3 * Y.countP (fun y => f y == 3)
  | [], _ => rfl
  | y :: Y, h => by
    have ih := sum_eq_counts f Y (fun z hz => h z (by simp [hz]))
    have hy := h y (by simp)
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih, beq_iff_eq]
    rcases (show f y = 0 ∨ f y = 1 ∨ f y = 2 ∨ f y = 3 by omega) with e | e | e | e <;>
      simp [e] <;> omega

theorem length_eq_counts {β : Type} (f : β → Nat) : ∀ Y : List β, (∀ y ∈ Y, f y ≤ 3) →
    Y.length = Y.countP (fun y => f y == 0) + Y.countP (fun y => f y == 1) +
      Y.countP (fun y => f y == 2) + Y.countP (fun y => f y == 3)
  | [], _ => rfl
  | y :: Y, h => by
    have ih := length_eq_counts f Y (fun z hz => h z (by simp [hz]))
    have hy := h y (by simp)
    simp only [List.length_cons, List.countP_cons, ih, beq_iff_eq]
    rcases (show f y = 0 ∨ f y = 1 ∨ f y = 2 ∨ f y = 3 by omega) with e | e | e | e <;>
      simp [e] <;> omega

/-- `c₀ + c₁ + c₂ + c₃ = 2 ^ N`. -/
theorem numWithPreds_total (N : Nat) (hN : 1 ≤ N) :
    numWithPreds 0 N + numWithPreds 1 N + numWithPreds 2 N + numWithPreds 3 N = 2 ^ N := by
  rw [← length_regs N, length_eq_counts predCount (regs N)
    (fun y hy => predCount_le_three y (ne_nil_of_mem_regs hN hy))]
  rfl

/-- `c₁ + 2 c₂ + 3 c₃ = 2 ^ N`. -/
theorem numWithPreds_weighted (N : Nat) (hN : 1 ≤ N) :
    numWithPreds 1 N + 2 * numWithPreds 2 N + 3 * numWithPreds 3 N = 2 ^ N := by
  rw [← sum_predCount N hN, sum_eq_counts predCount (regs N)
    (fun y hy => predCount_le_three y (ne_nil_of_mem_regs hN hy))]
  rfl

/-- One register (all `1`s) has three predecessors when `3 ∣ N`, and none otherwise. -/
theorem numWithPreds_three (N : Nat) (hN : 1 ≤ N) :
    numWithPreds 3 N = if N % 3 = 0 then 1 else 0 := by
  have hc : numWithPreds 3 N =
      (regs N).countP fun y => y == List.replicate N true && decide (N % 3 = 0) := by
    apply List.countP_congr
    intro y hy
    have hl := mem_regs.1 hy
    rw [beq_iff_eq, predCount_eq_three_iff y (ne_nil_of_mem_regs hN hy), hl]
    simp
  rw [hc]
  split
  · rename_i h
    simp only [h, decide_true, Bool.and_true]
    have := (nodup_regs N).count (a := List.replicate N true)
    rw [ite_eq_left (mem_regs.2 (by simp))] at this
    rw [← this, List.count]
  · rename_i h
    simp [h]

/-- **Counting corollary.** `c₀ = c₂ + 2 · [3 ∣ N]`: as many configurations have no predecessor
as have two, plus two more when `3 ∣ N`. -/
theorem numWithPreds_zero (N : Nat) (hN : 1 ≤ N) :
    numWithPreds 0 N = numWithPreds 2 N + 2 * (if N % 3 = 0 then 1 else 0) := by
  have h₁ := numWithPreds_total N hN
  have h₂ := numWithPreds_weighted N hN
  rw [← numWithPreds_three N hN]
  omega

example : (List.range 4).map (fun k => numWithPreds k 6) = [12, 41, 10, 1] := by decide

end Rule30
end Ruliology.CellularAutomata
