module

public import Ruliology.CellularAutomata.Rule30FiveTail

@[expose] public section

/-!
Reduce every Boolean tail of length at most six to the five-tail
family or one of sixteen new black-ended cores, by trimming white ends
and rotating the resulting finite period.
-/
namespace Ruliology.CellularAutomata.Rule30SixTailReduction
open Rule30Jen Rule30Realization Rule30WordRotation Rule30FiveTailReduction

def sixCores : List (List Bool) :=
  [[true,false,false,false,false,true],
   [true,false,false,false,true,true],
   [true,false,false,true,false,true],
   [true,false,false,true,true,true],
   [true,false,true,false,false,true],
   [true,false,true,false,true,true],
   [true,false,true,true,false,true],
   [true,false,true,true,true,true],
   [true,true,false,false,false,true],
   [true,true,false,false,true,true],
   [true,true,false,true,false,true],
   [true,true,false,true,true,true],
   [true,true,true,false,false,true],
   [true,true,true,false,true,true],
   [true,true,true,true,false,true],
   [true,true,true,true,true,true]]

private def words : List (List Bool) := (List.range 7).flatMap Rule30Jen.allLists
private theorem decomposition_check : words.all (fun u =>
    u.all (! ·) || ((shortCores ++ fiveCores) ++ sixCores).any (fun v => (List.range 7).any (fun a =>
      (List.range 7).any (fun b => u == List.replicate a false ++ v ++ List.replicate b false)))) = true :=
  by decide +kernel

theorem decomposition (u : List Bool) (hlen : u.length ≤ 6) :
    (∀ b, b ∈ u → b = false) ∨ ∃ a b v, v ∈ (shortCores ++ fiveCores) ++ sixCores ∧
      u = List.replicate a false ++ v ++ List.replicate b false := by
  have hmem : u ∈ words := List.mem_flatMap.mpr
    ⟨u.length, List.mem_range.mpr (by omega), Rule30Jen.mem_allLists u⟩
  have h := List.all_eq_true.mp decomposition_check u hmem
  rcases Bool.or_eq_true_iff.mp h with hz | hc
  · left
    intro b hb
    have := List.all_eq_true.mp hz b hb
    cases b <;> simp_all
  · right
    obtain ⟨v, hv, hvcheck⟩ := List.any_eq_true.mp hc
    obtain ⟨a, _, hacheck⟩ := List.any_eq_true.mp hvcheck
    obtain ⟨b, _, hbcheck⟩ := List.any_eq_true.mp hacheck
    exact ⟨a,b,v,hv,by simpa only [beq_iff_eq] using hbcheck⟩

private theorem replicate_append (a b : Nat) :
    List.replicate a false ++ List.replicate b false = List.replicate (a+b) false := by
  induction a with
  | zero => simp
  | succ a ih => simpa [List.replicate_succ, Nat.succ_add] using congrArg (false :: ·) ih

private theorem replicate_getD (r n : Nat) : (List.replicate r false).getD n false = false := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    cases n with
    | zero => simp [List.replicate_succ]
    | succ n => simpa only [List.replicate_succ,List.getD_cons_succ] using ih n

/-- The sixteen length-six core exclusions imply every length-at-most-six exclusion.
The threshold is a sufficient bound; this theorem does not provide the core proofs. -/
theorem no_six_tail_of_cores {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (hcores : ∀ v, v ∈ sixCores → ∀ r, 77 ≤ r →
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v))
    (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  rcases decomposition u hu with hz | ⟨a,b,v,hv,he⟩
  · obtain ⟨T,hT⟩ := hword
    apply Rule30FiniteConfigs.no_column_eventually_constant hlo hzero i
    refine ⟨T,false,fun t ht => ?_⟩
    rw [hT t ht]
    have hzword : ∀ b, b ∈ List.replicate r false ++ u → b = false := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact (List.mem_replicate.mp hb).2
      · exact hz b hb
    rw [List.eq_replicate_of_mem hzword]
    exact replicate_getD _ _
  · rw [he] at hword
    have hw : Rule30FiniteStrips.EventuallyWord x i
        ((List.replicate r false ++ List.replicate a false ++ v) ++ List.replicate b false) := by
      simpa only [List.append_assoc] using hword
    have hrot := eventuallyWord_swap (by simp; omega) hw
    have hlist : List.replicate b false ++ (List.replicate r false ++ List.replicate a false ++ v) =
        List.replicate (b+(r+a)) false ++ v := by
      rw [replicate_append, ← List.append_assoc, replicate_append]
    rw [hlist] at hrot
    rcases List.mem_append.mp hv with hv | hv
    · have hvlen : v.length ≤ 5 := by
        simp only [shortCores, fiveCores, List.mem_append, List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact Rule30FiveTail.no_five_tail_leftFinite hlo hzero i v hvlen
        (b+(r+a)) (by omega) hrot
    · exact hcores v hv (b+(r+a)) (by omega) hrot

end Ruliology.CellularAutomata.Rule30SixTailReduction
