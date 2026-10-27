module

public import Ruliology.CellularAutomata.Rule30ShortTail

@[expose] public section

/-!
Reduce every Boolean tail of length at most five to the shorter-tail
family or one of eight new black-ended cores. Removing white ends and
rotating finite periods preserves the eventual-word assertion.
-/
namespace Ruliology.CellularAutomata.Rule30FiveTailReduction
open Rule30Jen Rule30Realization Rule30WordRotation

def fiveCores : List (List Bool) :=
  [[true,false,false,false,true], [true,false,false,true,true],
   [true,false,true,false,true], [true,false,true,true,true],
   [true,true,false,false,true], [true,true,false,true,true],
   [true,true,true,false,true], [true,true,true,true,true]]

private def words : List (List Bool) := (List.range 6).flatMap Rule30Jen.allLists
private theorem decomposition_check : words.all (fun u =>
    u.all (! ·) || (shortCores ++ fiveCores).any (fun v => (List.range 6).any (fun a =>
      (List.range 6).any (fun b => u == List.replicate a false ++ v ++ List.replicate b false)))) = true :=
  by decide +kernel

theorem decomposition (u : List Bool) (hlen : u.length ≤ 5) :
    (∀ b, b ∈ u → b = false) ∨ ∃ a b v, v ∈ shortCores ++ fiveCores ∧
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

/-- The eight length-five core exclusions imply every length-at-most-five exclusion.
The threshold is a sufficient bound; this theorem does not provide the core proofs. -/
theorem no_five_tail_of_cores {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (hcores : ∀ v, v ∈ fiveCores → ∀ r, 69 ≤ r →
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v))
    (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
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
    · have hvlen : v.length ≤ 4 := by
        simp only [shortCores,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact Rule30ShortTail.no_short_tail_leftFinite hlo hzero i v hvlen
        (b+(r+a)) (by omega) hrot
    · exact hcores v hv (b+(r+a)) (by omega) hrot

end Ruliology.CellularAutomata.Rule30FiveTailReduction
