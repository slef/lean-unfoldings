module

public import Unfoldings.Topology.FilterRunChain

/-! Turn a finite list run into ordered indexed occurrences and exact neighboring contacts. -/

@[expose] public section

namespace Unfoldings

variable {α : Type*} {R : α → α → Prop}

theorem indexed_run_data (whole : List α) (first head last : α) (tail : List α)
    (sublist : List.Sublist (first :: ((head :: tail) ++ [last])) whole)
    (chain : (first :: ((head :: tail) ++ [last])).IsChain R) :
    let cells : Fin (tail.length + 1) → α := (head :: tail).get
    (∀ j : Fin tail.length, R (cells j.castSucc) (cells j.succ)) ∧
      (∀ a b : Fin (tail.length + 1), a < b → List.Sublist [cells a, cells b] whole) ∧
      (∀ j, List.Sublist [first, cells j] whole) ∧
      (∀ j, List.Sublist [cells j, last] whole) ∧
      R first (cells 0) ∧ R (cells (Fin.last tail.length)) last := by
  dsimp only
  have middle : (head :: tail).IsChain R := chain.tail.left_of_append
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact List.isChain_iff_getElem.mp middle j.val (by simp)
  · intro a b ordered
    have pair := pair_getElem_sublist (head :: tail) a.val b.val ordered b.isLt
    exact ((pair.trans (List.sublist_append_left _ [last])).cons first).trans sublist
  · intro j
    have member : (head :: tail).get j ∈ (head :: tail) ++ [last] :=
      List.mem_append_left _ (List.get_mem _ _)
    exact (List.Sublist.cons_cons first (List.singleton_sublist.mpr member)).trans sublist
  · intro j
    have singleton : List.Sublist [(head :: tail).get j] (head :: tail) :=
      List.singleton_sublist.mpr (List.get_mem _ _)
    exact ((singleton.append_right [last]).cons first).trans sublist
  · exact chain.rel
  · have contact := chain.tail.rel_getLast_head_of_append (by simp) (by simp)
    simpa only [List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel,
      List.head_cons, List.get_eq_getElem, Fin.val_last] using contact

end Unfoldings
