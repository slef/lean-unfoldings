module

public import Unfoldings.Topology.IndexedRun

/-! Indexed actual occurrences of initial and final removed boundary runs. -/

@[expose] public section

namespace Unfoldings

variable {α : Type*} {R : α → α → Prop}

theorem indexed_initial_run_data (whole : List α) (head last : α) (tail after : List α)
    (equal : whole = (head :: tail) ++ last :: after) (chain : whole.IsChain R) :
    let cells : Fin (tail.length + 1) → α := (head :: tail).get
    (∀ j : Fin tail.length, R (cells j.castSucc) (cells j.succ)) ∧
      (∀ a b : Fin (tail.length + 1), a < b → List.Sublist [cells a, cells b] whole) ∧
      (∀ j, List.Sublist [cells j, last] whole) ∧
      R (cells (Fin.last tail.length)) last ∧ whole.head? = some (cells 0) := by
  dsimp only
  subst whole
  have middle : (head :: tail).IsChain R := chain.left_of_append
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · intro j
    exact List.isChain_iff_getElem.mp middle j.val (by simp)
  · intro a b ordered
    exact (pair_getElem_sublist (head :: tail) a.val b.val ordered b.isLt).trans
      (List.sublist_append_left _ _)
  · intro j
    have singleton : List.Sublist [(head :: tail).get j] (head :: tail) :=
      List.singleton_sublist.mpr (List.get_mem _ _)
    exact (singleton.append_right [last]).trans
      ((List.singleton_sublist.mpr (List.mem_cons_self ..)).append_left (head :: tail))
  · have contact := chain.rel_getLast_head_of_append (by simp) (by simp)
    simpa only [List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel,
      List.head_cons, List.get_eq_getElem, Fin.val_last] using contact

theorem indexed_final_run_data (whole : List α) (first head : α) (tail before : List α)
    (equal : whole = before ++ first :: (head :: tail)) (chain : whole.IsChain R) :
    let cells : Fin (tail.length + 1) → α := (head :: tail).get
    (∀ j : Fin tail.length, R (cells j.castSucc) (cells j.succ)) ∧
      (∀ a b : Fin (tail.length + 1), a < b → List.Sublist [cells a, cells b] whole) ∧
      (∀ j, List.Sublist [first, cells j] whole) ∧
      R first (cells 0) ∧ whole.getLast? = some (cells (Fin.last tail.length)) := by
  dsimp only
  subst whole
  have ending : (first :: head :: tail).IsChain R := chain.right_of_append
  have middle : (head :: tail).IsChain R := ending.tail
  refine ⟨?_, ?_, ?_, ending.rel, ?_⟩
  · intro j
    exact List.isChain_iff_getElem.mp middle j.val (by simp)
  · intro a b ordered
    exact ((pair_getElem_sublist (head :: tail) a.val b.val ordered b.isLt).cons first).trans
      (List.sublist_append_right _ _)
  · intro j
    exact (List.Sublist.cons_cons first (List.singleton_sublist.mpr (List.get_mem _ _))).trans
      (List.sublist_append_right _ _)
  · rw [List.getLast?_append, List.getLast?_eq_some_getLast (by simp), Option.some_or]
    simp only [List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel,
      List.get_eq_getElem, Fin.val_last]
    rfl

end Unfoldings
