module

public import Unfoldings.Topology.OrderedBankPieces
public import Mathlib.Data.List.Pairwise

/-! The first and last actual bank pieces bound every retained interval. -/

@[expose] public section

namespace Unfoldings

variable {α β : Type*} [Preorder β] (first last : α → β) (pieces : List α)
  (within : ∀ a ∈ pieces, first a ≤ last a)
  (ordered : pieces.Pairwise (fun a b => last a ≤ first b))

include within ordered

theorem first_bank_le_of_head {head a : α} (at_head : pieces.head? = some head)
    (member : a ∈ pieces) : first head ≤ first a := by
  obtain ⟨tail, equal⟩ := List.head?_eq_some_iff.mp at_head
  subst pieces
  rcases List.mem_cons.mp member with rfl | later
  · exact le_rfl
  · exact (within head (List.mem_cons_self ..)).trans
      ((List.pairwise_cons.mp ordered).1 a later)

theorem last_bank_le_of_last {endPiece a : α} (at_last : pieces.getLast? = some endPiece)
    (member : a ∈ pieces) : last a ≤ last endPiece := by
  obtain ⟨before, equal⟩ := List.getLast?_eq_some_iff.mp at_last
  subst pieces
  rcases List.mem_append.mp member with earlier | last_member
  · exact ((List.pairwise_append.mp ordered).2.2 a earlier endPiece
      (List.mem_singleton_self _)).trans
        (within endPiece (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact le_of_eq (congrArg last (List.mem_singleton.mp last_member))

end Unfoldings
