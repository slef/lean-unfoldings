module

public import Unfoldings.Topology.OrderedBankEndpoints

/-! A different bank piece lies beyond the whole first or last retained interval. -/

@[expose] public section

namespace Unfoldings

variable {α β : Type*} [Preorder β] (first last : α → β) (pieces : List α)
  (ordered : pieces.Pairwise (fun a b => last a ≤ first b))

include ordered

theorem last_bank_le_first_of_ne_last {endPiece a : α}
    (at_last : pieces.getLast? = some endPiece) (member : a ∈ pieces) (different : a ≠ endPiece) :
    last a ≤ first endPiece := by
  obtain ⟨before, rfl⟩ := List.getLast?_eq_some_iff.mp at_last
  rcases List.mem_append.mp member with earlier | at_end
  · exact (List.pairwise_append.mp ordered).2.2 a earlier endPiece (List.mem_singleton_self _)
  · exact (different (List.mem_singleton.mp at_end)).elim

theorem last_head_bank_le_first_of_ne_head {head a : α}
    (at_head : pieces.head? = some head) (member : a ∈ pieces) (different : a ≠ head) :
    last head ≤ first a := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp at_head
  rcases List.mem_cons.mp member with same | later
  · exact (different same).elim
  · exact (List.pairwise_cons.mp ordered).1 a later

end Unfoldings
