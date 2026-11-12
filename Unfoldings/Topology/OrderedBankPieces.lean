module

public import Mathlib.Data.List.Chain

/-! Consecutive ordered bank intervals are ordered pairwise along an entire finite chain. -/

@[expose] public section

namespace Unfoldings

theorem ordered_bank_pieces_pairwise {α β : Type*} [Preorder β]
    (first last : α → β) (pieces : List α)
    (within : ∀ a ∈ pieces, first a ≤ last a)
    (chain : pieces.IsChain (fun a b => last a ≤ first b)) :
    pieces.Pairwise (fun a b => last a ≤ first b) := by
  induction pieces with
  | nil => exact List.Pairwise.nil
  | cons x pieces ih =>
    have remaining : ∀ a ∈ pieces, first a ≤ last a :=
      fun a member => within a (List.mem_cons_of_mem _ member)
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih remaining chain.tail⟩
    cases pieces with
    | nil => simp
    | cons y pieces =>
      have ordered : (y :: pieces).IsChain (fun a b => first a ≤ first b) :=
        List.IsChain.imp_of_mem_imp
          (fun a b member _ relation => (remaining a member).trans relation) chain.tail
      have below : ∀ a ∈ y :: pieces, first y ≤ first a :=
        List.IsChain.induction (fun a => first y ≤ first a) (y :: pieces) ordered
          (fun {a b} relation bound => bound.trans relation) (fun _ => le_rfl)
      exact fun a member => chain.rel.trans (below a member)

end Unfoldings
