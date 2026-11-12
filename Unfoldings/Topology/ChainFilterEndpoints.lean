module

public import Unfoldings.Topology.ChainIdentityContraction

/-! Removing identity pieces preserves the two physical endpoints of every surviving chain. -/

@[expose] public section

namespace Unfoldings

variable {α β : Type*} (first last : α → β) (keep : α → Bool)

theorem chain_filter_head_of_removed_identity (pieces : List α)
    (chain : pieces.IsChain (fun a b => last a = first b))
    (removed : ∀ a ∈ pieces, keep a = false → first a = last a)
    {x : α} (head : (pieces.filter keep).head? = some x) :
    pieces.head?.map first = some (first x) := by
  induction pieces with
  | nil => simp only [List.filter_nil, List.head?_nil, reduceCtorEq] at head
  | cons a pieces ih =>
    have remaining : ∀ b ∈ pieces, keep b = false → first b = last b :=
      fun b member => removed b (List.mem_cons_of_mem _ member)
    cases active : keep a with
    | false =>
      have next : (pieces.filter keep).head? = some x := by
        simpa only [List.filter_cons, active, Bool.false_eq_true, ↓reduceIte] using head
      have contact := ih chain.tail remaining next
      cases pieces with
      | nil => simp only [List.filter_nil, List.head?_nil, reduceCtorEq] at next
      | cons b pieces =>
        have equal : first b = first x := Option.some.inj contact
        exact congrArg some ((removed a (List.mem_cons_self ..) active).trans
          (chain.rel.trans equal))
    | true =>
      have same : a = x := Option.some.inj (by
        simpa only [List.filter_cons, active, ↓reduceIte, List.head?_cons] using head)
      subst x
      rfl

theorem chain_filter_last_of_removed_identity (pieces : List α)
    (chain : pieces.IsChain (fun a b => last a = first b))
    (removed : ∀ a ∈ pieces, keep a = false → first a = last a)
    {x : α} (end_point : (pieces.filter keep).getLast? = some x) :
    pieces.getLast?.map last = some (last x) := by
  have reversed : pieces.reverse.IsChain (fun a b => first a = last b) :=
    List.isChain_reverse.mpr (chain.imp (fun _ _ equal => equal.symm))
  have endpoint : (pieces.reverse.filter keep).head? = some x := by
    simpa only [List.filter_reverse, List.head?_reverse] using end_point
  have matched := chain_filter_head_of_removed_identity last first keep pieces.reverse reversed
    (fun a member absent => (removed a (List.mem_reverse.mp member) absent).symm) endpoint
  simpa only [List.head?_reverse] using matched

end Unfoldings
