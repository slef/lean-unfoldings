module

public import Mathlib.Data.List.Chain

/-! Removing identity pieces preserves the endpoint matches in a finite composable chain. -/

@[expose] public section

namespace Unfoldings

variable {α β : Type*} (first last : α → β) (keep : α → Bool)

/-- The retained first piece is allowed to be an identity too. Only removed
pieces must have equal endpoints. No transitivity of the chain relation is assumed. -/
theorem chain_filter_tail_of_removed_identity (pieces : List α) (x : α)
    (chain : (x :: pieces).IsChain (fun a b => last a = first b))
    (removed : ∀ a ∈ pieces, keep a = false → first a = last a) :
    (x :: pieces.filter keep).IsChain (fun a b => last a = first b) := by
  induction pieces generalizing x with
  | nil => exact List.isChain_singleton _
  | cons y pieces ih =>
    have remaining : ∀ a ∈ pieces, keep a = false → first a = last a :=
      fun a member => removed a (List.mem_cons_of_mem _ member)
    cases active : keep y with
    | false =>
      have identity := removed y (List.mem_cons_self ..) active
      have bridge : (x :: pieces).IsChain (fun a b => last a = first b) :=
        List.IsChain.imp_head (R := fun a b : α => last a = first b)
          (fun {z} relation => chain.rel.trans (identity.trans relation)) chain.tail
      simpa only [List.filter_cons, active, Bool.false_eq_true, ↓reduceIte] using
        ih x bridge remaining
    | true =>
      have kept : (x :: y :: pieces.filter keep).IsChain (fun a b => last a = first b) :=
        List.isChain_cons_cons.mpr ⟨chain.rel, ih y chain.tail remaining⟩
      simpa only [List.filter_cons, active, ↓reduceIte] using kept

/-- Contract every removed identity in one pass, including consecutive ones. -/
theorem chain_filter_of_removed_identity (pieces : List α)
    (chain : pieces.IsChain (fun a b => last a = first b))
    (removed : ∀ a ∈ pieces, keep a = false → first a = last a) :
    (pieces.filter keep).IsChain (fun a b => last a = first b) := by
  induction pieces with
  | nil => exact List.isChain_nil
  | cons x pieces ih =>
    have remaining : ∀ a ∈ pieces, keep a = false → first a = last a :=
      fun a member => removed a (List.mem_cons_of_mem _ member)
    cases active : keep x with
    | false =>
      simpa only [List.filter_cons, active, Bool.false_eq_true, ↓reduceIte] using
        ih chain.tail remaining
    | true =>
      simpa only [List.filter_cons, active, ↓reduceIte] using
        chain_filter_tail_of_removed_identity first last keep pieces x chain remaining

end Unfoldings
