module

public import Unfoldings.Topology.FilterRunChain

/-! First and last survivors retain their actual removed boundary runs. -/

@[expose] public section

namespace Unfoldings

variable {α : Type*} (keep : α → Bool) (pieces : List α)

theorem filter_head_boundary_run {a : α} (at_head : (pieces.filter keep).head? = some a) :
    ∃ before after : List α, pieces = before ++ a :: after ∧
      (∀ x ∈ before, ¬ keep x) ∧ keep a := by
  obtain ⟨rest, equal⟩ := List.head?_eq_some_iff.mp at_head
  obtain ⟨before, after, original, removed, kept, _⟩ := List.filter_eq_cons_iff.mp equal
  exact ⟨before, after, original, removed, kept⟩

theorem filter_last_boundary_run {a : α} (at_last : (pieces.filter keep).getLast? = some a) :
    ∃ before after : List α, pieces = before ++ a :: after ∧
      keep a ∧ ∀ x ∈ after, ¬ keep x := by
  have at_head : (pieces.reverse.filter keep).head? = some a := by
    rwa [List.filter_reverse, List.head?_reverse]
  obtain ⟨before, after, equal, removed, kept⟩ :=
    filter_head_boundary_run keep pieces.reverse at_head
  refine ⟨after.reverse, before.reverse, ?_, kept, ?_⟩
  · have reverse := congrArg List.reverse equal
    simpa only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append] using reverse
  · intro x member
    exact removed x (List.mem_reverse.mp member)

end Unfoldings
