module

public import Mathlib.Topology.Connected.Basic

/-! Connected pieces cannot switch between closed sets away from their common contacts. -/

@[expose] public section

namespace Unfoldings

theorem subset_left_or_right_of_closed_cover {X : Type*} [TopologicalSpace X]
    {s a b : Set X} (connected : IsPreconnected s) (left : IsClosed a) (right : IsClosed b)
    (cover : s ⊆ a ∪ b) (separate : Disjoint s (a ∩ b)) : s ⊆ a ∨ s ⊆ b := by
  classical
  by_cases contained : s ⊆ a
  · exact Or.inl contained
  · right
    obtain ⟨x, member, outside⟩ := Set.not_subset.mp contained
    intro y on_set
    by_contra absent
    obtain ⟨z, on_set, both⟩ := isPreconnected_closed_iff.mp connected a b left right cover
      ⟨y, on_set, (cover on_set).resolve_right absent⟩
      ⟨x, member, (cover member).resolve_left outside⟩
    exact Set.disjoint_left.mp separate on_set both

end Unfoldings
