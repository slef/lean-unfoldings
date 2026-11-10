module

public import Unfoldings.Topology.RootedForest

/-! Empty forests and the one-boundary-root condition, with both failure modes. -/

@[expose] public section

namespace Unfoldings.Examples

open SimpleGraph

def singleCutEdge : SimpleGraph Bool := edge false true

theorem singleCutEdge_acyclic : singleCutEdge.IsAcyclic :=
  IsAcyclic.of_card_le_two (by simp)

theorem singleCutEdge_one_root : singleCutEdge.IsRootedForest {false} := by
  refine ⟨singleCutEdge_acyclic, ?_⟩
  intro v
  refine ⟨false, ⟨rfl, ?_⟩, ?_⟩
  · cases v
    · exact Reachable.rfl
    · exact Adj.reachable (by simp [singleCutEdge, edge_adj])
  · rintro r ⟨hr, _⟩
    exact hr

theorem singleCutEdge_two_roots_not_forest : ¬ singleCutEdge.IsRootedForest Set.univ := by
  intro rooted
  have reachable : singleCutEdge.Reachable false true :=
    Adj.reachable (by simp [singleCutEdge, edge_adj])
  exact Bool.false_ne_true (rooted.roots_separated (Set.mem_univ _) (Set.mem_univ _) reachable)

theorem singleCutEdge_no_roots_not_forest : ¬ singleCutEdge.IsRootedForest ∅ := by
  intro rooted
  obtain ⟨r, ⟨hr, _⟩, _⟩ := rooted.2 false
  exact hr

theorem empty_cut_forest : (⊥ : SimpleGraph Empty).IsRootedForest ∅ :=
  isRootedForest_empty_iff.mpr inferInstance

theorem empty_cut_extension_tree : ((⊥ : SimpleGraph Empty).rootExtension ∅).IsTree :=
  (rootExtension_tree_iff _ ∅ Set.finite_empty).mpr empty_cut_forest

end Unfoldings.Examples
