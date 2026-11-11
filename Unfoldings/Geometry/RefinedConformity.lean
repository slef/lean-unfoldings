module

public import Unfoldings.Geometry.RefinedParentIntersections
public import Unfoldings.Geometry.RefinedFanIntersections
public import Unfoldings.Geometry.ConformingTriangles

/-! The common boundary subdivision yields a genuinely face-to-face triangle partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.CommonTriangleRefinement

variable {I : Type*} {original : I → Triangle} (R : CommonTriangleRefinement original)

/-- The actual endpoints of a globally named base are refined triangle vertices. -/
theorem base_endpoint_isVertex (j : R.Index) {v : R.Vertex}
    (endpoint : v = R.graph.left j.2.val ∨ v = R.graph.right j.2.val) :
    (R.triangle j).IsVertex (R.graph.vertex v) := by
  rcases endpoint with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- Subdividing all parent boundaries together removes all partial-edge contacts. -/
theorem conforming
    (parents_separated : Pairwise (fun i j =>
      Disjoint (interior (original i).carrier) (interior (original j).carrier))) :
    TriangleFamily.Conforming R.triangle := by
  intro j k different p member
  by_cases same_parent : j.1 = k.1
  · obtain ⟨i, e⟩ := j
    obtain ⟨l, f⟩ := k
    change i = l at same_parent
    subst l
    by_cases center : p = R.center i
    · exact Or.inl ⟨⟨0, center.symm⟩, ⟨0, center.symm⟩⟩
    · exact Or.inr (R.same_parent_intersection_shared_edge i e f
        (fun equal => different (congrArg (Sigma.mk i) equal)) member.1 member.2 center)
  · by_cases same_base : j.2.val = k.2.val
    · refine Or.inr ⟨1, 1, ?_, ?_⟩
      · rw [R.base_edge j, R.base_edge k, same_base]
      · rw [R.base_edge j]
        exact (R.different_parent_intersection_bases parents_separated same_parent member).1
    · obtain ⟨v, at_v, first, last⟩ :=
        R.different_parent_distinct_base parents_separated same_parent same_base member
      exact Or.inl ⟨at_v ▸ R.base_endpoint_isVertex j first,
        at_v ▸ R.base_endpoint_isVertex k last⟩

end Unfoldings.CommonTriangleRefinement
