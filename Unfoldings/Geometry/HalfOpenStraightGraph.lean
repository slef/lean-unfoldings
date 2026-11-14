module

public import Unfoldings.Geometry.StraightGraphLinks

/-! Directed straight graph edges with unique initial vertices have disjoint half-open images. -/

@[expose] public section

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {G : FiniteEmbeddedGraph V E X} (straight : G.IsStraight)

include straight in
theorem IsStraight.halfOpen_segments_disjoint (outgoing : Function.Injective G.left) :
    Pairwise (fun e f => Disjoint
      (segment ℝ (G.vertex (G.left e)) (G.vertex (G.right e)) \ {G.vertex (G.right e)})
      (segment ℝ (G.vertex (G.left f)) (G.vertex (G.right f)) \ {G.vertex (G.right f)})) := by
  intro e f different
  apply Set.disjoint_left.mpr
  rintro x ⟨first, not_last⟩ ⟨second, not_last_f⟩
  have last_ne : x ≠ G.vertex (G.right e) := not_last
  have last_f_ne : x ≠ G.vertex (G.right f) := not_last_f
  by_cases first_eq : x = G.vertex (G.left e)
  · by_cases second_eq : x = G.vertex (G.left f)
    · exact different (outgoing (G.vertex_injective (first_eq.symm.trans second_eq)))
    · have inside := mem_openSegment_of_ne_left_right (Ne.symm second_eq) last_f_ne.symm second
      exact straight.openSegment_avoids_vertices (Or.inl ⟨rfl, rfl⟩ :
        G.graph.IsLink f (G.left f) (G.right f)) (first_eq ▸ inside)
  · have inside := mem_openSegment_of_ne_left_right (Ne.symm first_eq) last_ne.symm first
    by_cases second_eq : x = G.vertex (G.left f)
    · exact straight.openSegment_avoids_vertices (Or.inl ⟨rfl, rfl⟩ :
        G.graph.IsLink e (G.left e) (G.right e)) (second_eq ▸ inside)
    · exact Set.disjoint_left.mp (straight.openSegments_disjoint different
        (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)) inside
        (mem_openSegment_of_ne_left_right (Ne.symm second_eq) last_f_ne.symm second)

end Unfoldings.FiniteEmbeddedGraph
