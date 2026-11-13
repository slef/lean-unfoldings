module

public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Geometry.SubsegmentEndpoints

/-! Whole-edge segment coverage preserves actual vertices of spatial envelope meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialEndpointIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem vertex_of_segment_endpoint (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) {a b : Plane} (different : a ≠ b)
    (cover : segment ℝ a b =
      ⋃ e : {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆ segment ℝ a b},
        (T.projectedTriangle e.val.1).edge e.val.2) :
    ∃ w : T.pairedComplex.Vertex Set.univ,
      (T.normalizedCap conforming inside).projectedVertex w = a := by
  let Q := T.normalizedCap conforming inside
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (cover.subset (left_mem_segment ℝ a b))
  rcases left_endpoint_of_subsegment different on_edge e.property with first | last
  · refine ⟨T.pairedComplex.vertexOfCorner Set.univ (e.val.1, e.val.2), ?_⟩
    exact (Q.projectedVertex_ofCorner _ _).trans
      ((T.normalizedCap_projectedTriangle_vertex conforming inside _ _).trans first.symm)
  · refine ⟨T.pairedComplex.vertexOfCorner Set.univ (e.val.1, Triangle.next e.val.2), ?_⟩
    exact (Q.projectedVertex_ofCorner _ _).trans
      ((T.normalizedCap_projectedTriangle_vertex conforming inside _ _).trans last.symm)

end Unfoldings.SpatialEnvelope.Triangulation
