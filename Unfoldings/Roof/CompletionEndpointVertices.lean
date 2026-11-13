module

public import Unfoldings.Roof.CompletionOriginalEdgeCover
public import Unfoldings.Roof.SpatialEnvelopeEndpointVertices

/-! Every original vertex survives as an actual vertex of the physical completion mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionEndpointIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

theorem original_vertex_preserved (w : C.Vertex Set.univ) :
    ∃ z : E.partition.pairedComplex.Vertex Set.univ,
      E.cap.projectedVertex z = K.projectedVertex w := by
  obtain ⟨⟨f, k⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ w
  obtain ⟨z, at_endpoint⟩ := E.partition.vertex_of_segment_endpoint E.conforming E.interior_nonempty
    ((K.projectedTriangle f).edge_endpoints_ne k) (E.original_edge_eq_union_subedges f k)
  exact ⟨z, at_endpoint.trans
    ((K.projectedVertex_ofCorner f k).symm.trans (congrArg K.projectedVertex at_corner))⟩

end Unfoldings.ConvexRoof.CompletionMesh
