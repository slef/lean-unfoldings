module

public import Unfoldings.Cap.ClipEdgeLift
public import Unfoldings.Cap.ClippedCapCoordinates
public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Geometry.SubsegmentEndpoints

/-! Exact whole-edge meshing preserves actual original intrinsic vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ}

namespace ClipSpatialTriangles

variable (T : K.ClipSpatialTriangles Z)

local instance endpointClipIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Covering a genuine old segment by whole fine edges forces its first endpoint to be a fine
intrinsic vertex, rather than a point in an edge interior. -/
theorem vertex_of_segment_endpoint (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (lower : Z < 0) {a b : Plane} (different : a ≠ b)
    (cover : segment ℝ a b =
      ⋃ e : {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆ segment ℝ a b},
        (T.projectedTriangle e.val.1).edge e.val.2) :
    ∃ w : T.pairedComplex.Vertex Set.univ,
      (T.normalizedCap conforming lower).projectedVertex w = a := by
  let Q := T.normalizedCap conforming lower
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (cover.subset (left_mem_segment ℝ a b))
  rcases left_endpoint_of_subsegment different on_edge e.property with first | last
  · refine ⟨T.pairedComplex.vertexOfCorner Set.univ (e.val.1, e.val.2), ?_⟩
    exact (Q.projectedVertex_ofCorner _ _).trans
      ((T.normalizedCap_projectedTriangle_vertex conforming lower _ _).trans first.symm)
  · refine ⟨T.pairedComplex.vertexOfCorner Set.univ (e.val.1, Triangle.next e.val.2), ?_⟩
    exact (Q.projectedVertex_ofCorner _ _).trans
      ((T.normalizedCap_projectedTriangle_vertex conforming lower _ _).trans last.symm)

end ClipSpatialTriangles

namespace LineAlignedClip

variable (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalVertexClipIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

/-- Every original vertex survives the actual line-aligned physical roof triangulation. -/
theorem original_vertex_preserved (lower : Z < 0) (w : C.Vertex Set.univ) :
    ∃ z : L.partition.pairedComplex.Vertex Set.univ,
      (L.partition.normalizedCap L.conforming lower).projectedVertex z = K.projectedVertex w := by
  obtain ⟨⟨f, k⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ w
  obtain ⟨z, at_endpoint⟩ := L.partition.vertex_of_segment_endpoint L.conforming lower
    ((K.projectedTriangle f).edge_endpoints_ne k) (L.original_edge_eq_union_subedges lower f k)
  exact ⟨z, at_endpoint.trans
    ((K.projectedVertex_ofCorner f k).symm.trans (congrArg K.projectedVertex at_corner))⟩

end LineAlignedClip
end Unfoldings.ConvexCap
