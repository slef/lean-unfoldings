module

public import Unfoldings.Roof.SpatialEnvelopeEndpointVertices
public import Unfoldings.Complex.VertexCopyFibers

/-! Every original metric copy above a preserved mesh endpoint is its original vertex copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance vertexFiberIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Vertical cap normalization keeps the exact projected original vertex. -/
theorem normalizedCap_projectedVertex_eq
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (v : T.pairedComplex.Vertex Set.univ) :
    (T.normalizedCap conforming inside).projectedVertex v =
      Cap.horizontal (T.pairedFolding.toSpace Set.univ
        (T.pairedComplex.vertexPoint Set.univ v)) := by
  obtain ⟨⟨f, k⟩, rfl⟩ := T.pairedComplex.vertexOfCorner_surjective Set.univ v
  have projected := ((T.normalizedCap conforming inside).projectedVertex_ofCorner f k).trans
    (T.normalizedCap_projectedTriangle_vertex conforming inside f k)
  apply projected.trans
  exact (((family (T.support f)).horizontal_place ((T.triangle f).vertex k)).trans
    ((family (T.support f)).project.apply_symm_apply _)).symm

/-- Restoring cuts keeps the exact original projected vertex in the unnormalized mesh roof. -/
theorem roof_projectedVertex_vertexForgetCuts
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (retain : Set T.pairedComplex.Seam)
    (v : T.pairedComplex.Vertex retain) :
    (T.roof conforming inside).projectedVertex
      (T.pairedComplex.vertexForgetCuts (Set.subset_univ retain) v) =
        Cap.horizontal (T.pairedFolding.toSpace retain (T.pairedComplex.vertexPoint retain v)) :=
  (congrArg (fun x => Cap.horizontal (T.pairedFolding.toSpace Set.univ x))
    (T.pairedComplex.vertexPoint_vertexForgetCuts (Set.subset_univ retain) v)).trans
    (congrArg Cap.horizontal (T.pairedFolding.toSpace_forgetCuts (Set.subset_univ retain) _))

/-- Every retained metric copy above an original full vertex is an actual original cut vertex. -/
theorem exists_vertexPoint_of_projected_eq
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (retain : Set T.pairedComplex.Seam)
    (v : T.pairedComplex.Vertex Set.univ) (x : T.pairedComplex.Realization retain)
    (same : Cap.horizontal (T.pairedFolding.toSpace retain x) =
      (T.normalizedCap conforming inside).projectedVertex v) :
    ∃ w : T.pairedComplex.Vertex retain, T.pairedComplex.vertexPoint retain w = x := by
  let included := Set.subset_univ retain
  have full := T.pairedProjection_injective conforming
    ((congrArg Cap.horizontal (T.pairedFolding.toSpace_forgetCuts included x)).trans
      (same.trans (T.normalizedCap_projectedVertex_eq conforming inside v)))
  exact (T.pairedComplex.forgetCuts_mem_range_vertexPoint_iff included x).mp ⟨v, full.symm⟩

/-- Whole-edge coverage preserves every cut copy at the segment's original first endpoint. -/
theorem exists_vertexPoint_of_segment_endpoint
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) {a b : Plane} (different : a ≠ b)
    (cover : segment ℝ a b =
      ⋃ e : {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆ segment ℝ a b},
        (T.projectedTriangle e.val.1).edge e.val.2)
    (retain : Set T.pairedComplex.Seam) (x : T.pairedComplex.Realization retain)
    (position : Cap.horizontal (T.pairedFolding.toSpace retain x) = a) :
    ∃ w : T.pairedComplex.Vertex retain, T.pairedComplex.vertexPoint retain w = x := by
  obtain ⟨v, same⟩ := T.vertex_of_segment_endpoint conforming inside different cover
  exact T.exists_vertexPoint_of_projected_eq conforming inside retain v x (position.trans same.symm)

end Unfoldings.SpatialEnvelope.Triangulation
