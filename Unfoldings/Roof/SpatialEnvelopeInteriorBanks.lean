module

public import Unfoldings.Roof.SpatialEnvelopeVertexFibers
public import Unfoldings.Roof.SpatialEnvelopeCap
public import Unfoldings.Roof.SpatialEnvelopeProjection
public import Unfoldings.Polyhedron.BoundaryDirections

/-! A bank starting strictly inside a finite roof section was created by an actual cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z) (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (clip family Z)).Nonempty)

local instance interiorBankIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

include conforming inside in
/-- Strict original graph height excludes an original rim edge, independently of
which other banks have already been cut. -/
theorem boundaryEnd_is_cut_of_strict_height (retain : Set T.pairedComplex.Seam)
    (p : T.pairedComplex.BoundaryEnd retain)
    (above : Z < height family (Cap.horizontal (T.pairedFolding.boundaryPosition p))) :
    ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge p.val) := by
  let roof := T.roof conforming inside
  let vertex := T.pairedComplex.vertexForgetCuts (Set.subset_univ retain)
    (T.pairedComplex.boundaryEndVertex retain p)
  have internal : ¬ T.pairedComplex.IsBoundaryVertex Set.univ vertex := by
    apply (roof.projectedVertex_mem_interior_iff vertex).mp
    rw [T.roof_footprint conforming inside]
    apply AffineEnvelope.mem_interior_clip (fun i => (family i).height)
    exact above.trans_eq (congrArg (height family)
      (T.roof_projectedVertex_vertexForgetCuts conforming inside retain
        (T.pairedComplex.boundaryEndVertex retain p))).symm
  intro boundary
  apply internal
  have original := T.pairedComplex.isBoundaryVertex_of_boundary_germ Set.univ p.val boundary
  simpa only [vertex, TriangleComplex.boundaryEndVertex,
    TriangleComplex.vertexForgetCuts_vertexOfCorner] using original

end Unfoldings.SpatialEnvelope.Triangulation
