module

public import Unfoldings.Development.BoundaryDisplacements
public import Unfoldings.Complex.ParentBankEndpoints

public import Unfoldings.Roof.DevelopmentCoordinates
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Development.BoundaryRays

/-! Actual original bank vertices and closed bank segments in arbitrary-rim roof face charts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexRoof C)

theorem roofPlacement_boundary_vertex (p : C.BoundaryEnd retain) :
    D.roofPlacement K p.val.1.1 (K.projectedVertex
      (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p))) =
        D.boundaryPosition p := by
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    K.projectedVertex_ofCorner]
  rw [K.projectedTriangle_vertex, ← K.projectFace_apply, D.roofPlacement_apply]
  exact D.linkGerm_apex (⟨p.val, rfl⟩ : C.LinkGerm retain
    (C.vertexOfCorner retain p.val.1))

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projected_bank_segment_mem_face {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    {s : ℝ} (inside : s ∈ Set.Icc 0 1) :
    AffineMap.lineMap
      (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain p)))
      (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain (C.boundaryTurn retain p)))) s ∈
      (K.projectedTriangle p.val.1.1).carrier := by
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    C.boundaryTurn_corner, K.projectedVertex_ofCorner]
  apply (K.projectedTriangle p.val.1.1).convex_carrier.lineMap_mem
    ((K.projectedTriangle p.val.1.1).vertex_mem p.val.1.2) _ inside
  exact (K.projectedTriangle p.val.1.1).vertex_mem (C.germFarCorner p.val).2

end Unfoldings.ConvexRoof
