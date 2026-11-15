module

public import Unfoldings.Roof.CompletionFaceAngles
public import Unfoldings.Cap.TriangularFootprintStraightAngles

/-! Actual fine vertices inside an original face or its open sides introduce no extra turns. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations) (f : Face)

local instance completionFaceStraightAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- A fine vertex along the open side of an old metric triangle has exactly a half-plane fan. -/
theorem facePiece_totalAngle_at_noncorner_boundary
    (w : (E.facePieceComplex f).Vertex Set.univ)
    (on_boundary : (E.facePieceDevelopment f).toPlane
      ((E.facePieceComplex f).vertexPoint Set.univ w) ∈ frontier (C.triangle f).carrier)
    (noncorner : ¬ (C.triangle f).IsVertex ((E.facePieceDevelopment f).toPlane
      ((E.facePieceComplex f).vertexPoint Set.univ w))) :
    (E.facePieceComplex f).totalAngle Set.univ w = Real.pi := by
  have projection : (E.facePieceFlatCap f).projectedVertex w =
      (E.facePieceDevelopment f).toPlane ((E.facePieceComplex f).vertexPoint Set.univ w) :=
    (E.facePieceDevelopment f).horizontalFolding_projection _
  have straight := (E.facePieceFlatCap f).projectedTotalAngle_eq_pi_of_triangle_boundary
    (C.triangle f) (E.facePieceFlatCap_footprint f) w (projection.symm ▸ on_boundary)
    (projection.symm ▸ noncorner)
  exact ((E.facePieceDevelopment f).flatCap_projectedTotalAngle _ _ _ Set.univ w).symm.trans
    straight

open Classical in
/-- A fine vertex strictly inside an old face carries precisely a full Euclidean fan. -/
theorem facePiece_totalAngle_at_original_interior
    (w : (E.facePieceComplex f).Vertex Set.univ)
    (inside : (E.facePieceDevelopment f).toPlane
      ((E.facePieceComplex f).vertexPoint Set.univ w) ∈ interior (C.triangle f).carrier) :
    (E.facePieceComplex f).totalAngle Set.univ w = 2 * Real.pi := by
  have projection : (E.facePieceFlatCap f).projectedVertex w =
      (E.facePieceDevelopment f).toPlane ((E.facePieceComplex f).vertexPoint Set.univ w) :=
    (E.facePieceDevelopment f).horizontalFolding_projection _
  have internal : ¬ (E.facePieceComplex f).IsBoundaryVertex Set.univ w := by
    intro boundary
    have frontier := (E.facePieceFlatCap f).projectedVertex_mem_frontier_iff w |>.mpr boundary
    rw [E.facePieceFlatCap_footprint f, projection] at frontier
    exact disjoint_interior_frontier.le_bot ⟨inside, frontier⟩
  exact ((E.facePieceDevelopment f).flatCap_projectedTotalAngle _ _ _ Set.univ w).symm.trans
    ((E.facePieceFlatCap f).projectedTotalAngle_eq_two_pi w internal)

end Unfoldings.ConvexRoof.CompletionMesh
