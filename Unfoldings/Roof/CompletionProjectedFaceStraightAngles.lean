module

public import Unfoldings.Roof.CompletionProjectedFaceAngles
public import Unfoldings.Cap.TriangularFootprintStraightAngles

/-! Actual fine vertices inside an original face or its open sides introduce no extra turns. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations) (f : Face)

local instance completionProjectedFaceStraightAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- A fine vertex along the open side of an old metric triangle has exactly a half-plane fan. -/
theorem facePieceProjected_totalAngle_at_noncorner_boundary
    (w : (E.facePieceProjectedComplex f).Vertex Set.univ)
    (on_boundary : (E.facePieceProjectedDevelopment f).toPlane
      ((E.facePieceProjectedComplex f).vertexPoint Set.univ w) ∈ frontier (K.projectedTriangle
        f).carrier)
    (noncorner : ¬ (K.projectedTriangle f).IsVertex ((E.facePieceProjectedDevelopment f).toPlane
      ((E.facePieceProjectedComplex f).vertexPoint Set.univ w))) :
    (E.facePieceProjectedComplex f).totalAngle Set.univ w = Real.pi := by
  have projection : (E.facePieceProjectedFlatCap f).projectedVertex w =
      (E.facePieceProjectedDevelopment f).toPlane ((E.facePieceProjectedComplex f).vertexPoint
        Set.univ w) :=
    (E.facePieceProjectedDevelopment f).horizontalFolding_projection _
  have straight := (E.facePieceProjectedFlatCap f).projectedTotalAngle_eq_pi_of_triangle_boundary
    (K.projectedTriangle f) (E.facePieceProjectedFlatCap_footprint f) w (projection.symm ▸
      on_boundary)
    (projection.symm ▸ noncorner)
  exact ((E.facePieceProjectedDevelopment f).flatCap_projectedTotalAngle _ _ _ Set.univ
    w).symm.trans
    straight

open Classical in
/-- A fine vertex strictly inside an old face carries precisely a full Euclidean fan. -/
theorem facePieceProjected_totalAngle_at_original_interior
    (w : (E.facePieceProjectedComplex f).Vertex Set.univ)
    (inside : (E.facePieceProjectedDevelopment f).toPlane
      ((E.facePieceProjectedComplex f).vertexPoint Set.univ w) ∈ interior (K.projectedTriangle
        f).carrier) :
    (E.facePieceProjectedComplex f).totalAngle Set.univ w = 2 * Real.pi := by
  have projection : (E.facePieceProjectedFlatCap f).projectedVertex w =
      (E.facePieceProjectedDevelopment f).toPlane ((E.facePieceProjectedComplex f).vertexPoint
        Set.univ w) :=
    (E.facePieceProjectedDevelopment f).horizontalFolding_projection _
  have internal : ¬ (E.facePieceProjectedComplex f).IsBoundaryVertex Set.univ w := by
    intro boundary
    have frontier := (E.facePieceProjectedFlatCap f).projectedVertex_mem_frontier_iff w |>.mpr
      boundary
    rw [E.facePieceProjectedFlatCap_footprint f, projection] at frontier
    exact disjoint_interior_frontier.le_bot ⟨inside, frontier⟩
  exact ((E.facePieceProjectedDevelopment f).flatCap_projectedTotalAngle _ _ _ Set.univ
    w).symm.trans
    ((E.facePieceProjectedFlatCap f).projectedTotalAngle_eq_two_pi w internal)

end Unfoldings.ConvexRoof.CompletionMesh
