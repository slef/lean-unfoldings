module

public import Unfoldings.Roof.CompletionCurve
public import Unfoldings.Geometry.MarkedPointConstraints

/-! Prescribed crossing lines retain marked points as actual vertices of the completion cap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.ConstrainedTriangulation

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ} (T : ConstrainedTriangulation family extra Z)

/-- Actual coordinate constraints, together with coverage, construct a genuine mesh corner. -/
theorem exists_corner_of_coordinate_constraints (p : Plane) (mark : Fin 2 → J)
    (equations : ∀ k, extra (mark k) = pointCoordinateEquation p k)
    (member : p ∈ clip family Z) : ∃ i k, (T.projectedTriangle i).vertex k = p := by
  obtain ⟨i, inside⟩ := Set.mem_iUnion.mp (T.cover.subset member)
  have vertex := (T.projectedTriangle i).isVertex_of_coordinate_signs p
    (fun k => T.signs i (mark k)) (by
      intro k x hx
      rw [← equations]
      exact T.constrained i x hx (mark k)) inside
  obtain ⟨k, equal⟩ := vertex
  exact ⟨i, k, equal⟩

end Unfoldings.SpatialEnvelope.ConstrainedTriangulation

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

local instance : Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

/-- Marked coordinate lines preserve the point as an actual intrinsic vertex of the cap. -/
theorem exists_projected_vertex_of_coordinate_constraints (p : Plane) (mark : Fin 2 → J)
    (equations : ∀ k, extra (mark k) = pointCoordinateEquation p k) (member : p ∈ region) :
    ∃ w : E.mesh.pairedComplex.Vertex Set.univ, E.cap.projectedVertex w = p := by
  obtain ⟨i, k, equal⟩ := E.mesh.exists_corner_of_coordinate_constraints p mark equations
    (interior_subset (E.covers (Or.inr member)))
  refine ⟨E.mesh.pairedComplex.vertexOfCorner Set.univ (i, k), ?_⟩
  exact (E.cap.projectedVertex_ofCorner i k).trans
    ((E.mesh.toTriangulation.normalizedCap_projectedTriangle_vertex E.conforming
      E.interior_nonempty i k).trans equal)

end Unfoldings.ConvexRoof.CompletionMesh
