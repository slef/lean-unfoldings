module

public import Unfoldings.Roof.CompletionRegion
public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Geometry.ConstraintInteriors

/-! Exact curve avoidance and containment in physically constructed roof completions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

local instance : Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

/-- Every requested region point lies strictly inside the actual normalized cap. -/
theorem region_inside : region ⊆ interior E.cap.footprint := by
  rw [E.cap_footprint]
  exact fun _ member => E.covers (Or.inr member)

/-- Prescribed proper equations force actual cap triangle interiors to avoid the curve. -/
theorem cap_avoids_supported_curve (proper : ∀ j, extra j ≠ 0)
    {curve : Set Plane} (support : ∀ p ∈ curve, ∃ j, extra j p = 0) (i : E.mesh.Index) :
    Disjoint (interior (E.cap.projectedTriangle i).carrier) curve := by
  change Disjoint (interior ((E.mesh.toTriangulation.normalizedCap
    E.conforming E.interior_nonempty).projectedTriangle i).carrier) curve
  rw [E.mesh.toTriangulation.normalizedCap_projectedTriangle_carrier]
  exact E.mesh.interior_avoids_supported_curve proper support i

end Unfoldings.ConvexRoof.CompletionMesh
