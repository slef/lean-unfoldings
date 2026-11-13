module

public import Unfoldings.Roof.CompletionRefinement
public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Geometry.SpatialPlaneSlopes
public import Unfoldings.Cap.RefinementCurvatureSupport

/-! Physical line refinement creates no positive curvature away from preceding mesh corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- Old physical parents and unchanged normals locate every refined curvature seed. -/
theorem alignToLines_curvature_support {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ v : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
      0 < L.mesh.toTriangulation.pairedComplex.interiorAngularDefect Set.univ v →
        ∃ i k, (E.mesh.projectedTriangle i).vertex k = L.cap.projectedVertex v := by
  let L := E.alignToLines equation proper
  let := @Fintype.ofFinite _ L.mesh.finite
  let := @Fintype.ofFinite _ E.mesh.finite
  let family := K.completionPlanes E.tentHeight (Real.sin φ / 2)
  obtain ⟨parent, subordinate⟩ := E.alignToLines_subordinate equation proper
  have inside (i : L.mesh.Index) :
      (L.cap.projectedTriangle i).carrier ⊆ (E.mesh.projectedTriangle (parent i)).carrier := by
    change ((L.mesh.toTriangulation.normalizedCap L.conforming
      L.interior_nonempty).projectedTriangle i).carrier ⊆ _
    rw [L.mesh.toTriangulation.normalizedCap_projectedTriangle_carrier
      L.conforming L.interior_nonempty]
    exact (subordinate i).1
  have normal_eq (i : L.mesh.Index) :
      L.cap.normalSlope i = (family (E.mesh.support (parent i))).normalSlope := by
    change (family (L.mesh.support i)).normalSlope = _
    rw [(subordinate i).2]
  exact fun v curved => L.cap.exists_parent_corner_of_positive_curvature E.mesh.projectedTriangle
    E.conforming E.mesh.separated (fun i => (family (E.mesh.support i)).normalSlope) parent
    inside normal_eq (fun i => height (L.mesh.support i)) v curved

end Unfoldings.ConvexRoof.CompletionMesh
