module

public import Unfoldings.Roof.CompletionRefinement
public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Geometry.SpatialPlaneSlopes
public import Unfoldings.Cap.TransverseRefinementSlopes

/-! Physical line refinement creates no positive curvature away from preceding mesh corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- The line-aligned completion lies in the old physical triangles and has
their exact support slopes. -/
theorem alignToLines_parent_slopes {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    let family := K.completionPlanes E.tentHeight (Real.sin φ / 2)
    ∃ parent : L.mesh.Index → E.mesh.Index,
      (∀ i, (L.cap.projectedTriangle i).carrier ⊆ (E.mesh.projectedTriangle (parent i)).carrier) ∧
      (∀ i, L.cap.normalSlope i = (family (E.mesh.support (parent i))).normalSlope) := by
  let L := E.alignToLines equation proper
  let := @Fintype.ofFinite _ L.mesh.finite
  let family := K.completionPlanes E.tentHeight (Real.sin φ / 2)
  obtain ⟨parent, subordinate⟩ := E.alignToLines_subordinate equation proper
  refine ⟨parent, ?_, ?_⟩
  · intro i
    change ((L.mesh.toTriangulation.normalizedCap L.conforming
      L.interior_nonempty).projectedTriangle i).carrier ⊆ _
    rw [L.mesh.toTriangulation.normalizedCap_projectedTriangle_carrier
      L.conforming L.interior_nonempty]
    exact (subordinate i).1
  · intro i
    change (family (L.mesh.support i)).normalSlope = _
    rw [(subordinate i).2]

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
  obtain ⟨parent, inside, normal_eq⟩ := E.alignToLines_parent_slopes equation proper
  exact fun v curved => L.cap.exists_parent_corner_of_positive_curvature E.mesh.projectedTriangle
    E.conforming E.mesh.separated (fun i => (family (E.mesh.support i)).normalSlope) parent
    inside normal_eq (fun i => height (L.mesh.support i)) v curved

open Classical in
/-- A connector through no old vertex meets the refined completion only
at flat or transverse contacts. -/
theorem alignToLines_regular_jordan_sectionSlopes {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0)
    {a b : Plane} (different : a ≠ b)
    (regular : ∀ (t : ℝ) (j : E.mesh.Index) (k : Fin 3),
      AffineMap.lineMap a b t ≠ (E.mesh.projectedTriangle j).vertex k) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ L.cap.footprint)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier) J)
      (i : Fin ((L.cap.jordanContour jordan contains avoids).length + 1)),
      L.cap.jordanBankPosition jordan contains avoids i ∈ segment ℝ a b →
      L.cap.HasRegularSectionSlopes ((L.cap.jordanContourVertexEquiv jordan contains avoids) i).val
        (b - a) := by
  let L := E.alignToLines equation proper
  let := @Fintype.ofFinite _ L.mesh.finite
  let family := K.completionPlanes E.tentHeight (Real.sin φ / 2)
  obtain ⟨parent, inside, normal_eq⟩ := E.alignToLines_parent_slopes equation proper
  let plane (j : E.mesh.Index) := family (E.mesh.support j)
  have affine (j : E.mesh.Index) (x y : Plane) :
      (plane j).height x - (plane j).height y = -inner ℝ (plane j).normalSlope (x - y) := by
    linarith only [(plane j).height_difference y x]
  have agree (i j : E.mesh.Index) (x : Plane)
      (hi : x ∈ (E.mesh.projectedTriangle i).carrier) (hj : x ∈ (E.mesh.projectedTriangle j).carrier) :
      (plane i).height x = (plane j).height x :=
    (E.mesh.active i x hi).symm.trans (E.mesh.active j x hj)
  exact fun {J} jordan contains avoids i contact =>
    L.cap.regular_jordan_sectionSlopes_of_avoids_old_vertices E.mesh.projectedTriangle
      E.conforming E.mesh.separated (fun j => (plane j).normalSlope) (fun j => (plane j).height)
      parent inside normal_eq affine agree jordan contains avoids i different contact regular

end Unfoldings.ConvexRoof.CompletionMesh
