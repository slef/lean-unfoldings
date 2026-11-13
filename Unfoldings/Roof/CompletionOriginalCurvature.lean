module

public import Unfoldings.Roof.CompletionMesh
public import Unfoldings.Roof.SpatialEnvelopeCurvature
public import Unfoldings.Roof.OriginalFaceHeight
public import Unfoldings.Roof.CompletionOriginalPieces

/-! Completion curvature inside the original roof is supported only on original vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

local instance completionOriginalCurvatureIndexFintype : Fintype E.mesh.Index :=
  @Fintype.ofFinite _ E.mesh.finite

theorem interiorCurvature_eq_zero_at_regular_original
    (height : ∀ i, (3 : ℝ) / 4 ≤ E.cap.normal i 2)
    (v : E.mesh.toTriangulation.pairedComplex.Vertex Set.univ) (f : Face)
    (member : E.cap.projectedVertex v ∈ (K.projectedTriangle f).carrier)
    (regular : ¬ (K.projectedTriangle f).IsVertex (E.cap.projectedVertex v)) :
    E.mesh.toTriangulation.pairedComplex.interiorAngularDefect Set.univ v = 0 := by
  apply E.cap.interiorCurvature_eq_zero_of_incidentSlopes_collinear height v
  apply Collinear.subset
    (E.mesh.toTriangulation.incidentSlopes_subset_activeSlopes E.conforming E.interior_nonempty v)
  apply SpatialEnvelope.activeSlopes_collinear_of_unchanged_nonvertex _
    (K.projectedTriangle f) (K.supportHeight f) _ member regular
  intro x inside
  exact (E.unchanged x (K.projectedTriangle_subset_footprint f inside)).trans
    (K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f inside)

theorem exists_original_corner_of_positive_curvature
    (height : ∀ i, (3 : ℝ) / 4 ≤ E.cap.normal i 2)
    (v : E.mesh.toTriangulation.pairedComplex.Vertex Set.univ)
    (member : E.cap.projectedVertex v ∈ K.footprint)
    (curved : 0 < E.mesh.toTriangulation.pairedComplex.interiorAngularDefect Set.univ v) :
    ∃ f k, (K.projectedTriangle f).vertex k = E.cap.projectedVertex v := by
  obtain ⟨f, inside⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset member)
  by_cases vertex : (K.projectedTriangle f).IsVertex (E.cap.projectedVertex v)
  · obtain ⟨k, equal⟩ := vertex
    exact ⟨f, k, equal⟩
  · exact (curved.ne'
      (E.interiorCurvature_eq_zero_at_regular_original height v f inside vertex)).elim

end Unfoldings.ConvexRoof.CompletionMesh
