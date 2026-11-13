module

public import Unfoldings.Roof.CompletionRadialMesh
public import Unfoldings.Roof.CompletionRefinementCurvature
public import Unfoldings.Roof.CompletionOriginalCurvature
public import Unfoldings.Roof.ExtendedGeometricCuts

/-! Constructed original and radial cuts cover every positive-curvature auxiliary vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

/-- Every original rim vertex is continued; every exterior refined curvature seed was selected
before meshing. The proof assumes neither auxiliary acuteness nor an unfolding certificate. -/
theorem radialMesh_curvature_covered
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let F := E.cornerTails M.inside
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ v : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
      0 < L.mesh.toTriangulation.pairedComplex.interiorAngularDefect Set.univ v →
        L.cap.projectedVertex v ∈ M.extendedGeometricCuts F := by
  let F := E.cornerTails M.inside
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  change ∀ v : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
    0 < L.mesh.toTriangulation.pairedComplex.interiorAngularDefect Set.univ v →
      L.cap.projectedVertex v ∈ M.extendedGeometricCuts F
  intro v curved
  by_cases inside : L.cap.projectedVertex v ∈ K.footprint
  · obtain ⟨f, k, corner⟩ := L.exists_original_corner_of_positive_curvature
      (fun i => height (L.mesh.support i)) v inside curved
    let w := C.vertexOfCorner Set.univ (f, k)
    have at_point : K.projectedVertex w = L.cap.projectedVertex v := corner
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · exact Or.inr (at_point ▸ E.cornerTails_covers_rim M.inside w boundary)
    · have nonroot : w ∉ M.parents.roots := by rw [M.roots_eq]; exact boundary
      exact Or.inl (at_point ▸ M.projectedVertex_mem_cutCarrier w nonroot)
  · have supported := E.alignToLines_curvature_support
      (K.originalAndSegmentEquations F.first F.last F.different)
      (K.originalAndSegmentEquations_ne_zero F.first F.last F.different) height v curved
    obtain ⟨i, k, corner⟩ := supported
    have seed : L.cap.projectedVertex v ∈ E.skirtSeedSet :=
      ⟨Or.inl ⟨(i, k), corner⟩, fun member => inside (interior_subset member)⟩
    exact Or.inr (F.seeds_covered ⟨_, seed⟩)

end Unfoldings.ConvexRoof.SectorForest
