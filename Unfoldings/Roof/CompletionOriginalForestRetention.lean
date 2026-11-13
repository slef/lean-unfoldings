module

public import Unfoldings.Roof.CompletionCutRestriction
public import Unfoldings.Roof.CompletionOutwardForest

/-! Auxiliary radial forests keep all fine seams needed by the original cut roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

open Classical in
theorem completionOriginalRetain_subset_radial :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ R : L.cap.RadialCutForest origin (M.extendedGeometricCuts (E.cornerTails M.inside)),
      L.originalPart.originalRetain M.retain ⊆
        L.mesh.toTriangulation.pairedComplex.restrictRetain
          L.originalPart.originalPieceSet R.retain := by
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  change ∀ R : L.cap.RadialCutForest origin (M.extendedGeometricCuts (E.cornerTails M.inside)),
    L.originalPart.originalRetain M.retain ⊆
      L.mesh.toTriangulation.pairedComplex.restrictRetain L.originalPart.originalPieceSet R.retain
  intro R s kept
  change s.val ∉ Set.range R.selection.edge
  rintro ⟨e, chosen⟩
  have selected := R.selected_subset e
  rw [chosen] at selected
  have kept_network : s.val ∈ M.extendedRetain E := by
    have equal := M.extendedRetain_restrict_original_eq E
    have kept' : s ∈ L.mesh.toTriangulation.pairedComplex.restrictRetain
        L.originalPart.originalPieceSet (M.extendedRetain E) := equal.symm ▸ kept
    exact kept'
  apply kept_network
  exact (L.mesh.toTriangulation.normalizedCap_projectedTriangle_edge L.conforming
    L.interior_nonempty (L.mesh.toTriangulation.pairedComplex.left s.val).face
    (L.mesh.toTriangulation.pairedComplex.left s.val).edge).symm.subset.trans selected

end Unfoldings.ConvexRoof.SectorForest
