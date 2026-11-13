module

public import Unfoldings.Roof.CompletionOutwardForest
public import Unfoldings.Roof.ExtendedComponentWedges
public import Unfoldings.Cap.CompletedRootPathSupport

/-! Curvature-carrying auxiliary paths inherit the acute wedges of the constructed network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

theorem completionOutward_curvedPathWedges (positive : 0 < t) (small : t < 1)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    (M.completionOutwardForest E positive small).val.CurvedPathWedges := by
  let F := E.cornerTails M.inside
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let R := M.completionOutwardForest E positive small
  have covered := E.cornerTails_covers_rim M.inside
  exact R.val.curvedPathWedges_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered)
    (M.exists_cut_component_wedge F covered positive small)
    (M.radialMesh_curvature_covered E height)

/-- Every signed seam-crossing correction is bounded by the completed cap's total curvature. -/
theorem completionOutward_crossing_bound (positive : 0 < t) (small : t < 1)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    let R := (M.completionOutwardForest E positive small).val
    ∀ (A : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ),
      |R.completedRayCurvaturePotential A center cut level| ≤
        L.mesh.toTriangulation.pairedComplex.totalInteriorAngularDefect Set.univ := by
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest E positive small).val
  exact fun A center cut level => R.abs_completedRayCurvaturePotential_le
    (M.completionOutward_curvedPathWedges E positive small height) A center cut level

end Unfoldings.ConvexRoof.SectorForest
