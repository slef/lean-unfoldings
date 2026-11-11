module

public import Unfoldings.Cap.ExtendedOutwardForest
public import Unfoldings.Cap.ExtendedComponentWedges
public import Unfoldings.Cap.CompletedRootPathSupport

/-! Derive acute whole-path wedges and uniform crossing bounds for the actual extended roof cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- Every actual curvature-carrying fine-seam path has an acute wedge derived from the original
forest and its constructed radial components. No fine-seam path or auxiliary acuteness
certificate is assumed. Arbitrary additional flat branches are harmless. -/
theorem cornerExtendedOutward_curvedPathWedges (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := M.cornerExtendedOutwardForest positive small T internal source_height lower
    R.val.CurvedPathWedges := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let R := M.cornerExtendedOutwardForest positive small T internal source_height lower
  have covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier :=
    T.cornerTails_covers_rim inside source_height lower
  exact R.val.curvedPathWedges_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered lower)
    (M.exists_cut_component_wedge F covered positive small)
    (M.extended_cut_curvature_covered T internal source_height lower conforming height)

/-- All actual signed seam-crossing corrections are bounded uniformly in the auxiliary mesh.
The acute path condition used in the generic estimate is now proved for the constructed cuts. -/
theorem cornerExtendedOutward_crossing_bound (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ (A : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ),
      |R.completedRayCurvaturePotential A center cut level| ≤
        L.partition.pairedComplex.totalInteriorAngularDefect Set.univ := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have wedges := M.cornerExtendedOutward_curvedPathWedges positive small T internal source_height
    lower conforming height
  exact fun A center cut level => R.abs_completedRayCurvaturePotential_le wedges A center cut level

end Unfoldings.ConvexCap.SectorForest
