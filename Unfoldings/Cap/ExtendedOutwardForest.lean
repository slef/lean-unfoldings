module

public import Unfoldings.Cap.ExtendedCutDevelopment
public import Unfoldings.Cap.OutwardRadialForest

/-! Construct extended fine-seam forests with whole-edge, whole-path radial control. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- The strengthened construction rules out an initial inward excursion on every selected seam,
including all fine subdivision edges and independent skirt components. -/
def cornerExtendedOutwardForest (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    {R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F) //
      R.Outward} := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  apply Q.outwardRadialCutForest
  intro v nonboundary member
  have in_clip : Q.projectedVertex v ∈ interior (K.clipFootprint Z) := by
    have interior_point := (Q.projectedVertex_mem_interior_iff v).mpr nonboundary
    rw [L.partition.normalizedCap_footprint L.conforming lower] at interior_point
    exact interior_point
  have growth := M.corner_extended_local_growth positive small T internal source_height lower
    (Q.projectedVertex v) member in_clip
  have seam_cover : M.extendedGeometricCuts F ∩ interior (K.clipFootprint Z) ⊆
      ⋃ s : {s : L.partition.pairedComplex.Seam // s ∉ M.extendedRetain T F lower},
        (Q.projectedTriangle (L.partition.pairedComplex.left s.val).face).edge
          (L.partition.pairedComplex.left s.val).edge := by
    intro p hp
    obtain ⟨s, cut, on_edge⟩ := M.extended_cut_seam T F lower hp.1 hp.2
    refine Set.mem_iUnion.mpr ⟨⟨s, cut⟩, ?_⟩
    exact (L.partition.normalizedCap_projectedTriangle_edge L.conforming lower _ _).symm.subset
      on_edge
  obtain ⟨w, s, cut, link, farther, outward⟩ := Q.exists_outward_cut_seam
    (M.extendedRetain T F lower) (K.projectedVertex origin) v (growth.mono seam_cover)
  refine ⟨w, s, link, farther, ?_, outward⟩
  have selected : (L.partition.projectedTriangle (L.partition.pairedComplex.left s).face).edge
      (L.partition.pairedComplex.left s).edge ⊆ M.extendedGeometricCuts F := not_not.mp cut
  exact (L.partition.normalizedCap_projectedTriangle_edge L.conforming lower _ _).subset.trans
    selected

/-- The stronger radial selection retains the actual cut disk and local development. -/
theorem cornerExtendedOutward_exists_development (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∃ E : FacewiseDevelopment L.partition.pairedComplex R.retain,
      ∀ x, ‖(R.cutDisk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  exact R.exists_development
    (M.extended_cut_curvature_covered T internal source_height lower conforming height)

end Unfoldings.ConvexCap.SectorForest
