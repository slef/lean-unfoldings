module

public import Unfoldings.Cap.ExtendedCutGrowth
public import Unfoldings.Cap.ExtendedCutFlat
public import Unfoldings.Cap.RadialCutForest

/-! Construct a boundary-rooted subforest of the actual extended geometric cut seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- Choose actual outward fine seams. The only marked roots away from the outer rim are unused
vertices outside the geometric cuts; they never occur in the actual relative cut graph. -/
def cornerExtendedForest (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  apply Q.radialCutForest
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
  obtain ⟨w, s, cut, link, farther⟩ := Q.exists_radially_ascending_seam
    (M.extendedRetain T F lower) (K.projectedVertex origin) v (growth.mono seam_cover)
  refine ⟨w, s, link, farther, ?_⟩
  have selected : (L.partition.projectedTriangle (L.partition.pairedComplex.left s).face).edge
      (L.partition.pairedComplex.left s).edge ⊆ M.extendedGeometricCuts F := not_not.mp cut
  exact (L.partition.normalizedCap_projectedTriangle_edge L.conforming lower _ _).subset.trans
    selected

end Unfoldings.ConvexCap.SectorForest
