module

public import Unfoldings.Cap.ExtendedBankChainPositions
public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Geometry.ChainTruncation

/-! Construct physically bounded finite bank-path prefixes in the actual deep roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- Reach a chosen source radius on an actual fine seam, retaining common position
and opening sectors and an explicit truncated path wholly inside the controlled ball. -/
theorem cornerExtendedOutward_bankChain_radius_prefix (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (radius : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) radius ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let Q := L.partition.normalizedCap L.conforming lower
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ w : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex w ∈ M.extendedGeometricCuts F →
      dist (K.projectedVertex origin) (Q.projectedVertex w) < radius →
      ∃ i : FiveSector,
        (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
          (Q.projectedVertex
            (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
              Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
          R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j)) ∧
        (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
          (R.completedRootPath w).vertex j - K.projectedVertex origin ∈ closedFiveSector t i) ∧
        ∃ k : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
          dist (K.projectedVertex origin) ((R.completedRootPath w).point k s) = radius ∧
          (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
            PolygonalChain.Before j r k s →
              dist (K.projectedVertex origin) ((R.completedRootPath w).point j r) ≤ radius) ∧
          ∀ j : Fin (k.val + 1), ∀ r : unitInterval,
            dist (K.projectedVertex origin)
              (((R.completedRootPath w).truncate k s).point j r) ≤ radius := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let Q := L.partition.normalizedCap L.conforming lower
  let R := M.cornerExtendedOutwardForest positive small T internal source_height lower
  have deepQ : Metric.closedBall (K.projectedVertex origin) radius ⊆ interior Q.footprint := by
    rw [L.partition.normalizedCap_footprint L.conforming lower]
    exact deep
  refine fun w member start => ?_
  obtain ⟨i, sectors, positions⟩ := M.cornerExtendedOutward_bankChain_sector_positions
    positive small T internal source_height lower conforming height w member
  obtain ⟨k, s, equal, _, bounded⟩ :=
    R.val.completedRootPath_exists_radius_prefix R.property member radius start deepQ
  refine ⟨i, sectors, positions, k, s, equal, bounded, ?_⟩
  intro j r
  obtain ⟨a, u, before, point⟩ := (R.val.completedRootPath w).truncate_point_covered k s j r
  rw [point]
  exact bounded a u before

end Unfoldings.ConvexCap.SectorForest
