module

public import Unfoldings.Cap.CompletedComparisonQuadrants
public import Unfoldings.Cap.CenteredDevelopedMap

/-! Actual centered parent-bank charts give the corresponding complete comparison-chain points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem centered_coordinate_eq_sectorFrame (i : FiveSector) (f : Face) (z : ℂ) :
    D.centeredCoordinatePlacement K source (N.calibratedFrame D B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f z =
      B.sectorFrame i (D.projectedPlacement K f
        (source + (fiveSectorFrame t positive small i).place.symm z)) := by
  let frame := (fiveSectorFrame t positive small i).place
  let calibration := N.calibratedFrame D B.anchor B.reference
  let output := Complex.orthonormalBasisOneI.repr.trans frame
  change output (calibration (D.projectedPlacement K f (frame.symm (frame source + z)))) =
    output (calibration (D.projectedPlacement K f (source + frame.symm z)))
  rw [frame.symm.map_add, frame.symm_apply_apply]

/-- The geometric point is on an actual whole parent edge at its physical parameter. -/
theorem centered_entrance_chart_eq_comparison_point (i : FiveSector)
    (w : C.Vertex Set.univ) (origin : Plane)
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) (z : ℂ)
    (physical : source + (fiveSectorFrame t positive small i).place.symm z =
      (N.completedRootPath w).point j s) :
    D.centeredCoordinatePlacement K source (N.calibratedFrame D B.anchor B.reference)
        (fiveSectorFrame t positive small i).place
        (N.parentBankOpening D (N.completedBankChain w j)).entranceFace z =
      (B.entranceComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s := by
  rw [B.entranceComparisonChain_original_point, N.parentEntrancePoint_eq_projectedPlacement,
    AffineMap.lineMap_apply_one_sub, ← N.completedRootPath_point_bankChain, ← physical]
  exact B.centered_coordinate_eq_sectorFrame i _ z

theorem centered_exit_chart_eq_comparison_point (i : FiveSector)
    (w : C.Vertex Set.univ) (origin : Plane)
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) (z : ℂ)
    (physical : source + (fiveSectorFrame t positive small i).place.symm z =
      (N.completedRootPath w).point j s) :
    D.centeredCoordinatePlacement K source (N.calibratedFrame D B.anchor B.reference)
        (fiveSectorFrame t positive small i).place
        (N.parentBankOpening D (N.completedBankChain w j)).exitFace z =
      (B.exitComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s := by
  rw [B.exitComparisonChain_original_point, N.parentExitPoint_eq_projectedPlacement,
    AffineMap.lineMap_apply_one_sub, ← N.completedRootPath_point_bankChain, ← physical]
  exact B.centered_coordinate_eq_sectorFrame i _ z

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
