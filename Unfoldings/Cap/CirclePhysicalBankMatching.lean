module

public import Unfoldings.Cap.RadialStripCircleComparison
public import Unfoldings.Cap.RadialStripPhysicalMap

/-! Circle endpoints transported from any sector equal their named actual parent-bank points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)
  (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
  (directions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
    K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
      K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
  (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval)

include radius_positive far on_cuts directions

theorem circle_lower_physical_eq_entrance
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) = (N.completedRootPath w).point j s) :
    data.outputFrame.symm (data.value (S.lower.point slice.lowerHeight)) =
      N.parentEntrancePoint (N.completedDevelopment D) (N.completedBankChain w j)
        (1 - (s : ℝ)) := by
  have matching := B.circle_lower_eq_entrance_comparison_point i data radius_positive far slice
    w on_cuts directions 0 j s regular physical
  rw [B.entranceComparisonChain_original_point] at matching
  rw [matching]
  exact data.outputFrame.symm_apply_apply _

theorem circle_upper_physical_eq_exit
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) = (N.completedRootPath w).point j s) :
    data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
      N.parentExitPoint (N.completedDevelopment D) (N.completedBankChain w j) (1 - (s : ℝ)) := by
  have matching := B.circle_upper_eq_exit_comparison_point i data radius_positive far slice
    w on_cuts directions 0 j s regular physical
  rw [B.exitComparisonChain_original_point] at matching
  rw [matching]
  exact data.outputFrame.symm_apply_apply _

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
