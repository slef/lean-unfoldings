module

public import Unfoldings.Cap.RadialStripCircleMatching
public import Unfoldings.Cap.CompletedChartComparisonPoints

/-! Actual regular strip-circle endpoints are points of the named complete comparison banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)

/-- Positive-width circle matching identifies the lower endpoint with an actual
whole edge of the entrance comparison chain at the same physical parameter. -/
theorem circle_lower_eq_entrance_comparison_point {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
    (directions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (origin : Plane) (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval)
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) = (N.completedRootPath w).point j s) :
    data.value (S.lower.point slice.lowerHeight) =
      (B.entranceComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s := by
  have child_on_cut : K.projectedVertex (N.completedBankChain w j).val ∈ cuts :=
    N.completedRootPath_vertex_mem on_cuts j.castSucc
  have member : source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ∈
      segment ℝ (K.projectedVertex (N.completedBankChain w j).val)
        (K.projectedVertex
          (N.spanningCompletion.parents.parent (N.completedBankChain w j).val)) := by
    rw [physical, N.completedRootPath_point_bankChain]
    exact lineMap_mem_segment ℝ _ _ s.property
  have matching := data.circle_lower_matches_parent radius_positive far slice
    (N.completedBankChain w j) child_on_cut (directions j) regular member
  exact matching.trans (B.centered_entrance_chart_eq_comparison_point i w origin j s _ physical)

/-- The upper endpoint uses the exit comparison chain in this same calibration. -/
theorem circle_upper_eq_exit_comparison_point {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
    (directions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (origin : Plane) (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval)
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) = (N.completedRootPath w).point j s) :
    data.value (S.upper.point slice.upperHeight) =
      (B.exitComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s := by
  have child_on_cut : K.projectedVertex (N.completedBankChain w j).val ∈ cuts :=
    N.completedRootPath_vertex_mem on_cuts j.castSucc
  have member : source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ∈
      segment ℝ (K.projectedVertex (N.completedBankChain w j).val)
        (K.projectedVertex
          (N.spanningCompletion.parents.parent (N.completedBankChain w j).val)) := by
    rw [physical, N.completedRootPath_point_bankChain]
    exact lineMap_mem_segment ℝ _ _ s.property
  have matching := data.circle_upper_matches_parent radius_positive far slice
    (N.completedBankChain w j) child_on_cut (directions j) regular member
  exact matching.trans (B.centered_exit_chart_eq_comparison_point i w origin j s _ physical)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
