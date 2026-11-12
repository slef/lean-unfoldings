module

public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Cap.MatchedBankAtHeight

/-! Regular circle endpoints select their named actual parent-bank charts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  {radius : ℝ} (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)
  (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
  (on_cut : K.projectedVertex e.val ∈ cuts)
  (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
    K.projectedVertex e.val ∈ closedFiveSector t i)

include radius_positive far on_cut direction

/-- The nonempty slice itself supplies width and an active point; only the actual
regular edge containing the lower endpoint is identified by the caller. -/
theorem circle_lower_matches_parent
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ≠ (K.projectedTriangle f).vertex j)
    (member : source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ∈ segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :
    data.value (S.lower.point slice.lowerHeight) =
      (N.completedDevelopment D).centeredCoordinatePlacement K source calibration
        (fiveSectorFrame t positive small i).place
        (N.parentBankOpening (N.completedDevelopment D) e).entranceFace
        (S.lower.point slice.lowerHeight) := by
  have heights := data.circle_slice_heights radius_positive far slice
  have widths := data.circle_slice_width radius_positive slice
  exact (data.bank_matching.at_positive_width heights.1 widths.1 e on_cut direction).1
    regular member

/-- The upper endpoint similarly uses the actual exit chart, in the same calibration. -/
theorem circle_upper_matches_parent
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ≠ (K.projectedTriangle f).vertex j)
    (member : source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ∈ segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :
    data.value (S.upper.point slice.upperHeight) =
      (N.completedDevelopment D).centeredCoordinatePlacement K source calibration
        (fiveSectorFrame t positive small i).place
        (N.parentBankOpening (N.completedDevelopment D) e).exitFace
        (S.upper.point slice.upperHeight) := by
  have heights := data.circle_slice_heights radius_positive far slice
  have widths := data.circle_slice_width radius_positive slice
  exact (data.bank_matching.at_positive_width heights.2 widths.2 e on_cut direction).2
    regular member

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
