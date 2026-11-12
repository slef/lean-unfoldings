module

public import Unfoldings.Cap.MatchedBankAtHeight
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.RecoverableStripClosure

/-! Actual named parent-bank chart matching extends through terminal fine vertices by continuity. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  (pinches : S.ApproachedPinchesIn
    (Set.range (fun v : {v : C.Vertex Set.univ // K.projectedVertex v ∈ cuts} =>
      (fiveSectorFrame t positive small i).place (K.projectedVertex v.val - source))) 0 cutoff)
  (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
  (on_cuts : K.projectedVertex e.val ∈ cuts)
  (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
    K.projectedVertex e.val ∈ closedFiveSector t i)
  {a b : ℝ} (start : 0 ≤ a) (ordered : a < b) (finish : b ≤ cutoff)

include pinches on_cuts direction start ordered finish

/-- Only regular heights select the chart directly. Finite vertex heights,
including both closed interval endpoints, retain that same named chart value. -/
theorem lower_matches_parent_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.lower.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) ∈
        segment ℝ (K.projectedVertex e.val)
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :
    ∀ h ∈ Set.Icc a b, data.value (S.lower.point h) =
      (N.completedDevelopment D).centeredCoordinatePlacement K source calibration
        (fiveSectorFrame t positive small i).place
        (N.parentBankOpening (N.completedDevelopment D) e).entranceFace (S.lower.point h) := by
  let frame := (fiveSectorFrame t positive small i).place
  let chart := (N.completedDevelopment D).centeredCoordinatePlacement K source calibration frame
    (N.parentBankOpening (N.completedDevelopment D) e).entranceFace
  have closed_equal : IsClosed {h : ℝ | data.value (S.lower.point h) = chart (S.lower.point h)} :=
    isClosed_eq (data.continuous.comp S.lower.point_continuous)
      (chart.continuous_of_finiteDimensional.comp S.lower.point_continuous)
  have good : Set.Ioo a b \ K.framedVertexHeights source frame ⊆
      {h : ℝ | data.value (S.lower.point h) = chart (S.lower.point h)} := by
    intro h member
    have regular := K.regular_of_not_framedVertexHeights source frame
      (z := S.lower.point h) (by simpa only [S.lower.point_height] using member.2)
    have height : h ∈ Set.Ioo 0 cutoff :=
      ⟨start.trans_lt member.1.1, member.1.2.trans_le finish⟩
    have width := data.width_pos_of_approached_regular pinches height (closed h member.1) regular
    exact (data.bank_matching.at_positive_width height width e on_cuts direction).1
      regular (tracked h member.1)
  exact (Icc_subset_closure_Ioo_sdiff_finite ordered
    (K.finite_framedVertexHeights source frame)).trans (closure_minimal good closed_equal)

theorem upper_matches_parent_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.upper.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) ∈
        segment ℝ (K.projectedVertex e.val)
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :
    ∀ h ∈ Set.Icc a b, data.value (S.upper.point h) =
      (N.completedDevelopment D).centeredCoordinatePlacement K source calibration
        (fiveSectorFrame t positive small i).place
        (N.parentBankOpening (N.completedDevelopment D) e).exitFace (S.upper.point h) := by
  let frame := (fiveSectorFrame t positive small i).place
  let chart := (N.completedDevelopment D).centeredCoordinatePlacement K source calibration frame
    (N.parentBankOpening (N.completedDevelopment D) e).exitFace
  have closed_equal : IsClosed {h : ℝ | data.value (S.upper.point h) = chart (S.upper.point h)} :=
    isClosed_eq (data.continuous.comp S.upper.point_continuous)
      (chart.continuous_of_finiteDimensional.comp S.upper.point_continuous)
  have good : Set.Ioo a b \ K.framedVertexHeights source frame ⊆
      {h : ℝ | data.value (S.upper.point h) = chart (S.upper.point h)} := by
    intro h member
    have regular := K.regular_of_not_framedVertexHeights source frame
      (z := S.upper.point h) (by simpa only [S.upper.point_height] using member.2)
    have height : h ∈ Set.Ioo 0 cutoff :=
      ⟨start.trans_lt member.1.1, member.1.2.trans_le finish⟩
    have width := data.width_pos_of_upper_approached_regular pinches height
      (closed h member.1) regular
    exact (data.bank_matching.at_positive_width height width e on_cuts direction).2
      regular (tracked h member.1)
  exact (Icc_subset_closure_Ioo_sdiff_finite ordered
    (K.finite_framedVertexHeights source frame)).trans (closure_minimal good closed_equal)

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
