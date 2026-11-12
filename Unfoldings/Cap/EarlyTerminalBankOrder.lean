module

public import Unfoldings.Cap.GeometricTailTraceOrder
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Cap.MatchedStripBankOrder
public import Unfoldings.Cap.LeafTailCircleSeparation
public import Unfoldings.Cap.EmptyCircleContinuation

/-! Early surviving circle crossings are bounded by the intermediate strip's terminal copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (outward : R.Outward) (w : FineC.Vertex Set.univ)
  (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
  (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
  (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
  (D : FacewiseDevelopment FineC R.retain)
  (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
  {S U : MonotoneStrip} {ε physicalRadius radius : ℝ}
  (data : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (middle : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
  (pinches : U.ApproachedPinchesIn
    (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
        M.extendedGeometricCuts F} =>
      (fiveSectorFrame t positive small i).place (Q.projectedVertex v.val -
        K.projectedVertex origin))) 0 cutoff)
  (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
  (curvature_covered : ∀ v : FineC.Vertex Set.univ,
    0 < FineC.interiorAngularDefect Set.univ v →
      Q.projectedVertex v ∈ M.extendedGeometricCuts F)
  (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)

include outward same_start footprint deep pinches curvature_covered budget
  radius_positive far outside

/-- If the left survivor crosses before the intermediate terminal height, its
exit coordinate is at most that terminal copy's horizontal coordinate. -/
theorem upper_circle_le_terminal_re
    (wall : S.upper = U.lower)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff U.lower)
    (after_leaf : leaf.point.re + leaf.point.im ≤ slice.upperHeight)
    (early : slice.upperHeight ≤ continuation.height) :
    (data.value (S.upper.point slice.upperHeight)).re ≤
      (middle.value (U.lower.point continuation.height)).re := by
  have height := (data.circle_slice_heights radius_positive far slice).2
  have regular := data.regular_of_radius_not_vertexRadii outside slice.upper_closed
    slice.upper_radius
  have included : U.openSlab 0 cutoff ⊆ middle.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have terminal_closed : U.lower.point continuation.height ∈ closure middle.strictDomain :=
    closure_mono included continuation.lower_closed
  have closed : U.lower.point slice.upperHeight ∈ closure middle.strictDomain := by
    apply middle.closed_initial terminal_closed
    · change U.lower.coordinate ((U.lower.point slice.upperHeight).re +
        (U.lower.point slice.upperHeight).im) ≤ (U.lower.point slice.upperHeight).re ∧
          (U.lower.point slice.upperHeight).re ≤ U.upper.coordinate
            ((U.lower.point slice.upperHeight).re + (U.lower.point slice.upperHeight).im)
      rw [U.lower.point_height]
      exact ⟨le_rfl, U.ordered _⟩
    · rw [U.lower.point_height, U.lower.point_height]
      exact ⟨height.1.le, early⟩
  have width := middle.width_pos_of_approached_regular pinches height closed
    (by rw [← wall]; exact regular)
  obtain ⟨j, s, tracked⟩ := leaf.tailGraph_point_on_completed_path R outward w same_start
    footprint deep ⟨after_leaf, height.2.le⟩
  have physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) = (R.completedRootPath w).point j s := by
    rw [wall, completion.point_eq ⟨after_leaf, height.2.le⟩, tracked,
      LinearIsometryEquiv.symm_apply_apply]
    abel
  obtain ⟨anchor, _, at_start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered positive
    small lower leaf.val leaf.property.1
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [same_start, M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨anchor, at_start⟩
  have directions := leaf.completed_bank_directions R outward w same_start
  have sectors := leaf.completed_curved_subtree_sectors R outward w same_start curvature_covered
  have gap := B.matched_strip_bank_order i data middle wall height
    (data.circle_slice_width radius_positive slice).2 width (R.completedBankChain w j)
    (R.completedRootPath_vertex_mem on_cuts j.castSucc) (directions j) (sectors j) budget.le s
    regular (physical.trans (R.completedRootPath_point_bankChain w j s))
  have progress := leaf.developed_completed_bank_order R D B middle (Or.inl rfl) completion
    after_leaf early continuation.height_bounds.2.le
    (continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep)) terminal_closed
  exact gap.1.trans progress.1

/-- The right survivor's early entrance crossing is bounded vertically by the
same terminal copy. This is the other coordinate needed for circle separation. -/
theorem lower_circle_le_terminal_im
    (wall : U.upper = S.lower)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff U.upper)
    (after_leaf : leaf.point.re + leaf.point.im ≤ slice.lowerHeight)
    (early : slice.lowerHeight ≤ continuation.height) :
    (data.value (S.lower.point slice.lowerHeight)).im ≤
      (middle.value (U.lower.point continuation.height)).im := by
  have height := (data.circle_slice_heights radius_positive far slice).1
  have regular := data.regular_of_radius_not_vertexRadii outside slice.lower_closed
    slice.lower_radius
  have included : U.openSlab 0 cutoff ⊆ middle.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have terminal_closed : U.upper.point continuation.height ∈ closure middle.strictDomain :=
    closure_mono included continuation.upper_closed
  have closed : U.upper.point slice.lowerHeight ∈ closure middle.strictDomain := by
    apply middle.closed_initial terminal_closed
    · change U.lower.coordinate ((U.upper.point slice.lowerHeight).re +
        (U.upper.point slice.lowerHeight).im) ≤ (U.upper.point slice.lowerHeight).re ∧
          (U.upper.point slice.lowerHeight).re ≤ U.upper.coordinate
            ((U.upper.point slice.lowerHeight).re + (U.upper.point slice.lowerHeight).im)
      rw [U.upper.point_height]
      exact ⟨U.ordered _, le_rfl⟩
    · rw [U.upper.point_height, U.upper.point_height]
      exact ⟨height.1.le, early⟩
  have width := middle.width_pos_of_upper_approached_regular pinches height closed
    (by rw [wall]; exact regular)
  obtain ⟨j, s, tracked⟩ := leaf.tailGraph_point_on_completed_path R outward w same_start
    footprint deep ⟨after_leaf, height.2.le⟩
  have physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (U.upper.point slice.lowerHeight) = (R.completedRootPath w).point j s := by
    rw [completion.point_eq ⟨after_leaf, height.2.le⟩, tracked,
      LinearIsometryEquiv.symm_apply_apply]
    abel
  obtain ⟨anchor, _, at_start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered positive
    small lower leaf.val leaf.property.1
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [same_start, M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨anchor, at_start⟩
  have directions := leaf.completed_bank_directions R outward w same_start
  have sectors := leaf.completed_curved_subtree_sectors R outward w same_start curvature_covered
  have gap := B.matched_strip_bank_order i middle data wall height
    width (data.circle_slice_width radius_positive slice).1 (R.completedBankChain w j)
    (R.completedRootPath_vertex_mem on_cuts j.castSucc) (directions j) (sectors j) budget.le s
    (by rw [wall]; exact regular) (physical.trans (R.completedRootPath_point_bankChain w j s))
  have progress := leaf.developed_completed_bank_order R D B middle (Or.inr rfl) completion
    after_leaf early continuation.height_bounds.2.le
    (continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep)) terminal_closed
  have terminal_equal := U.lower.point_eq_of_same_coordinate U.upper
    (continuation.merged continuation.height ⟨le_rfl, continuation.height_bounds.2.le⟩)
  rw [← terminal_equal] at progress
  exact gap.2.trans progress.2

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
