module

public import Unfoldings.Cap.ClosedStripCircleSection
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Roof.LeafTailCircleOrder
public import Unfoldings.Cap.ClosedParentPathBankContact
public import Unfoldings.Cap.ActiveBankClosedInterval

/-! Contact across one actual leaf tail identifies the same physical circle endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small i)

/-- Approached tail contacts identify physical points even if a section is only a pinch. -/
theorem closed_section_tail_contact_same_point
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T : MonotoneStrip} {ε : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (first_pinches : S.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)
    (last_pinches : T.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    {radius : ℝ}
    (first_slice : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (last_slice : T.ClosedBankCircleSection other.value other.center cutoff radius)
    (first_tail : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff S.upper)
    (last_tail : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff T.lower)
    (first_after : leaf.point.re + leaf.point.im < first_slice.upperHeight)
    (last_after : leaf.point.re + leaf.point.im < last_slice.lowerHeight)
    (same : data.value (S.upper.point first_slice.upperHeight) =
      other.value (T.lower.point last_slice.lowerHeight)) :
    (fiveSectorFrame t positive small i).place.symm (S.upper.point first_slice.upperHeight) =
      (fiveSectorFrame t positive small i).place.symm (T.lower.point last_slice.lowerHeight) := by
  obtain ⟨anchor, _, start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered positive small
     leaf.val leaf.property.1
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [same_start, M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨anchor, start⟩
  have source_nonnegative : 0 ≤ leaf.point.re + leaf.point.im :=
    add_nonneg leaf.point_nonnegative.1 leaf.point_nonnegative.2
  let first_end := first_slice.upperHeight
  have first_prior (h : ℝ) (bounds : h ∈ Set.Icc 0 first_end) :
      S.upper.point h ∈ closure data.strictDomain :=
    data.upper_bank_closed_before first_slice.upper_closed
      (by rw [S.upper.point_height]; exact bounds)
  have first_closed : ∀ h ∈ Set.Ioo (leaf.point.re + leaf.point.im) first_end,
      S.upper.point h ∈ closure data.strictDomain := fun h bounds =>
    first_prior h ⟨source_nonnegative.trans bounds.1.le, bounds.2.le⟩
  have first_tracked : ∀ h ∈ Set.Ioo (leaf.point.re + leaf.point.im) first_end,
      ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        origin + (fiveSectorFrame t positive small i).place.symm
          (S.upper.point h) = (R.completedRootPath w).point j s := by
    intro h bounds
    have within : h ∈ Set.Icc (leaf.point.re + leaf.point.im) cutoff :=
      ⟨bounds.1.le, bounds.2.le.trans first_slice.upper_bounds.2⟩
    obtain ⟨j, s, point⟩ := leaf.tailGraph_point_on_completed_path R outward w same_start
      footprint deep within
    refine ⟨j, s, ?_⟩
    rw [first_tail.point_eq within, point, LinearIsometryEquiv.symm_apply_apply]
    abel
  let last_end := last_slice.lowerHeight
  have last_prior (h : ℝ) (bounds : h ∈ Set.Icc 0 last_end) :
      T.lower.point h ∈ closure other.strictDomain :=
    other.lower_bank_closed_before last_slice.lower_closed
      (by rw [T.lower.point_height]; exact bounds)
  have last_closed : ∀ h ∈ Set.Ioo (leaf.point.re + leaf.point.im) last_end,
      T.lower.point h ∈ closure other.strictDomain := fun h bounds =>
    last_prior h ⟨source_nonnegative.trans bounds.1.le, bounds.2.le⟩
  have last_tracked : ∀ h ∈ Set.Ioo (leaf.point.re + leaf.point.im) last_end,
      ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        origin + (fiveSectorFrame t positive small i).place.symm
          (T.lower.point h) = (R.completedRootPath w).point j s := by
    intro h bounds
    have within : h ∈ Set.Icc (leaf.point.re + leaf.point.im) cutoff :=
      ⟨bounds.1.le, bounds.2.le.trans last_slice.lower_bounds.2⟩
    obtain ⟨j, s, point⟩ := leaf.tailGraph_point_on_completed_path R outward w same_start
      footprint deep within
    refine ⟨j, s, ?_⟩
    rw [last_tail.point_eq within, point, LinearIsometryEquiv.symm_apply_apply]
    abel
  exact B.closed_parent_path_bank_contact_same_point i data other w on_cuts
    (leaf.completed_bank_directions R outward w same_start)
    (leaf.completed_curved_subtree_sectors R outward w same_start curvature_covered)
    budget first_pinches last_pinches
    source_nonnegative first_after first_slice.upper_bounds.2
    source_nonnegative last_after last_slice.lower_bounds.2
    first_closed last_closed first_tracked last_tracked
    ⟨first_after.le, le_rfl⟩ ⟨last_after.le, le_rfl⟩ same

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
