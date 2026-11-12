module

public import Unfoldings.Cap.WaterfallLevelBankOrder
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Geometry.RecoverableStripClosure
public import Unfoldings.Cap.RadialStripLevelOrder
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.SubdivisionActiveCells
public import Unfoldings.Topology.OrderedBankPieces

/-! Actual approached bank order extends to all sweep heights, including terminal mesh vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}

/-- Both compared banks remain actual approached values. Vertex heights are
removed for matching and restored by continuity, without evaluating dead traces
beyond their own approached domains. -/
theorem waterfall_closed_level_bank_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) {ε : ℝ}
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε ≤ 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (first last : {S : MonotoneStrip // S ∈ P.cells})
    (ordered : List.Sublist [first, last] P.cells.attach)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (first_closed : first.val.upper.point h ∈ closure (traces first).strictDomain)
    (last_closed : last.val.lower.point h ∈ closure (traces last).strictDomain) :
    ((traces first).value (first.val.upper.point h)).re ≤
        ((traces last).value (last.val.lower.point h)).re ∧
      ((traces last).value (last.val.lower.point h)).im ≤
        ((traces first).value (first.val.upper.point h)).im := by
  let frame := (fiveSectorFrame t positive small i).place
  let good : Set ℝ := {k |
    ((traces first).value (first.val.upper.point k)).re ≤
        ((traces last).value (last.val.lower.point k)).re ∧
      ((traces last).value (last.val.lower.point k)).im ≤
        ((traces first).value (first.val.upper.point k)).im}
  have first_continuous := (traces first).continuous.comp first.val.upper.point_continuous
  have last_continuous := (traces last).continuous.comp last.val.lower.point_continuous
  have closed_good : IsClosed good :=
    (isClosed_le (Complex.continuous_re.comp first_continuous)
      (Complex.continuous_re.comp last_continuous)).inter
      (isClosed_le (Complex.continuous_im.comp last_continuous)
        (Complex.continuous_im.comp first_continuous))
  have regular_good : Set.Ioo 0 h \ Q.framedVertexHeights (K.projectedVertex origin) frame ⊆
      good := by
    intro k member
    have within : k ∈ Set.Ioo 0 cutoff := ⟨member.1.1, member.1.2.trans height.2⟩
    have first_closed_k := (traces first).upper_bank_closed_before first_closed
      (by rw [first.val.upper.point_height]; exact ⟨member.1.1.le, member.1.2.le⟩)
    have last_closed_k := (traces last).lower_bank_closed_before last_closed
      (by rw [last.val.lower.point_height]; exact ⟨member.1.1.le, member.1.2.le⟩)
    have first_regular := Q.regular_of_not_framedVertexHeights (K.projectedVertex origin) frame
      (z := first.val.upper.point k)
      (by simpa only [first.val.upper.point_height] using member.2)
    have last_regular := Q.regular_of_not_framedVertexHeights (K.projectedVertex origin) frame
      (z := last.val.lower.point k)
      (by simpa only [last.val.lower.point_height] using member.2)
    have first_width := (traces first).width_pos_of_upper_approached_regular (pinches first)
      within first_closed_k first_regular
    have last_width := (traces last).width_pos_of_approached_regular (pinches last)
      within last_closed_k last_regular
    have first_kept : decide (first.val.lower.coordinate k < first.val.upper.coordinate k) = true :=
      decide_eq_true_eq.mpr first_width
    have last_kept : decide (last.val.lower.coordinate k < last.val.upper.coordinate k) = true :=
      decide_eq_true_eq.mpr last_width
    have filtered : List.Sublist [first, last] (P.activeCells k) := by
      have sublist := List.Sublist.filter
        (fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
          decide (cell.val.lower.coordinate k < cell.val.upper.coordinate k)) ordered
      simpa only [MonotoneStrip.Subdivision.activeCells, List.filter_cons, List.filter_nil,
        first_kept, last_kept, ↓reduceIte]
        using sublist
    have all := waterfall_level_bank_pairwise R outward D B leaf_vertices footprint deep P traces
      curvature_covered budget nonnegative small_error linear_error within member.2
    have paired := List.Pairwise.sublist (l₁ := [first, last]) filtered all
    exact (List.pairwise_pair (a := first) (b := last)).mp paired
  have all := (Icc_subset_closure_Ioo_sdiff_finite height.1
    (Q.finite_framedVertexHeights (K.projectedVertex origin) frame)).trans
    (closure_minimal regular_good closed_good)
  exact all ⟨height.1.le, le_rfl⟩

end Unfoldings.ConvexCap.SectorForest
