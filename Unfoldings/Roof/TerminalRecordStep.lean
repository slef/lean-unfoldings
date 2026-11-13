module

public import Unfoldings.Roof.WaterfallClosedLevelBankOrder
public import Unfoldings.Roof.TerminalBankIntervalOrder
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Geometry.RecoverableStripClosure
public import Unfoldings.Cap.RadialStripLevelOrder
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.SubdivisionActiveCells
public import Unfoldings.Topology.OrderedBankPieces

/-! Progress from one actual terminal copy to a later terminal along the same physical tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

variable
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
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
          (Q.projectedVertex v.val - origin))) 0 cutoff)

variable (first last : {S : MonotoneStrip // S ∈ P.cells}) {physicalRadius radius : ℝ}
  (first_terminal : B.EmptyCircleContinuation i (traces first) physicalRadius radius)
  (last_terminal : B.EmptyCircleContinuation i (traces last) physicalRadius radius)
  (height_order : first_terminal.height ≤ last_terminal.height)
  (tails : first.val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches height_order tails

/-- Ordered approached values supply the initial gap, and the actual terminal
tail supplies coordinate progress until the next, higher terminal. -/
theorem terminal_re_le_of_lower_tail_agreement
    (ordered : List.Sublist [first, last] P.cells.attach)
    (agreement : Set.EqOn last.val.lower.point first.val.lower.point
      (Set.Icc first_terminal.height last_terminal.height)) :
    ((traces first).value (first.val.lower.point first_terminal.height)).re ≤
      ((traces last).value (last.val.lower.point last_terminal.height)).re := by
  have first_included : first.val.openSlab 0 cutoff ⊆ (traces first).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_included : last.val.openSlab 0 cutoff ⊆ (traces last).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_closed := closure_mono first_included first_terminal.upper_closed
  have last_endpoint := closure_mono last_included last_terminal.lower_closed
  have last_start := (traces last).lower_bank_closed_before last_endpoint
    (by rw [last.val.lower.point_height]; exact ⟨first_terminal.height_bounds.1.le, height_order⟩)
  have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches first last ordered
    first_terminal.height_bounds first_closed last_start
  have progress := terminal_tail_bank_interval_order R D B (traces first) tails first_terminal
    (traces last) (Or.inl rfl) deep height_order last_terminal.height_bounds.2.le
    agreement last_endpoint
  have first_equal := first.val.lower.point_eq_of_same_coordinate first.val.upper
    (first_terminal.merged first_terminal.height ⟨le_rfl, first_terminal.height_bounds.2.le⟩)
  rw [← first_equal] at gap
  exact gap.1.trans progress.1

/-- For records processed from right to left, the corresponding actual
terminal copy progresses vertically. -/
theorem terminal_im_le_of_upper_tail_agreement
    (ordered : List.Sublist [last, first] P.cells.attach)
    (agreement : Set.EqOn last.val.upper.point first.val.lower.point
      (Set.Icc first_terminal.height last_terminal.height)) :
    ((traces first).value (first.val.lower.point first_terminal.height)).im ≤
      ((traces last).value (last.val.lower.point last_terminal.height)).im := by
  have first_included : first.val.openSlab 0 cutoff ⊆ (traces first).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_included : last.val.openSlab 0 cutoff ⊆ (traces last).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_closed := closure_mono first_included first_terminal.lower_closed
  have last_endpoint := closure_mono last_included last_terminal.upper_closed
  have last_start := (traces last).upper_bank_closed_before last_endpoint
    (by rw [last.val.upper.point_height]; exact ⟨first_terminal.height_bounds.1.le, height_order⟩)
  have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches last first ordered
    first_terminal.height_bounds last_start first_closed
  have progress := terminal_tail_bank_interval_order R D B (traces first) tails first_terminal
    (traces last) (Or.inr rfl) deep height_order last_terminal.height_bounds.2.le
    agreement last_endpoint
  have last_equal := last.val.lower.point_eq_of_same_coordinate last.val.upper
    (last_terminal.merged last_terminal.height ⟨le_rfl, last_terminal.height_bounds.2.le⟩)
  rw [← last_equal] at progress
  exact gap.2.trans progress.2

end Unfoldings.ConvexRoof.SectorForest
