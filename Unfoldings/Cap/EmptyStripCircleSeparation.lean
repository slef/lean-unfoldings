module

public import Unfoldings.Cap.EmptyNeighborCirclePrefix
public import Unfoldings.Cap.EarlyTerminalBankOrder
public import Unfoldings.Cap.LateTerminalBankOrder
public import Unfoldings.Cap.EmptyStripLateCircleSeparation
public import Unfoldings.Geometry.CircleTerminalOrder
public import Unfoldings.Cap.ParentPathCircleBankOrder
public import Unfoldings.Cap.RegularCircleRadius

/-! Separate two surviving circle slices across one disappearing actual strip. -/

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

/-- All early and late crossing cases use actual terminal and bank values.
The shared-leaf height correspondence is derived from the constructed waterfall,
without a developed gap-order or comparison-curve avoidance hypothesis. -/
theorem circle_slices_disjoint_across_empty_strip
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T U : MonotoneStrip} {ε μ cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (middle : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
    (tails : U.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
    (footprint : Q.footprint = K.clipFootprint Z)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_wall : S.upper = U.lower) (last_wall : T.lower = U.upper)
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G)
    (traces : ∀ V ∈ P.cells, Nonempty (R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i V ε cutoff))
    (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells) (middle_cell : U ∈ P.cells)
    (pinches : U.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (outside_middle : radius ∉ middle.emptyCircleExceptions)
    (empty : middle.value '' U.openSlab 0 cutoff ∩ {z | ‖z - middle.center‖ = radius} = ∅)
    (first_separator : U.lower ∈ P.separators) (last_separator : U.upper ∈ P.separators)
    (first_leaf : ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val ∧
        leaf.point.re + leaf.point.im ≤ cutoff ∧
        D.ProjectedCoherentAt Q (F.geometricPosition leaf.val) ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff U.lower)
    (last_leaf : ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val ∧
        leaf.point.re + leaf.point.im ≤ cutoff ∧
        D.ProjectedCoherentAt Q (F.geometricPosition leaf.val) ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff U.upper) :
    Disjoint (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius})
      (other.value '' T.openSlab 0 cutoff ∩ {z | ‖z - other.center‖ = radius}) := by
  by_cases both_after : continuation.height ≤ first_slice.upperHeight ∧
      continuation.height ≤ last_slice.lowerHeight
  · exact circle_slices_disjoint_after_terminal_strip R outward D B data other middle tails
      continuation footprint deep nonnegative small_error numerical linear_error first_margin
      last_margin curvature_covered budget radius_positive far outside first_slice last_slice
      first_wall last_wall both_after.1 both_after.2
  obtain ⟨leftLeaf, leftVertex, leftStart, leftActive, leftCoherent, leftCompletion⟩ := first_leaf
  obtain ⟨rightLeaf, rightVertex, rightStart, rightActive, rightCoherent, rightCompletion⟩ :=
    last_leaf
  have left_after := leftLeaf.upper_circle_after_empty_neighbor_leaf R D B deep P represented
    traces leftActive leftCoherent first_cell middle_cell data middle tails pinches continuation
    radius_positive far outside outside_middle empty first_slice first_separator first_wall
    leftCompletion
  have right_after := rightLeaf.lower_circle_after_empty_neighbor_leaf R D B deep P represented
    traces rightActive rightCoherent last_cell middle_cell other middle tails pinches continuation
    radius_positive far outside outside_middle empty last_slice last_separator last_wall
    rightCompletion
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have first_quadrant := data.strict_quadrant_of_closed_margin close_margin first_margin
    first_slice.upper_closed (data.closed_height_pos_of_norm first_slice.upper_closed
      (by rw [first_slice.upper_radius]; exact radius_positive))
  have last_quadrant := other.strict_quadrant_of_closed_margin close_margin last_margin
    last_slice.lower_closed (other.closed_height_pos_of_norm last_slice.lower_closed
      (by rw [last_slice.lower_radius]; exact radius_positive))
  let x := data.value (S.upper.point first_slice.upperHeight) - data.center
  let y := other.value (T.lower.point last_slice.lowerHeight) - data.center
  let m := middle.value (U.lower.point continuation.height) - data.center
  have equal_radius : ‖x‖ = ‖y‖ := first_slice.upper_radius.trans last_slice.lower_radius.symm
  have inside : ‖m‖ < ‖x‖ := by
    change ‖middle.value (U.lower.point continuation.height) - data.center‖ <
      ‖data.value (S.upper.point first_slice.upperHeight) - data.center‖
    rw [first_slice.upper_radius]
    exact continuation.inside
  have gap : x.re ≤ y.re ∧ y.im ≤ x.im := by
    apply circle_order_across_terminal_height first_quadrant.1.le first_quadrant.2.le
      last_quadrant.1.le last_quadrant.2.le equal_radius inside
      (a := first_slice.upperHeight) (b := last_slice.lowerHeight)
      (terminal := continuation.height)
    · intro early
      have bound := leftLeaf.upper_circle_le_terminal_re R outward leftVertex leftStart
        footprint deep D B data middle pinches continuation curvature_covered budget
        radius_positive far outside first_slice first_wall leftCompletion left_after.le early
      exact sub_le_sub_right bound data.center.re
    · intro early
      have bound := rightLeaf.lower_circle_le_terminal_im R outward rightVertex rightStart
        footprint deep D B other middle pinches continuation curvature_covered budget
        radius_positive far outside last_slice last_wall.symm rightCompletion right_after.le early
      exact sub_le_sub_right bound data.center.im
    · intro late
      have bound := terminal_im_le_late_upper_circle R outward D B data middle tails continuation
        footprint deep curvature_covered budget radius_positive far outside
        first_slice first_wall late
      exact sub_le_sub_right bound data.center.im
    · intro late
      have bound := terminal_re_le_late_lower_circle R outward D B other middle tails continuation
        footprint deep curvature_covered budget radius_positive far outside
        last_slice last_wall late
      exact sub_le_sub_right bound data.center.re
    · intro first last
      exact (both_after ⟨first, last⟩).elim
  have first_order := data.bank_circle_order nonnegative small_error numerical linear_error
    first_margin radius_positive first_slice.lower_closed first_slice.upper_closed
    first_slice.lower_radius first_slice.upper_radius first_slice.distinct
  have last_order := other.bank_circle_order nonnegative small_error numerical linear_error
    last_margin radius_positive last_slice.lower_closed last_slice.upper_closed
    last_slice.lower_radius last_slice.upper_radius last_slice.distinct
  apply first_slice.disjoint_circle_images_of_bank_order last_slice first_order.1 last_order.1 gap.1
  rintro z ⟨p, member, rfl⟩
  exact data.strict_quadrant_of_margin close_margin first_margin member

end Unfoldings.ConvexCap.SectorForest
