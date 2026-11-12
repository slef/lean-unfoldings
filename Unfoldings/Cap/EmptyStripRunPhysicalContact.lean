module

public import Unfoldings.Cap.EmptyStripRunContactSeparation
public import Unfoldings.Cap.TerminalRunStrictLateBoundsContacts
public import Unfoldings.Cap.EmptyStripChainLatePhysicalContact
public import Unfoldings.Geometry.CircleTerminalContact

/-! Separate circle slices across any nonempty run of disappearing actual strips. -/

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

variable
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
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))

variable (first last : {S : MonotoneStrip // S ∈ P.cells})
  (first_slice : first.val.BankCircleSlice (traces first).value (traces first).center cutoff radius)
  (last_slice : last.val.BankCircleSlice (traces last).value (traces last).center cutoff radius)
  {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (first_margin : ∀ z ∈ first.val.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (last_margin : ∀ z ∈ last.val.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (outside_empty : ∀ k, radius ∉ (traces (cells k)).emptyCircleExceptions)
  (empty : ∀ k, (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)
  (first_order : ∀ k, List.Sublist [first, cells k] P.cells.attach)
  (last_order : ∀ k, List.Sublist [cells k, last] P.cells.attach)
  (first_wall : Set.EqOn first.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
  (last_wall : Set.EqOn last.val.lower.point (cells (Fin.last n)).val.upper.point
    (Set.Icc 0 cutoff))
  (first_separator : first.val.upper ∈ P.separators)
  (last_separator : last.val.lower ∈ P.separators)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells terminals tails provenance represented
  leaf_coherent first_slice last_slice numerical first_margin last_margin radius_positive far
  outside outside_empty empty first_order last_order first_wall last_wall
  first_separator last_separator

/-- Every intermediate strip retains its own actual continuation and terminal
copy. Strict records handle early crossings, tied maxima retain contour order,
and all late banks are tracked on one actual completed parent path. -/
theorem circle_contact_across_empty_strip_run_same_point
    (same : (traces first).value (first.val.upper.point first_slice.upperHeight) =
      (traces last).value (last.val.lower.point last_slice.lowerHeight)) :
    (fiveSectorFrame t positive small i).place.symm (first.val.upper.point
      first_slice.upperHeight) =
      (fiveSectorFrame t positive small i).place.symm (last.val.lower.point
        last_slice.lowerHeight) := by
  obtain ⟨leftMax, rightMax, max_order, same_height, maximum, strict_before, strict_after⟩ :=
    exists_first_last_max_positions (fun k => (terminals k).height)
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have first_quadrant := (traces first).strict_quadrant_of_closed_margin close_margin first_margin
    first_slice.upper_closed ((traces first).closed_height_pos_of_norm first_slice.upper_closed
      (by rw [first_slice.upper_radius]; exact radius_positive))
  have last_quadrant := (traces last).strict_quadrant_of_closed_margin close_margin last_margin
    last_slice.lower_closed ((traces last).closed_height_pos_of_norm last_slice.lower_closed
      (by rw [last_slice.lower_radius]; exact radius_positive))
  let x :=
    (traces first).value (first.val.upper.point first_slice.upperHeight) - (traces first).center
  let y := (traces last).value (last.val.lower.point last_slice.lowerHeight) - (traces first).center
  let m := (traces (cells leftMax)).value
    ((cells leftMax).val.lower.point (terminals leftMax).height) - (traces first).center
  have equal_radius : ‖x‖ = ‖y‖ := first_slice.upper_radius.trans last_slice.lower_radius.symm
  have inside : ‖m‖ < ‖x‖ := by
    change ‖(traces (cells leftMax)).value
      ((cells leftMax).val.lower.point (terminals leftMax).height) - (traces first).center‖ <
        ‖(traces first).value (first.val.upper.point first_slice.upperHeight) -
          (traces first).center‖
    rw [first_slice.upper_radius]
    exact (terminals leftMax).inside
  have points_equal : x = y := congrArg (fun z : ℂ => z - (traces first).center) same
  have both_late : (terminals leftMax).height ≤ first_slice.upperHeight ∧
      (terminals leftMax).height ≤ last_slice.lowerHeight := by
    apply circle_contact_forces_both_late last_quadrant.1.le last_quadrant.2.le
      equal_radius inside ?_ ?_ ?_ ?_ points_equal
    · intro early
      have bound := early_upper_circle_re_le_first_run_maximum_of_contacts R outward D B
        leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error.le
        linear_error
        pinches cells contacts ordered_cells terminals tails provenance represented leaf_coherent
        first first_slice radius_positive far outside outside_empty empty leftMax strict_before
        first_order first_wall first_separator early
      exact sub_le_sub_right bound (traces first).center.re
    · intro early
      have bound := early_lower_circle_im_le_last_run_maximum_of_contacts R outward D B
        leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error.le
        linear_error
        pinches cells contacts ordered_cells terminals tails provenance represented leaf_coherent
        last last_slice radius_positive far outside outside_empty empty rightMax strict_after
        last_order last_wall last_separator (early.trans_eq same_height)
      have tied := terminal_copies_order_at_equal_height R outward D B leaf_vertices footprint
        deep P
        traces curvature_covered budget.le nonnegative small_error.le linear_error pinches cells
        ordered_cells terminals leftMax rightMax max_order same_height
      exact sub_le_sub_right (bound.trans tied.2) (traces first).center.im
    · intro late
      have bound := late_upper_circle_im_gt_run_terminal_of_contacts
        (R := R) (outward := outward) (D := D) (B := B) (footprint := footprint) (deep := deep)
        (P := P) (traces := traces) (curvature_covered := curvature_covered) (budget := budget)
        (cells := cells) (contacts := contacts) (terminals := terminals) (tails := tails)
        (source := first) (slice := first_slice) (radius_positive := radius_positive) (far := far)
        leftMax maximum outside first_wall late
      exact sub_lt_sub_right bound (traces first).center.im
    · intro late
      have bound := late_lower_circle_re_gt_run_terminal_of_contacts
        (R := R) (outward := outward) (D := D) (B := B) (footprint := footprint) (deep := deep)
        (P := P) (traces := traces) (curvature_covered := curvature_covered) (budget := budget)
        (cells := cells) (contacts := contacts) (terminals := terminals) (tails := tails)
        (source := last) (slice := last_slice) (radius_positive := radius_positive) (far := far)
        leftMax maximum outside last_wall late
      exact sub_lt_sub_right bound (traces first).center.re
  exact circle_contact_after_terminal_strip_chain_same_point R outward D B (traces first)
    (traces last) (traces (cells leftMax)) (tails leftMax) (terminals leftMax) footprint deep
    curvature_covered budget radius_positive far outside first_slice last_slice
    (fun k => (cells k).val) contacts leftMax rfl first_wall last_wall
    (fun k h member => (terminals k).merged h ⟨(maximum k).trans member.1, member.2⟩)
    both_late.1 both_late.2 same

end Unfoldings.ConvexCap.SectorForest
