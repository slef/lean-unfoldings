module

public import Unfoldings.Roof.ClosedSectionEarlyRunBounds
public import Unfoldings.Roof.ClosedSectionLateRunBounds
public import Unfoldings.Cap.ClosedParentPathBankContact
public import Unfoldings.Roof.TerminalRunRecords
public import Unfoldings.Geometry.CircleTerminalStrictContact

/-! Closed section contacts across disappearing strip runs preserve physical points at all radii. -/

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
          (Q.projectedVertex v.val - origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))

variable (first last : {S : MonotoneStrip // S ∈ P.cells})
  (first_slice : first.val.ClosedBankCircleSection
    (traces first).value (traces first).center cutoff radius)
  (last_slice : last.val.ClosedBankCircleSection
    (traces last).value (traces last).center cutoff radius)
  {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (first_margin : ∀ z ∈ first.val.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (last_margin : ∀ z ∈ last.val.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (empty : ∀ k, (traces (cells k)).value '' closure ((cells k).val.openSlab 0 cutoff) ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)
  (continuations : ∀ r ∈ Set.Ioo 0 radius, ∀ k,
    r ∉ (traces (cells k)).emptyCircleExceptions →
    (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
      {z | ‖z - (traces (cells k)).center‖ = r} = ∅ →
    Nonempty (B.EmptyCircleContinuation i (traces (cells k)) physicalRadius r))
  (enclosing_margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
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
  empty continuations enclosing_margin first_order last_order first_wall last_wall
  first_separator last_separator

/-- Every intermediate strip retains its own actual continuation and terminal
copy. Strict records handle early crossings, tied maxima retain contour order,
and all late banks are tracked on one actual completed parent path. -/
theorem closed_section_contact_across_empty_strip_run_same_point
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
  have both_late : (terminals leftMax).height < first_slice.upperHeight ∧
      (terminals leftMax).height < last_slice.lowerHeight := by
    apply circle_contact_forces_both_strictly_late last_quadrant.1.le last_quadrant.2.le
      equal_radius inside ?_ ?_ ?_ ?_ points_equal
    · intro early
      have bound := closed_section_early_upper_re_le_first_run_maximum R outward D B
        leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error.le
        linear_error
        pinches cells contacts ordered_cells terminals tails provenance represented leaf_coherent
        first first_slice radius_positive far empty continuations close_margin first_margin
        leftMax strict_before
        first_order first_wall first_separator early
      exact sub_le_sub_right bound (traces first).center.re
    · intro early
      have bound := closed_section_early_lower_im_le_last_run_maximum R outward D B
        leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error.le
        linear_error
        pinches cells contacts ordered_cells terminals tails provenance represented leaf_coherent
        last last_slice radius_positive far empty continuations close_margin last_margin
        rightMax strict_after
        last_order last_wall last_separator (early.trans_eq same_height)
      have tied := terminal_copies_order_at_equal_height R outward D B leaf_vertices footprint
        deep P
        traces curvature_covered budget.le nonnegative small_error.le linear_error pinches cells
        ordered_cells terminals leftMax rightMax max_order same_height
      exact sub_le_sub_right (bound.trans tied.2) (traces first).center.im
    · intro late
      have bound := closed_section_late_upper_im_gt_run_terminal
        (R := R) (outward := outward) (D := D) (B := B) (footprint := footprint) (deep := deep)
        (P := P) (traces := traces) (curvature_covered := curvature_covered) (budget := budget)
        (nonnegative := nonnegative) (linear_error := linear_error) (pinches := pinches)
        (cells := cells) (contacts := contacts) (terminals := terminals) (tails := tails)
        (source := first) (slice := first_slice)
        leftMax maximum first_wall (by nlinarith [sq_nonneg ε]) enclosing_margin late
      exact sub_lt_sub_right bound (traces first).center.im
    · intro late
      have bound := closed_section_late_lower_re_gt_run_terminal
        (R := R) (outward := outward) (D := D) (B := B) (footprint := footprint) (deep := deep)
        (P := P) (traces := traces) (curvature_covered := curvature_covered) (budget := budget)
        (nonnegative := nonnegative) (linear_error := linear_error) (pinches := pinches)
        (cells := cells) (contacts := contacts) (terminals := terminals) (tails := tails)
        (source := last) (slice := last_slice)
        leftMax maximum last_wall (by nlinarith [sq_nonneg ε]) enclosing_margin late
      exact sub_lt_sub_right bound (traces first).center.re
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells leftMax)) (tails leftMax) (terminals leftMax)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals leftMax).vertex after_leaf
    ((terminals leftMax).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  have first_tracking := closed_section_late_upper_tracking R outward D B footprint deep P traces
    cells contacts terminals tails first first_slice leftMax maximum first_wall
  have last_tracking := closed_section_late_lower_tracking R outward D B footprint deep P traces
    cells contacts terminals tails last last_slice leftMax maximum last_wall
  exact B.closed_parent_path_bank_contact_same_point i (traces first) (traces last)
    (terminals leftMax).vertex (terminals leftMax).on_cuts directions sectors budget
    (pinches first) (pinches last)
    (terminals leftMax).height_bounds.1.le both_late.1 first_slice.upper_bounds.2
    (terminals leftMax).height_bounds.1.le both_late.2 last_slice.lower_bounds.2
    (fun h bounds => (first_tracking h bounds).1) (fun h bounds => (last_tracking h bounds).1)
    (fun h bounds => (first_tracking h bounds).2) (fun h bounds => (last_tracking h bounds).2)
    ⟨both_late.1.le, le_rfl⟩ ⟨both_late.2.le, le_rfl⟩ same

end Unfoldings.ConvexRoof.SectorForest
