module

public import Unfoldings.Cap.ActiveBankClosedInterval
public import Unfoldings.Cap.ClosedBankStrictStartOrder
public import Unfoldings.Cap.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.PositiveWidthBankStartOrder
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Geometry.StripBankContacts
public import Unfoldings.Topology.FiniteRecordProgress

/-! Late surviving bank bounds include all vertex radii, using actual closed tracking intervals. -/

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

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include outward footprint deep curvature_covered budget contacts tails radius_positive far

omit curvature_covered budget in
/-- Extend a late surviving bank point to a genuine closed tracking interval. -/
theorem exists_late_run_upper_tracking_interval (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff)) :
    ∃ b : ℝ, slice.upperHeight < b ∧ b < cutoff ∧
      (∀ h ∈ Set.Ioo (terminals pivot).height b,
        source.val.upper.point h ∈ closure (traces source).strictDomain) ∧
      (∀ h ∈ Set.Ioo (terminals pivot).height b,
        ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot (terminals pivot).vertex),
          ∃ s : unitInterval,
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
              (source.val.upper.point h) =
                (R.completedRootPath (terminals pivot).vertex).point j s) := by
  obtain ⟨b, after, before, closed⟩ :=
    (traces source).exists_later_height_with_all_prior_banks_closed
      ((traces source).circle_slice_heights radius_positive far slice).2
      ((traces source).circle_slice_width radius_positive slice).2
  refine ⟨b, after, before, ?_, ?_⟩
  · intro h bounds
    exact (closed h ⟨(terminals pivot).height_bounds.1.le.trans bounds.1.le, bounds.2.le⟩).2
  · intro h bounds
    have within : h ∈ Set.Icc 0 cutoff :=
      ⟨(terminals pivot).height_bounds.1.le.trans bounds.1.le, bounds.2.le.trans before.le⟩
    obtain ⟨j, s, _, tracked⟩ := terminal_banks_on_completed_path R outward D B
      (traces (cells pivot)) (tails pivot) (terminals pivot) footprint deep h
      ⟨bounds.1.le, within.2⟩
    have equal := MonotoneStrip.collapsed_chain_points_of_contacts (fun k => (cells k).val)
      (fun k => congrArg Complex.re (contacts k within))
      (fun k => (terminals k).merged h ⟨(highest k).trans bounds.1.le, within.2⟩) 0 pivot
    refine ⟨j, s, ?_⟩
    rw [wall within, equal]
    exact tracked

omit curvature_covered budget in
/-- Extend a late surviving bank point to a genuine closed tracking interval. -/
theorem exists_late_run_lower_tracking_interval (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff)) :
    ∃ b : ℝ, slice.lowerHeight < b ∧ b < cutoff ∧
      (∀ h ∈ Set.Ioo (terminals pivot).height b,
        source.val.lower.point h ∈ closure (traces source).strictDomain) ∧
      (∀ h ∈ Set.Ioo (terminals pivot).height b,
        ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot (terminals pivot).vertex),
          ∃ s : unitInterval,
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
              (source.val.lower.point h) =
                (R.completedRootPath (terminals pivot).vertex).point j s) := by
  obtain ⟨b, after, before, closed⟩ :=
    (traces source).exists_later_height_with_all_prior_banks_closed
      ((traces source).circle_slice_heights radius_positive far slice).1
      ((traces source).circle_slice_width radius_positive slice).1
  refine ⟨b, after, before, ?_, ?_⟩
  · intro h bounds
    exact (closed h ⟨(terminals pivot).height_bounds.1.le.trans bounds.1.le, bounds.2.le⟩).1
  · intro h bounds
    have within : h ∈ Set.Icc 0 cutoff :=
      ⟨(terminals pivot).height_bounds.1.le.trans bounds.1.le, bounds.2.le.trans before.le⟩
    obtain ⟨j, s, tracked, _⟩ := terminal_banks_on_completed_path R outward D B
      (traces (cells pivot)) (tails pivot) (terminals pivot) footprint deep h
      ⟨bounds.1.le, within.2⟩
    have equal := MonotoneStrip.collapsed_chain_points_of_contacts (fun k => (cells k).val)
      (fun k => congrArg Complex.re (contacts k within))
      (fun k => (terminals k).merged h ⟨(highest k).trans bounds.1.le, within.2⟩) pivot (Fin.last n)
    refine ⟨j, s, ?_⟩
    rw [wall within, ← equal]
    exact tracked

include pinches

/-- The actual terminal bound holds at every radius, including fine vertex radii. -/
theorem closed_late_upper_circle_im_ge_run_terminal (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (late : (terminals pivot).height ≤ slice.upperHeight) :
    ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).im
      ≤ ((traces source).value (source.val.upper.point slice.upperHeight)).im := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨b, after, before, closed, tracked⟩ :=
    exists_late_run_upper_tracking_interval R outward D B footprint deep P traces
      cells contacts terminals tails source slice radius_positive far
      pivot highest wall
  have bound := B.upper_bank_start_order_on_closed_interval i
    (terminals pivot).vertex (terminals pivot).on_cuts (terminals pivot).target
    (terminals pivot).original directions sectors budget (traces source) (pinches source)
    (terminals pivot).height_bounds.1.le
    (lt_of_le_of_lt late after) before.le
    closed tracked
    slice.upperHeight ⟨late, after.le⟩
  rw [← (terminals pivot).value] at bound
  exact bound

/-- The actual terminal bound holds at every radius, including fine vertex radii. -/
theorem closed_late_lower_circle_re_ge_run_terminal (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point (Set.Icc 0 cutoff))
    (late : (terminals pivot).height ≤ slice.lowerHeight) :
    ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).re
      ≤ ((traces source).value (source.val.lower.point slice.lowerHeight)).re := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨b, after, before, closed, tracked⟩ :=
    exists_late_run_lower_tracking_interval R outward D B footprint deep P traces
      cells contacts terminals tails source slice radius_positive far
      pivot highest wall
  have bound := B.lower_bank_start_order_on_closed_interval i
    (terminals pivot).vertex (terminals pivot).on_cuts (terminals pivot).target
    (terminals pivot).original directions sectors budget (traces source) (pinches source)
    (terminals pivot).height_bounds.1.le
    (lt_of_le_of_lt late after) before.le
    closed tracked
    slice.lowerHeight ⟨late, after.le⟩
  rw [← (terminals pivot).value] at bound
  exact bound

include nonnegative linear_error

/-- The actual terminal bound holds at every radius, including fine vertex radii. -/
theorem closed_late_upper_circle_im_gt_run_terminal (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    {μ : ℝ} (numerical : 2 * ε < μ)
    (margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
      0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (late : (terminals pivot).height < slice.upperHeight) :
    ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).im
      < ((traces source).value (source.val.upper.point slice.upperHeight)).im := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨b, after, before, closed, tracked⟩ :=
    exists_late_run_upper_tracking_interval R outward D B footprint deep P traces
      cells contacts terminals tails source slice radius_positive far
      pivot highest wall
  have bound := B.upper_bank_start_strict_on_closed_interval i
    (terminals pivot).vertex (terminals pivot).on_cuts (terminals pivot).target
    (terminals pivot).original directions sectors budget (traces source) (pinches source)
    (terminals pivot).height_bounds.1.le
    (lt_of_le_of_lt late.le after) before.le
    nonnegative linear_error numerical margin closed tracked
    slice.upperHeight ⟨late, after.le⟩
  rw [← (terminals pivot).value] at bound
  exact bound

/-- The actual terminal bound holds at every radius, including fine vertex radii. -/
theorem closed_late_lower_circle_re_gt_run_terminal (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point (Set.Icc 0 cutoff))
    {μ : ℝ} (numerical : 2 * ε < μ)
    (margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
      0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (late : (terminals pivot).height < slice.lowerHeight) :
    ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).re
      < ((traces source).value (source.val.lower.point slice.lowerHeight)).re := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨b, after, before, closed, tracked⟩ :=
    exists_late_run_lower_tracking_interval R outward D B footprint deep P traces
      cells contacts terminals tails source slice radius_positive far
      pivot highest wall
  have bound := B.lower_bank_start_strict_on_closed_interval i
    (terminals pivot).vertex (terminals pivot).on_cuts (terminals pivot).target
    (terminals pivot).original directions sectors budget (traces source) (pinches source)
    (terminals pivot).height_bounds.1.le
    (lt_of_le_of_lt late.le after) before.le
    nonnegative linear_error numerical margin closed tracked
    slice.lowerHeight ⟨late, after.le⟩
  rw [← (terminals pivot).value] at bound
  exact bound

end Unfoldings.ConvexCap.SectorForest
