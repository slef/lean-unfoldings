module

public import Unfoldings.Cap.TerminalRunClosedLateBounds
public import Unfoldings.Cap.ClosedStripCircleSection
public import Unfoldings.Cap.RadialStripClosedBanks

/-! Closed sections retain strict terminal progress even when they end at a pinch. -/

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
  (slice : source.val.ClosedBankCircleSection
    (traces source).value (traces source).center cutoff radius)


include outward footprint deep contacts tails

/-- The actual bank is approached and follows one completed parent path up to its endpoint. -/
theorem closed_section_late_upper_tracking (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point
      (Set.Icc 0 cutoff)) :
    ∀ h ∈ Set.Ioo (terminals pivot).height slice.upperHeight,
      source.val.upper.point h ∈ closure (traces source).strictDomain ∧
        ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot (terminals pivot).vertex),
          ∃ s : unitInterval,
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
              (source.val.upper.point h) =
                (R.completedRootPath (terminals pivot).vertex).point j s := by
  intro h bounds
  have within : h ∈ Set.Icc 0 cutoff :=
    ⟨(terminals pivot).height_bounds.1.le.trans bounds.1.le,
      bounds.2.le.trans slice.upper_bounds.2⟩
  refine ⟨(traces source).upper_bank_closed_before slice.upper_closed
    (by rw [source.val.upper.point_height]; exact ⟨within.1, bounds.2.le⟩), ?_⟩
  obtain ⟨j, s, _, tracked⟩ := terminal_banks_on_completed_path R outward D B
    (traces (cells pivot)) (tails pivot) (terminals pivot) footprint deep h
    ⟨bounds.1.le, within.2⟩
  have equal := MonotoneStrip.collapsed_chain_points_of_contacts (fun k => (cells k).val)
    (fun k => congrArg Complex.re (contacts k within))
    (fun k => (terminals k).merged h ⟨(highest k).trans bounds.1.le, within.2⟩) 0 pivot
  refine ⟨j, s, ?_⟩
  rw [wall within, equal]
  exact tracked

/-- The actual bank is approached and follows one completed parent path up to its endpoint. -/
theorem closed_section_late_lower_tracking (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff)) :
    ∀ h ∈ Set.Ioo (terminals pivot).height slice.lowerHeight,
      source.val.lower.point h ∈ closure (traces source).strictDomain ∧
        ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot (terminals pivot).vertex),
          ∃ s : unitInterval,
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
              (source.val.lower.point h) =
                (R.completedRootPath (terminals pivot).vertex).point j s := by
  intro h bounds
  have within : h ∈ Set.Icc 0 cutoff :=
    ⟨(terminals pivot).height_bounds.1.le.trans bounds.1.le,
      bounds.2.le.trans slice.lower_bounds.2⟩
  refine ⟨(traces source).lower_bank_closed_before slice.lower_closed
    (by rw [source.val.lower.point_height]; exact ⟨within.1, bounds.2.le⟩), ?_⟩
  obtain ⟨j, s, tracked, _⟩ := terminal_banks_on_completed_path R outward D B
    (traces (cells pivot)) (tails pivot) (terminals pivot) footprint deep h
    ⟨bounds.1.le, within.2⟩
  have equal := MonotoneStrip.collapsed_chain_points_of_contacts (fun k => (cells k).val)
    (fun k => congrArg Complex.re (contacts k within))
    (fun k => (terminals k).merged h ⟨(highest k).trans bounds.1.le, within.2⟩) pivot (Fin.last n)
  refine ⟨j, s, ?_⟩
  rw [wall within, ← equal]
  exact tracked

include curvature_covered budget pinches nonnegative linear_error

/-- Strictly later closed sections progress beyond the actual terminal
in the controlling coordinate. -/
theorem closed_section_late_upper_im_gt_run_terminal (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point
      (Set.Icc 0 cutoff))
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
  have tracking := closed_section_late_upper_tracking R outward D B footprint deep P traces
    cells contacts terminals tails source slice pivot highest wall
  have bound := B.upper_bank_start_strict_on_closed_interval i
    (terminals pivot).vertex (terminals pivot).on_cuts (terminals pivot).target
    (terminals pivot).original directions sectors budget (traces source) (pinches source)
    (terminals pivot).height_bounds.1.le late slice.upper_bounds.2
    nonnegative linear_error numerical margin (fun h bounds => (tracking h bounds).1)
    (fun h bounds => (tracking h bounds).2) slice.upperHeight ⟨late, le_rfl⟩
  rw [← (terminals pivot).value] at bound
  exact bound

/-- Strictly later closed sections progress beyond the actual terminal
in the controlling coordinate. -/
theorem closed_section_late_lower_re_gt_run_terminal (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff))
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
  have tracking := closed_section_late_lower_tracking R outward D B footprint deep P traces
    cells contacts terminals tails source slice pivot highest wall
  have bound := B.lower_bank_start_strict_on_closed_interval i
    (terminals pivot).vertex (terminals pivot).on_cuts (terminals pivot).target
    (terminals pivot).original directions sectors budget (traces source) (pinches source)
    (terminals pivot).height_bounds.1.le late slice.lower_bounds.2
    nonnegative linear_error numerical margin (fun h bounds => (tracking h bounds).1)
    (fun h bounds => (tracking h bounds).2) slice.lowerHeight ⟨late, le_rfl⟩
  rw [← (terminals pivot).value] at bound
  exact bound

end Unfoldings.ConvexCap.SectorForest
