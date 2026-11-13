module

public import Unfoldings.Roof.ClosedSectionLateRunBounds
public import Unfoldings.Roof.BoundaryTerminalSectorAssignment
public import Unfoldings.Cap.BoundaryRunTerminalPoint
public import Unfoldings.Roof.RadialComponentFinePath
public import Unfoldings.Cap.ClosedParentPathBankMatching
public import Unfoldings.Cap.ClosedStripCircleSection
public import Unfoldings.Cap.RadialStripClosedBanks

/-! Closed sections retain strict terminal progress even when they end at a pinch. -/

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

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.ClosedBankCircleSection
    (traces source).value (traces source).center cutoff radius)


include outward footprint deep contacts tails pinches curvature_covered

/-- A strictly late closed section has an actual component-bank parameter at every radius.
The terminal path is matched up to the endpoint; no future active width is required. -/
theorem exists_closed_section_boundary_late_candidate (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (upper : Bool)
    (outer : if upper then
      Set.EqOn (cells (Fin.last n)).val.upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
      else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (facing : if upper then
      Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff)
      else Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point (Set.Icc 0 cutoff))
    (late : (terminals pivot).height < if upper then slice.upperHeight else slice.lowerHeight) :
    let z := if upper then source.val.upper.point slice.upperHeight
      else source.val.lower.point slice.lowerHeight
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
        Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
          origin + (fiveSectorFrame t positive small i).place.symm z =
            AffineMap.lineMap (Q.projectedVertex e.val)
              (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) ∧
          (traces source).outputFrame.symm ((traces source).value z) =
            (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
              else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) ∧
          ‖(if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
              else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
            D.projectedMap Q (origin)‖ = radius := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  have wall : H = frame.enclosingStrip.lower ∨ H = frame.enclosingStrip.upper := by
    cases upper
    · exact Or.inl rfl
    · exact Or.inr rfl
  have agreement : Set.EqOn H.point (cells pivot).val.lower.point
      (Set.Icc (terminals pivot).height cutoff) := by
    cases upper
    · exact B.first_run_lower_tail_on_boundary i (fun k => (cells k).val)
        (fun k => traces (cells k)) contacts terminals pivot highest outer
    · intro h member
      exact (B.last_run_lower_tail_on_boundary i (fun k => (cells k).val)
        (fun k => traces (cells k)) contacts terminals pivot highest outer member).symm
  obtain ⟨leaf, after_leaf, same_start, _, member, unattached⟩ :=
    boundary_terminal_leaf_component R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
      deep H wall agreement
  let c := M.geometricComponent F covered leaf.val
  obtain ⟨_, directions, _⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  have child (j : Fin (R.spanningCompletion.parents.distanceToRoot (terminals pivot).vertex)) :
      Q.projectedVertex (R.completedBankChain (terminals pivot).vertex j).val ∈
        (F.componentTail c).carrier :=
    M.unattached_component_completed_path_positions F covered R (terminals pivot).vertex c
      unattached member j.castSucc
  cases upper
  · have tracking := closed_section_late_lower_tracking R outward D B footprint deep P traces
      cells contacts terminals tails source slice pivot highest facing
    obtain ⟨j, s, physical, value⟩ := B.lower_matches_completed_path_on_closed_interval i
      (terminals pivot).vertex (terminals pivot).on_cuts directions (traces source) (pinches source)
      (terminals pivot).height_bounds.1.le late slice.lower_bounds.2
      (fun h bounds => (tracking h bounds).1) (fun h bounds => (tracking h bounds).2)
      slice.lowerHeight ⟨late.le, le_rfl⟩
    have matching : (traces source).outputFrame.symm
        ((traces source).value (source.val.lower.point slice.lowerHeight)) =
          R.parentEntrancePoint (R.completedDevelopment D)
            (R.completedBankChain (terminals pivot).vertex j) (1 - (s : ℝ)) := by
      rw [value]
      exact (B.sectorFrame i).symm_apply_apply _
    refine ⟨c, member, unattached, R.completedBankChain (terminals pivot).vertex j, child j, s,
      physical.trans (R.completedRootPath_point_bankChain _ j s), matching, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← matching, (traces source).outputFrame_symm_source_distance]
    exact slice.lower_radius
  · have tracking := closed_section_late_upper_tracking R outward D B footprint deep P traces
      cells contacts terminals tails source slice pivot highest facing
    obtain ⟨j, s, physical, value⟩ := B.upper_matches_completed_path_on_closed_interval i
      (terminals pivot).vertex (terminals pivot).on_cuts directions (traces source) (pinches source)
      (terminals pivot).height_bounds.1.le late slice.upper_bounds.2
      (fun h bounds => (tracking h bounds).1) (fun h bounds => (tracking h bounds).2)
      slice.upperHeight ⟨late.le, le_rfl⟩
    have matching : (traces source).outputFrame.symm
        ((traces source).value (source.val.upper.point slice.upperHeight)) =
          R.parentExitPoint (R.completedDevelopment D)
            (R.completedBankChain (terminals pivot).vertex j) (1 - (s : ℝ)) := by
      rw [value]
      exact (B.sectorFrame i).symm_apply_apply _
    refine ⟨c, member, unattached, R.completedBankChain (terminals pivot).vertex j, child j, s,
      physical.trans (R.completedRootPath_point_bankChain _ j s), matching, ?_⟩
    simp only [↓reduceIte]
    rw [← matching, (traces source).outputFrame_symm_source_distance]
    exact slice.upper_radius

end Unfoldings.ConvexRoof.SectorForest
