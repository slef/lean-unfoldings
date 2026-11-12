module

public import Unfoldings.Cap.BoundaryRunApproachedBanks
public import Unfoldings.Cap.EnclosingBankSegments
public import Unfoldings.Cap.ClosedParentBankMatching
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.CompletedChartComparisonPoints

/-! Extreme terminal contour copies are the named banks of an actual incoming fine edge. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {ε cutoff physicalRadius radius : ℝ} {n : ℕ}
  (cells : Fin (n + 1) → MonotoneStrip)
  (traces : ∀ j, N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i (cells j) ε cutoff)
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
    (cells j.succ).lower.point (Set.Icc 0 cutoff))
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces j) physicalRadius radius)
  (pivot : Fin (n + 1))
  (pinches : (cells pivot).ApproachedPinchesIn
    (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
      (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
  (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
  (on_cuts : K.projectedVertex e.val ∈ cuts)
  (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
    K.projectedVertex e.val ∈ closedFiveSector t i)
  (parent : N.spanningCompletion.parents.parent e.val = (terminals pivot).vertex)
  {child_height : ℝ} (child_nonnegative : 0 ≤ child_height)
  (child_before : child_height < (terminals pivot).height)

theorem run_terminal_vertex_not_completed_root
    (deep : Metric.closedBall source physicalRadius ⊆ interior K.footprint) :
    (terminals pivot).vertex ∉ N.spanningCompletion.parents.roots := by
  have internal : K.projectedVertex (terminals pivot).vertex ∈ interior K.footprint := by
    apply deep
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (terminals pivot).physical_inside.le
  have not_boundary := (K.projectedVertex_mem_interior_iff (terminals pivot).vertex).mp internal
  intro root
  exact not_boundary ((Set.ext_iff.mp N.spanningCompletion.roots_eq _).mp root)

include contacts pinches on_cuts direction parent child_nonnegative child_before

theorem first_run_maximum_matches_incoming_entrance
    (strict_before : ∀ j, j < pivot → (terminals j).height < (terminals pivot).height)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff))
    (child_bank : source + (fiveSectorFrame t positive small i).place.symm
      ((fiveSectorFrame t positive small i).enclosingStrip.lower.point child_height) =
        K.projectedVertex e.val) :
    (traces pivot).value ((cells pivot).lower.point (terminals pivot).height) =
      B.sectorFrame i (N.parentEntrancePoint (N.completedDevelopment D) e 0) := by
  let frame := fiveSectorFrame t positive small i
  obtain ⟨a, bounds, agreement⟩ := B.first_run_maximum_approaches_lower_bank i cells traces
    contacts terminals pivot strict_before outer
  let b := max a child_height
  have start : 0 ≤ b := bounds.1.le.trans (le_max_left _ _)
  have ordered : b < (terminals pivot).height := max_lt bounds.2 child_before
  have included : (cells pivot).openSlab 0 cutoff ⊆ (traces pivot).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have endpoint := closure_mono included (terminals pivot).lower_closed
  have closed (h : ℝ) (member : h ∈ Set.Ioo b (terminals pivot).height) :
      (cells pivot).lower.point h ∈ closure (traces pivot).strictDomain := by
    apply (traces pivot).lower_bank_closed_before endpoint
    rw [(cells pivot).lower.point_height]
    exact ⟨start.trans member.1.le, member.2.le⟩
  have parent_bank : source + frame.place.symm
      (frame.enclosingStrip.lower.point (terminals pivot).height) =
      K.projectedVertex (N.spanningCompletion.parents.parent e.val) := by
    rw [agreement ⟨bounds.2.le, le_rfl⟩, parent]
    exact (terminals pivot).physical
  have tracked (h : ℝ) (member : h ∈ Set.Ioo b (terminals pivot).height) :
      source + frame.place.symm ((cells pivot).lower.point h) ∈
        segment ℝ (K.projectedVertex e.val)
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) := by
    have position := frame.enclosingStrip_lower_physical_mem_segment source child_nonnegative
      ⟨(le_max_right a child_height).trans member.1.le, member.2.le⟩
    rw [child_bank, parent_bank] at position
    rw [← agreement ⟨(le_max_left a child_height).trans member.1.le, member.2.le⟩]
    exact position
  have matched := (traces pivot).lower_matches_parent_on_closed_interval pinches e on_cuts
    direction start ordered (terminals pivot).height_bounds.2.le closed tracked
    (terminals pivot).height ⟨ordered.le, le_rfl⟩
  rw [B.centered_coordinate_eq_sectorFrame, (terminals pivot).physical] at matched
  rw [N.parentEntrancePoint_eq_projectedPlacement, AffineMap.lineMap_apply_zero, parent]
  exact matched

theorem last_run_maximum_matches_incoming_exit
    (strict_after : ∀ j, pivot < j → (terminals j).height < (terminals pivot).height)
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (child_bank : source + (fiveSectorFrame t positive small i).place.symm
      ((fiveSectorFrame t positive small i).enclosingStrip.upper.point child_height) =
        K.projectedVertex e.val) :
    (traces pivot).value ((cells pivot).lower.point (terminals pivot).height) =
      B.sectorFrame i (N.parentExitPoint (N.completedDevelopment D) e 0) := by
  let frame := fiveSectorFrame t positive small i
  obtain ⟨a, bounds, agreement⟩ := B.last_run_maximum_approaches_upper_bank i cells traces
    contacts terminals pivot strict_after outer
  let b := max a child_height
  have start : 0 ≤ b := bounds.1.le.trans (le_max_left _ _)
  have ordered : b < (terminals pivot).height := max_lt bounds.2 child_before
  have included : (cells pivot).openSlab 0 cutoff ⊆ (traces pivot).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have endpoint := closure_mono included (terminals pivot).upper_closed
  have merged : (cells pivot).lower.point (terminals pivot).height =
      (cells pivot).upper.point (terminals pivot).height :=
    (cells pivot).lower.point_eq_of_same_coordinate (cells pivot).upper
      ((terminals pivot).merged _ ⟨le_rfl, (terminals pivot).height_bounds.2.le⟩)
  have closed (h : ℝ) (member : h ∈ Set.Ioo b (terminals pivot).height) :
      (cells pivot).upper.point h ∈ closure (traces pivot).strictDomain := by
    apply (traces pivot).upper_bank_closed_before endpoint
    rw [(cells pivot).upper.point_height]
    exact ⟨start.trans member.1.le, member.2.le⟩
  have parent_bank : source + frame.place.symm
      (frame.enclosingStrip.upper.point (terminals pivot).height) =
      K.projectedVertex (N.spanningCompletion.parents.parent e.val) := by
    rw [← agreement ⟨bounds.2.le, le_rfl⟩, ← merged, parent]
    exact (terminals pivot).physical
  have tracked (h : ℝ) (member : h ∈ Set.Ioo b (terminals pivot).height) :
      source + frame.place.symm ((cells pivot).upper.point h) ∈
        segment ℝ (K.projectedVertex e.val)
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) := by
    have position := frame.enclosingStrip_upper_physical_mem_segment source child_nonnegative
      ⟨(le_max_right a child_height).trans member.1.le, member.2.le⟩
    rw [child_bank, parent_bank] at position
    rw [agreement ⟨(le_max_left a child_height).trans member.1.le, member.2.le⟩]
    exact position
  have matched := (traces pivot).upper_matches_parent_on_closed_interval pinches e on_cuts
    direction start ordered (terminals pivot).height_bounds.2.le closed tracked
    (terminals pivot).height ⟨ordered.le, le_rfl⟩
  rw [B.centered_coordinate_eq_sectorFrame, ← merged, (terminals pivot).physical] at matched
  rw [N.parentExitPoint_eq_projectedPlacement, AffineMap.lineMap_apply_zero, parent]
  exact matched

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
