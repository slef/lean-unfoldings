module

public import Unfoldings.Cap.TerminalRunClosedLateBounds
public import Unfoldings.Cap.ClosedParentPathBankContact

/-! Late contacts across an actual collapsed strip run identify physical points at every radius. -/

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
  (first last : {S : MonotoneStrip // S ∈ P.cells})
  (first_slice : first.val.BankCircleSlice (traces first).value (traces first).center cutoff radius)
  (last_slice : last.val.BankCircleSlice (traces last).value (traces last).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include outward footprint deep curvature_covered budget pinches contacts tails radius_positive far

/-- Closed matching of both late banks handles every vertex radius and branch endpoint. -/
theorem closed_circle_contact_after_empty_strip_run_same_point
    (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (first_wall : Set.EqOn first.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (last_wall : Set.EqOn last.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff))
    (first_after : (terminals pivot).height ≤ first_slice.upperHeight)
    (last_after : (terminals pivot).height ≤ last_slice.lowerHeight)
    (same : (traces first).value (first.val.upper.point first_slice.upperHeight) =
      (traces last).value (last.val.lower.point last_slice.lowerHeight)) :
    (fiveSectorFrame t positive small i).place.symm (first.val.upper.point
      first_slice.upperHeight) =
      (fiveSectorFrame t positive small i).place.symm (last.val.lower.point
        last_slice.lowerHeight) := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨first_end, first_before, first_cutoff, first_closed, first_tracked⟩ :=
    exists_late_run_upper_tracking_interval R outward D B footprint deep P traces
      cells contacts terminals tails first first_slice radius_positive far pivot highest first_wall
  obtain ⟨last_end, last_before, last_cutoff, last_closed, last_tracked⟩ :=
    exists_late_run_lower_tracking_interval R outward D B footprint deep P traces
      cells contacts terminals tails last last_slice radius_positive far pivot highest last_wall
  exact B.closed_parent_path_bank_contact_same_point i (traces first) (traces last)
    (terminals pivot).vertex (terminals pivot).on_cuts directions sectors budget
    (pinches first) (pinches last)
    (terminals pivot).height_bounds.1.le (first_after.trans_lt first_before) first_cutoff.le
    (terminals pivot).height_bounds.1.le (last_after.trans_lt last_before) last_cutoff.le
    first_closed last_closed first_tracked last_tracked
    ⟨first_after, first_before.le⟩ ⟨last_after, last_before.le⟩ same

end Unfoldings.ConvexCap.SectorForest
