module

public import Unfoldings.Cap.TerminalRecordStep
public import Unfoldings.Geometry.StripBankContacts
public import Unfoldings.Topology.FiniteRecordProgress

/-! Actual terminal-copy progress propagates through arbitrary runs of disappearing strips. -/

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

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells tails

/-- A higher terminal reached after skipping only lower terminals increases
the actual horizontal terminal coordinate. Iterate to the first maximum. -/
theorem terminal_re_le_at_first_maximum_of_contacts (i j : Fin (n + 1)) (ordered : i ≤ j)
    (highest : ∀ k : Fin (n + 1), i ≤ k → k < j →
      (terminals k).height < (terminals j).height) :
    ((traces (cells i)).value ((cells i).val.lower.point (terminals i).height)).re ≤
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).re := by
  apply finite_record_increases_to_first_maximum (fun k => (terminals k).height)
    (fun k => ((traces (cells k)).value ((cells k).val.lower.point (terminals k).height)).re)
    _ i j ordered highest
  intro a b before rises previous
  apply terminal_re_le_of_lower_tail_agreement R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches
    (cells a) (cells b) (terminals a) (terminals b) rises.le (tails a) (ordered_cells a b before)
  intro h member
  have collapsed (k : Fin (n + 1)) (after_a : a ≤ k) (before_b : k < b) :
      (cells k).val.lower.coordinate h = (cells k).val.upper.coordinate h := by
    have lower_height : (terminals k).height ≤ (terminals a).height := by
      by_cases same : k = a
      · rw [same]
      · exact previous k (lt_of_le_of_ne after_a (Ne.symm same)) before_b
    exact (terminals k).merged h
      ⟨lower_height.trans member.1, member.2.trans (terminals b).height_bounds.2.le⟩
  have coordinates := MonotoneStrip.lower_coordinates_eq_between_of_contacts
    (fun k => (cells k).val) (fun k => congrArg Complex.re
      (contacts k ⟨(terminals a).height_bounds.1.le.trans member.1,
        member.2.trans (terminals b).height_bounds.2.le⟩)) a b before.le collapsed
  exact (cells b).val.lower.point_eq_of_same_coordinate (cells a).val.lower coordinates.symm

/-- Processing the same actual run from right to left gives vertical terminal
progress to its last maximum, with all skipped physical banks derived. -/
theorem terminal_im_le_at_last_maximum_of_contacts (i j : Fin (n + 1)) (ordered : j ≤ i)
    (highest : ∀ k : Fin (n + 1), j < k → k ≤ i →
      (terminals k).height < (terminals j).height) :
    ((traces (cells i)).value ((cells i).val.lower.point (terminals i).height)).im ≤
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).im := by
  apply finite_record_increases_to_last_maximum (fun k => (terminals k).height)
    (fun k => ((traces (cells k)).value ((cells k).val.lower.point (terminals k).height)).im)
    _ i j ordered highest
  intro a b before rises previous
  apply terminal_im_le_of_upper_tail_agreement R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches
    (cells a) (cells b) (terminals a) (terminals b) rises.le (tails a) (ordered_cells b a before)
  intro h member
  have collapsed (k : Fin (n + 1)) (after_b : b < k) (before_a : k ≤ a) :
      (cells k).val.lower.coordinate h = (cells k).val.upper.coordinate h := by
    have lower_height : (terminals k).height ≤ (terminals a).height := by
      by_cases same : k = a
      · rw [same]
      · exact previous k after_b (lt_of_le_of_ne before_a same)
    exact (terminals k).merged h
      ⟨lower_height.trans member.1, member.2.trans (terminals b).height_bounds.2.le⟩
  have coordinates := MonotoneStrip.upper_coordinates_eq_between_of_contacts
    (fun k => (cells k).val) (fun k => congrArg Complex.re
      (contacts k ⟨(terminals a).height_bounds.1.le.trans member.1,
        member.2.trans (terminals b).height_bounds.2.le⟩)) b a before.le collapsed
  have source_collapsed := (terminals a).merged h
    ⟨member.1, member.2.trans (terminals b).height_bounds.2.le⟩
  exact (cells b).val.upper.point_eq_of_same_coordinate (cells a).val.lower
    (coordinates.trans source_collapsed.symm)

end Unfoldings.ConvexCap.SectorForest
