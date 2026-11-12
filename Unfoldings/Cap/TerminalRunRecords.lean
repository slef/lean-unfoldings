module

public import Unfoldings.Cap.TerminalRecordStep
public import Unfoldings.Geometry.StripBankChain
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
  (adjacent : ∀ j : Fin n, (cells j.castSucc).val.upper = (cells j.succ).val.lower)
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches adjacent ordered_cells tails

/-- A higher terminal reached after skipping only lower terminals increases
the actual horizontal terminal coordinate. Iterate to the first maximum. -/
theorem terminal_re_le_at_first_maximum (i j : Fin (n + 1)) (ordered : i ≤ j)
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
  have coordinates := MonotoneStrip.lower_coordinates_eq_between
    (fun k => (cells k).val) adjacent a b before.le collapsed
  exact (cells b).val.lower.point_eq_of_same_coordinate (cells a).val.lower coordinates.symm

/-- Processing the same actual run from right to left gives vertical terminal
progress to its last maximum, with all skipped physical banks derived. -/
theorem terminal_im_le_at_last_maximum (i j : Fin (n + 1)) (ordered : j ≤ i)
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
  have coordinates := MonotoneStrip.upper_coordinates_eq_between
    (fun k => (cells k).val) adjacent b a before.le collapsed
  have source_collapsed := (terminals a).merged h
    ⟨member.1, member.2.trans (terminals b).height_bounds.2.le⟩
  exact (cells b).val.upper.point_eq_of_same_coordinate (cells a).val.lower
    (coordinates.trans source_collapsed.symm)

omit adjacent tails in
/-- Tied terminal heights retain the actual subdivision order of their copies.
The first maximum's imaginary coordinate dominates the last maximum's. -/
theorem terminal_copies_order_at_equal_height (i j : Fin (n + 1)) (ordered : i ≤ j)
    (same_height : (terminals i).height = (terminals j).height) :
    (((traces (cells i)).value ((cells i).val.lower.point (terminals i).height)).re ≤
        ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).re) ∧
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).im ≤
        ((traces (cells i)).value ((cells i).val.lower.point (terminals i).height)).im := by
  by_cases same : i = j
  · subst j
    exact ⟨le_rfl, le_rfl⟩
  have before : i < j := lt_of_le_of_ne ordered same
  have first_included : (cells i).val.openSlab 0 cutoff ⊆ (traces (cells i)).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_included : (cells j).val.openSlab 0 cutoff ⊆ (traces (cells j)).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_closed := closure_mono first_included (terminals i).upper_closed
  have last_closed : (cells j).val.lower.point (terminals i).height ∈
      closure (traces (cells j)).strictDomain := by
    rw [same_height]
    exact closure_mono last_included (terminals j).lower_closed
  have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches (cells i) (cells j)
    (ordered_cells i j before) (terminals i).height_bounds first_closed last_closed
  have first_equal := (cells i).val.lower.point_eq_of_same_coordinate (cells i).val.upper
    ((terminals i).merged (terminals i).height ⟨le_rfl, (terminals i).height_bounds.2.le⟩)
  have last_value : (traces (cells j)).value ((cells j).val.lower.point (terminals i).height) =
      (traces (cells j)).value ((cells j).val.lower.point (terminals j).height) := by
    rw [same_height]
  rw [← first_equal, last_value] at gap
  exact gap

end Unfoldings.ConvexCap.SectorForest

