module

public import Unfoldings.Cap.BoundaryRunSourceBankCandidate
public import Unfoldings.Cap.BoundaryRunNeighborCircleCandidate
public import Unfoldings.Cap.BoundaryRunSharedMargins
public import Unfoldings.Cap.ComponentBankCircleSeparation

/-! Actual neighboring circle images are disjoint across one disappearing boundary run. -/

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
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (outside_empty : ∀ k, radius ∉ (traces (cells k)).emptyCircleExceptions)
  (empty : ∀ k, (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells tails provenance represented
  leaf_coherent radius_positive far outside outside_empty empty

theorem circle_images_disjoint_across_upper_boundary_run
    (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (last_maximum : ∀ k, pivot < k → (terminals k).height < (terminals pivot).height)
    (physical_room : 2 * physicalRadius < cutoff)
    (source_order : ∀ k, List.Sublist [source, cells k] P.cells.attach)
    (facing : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (separator : source.val.upper ∈ P.separators)
    (outer : Set.EqOn (cells (Fin.last n)).val.upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (j : FiveSector) (shared : fiveSectorFirst t i = fiveSectorLast t j)
    (all_leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {T : MonotoneStrip}
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (neighbor_outer : Set.EqOn T.lower.point
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff))
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    {μ ν ω : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ source.val.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im)
    (first_order : ((traces source).value (source.val.lower.point slice.lowerHeight) -
        (traces source).center).re <
      ((traces source).value (source.val.upper.point slice.upperHeight) -
        (traces source).center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re) :
    Disjoint ((traces source).outputFrame.symm ''
      ((traces source).value '' source.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces source).center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  have physical_nonnegative : 0 ≤ physicalRadius :=
    (norm_nonneg _).trans (terminals pivot).physical_inside.le
  have physical_bound : physicalRadius ≤ cutoff := by linarith
  obtain ⟨c, terminal_member, unattached, e, child, s, trace_origin, bound, inside⟩ :=
    exists_boundary_run_source_bank_candidate_with_trace R outward D B leaf_vertices footprint deep
      P traces curvature_covered budget nonnegative small_error linear_error pinches cells contacts
      ordered_cells terminals tails provenance represented leaf_coherent source slice
      radius_positive
      far outside outside_empty empty pivot highest physical_bound true last_maximum source_order
      facing separator outer
  obtain ⟨d, other_terminal, _, f, other_child, r, matching, size⟩ :=
    exists_boundary_run_neighbor_circle_candidate R outward D B (fun k => (cells k).val)
      (fun k => traces (cells k)) contacts terminals tails pivot highest footprint deep
      physical_bound
      leaf_vertices all_leaf_coherent true shared outer radius_positive small_error room
      outside_empty
      empty other other_slice neighbor_outer outside
  have same : d = c := F.component_eq_of_pos_scaled_positions lower other_terminal terminal_member
    zero_lt_one (by simp only [one_smul])
  have last_member : Q.projectedVertex f.val ∈ (F.componentTail c).carrier :=
    (congrArg (fun a => (F.componentTail a).carrier) same).subset other_child
  have exit_margins := B.boundary_run_candidate_shared_margins i j true shared
    (fun k => (cells k).val) (fun k => traces (cells k)) contacts terminals pivot highest outer
    positive_margin face_bounds (traces source) slice physical_room radius_positive small_error
    room facing _ trace_origin
  have other_heights := other.circle_slice_heights radius_positive far other_slice
  have entrance_margins := B.circle_shared_bank_margins j i false shared positive_margin
    face_bounds other other_slice radius_positive small_error room
    (neighbor_outer ⟨other_heights.1.1.le, other_heights.1.2.le⟩)
  change other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight)) =
    R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) at matching
  change ∀ a, a = j ∨ a = i →
    0 < (B.sectorFrame a (other.outputFrame.symm
      (other.value (T.lower.point other_slice.lowerHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).re ∧
    0 < (B.sectorFrame a (other.outputFrame.symm
      (other.value (T.lower.point other_slice.lowerHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).im at entrance_margins
  rw [matching] at entrance_margins
  have at_root : (cells pivot).val.lower.point (terminals pivot).height =
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (terminals pivot).height :=
    B.last_run_lower_tail_on_boundary i (fun k => (cells k).val) (fun k => traces (cells k))
      contacts terminals pivot highest outer ⟨le_rfl, (terminals pivot).height_bounds.2.le⟩
  have cones := shared_sector_bank_mem_both_cones positive small i j true shared
    (terminals pivot).height_bounds.1
  have physical : Q.projectedVertex (terminals pivot).vertex - K.projectedVertex origin =
      (fiveSectorFrame t positive small i).place.symm
        ((fiveSectorFrame t positive small i).enclosingStrip.upper.point
          (terminals pivot).height) := by
    rw [← (terminals pivot).physical, add_sub_cancel_left, at_root]
  have first_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t i :=
    (F.componentTail c).position_inDirectionWedge_of_mem terminal_member
      (physical.symm ▸ cones.1) child
  have last_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t j :=
    (F.componentTail c).position_inDirectionWedge_of_mem terminal_member
      (physical.symm ▸ cones.2) child
  have centered : other.value (T.lower.point other_slice.lowerHeight) - other.center =
      B.sectorFrame j (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
        D.projectedMap Q (K.projectedVertex origin)) := by
    have value := congrArg other.outputFrame matching
    rw [LinearIsometryEquiv.apply_symm_apply] at value
    rw [value, other.center_eq_outputFrame, map_sub]
    rfl
  apply M.circle_images_disjoint_of_component_bank_bounds F covered lower R e f c unattached
    child
    last_member positive small outward footprint i j first_inside last_inside curvature_covered D B
    (traces source) other slice other_slice first_order last_order first_error last_error
    first_margin
    last_margin radius_positive budget.le s r inside size.le
  · intro a choice
    exact ⟨exit_margins a choice, entrance_margins a choice.symm⟩
  · exact bound
  · rw [← centered]

theorem circle_images_disjoint_across_lower_boundary_run
    (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (first_maximum : ∀ k, k < pivot → (terminals k).height < (terminals pivot).height)
    (physical_room : 2 * physicalRadius < cutoff)
    (source_order : ∀ k, List.Sublist [cells k, source] P.cells.attach)
    (facing : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff))
    (separator : source.val.lower ∈ P.separators)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (j : FiveSector) (shared : fiveSectorFirst t j = fiveSectorLast t i)
    (all_leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {T : MonotoneStrip}
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (neighbor_outer : Set.EqOn T.upper.point
      (fiveSectorFrame t positive small j).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    {μ ν ω : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ source.val.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im)
    (first_order : ((traces source).value (source.val.lower.point slice.lowerHeight) -
        (traces source).center).re <
      ((traces source).value (source.val.upper.point slice.upperHeight) -
        (traces source).center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re) :
    Disjoint ((traces source).outputFrame.symm ''
      ((traces source).value '' source.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces source).center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  have physical_nonnegative : 0 ≤ physicalRadius :=
    (norm_nonneg _).trans (terminals pivot).physical_inside.le
  have physical_bound : physicalRadius ≤ cutoff := by linarith
  obtain ⟨c, terminal_member, unattached, e, child, s, trace_origin, bound, inside⟩ :=
    exists_boundary_run_source_bank_candidate_with_trace R outward D B leaf_vertices footprint deep
      P traces curvature_covered budget nonnegative small_error linear_error pinches cells contacts
      ordered_cells terminals tails provenance represented leaf_coherent source slice
      radius_positive
      far outside outside_empty empty pivot highest physical_bound false first_maximum source_order
      facing separator outer
  obtain ⟨d, other_terminal, _, f, other_child, r, matching, size⟩ :=
    exists_boundary_run_neighbor_circle_candidate R outward D B (fun k => (cells k).val)
      (fun k => traces (cells k)) contacts terminals tails pivot highest footprint deep
      physical_bound
      leaf_vertices all_leaf_coherent false shared outer radius_positive small_error room
      outside_empty
      empty other other_slice neighbor_outer outside
  have same : d = c := F.component_eq_of_pos_scaled_positions lower other_terminal terminal_member
    zero_lt_one (by simp only [one_smul])
  have last_member : Q.projectedVertex f.val ∈ (F.componentTail c).carrier :=
    (congrArg (fun a => (F.componentTail a).carrier) same).subset other_child
  have entrance_margins := B.boundary_run_candidate_shared_margins i j false shared
    (fun k => (cells k).val) (fun k => traces (cells k)) contacts terminals pivot highest outer
    positive_margin face_bounds (traces source) slice physical_room radius_positive small_error
    room facing _ trace_origin
  have other_heights := other.circle_slice_heights radius_positive far other_slice
  have exit_margins := B.circle_shared_bank_margins j i true shared positive_margin
    face_bounds other other_slice radius_positive small_error room
    (neighbor_outer ⟨other_heights.2.1.le, other_heights.2.2.le⟩)
  change other.outputFrame.symm (other.value (T.upper.point other_slice.upperHeight)) =
    R.parentExitPoint (R.completedDevelopment D) f (1 - (r : ℝ)) at matching
  change ∀ a, a = j ∨ a = i →
    0 < (B.sectorFrame a (other.outputFrame.symm
      (other.value (T.upper.point other_slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).re ∧
    0 < (B.sectorFrame a (other.outputFrame.symm
      (other.value (T.upper.point other_slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).im at exit_margins
  rw [matching] at exit_margins
  have at_root : (cells pivot).val.lower.point (terminals pivot).height =
      (fiveSectorFrame t positive small i).enclosingStrip.lower.point (terminals pivot).height :=
    (B.first_run_lower_tail_on_boundary i (fun k => (cells k).val) (fun k => traces (cells k))
      contacts terminals pivot highest outer ⟨le_rfl, (terminals pivot).height_bounds.2.le⟩).symm
  have cones := shared_sector_bank_mem_both_cones positive small i j false shared
    (terminals pivot).height_bounds.1
  have physical : Q.projectedVertex (terminals pivot).vertex - K.projectedVertex origin =
      (fiveSectorFrame t positive small i).place.symm
        ((fiveSectorFrame t positive small i).enclosingStrip.lower.point
          (terminals pivot).height) := by
    rw [← (terminals pivot).physical, add_sub_cancel_left, at_root]
  have first_inside : Q.projectedVertex f.val - K.projectedVertex origin ∈
      closedFiveSector t j :=
    (F.componentTail c).position_inDirectionWedge_of_mem terminal_member
      (physical.symm ▸ cones.2) last_member
  have last_inside : Q.projectedVertex f.val - K.projectedVertex origin ∈ closedFiveSector t i :=
    (F.componentTail c).position_inDirectionWedge_of_mem terminal_member
      (physical.symm ▸ cones.1) last_member
  have centered : other.value (T.upper.point other_slice.upperHeight) - other.center =
      B.sectorFrame j (R.parentExitPoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
        D.projectedMap Q (K.projectedVertex origin)) := by
    have value := congrArg other.outputFrame matching
    rw [LinearIsometryEquiv.apply_symm_apply] at value
    rw [value, other.center_eq_outputFrame, map_sub]
    rfl
  apply Disjoint.symm
  apply M.circle_images_disjoint_of_component_bank_bounds F covered lower R f e c unattached
    last_member child positive small outward footprint j i first_inside last_inside
    curvature_covered
    D B other (traces source) other_slice slice last_order first_order last_error first_error
    last_margin first_margin radius_positive budget.le r s size.le inside
  · intro a choice
    exact ⟨exit_margins a choice, entrance_margins a choice.symm⟩
  · rw [← centered]
  · exact bound

end Unfoldings.ConvexCap.SectorForest

