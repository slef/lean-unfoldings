module

public import Unfoldings.Cap.WaterfallCircleSurvivorOrder
public import Unfoldings.Cap.ClosedSectionBankOrderLimit
public import Unfoldings.Cap.ClosedCircleAbsenceBounds
public import Unfoldings.Topology.OrderedBankPieces
public import Unfoldings.Topology.FilterDisjoint

/-! Full waterfall bank order includes closed-only sections and all vertex radii. -/

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

variable {physicalRadius radius : ℝ}

variable {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (margins : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, ∀ z ∈ cell.val.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)


variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuations : ∀ r ∈ Set.Ioo 0 radius,
    ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      r ∉ (traces cell).emptyCircleExceptions →
      (traces cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces cell).center‖ = r} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius r))


include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent numerical margins
  radius_positive far all_tails continuations

/-- All physically ordered approached sections have weakly ordered facing banks.
Compactness fills every exceptional radius; sections with a single pinch are retained. -/
theorem waterfall_closed_section_facing_bank_order
    (a b : {S : MonotoneStrip // S ∈ P.cells})
    (physical_order : List.Sublist [a, b] P.cells.attach)
    (first_section : a.val.ClosedBankCircleSection
      (traces a).value (traces a).center cutoff radius)
    (last_section : b.val.ClosedBankCircleSection
      (traces b).value (traces b).center cutoff radius) :
    ((traces a).value (a.val.upper.point first_section.upperHeight) - (traces a).center).re ≤
      ((traces b).value (b.val.lower.point last_section.lowerHeight) - (traces b).center).re := by
  classical
  let : Finite {S : MonotoneStrip // S ∈ P.cells} := P.cells.finite_toSet.to_subtype
  let exception := D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small ∪
    ⋃ cell : {S : MonotoneStrip // S ∈ P.cells}, (traces cell).emptyCircleExceptions
  have finite : exception.Finite :=
    (D.finite_fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
      positive small).union (Set.finite_iUnion fun cell =>
        (traces cell).finite_emptyCircleExceptions)
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  apply (traces a).closed_section_facing_order_of_regular (traces b)
    first_section last_section close_margin (margins a) (margins b)
    radius_positive far finite
  intro r bounds outside
  have far_r := bounds.2.trans far
  have outside_vertices : r ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small :=
    fun member => outside (Or.inl member)
  have outside_empty (cell : {S : MonotoneStrip // S ∈ P.cells}) :
      r ∉ (traces cell).emptyCircleExceptions :=
    fun member => outside (Or.inr (Set.mem_iUnion.mpr ⟨cell, member⟩))
  have first_approached := (traces a).closed_circle_point_mem_closure_openSlab
    radius_positive far first_section.upper_closed first_section.upper_radius
  have last_approached := (traces b).closed_circle_point_mem_closure_openSlab
    radius_positive far last_section.lower_closed last_section.lower_radius
  obtain ⟨_, ⟨x, first_closed, rfl⟩, first_size⟩ :=
    (traces a).closed_circle_nonempty_of_norm_ge bounds.1 far_r first_approached
      (by rw [first_section.upper_radius]; exact bounds.2.le)
  obtain ⟨_, ⟨y, last_closed, rfl⟩, last_size⟩ :=
    (traces b).closed_circle_nonempty_of_norm_ge bounds.1 far_r last_approached
      (by rw [last_section.lower_radius]; exact bounds.2.le)
  let meets := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces cell).center‖ = r}).Nonempty
  have meet_a : meets a := (traces a).circle_nonempty_of_approached_point_off_vertexRadii
    (pinches a) bounds.1 far_r outside_vertices first_closed first_size
  have meet_b : meets b := (traces b).circle_nonempty_of_approached_point_off_vertexRadii
    (pinches b) bounds.1 far_r outside_vertices last_closed last_size
  let slices := fun cell (meet : meets cell) =>
    Classical.choice ((traces cell).circle_slice close_margin (margins cell)
      bounds.1 far_r meet)
  have ordered := waterfall_circle_survivor_bank_order R outward D B leaf_vertices footprint
    deep P traces curvature_covered budget nonnegative small_error linear_error pinches provenance
    represented leaf_coherent numerical margins bounds.1 far_r outside_vertices all_tails
    (fun cell => continuations r bounds cell (outside_empty cell)) outside_empty slices
  have nonempty_a : (a.val.openSlab 0 cutoff).Nonempty :=
    closure_nonempty_iff.mp ⟨x, first_closed⟩
  have nonempty_b : (b.val.openSlab 0 cutoff).Nonempty :=
    closure_nonempty_iff.mp ⟨y, last_closed⟩
  have physical_filtered : List.Sublist [a, b] (P.nonemptyCells cutoff) := by
    simpa [MonotoneStrip.Subdivision.nonemptyCells, nonempty_a, nonempty_b] using
      physical_order.filter (fun cell => decide (cell.val.openSlab 0 cutoff).Nonempty)
  have retained : List.Sublist [a, b] ((P.nonemptyCells cutoff).filter
      (fun cell => decide (meets cell))) := by
    simpa [meet_a, meet_b] using physical_filtered.filter (fun cell => decide (meets cell))
  have pair := ordered.sublist retained
  exact ⟨slices a meet_a, slices b meet_b,
    (List.pairwise_cons.mp pair).1 b (by simp) meet_a meet_b⟩

end Unfoldings.ConvexCap.SectorForest
