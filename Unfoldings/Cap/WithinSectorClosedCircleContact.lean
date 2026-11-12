module

public import Unfoldings.Cap.WaterfallClosedCircleContacts
public import Unfoldings.Cap.WaterfallCirclePhysicalOrder

/-! Actual within-sector closed circle contacts identify one physical strip coordinate. -/

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
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)

variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    (traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius))
  (all_outside_empty : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    radius ∉ (traces cell).emptyCircleExceptions)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent numerical margins
  radius_positive far outside all_tails continuations all_outside_empty

open Classical in
theorem waterfall_within_sector_closed_circle_physical_contact
    (a b : {S : MonotoneStrip // S ∈ P.cells})
    (physical_order : List.Sublist [a, b] P.cells.attach)
    {x y : ℂ} (first : x ∈ closure (a.val.openSlab 0 cutoff))
    (last : y ∈ closure (b.val.openSlab 0 cutoff))
    (size : ‖(traces a).value x - (traces a).center‖ = radius)
    (same : (traces a).outputFrame.symm ((traces a).value x) =
      (traces b).outputFrame.symm ((traces b).value y)) : x = y := by
  classical
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have other_size : ‖(traces b).value y - (traces b).center‖ = radius := by
    rw [← (traces b).outputFrame_symm_source_distance, ← same,
      (traces a).outputFrame_symm_source_distance]
    exact size
  let meets := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces cell).center‖ = radius}).Nonempty
  have meet_a : meets a := (traces a).circle_nonempty_of_approached_point_off_vertexRadii
    (pinches a) radius_positive far outside first size
  have meet_b : meets b := (traces b).circle_nonempty_of_approached_point_off_vertexRadii
    (pinches b) radius_positive far outside last other_size
  let slices := fun cell (meet : meets cell) =>
    Classical.choice ((traces cell).circle_slice close_margin (margins cell)
      radius_positive far meet)
  have classified := waterfall_closed_circle_survivor_contacts R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    provenance represented leaf_coherent numerical margins radius_positive far outside
    all_tails continuations all_outside_empty slices
  have physical_ordered := waterfall_circle_survivor_physical_contacts R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    provenance represented leaf_coherent numerical margins radius_positive far outside
    all_tails continuations all_outside_empty slices
  have nonempty_a : (a.val.openSlab 0 cutoff).Nonempty := closure_nonempty_iff.mp ⟨x, first⟩
  have nonempty_b : (b.val.openSlab 0 cutoff).Nonempty := closure_nonempty_iff.mp ⟨y, last⟩
  have physical_filtered : List.Sublist [a, b] (P.nonemptyCells cutoff) := by
    simpa [MonotoneStrip.Subdivision.nonemptyCells, nonempty_a, nonempty_b] using
      physical_order.filter (fun cell => decide (cell.val.openSlab 0 cutoff).Nonempty)
  have retained : List.Sublist [a, b] ((P.nonemptyCells cutoff).filter
      (fun cell => decide (meets cell))) := by
    simpa [meet_a, meet_b] using physical_filtered.filter (fun cell => decide (meets cell))
  have pair := classified.sublist retained
  have contact := (List.pairwise_cons.mp pair).1 b (by simp)
  have physical_pair := physical_ordered.sublist retained
  have physical_contact := (List.pairwise_cons.mp physical_pair).1 b (by simp)
  have points := contact meet_a meet_b first last size same
  have values : (traces a).value (a.val.upper.point (slices a meet_a).upperHeight) =
      (traces b).value (b.val.lower.point (slices b meet_b).lowerHeight) := by
    change (traces a).outputFrame.symm ((traces a).value x) =
      (traces a).outputFrame.symm ((traces b).value y) at same
    have equal := (traces a).outputFrame.symm.injective same
    exact (congrArg (traces a).value points.1).symm.trans
      (equal.trans (congrArg (traces b).value points.2))
  exact points.1.trans ((physical_contact meet_a meet_b values).trans points.2.symm)

end Unfoldings.ConvexCap.SectorForest
