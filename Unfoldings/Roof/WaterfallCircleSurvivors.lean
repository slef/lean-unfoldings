module

public import Unfoldings.Roof.WaterfallCircleSurvivorOrder
public import Unfoldings.Topology.OrderedBankPieces
public import Unfoldings.Topology.FilterDisjoint

/-! Pairwise separation of surviving actual strip-circle images in one sector. -/

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
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))

variable {physicalRadius radius : ℝ}

variable {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (margins : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, ∀ z ∈ cell.val.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)

variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
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
/-- All physical empty cells and all cells missing the circle are removed.
Each retained interval has its actual bank endpoints, and their order follows
from the intervening runs rather than a supplied developed-order hypothesis. -/
theorem waterfall_circle_survivors_pairwise_disjoint :
    ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).Pairwise
      (fun first last => Disjoint
        ((traces first).value '' first.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces first).center‖ = radius})
        ((traces last).value '' last.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces last).center‖ = radius})) := by
  classical
  let meets := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces cell).center‖ = radius}).Nonempty
  let keep := fun cell => decide (meets cell)
  let survivors := (P.nonemptyCells cutoff).filter keep
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  let slices := fun cell (meet : meets cell) => Classical.choice
    ((traces cell).circle_slice close_margin (margins cell) radius_positive far meet)
  have survivor_meets {cell} (member : cell ∈ survivors) : meets cell :=
    of_decide_eq_true (List.mem_filter.mp member).2
  have ordered := waterfall_circle_survivor_bank_order R outward D B leaf_vertices footprint
    deep P traces curvature_covered budget nonnegative small_error linear_error pinches provenance
    represented leaf_coherent numerical margins radius_positive far outside all_tails continuations
    all_outside_empty slices
  apply List.Pairwise.imp_of_mem _ ordered
  intro a b member_a member_b gap
  have meet_a := survivor_meets member_a
  have meet_b := survivor_meets member_b
  have first_order := (traces a).bank_circle_order nonnegative small_error numerical linear_error
    (margins a) radius_positive (slices a meet_a).lower_closed (slices a meet_a).upper_closed
    (slices a meet_a).lower_radius (slices a meet_a).upper_radius (slices a meet_a).distinct
  have last_order := (traces b).bank_circle_order nonnegative small_error numerical linear_error
    (margins b) radius_positive (slices b meet_b).lower_closed (slices b meet_b).upper_closed
    (slices b meet_b).lower_radius (slices b meet_b).upper_radius (slices b meet_b).distinct
  apply (slices a meet_a).disjoint_circle_images_of_bank_order (slices b meet_b)
    first_order.1 last_order.1
  · simpa only [ConvexCap.RadialCutForest.RadialStripTraceData.center] using gap meet_a meet_b
  · rintro z ⟨p, member, rfl⟩
    exact (traces a).strict_quadrant_of_margin close_margin (margins a) member

/-- Reinsert both kinds of empty entries. The conclusion concerns every cell
of the original waterfall subdivision, without any survivor-list hypothesis. -/
theorem waterfall_circle_images_pairwise_disjoint :
    P.cells.attach.Pairwise (fun first last => Disjoint
      ((traces first).value '' first.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces first).center‖ = radius})
      ((traces last).value '' last.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces last).center‖ = radius})) := by
  classical
  let images := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    (traces cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces cell).center‖ = radius}
  have surviving := waterfall_circle_survivors_pairwise_disjoint R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    provenance represented leaf_coherent numerical margins radius_positive far outside all_tails
    continuations all_outside_empty
  have physical : (P.nonemptyCells cutoff).Pairwise (fun a b => Disjoint (images a) (images b)) :=
    pairwise_disjoint_of_filter images (fun cell => decide (images cell).Nonempty)
      (P.nonemptyCells cutoff) surviving (fun cell _ removed =>
        Set.not_nonempty_iff_eq_empty.mp (of_decide_eq_false removed))
  apply pairwise_disjoint_of_filter images
    (fun cell => decide (cell.val.openSlab 0 cutoff).Nonempty) P.cells.attach physical
  intro cell _ removed
  have empty : cell.val.openSlab 0 cutoff = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp (of_decide_eq_false removed)
  simp only [images, empty, Set.image_empty, Set.empty_inter]

end Unfoldings.ConvexRoof.SectorForest
