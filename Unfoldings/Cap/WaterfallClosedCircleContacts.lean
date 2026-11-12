module

public import Unfoldings.Cap.WaterfallCircleSurvivorBanks
public import Unfoldings.Cap.ClosedStripCircleContact
public import Unfoldings.Cap.ClosedCirclePinches

/-! Every ordered actual waterfall survivor has only its facing bank as a closed contact. -/

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
/-- The complete finite waterfall order controls closed image contacts, rather than
only disjointness of open images. Both physical preimage coordinates are identified. -/
theorem waterfall_closed_circle_survivor_contacts
    (slices : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty →
      cell.val.BankCircleSlice (traces cell).value (traces cell).center cutoff radius) :
    ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).Pairwise
      (fun a b => ∀ meet_a meet_b, ∀ {x y : ℂ},
        x ∈ closure (a.val.openSlab 0 cutoff) → y ∈ closure (b.val.openSlab 0 cutoff) →
        ‖(traces a).value x - (traces a).center‖ = radius →
        (traces a).outputFrame.symm ((traces a).value x) =
          (traces b).outputFrame.symm ((traces b).value y) →
        x = a.val.upper.point (slices a meet_a).upperHeight ∧
          y = b.val.lower.point (slices b meet_b).lowerHeight) := by
  have ordered := waterfall_circle_survivor_banks_ordered R outward D B leaf_vertices footprint
    deep P traces curvature_covered budget nonnegative small_error linear_error pinches provenance
    represented leaf_coherent numerical margins radius_positive far outside all_tails
    continuations all_outside_empty slices
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  apply List.Pairwise.imp_of_mem _ ordered
  intro a b _ _ gap meet_a meet_b x y first last size same
  have first_order := (traces a).bank_circle_order nonnegative small_error numerical linear_error
    (margins a) radius_positive (slices a meet_a).lower_closed (slices a meet_a).upper_closed
    (slices a meet_a).lower_radius (slices a meet_a).upper_radius (slices a meet_a).distinct
  have last_order := (traces b).bank_circle_order nonnegative small_error numerical linear_error
    (margins b) radius_positive (slices b meet_b).lower_closed (slices b meet_b).upper_closed
    (slices b meet_b).lower_radius (slices b meet_b).upper_radius (slices b meet_b).distinct
  exact B.closed_circle_contact_preimages_eq_bank_points i (traces a) (traces b)
    (slices a meet_a) (slices b meet_b) first_order.1 last_order.1 close_margin close_margin
    (margins a) (margins b) radius_positive far (gap meet_a meet_b).1 first last size same

open Classical in
/-- Any closed contact in physical cell order is a pair of facing bank points.
The two circle survivors and their slices are constructed from the contact itself. -/
theorem waterfall_closed_circle_contact
    (a b : {S : MonotoneStrip // S ∈ P.cells})
    (physical_order : List.Sublist [a, b] P.cells.attach)
    {x y : ℂ} (first : x ∈ closure (a.val.openSlab 0 cutoff))
    (last : y ∈ closure (b.val.openSlab 0 cutoff))
    (size : ‖(traces a).value x - (traces a).center‖ = radius)
    (same : (traces a).outputFrame.symm ((traces a).value x) =
      (traces b).outputFrame.symm ((traces b).value y)) :
    ∃ first_slice : a.val.BankCircleSlice (traces a).value (traces a).center cutoff radius,
      ∃ last_slice : b.val.BankCircleSlice (traces b).value (traces b).center cutoff radius,
        x = a.val.upper.point first_slice.upperHeight ∧
          y = b.val.lower.point last_slice.lowerHeight := by
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
  exact ⟨slices a meet_a, slices b meet_b, contact meet_a meet_b first last size same⟩

end Unfoldings.ConvexCap.SectorForest
