module

public import Unfoldings.Roof.WaterfallClosedSectionOrder
public import Unfoldings.Roof.WaterfallClosedSectionPhysicalOrder
public import Unfoldings.Cap.ClosedSectionCircleContact
public import Unfoldings.Cap.RadialClosedCircleSections
public import Unfoldings.Cap.ClosedCircleSectionLexOrder

/-! Full survivor order retains physical point equality whenever developed bank values coincide. -/

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


variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    (traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius))
  (regular_continuations : ∀ r ∈ Set.Ioo 0 radius,
    ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      r ∉ (traces cell).emptyCircleExceptions →
      (traces cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces cell).center‖ = r} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius r))
  (enclosing_margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)


include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent numerical margins
  radius_positive far all_tails continuations regular_continuations enclosing_margin

/-- Every actual within-sector closed contact has one physical preimage, at every radius. -/
theorem waterfall_within_sector_all_radius_physical_contact
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
    ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
      {z | ‖z - (traces cell).center‖ = radius}).Nonempty
  have meet_a : meets a := ⟨_, ⟨x, first, rfl⟩, size⟩
  have meet_b : meets b := ⟨_, ⟨y, last, rfl⟩, other_size⟩
  have exists_section (cell) (meet : meets cell) :
      Nonempty (cell.val.ClosedBankCircleSection
        (traces cell).value (traces cell).center cutoff radius) := by
    obtain ⟨_, ⟨z, approached, rfl⟩, on_circle⟩ := meet
    exact (traces cell).closed_circle_section_of_approached_point close_margin (margins cell)
      radius_positive far approached on_circle
  let sections := fun cell (meet : meets cell) => Classical.choice (exists_section cell meet)
  have order := waterfall_closed_section_facing_bank_order R outward D B leaf_vertices footprint
    deep P traces curvature_covered budget nonnegative small_error linear_error pinches provenance
    represented leaf_coherent numerical margins radius_positive far all_tails regular_continuations
    a b physical_order (sections a meet_a) (sections b meet_b)
  have values : (traces a).value x = (traces b).value y :=
    (traces a).outputFrame.symm.injective same
  have points := (traces a).closed_section_contact_preimages_eq_bank_points (traces b)
    (sections a meet_a) (sections b meet_b) nonnegative small_error numerical linear_error
    (margins a) (margins b) radius_positive far order first last size values
  have physical_ordered := waterfall_closed_section_physical_contacts R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    provenance represented leaf_coherent numerical margins radius_positive far all_tails
    continuations regular_continuations enclosing_margin sections
  have nonempty_a : (a.val.openSlab 0 cutoff).Nonempty := closure_nonempty_iff.mp ⟨x, first⟩
  have nonempty_b : (b.val.openSlab 0 cutoff).Nonempty := closure_nonempty_iff.mp ⟨y, last⟩
  have physical_filtered : List.Sublist [a, b] (P.nonemptyCells cutoff) := by
    simpa [MonotoneStrip.Subdivision.nonemptyCells, nonempty_a, nonempty_b] using
      physical_order.filter (fun cell => decide (cell.val.openSlab 0 cutoff).Nonempty)
  have retained : List.Sublist [a, b] ((P.nonemptyCells cutoff).filter
      (fun cell => decide (meets cell))) := by
    simpa [meet_a, meet_b] using physical_filtered.filter (fun cell => decide (meets cell))
  have physical_pair := physical_ordered.sublist retained
  have physical_contact := (List.pairwise_cons.mp physical_pair).1 b (by simp)
  have bank_values : (traces a).value (a.val.upper.point (sections a meet_a).upperHeight) =
      (traces b).value (b.val.lower.point (sections b meet_b).lowerHeight) :=
    (congrArg (traces a).value points.1).symm.trans
      (values.trans (congrArg (traces b).value points.2))
  exact points.1.trans ((physical_contact meet_a meet_b bank_values).trans points.2.symm)

end Unfoldings.ConvexRoof.SectorForest
