module

public import Unfoldings.Cap.WaterfallClosedSectionOrder
public import Unfoldings.Cap.WithinSectorAllRadiusContact
public import Unfoldings.Cap.ClosedSectionCircleContact
public import Unfoldings.Cap.RadialClosedCircleSections
public import Unfoldings.Cap.ClosedCircleSectionLexOrder

/-! Full survivor order retains physical point equality whenever developed bank values coincide. -/

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

/-- Actual same-sector contact has one physical preimage, in either cell order. -/
theorem waterfall_same_sector_all_radius_physical_contact
    (first last : {S : MonotoneStrip // S ∈ P.cells})
    {x y : ℂ} (first_closed : x ∈ closure (first.val.openSlab 0 cutoff))
    (last_closed : y ∈ closure (last.val.openSlab 0 cutoff))
    (size : ‖(traces first).value x - (traces first).center‖ = radius)
    (same : (traces first).outputFrame.symm ((traces first).value x) =
      (traces last).outputFrame.symm ((traces last).value y)) : x = y := by
  classical
  by_cases same_cell : first = last
  · subst last
    have included : first.val.openSlab 0 cutoff ⊆ (traces first).strictDomain :=
      fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
    exact (traces first).closed_injective (closure_mono included first_closed)
      (closure_mono included last_closed) ((traces first).outputFrame.symm.injective same)
  have within := waterfall_within_sector_all_radius_physical_contact R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches provenance represented leaf_coherent numerical margins radius_positive
    far all_tails continuations regular_continuations enclosing_margin
  obtain ⟨a, a_bound, at_a⟩ := List.mem_iff_getElem.mp (List.mem_attach P.cells first)
  obtain ⟨b, b_bound, at_b⟩ := List.mem_iff_getElem.mp (List.mem_attach P.cells last)
  rcases lt_trichotomy a b with before | equal | after
  · have order := pair_getElem_sublist P.cells.attach a b before b_bound
    rw [at_a, at_b] at order
    exact within first last order first_closed last_closed size same
  · have at_same : first = last := at_a.symm.trans (by simpa only [equal] using at_b)
    exact (same_cell at_same).elim
  · have order := pair_getElem_sublist P.cells.attach b a after a_bound
    rw [at_a, at_b] at order
    have other_size : ‖(traces last).value y - (traces last).center‖ = radius := by
      rw [← (traces last).outputFrame_symm_source_distance, ← same,
        (traces first).outputFrame_symm_source_distance]
      exact size
    exact (within last first order last_closed first_closed other_size same.symm).symm

end Unfoldings.ConvexCap.SectorForest
