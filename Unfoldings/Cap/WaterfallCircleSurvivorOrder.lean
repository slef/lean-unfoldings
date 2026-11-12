module

public import Unfoldings.Cap.WaterfallCircleSurvivorBanks
public import Unfoldings.Topology.OrderedBankPieces
public import Unfoldings.Topology.FilterDisjoint

/-! Actual source-circle survivors retain their full ordered bank endpoints. -/

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
/-- Removing empty physical cells and disappearing circle runs preserves the
actual order of every surviving pair of bank endpoints. The slices may be
chosen independently by the caller; radial uniqueness makes their choices immaterial. -/
theorem waterfall_circle_survivor_bank_order
    (slices : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty →
      cell.val.BankCircleSlice (traces cell).value (traces cell).center cutoff radius) :
    ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).Pairwise
      (fun a b => ∀ meet_a meet_b,
        ((traces a).value (a.val.upper.point (slices a meet_a).upperHeight) -
          (traces a).center).re ≤
        ((traces b).value (b.val.lower.point (slices b meet_b).lowerHeight) -
          (traces b).center).re) := by
  have ordered := waterfall_circle_survivor_banks_ordered R outward D B leaf_vertices footprint
    deep P traces curvature_covered budget nonnegative small_error linear_error pinches provenance
    represented leaf_coherent numerical margins radius_positive far outside all_tails continuations
    all_outside_empty slices
  exact ordered.imp (fun gap meet_a meet_b => (gap meet_a meet_b).1)

end Unfoldings.ConvexCap.SectorForest
