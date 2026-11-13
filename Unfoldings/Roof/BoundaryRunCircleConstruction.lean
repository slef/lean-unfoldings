module

public import Unfoldings.Roof.BoundaryRunCircleCaps
public import Unfoldings.Geometry.SubdivisionBoundaryRun
public import Unfoldings.Topology.FiniteMaxPositions

/-! Construct extreme actual terminals and separating circle portions for indexed boundary runs. -/

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

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent

theorem circle_caps_disjoint_of_boundary_run {physicalRadius radius : ℝ}
    (upper : Bool) (source : {S : MonotoneStrip // S ∈ P.cells})
    (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
    {keep : {S : MonotoneStrip // S ∈ P.cells} → Bool}
    (run : P.BoundaryRun cutoff keep source upper)
    (empty : ∀ k, (traces (run.cells k)).value '' (run.cells k).val.openSlab 0 cutoff ∩
      {z | ‖z - (traces (run.cells k)).center‖ = radius} = ∅)
    (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      (traces cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces cell).center‖ = radius} = ∅ →
        (cell.val.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius))
    (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      cell.val.TerminalTailsFrom
        (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
        (fun leaf => leaf.tailGraph.graph) cutoff)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (all_outside_empty : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      radius ∉ (traces cell).emptyCircleExceptions)
    (physical_room : 2 * physicalRadius < cutoff)
    (j : FiveSector)
    (shared : if upper then fiveSectorFirst t i = fiveSectorLast t j
      else fiveSectorFirst t j = fiveSectorLast t i)
    (all_leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {T : MonotoneStrip}
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (neighbor_outer : if upper then Set.EqOn T.lower.point
        (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff)
      else Set.EqOn T.upper.point
        (fiveSectorFrame t positive small j).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    {ω : ℝ} (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (origin) cutoff →
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).re ∧
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).im) :
    Disjoint
      (if upper then circleUpperCap (B.sectorFrame i)
          (D.projectedMap Q (origin)) radius
          ((traces source).value (source.val.upper.point slice.upperHeight) -
            (traces source).center).re
        else circleLowerCap (B.sectorFrame i) (D.projectedMap Q (origin)) radius
          ((traces source).value (source.val.lower.point slice.lowerHeight) -
            (traces source).center).im)
      (if upper then circleLowerCap (B.sectorFrame j)
          (D.projectedMap Q (origin)) radius
          (other.value (T.lower.point other_slice.lowerHeight) - other.center).im
        else circleUpperCap (B.sectorFrame j) (D.projectedMap Q (origin)) radius
          (other.value (T.upper.point other_slice.upperHeight) - other.center).re) := by
  classical
  let terminals := fun k => Classical.choice
    (continuations (run.cells k) (empty k) (run.physical k))
  obtain ⟨first, last, _, same, highest, strict_first, strict_last⟩ :=
    exists_first_last_max_positions (fun k => (terminals k).height)
  have highest_last (k) : (terminals k).height ≤ (terminals last).height :=
    (highest k).trans_eq same
  cases upper
  · have separator := P.lower_bank_separator_of_nonempty_contact
      (run.cells (Fin.last run.length)).property source.property
      (fun h member => (run.facing member).symm) (run.physical (Fin.last run.length))
    exact circle_caps_disjoint_across_lower_boundary_run R outward D B leaf_vertices footprint deep
      P traces curvature_covered budget nonnegative small_error linear_error pinches run.cells
      run.contacts run.ordered terminals (fun k => all_tails (run.cells k)) provenance represented
      leaf_coherent source slice radius_positive far outside
      (fun k => all_outside_empty (run.cells k))
      empty first highest strict_first physical_room run.source_order run.facing separator run.outer
      j shared all_leaf_coherent other other_slice neighbor_outer room positive_margin face_bounds
  · have separator := P.upper_bank_separator_of_nonempty_contact source.property
      (run.cells 0).property run.facing (run.physical 0)
    exact circle_caps_disjoint_across_upper_boundary_run R outward D B leaf_vertices footprint deep
      P traces curvature_covered budget nonnegative small_error linear_error pinches run.cells
      run.contacts run.ordered terminals (fun k => all_tails (run.cells k)) provenance represented
      leaf_coherent source slice radius_positive far outside
      (fun k => all_outside_empty (run.cells k))
      empty last highest_last strict_last physical_room run.source_order run.facing separator
      run.outer
      j shared all_leaf_coherent other other_slice neighbor_outer room positive_margin face_bounds

end Unfoldings.ConvexRoof.SectorForest
