module

public import Unfoldings.Cap.BoundaryRunSourceBankCandidate
public import Unfoldings.Cap.BoundaryRunNeighborCircleCandidate
public import Unfoldings.Cap.BoundaryRunSharedMargins
public import Unfoldings.Cap.BoundaryRunCircleCaps
public import Unfoldings.Cap.StripCircleCoordinateCaps

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
  have caps := circle_caps_disjoint_across_upper_boundary_run R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    cells contacts ordered_cells terminals tails provenance represented leaf_coherent source slice
    radius_positive far outside outside_empty empty pivot highest last_maximum physical_room
    source_order facing separator outer j shared all_leaf_coherent other other_slice neighbor_outer
    room positive_margin face_bounds
  exact caps.mono
    (B.circle_image_subset_upper_cap i (traces source) slice first_order first_error first_margin
      radius_positive)
    (B.circle_image_subset_lower_cap j other other_slice last_order last_error last_margin
      radius_positive)

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
  have caps := circle_caps_disjoint_across_lower_boundary_run R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    cells contacts ordered_cells terminals tails provenance represented leaf_coherent source slice
    radius_positive far outside outside_empty empty pivot highest first_maximum physical_room
    source_order facing separator outer j shared all_leaf_coherent other other_slice neighbor_outer
    room positive_margin face_bounds
  exact caps.mono
    (B.circle_image_subset_lower_cap i (traces source) slice first_order first_error first_margin
      radius_positive)
    (B.circle_image_subset_upper_cap j other other_slice last_order last_error last_margin
      radius_positive)

end Unfoldings.ConvexCap.SectorForest

