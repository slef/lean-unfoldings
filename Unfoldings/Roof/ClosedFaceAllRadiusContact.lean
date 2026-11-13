module

public import Unfoldings.Roof.AllSectorAllRadiusContact
public import Unfoldings.Cap.ClosedTraceGraphs

/-! Coincident actual closed-face copies identify the same physical point at controlled radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain origin)
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

open Classical in
theorem closed_face_all_radius_contact_same_projected_point
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest origin (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff ε physicalRadius radius : ℝ}
    (deep : Metric.closedBall origin cutoff ⊆ interior (outerDomain))
    (P : ∀ a : FiveSector, (fiveSectorFrame t positive small a).enclosingStrip.Subdivision)
    (traces : ∀ a : FiveSector, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) a cell.val ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (linear_error : ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) frame f).linear z - z‖ ≤
          ε * ‖z‖)
    (pinches : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      cell.val.ApproachedPinchesIn
        (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
            M.extendedGeometricCuts F} =>
          (fiveSectorFrame t positive small a).place
            (Q.projectedVertex v.val - origin))) 0 cutoff)
    (provenance : ∀ a, ∀ H ∈ (P a).separators,
      ∃ leaf : M.GeometricSectorLeaf F covered positive small a,
        leaf.point.re + leaf.point.im ≤ cutoff ∧
          MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (represented : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ (P a).separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (all_tails : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      cell.val.TerminalTailsFrom
        (fun leaf : M.GeometricSectorLeaf F covered positive small a => leaf.point)
        (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuations : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      (traces a cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
          {z | ‖z - (traces a cell).center‖ = radius} = ∅ →
        (cell.val.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation a (traces a cell) physicalRadius radius))
    (regular_continuations : ∀ r ∈ Set.Ioo 0 radius, ∀ a,
      ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
        r ∉ (traces a cell).emptyCircleExceptions →
        (traces a cell).value '' cell.val.openSlab 0 cutoff ∩
            {z | ‖z - (traces a cell).center‖ = r} = ∅ →
        (cell.val.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation a (traces a cell) physicalRadius r))
    (physical_room : 2 * physicalRadius < cutoff)
    (radius_positive : 0 < radius) (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (μ : FiveSector → ℝ) (numerical : ∀ a, ε * (1 + ε) < μ a - ε)
    (margins : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells}, ∀ z ∈ cell.val.carrier,
      0 ≤ z.re + z.im → μ a * (z.re + z.im) ≤ z.re ∧ μ a * (z.re + z.im) ≤ z.im)
    (enclosing_margin : ∀ a, ∀ z ∈ (fiveSectorFrame t positive small a).enclosingStrip.carrier,
      0 ≤ z.re + z.im → μ a * (z.re + z.im) ≤ z.re ∧ μ a * (z.re + z.im) ≤ z.im)
    {ω : ℝ} (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small origin cutoff →
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q origin)).re ∧
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q origin)).im)
    {U : Set Plane} (opened : IsOpen U)
    (inside : U ⊆ sectorSweepInterior positive small origin cutoff)
    (f g : FineFace) {p q : Plane}
    (first : p ∈ (Q.projectedTriangle f).carrier ∩ U)
    (last : q ∈ (Q.projectedTriangle g).carrier ∩ U)
    (size : ‖D.projectedPlacement Q f p - D.projectedMap Q origin‖ = radius)
    (same : D.projectedPlacement Q f p = D.projectedPlacement Q g q) : p = q := by
  obtain ⟨a, first_cell, x, first_closed, first_physical, first_value⟩ :=
    ConvexCap.RadialCutForest.exists_closed_trace_of_face_point P traces opened inside f first
  obtain ⟨b, last_cell, y, last_closed, last_physical, last_value⟩ :=
    ConvexCap.RadialCutForest.exists_closed_trace_of_face_point P traces opened inside g last
  have first_size : ‖(traces a first_cell).value x - (traces a first_cell).center‖ = radius := by
    rw [← (traces a first_cell).outputFrame_symm_source_distance, ← first_value]
    exact size
  have values : (traces a first_cell).outputFrame.symm ((traces a first_cell).value x) =
      (traces b last_cell).outputFrame.symm ((traces b last_cell).value y) :=
    first_value.symm.trans (same.trans last_value)
  have physical := M.waterfall_all_radius_closed_contact F covered positive small R
    outward D B leaf_vertices footprint deep P traces curvature_covered budget nonnegative
    small_error linear_error pinches provenance represented leaf_coherent all_tails continuations
    regular_continuations physical_room ⟨a, first_cell⟩ ⟨b, last_cell⟩ radius_positive room
    μ numerical margins enclosing_margin positive_margin face_bounds first_closed
      last_closed first_size values
  rw [first_physical, last_physical, physical]

end Unfoldings.ConvexRoof.SectorForest
