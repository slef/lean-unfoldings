module

public import Unfoldings.Cap.AcrossSectorAllRadiusContact
public import Unfoldings.Cap.SameSectorAllRadiusContact

/-! All actual waterfall strip-circle images are pairwise disjoint across the five sectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

open Classical in
theorem waterfall_all_radius_closed_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff ε physicalRadius radius : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
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
            (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (provenance : ∀ a, ∀ H ∈ (P a).separators,
      ∃ leaf : M.GeometricSectorLeaf F covered positive small lower a,
        leaf.point.re + leaf.point.im ≤ cutoff ∧
          MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (represented : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ (P a).separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (all_tails : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      cell.val.TerminalTailsFrom
        (fun leaf : M.GeometricSectorLeaf F covered positive small lower a => leaf.point)
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
    (first last : Σ a : FiveSector, {S : MonotoneStrip // S ∈ (P a).cells})
    (radius_positive : 0 < radius) (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (μ : FiveSector → ℝ) (numerical : ∀ a, ε * (1 + ε) < μ a - ε)
    (margins : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells}, ∀ z ∈ cell.val.carrier,
      0 ≤ z.re + z.im → μ a * (z.re + z.im) ≤ z.re ∧ μ a * (z.re + z.im) ≤ z.im)
    (enclosing_margin : ∀ a, ∀ z ∈ (fiveSectorFrame t positive small a).enclosingStrip.carrier,
      0 ≤ z.re + z.im → μ a * (z.re + z.im) ≤ z.re ∧ μ a * (z.re + z.im) ≤ z.im)
    {ω : ℝ} (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im)
    {x y : ℂ} (first_closed : x ∈ closure (first.2.val.openSlab 0 cutoff))
    (last_closed : y ∈ closure (last.2.val.openSlab 0 cutoff))
    (size : ‖(traces first.1 first.2).value x - (traces first.1 first.2).center‖ = radius)
    (same : (traces first.1 first.2).outputFrame.symm ((traces first.1 first.2).value x) =
      (traces last.1 last.2).outputFrame.symm ((traces last.1 last.2).value y)) :
    (fiveSectorFrame t positive small first.1).place.symm x =
      (fiveSectorFrame t positive small last.1).place.symm y := by
  classical
  rcases first with ⟨i, first⟩
  rcases last with ⟨j, last⟩
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  by_cases same_sector : i = j
  · subst j
    exact congrArg (fiveSectorFrame t positive small i).place.symm
      (waterfall_same_sector_all_radius_physical_contact R outward D B (leaf_vertices i)
        footprint deep (P i) (traces i) curvature_covered budget nonnegative small_error
        (linear_error (fiveSectorFrame t positive small i).place) (pinches i)
        (provenance i) (represented i) (leaf_coherent i) (numerical i) (margins i)
        radius_positive far (all_tails i) (continuations i)
        (fun r bounds => regular_continuations r bounds i) (enclosing_margin i)
        first last first_closed last_closed size same)
  · exact M.waterfall_all_radius_contact_across_distinct_sectors F covered positive small lower
      R outward D B leaf_vertices footprint deep P traces curvature_covered budget nonnegative
      small_error linear_error pinches provenance represented leaf_coherent all_tails continuations
      regular_continuations physical_room ⟨i, first⟩ ⟨j, last⟩ same_sector radius_positive room 
      μ numerical margins enclosing_margin positive_margin face_bounds first_closed
        last_closed size same

end Unfoldings.ConvexCap.SectorForest
