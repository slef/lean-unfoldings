module

public import Unfoldings.Cap.AllSectorCircleSeparation
public import Unfoldings.Cap.AdjacentSectorAllRadiusContact
public import Unfoldings.Cap.NonadjacentClosedSeparation

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
theorem waterfall_all_radius_contact_across_distinct_sectors
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
    (different_sectors : first.1 ≠ last.1)
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
  rcases first with ⟨i, first⟩
  rcases last with ⟨j, last⟩
  have other_size : ‖(traces j last).value y - (traces j last).center‖ = radius := by
    rw [← (traces j last).outputFrame_symm_source_distance, ← same,
      (traces i first).outputFrame_symm_source_distance]
    exact size
  obtain ⟨a, rfl⟩ := fiveSectorCycle.surjective i
  obtain ⟨b, rfl⟩ := fiveSectorCycle.surjective j
  by_cases next : finRotate 5 a = b
  · have shared : fiveSectorFirst t (fiveSectorCycle b) =
        fiveSectorLast t (fiveSectorCycle a) := by
      have contact := fiveSectorCycle_last_eq_next_first t a
      rw [next] at contact
      exact contact.symm
    exact (M.adjacent_sector_all_radius_physical_contact F covered positive small lower R
      outward D B leaf_vertices footprint deep P traces curvature_covered budget nonnegative
      small_error linear_error pinches provenance represented leaf_coherent all_tails continuations
      regular_continuations physical_room shared last first radius_positive room  μ numerical
      margins enclosing_margin positive_margin face_bounds last_closed first_closed
        other_size same.symm).symm
  · by_cases previous : finRotate 5 b = a
    · have shared : fiveSectorFirst t (fiveSectorCycle a) =
          fiveSectorLast t (fiveSectorCycle b) := by
        have contact := fiveSectorCycle_last_eq_next_first t b
        rw [previous] at contact
        exact contact.symm
      exact M.adjacent_sector_all_radius_physical_contact F covered positive small lower R
        outward D B leaf_vertices footprint deep P traces curvature_covered budget nonnegative
        small_error linear_error pinches provenance represented leaf_coherent all_tails
        continuations regular_continuations physical_room shared first last radius_positive room
         μ numerical margins enclosing_margin positive_margin face_bounds first_closed
           last_closed size same
    · have different_indices : a ≠ b :=
        fun equal => different_sectors (congrArg fiveSectorCycle equal)
      have first_error : ε < μ (fiveSectorCycle a) := by
        nlinarith [sq_nonneg ε, numerical (fiveSectorCycle a)]
      have last_error : ε < μ (fiveSectorCycle b) := by
        nlinarith [sq_nonneg ε, numerical (fiveSectorCycle b)]
      have disjoint := RadialCutForest.nonadjacent_sector_closed_circle_images_disjoint
        (traces (fiveSectorCycle a) first) (traces (fiveSectorCycle b) last) different_indices
        next previous first_error last_error (margins (fiveSectorCycle a) first)
        (margins (fiveSectorCycle b) last) radius_positive
      exact (Set.disjoint_left.mp disjoint
        ⟨(traces (fiveSectorCycle a) first).value x, ⟨⟨x, first_closed, rfl⟩, size⟩, rfl⟩
        ⟨(traces (fiveSectorCycle b) last).value y,
          ⟨⟨y, last_closed, rfl⟩, other_size⟩, same.symm⟩).elim

end Unfoldings.ConvexCap.SectorForest
