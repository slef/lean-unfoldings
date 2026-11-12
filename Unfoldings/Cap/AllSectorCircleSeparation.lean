module

public import Unfoldings.Cap.AdjacentSectorCircleSeparation
public import Unfoldings.Cap.NonadjacentSectorSeparation
public import Unfoldings.Cap.WaterfallCircleSurvivors

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
theorem waterfall_circle_images_pairwise_disjoint_across_sectors
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
      (traces a cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces a cell).center‖ = radius} = ∅ →
        (cell.val.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation a (traces a cell) physicalRadius radius))
    (all_outside_empty : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      radius ∉ (traces a cell).emptyCircleExceptions)
    (physical_room : 2 * physicalRadius < cutoff)
    (first last : Σ a : FiveSector, {S : MonotoneStrip // S ∈ (P a).cells})
    (different : first ≠ last)
    (radius_positive : 0 < radius) (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (μ : FiveSector → ℝ) (numerical : ∀ a, ε * (1 + ε) < μ a - ε)
    (margins : ∀ a, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells}, ∀ z ∈ cell.val.carrier,
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
          D.projectedMap Q (K.projectedVertex origin))).im) :
    Disjoint ((traces first.1 first.2).outputFrame.symm ''
        ((traces first.1 first.2).value '' first.2.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces first.1 first.2).center‖ = radius}))
      ((traces last.1 last.2).outputFrame.symm ''
        ((traces last.1 last.2).value '' last.2.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces last.1 last.2).center‖ = radius})) := by
  rcases first with ⟨i, first⟩
  rcases last with ⟨j, last⟩
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  by_cases same_sector : i = j
  · subst j
    have different_cells : first ≠ last := by
      intro equal
      apply different
      cases equal
      rfl
    have within := waterfall_circle_images_pairwise_disjoint R outward D B (leaf_vertices i)
      footprint deep (P i) (traces i) curvature_covered budget nonnegative small_error
      (linear_error (fiveSectorFrame t positive small i).place) (pinches i) (provenance i)
      (represented i) (leaf_coherent i) (numerical i) (margins i) radius_positive far outside
      (all_tails i) (continuations i) (all_outside_empty i)
    have separated := within.forall (List.mem_attach _ first) (List.mem_attach _ last)
      different_cells
    apply Set.disjoint_left.mpr
    rintro p ⟨x, first_member, at_first⟩ ⟨y, last_member, at_last⟩
    have equal : x = y := (traces i first).outputFrame.symm.injective
      (at_first.trans at_last.symm)
    exact Set.disjoint_left.mp separated first_member (equal.symm ▸ last_member)
  · obtain ⟨a, rfl⟩ := fiveSectorCycle.surjective i
    obtain ⟨b, rfl⟩ := fiveSectorCycle.surjective j
    by_cases next : finRotate 5 a = b
    · have shared : fiveSectorFirst t (fiveSectorCycle b) =
          fiveSectorLast t (fiveSectorCycle a) := by
        have contact := fiveSectorCycle_last_eq_next_first t a
        rw [next] at contact
        exact contact.symm
      exact (M.adjacent_sector_circle_images_disjoint F covered positive small lower R outward D B
        leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
        linear_error pinches provenance represented leaf_coherent all_tails continuations
        all_outside_empty physical_room shared last first radius_positive room outside μ numerical
        margins positive_margin face_bounds).symm
    · by_cases previous : finRotate 5 b = a
      · have shared : fiveSectorFirst t (fiveSectorCycle a) =
            fiveSectorLast t (fiveSectorCycle b) := by
          have contact := fiveSectorCycle_last_eq_next_first t b
          rw [previous] at contact
          exact contact.symm
        exact M.adjacent_sector_circle_images_disjoint F covered positive small lower R outward D B
          leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
          linear_error pinches provenance represented leaf_coherent all_tails continuations
          all_outside_empty physical_room shared first last radius_positive room outside μ numerical
          margins positive_margin face_bounds
      · have different_indices : a ≠ b := fun equal => same_sector (congrArg fiveSectorCycle equal)
        have first_error : ε < μ (fiveSectorCycle a) := by
          nlinarith [sq_nonneg ε, numerical (fiveSectorCycle a)]
        have last_error : ε < μ (fiveSectorCycle b) := by
          nlinarith [sq_nonneg ε, numerical (fiveSectorCycle b)]
        exact RadialCutForest.nonadjacent_sector_circle_images_disjoint
          (traces (fiveSectorCycle a) first) (traces (fiveSectorCycle b) last) different_indices
          next previous first_error last_error (margins (fiveSectorCycle a) first)
          (margins (fiveSectorCycle b) last) radius

end Unfoldings.ConvexCap.SectorForest
