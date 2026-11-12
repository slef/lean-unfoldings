module

public import Unfoldings.Cap.AdjacentSectorCircleSeparation
public import Unfoldings.Cap.AdjacentSurvivorClosedCircleContact
public import Unfoldings.Cap.WaterfallClosedCircleExtremeBounds

/-! Every pair of actual waterfall circle images in adjacent sectors is disjoint. -/

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
theorem adjacent_sector_closed_circle_physical_contact
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
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    (first : {S : MonotoneStrip // S ∈ (P i).cells})
    (last : {S : MonotoneStrip // S ∈ (P j).cells})
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
          D.projectedMap Q (K.projectedVertex origin))).im)
    {x y : ℂ} (first_closed : x ∈ closure (first.val.openSlab 0 cutoff))
    (last_closed : y ∈ closure (last.val.openSlab 0 cutoff))
    (size : ‖(traces i first).value x - (traces i first).center‖ = radius)
    (same : (traces i first).outputFrame.symm ((traces i first).value x) =
      (traces j last).outputFrame.symm ((traces j last).value y)) :
    (fiveSectorFrame t positive small i).place.symm x =
      (fiveSectorFrame t positive small j).place.symm y := by
  let meets := fun a (cell : {S : MonotoneStrip // S ∈ (P a).cells}) =>
    ((traces a cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces a cell).center‖ = radius}).Nonempty
  let keep := fun a (cell : {S : MonotoneStrip // S ∈ (P a).cells}) => decide (meets a cell)
  let survivors := fun a => ((P a).nonemptyCells cutoff).filter (keep a)
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  have cutoff_positive : 0 < cutoff := by
    by_contra nonpositive
    have bound := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr small_error.le)
      (not_lt.mp nonpositive)
    exact (not_lt_of_ge bound) (radius_positive.trans far)
  have nonempty (a) : survivors a ≠ [] :=
    B.waterfall_circle_survivors_ne_nil a (P a) (traces a) cutoff_positive (continuations a)
  let head := fun a => (survivors a).head (nonempty a)
  let endPiece := fun a => (survivors a).getLast (nonempty a)
  have at_head (a) : (survivors a).head? = some (head a) :=
    List.head?_eq_some_head (nonempty a)
  have at_end (a) : (survivors a).getLast? = some (endPiece a) :=
    List.getLast?_eq_some_getLast (nonempty a)
  have survivor_meets {a} {cell} (member : cell ∈ survivors a) : meets a cell :=
    of_decide_eq_true (List.mem_filter.mp member).2
  have head_meets (a) : meets a (head a) := survivor_meets (List.head_mem (nonempty a))
  have end_meets (a) : meets a (endPiece a) := survivor_meets (List.getLast_mem (nonempty a))
  have close_margin (a) : ε < μ a := by nlinarith [sq_nonneg ε, numerical a]
  let slices := fun a cell (meet : meets a cell) => Classical.choice
    ((traces a cell).circle_slice (close_margin a) (margins a cell) radius_positive far meet)
  have bounds (a) := waterfall_closed_circle_images_extreme_bounds R outward D B (leaf_vertices a)
    footprint deep (P a) (traces a) curvature_covered budget nonnegative small_error
    (linear_error (fiveSectorFrame t positive small a).place) (pinches a) (provenance a)
    (represented a) (leaf_coherent a) (numerical a) (margins a) radius_positive far outside
    (all_tails a) (continuations a) (all_outside_empty a) (slices a) (head a) (endPiece a)
    (head_meets a) (end_meets a) (at_head a) (at_end a)
  have other_size : ‖(traces j last).value y - (traces j last).center‖ = radius := by
    rw [← (traces j last).outputFrame_symm_source_distance, ← same,
      (traces i first).outputFrame_symm_source_distance]
    exact size
  let p := (traces i first).outputFrame.symm ((traces i first).value x)
  have first_bounds := bounds i first p
    ⟨(traces i first).value x, ⟨⟨x, first_closed, rfl⟩, size⟩, rfl⟩
  have last_bounds := bounds j last p
    ⟨(traces j last).value y, ⟨⟨y, last_closed, rfl⟩, other_size⟩, same.symm⟩
  have contact := M.adjacent_survivor_weak_circle_contact F covered positive small lower R outward
    D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches provenance represented leaf_coherent all_tails continuations
    all_outside_empty
    physical_room shared (endPiece i) (head j) (slices i (endPiece i) (end_meets i))
    (slices j (head j) (head_meets j)) (at_end i) (at_head j) radius_positive room outside
    positive_margin face_bounds first_bounds.1.1 last_bounds.1.2
  have first_piece : first = endPiece i := first_bounds.2.1 contact.1
  have last_piece : last = head j := last_bounds.2.2 (contact.1.trans contact.2.1)
  have first_subset : first.val.openSlab 0 cutoff ⊆ (traces i first).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_subset : last.val.openSlab 0 cutoff ⊆ (traces j last).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_point : x = (endPiece i).val.upper.point
      (slices i (endPiece i) (end_meets i)).upperHeight := by
    have values := contact.1
    change (traces i first).outputFrame.symm ((traces i first).value x) = _ at values
    rw [first_piece] at values first_closed
    exact (traces i (endPiece i)).closed_injective
      (closure_mono (first_piece ▸ first_subset) first_closed)
      (slices i (endPiece i) (end_meets i)).upper_closed
      ((traces i (endPiece i)).outputFrame.symm.injective values)
  have last_point : y = (head j).val.lower.point
      (slices j (head j) (head_meets j)).lowerHeight := by
    have values := same.symm.trans (contact.1.trans contact.2.1)
    rw [last_piece] at values last_closed
    exact (traces j (head j)).closed_injective
      (closure_mono (last_piece ▸ last_subset) last_closed)
      (slices j (head j) (head_meets j)).lower_closed
      ((traces j (head j)).outputFrame.symm.injective values)
  rw [first_point, last_point]
  exact contact.2.2

end Unfoldings.ConvexCap.SectorForest
