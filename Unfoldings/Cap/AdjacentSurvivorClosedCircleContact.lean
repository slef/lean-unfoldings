module

public import Unfoldings.Cap.AdjacentSurvivorCircleCaps
public import Unfoldings.Cap.OuterClosedCircleContact
public import Unfoldings.Cap.BoundaryRunClosedConstruction

/-! Actual extreme circle survivors in adjacent sectors have disjoint bounding portions. -/

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
theorem adjacent_survivor_weak_circle_contact
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
    (slice : first.val.BankCircleSlice (traces i first).value (traces i first).center cutoff radius)
    (other_slice : last.val.BankCircleSlice (traces j last).value (traces j last).center
      cutoff radius)
    (at_first_last : (((P i).nonemptyCells cutoff).filter (fun cell => decide
      ((traces i cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces i cell).center‖ = radius}).Nonempty)).getLast? = some first)
    (at_last_head : (((P j).nonemptyCells cutoff).filter (fun cell => decide
      ((traces j cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces j cell).center‖ = radius}).Nonempty)).head? = some last)
    (radius_positive : 0 < radius) (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
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
    {p : Plane}
    (first_member : p ∈ weakCircleUpperCap (B.sectorFrame i)
      (D.projectedMap Q (K.projectedVertex origin)) radius
      ((traces i first).value (first.val.upper.point slice.upperHeight) -
        (traces i first).center).re)
    (last_member : p ∈ weakCircleLowerCap (B.sectorFrame j)
      (D.projectedMap Q (K.projectedVertex origin)) radius
      ((traces j last).value (last.val.lower.point other_slice.lowerHeight) -
        (traces j last).center).im) :
    p = (traces i first).outputFrame.symm
        ((traces i first).value (first.val.upper.point slice.upperHeight)) ∧
      (traces i first).outputFrame.symm
          ((traces i first).value (first.val.upper.point slice.upperHeight)) =
        (traces j last).outputFrame.symm
          ((traces j last).value (last.val.lower.point other_slice.lowerHeight)) ∧
      (fiveSectorFrame t positive small i).place.symm (first.val.upper.point slice.upperHeight) =
        (fiveSectorFrame t positive small j).place.symm
          (last.val.lower.point other_slice.lowerHeight) := by
  let keep := fun a (cell : {S : MonotoneStrip // S ∈ (P a).cells}) => decide
    ((traces a cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces a cell).center‖ = radius}).Nonempty
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  have cutoff_positive : 0 < cutoff :=
    ((traces i first).circle_slice_heights radius_positive far slice).2.1.trans
      ((traces i first).circle_slice_heights radius_positive far slice).2.2
  have missing {a : FiveSector} {source : {S : MonotoneStrip // S ∈ (P a).cells}} {upper : Bool}
      (run : (P a).BoundaryRun cutoff (keep a) source upper) (k) :
      (traces a (run.cells k)).value '' (run.cells k).val.openSlab 0 cutoff ∩
        {z | ‖z - (traces a (run.cells k)).center‖ = radius} = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    simpa only [keep, decide_eq_true_eq] using run.removed k
  rcases (P i).upper_boundary_run_or_contact cutoff_positive (keep i) first at_first_last with
    first_outer | first_exists
  · rcases (P j).lower_boundary_run_or_contact cutoff_positive (keep j) last at_last_head with
      last_outer | last_exists
    · exact M.weak_circle_outer_banks_contact F covered positive small lower
        R outward D B leaf_vertices leaf_coherent footprint curvature_covered budget shared
        (traces i first) (traces j last) slice other_slice first_outer
        (fun h member => (last_outer member).symm) radius_positive small_error room outside deep
        positive_margin face_bounds first_member last_member
    · let last_run := Classical.choice last_exists
      obtain ⟨point, values, physical⟩ := weak_circle_contact_of_boundary_run R outward D B
        (leaf_vertices j) footprint deep
        (P j) (traces j) curvature_covered budget nonnegative small_error
        (linear_error (fiveSectorFrame t positive small j).place) (pinches j) (provenance j)
        (represented j) (leaf_coherent j) false last other_slice last_run (missing last_run)
        (continuations j) (all_tails j) radius_positive far outside (all_outside_empty j)
        physical_room i shared leaf_coherent (traces i first) slice first_outer room positive_margin
        face_bounds last_member first_member
      exact ⟨point.trans values, values.symm, physical.symm⟩
  · let first_run := Classical.choice first_exists
    rcases (P j).lower_boundary_run_or_contact cutoff_positive (keep j) last at_last_head with
      last_outer | last_exists
    · exact weak_circle_contact_of_boundary_run R outward D B (leaf_vertices i) footprint deep
        (P i) (traces i) curvature_covered budget nonnegative small_error
        (linear_error (fiveSectorFrame t positive small i).place) (pinches i) (provenance i)
        (represented i) (leaf_coherent i) true first slice first_run (missing first_run)
        (continuations i) (all_tails i) radius_positive far outside (all_outside_empty i)
        physical_room j shared leaf_coherent (traces j last) other_slice
        (fun h member => (last_outer member).symm) room positive_margin face_bounds first_member
          last_member
    · let last_run := Classical.choice last_exists
      let first_terminals := fun k => Classical.choice (continuations i (first_run.cells k)
        (missing first_run k) (first_run.physical k))
      let last_terminals := fun k => Classical.choice (continuations j (last_run.cells k)
        (missing last_run k) (last_run.physical k))
      obtain ⟨a, first_highest⟩ := Finite.exists_max (fun k => (first_terminals k).height)
      obtain ⟨b, last_highest⟩ := Finite.exists_max (fun k => (last_terminals k).height)
      exact (not_adjacent_boundary_runs R D B shared (fun k => (first_run.cells k).val)
        (fun k => (last_run.cells k).val) (fun k => traces i (first_run.cells k))
        (fun k => traces j (last_run.cells k)) first_run.contacts last_run.contacts first_terminals
        last_terminals (fun k => all_tails i (first_run.cells k))
        (fun k => all_tails j (last_run.cells k)) deep a b first_highest last_highest
        first_run.outer last_run.outer).elim

end Unfoldings.ConvexCap.SectorForest
