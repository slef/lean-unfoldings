module

public import Unfoldings.Roof.EmptyStripRunContactSeparation
public import Unfoldings.Roof.ContactSeparatorCircleOrder
public import Unfoldings.Geometry.EmptyStripBanks
public import Unfoldings.Geometry.SubdivisionNonemptyCells
public import Unfoldings.Topology.IndexedRun

/-! Actual facing circle endpoints retain order across every removed physical-cell run. -/

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

variable {physicalRadius radius : ℝ}

variable (first last : {S : MonotoneStrip // S ∈ P.cells})
  (first_slice : first.val.BankCircleSlice (traces first).value (traces first).center cutoff radius)
  (last_slice : last.val.BankCircleSlice (traces last).value (traces last).center cutoff radius)
  {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (first_margin : ∀ z ∈ first.val.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (last_margin : ∀ z ∈ last.val.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)

variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    (traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius))
  (all_outside_empty : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    radius ∉ (traces cell).emptyCircleExceptions)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent first_slice last_slice
  numerical first_margin last_margin radius_positive far outside all_tails continuations
  all_outside_empty

/-- The run is taken in the actual ordered subdivision. Its cells may have
different globally extended walls; the physical contacts in the controlled
slab suffice, including when the removed run is empty. -/
theorem circle_banks_order_across_removed_run
    (middle : List {S : MonotoneStrip // S ∈ P.cells})
    (ordered : List.Sublist (first :: (middle ++ [last])) P.cells.attach)
    (contacts : (first :: (middle ++ [last])).IsChain (fun A B =>
      Set.EqOn A.val.upper.point B.val.lower.point (Set.Icc 0 cutoff)))
    (nonempty : ∀ cell ∈ middle, (cell.val.openSlab 0 cutoff).Nonempty)
    (empty : ∀ cell ∈ middle, (traces cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces cell).center‖ = radius} = ∅) :
    ((traces first).value (first.val.upper.point first_slice.upperHeight) -
        (traces first).center).re ≤
      ((traces last).value (last.val.lower.point last_slice.lowerHeight) -
        (traces last).center).re ∧
    ((traces last).value (last.val.lower.point last_slice.lowerHeight) -
        (traces last).center).im ≤
      ((traces first).value (first.val.upper.point first_slice.upperHeight) -
        (traces first).center).im := by
  classical
  cases middle with
  | nil =>
    have wall := contacts.rel
    obtain ⟨z, member, _⟩ := last.val.exists_openSlab_point_at_height
      ((traces last).circle_slice_heights radius_positive far last_slice).1
      ((traces last).circle_slice_width radius_positive last_slice).1
    have separator := P.upper_bank_separator_of_nonempty_contact first.property last.property
      wall ⟨z, member⟩
    obtain ⟨leaf, active, completion⟩ := provenance _ separator
    obtain ⟨w, position⟩ := leaf_vertices leaf
    have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
    exact leaf.circle_contact_separator_bank_order R outward w position footprint deep P represented
      D B (traces first) (traces last) (fun S member => ⟨traces ⟨S, member⟩⟩)
      first.property last.property separator rfl wall active completion (leaf_coherent leaf)
      close_margin first_margin last_margin curvature_covered budget radius_positive far outside
      first_slice last_slice
  | cons head tail =>
    let cells : Fin (tail.length + 1) → {S : MonotoneStrip // S ∈ P.cells} :=
      (head :: tail).get
    obtain ⟨adjacent, ordered_cells, first_order, last_order, first_wall, last_wall⟩ :=
      indexed_run_data P.cells.attach first head last tail ordered contacts
    have member (j : Fin (tail.length + 1)) : cells j ∈ head :: tail := List.get_mem _ _
    let terminals := fun j => Classical.choice
      (continuations (cells j) (empty (cells j) (member j)) (nonempty (cells j) (member j)))
    have first_separator := P.upper_bank_separator_of_nonempty_contact first.property
      (cells 0).property first_wall (nonempty (cells 0) (member 0))
    have last_separator := P.lower_bank_separator_of_nonempty_contact
      (cells (Fin.last tail.length)).property last.property last_wall
      (nonempty (cells (Fin.last tail.length)) (member (Fin.last tail.length)))
    exact circle_banks_order_across_empty_strip_run_of_contacts R outward D B leaf_vertices
      footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
      cells adjacent ordered_cells terminals (fun j => all_tails (cells j)) provenance represented
      leaf_coherent first last first_slice last_slice numerical first_margin last_margin
      radius_positive far outside (fun j => all_outside_empty (cells j))
      (fun j => empty (cells j) (member j)) first_order last_order first_wall
      (fun h member => (last_wall member).symm) first_separator last_separator

end Unfoldings.ConvexRoof.SectorForest
