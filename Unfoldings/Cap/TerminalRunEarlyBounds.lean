module

public import Unfoldings.Cap.TerminalRunRecords
public import Unfoldings.Cap.EarlyCircleTerminalPrefix
public import Unfoldings.Cap.EmptyNeighborCirclePrefix
public import Unfoldings.Cap.EarlyTerminalBankOrder
public import Unfoldings.Topology.FiniteMaxPositions
public import Unfoldings.Geometry.StripBankChain
public import Unfoldings.Topology.FiniteRecordProgress

/-! Early circle crossings are bounded by extreme terminal maxima of a disappearing run. -/

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
    (nonnegative : 0 ≤ ε) (small_error : ε ≤ 1 / 2)
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
  (adjacent : ∀ j : Fin n, (cells j.castSucc).val.upper = (cells j.succ).val.lower)
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
  small_error linear_error pinches adjacent ordered_cells tails provenance represented
  leaf_coherent radius_positive far outside outside_empty empty

/-- The first threshold-crossing cell supplies the initial actual bound; strict
terminal records then propagate it to the first maximum of the whole run. -/
theorem early_upper_circle_re_le_first_run_maximum (pivot : Fin (n + 1))
    (strict_before : ∀ k : Fin (n + 1), k < pivot →
      (terminals k).height < (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [source, cells k] P.cells.attach)
    (wall : source.val.upper = (cells 0).val.lower)
    (separator : (cells 0).val.lower ∈ P.separators)
    (early : slice.upperHeight ≤ (terminals pivot).height) :
    ((traces source).value (source.val.upper.point slice.upperHeight)).re ≤
      ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).re
    := by
  obtain ⟨j, before_pivot, reaches, earlier⟩ := exists_first_ge_position
    (fun k => (terminals k).height) slice.upperHeight pivot early
  have initial : ((traces source).value (source.val.upper.point slice.upperHeight)).re ≤
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).re := by
    by_cases zero : j = 0
    · subst j
      obtain ⟨leaf, active, completion⟩ := provenance _ separator
      obtain ⟨w, position⟩ := leaf_vertices leaf
      have after := leaf.upper_circle_after_empty_neighbor_leaf R D B deep P represented
        (fun S member => ⟨traces ⟨S, member⟩⟩) active (leaf_coherent leaf)
        source.property (cells 0).property (traces source) (traces (cells 0)) (tails 0)
        (pinches (cells 0)) (terminals 0) radius_positive far outside (outside_empty 0)
        (empty 0) slice separator wall completion
      exact leaf.upper_circle_le_terminal_re R outward w position footprint deep D B
        (traces source) (traces (cells 0)) (pinches (cells 0)) (terminals 0)
        curvature_covered budget radius_positive far outside slice wall completion after.le reaches
    · exact upper_circle_re_le_after_terminal_prefix R outward D B leaf_vertices footprint deep P
        traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells adjacent
        terminals tails source slice radius_positive far j
        (lt_of_le_of_ne (Nat.zero_le _) (Ne.symm zero)) (source_order j) reaches earlier
  have records := terminal_re_le_at_first_maximum R outward D B leaf_vertices footprint deep P
    traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells adjacent
    ordered_cells terminals tails j pivot before_pivot (fun k _ before => strict_before k before)
  exact initial.trans records

/-- Processing threshold crossings and strict terminal records from the right
gives the matching vertical bound at the run's last maximum. -/
theorem early_lower_circle_im_le_last_run_maximum (pivot : Fin (n + 1))
    (strict_after : ∀ k : Fin (n + 1), pivot < k →
      (terminals k).height < (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [cells k, source] P.cells.attach)
    (wall : source.val.lower = (cells (Fin.last n)).val.upper)
    (separator : (cells (Fin.last n)).val.upper ∈ P.separators)
    (early : slice.lowerHeight ≤ (terminals pivot).height) :
    ((traces source).value (source.val.lower.point slice.lowerHeight)).im ≤
      ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).im
    := by
  obtain ⟨j, after_pivot, reaches, later⟩ := exists_last_ge_position
    (fun k => (terminals k).height) slice.lowerHeight pivot early
  have initial : ((traces source).value (source.val.lower.point slice.lowerHeight)).im ≤
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).im := by
    by_cases last : j = Fin.last n
    · subst j
      obtain ⟨leaf, active, completion⟩ := provenance _ separator
      obtain ⟨w, position⟩ := leaf_vertices leaf
      have after := leaf.lower_circle_after_empty_neighbor_leaf R D B deep P represented
        (fun S member => ⟨traces ⟨S, member⟩⟩) active (leaf_coherent leaf)
        source.property (cells (Fin.last n)).property (traces source)
        (traces (cells (Fin.last n))) (tails (Fin.last n)) (pinches (cells (Fin.last n)))
        (terminals (Fin.last n)) radius_positive far outside (outside_empty (Fin.last n))
        (empty (Fin.last n)) slice separator wall completion
      exact leaf.lower_circle_le_terminal_im R outward w position footprint deep D B
        (traces source) (traces (cells (Fin.last n))) (pinches (cells (Fin.last n)))
        (terminals (Fin.last n)) curvature_covered budget radius_positive far outside slice
        wall.symm completion after.le reaches
    · exact lower_circle_im_le_before_terminal_suffix R outward D B leaf_vertices footprint deep P
        traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells adjacent
        terminals tails source slice radius_positive far j
        (lt_of_le_of_ne (Fin.le_last j) last) (source_order j) reaches later
  have records := terminal_im_le_at_last_maximum R outward D B leaf_vertices footprint deep P
    traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells adjacent
    ordered_cells terminals tails j pivot after_pivot (fun k after _ => strict_after k after)
  exact initial.trans records

end Unfoldings.ConvexCap.SectorForest

