module

public import Unfoldings.Roof.TerminalRunRecordsContacts
public import Unfoldings.Roof.EarlyCircleTerminalPrefixContacts
public import Unfoldings.Roof.EmptyNeighborContactPrefix
public import Unfoldings.Roof.GeometricTailTraceOrder
public import Unfoldings.Topology.FiniteMaxPositions
public import Unfoldings.Geometry.StripBankChain
public import Unfoldings.Topology.FiniteRecordProgress

/-! Early circle crossings are bounded by extreme terminal maxima of a disappearing run. -/

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
    (nonnegative : 0 ≤ ε) (small_error : ε ≤ 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

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
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (outside_empty : ∀ k, radius ∉ (traces (cells k)).emptyCircleExceptions)
  (empty : ∀ k, (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells tails provenance represented
  leaf_coherent radius_positive far outside outside_empty empty

/-- The first threshold-crossing cell supplies the initial actual bound; strict
terminal records then propagate it to the first maximum of the whole run. -/
theorem early_upper_circle_re_le_first_run_maximum_of_contacts (pivot : Fin (n + 1))
    (strict_before : ∀ k : Fin (n + 1), k < pivot →
      (terminals k).height < (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [source, cells k] P.cells.attach)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (separator : source.val.upper ∈ P.separators)
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
      have after := leaf.upper_circle_after_empty_neighbor_leaf_of_contact R D B deep P represented
        (fun S member => ⟨traces ⟨S, member⟩⟩) active (leaf_coherent leaf)
        source.property (cells 0).property (traces source) (traces (cells 0)) (tails 0)
        (pinches (cells 0)) (terminals 0) radius_positive far outside (outside_empty 0)
        (empty 0) slice separator wall completion
      have height := ((traces source).circle_slice_heights radius_positive far slice).2
      have included : (cells 0).val.openSlab 0 cutoff ⊆ (traces (cells 0)).strictDomain :=
        fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
      have endpoint := closure_mono included (terminals 0).lower_closed
      have at_height := (traces (cells 0)).lower_bank_closed_before endpoint
        (by rw [(cells 0).val.lower.point_height]; exact ⟨height.1.le, reaches⟩)
      have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P
        traces curvature_covered budget.le nonnegative small_error linear_error pinches
        source (cells 0) (source_order 0) height slice.upper_closed at_height
      have agreement : Set.EqOn (cells 0).val.lower.point leaf.tailGraph.graph.point
          (Set.Icc slice.upperHeight (terminals 0).height) := by
        intro h member
        have slab : h ∈ Set.Icc 0 cutoff :=
          ⟨height.1.le.trans member.1, member.2.trans (terminals 0).height_bounds.2.le⟩
        exact (wall slab).symm.trans (source.val.upper.point_eq_of_same_coordinate
          leaf.tailGraph.graph (completion.2 h ⟨after.le.trans member.1, slab.2⟩))
      have progress := leaf.developed_bank_tail_interval_order R D B (traces (cells 0))
        (Or.inl rfl) after.le reaches
        ((terminals 0).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
        agreement endpoint
      exact gap.1.trans progress.1
    · exact upper_circle_re_le_after_terminal_prefix_of_contacts R outward D B leaf_vertices
        footprint deep P
        traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells contacts
        terminals tails source slice radius_positive far j
        (lt_of_le_of_ne (Nat.zero_le _) (Ne.symm zero)) (source_order j) reaches earlier
  have records := terminal_re_le_at_first_maximum_of_contacts R outward D B leaf_vertices
    footprint deep P
    traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells contacts
    ordered_cells terminals tails j pivot before_pivot (fun k _ before => strict_before k before)
  exact initial.trans records

/-- Processing threshold crossings and strict terminal records from the right
gives the matching vertical bound at the run's last maximum. -/
theorem early_lower_circle_im_le_last_run_maximum_of_contacts (pivot : Fin (n + 1))
    (strict_after : ∀ k : Fin (n + 1), pivot < k →
      (terminals k).height < (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [cells k, source] P.cells.attach)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff))
    (separator : source.val.lower ∈ P.separators)
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
      have after := leaf.lower_circle_after_empty_neighbor_leaf_of_contact R D B deep P represented
        (fun S member => ⟨traces ⟨S, member⟩⟩) active (leaf_coherent leaf)
        source.property (cells (Fin.last n)).property (traces source)
        (traces (cells (Fin.last n))) (tails (Fin.last n)) (pinches (cells (Fin.last n)))
        (terminals (Fin.last n)) radius_positive far outside (outside_empty (Fin.last n))
        (empty (Fin.last n)) slice separator wall completion
      have height := ((traces source).circle_slice_heights radius_positive far slice).1
      have included : (cells (Fin.last n)).val.openSlab 0 cutoff ⊆
          (traces (cells (Fin.last n))).strictDomain :=
        fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
      have endpoint := closure_mono included (terminals (Fin.last n)).upper_closed
      have at_height := (traces (cells (Fin.last n))).upper_bank_closed_before endpoint
        (by rw [(cells (Fin.last n)).val.upper.point_height]; exact ⟨height.1.le, reaches⟩)
      have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P
        traces curvature_covered budget.le nonnegative small_error linear_error pinches
        (cells (Fin.last n)) source (source_order (Fin.last n)) height at_height slice.lower_closed
      have agreement : Set.EqOn (cells (Fin.last n)).val.upper.point leaf.tailGraph.graph.point
          (Set.Icc slice.lowerHeight (terminals (Fin.last n)).height) := by
        intro h member
        have slab : h ∈ Set.Icc 0 cutoff :=
          ⟨height.1.le.trans member.1, member.2.trans (terminals (Fin.last n)).height_bounds.2.le⟩
        exact (wall slab).symm.trans (source.val.lower.point_eq_of_same_coordinate
          leaf.tailGraph.graph (completion.2 h ⟨after.le.trans member.1, slab.2⟩))
      have progress := leaf.developed_bank_tail_interval_order R D B (traces (cells (Fin.last n)))
        (Or.inr rfl) after.le reaches
        ((terminals (Fin.last n)).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
        agreement endpoint
      have merged := (cells (Fin.last n)).val.lower.point_eq_of_same_coordinate
        (cells (Fin.last n)).val.upper ((terminals (Fin.last n)).merged
          (terminals (Fin.last n)).height ⟨le_rfl, (terminals (Fin.last n)).height_bounds.2.le⟩)
      rw [← merged] at progress
      exact gap.2.trans progress.2
    · exact lower_circle_im_le_before_terminal_suffix_of_contacts R outward D B leaf_vertices
        footprint deep P
        traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells contacts
        terminals tails source slice radius_positive far j
        (lt_of_le_of_ne (Fin.le_last j) last) (source_order j) reaches later
  have records := terminal_im_le_at_last_maximum_of_contacts R outward D B leaf_vertices
    footprint deep P
    traces curvature_covered budget.le nonnegative small_error linear_error pinches
        cells contacts
    ordered_cells terminals tails j pivot after_pivot (fun k after _ => strict_after k after)
  exact initial.trans records

end Unfoldings.ConvexRoof.SectorForest
