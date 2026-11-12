module

public import Unfoldings.Cap.TerminalRunEarlyBoundsContacts

/-! Every maximal terminal, including either extreme tied copy, bounds an early circle crossing. -/

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
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches ordered_cells

/-- Equal physical terminal heights retain the actual subdivision order of
their approached copies, even when the physical points coincide. -/
theorem run_terminal_coordinates_order_of_equal_height (a b : Fin (n + 1))
    (ordered : a ≤ b) (same : (terminals a).height = (terminals b).height) :
    ((traces (cells a)).value ((cells a).val.lower.point (terminals a).height)).re ≤
        ((traces (cells b)).value ((cells b).val.lower.point (terminals b).height)).re ∧
      ((traces (cells b)).value ((cells b).val.lower.point (terminals b).height)).im ≤
        ((traces (cells a)).value ((cells a).val.lower.point (terminals a).height)).im := by
  rcases ordered.lt_or_eq with before | rfl
  · have included (k : Fin (n + 1)) :
        (cells k).val.openSlab 0 cutoff ⊆ (traces (cells k)).strictDomain :=
      fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
    have first_closed := closure_mono (included a) (terminals a).upper_closed
    have last_closed : (cells b).val.lower.point (terminals a).height ∈
        closure (traces (cells b)).strictDomain := by
      rw [same]
      exact closure_mono (included b) (terminals b).lower_closed
    have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P
      traces curvature_covered budget.le nonnegative small_error linear_error pinches
      (cells a) (cells b) (ordered_cells a b before) (terminals a).height_bounds
      first_closed last_closed
    have merged := (cells a).val.lower.point_eq_of_same_coordinate (cells a).val.upper
      ((terminals a).merged _ ⟨le_rfl, (terminals a).height_bounds.2.le⟩)
    have last_point := congrArg (cells b).val.lower.point same
    rw [← merged, last_point] at gap
    exact gap
  · exact ⟨le_rfl, le_rfl⟩


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

theorem early_upper_circle_re_le_any_run_maximum_of_contacts (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [source, cells k] P.cells.attach)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (separator : source.val.upper ∈ P.separators)
    (early : slice.upperHeight ≤ (terminals pivot).height) :
    ((traces source).value (source.val.upper.point slice.upperHeight)).re ≤
      ((traces (cells pivot)).value
        ((cells pivot).val.lower.point (terminals pivot).height)).re := by
  obtain ⟨firstMax, maximum, strict_before⟩ :=
    exists_first_max_position (fun k => (terminals k).height)
  have same : (terminals firstMax).height = (terminals pivot).height :=
    le_antisymm (highest firstMax) (maximum pivot)
  have before : firstMax ≤ pivot := by
    by_contra reversed
    exact (not_lt_of_ge (highest firstMax)) (strict_before pivot (not_le.mp reversed))
  have initial := early_upper_circle_re_le_first_run_maximum_of_contacts R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches cells contacts ordered_cells terminals tails provenance represented
    leaf_coherent source slice radius_positive far outside outside_empty empty firstMax
    strict_before source_order wall separator (early.trans_eq same.symm)
  have tied := run_terminal_coordinates_order_of_equal_height R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    cells ordered_cells terminals firstMax pivot before same
  exact initial.trans tied.1

theorem early_lower_circle_im_le_any_run_maximum_of_contacts (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [cells k, source] P.cells.attach)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff))
    (separator : source.val.lower ∈ P.separators)
    (early : slice.lowerHeight ≤ (terminals pivot).height) :
    ((traces source).value (source.val.lower.point slice.lowerHeight)).im ≤
      ((traces (cells pivot)).value
        ((cells pivot).val.lower.point (terminals pivot).height)).im := by
  obtain ⟨_, lastMax, _, first_last, first_maximum, _, strict_after⟩ :=
    exists_first_last_max_positions (fun k => (terminals k).height)
  have maximum (k : Fin (n + 1)) : (terminals k).height ≤ (terminals lastMax).height :=
    (first_maximum k).trans_eq first_last
  have same : (terminals pivot).height = (terminals lastMax).height :=
    le_antisymm (maximum pivot) (highest lastMax)
  have before : pivot ≤ lastMax := by
    by_contra reversed
    exact (not_lt_of_ge (highest lastMax)) (strict_after pivot (not_le.mp reversed))
  have initial := early_lower_circle_im_le_last_run_maximum_of_contacts R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches cells contacts ordered_cells terminals tails provenance represented
    leaf_coherent source slice radius_positive far outside outside_empty empty lastMax strict_after
    source_order wall separator (early.trans_eq same)
  have tied := run_terminal_coordinates_order_of_equal_height R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    cells ordered_cells terminals pivot lastMax before same
  exact initial.trans tied.2

end Unfoldings.ConvexCap.SectorForest

