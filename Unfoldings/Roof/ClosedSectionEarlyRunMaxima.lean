module

public import Unfoldings.Roof.ClosedSectionEarlyRunBounds
public import Unfoldings.Roof.TerminalRunEarlyMaximaContacts
public import Unfoldings.Cap.ClosedBankPropertyLimit
public import Unfoldings.Cap.ClosedBankCircleCrossing
public import Unfoldings.Cap.ClosedEmptyCircleRunRadiusGap
public import Unfoldings.Cap.TerminalHeightUniqueness
public import Unfoldings.Cap.RadialClosedCircleSections

/-! Early terminal bounds persist at every closed circle section, including vertex radii. -/

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
  (slice : source.val.ClosedBankCircleSection
    (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (empty : ∀ k, (traces (cells k)).value '' closure ((cells k).val.openSlab 0 cutoff) ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)
  (continuations : ∀ r ∈ Set.Ioo 0 radius, ∀ k,
    r ∉ (traces (cells k)).emptyCircleExceptions →
    (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
      {z | ‖z - (traces (cells k)).center‖ = r} = ∅ →
    Nonempty (B.EmptyCircleContinuation i (traces (cells k)) physicalRadius r))


include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells tails provenance represented
  leaf_coherent radius_positive far empty continuations

/-- Closed early upper bounds hold at any chosen maximum, including tied terminals. -/
theorem closed_section_early_upper_re_le_any_run_maximum
    {μ : ℝ} (close_margin : ε < μ)
    (margin : ∀ z ∈ source.val.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (pivot : Fin (n + 1))
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
  have initial := closed_section_early_upper_re_le_first_run_maximum R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches cells contacts ordered_cells terminals tails provenance represented
    leaf_coherent source slice radius_positive far empty continuations close_margin margin firstMax
    strict_before source_order wall separator (early.trans_eq same.symm)
  have tied := run_terminal_coordinates_order_of_equal_height R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    cells ordered_cells terminals firstMax pivot before same
  exact initial.trans tied.1

/-- Closed early bounds hold at any chosen maximum, including tied terminals. -/
theorem closed_section_early_lower_im_le_any_run_maximum
    {μ : ℝ} (close_margin : ε < μ)
    (margin : ∀ z ∈ source.val.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (pivot : Fin (n + 1))
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
  have initial := closed_section_early_lower_im_le_last_run_maximum R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches cells contacts ordered_cells terminals tails provenance represented
    leaf_coherent source slice radius_positive far empty continuations close_margin margin
      lastMax strict_after
    source_order wall separator (early.trans_eq same)
  have tied := run_terminal_coordinates_order_of_equal_height R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    cells ordered_cells terminals pivot lastMax before same
  exact initial.trans tied.2

end Unfoldings.ConvexRoof.SectorForest
