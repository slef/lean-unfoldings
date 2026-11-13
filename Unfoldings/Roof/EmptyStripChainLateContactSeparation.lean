module

public import Unfoldings.Roof.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.ParentPathCircleBankOrder
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Geometry.StripBankContacts

/-! Separate surviving circle slices beyond a finite chain of permanently collapsed strips. -/

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

/-- Every intervening strip is retained in its physical wall chain. Once all
those banks have merged, an actual terminal copy supplies the common fine path
and named bank order; no auxiliary curve avoidance is needed. -/
theorem circle_banks_order_after_terminal_strip_chain_of_contacts
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T U : MonotoneStrip} {ε μ cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (middle : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
    (tails : U.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (nonnegative : 0 ≤ ε) (_small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (_linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    {n : ℕ} (cells : Fin (n + 1) → MonotoneStrip)
    (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
      (cells j.succ).lower.point (Set.Icc 0 cutoff))
    (pivot : Fin (n + 1)) (pivot_cell : cells pivot = U)
    (first_wall : Set.EqOn S.upper.point (cells 0).lower.point (Set.Icc 0 cutoff))
    (last_wall : Set.EqOn T.lower.point (cells (Fin.last n)).upper.point (Set.Icc 0 cutoff))
    (merged : ∀ j, ∀ h ∈ Set.Icc continuation.height cutoff,
      (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (first_after : continuation.height ≤ first_slice.upperHeight)
    (last_after : continuation.height ≤ last_slice.lowerHeight) :
    (data.value (S.upper.point first_slice.upperHeight) - data.center).re ≤
        (other.value (T.lower.point last_slice.lowerHeight) - other.center).re ∧
      (other.value (T.lower.point last_slice.lowerHeight) - other.center).im ≤
        (data.value (S.upper.point first_slice.upperHeight) - data.center).im := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B middle tails continuation
  have before_end := continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    continuation.vertex after_leaf before_end same_start curvature_covered
  have tracked := terminal_banks_on_completed_path R outward D B middle tails continuation
    footprint deep
  obtain ⟨j, s, _, first_point⟩ := tracked first_slice.upperHeight
    ⟨first_after, first_slice.upper_bounds.2⟩
  obtain ⟨k, r, last_point, _⟩ := tracked last_slice.lowerHeight
    ⟨last_after, last_slice.lower_bounds.2⟩
  have first_equal := MonotoneStrip.collapsed_chain_points_of_contacts cells
    (fun a => congrArg Complex.re (contacts a first_slice.upper_bounds))
    (fun a => merged a first_slice.upperHeight ⟨first_after, first_slice.upper_bounds.2⟩)
    0 pivot
  have last_equal := MonotoneStrip.collapsed_chain_points_of_contacts cells
    (fun a => congrArg Complex.re (contacts a last_slice.lower_bounds))
    (fun a => merged a last_slice.lowerHeight ⟨last_after, last_slice.lower_bounds.2⟩)
    pivot (Fin.last n)
  rw [pivot_cell] at first_equal last_equal
  have first_physical : origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) =
        (R.completedRootPath continuation.vertex).point j s := by
    rw [first_wall first_slice.upper_bounds, first_equal]
    exact first_point
  have last_physical : origin + (fiveSectorFrame t positive small i).place.symm
      (T.lower.point last_slice.lowerHeight) =
        (R.completedRootPath continuation.vertex).point k r := by
    rw [last_wall last_slice.lower_bounds, ← last_equal]
    exact last_point
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  exact B.circle_parent_path_bank_order i data other close_margin first_margin last_margin
    radius_positive far first_slice last_slice continuation.vertex continuation.on_cuts
    directions sectors budget j k s r
    (data.regular_of_radius_not_vertexRadii outside
      first_slice.upper_closed first_slice.upper_radius)
    (other.regular_of_radius_not_vertexRadii outside
      last_slice.lower_closed last_slice.lower_radius)
    first_physical last_physical

/-- Every intervening strip is retained in its physical wall chain. Once all
those banks have merged, an actual terminal copy supplies the common fine path
and named bank order; no auxiliary curve avoidance is needed. -/
theorem circle_slices_disjoint_after_terminal_strip_chain_of_contacts
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T U : MonotoneStrip} {ε μ cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (middle : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
    (tails : U.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    {n : ℕ} (cells : Fin (n + 1) → MonotoneStrip)
    (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
      (cells j.succ).lower.point (Set.Icc 0 cutoff))
    (pivot : Fin (n + 1)) (pivot_cell : cells pivot = U)
    (first_wall : Set.EqOn S.upper.point (cells 0).lower.point (Set.Icc 0 cutoff))
    (last_wall : Set.EqOn T.lower.point (cells (Fin.last n)).upper.point (Set.Icc 0 cutoff))
    (merged : ∀ j, ∀ h ∈ Set.Icc continuation.height cutoff,
      (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (first_after : continuation.height ≤ first_slice.upperHeight)
    (last_after : continuation.height ≤ last_slice.lowerHeight) :
    Disjoint (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius})
      (other.value '' T.openSlab 0 cutoff ∩ {z | ‖z - other.center‖ = radius}) := by
  have gap := circle_banks_order_after_terminal_strip_chain_of_contacts R outward D B data other
    middle tails continuation footprint deep nonnegative small_error numerical linear_error
    first_margin last_margin curvature_covered budget radius_positive far outside first_slice
    last_slice cells contacts pivot pivot_cell first_wall last_wall merged first_after last_after
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have first_order := data.bank_circle_order nonnegative small_error numerical linear_error
    first_margin radius_positive first_slice.lower_closed first_slice.upper_closed
    first_slice.lower_radius first_slice.upper_radius first_slice.distinct
  have last_order := other.bank_circle_order nonnegative small_error numerical linear_error
    last_margin radius_positive last_slice.lower_closed last_slice.upper_closed
    last_slice.lower_radius last_slice.upper_radius last_slice.distinct
  apply first_slice.disjoint_circle_images_of_bank_order last_slice first_order.1 last_order.1 gap.1
  rintro z ⟨p, member, rfl⟩
  exact data.strict_quadrant_of_margin close_margin first_margin member

end Unfoldings.ConvexRoof.SectorForest
