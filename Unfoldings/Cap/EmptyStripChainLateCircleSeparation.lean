module

public import Unfoldings.Cap.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.ParentPathCircleBankOrder
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Geometry.StripBankChain

/-! Separate surviving circle slices beyond a finite chain of permanently collapsed strips. -/

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

/-- Every intervening strip is retained in its physical wall chain. Once all
those banks have merged, an actual terminal copy supplies the common fine path
and named bank order; no auxiliary curve avoidance is needed. -/
theorem circle_slices_disjoint_after_terminal_strip_chain
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
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
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
    (footprint : Q.footprint = K.clipFootprint Z)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
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
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    {n : ℕ} (cells : Fin (n + 1) → MonotoneStrip)
    (adjacent : ∀ j : Fin n, (cells j.castSucc).upper = (cells j.succ).lower)
    (pivot : Fin (n + 1)) (pivot_cell : cells pivot = U)
    (first_wall : S.upper = (cells 0).lower)
    (last_wall : T.lower = (cells (Fin.last n)).upper)
    (merged : ∀ j, ∀ h ∈ Set.Icc continuation.height cutoff,
      (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (first_after : continuation.height ≤ first_slice.upperHeight)
    (last_after : continuation.height ≤ last_slice.lowerHeight) :
    Disjoint (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius})
      (other.value '' T.openSlab 0 cutoff ∩ {z | ‖z - other.center‖ = radius}) := by
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
  have first_equal := MonotoneStrip.collapsed_chain_bank_points cells adjacent
    (fun a => merged a first_slice.upperHeight ⟨first_after, first_slice.upper_bounds.2⟩)
    0 pivot
  have last_equal := MonotoneStrip.collapsed_chain_bank_points cells adjacent
    (fun a => merged a last_slice.lowerHeight ⟨last_after, last_slice.lower_bounds.2⟩)
    pivot (Fin.last n)
  rw [pivot_cell] at first_equal last_equal
  have first_physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) =
        (R.completedRootPath continuation.vertex).point j s := by
    rw [first_wall, first_equal]
    exact first_point
  have last_physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (T.lower.point last_slice.lowerHeight) =
        (R.completedRootPath continuation.vertex).point k r := by
    rw [last_wall, ← last_equal]
    exact last_point
  exact B.circle_parent_path_slices_disjoint i data other nonnegative small_error numerical
    linear_error first_margin last_margin radius_positive far first_slice last_slice
    continuation.vertex continuation.on_cuts directions sectors budget j k s r
    (data.regular_of_radius_not_vertexRadii outside
      first_slice.upper_closed first_slice.upper_radius)
    (other.regular_of_radius_not_vertexRadii outside
      last_slice.lower_closed last_slice.lower_radius)
    first_physical last_physical

end Unfoldings.ConvexCap.SectorForest
