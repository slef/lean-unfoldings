module

public import Unfoldings.Cap.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.PositiveWidthBankStartOrder
public import Unfoldings.Cap.RadialStripCircleComparison
public import Unfoldings.Cap.RegularCircleRadius

/-! Late circle crossings progress beyond an intermediate strip's actual terminal copy. -/

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
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
  (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
  {S U : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
  (data : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (middle : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
  (tails : U.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
  (footprint : Q.footprint = K.clipFootprint Z)
  (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
  (curvature_covered : ∀ v : FineC.Vertex Set.univ,
    0 < FineC.interiorAngularDefect Set.univ v →
      Q.projectedVertex v ∈ M.extendedGeometricCuts F)
  (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)

include outward tails footprint deep curvature_covered budget radius_positive far outside

/-- A late entrance crossing lies to the right of the disappearing strip's
own terminal copy. Straight gap segments are handled by their proved signs. -/
theorem terminal_re_le_late_lower_circle
    (wall : S.lower = U.upper) (late : continuation.height ≤ slice.lowerHeight) :
    (middle.value (U.lower.point continuation.height)).re ≤
      (data.value (S.lower.point slice.lowerHeight)).re := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B middle tails continuation
  have before_end := continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    continuation.vertex after_leaf before_end same_start curvature_covered
  obtain ⟨j, s, _, tracked⟩ := terminal_banks_on_completed_path R outward D B middle tails
    continuation footprint deep slice.lowerHeight ⟨late, slice.lower_bounds.2⟩
  have physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) =
        (R.completedRootPath continuation.vertex).point j s := by
    rw [wall]
    exact tracked
  have bound := B.lower_bank_start_order i continuation.vertex continuation.on_cuts
    continuation.target continuation.original directions sectors budget data
    (data.circle_slice_heights radius_positive far slice).1
    (data.circle_slice_width radius_positive slice).1 j s
    (data.regular_of_radius_not_vertexRadii outside slice.lower_closed slice.lower_radius) physical
  rw [← continuation.value] at bound
  exact bound

/-- A late exit crossing lies above the same actual terminal copy. -/
theorem terminal_im_le_late_upper_circle
    (wall : S.upper = U.lower) (late : continuation.height ≤ slice.upperHeight) :
    (middle.value (U.lower.point continuation.height)).im ≤
      (data.value (S.upper.point slice.upperHeight)).im := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B middle tails continuation
  have before_end := continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    continuation.vertex after_leaf before_end same_start curvature_covered
  obtain ⟨j, s, tracked, _⟩ := terminal_banks_on_completed_path R outward D B middle tails
    continuation footprint deep slice.upperHeight ⟨late, slice.upper_bounds.2⟩
  have physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) =
        (R.completedRootPath continuation.vertex).point j s := by
    rw [wall]
    exact tracked
  have bound := B.upper_bank_start_order i continuation.vertex continuation.on_cuts
    continuation.target continuation.original directions sectors budget data
    (data.circle_slice_heights radius_positive far slice).2
    (data.circle_slice_width radius_positive slice).2 j s
    (data.regular_of_radius_not_vertexRadii outside slice.upper_closed slice.upper_radius) physical
  rw [← continuation.value] at bound
  exact bound

end Unfoldings.ConvexCap.SectorForest
