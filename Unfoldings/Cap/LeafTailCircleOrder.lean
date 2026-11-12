module

public import Unfoldings.Cap.GeometricChainSectors
public import Unfoldings.Cap.LeafCompletedTailTracking
public import Unfoldings.Cap.ParentPathCircleBankOrder
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.LeafTailCircleSeparation

/-! Actual strip-circle slices on opposite sides of a constructed leaf tail are disjoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)

/-- Once both facing endpoints are on the common actual leaf tail, geometric
tracking and named bank matching prove disjointness. The finite exceptional set
excludes mesh-vertex radii. No developed gap-order or curve-separation input is used. -/
theorem circle_tail_bank_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T : MonotoneStrip} {ε μ : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (close_margin : ε < μ)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_tail : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff S.upper)
    (last_tail : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff T.lower)
    (first_after : leaf.point.re + leaf.point.im ≤ first_slice.upperHeight)
    (last_after : leaf.point.re + leaf.point.im ≤ last_slice.lowerHeight) :
    (data.value (S.upper.point first_slice.upperHeight) - data.center).re ≤
        (other.value (T.lower.point last_slice.lowerHeight) - other.center).re ∧
      (other.value (T.lower.point last_slice.lowerHeight) - other.center).im ≤
        (data.value (S.upper.point first_slice.upperHeight) - data.center).im := by
  have first_height : first_slice.upperHeight ∈ Set.Icc (leaf.point.re + leaf.point.im) cutoff :=
    ⟨first_after, first_slice.upper_bounds.2⟩
  have last_height : last_slice.lowerHeight ∈ Set.Icc (leaf.point.re + leaf.point.im) cutoff :=
    ⟨last_after, last_slice.lower_bounds.2⟩
  obtain ⟨j, s, first_point⟩ := leaf.tailGraph_point_on_completed_path R outward w same_start
    footprint deep first_height
  obtain ⟨k, r, last_point⟩ := leaf.tailGraph_point_on_completed_path R outward w same_start
    footprint deep last_height
  have first_physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) = (R.completedRootPath w).point j s := by
    rw [first_tail.point_eq first_height, first_point, LinearIsometryEquiv.symm_apply_apply]
    abel
  have last_physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (T.lower.point last_slice.lowerHeight) = (R.completedRootPath w).point k r := by
    rw [last_tail.point_eq last_height, last_point, LinearIsometryEquiv.symm_apply_apply]
    abel
  obtain ⟨anchor, _, start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered positive small
    lower leaf.val leaf.property.1
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [same_start, M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨anchor, start⟩
  have first_regular := data.regular_of_radius_not_vertexRadii outside
    first_slice.upper_closed first_slice.upper_radius
  have last_regular := other.regular_of_radius_not_vertexRadii outside
    last_slice.lower_closed last_slice.lower_radius
  exact B.circle_parent_path_bank_order i data other close_margin first_margin last_margin
    radius_positive far first_slice last_slice w on_cuts
    (leaf.completed_bank_directions R outward w same_start)
    (leaf.completed_curved_subtree_sectors R outward w same_start curvature_covered)
    budget j k s r first_regular last_regular first_physical last_physical

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
