module

public import Unfoldings.Cap.ContactSeparatorCircleOrder
public import Unfoldings.Cap.ClosedLeafTailCircleContact

/-! Circle endpoint contact across an actual shared separator preserves the physical point. -/

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

/-- The constructed separator's coherent prefix and actual tail together separate
its adjacent open strip-circle images. No bank order or curve separation is assumed. -/
theorem closed_circle_contact_separator_same_point
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ v : M.GeometricSectorLeaf F covered positive small lower i,
      v.point.re + v.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail v.point v.tailGraph.graph cutoff G)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T : MonotoneStrip} {ε : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (traces : ∀ U ∈ P.cells, Nonempty (R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff))
    (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells)
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (first_wall : S.upper = H) (last_wall : Set.EqOn H.point T.lower.point (Set.Icc 0 cutoff))
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (first_pinches : S.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (last_pinches : T.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (same : data.value (S.upper.point first_slice.upperHeight) =
      other.value (T.lower.point last_slice.lowerHeight)) :
    (fiveSectorFrame t positive small i).place.symm (S.upper.point first_slice.upperHeight) =
      (fiveSectorFrame t positive small i).place.symm (T.lower.point last_slice.lowerHeight) := by
  have alternative := leaf.shared_separator_circle_prefix_alternative_of_contact R D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) deep P represented traces
    separator active completion leaf_coherent first_cell last_cell first_wall last_wall data other
    radius_positive first_slice last_slice
  rcases alternative with ⟨heights, _⟩ | ⟨first_after, last_after⟩
  · apply congrArg (fiveSectorFrame t positive small i).place.symm
    rw [first_wall, heights]
    exact last_wall last_slice.lower_bounds
  · exact leaf.closed_circle_tail_contact_same_point R outward w same_start footprint deep
      D B data other
      first_pinches last_pinches curvature_covered budget radius_positive far first_slice last_slice
      (first_wall.symm ▸ completion)
      (completion.of_point_eqOn (add_nonneg leaf.point_nonnegative.1 leaf.point_nonnegative.2)
        active last_wall) first_after.le last_after.le same

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
