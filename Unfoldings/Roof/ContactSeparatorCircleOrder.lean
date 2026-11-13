module

public import Unfoldings.Roof.ContactSeparatorCirclePrefix
public import Unfoldings.Geometry.TailContact
public import Unfoldings.Roof.LeafTailCircleOrder

/-! Actual adjacent developed strip-circle slices are disjoint across their shared separator. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small i)

/-- The constructed separator's coherent prefix and actual tail together separate
its adjacent open strip-circle images. No bank order or curve separation is assumed. -/
theorem circle_contact_separator_bank_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ v : M.GeometricSectorLeaf F covered positive small i,
      v.point.re + v.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail v.point v.tailGraph.graph cutoff G)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T : MonotoneStrip} {ε μ : ℝ}
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
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius) :
    (data.value (S.upper.point first_slice.upperHeight) - data.center).re ≤
        (other.value (T.lower.point last_slice.lowerHeight) - other.center).re ∧
      (other.value (T.lower.point last_slice.lowerHeight) - other.center).im ≤
        (data.value (S.upper.point first_slice.upperHeight) - data.center).im := by
  have alternative := leaf.shared_separator_circle_prefix_alternative_of_contact R D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) deep P represented traces
    separator active completion leaf_coherent first_cell last_cell first_wall last_wall data other
    radius_positive first_slice last_slice
  rcases alternative with ⟨_, equal⟩ | ⟨first_after, last_after⟩
  · exact ⟨(congrArg (fun z : ℂ => (z - data.center).re) equal).le,
      (congrArg (fun z : ℂ => (z - data.center).im) equal).symm.le⟩
  · exact leaf.circle_tail_bank_order R outward w same_start footprint deep D B data other
      close_margin first_margin last_margin curvature_covered budget radius_positive far outside
      first_slice last_slice (first_wall.symm ▸ completion)
      (completion.of_point_eqOn (add_nonneg leaf.point_nonnegative.1 leaf.point_nonnegative.2)
        active last_wall) first_after.le last_after.le

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
