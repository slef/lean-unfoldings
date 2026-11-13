module

public import Unfoldings.Roof.SharedSeparatorCirclePrefix
public import Unfoldings.Roof.LeafTailCircleSeparation

/-! Actual adjacent developed strip-circle slices are disjoint across their shared separator. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain origin}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small i)

/-- The constructed separator's coherent prefix and actual tail together separate
its adjacent open strip-circle images. No bank order or curve separation is assumed. -/
theorem circle_shared_separator_slices_disjoint
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest origin (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall origin cutoff ⊆ interior (outerDomain))
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
    (first_wall : S.upper = H) (last_wall : T.lower = H)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
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
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q origin
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius) :
    Disjoint (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius})
      (other.value '' T.openSlab 0 cutoff ∩ {z | ‖z - other.center‖ = radius}) := by
  have alternative := leaf.shared_separator_circle_prefix_alternative R D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) deep P represented traces
    separator active completion leaf_coherent first_cell last_cell first_wall last_wall data other
    radius_positive first_slice last_slice
  rcases alternative with ⟨_, equal⟩ | ⟨first_after, last_after⟩
  · have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
    have first_order := data.bank_circle_order nonnegative small_error numerical linear_error
      first_margin radius_positive first_slice.lower_closed first_slice.upper_closed
      first_slice.lower_radius first_slice.upper_radius first_slice.distinct
    have last_order := other.bank_circle_order nonnegative small_error numerical linear_error
      last_margin radius_positive last_slice.lower_closed last_slice.upper_closed
      last_slice.lower_radius last_slice.upper_radius last_slice.distinct
    apply first_slice.disjoint_circle_images_of_bank_order last_slice first_order.1 last_order.1
    · exact (congrArg (fun z : ℂ => (z - data.center).re) equal).le
    · rintro z ⟨p, member, rfl⟩
      exact data.strict_quadrant_of_margin close_margin first_margin member
  · exact leaf.circle_tail_slices_disjoint R outward w same_start footprint deep D B data other
      nonnegative small_error numerical linear_error first_margin last_margin curvature_covered
      budget
      radius_positive far outside first_slice last_slice (first_wall.symm ▸ completion)
      (last_wall.symm ▸ completion) first_after.le last_after.le

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
