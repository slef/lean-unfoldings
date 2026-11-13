module

public import Unfoldings.Roof.ClosedSharedSeparatorPrefixValue
public import Unfoldings.Roof.ClosedSectionTailContact
public import Unfoldings.Geometry.TailContact
public import Unfoldings.Roof.ClosedLeafTailCircleContact

/-! Circle endpoint contact across an actual shared separator preserves the physical point. -/

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
theorem closed_section_contact_separator_same_point
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
          (Q.projectedVertex v.val - origin))) 0 cutoff)
    (last_pinches : T.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    {radius : ℝ} (radius_positive : 0 < radius)
    (first_slice : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (last_slice : T.ClosedBankCircleSection other.value other.center cutoff radius)
    (same : data.value (S.upper.point first_slice.upperHeight) =
      other.value (T.lower.point last_slice.lowerHeight)) :
    (fiveSectorFrame t positive small i).place.symm (S.upper.point first_slice.upperHeight) =
      (fiveSectorFrame t positive small i).place.symm (T.lower.point last_slice.lowerHeight) := by
  have alternative := data.circle_bank_prefix_alternative other
    (leaf.point.re + leaf.point.im)
    (fun h height _ _ first_closed last_closed =>
      leaf.closed_shared_separator_prefix_value_of_contact R D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) deep P represented
        traces separator active completion leaf_coherent first_cell last_cell first_wall last_wall
        data other height first_closed last_closed)
    first_slice.upper_bounds.1 last_slice.lower_bounds.1 radius_positive
    first_slice.upper_closed last_slice.lower_closed first_slice.upper_radius
    last_slice.lower_radius
  rcases alternative with ⟨heights, _⟩ | ⟨first_after, last_after⟩
  · apply congrArg (fiveSectorFrame t positive small i).place.symm
    rw [first_wall, heights]
    exact last_wall last_slice.lower_bounds
  · exact leaf.closed_section_tail_contact_same_point R outward w same_start footprint deep
      D B data other
      first_pinches last_pinches curvature_covered budget first_slice last_slice
      (first_wall.symm ▸ completion)
      (completion.of_point_eqOn (add_nonneg leaf.point_nonnegative.1 leaf.point_nonnegative.2)
        active last_wall) first_after last_after same

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
