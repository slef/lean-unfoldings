module

public import Unfoldings.Roof.ContactSeparatorValues
public import Unfoldings.Cap.SharedBankCirclePrefix
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Actual adjacent circle endpoints agree before their shared separator's leaf. -/

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

/-- The actual strip data supply the subdivision's coherent pinch invariant.
Wall-contact geometry then proves equality on the tested common prefix, including
possible isolated pinches and contacts with the exterior sector rays. -/
theorem shared_separator_circle_prefix_alternative_of_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain) (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
    {cutoff ε : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ w : M.GeometricSectorLeaf F covered positive small i,
      w.point.re + w.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G)
    (traces : ∀ S ∈ P.cells, Nonempty
      (R.RadialStripTraceData positive small D calibration i S ε cutoff))
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {S T : MonotoneStrip} (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells)
    (first_wall : S.upper = H) (last_wall : Set.EqOn H.point T.lower.point (Set.Icc 0 cutoff))
    (data : R.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : R.RadialStripTraceData positive small D calibration i T ε cutoff)
    {radius : ℝ} (radius_positive : 0 < radius)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius) :
    (first_slice.upperHeight = last_slice.lowerHeight ∧
      data.value (S.upper.point first_slice.upperHeight) =
        other.value (T.lower.point last_slice.lowerHeight)) ∨
      (leaf.point.re + leaf.point.im < first_slice.upperHeight ∧
        leaf.point.re + leaf.point.im < last_slice.lowerHeight) := by
  have first_width := (data.circle_slice_width radius_positive first_slice).2
  have last_width := (other.circle_slice_width radius_positive last_slice).1
  apply data.circle_bank_prefix_alternative other (leaf.point.re + leaf.point.im) _
    first_slice.upper_bounds.1 last_slice.lower_bounds.1 radius_positive
    first_slice.upper_closed last_slice.lower_closed first_slice.upper_radius
    last_slice.lower_radius
  intro h height before_first before_last first_closed last_closed
  exact leaf.shared_separator_prefix_value_of_contact R D calibration deep P represented traces
    separator
    active completion leaf_coherent first_cell last_cell first_wall last_wall data other height
    ⟨before_first, first_slice.upper_bounds.2⟩ first_width
    ⟨before_last, last_slice.lower_bounds.2⟩ last_width first_closed last_closed

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
