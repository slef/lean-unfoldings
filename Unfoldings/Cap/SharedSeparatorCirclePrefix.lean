module

public import Unfoldings.Cap.GeometricSeparatorPrefix
public import Unfoldings.Cap.SharedBankCirclePrefix
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Actual adjacent circle endpoints agree before their shared separator's leaf. -/

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

/-- The actual strip data supply the subdivision's coherent pinch invariant.
Wall-contact geometry then proves equality on the tested common prefix, including
possible isolated pinches and contacts with the exterior sector rays. -/
theorem shared_separator_circle_prefix_alternative
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain) (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
    {cutoff ε : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G)
    (traces : ∀ S ∈ P.cells, Nonempty
      (R.RadialStripTraceData positive small D calibration i S ε cutoff))
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {S T : MonotoneStrip} (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells)
    (first_wall : S.upper = H) (last_wall : T.lower = H)
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
  let frame := (fiveSectorFrame t positive small i).place
  let E := {z : ℂ | D.ProjectedCoherentAt Q (K.projectedVertex origin + frame.symm z)}
  have pinches : ∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff := by
    intro S cell h slab collapsed k later width
    obtain ⟨trace⟩ := traces S cell
    have coherent := trace.pinches h slab collapsed k later width
    exact (trace.physical _ (Or.inr coherent) (by rw [S.lower.point_height]; exact slab)).2
  have leaf_member : leaf.point ∈ E := by
    have position : K.projectedVertex origin + frame.symm leaf.point =
        F.geometricPosition leaf.val := by
      change K.projectedVertex origin + frame.symm
        (frame (F.geometricPosition leaf.val - K.projectedVertex origin)) = _
      rw [frame.symm_apply_apply]
      abel
    change D.ProjectedCoherentAt Q (K.projectedVertex origin + frame.symm leaf.point)
    rw [position]
    exact leaf_coherent
  have first_width := (data.circle_slice_width radius_positive first_slice).2
  have last_width := (other.circle_slice_width radius_positive last_slice).1
  apply data.circle_bank_prefix_alternative other (leaf.point.re + leaf.point.im) _
    first_slice.upper_bounds.1 last_slice.lower_bounds.1 radius_positive
    first_slice.upper_closed last_slice.lower_closed first_slice.upper_radius
    last_slice.lower_radius
  intro h height before_first before_last first_closed last_closed
  have geometric := M.shared_separator_prefix_uncut_or_coherent F covered positive small lower
    deep P represented pinches separator leaf active completion leaf_member first_cell last_cell
    first_wall last_wall height ⟨before_first, first_slice.upper_bounds.2⟩ first_width
    ⟨before_last, last_slice.lower_bounds.2⟩ last_width
  have coherent : D.ProjectedCoherentAt Q (K.projectedVertex origin + frame.symm (H.point h)) := by
    rcases geometric with coherent | outside
    · exact coherent
    · exact D.projected_coherentAt_of_not_cut Q (fun cut => outside (R.projectedCutSet_subset cut))
  rw [← first_wall] at coherent
  exact data.shared_bank_value_of_coherent other (first_wall.trans last_wall.symm)
    first_closed last_closed coherent

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
