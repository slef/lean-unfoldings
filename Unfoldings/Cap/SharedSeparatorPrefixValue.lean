module

public import Unfoldings.Cap.GeometricSeparatorPrefix
public import Unfoldings.Cap.SharedBankCirclePrefix
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Actual developed traces agree on a separator's approached coherent prefix. -/

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

/-- Positive width may be witnessed at different later heights on the two
sides. Neither trace is required to meet a specified source circle. -/
theorem shared_separator_prefix_value
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
    {h a b : ℝ} (height : h ∈ Set.Icc 0 (leaf.point.re + leaf.point.im))
    (first_later : a ∈ Set.Icc h cutoff)
    (first_width : S.lower.coordinate a < S.upper.coordinate a)
    (last_later : b ∈ Set.Icc h cutoff)
    (last_width : T.lower.coordinate b < T.upper.coordinate b)
    (first_closed : S.upper.point h ∈ closure data.strictDomain)
    (last_closed : T.lower.point h ∈ closure other.strictDomain) :
    data.value (S.upper.point h) = other.value (T.lower.point h) := by
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
  have geometric := M.shared_separator_prefix_uncut_or_coherent F covered positive small lower
    deep P represented pinches separator leaf active completion leaf_member first_cell last_cell
    first_wall last_wall height first_later first_width last_later last_width
  have coherent : D.ProjectedCoherentAt Q (K.projectedVertex origin + frame.symm (H.point h)) := by
    rcases geometric with coherent | outside
    · exact coherent
    · exact D.projected_coherentAt_of_not_cut Q (fun cut => outside (R.projectedCutSet_subset cut))
  rw [← first_wall] at coherent
  exact data.shared_bank_value_of_coherent other (first_wall.trans last_wall.symm)
    first_closed last_closed coherent

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
