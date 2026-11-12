module

public import Unfoldings.Cap.SharedSeparatorPrefixValue
public import Unfoldings.Cap.TerminalHeightLeafOrder

/-! Coherent separator prefixes and terminal-height bounds need only physical bank contact. -/

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

/-- A completed separator can contact either terminal bank throughout the
remaining slab without being the same globally extended height graph. -/
theorem le_permanent_terminal_height_of_contact {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {S : MonotoneStrip}
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    {H : MonotoneHeightGraph}
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (merged : ∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = S.upper.coordinate k)
    (contact : Set.EqOn H.point S.lower.point (Set.Icc h cutoff) ∨
      Set.EqOn H.point S.upper.point (Set.Icc h cutoff)) :
    leaf.point.re + leaf.point.im ≤ h := by
  obtain ⟨older, after_older, follows⟩ := tails h height merged
  apply leaf.le_height_of_completed_tail_agreement deep older after_older completion active
  intro k member
  rcases contact with contact | contact
  · exact (congrArg Complex.re (contact member)).trans (follows k member).1
  · exact (congrArg Complex.re (contact member)).trans (follows k member).2

/-- The root-sector interior supplies the geometric hypothesis directly;
no neighboring cell or equality of complete wall functions is required. -/
theorem separator_prefix_coherent
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
    {h : ℝ} (height : h ∈ Set.Icc 0 (leaf.point.re + leaf.point.im))
    (inside : H.point h ∈ (fiveSectorFrame t positive small i).enclosingStrip.strictCarrier) :
    D.ProjectedCoherentAt Q
      (K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm (H.point h)) := by
  let frame := (fiveSectorFrame t positive small i).place
  let E := {z : ℂ | D.ProjectedCoherentAt Q (K.projectedVertex origin + frame.symm z)}
  have pinches : ∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff := by
    intro S cell k slab collapsed m later width
    obtain ⟨trace⟩ := traces S cell
    have coherent := trace.pinches k slab collapsed m later width
    exact (trace.physical _ (Or.inr coherent) (by rw [S.lower.point_height]; exact slab)).2
  by_cases before : h < leaf.point.re + leaf.point.im
  · by_cases on_cut : K.projectedVertex origin + frame.symm (H.point h) ∈
        M.extendedGeometricCuts F
    · exact M.separator_prefix_cut_mem_coherent F covered positive small lower deep P
        represented pinches separator leaf active completion ⟨height.1, height.2.trans active⟩
        before inside on_cut
    · exact D.projected_coherentAt_of_not_cut Q
        (fun cut => on_cut (R.projectedCutSet_subset cut))
  · have equal : h = leaf.point.re + leaf.point.im :=
      le_antisymm height.2 (le_of_not_gt before)
    have target : H.point (leaf.point.re + leaf.point.im) = leaf.point :=
      H.point_eq_of_coordinate leaf.point
        ((completion.2 _ ⟨le_rfl, active⟩).trans leaf.tailGraph_target)
    have position : K.projectedVertex origin + frame.symm leaf.point =
        F.geometricPosition leaf.val := by
      change K.projectedVertex origin + frame.symm
        (frame (F.geometricPosition leaf.val - K.projectedVertex origin)) = _
      rw [frame.symm_apply_apply]
      abel
    rw [equal, target]
    exact position ▸ leaf_coherent

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
