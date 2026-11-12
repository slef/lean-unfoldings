module

public import Unfoldings.Cap.GeometricTailLeaves
public import Unfoldings.Cap.GeometricTailCutoff
public import Unfoldings.Geometry.FiniteWaterfall
public import Unfoldings.Geometry.StripInsertionTerminalTail

/-! A permanently collapsed strip cannot end before a leaf completed by either bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)

/-- Agreement after a tested height suffices; the two complete wall functions
may differ below it. This also applies across several collapsed cells. -/
theorem le_height_of_completed_tail_agreement {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (older : M.GeometricSectorLeaf F covered positive small lower i)
    {h : ℝ} (after_older : older.point.re + older.point.im ≤ h)
    {H : MonotoneHeightGraph}
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (agreement : ∀ k ∈ Set.Icc h cutoff, H.coordinate k = older.tailGraph.graph.coordinate k) :
    leaf.point.re + leaf.point.im ≤ h := by
  by_contra before_leaf
  have before : h < leaf.point.re + leaf.point.im := not_le.mp before_leaf
  have different : older.val ≠ leaf.val := by
    intro equal
    have same : older = leaf := Subtype.ext equal
    subst older
    exact (not_le_of_gt before) after_older
  have avoids := older.tailGraph.leaf_coordinate_ne leaf.property.1 leaf.property.2.1 different
    (after_older.trans before.le) (active.trans_lt (older.tail_end_beyond_clip_ball deep))
  have at_bank := agreement (leaf.point.re + leaf.point.im) ⟨before.le, active⟩
  rw [completion.2 _ ⟨le_rfl, active⟩, leaf.tailGraph_target] at at_bank
  exact avoids at_bank.symm

/-- Otherwise the completed leaf would lie on the earlier actual terminal
tail, contradicting that a distinct childless leaf avoids every such tail. -/
theorem le_permanent_terminal_height {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {S : MonotoneStrip}
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    {H : MonotoneHeightGraph} (bank : H = S.lower ∨ H = S.upper)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (merged : ∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = S.upper.coordinate k) :
    leaf.point.re + leaf.point.im ≤ h := by
  obtain ⟨older, after_older, follows⟩ := tails h height merged
  apply leaf.le_height_of_completed_tail_agreement deep older after_older completion active
  intro k member
  rcases bank with rfl | rfl
  · exact (follows k member).1
  · exact (follows k member).2

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
