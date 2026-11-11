module

public import Unfoldings.Cap.CompletedSubtreeDirections
public import Unfoldings.Cap.CompletedBankPositionOrder

/-! Transfer labeled geometric component sectors to every curvature-carrying descendant. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)
  {t : ℝ}

/-- The actual top direction and every positive descendant opening share a fixed sector.
The assertion imposes no direction restriction on the additional flat branches. -/
theorem exists_subtree_sector_of_component_cover {I A : Type*} [Finite I]
    (outward : R.Outward) (first last : I → Plane) (label : I → A)
    (cover : cuts = ⋃ i, segment ℝ (first i) (last i))
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (component_sector : ∀ a : A, ∃ i : FiveSector,
      ∀ j, label j = a → last j - first j ∈ closedFiveSector t i)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (member : K.projectedVertex e.val ∈ cuts) :
    ∃ i : FiveSector,
      K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val ∈
        closedFiveSector t i ∧ R.CurvedSubtreeInSector (t := t) i e := by
  obtain ⟨anchor, at_anchor⟩ := Set.mem_iUnion.mp (cover.subset member)
  obtain ⟨i, directions⟩ := component_sector (label anchor)
  refine ⟨i, ?_, fun child ancestor positive => ?_⟩
  · have different : K.projectedVertex e.val ≠
        K.projectedVertex (R.spanningCompletion.parents.parent e.val) := by
      intro same
      exact R.completed_parent_direction_ne_zero e.val e.property (sub_eq_zero.mpr same.symm)
    exact direction_wedge_of_labeled_segment_cover q _ _
      (fiveSectorFirst t i) (fiveSectorLast t i) different
      (R.completed_parent_outward outward e member) first last label piece_outward compatible
      ((R.completed_parent_segment_subset_cuts e member).trans cover.subset) anchor
      ⟨K.projectedVertex e.val, left_mem_segment ℝ _ _, at_anchor⟩ directions
  · exact R.nonzero_descendant_direction_of_component_cover outward first last label cover
      piece_outward compatible covered e child ancestor positive anchor at_anchor
      (fiveSectorFirst t i) (fiveSectorLast t i) directions

end Unfoldings.ConvexCap.RadialCutForest
