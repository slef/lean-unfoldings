module

public import Unfoldings.Cap.CompletedBankVectorOrder
public import Unfoldings.Cap.CompletedRootPathSupport

/-! Nonzero descendant openings retain the common direction wedge of their cut component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem completed_parent_original_nonroot
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (member : K.projectedVertex e.val ∈ cuts) : e.val ∉ R.parents.roots := by
  intro root
  rcases (Set.ext_iff.mp R.roots_eq e.val).mp root with boundary | outside
  · exact e.property ((Set.ext_iff.mp R.spanningCompletion.roots_eq e.val).mpr boundary)
  · exact outside member

theorem completed_parent_segment_subset_cuts
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (member : K.projectedVertex e.val ∈ cuts) :
    segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val)) ⊆ cuts := by
  have nonroot := R.completed_parent_original_nonroot e member
  rw [R.spanningCompletion.parent_eq _ nonroot]
  exact (K.selected_parent_segment_eq_seam R.selection ⟨e.val, nonroot⟩).subset.trans
    (R.selected_subset ⟨e.val, nonroot⟩)

theorem completed_parent_outward (outward : R.Outward)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (member : K.projectedVertex e.val ∈ cuts) :
    0 ≤ inner ℝ (K.projectedVertex e.val - q)
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
        K.projectedVertex e.val) := by
  have nonroot := R.completed_parent_original_nonroot e member
  rw [R.spanningCompletion.parent_eq _ nonroot]
  exact outward _ nonroot

/-- Any nonzero descendant curvature comes from the prescribed geometric cuts. -/
theorem mem_cuts_of_completedSubtreeCurvature_pos
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (w : C.Vertex Set.univ) (positive : 0 < R.completedSubtreeCurvature w) :
    K.projectedVertex w ∈ cuts := by
  by_contra outside
  have zero : R.completedSubtreeCurvature w = 0 := R.completed_extra_subtree_zero covered w outside
  exact positive.ne' zero

/-- Propagate the component label from an ancestor to every descendant with nonzero opening.
Added flat branches need no direction constraint because their paired vectors agree. -/
theorem nonzero_descendant_direction_of_component_cover {I A : Type*} [Finite I]
    (outward : R.Outward) (first last : I → Plane) (label : I → A)
    (cover : cuts = ⋃ i, segment ℝ (first i) (last i))
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (e child : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (ancestor : R.spanningCompletion.parents.Ancestor child.val e.val)
    (positive : 0 < R.completedSubtreeCurvature child.val)
    (anchor : I) (member : K.projectedVertex e.val ∈ segment ℝ (first anchor) (last anchor))
    (u0 u1 : Plane)
    (directions : ∀ j, label j = label anchor → InDirectionWedge u0 u1 (last j - first j)) :
    InDirectionWedge u0 u1
      (K.projectedVertex (R.spanningCompletion.parents.parent child.val) -
        K.projectedVertex child.val) := by
  have on_cuts := R.mem_cuts_of_completedSubtreeCurvature_pos covered child.val positive
  obtain ⟨start, at_start⟩ := Set.mem_iUnion.mp (cover.subset on_cuts)
  let P := R.completedRootPath child.val
  let index := (R.spanningCompletion.parents.nonrootAncestorEquiv child.val).symm
    ⟨e.val, e.property, ancestor⟩
  have at_e := congrArg Subtype.val
    ((R.spanningCompletion.parents.nonrootAncestorEquiv child.val).apply_symm_apply
      ⟨e.val, e.property, ancestor⟩)
  change R.spanningCompletion.parents.parent^[index.val] child.val = e.val at at_e
  have point_eq : P.vertex index.castSucc = K.projectedVertex e.val :=
    congrArg K.projectedVertex at_e
  have component := P.labels_eq_of_segment_cover first last label compatible
    (fun i => (R.completedRootPath_edge_subset on_cuts i).trans cover.subset) start at_start
    index.castSucc anchor (point_eq.symm ▸ member)
  have different : K.projectedVertex child.val ≠
      K.projectedVertex (R.spanningCompletion.parents.parent child.val) := by
    intro same
    exact R.completed_parent_direction_ne_zero child.val child.property (sub_eq_zero.mpr same.symm)
  exact direction_wedge_of_labeled_segment_cover q _ _ u0 u1 different
    (R.completed_parent_outward outward child on_cuts) first last label piece_outward compatible
    ((R.completed_parent_segment_subset_cuts child on_cuts).trans cover.subset) start
    ⟨K.projectedVertex child.val, left_mem_segment ℝ _ _, at_start⟩
    (fun j same => directions j (same.trans component.symm))

end Unfoldings.ConvexCap.RadialCutForest
