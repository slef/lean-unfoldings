module

public import Unfoldings.Cap.RadialForestDevelopment
public import Unfoldings.Cap.UnrestrictedRadialProgress
public import Unfoldings.Topology.SelectedRootCompletion
public import Unfoldings.Topology.SelectedSubtree

/-! Complete unused flat vertices while preserving the geometric cut paths carrying curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

/-- Fill in the unused roots by actual seams, with no acuteness requirement on the auxiliary
triangulation. Every previously selected edge and nonroot parent is preserved. -/
def spanningCompletion : R.selection.RootCompletion (C.relativeCutRoots Set.univ) := by
  apply R.selection.completeRoots
  · intro w boundary
    exact (Set.ext_iff.mp R.roots_eq w).mpr (Or.inl boundary)
  · intro w _old internal
    obtain ⟨z, s, link, farther, _outward⟩ := K.exists_unrestricted_radial_step q w internal
    refine ⟨z, s, link, ?_⟩
    simpa only [R.height_eq] using farther

def completedRetain : Set C.Seam := C.selectedRetain R.spanningCompletion.selection

/-- Completion adds cuts but never restores an old cut seam. -/
theorem completedRetain_subset : R.completedRetain ⊆ R.retain := by
  intro s retained old_cut
  exact retained (R.spanningCompletion.selected_subset old_cut)

def completedCutDisk : C.Realization R.completedRetain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  C.selectedCutDisk R.spanningCompletion.selection R.spanningCompletion.roots_eq
    K.folding K.diskHomeomorph

/-- Every actual vertex copy lies on the completed cut boundary. -/
theorem completed_all_vertices_boundary (w : C.Vertex R.completedRetain) :
    C.IsBoundaryVertex R.completedRetain w :=
  C.selectedCut_all_vertices_boundary R.spanningCompletion.selection
    R.spanningCompletion.roots_eq w

/-- Old geometric cuts are forward invariant under the completed parent map. -/
theorem completed_parent_mem_cuts (w : C.Vertex Set.univ) (member : K.projectedVertex w ∈ cuts) :
    K.projectedVertex (R.spanningCompletion.parents.parent w) ∈ cuts := by
  by_cases boundary : C.IsBoundaryVertex Set.univ w
  · have root : w ∈ R.spanningCompletion.parents.roots :=
      (Set.ext_iff.mp R.spanningCompletion.roots_eq w).mpr boundary
    rw [R.spanningCompletion.parents.fixed_root w root]
    exact member
  · have nonroot : w ∉ R.parents.roots := by
      intro root
      rcases (Set.ext_iff.mp R.roots_eq w).mp root with rim | outside
      · exact boundary rim
      · exact outside member
    rw [R.spanningCompletion.parent_eq w nonroot]
    let e : {w : C.Vertex Set.univ // w ∉ R.parents.roots} := ⟨w, nonroot⟩
    apply R.selected_subset e
    rcases R.selection.link e with first | last
    · rw [first.2]
      exact right_mem_segment ℝ _ _
    · rw [last.2]
      exact left_mem_segment ℝ _ _

theorem completed_ancestor_mem_cuts {w z : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts) (ancestor : R.spanningCompletion.parents.Ancestor w z) :
    K.projectedVertex z ∈ cuts := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => exact member
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact R.completed_parent_mem_cuts _ ih

/-- Every added branch outside the prescribed cuts has exactly zero descendant curvature. -/
theorem completed_extra_subtree_zero
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (w : C.Vertex Set.univ) (outside : K.projectedVertex w ∉ cuts) :
    (∑ z ∈ R.spanningCompletion.parents.descendants w,
      C.interiorAngularDefect Set.univ z) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z member
  have ancestor := (R.spanningCompletion.parents.mem_descendants z w).mp member
  have not_positive : ¬ 0 < C.interiorAngularDefect Set.univ z := by
    intro curved
    exact outside (R.completed_ancestor_mem_cuts (covered z curved) ancestor)
  exact le_antisymm (not_lt.mp not_positive) (K.interiorCurvature_nonneg z)

end Unfoldings.ConvexCap.RadialCutForest
