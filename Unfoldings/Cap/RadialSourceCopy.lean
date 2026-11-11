module

public import Unfoldings.Cap.RadialSourceLeaf

/-! The distinguished source has exactly one intrinsic copy after the completed cuts. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)
  {source : C.Vertex Set.univ}

/-- Cutting the one edge at an interior source leaf creates a slit endpoint, not two distinct
source copies. This supplies the common point at the final no-wrap gap. -/
theorem completed_source_copy_unique (at_source : K.projectedVertex source = q)
    (internal : ¬ C.IsBoundaryVertex Set.univ source)
    (a b : C.Vertex R.completedRetain)
    (first : C.vertexForgetCuts (Set.subset_univ R.completedRetain) a = source)
    (last : C.vertexForgetCuts (Set.subset_univ R.completedRetain) b = source) : a = b := by
  classical
  have nonroot : source ∉ R.spanningCompletion.parents.roots := by
    intro root
    exact internal ((Set.ext_iff.mp R.spanningCompletion.roots_eq source).mp root)
  have count := C.sum_subtree_vertex_copies R.spanningCompletion.selection
    R.spanningCompletion.roots_eq R.completedContour.cycle R.completedContour.closes
    R.completedContour.covers source nonroot
  rw [R.completed_descendants_source at_source internal] at count
  norm_num only [Finset.card_singleton, Nat.cast_one] at count
  simp only [R.completed_ancestor_source_iff at_source internal, Finset.sum_boole] at count
  let copies := Finset.univ.filter (fun w : C.Vertex R.completedRetain =>
    C.vertexForgetCuts (Set.subset_univ R.completedRetain) w = source)
  have card : copies.card = 1 := by exact_mod_cast count
  exact Finset.card_le_one.mp card.le a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, first⟩)
    b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, last⟩)

end Unfoldings.ConvexCap.RadialCutForest
