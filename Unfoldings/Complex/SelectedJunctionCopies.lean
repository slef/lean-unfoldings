module

public import Unfoldings.Complex.SelectedIncidence
public import Unfoldings.Complex.BoundaryContour

/-! A selected parent and child create genuinely distinct original cut copies at their junction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include roots Q in
/-- Every actual cut copy at a nonroot with a selected child has a distinct sibling.
The multiplicity follows from original selected-edge incidence, without a supplied degree
or vertex-splitting certificate. -/
theorem exists_other_selected_junction_copy (w : C.Vertex (C.selectedRetain S))
    (nonroot : C.vertexForgetCuts (Set.subset_univ _) w ∉ P.roots)
    (child : C.Vertex Set.univ)
    (parent : P.parent child = C.vertexForgetCuts (Set.subset_univ _) w) :
    ∃ z : C.Vertex (C.selectedRetain S), w ≠ z ∧
      C.vertexForgetCuts (Set.subset_univ _) z = C.vertexForgetCuts (Set.subset_univ _) w := by
  classical
  by_contra absent
  let target := C.vertexForgetCuts (Set.subset_univ _) w
  change target ∉ P.roots at nonroot
  let weight (v : C.Vertex Set.univ) : ℝ := if v = target then 1 else 0
  have unique (z : C.Vertex (C.selectedRetain S))
      (same : C.vertexForgetCuts (Set.subset_univ _) z = target) : z = w := by
    by_contra different
    exact absent ⟨z, fun equal => different equal.symm, same⟩
  have fiber (z : C.Vertex (C.selectedRetain S)) :
      C.vertexForgetCuts (Set.subset_univ _) z = target ↔ z = w :=
    ⟨unique z, fun equal => congrArg (C.vertexForgetCuts (Set.subset_univ _)) equal⟩
  have zero_roots (v : C.Vertex Set.univ) (root : v ∈ P.roots) : weight v = 0 := by
    have different : v ≠ target := by
      intro equal
      exact nonroot (equal ▸ root)
    exact ite_eq_right different
  have copies : (∑ z : C.Vertex (C.selectedRetain S),
      weight (C.vertexForgetCuts (Set.subset_univ _) z)) = 1 := by
    simp only [weight, fiber, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have selected := C.sum_selected_vertex_weights S roots Q.cycle Q.closes Q.covers weight zero_roots
  rw [copies, Finset.sum_add_distrib] at selected
  have source : (∑ v : C.Vertex Set.univ, weight v) = 1 := by simp [weight]
  rw [source] at selected
  have nonnegative (v : C.Vertex Set.univ) : 0 ≤ weight (P.parent v) := by
    dsimp [weight]
    split_ifs <;> norm_num
  have lower := Finset.single_le_sum (fun v _ => nonnegative v) (Finset.mem_univ child)
  have at_child : weight (P.parent child) = 1 := by simp only [weight, parent, target, ite_true]
  rw [at_child] at lower
  linarith

end Unfoldings.TriangleComplex
