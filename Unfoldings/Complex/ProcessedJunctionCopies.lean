module

public import Unfoldings.Complex.ProcessedCutIncidence

/-! Actual intermediate parent-child cut junctions have genuinely split original vertex copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier) (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.processedParentRetain S frontier))

include roots Q in
/-- Current parent-child incidence supplies a distinct cut copy at every intermediate
junction. Unprocessed original vertices may remain curved and internal. -/
theorem exists_other_processed_junction_copy (w : C.Vertex (C.processedParentRetain S frontier))
    (nonroot : C.vertexForgetCuts (Set.subset_univ _) w ∉ P.roots)
    (processed : C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed)
    (child : C.Vertex Set.univ) (child_processed : child ∈ frontier.processed)
    (parent : P.parent child = C.vertexForgetCuts (Set.subset_univ _) w) :
    ∃ z : C.Vertex (C.processedParentRetain S frontier), w ≠ z ∧
      C.vertexForgetCuts (Set.subset_univ _) z = C.vertexForgetCuts (Set.subset_univ _) w := by
  classical
  by_contra absent
  let target := C.vertexForgetCuts (Set.subset_univ _) w
  change target ∉ P.roots at nonroot
  change target ∈ frontier.processed at processed
  have parent_target : P.parent child = target := parent
  have child_nonroot : child ∉ P.roots := by
    intro root
    have same : child = target := (P.fixed_root child root).symm.trans parent_target
    exact nonroot (same ▸ root)
  let weight (v : C.Vertex Set.univ) : ℝ := if v = target then 1 else 0
  have unique (z : C.Vertex (C.processedParentRetain S frontier))
      (same : C.vertexForgetCuts (Set.subset_univ _) z = target) : z = w := by
    by_contra different
    exact absent ⟨z, fun equal => different equal.symm, same⟩
  have fiber (z : C.Vertex (C.processedParentRetain S frontier)) :
      C.vertexForgetCuts (Set.subset_univ _) z = target ↔ z = w :=
    ⟨unique z, fun equal => congrArg (C.vertexForgetCuts (Set.subset_univ _)) equal⟩
  have zero_roots (v : C.Vertex Set.univ) (root : v ∈ P.roots) : weight v = 0 := by
    have different : v ≠ target := fun equal => nonroot (equal ▸ root)
    exact ite_eq_right different
  have zero_unprocessed (v : C.Vertex Set.univ) (outside : v ∉ frontier.processed) :
      weight v = 0 := by
    have different : v ≠ target := fun equal => outside (equal.symm ▸ processed)
    exact ite_eq_right different
  have copies : (∑ z : C.Vertex (C.processedParentRetain S frontier),
      weight (C.vertexForgetCuts (Set.subset_univ _) z)) = 1 := by
    simp only [weight, fiber, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have counted := C.sum_processed_vertex_weights S frontier roots Q.cycle Q.closes Q.covers
    weight zero_roots zero_unprocessed
  rw [copies, Finset.sum_add_distrib] at counted
  let top : C.ProcessedParentSelector frontier := ⟨⟨target, nonroot⟩, processed⟩
  let bottom : C.ProcessedParentSelector frontier := ⟨⟨child, child_nonroot⟩, child_processed⟩
  have nonnegative (v : C.Vertex Set.univ) : 0 ≤ weight v := by
    dsimp [weight]
    split_ifs <;> norm_num
  have first := Finset.single_le_sum
    (fun (e : C.ProcessedParentSelector frontier) _ => nonnegative e.val.val) (Finset.mem_univ top)
  have last := Finset.single_le_sum
    (fun (e : C.ProcessedParentSelector frontier) _ => nonnegative (P.parent e.val.val))
    (Finset.mem_univ bottom)
  have at_top : weight top.val.val = 1 := by simp only [weight, top, ite_true]
  have at_bottom : weight (P.parent bottom.val.val) = 1 := by
    simp only [weight, bottom, parent_target, ite_true]
  rw [at_top] at first
  rw [at_bottom] at last
  linarith

end Unfoldings.TriangleComplex
