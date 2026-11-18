module

public import Unfoldings.Complex.RootwardChainLabels
public import Unfoldings.Complex.RootwardBankRestoration

/-! Restore every source-inclusive parent bank to its exact original ancestor-path cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots) (frontier : P.ParentFrontier)
  {m : ℕ} (chain : (C.boundarySystem (C.processedParentRetain S frontier)).Chain m)
  (source : C.Vertex Set.univ) (span : P.distanceToRoot source = m + 1)
  (labels : ∀ k, C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (chain.point k)) = P.parent^[k.val] source)
  (terminal : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (C.boundaryTurn _ chain.last)) = P.root source)

include roots span labels terminal in
/-- Every actual bank survives when all side branches outside the source path are restored. -/
theorem sourceBank_survives_reference (k : Fin (m + 1)) :
    C.IsBoundaryEdge (C.ancestorPathRetain S source) (C.germEdge (chain.point k).val) := by
  let p : C.BoundaryEnd (C.selectedRetain S) := ⟨(chain.point k).val,
    C.isBoundaryEdge_antitone (C.selectedRetain_subset_processed S frontier)
      (chain.point k).property⟩
  apply C.parent_bank_survives_source_path S roots p source
  · change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (chain.point k)) ∉ P.roots
    rw [labels]
    exact P.iterate_lt_distanceToRoot_not_mem source (by rw [span]; exact k.isLt)
  · change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (chain.point k))) =
        P.parent (C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex _ (chain.point k)))
    rw [labels, C.rootwardChain_finish_original chain source span labels terminal]
    exact Function.iterate_succ_apply' P.parent k.val source
  · change P.Ancestor source (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (chain.point k)))
    rw [labels]
    exact ⟨k.val, rfl⟩

variable (processed : source ∈ frontier.processed)

/-- The complete actual source-inclusive reference, cut only along its own original parent path. -/
def completeSourceReference : (C.boundarySystem (C.ancestorPathRetain S source)).Chain m :=
  C.survivingBoundaryChain (C.processedRetain_subset_ancestorPathRetain S frontier source processed)
    chain (C.sourceBank_survives_reference S roots frontier chain source span labels terminal)

/-- Original parent labels survive on every restored reference bank. -/
theorem completeSourceReference_original (k : Fin (m + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        ((C.completeSourceReference S roots frontier chain source span labels terminal
          processed).point k)) = P.parent^[k.val] source := labels k

/-- The literal original root stays the true far endpoint after restoration. -/
theorem completeSourceReference_terminal_original :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _
        (C.completeSourceReference S roots frontier chain source span labels terminal
          processed).last)) = P.root source := terminal

/-- Every point of every original closed bank is its canonical cut-restoration image. -/
theorem completeSourceReference_path (k : Fin (m + 1)) (t : unitInterval) :
    C.directedBoundaryPath
      ((C.completeSourceReference S roots frontier chain source span labels terminal
        processed).point k) t =
      C.forgetCuts (C.processedRetain_subset_ancestorPathRetain S frontier source processed)
        (C.directedBoundaryPath (chain.point k) t) :=
  C.survivingBoundaryEnd_path _ _ _ t

/-- Every unreduced real heading survives the canonical original-face restoration. -/
theorem completeSourceReference_heading (k : Fin (m + 1)) :
    C.boundaryChainRollHeading
      (C.completeSourceReference S roots frontier chain source span labels terminal processed) k =
      C.boundaryChainRollHeading chain k :=
  C.survivingBoundaryChain_rollHeading _ _ _ k

/-- Every intrinsic rolled vertex and full edge remains identical, including the source edge. -/
theorem completeSourceReference_roll :
    C.boundaryChainRoll
      (C.completeSourceReference S roots frontier chain source span labels terminal processed) =
      C.boundaryChainRoll chain := C.survivingBoundaryChain_roll _ _ _

end Unfoldings.TriangleComplex
