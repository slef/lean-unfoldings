module

public import Unfoldings.Complex.ReturnSourceChain
public import Unfoldings.Topology.ParentDistanceStep

/-! Every fresh contour source constructs its complete actual source-to-root boundary chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots) (j : Fin Q.length)
  (fresh : C.contourOriginalVertex S Q j.castSucc ∉
    (C.contourFrontier S Q j.castSucc).processed)

include F roots starts fresh in
/-- Both descent and return steps provide every genuine original parent edge, including
one-edge returns directly to the rim. Actual successors and endpoint labels are derived. -/
theorem exists_freshSourceBankChain (m : ℕ)
    (span : P.distanceToRoot (C.contourOriginalVertex S Q j.castSucc) = m + 1) :
    ∃ chain :
        (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q j.succ))).Chain m,
      (∀ k, C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ (chain.point k)) =
          P.parent^[k.val] (C.contourOriginalVertex S Q j.castSucc)) ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ (C.boundaryTurn _ chain.last)) =
          P.root (C.contourOriginalVertex S Q j.castSucc) := by
  rcases C.fresh_contour_step_direction S Q j roots fresh with child | returns
  · refine ⟨F.supportedProcessedBankChain S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span, ?_, ?_⟩
    · exact F.supportedProcessedBankChain_original S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span
    · exact F.supportedProcessedBankChain_terminal_original S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span
  · have nonroot : C.contourOriginalVertex S Q j.castSucc ∉ P.roots := by
      intro root
      have zero := (P.distanceToRoot_eq_zero_iff _).mpr root
      omega
    have distance := P.distanceToRoot_parent_step _ nonroot
    rw [returns, span] at distance
    have parent_span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m := by omega
    cases m with
    | zero =>
      refine ⟨returnSourceRootBankChain S Q j returns, ?_, ?_⟩
      · intro k
        have only : k = 0 := Fin.ext (by have bound := k.isLt; omega)
        subst k
        exact returnSourceRootBankChain_first_original S Q j returns
      · exact returnSourceRootBankChain_terminal_original S Q j returns
          ((P.distanceToRoot_eq_zero_iff _).mp parent_span)
    | succ m =>
      refine ⟨F.returnSourceBankChain S roots Q starts j returns m parent_span, ?_, ?_⟩
      · exact F.returnSourceBankChain_original S roots Q starts j returns m parent_span
      · exact F.returnSourceBankChain_terminal_original S roots Q starts j returns m parent_span

end Unfoldings.SpatialFolding
