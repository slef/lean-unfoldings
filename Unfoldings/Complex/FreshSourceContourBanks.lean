module

public import Unfoldings.Complex.FreshSourceBankChain

/-! Complete source-bank choices preserve the actual oriented original contour tags. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

/-- Every processed parent bank keeps its literal future contour tag. -/
theorem supportedProcessedBankChain_contour (stage : Fin (Q.length + 1))
    (base : C.Vertex Set.univ) (processed : base ∈ (C.contourFrontier S Q stage).processed)
    (ancestor : P.Ancestor (C.contourOriginalVertex S Q stage) base)
    (m : ℕ) (span : P.distanceToRoot base = m + 1) (k : Fin (m + 1)) :
    ∃ i : Fin (Q.length + 1), stage.val ≤ i.val ∧
      ((F.supportedProcessedBankChain S roots Q starts stage base
        processed ancestor m span).point k).val = (Q.cycle.point i).val := by
  let bank := supportedProcessedBank S roots Q starts stage base processed ancestor m span k
  exact ⟨bank.val, bank.property.1, rfl⟩

/-- The returning chain uses its literal source bank and only upcoming parent banks. -/
theorem returnSourceBankChain_contour (j : Fin Q.length)
    (returns : P.parent (C.contourOriginalVertex S Q j.castSucc) =
      C.contourOriginalVertex S Q j.succ)
    (m : ℕ) (span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m + 1)
    (k : Fin (m + 2)) :
    ∃ i : Fin (Q.length + 1), j.val ≤ i.val ∧
      ((F.returnSourceBankChain S roots Q starts j returns m span).point k).val =
        (Q.cycle.point i).val := by
  unfold returnSourceBankChain
  erw [PairedInvolutions.System.Chain.cast_point]
  change ∃ i, j.val ≤ i.val ∧
    ((PairedInvolutions.System.Chain.concatenatedPoint _ _ _) :
      C.BoundaryEnd (C.processedParentRetain S (C.contourFrontier S Q j.succ))).val =
        (Q.cycle.point i).val
  unfold PairedInvolutions.System.Chain.concatenatedPoint
  split
  · exact ⟨j.castSucc, le_rfl, rfl⟩
  · obtain ⟨i, future, same⟩ := F.supportedProcessedBankChain_contour S roots Q starts j.succ
      (C.contourOriginalVertex S Q j.succ) _ _ m span ⟨k.val - 1, by omega⟩
    exact ⟨i, by change j.val + 1 ≤ i.val at future; omega, same⟩

include F roots starts in
/-- Fresh-source construction keeps every exact bank tag of the named oriented contour.
This additional datum prevents choosing the opposite cut side with identical endpoint labels. -/
theorem exists_contourSourceBankChain (j : Fin Q.length)
    (fresh : C.contourOriginalVertex S Q j.castSucc ∉
      (C.contourFrontier S Q j.castSucc).processed)
    (m : ℕ) (span : P.distanceToRoot (C.contourOriginalVertex S Q j.castSucc) = m + 1) :
    ∃ chain :
        (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q j.succ))).Chain m,
      (∀ k, C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ (chain.point k)) =
          P.parent^[k.val] (C.contourOriginalVertex S Q j.castSucc)) ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ (C.boundaryTurn _ chain.last)) =
          P.root (C.contourOriginalVertex S Q j.castSucc) ∧
      ∀ k, ∃ i : Fin (Q.length + 1), j.val ≤ i.val ∧
        (chain.point k).val = (Q.cycle.point i).val := by
  rcases C.fresh_contour_step_direction S Q j roots fresh with child | returns
  · refine ⟨F.supportedProcessedBankChain S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span, ?_, ?_, ?_⟩
    · exact F.supportedProcessedBankChain_original S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span
    · exact F.supportedProcessedBankChain_terminal_original S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span
    · intro k
      obtain ⟨i, future, same⟩ := F.supportedProcessedBankChain_contour S roots Q starts j.succ
        (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
        ⟨1, child⟩ m span k
      exact ⟨i, by change j.val + 1 ≤ i.val at future; omega, same⟩
  · have nonroot : C.contourOriginalVertex S Q j.castSucc ∉ P.roots := by
      intro root
      have zero := (P.distanceToRoot_eq_zero_iff _).mpr root
      omega
    have distance := P.distanceToRoot_parent_step _ nonroot
    rw [returns, span] at distance
    have parent_span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m := by omega
    cases m with
    | zero =>
      refine ⟨returnSourceRootBankChain S Q j returns, ?_, ?_, ?_⟩
      · intro k
        have only : k = 0 := Fin.ext (by have bound := k.isLt; omega)
        subst k
        exact returnSourceRootBankChain_first_original S Q j returns
      · exact returnSourceRootBankChain_terminal_original S Q j returns
          ((P.distanceToRoot_eq_zero_iff _).mp parent_span)
      · intro k
        exact ⟨j.castSucc, le_rfl, rfl⟩
    | succ m =>
      refine ⟨F.returnSourceBankChain S roots Q starts j returns m parent_span, ?_, ?_, ?_⟩
      · exact F.returnSourceBankChain_original S roots Q starts j returns m parent_span
      · exact F.returnSourceBankChain_terminal_original S roots Q starts j returns m parent_span
      · exact F.returnSourceBankChain_contour S roots Q starts j returns m parent_span

end Unfoldings.SpatialFolding
