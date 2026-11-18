module

public import Unfoldings.Complex.SurvivingBoundaryChain
public import Unfoldings.Topology.ParentPaths

/-! Complete rootward start labels and the true terminal root determine every far endpoint. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} {retain : Set C.Seam} {m : ℕ}
  (chain : (C.boundarySystem retain).Chain m) (source : C.Vertex Set.univ)
  (span : P.distanceToRoot source = m + 1)
  (labels : ∀ k, C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (chain.point k)) = P.parent^[k.val] source)
  (terminal : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (C.boundaryTurn _ chain.last)) = P.root source)

include span labels terminal in
/-- Actual boundary successors give the next parent at both endpoints of every bank. -/
theorem rootwardChain_finish_original (k : Fin (m + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (chain.point k))) =
        P.parent^[k.val + 1] source := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have reaches := P.iterate_distanceToRoot_eq_root source
    rw [span] at reaches
    exact terminal.trans reaches.symm
  · have next := congrArg (C.boundaryEndVertex retain) (chain.next i)
    change C.boundaryEndVertex retain
      (C.boundaryMate retain (C.boundaryTurn retain (chain.point i.castSucc))) =
        C.boundaryEndVertex retain (chain.point i.succ) at next
    rw [(C.boundaryMate_spec retain _).2] at next
    exact (congrArg (C.vertexForgetCuts (Set.subset_univ _)) next).trans (labels i.succ)

end Unfoldings.TriangleComplex
