module

public import Unfoldings.Cap.SubtreeResidualBudget
public import Unfoldings.Topology.ParentFrontierHistory

/-! Constructed fresh-branch processing histories spend original opposite-bank residuals once. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include K roots in
open Classical in
/-- For every constructed parent-frontier history, actual original opposite-bank residuals
are nonnegative local curvature and their total absolute cost is at most cap curvature.
No vertex-distinctness or crossing-count certificate is supplied for the processing order. -/
theorem exists_parent_frontier_residual_budget :
    ∃ first leave : {e : C.Vertex Set.univ // e ∉ P.roots} → Fin (Q.length + 1),
      ∃ side : {e : C.Vertex Set.univ // e ∉ P.roots} → Bool,
      (∀ e, (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point (first e))).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S e.val e.property) (side e) ∧
        (C.boundaryEndEquiv (C.selectedRetain S)
          ((Q.rotate C (first e)).cycle.point (leave e))).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S e.val e.property) (!(side e))) ∧
      (∀ e, C.subtreeBankResidual S Q first leave e = C.interiorAngularDefect Set.univ e.val) ∧
      (∀ e, 0 ≤ C.subtreeBankResidual S Q first leave e) ∧
      ∀ (frontier : P.ParentFrontier) (seeds : List (C.Vertex Set.univ)),
        ((frontier.history seeds).map
          (fun e => |C.subtreeBankResidual S Q first leave e|)).sum ≤
            C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨first, leave, side, names, residual, positive, budget⟩ :=
    K.exists_subtree_residual_budget S roots Q
  exact ⟨first, leave, side, names, residual, positive,
    fun frontier seeds => budget (frontier.history seeds) (frontier.history_nodup seeds)⟩

end Unfoldings.ConvexCap
