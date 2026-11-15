module

public import Unfoldings.Cap.SubtreeResidualBudget
public import Unfoldings.Complex.SelectedContourHistory

/-! The actual cut contour's constructed history spends its original bank residuals exactly once. -/

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
/-- The actual original contour supplies a complete first-contact schedule whose original
opposite-bank residuals have total absolute charge exactly the original cap curvature.
No seed coverage or vertex-distinctness certificate is supplied. -/
theorem exists_contour_history_exact_residual_charge :
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
      ((((P.initialFrontier).history (C.selectedContourSeeds S Q)).map
        (fun e => |C.subtreeBankResidual S Q first leave e|)).sum =
          C.totalInteriorAngularDefect Set.univ) := by
  obtain ⟨first, leave, side, names, residual, positive, _budget⟩ :=
    K.exists_subtree_residual_budget S roots Q
  refine ⟨first, leave, side, names, residual, positive, ?_⟩
  simp_rw [residual, abs_of_nonneg (K.interiorCurvature_nonneg _)]
  exact C.sum_initial_history_curvature S roots Q

end Unfoldings.ConvexCap
