module

public import Unfoldings.Complex.SubtreeResidualHeading
public import Unfoldings.Cap.RimAngles
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Original local curvature pays once for the actual unreduced junction-bank residuals. -/

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
/-- Actual opposite-bank residuals are nonnegative local curvature. Any distinct list of
original junctions spends at most total cap curvature, even with branching subtrees. -/
theorem exists_subtree_residual_budget :
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
      ∀ processed : List {e : C.Vertex Set.univ // e ∉ P.roots}, processed.Nodup →
        (processed.map (fun e => |C.subtreeBankResidual S Q first leave e|)).sum ≤
          C.totalInteriorAngularDefect Set.univ := by
  classical
  obtain ⟨first, leave, side, names, residual⟩ := C.exists_subtree_residual_real_heading S roots Q
  refine ⟨first, leave, side, names, residual, ?_, ?_⟩
  · intro e
    rw [residual]
    exact K.interiorCurvature_nonneg e.val
  · intro processed distinct
    simp_rw [residual, abs_of_nonneg (K.interiorCurvature_nonneg _)]
    rw [← List.sum_toFinset _ distinct]
    have equal : (∑ e ∈ processed.toFinset, C.interiorAngularDefect Set.univ e.val) =
        ∑ v ∈ processed.toFinset.image Subtype.val, C.interiorAngularDefect Set.univ v := by
      symm
      exact Finset.sum_image (fun a _ b _ same => Subtype.ext same)
    rw [equal]
    exact K.sum_interiorAngularDefect_le_totalCurvature _

end Unfoldings.ConvexCap
