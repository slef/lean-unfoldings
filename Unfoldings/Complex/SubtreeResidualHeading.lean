module

public import Unfoldings.Complex.SubtreeRolling
public import Unfoldings.Topology.SubtreeResidualWeights

/-! Actual unreduced parent-bank holonomies leave precisely the original local curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- The actual parent's unreduced opposite-bank heading after subtracting child holonomies. -/
def subtreeBankResidual
    (first leave : {e : C.Vertex Set.univ // e ∉ P.roots} → Fin (Q.length + 1))
    (e : {e : C.Vertex Set.univ // e ∉ P.roots}) : ℝ := by
  classical
  exact (C.boundaryRollHeading (Q.rotate C (first e)) (leave e) + Real.pi) -
    (∑ c : {c : C.Vertex Set.univ // c ∉ P.roots}, if P.parent c.val = e.val then
      C.boundaryRollHeading (Q.rotate C (first c)) (leave c) + Real.pi else 0)

include roots in
open Classical in
/-- Choose the actual opposite banks at every nonroot. Subtracting all immediate-child real
holonomies from the parent's holonomy leaves the junction's original angular defect. -/
theorem exists_subtree_residual_real_heading :
    ∃ first leave : {e : C.Vertex Set.univ // e ∉ P.roots} → Fin (Q.length + 1),
      ∃ side : {e : C.Vertex Set.univ // e ∉ P.roots} → Bool,
      (∀ e, (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point (first e))).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S e.val e.property) (side e) ∧
        (C.boundaryEndEquiv (C.selectedRetain S)
          ((Q.rotate C (first e)).cycle.point (leave e))).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S e.val e.property) (!(side e))) ∧
      ∀ e : {e : C.Vertex Set.univ // e ∉ P.roots},
        C.subtreeBankResidual S Q first leave e = C.interiorAngularDefect Set.univ e.val := by
  classical
  choose first leave side entrance exit heading using
    (fun e : {e : C.Vertex Set.univ // e ∉ P.roots} =>
      C.exists_subtree_real_bank_heading S roots Q e.val e.property)
  refine ⟨first, leave, side, fun e => ⟨entrance e, exit e⟩, fun e => ?_⟩
  unfold subtreeBankResidual
  simp_rw [heading]
  exact P.descendant_weight_sub_children e.val e.property
    (C.interiorAngularDefect Set.univ)

end Unfoldings.TriangleComplex
