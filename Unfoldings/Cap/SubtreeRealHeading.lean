module

public import Unfoldings.Complex.SubtreeRolling
public import Unfoldings.Cap.RimAngles

/-! Actual real parent-bank holonomy is nonnegative and bounded by total original cap curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include K roots in
/-- Exact real heading on the actual two parent banks lies between zero and total cap curvature. -/
theorem exists_subtree_real_bank_heading_bounds (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    ∃ first leave : Fin (Q.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point first)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) ((Q.rotate C first).cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) (!side) ∧
      C.boundaryRollHeading (Q.rotate C first) leave + Real.pi =
        (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) ∧
      C.boundaryRollHeading (Q.rotate C first) leave + Real.pi ∈
        Set.Icc 0 (C.totalInteriorAngularDefect Set.univ) := by
  obtain ⟨first, leave, side, entrance, exit, heading⟩ :=
    C.exists_subtree_real_bank_heading S roots Q e nonroot
  refine ⟨first, leave, side, entrance, exit, heading, ?_⟩
  rw [heading]
  exact ⟨Finset.sum_nonneg (fun v _ => K.interiorCurvature_nonneg v),
    K.sum_interiorAngularDefect_le_totalCurvature (P.descendants e)⟩

end Unfoldings.ConvexCap
