module

public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Complex.BoundaryChainRolling

/-! Reverse actual directed bank paths without changing intrinsic copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- Reversing the actual boundary end reverses every point of the same original bank. -/
theorem directedBoundaryPath_turn (p : C.BoundaryEnd retain) (t : unitInterval) :
    C.directedBoundaryPath (C.boundaryTurn retain p) t =
      C.directedBoundaryPath p (unitInterval.symm t) := by
  unfold directedBoundaryPath
  rw [boundaryTurn, Equiv.apply_symm_apply]
  simp only [bankParameterFromEnd, Bool.not_not]
  apply congrArg (C.bankMap retain (C.boundaryEndEquiv retain p).1)
  apply Subtype.ext
  exact (AffineMap.lineMap_apply_one_sub
    ((C.triangle (C.boundaryEndEquiv retain p).1.val.face).endpoint
      (C.boundaryEndEquiv retain p).1.val.edge (C.boundaryEndEquiv retain p).2).val
    ((C.triangle (C.boundaryEndEquiv retain p).1.val.face).endpoint
      (C.boundaryEndEquiv retain p).1.val.edge (!(C.boundaryEndEquiv retain p).2)).val t.val).symm

/-- The initial directed-bank point is its actual original boundary vertex copy. -/
@[simp] theorem directedBoundaryPath_zero (p : C.BoundaryEnd retain) :
    C.directedBoundaryPath p 0 = C.vertexPoint retain (C.boundaryEndVertex retain p) := by
  rw [C.boundaryEnd_vertexPoint_eq_endpoint]
  unfold directedBoundaryPath bankParameterFromEnd
  congr 1
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero _ _

/-- The final directed-bank point is the opposite original endpoint copy. -/
@[simp] theorem directedBoundaryPath_one (p : C.BoundaryEnd retain) :
    C.directedBoundaryPath p 1 =
      C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain p)) := by
  have reversed := C.directedBoundaryPath_turn p (0 : unitInterval)
  simpa only [unitInterval.symm_zero, directedBoundaryPath_zero] using reversed.symm

end Unfoldings.TriangleComplex
