module

public import Unfoldings.Complex.DirectedBoundaryPath

/-! Named-bank computation for the genuine directed boundary path. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- A named bank with a chosen starting endpoint keeps its literal bank parameter. -/
@[simp] theorem directedBoundaryPath_from_bank (bank : C.BoundaryBank retain)
    (side : Bool) (t : unitInterval) :
    C.directedBoundaryPath ((C.boundaryEndEquiv retain).symm (bank, side)) t =
      C.bankMap retain bank (C.bankParameterFromEnd bank side t) := by
  unfold directedBoundaryPath
  rw [(C.boundaryEndEquiv retain).apply_symm_apply]

end Unfoldings.TriangleComplex
