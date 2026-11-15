module

public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Complex.BoundaryChainRolling

/-! Full folded bank vectors measure the actual intrinsic edge lengths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

/-- Rigid face placement preserves the full length of a directed original bank. -/
theorem boundaryBankLength_eq_germDirection_norm (p : C.BoundaryEnd retain) :
    C.boundaryBankLength p = ‖F.germDirection p.val‖ := by
  change _ = ‖F.place p.val.1.1 ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2) -
    F.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2)‖
  rw [← dist_eq_norm, (F.place p.val.1.1).isometry.dist_eq]
  rfl

end Unfoldings.SpatialFolding
