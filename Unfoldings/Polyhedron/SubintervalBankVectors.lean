module

public import Unfoldings.Polyhedron.DirectedBankSubinterval
public import Unfoldings.Polyhedron.BankLengths

/-! Original spatial bank subintervals determine exact fine-edge vectors and lengths. -/

@[expose] public section

namespace Unfoldings.SpatialFolding

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {Other : Type w} [Fintype Other] {D : TriangleComplex.{w, z} Other}
  (F : SpatialFolding C) (E : SpatialFolding D)
  {retain : Set C.Seam} {oldRetain : Set D.Seam}

/-- Original spatial endpoint copies determine the full fine-bank velocity. -/
theorem germDirection_eq_bank_subinterval (p : C.BoundaryEnd retain)
    (q : D.BoundaryEnd oldRetain) (s t : unitInterval)
    (initial : F.boundaryPosition p = E.toSpace oldRetain (D.directedBoundaryPath q s))
    (final : F.boundaryPosition (C.boundaryTurn retain p) =
      E.toSpace oldRetain (D.directedBoundaryPath q t)) :
    F.germDirection p.val = (t.val - s.val) • E.germDirection q.val := by
  rw [F.germDirection_boundary_positions, final, initial,
    E.directedBoundaryPath_position, E.directedBoundaryPath_position]
  module

/-- A forward original time increment measures the exact intrinsic fine-bank length. -/
theorem boundaryBankLength_eq_bank_subinterval (p : C.BoundaryEnd retain)
    (q : D.BoundaryEnd oldRetain) (s t : unitInterval) (forward : s.val ≤ t.val)
    (initial : F.boundaryPosition p = E.toSpace oldRetain (D.directedBoundaryPath q s))
    (final : F.boundaryPosition (C.boundaryTurn retain p) =
      E.toSpace oldRetain (D.directedBoundaryPath q t)) :
    C.boundaryBankLength p = (t.val - s.val) * ‖E.germDirection q.val‖ := by
  rw [F.boundaryBankLength_eq_germDirection_norm,
    F.germDirection_eq_bank_subinterval E p q s t initial final,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr forward)]

end Unfoldings.SpatialFolding
