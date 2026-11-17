module

public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Metric.ClosedUnitIntervalLineMap
public import Mathlib.Tactic.Module

/-! The full spatial trace of a bank restriction is the literal affine subsegment. -/

@[expose] public section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

/-- The complete spatial bank interpolates its literal folded endpoint copies. -/
theorem directedBoundaryPath_lineMap (p : C.BoundaryEnd retain) (u : unitInterval) :
    F.toSpace retain (C.directedBoundaryPath p u) =
      AffineMap.lineMap (F.boundaryPosition p)
        (F.boundaryPosition (C.boundaryTurn retain p)) u.val := by
  rw [F.directedBoundaryPath_position, F.germDirection_boundary_positions,
    AffineMap.lineMap_apply_module']
  exact add_comm _ _

/-- Original bank coordinates interpolate the exact spatial endpoint positions. -/
theorem directedBoundaryPath_subinterval (p : C.BoundaryEnd retain)
    (s t : unitInterval) (forward : s.val ≤ t.val) (u : unitInterval) :
    F.toSpace retain (C.directedBoundaryPath p (closedUnitIntervalLineMap s t forward u)) =
      AffineMap.lineMap (F.toSpace retain (C.directedBoundaryPath p s))
        (F.toSpace retain (C.directedBoundaryPath p t)) u.val := by
  rw [F.directedBoundaryPath_position, F.directedBoundaryPath_position,
    F.directedBoundaryPath_position, AffineMap.lineMap_apply_module']
  change F.boundaryPosition p + (s.val + u.val * (t.val - s.val)) • F.germDirection p.val = _
  module

end Unfoldings.SpatialFolding
