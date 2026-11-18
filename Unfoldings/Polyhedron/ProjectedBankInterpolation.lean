module

public import Unfoldings.Polyhedron.DirectedBankSubinterval
public import Unfoldings.Cap.Projection

/-! Actual horizontal bank interpolation retains both named spatial endpoint copies. -/

@[expose] public section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

theorem directedBoundaryPath_horizontal_lineMap (p : C.BoundaryEnd retain) (t : unitInterval) :
    Cap.horizontal (F.toSpace retain (C.directedBoundaryPath p t)) =
      AffineMap.lineMap (Cap.horizontal (F.boundaryPosition p))
        (Cap.horizontal (F.boundaryPosition (C.boundaryTurn retain p))) t.val :=
  (congrArg Cap.horizontal (F.directedBoundaryPath_lineMap p t)).trans
    (Cap.horizontal.toAffineMap.apply_lineMap _ _ _)

end Unfoldings.SpatialFolding
