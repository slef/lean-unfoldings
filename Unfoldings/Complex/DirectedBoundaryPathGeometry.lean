module

public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Cap.Projection

/-! Original directed bank paths are continuous and preserve their exact projected interpolation. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face) {retain : Set C.Seam}

theorem continuous_directedBoundaryPath (p : C.BoundaryEnd retain) :
    Continuous (C.directedBoundaryPath p) :=
  (C.bankMap_lipschitz retain (C.boundaryEndEquiv retain p).1).continuous.comp
    ((AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _)

end Unfoldings.TriangleComplex
namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {retain : Set C.Seam}

/-- Every original bank parameter retains the affine projected position of its original ends. -/
theorem horizontal_directedBoundaryPath (p : C.BoundaryEnd retain) (t : unitInterval) :
    Cap.horizontal (F.toSpace retain (C.directedBoundaryPath p t)) =
      AffineMap.lineMap (Cap.horizontal (F.boundaryPosition p))
        (Cap.horizontal (F.boundaryPosition (C.boundaryTurn retain p))) t.val := by
  rw [F.directedBoundaryPath_position, F.germDirection_boundary_positions]
  rw [map_add, map_smul, map_sub, AffineMap.lineMap_apply_module']
  exact add_comm _ _

end Unfoldings.SpatialFolding
