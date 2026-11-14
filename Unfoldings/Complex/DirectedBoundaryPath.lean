module

public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Geometry.EdgeParameters

/-! The genuine affine path along a boundary bank in its directed endpoint order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- Parameterize a closed bank starting at either of its actual endpoints. -/
def bankParameterFromEnd (bank : C.BoundaryBank retain) (side : Bool) (t : unitInterval) :
    (C.triangle bank.val.face).Edge bank.val.edge :=
  ⟨AffineMap.lineMap ((C.triangle bank.val.face).endpoint bank.val.edge side).val
      ((C.triangle bank.val.face).endpoint bank.val.edge (!side)).val t.val,
    (C.triangle bank.val.face).lineMap_endpoints_mem_edge bank.val.edge side t.property⟩

/-- Keep the actual bank label while following its prescribed starting endpoint. -/
def directedBoundaryPath (p : C.BoundaryEnd retain) (t : unitInterval) : C.Realization retain :=
  C.bankMap retain (C.boundaryEndEquiv retain p).1
    (C.bankParameterFromEnd (C.boundaryEndEquiv retain p).1 (C.boundaryEndEquiv retain p).2 t)

theorem bankParameterFromEnd_nonvertex (bank : C.BoundaryBank retain) (side : Bool)
    (t : unitInterval) (positive : 0 < t.val) (small : t.val < 1) :
    ¬ (C.triangle bank.val.face).IsVertex (C.bankParameterFromEnd bank side t).val :=
  (C.triangle bank.val.face).lineMap_endpoints_not_vertex bank.val.edge side ⟨positive, small⟩

theorem directedBoundaryPath_mem_boundary (p : C.BoundaryEnd retain) (t : unitInterval) :
    C.directedBoundaryPath p t ∈ C.bankBoundary retain :=
  C.bankMap_mem_bankBoundary retain _ _

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

/-- Physical bank interpolation uses its genuine initial position and its whole edge vector. -/
theorem directedBoundaryPath_position (p : C.BoundaryEnd retain) (t : unitInterval) :
    F.toSpace retain (C.directedBoundaryPath p t) =
      F.boundaryPosition p + t.val • F.germDirection p.val := by
  obtain ⟨⟨bank, side⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  rcases bank with ⟨⟨face, edge⟩, boundary⟩
  cases side <;> fin_cases edge
  all_goals
    rw [F.boundaryPosition_raw]
    change F.place face (AffineMap.lineMap _ _ t.val) =
      F.place face _ + t.val • (F.place face _ - F.place face _)
    calc
      _ = AffineMap.lineMap (F.place face _) (F.place face _) t.val :=
        (F.place face).toAffineMap.apply_lineMap _ _ _
      _ = _ := by
        rw [AffineMap.lineMap_apply_module']
        exact add_comm _ _

end Unfoldings.SpatialFolding
