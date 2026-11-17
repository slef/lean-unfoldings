module

public import Unfoldings.Complex.ClosedBanks
public import Unfoldings.Complex.DirectedBoundaryPathBank
public import Unfoldings.Polyhedron.DirectedBankMetric

/-! Both labeled cut banks retain the same physical edge and its original endpoint status. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

/-- Read either labeled bank in the original left-edge coordinates. -/
def cutBankLeftParameterEquiv (s : C.CutSeam retain) (side : Bool) :
    (C.triangle (C.cutBank retain s side).val.face).Edge (C.cutBank retain s side).val.edge ≃ᵢ
      (C.triangle (C.left s.val).face).Edge (C.left s.val).edge := by
  cases side
  · exact IsometryEquiv.refl _
  · exact (C.identify s.val).symm

/-- Bank-coordinate transport preserves precisely the original endpoint status. -/
theorem cutBankLeftParameter_isVertex_iff (s : C.CutSeam retain) (side : Bool)
    (q : (C.triangle (C.cutBank retain s side).val.face).Edge
      (C.cutBank retain s side).val.edge) :
    (C.triangle (C.left s.val).face).IsVertex (C.cutBankLeftParameterEquiv retain s side q).val ↔
      (C.triangle (C.cutBank retain s side).val.face).IsVertex q.val :=
  Triangle.edge_isometry_isVertex_iff _ _ _ _ (C.cutBankLeftParameterEquiv retain s side) q

/-- Original interval endpoints remain original triangle vertices. -/
theorem bankParameterFromEnd_isVertex_of_endpoint {retain : Set C.Seam}
    (bank : C.BoundaryBank retain) (side : Bool) (u : unitInterval)
    (endpoint : u.val = 0 ∨ u.val = 1) :
    (C.triangle bank.val.face).IsVertex (C.bankParameterFromEnd bank side u).val := by
  change (C.triangle bank.val.face).IsVertex (AffineMap.lineMap
    ((C.triangle bank.val.face).endpoint bank.val.edge side).val
    ((C.triangle bank.val.face).endpoint bank.val.edge (!side)).val u.val)
  rcases endpoint with first | last
  · rw [first, AffineMap.lineMap_apply_zero]
    exact (C.triangle bank.val.face).isVertex_endpoint bank.val.edge side
  · rw [last, AffineMap.lineMap_apply_one]
    exact (C.triangle bank.val.face).isVertex_endpoint bank.val.edge (!side)

end Unfoldings.TriangleComplex
namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam)

/-- Reading the other cut bank in left-edge coordinates keeps the full spatial point. -/
theorem toSpace_cutBank_left_parameter (s : C.CutSeam retain) (side : Bool)
    (q : (C.triangle (C.cutBank retain s side).val.face).Edge
      (C.cutBank retain s side).val.edge) :
    F.toSpace retain (C.bankMap retain (C.cutBank retain s side) q) =
      F.place (C.left s.val).face (C.cutBankLeftParameterEquiv retain s side q).val := by
  have folded := F.toSpace_bankMap (C.cutBank retain s side) q
  cases side
  · exact folded
  · have joined := F.joined s.val ((C.identify s.val).symm q)
    have physical := congrArg (fun z => F.place (C.right s.val).face z.val)
      ((C.identify s.val).apply_symm_apply q)
    exact folded.trans (joined.trans physical).symm

end Unfoldings.SpatialFolding
