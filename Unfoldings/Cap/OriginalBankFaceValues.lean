module

public import Unfoldings.Cap.BankSegments
public import Unfoldings.Cap.CompletedBankFaceValues

/-! Every original parent-bank point is the actual affine placement of its incident face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (D : FacewiseDevelopment C M.retain)

theorem parentEntrancePoint_eq_projectedPlacement
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) :
    M.parentEntrancePoint D e s = D.projectedPlacement K
      (M.parentBankOpening D e).entranceFace
      (AffineMap.lineMap (K.projectedVertex (M.parents.parent e.val))
        (K.projectedVertex e.val) s) := by
  let O := M.parentBankOpening D e
  have position := D.projectedPlacement_boundary_vertex K (M.projectionContour.cycle.point O.enter)
  rw [O.entrance_vertex] at position
  let a := K.projectedVertex (M.parents.parent e.val)
  let b := K.projectedVertex e.val
  let A := D.projectedPlacement K O.entranceFace
  have linear := A.toAffineMap.linear_apply_vsub (AffineMap.lineMap a b s) a
  change A.linear (AffineMap.lineMap a b s - a) = A (AffineMap.lineMap a b s) - A a at linear
  have displacement : AffineMap.lineMap a b s - a = -(s • (a - b)) := by
    rw [AffineMap.lineMap_apply_module']
    module
  rw [displacement, map_neg, map_smul] at linear
  change -(s • M.parentEntryVector D e) = A (AffineMap.lineMap a b s) - A a at linear
  change A a = _ at position
  rw [position] at linear
  calc
    _ = -(s • M.parentEntryVector D e) +
        D.boundaryPosition (M.projectionContour.cycle.point O.enter) := by
      dsimp only [parentEntrancePoint, O]
      abel
    _ = _ := eq_sub_iff_add_eq.mp linear

theorem parentExitPoint_eq_projectedPlacement
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) :
    M.parentExitPoint D e s = D.projectedPlacement K
      (M.parentBankOpening D e).exitFace
      (AffineMap.lineMap (K.projectedVertex (M.parents.parent e.val))
        (K.projectedVertex e.val) s) := by
  let O := M.parentBankOpening D e
  have parent : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (C.boundaryTurn M.retain (M.projectionContour.cycle.point O.leave))) =
        M.parents.parent e.val :=
    (C.selected_parent_bank_leaves M.selection e.val e.property
      (M.projectionContour.cycle.point O.leave) (!O.side) O.last_named O.inside).2
  have position := D.projectedPlacement_boundary_vertex K
    (C.boundaryTurn M.retain (M.projectionContour.cycle.point O.leave))
  rw [parent] at position
  let a := K.projectedVertex (M.parents.parent e.val)
  let b := K.projectedVertex e.val
  let A := D.projectedPlacement K O.exitFace
  change A a = _ at position
  have linear := A.toAffineMap.linear_apply_vsub (AffineMap.lineMap a b s) a
  change A.linear (AffineMap.lineMap a b s - a) = A (AffineMap.lineMap a b s) - A a at linear
  have displacement : AffineMap.lineMap a b s - a = -(s • (a - b)) := by
    rw [AffineMap.lineMap_apply_module']
    module
  rw [displacement, map_neg, map_smul] at linear
  change -(s • M.parentExitVector D e) = A (AffineMap.lineMap a b s) - A a at linear
  rw [position] at linear
  calc
    _ = -(s • M.parentExitVector D e) + D.boundaryPosition
        (C.boundaryTurn M.retain (M.projectionContour.cycle.point O.leave)) := by
      dsimp only [parentExitPoint, O]
      abel
    _ = _ := eq_sub_iff_add_eq.mp linear

end Unfoldings.ConvexCap.SectorForest
