module

public import Unfoldings.Cap.CompletedBranchJumpOrder
public import Unfoldings.Cap.CompletedParentRayCounter

/-! Every actual complete bank point is its own incident-face placement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem projectedPlacement_boundary_vertex (p : C.BoundaryEnd retain) :
    D.projectedPlacement K p.val.1.1 (K.projectedVertex
      (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p))) =
        D.boundaryPosition p := by
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    K.projectedVertex_ofCorner]
  rw [K.projectedTriangle_vertex, ← K.projectFace_apply, D.projectedPlacement_apply]
  exact D.linkGerm_apex (⟨p.val, rfl⟩ : C.LinkGerm retain
    (C.vertexOfCorner retain p.val.1))

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem projected_bank_segment_mem_face {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    {s : ℝ} (inside : s ∈ Set.Icc 0 1) :
    AffineMap.lineMap
      (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain p)))
      (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain (C.boundaryTurn retain p)))) s ∈
      (K.projectedTriangle p.val.1.1).carrier := by
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    C.boundaryTurn_corner, K.projectedVertex_ofCorner]
  apply (K.projectedTriangle p.val.1.1).convex_carrier.lineMap_mem
    ((K.projectedTriangle p.val.1.1).vertex_mem p.val.1.2) _ inside
  exact (K.projectedTriangle p.val.1.1).vertex_mem (C.germFarCorner p.val).2

end Unfoldings.ConvexCap

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

theorem parentEntrancePoint_eq_projectedPlacement
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) (s : ℝ) :
    N.parentEntrancePoint D e s = D.projectedPlacement K
      (N.parentBankOpening D e).entranceFace
      (AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
        (K.projectedVertex e.val) s) := by
  let O := N.parentBankOpening D e
  have position := D.projectedPlacement_boundary_vertex K (N.completedContour.cycle.point O.enter)
  rw [O.entrance_vertex] at position
  let a := K.projectedVertex (N.spanningCompletion.parents.parent e.val)
  let b := K.projectedVertex e.val
  let A := D.projectedPlacement K O.entranceFace
  have linear := A.toAffineMap.linear_apply_vsub (AffineMap.lineMap a b s) a
  change A.linear (AffineMap.lineMap a b s - a) = A (AffineMap.lineMap a b s) - A a at linear
  have displacement : AffineMap.lineMap a b s - a = -(s • (a - b)) := by
    rw [AffineMap.lineMap_apply_module']
    module
  rw [displacement, map_neg, map_smul] at linear
  change -(s • N.parentEntryVector D e) = A (AffineMap.lineMap a b s) - A a at linear
  change A a = _ at position
  rw [position] at linear
  calc
    _ = -(s • N.parentEntryVector D e) +
        D.boundaryPosition (N.completedContour.cycle.point O.enter) := by
      dsimp only [parentEntrancePoint, O]
      abel
    _ = _ := eq_sub_iff_add_eq.mp linear

theorem parentExitPoint_eq_projectedPlacement
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) (s : ℝ) :
    N.parentExitPoint D e s = D.projectedPlacement K
      (N.parentBankOpening D e).exitFace
      (AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
        (K.projectedVertex e.val) s) := by
  let O := N.parentBankOpening D e
  have parent : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex N.completedRetain
      (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave))) =
        N.spanningCompletion.parents.parent e.val :=
    (C.selected_parent_bank_leaves N.spanningCompletion.selection e.val e.property
      (N.completedContour.cycle.point O.leave) (!O.side) O.last_named O.inside).2
  have position := D.projectedPlacement_boundary_vertex K
    (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave))
  rw [parent] at position
  let a := K.projectedVertex (N.spanningCompletion.parents.parent e.val)
  let b := K.projectedVertex e.val
  let A := D.projectedPlacement K O.exitFace
  change A a = _ at position
  have linear := A.toAffineMap.linear_apply_vsub (AffineMap.lineMap a b s) a
  change A.linear (AffineMap.lineMap a b s - a) = A (AffineMap.lineMap a b s) - A a at linear
  have displacement : AffineMap.lineMap a b s - a = -(s • (a - b)) := by
    rw [AffineMap.lineMap_apply_module']
    module
  rw [displacement, map_neg, map_smul] at linear
  change -(s • N.parentExitVector D e) = A (AffineMap.lineMap a b s) - A a at linear
  rw [position] at linear
  calc
    _ = -(s • N.parentExitVector D e) + D.boundaryPosition
        (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave)) := by
      dsimp only [parentExitPoint, O]
      abel
    _ = _ := eq_sub_iff_add_eq.mp linear

theorem parent_bank_points_mem_faces
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    {s : ℝ} (inside : s ∈ Set.Icc 0 1) :
    let p := AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s
    p ∈ (K.projectedTriangle (N.parentBankOpening D e).entranceFace).carrier ∧
      p ∈ (K.projectedTriangle (N.parentBankOpening D e).exitFace).carrier := by
  let O := N.parentBankOpening D e
  have first := K.projected_bank_segment_mem_face (N.completedContour.cycle.point O.enter) inside
  rw [O.entrance_vertex] at first
  have enter_child : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex N.completedRetain
      (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.enter))) = e.val :=
    (C.selected_parent_bank_enters N.spanningCompletion.selection e.val e.property
      (N.completedContour.cycle.point O.enter) O.side O.first_named O.outside).2
  rw [enter_child] at first
  have last := K.projected_bank_segment_mem_face
    (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave)) inside
  rw [C.boundaryTurn_involutive] at last
  have leave_parent : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave))) =
      N.spanningCompletion.parents.parent e.val :=
    (C.selected_parent_bank_leaves N.spanningCompletion.selection e.val e.property
      (N.completedContour.cycle.point O.leave) (!O.side) O.last_named O.inside).2
  rw [leave_parent, O.exit_vertex] at last
  exact ⟨first, last⟩

end Unfoldings.ConvexCap.RadialCutForest
