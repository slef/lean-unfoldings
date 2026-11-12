module

public import Unfoldings.Cap.CompletedBankFaceValues
public import Unfoldings.Cap.CompletedParentBankSides

/-! Actual complete-bank incident faces lie on their named physical sides of the parent edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem projected_bank_side_nonneg {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    (positive : 0 < K.projectedGermOrientation p.val) {x : Plane}
    (member : x ∈ (K.projectedTriangle p.val.1.1).carrier) :
    0 ≤ orient
      (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p)))
      (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain (C.boundaryTurn retain p)))) x := by
  simpa only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    C.boundaryTurn_corner, K.projectedVertex_ofCorner, K.projectedTriangle_vertex,
    K.projectFace_apply, TriangleComplex.germFarCorner] using
      K.projectedGerm_side_nonneg p.val positive member

end Unfoldings.ConvexCap

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

theorem parent_entrance_face_side
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    {x : Plane} (member : x ∈ (K.projectedTriangle
      (N.parentBankOpening D e).entranceFace).carrier) :
    orient (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) x ≤ 0 := by
  let O := N.parentBankOpening D e
  have positive := D.projectedGermOrientation_cycle_positive K N.completedDuallyConnected
    N.completedContour.cycle N.completedContour_positive O.enter
  have side := K.projected_bank_side_nonneg (N.completedContour.cycle.point O.enter)
    positive member
  have child : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.enter))) = e.val :=
    (C.selected_parent_bank_enters N.spanningCompletion.selection e.val e.property
      (N.completedContour.cycle.point O.enter) O.side O.first_named O.outside).2
  rw [O.entrance_vertex, child,
    orient_swap (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) x] at side
  exact neg_nonneg.mp side

theorem parent_exit_face_side
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    {x : Plane} (member : x ∈ (K.projectedTriangle
      (N.parentBankOpening D e).exitFace).carrier) :
    0 ≤ orient (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) x := by
  let O := N.parentBankOpening D e
  have positive := D.projectedGermOrientation_cycle_positive K N.completedDuallyConnected
    N.completedContour.cycle N.completedContour_positive O.leave
  have side := K.projected_bank_side_nonneg (N.completedContour.cycle.point O.leave)
    positive member
  have parent : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave))) =
      N.spanningCompletion.parents.parent e.val :=
    (C.selected_parent_bank_leaves N.spanningCompletion.selection e.val e.property
      (N.completedContour.cycle.point O.leave) (!O.side) O.last_named O.inside).2
  rwa [O.exit_vertex, parent] at side

end Unfoldings.ConvexCap.RadialCutForest
