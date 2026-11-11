module

public import Unfoldings.Cap.CompletedParentBankOpening
public import Unfoldings.Cap.RadialSourceCopy
public import Unfoldings.Development.BoundaryDisplacements

/-! The two actual banks at the distinguished source have one common intrinsic slit endpoint. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} {R : K.RadialCutForest q cuts}
  {D : FacewiseDevelopment C R.completedRetain}
  {e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots}}
  (B : R.ParentBankOpening D e)

/-- The no-wrap gap starts at one actual cut-surface vertex, even after all auxiliary cuts. -/
theorem source_child_vertices_eq (at_source : K.projectedVertex e.val = q) :
    C.boundaryEndVertex R.completedRetain
        (C.boundaryTurn R.completedRetain (R.completedContour.cycle.point B.enter)) =
      C.boundaryEndVertex R.completedRetain (R.completedContour.cycle.point B.leave) := by
  have internal : ¬ C.IsBoundaryVertex Set.univ e.val := fun boundary =>
    e.property ((Set.ext_iff.mp R.spanningCompletion.roots_eq e.val).mpr boundary)
  have first := (C.selected_parent_bank_enters R.spanningCompletion.selection e.val e.property
    (R.completedContour.cycle.point B.enter) B.side B.first_named B.outside).2
  have last := (C.selected_parent_bank_leaves R.spanningCompletion.selection e.val e.property
    (R.completedContour.cycle.point B.leave) (!B.side) B.last_named B.inside).1
  exact R.completed_source_copy_unique at_source internal _ _ first last

/-- Every actual development places both source-bank ends at the same point. -/
theorem source_child_points_eq (at_source : K.projectedVertex e.val = q) :
    D.boundaryPosition
        (C.boundaryTurn R.completedRetain (R.completedContour.cycle.point B.enter)) =
      D.boundaryPosition (R.completedContour.cycle.point B.leave) :=
  congrArg (fun w => D.toPlane (C.vertexPoint R.completedRetain w))
    (B.source_child_vertices_eq at_source)

end Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening
