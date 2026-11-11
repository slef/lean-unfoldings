module

public import Unfoldings.Cap.CompletedPhaseSectionTurn

/-! Construct actual oriented parent-bank opening data for completed extended roof cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

/-- Actual distinctly named banks, with endpoint order and rigid curvature phase proved. -/
structure ParentBankOpening (D : FacewiseDevelopment C R.completedRetain)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots}) where
  enter : Fin (R.completedContour.length + 1)
  leave : Fin (R.completedContour.length + 1)
  side : Bool
  first_named : (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point enter)).1 =
    C.relativeCutBank R.completedRetain Set.univ (C.selectedParentCut
      R.spanningCompletion.selection e.val e.property) side
  last_named : (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point leave)).1 =
    C.relativeCutBank R.completedRetain Set.univ (C.selectedParentCut
      R.spanningCompletion.selection e.val e.property) (!side)
  outside : ¬ C.SubtreeBoundaryInside R.spanningCompletion.selection R.completedContour.cycle
    e.val enter
  inside : C.SubtreeBoundaryInside R.spanningCompletion.selection R.completedContour.cycle e.val
    leave
  rotation : D.boundaryCycleFrame R.completedContour.cycle
      (D.developedDirection K (R.completedContour.cycle.point leave).val.1.1
        (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val)) =
    polarRay (R.completedSubtreeCurvature e.val) *
      D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K (R.completedContour.cycle.point enter).val.1.1
          (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val))

/-- Construct actual opening data from the forest and the actual rigid development. -/
def parentBankOpening (D : FacewiseDevelopment C R.completedRetain)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots}) : R.ParentBankOpening
      D e :=
  Classical.choice (by
    obtain ⟨enter, leave, side, first, last, outside, inside, rotation⟩ :=
      R.completed_parent_direction_rotation D e.val e.property
    exact ⟨⟨enter, leave, side, first, last, outside, inside, rotation⟩⟩)

namespace ParentBankOpening

variable {R} {D : FacewiseDevelopment C R.completedRetain}
  {e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots}} (B : R.ParentBankOpening
    D e)

def entranceFace : Face := (R.completedContour.cycle.point B.enter).val.1.1

def exitFace : Face := (R.completedContour.cycle.point B.leave).val.1.1

theorem entranceFace_eq : B.entranceFace = (C.seamSide (R.spanningCompletion.selection.edge e)
  B.side).face := by
  exact congrArg (fun bank : C.BoundaryBank R.completedRetain => bank.val.face) B.first_named

theorem exitFace_eq : B.exitFace = (C.seamSide (R.spanningCompletion.selection.edge e)
  (!B.side)).face := by
  exact congrArg (fun bank : C.BoundaryBank R.completedRetain => bank.val.face) B.last_named

/-- Transverse sections from the entrance face to the exit face have positive subtree phase. -/
theorem section_turn_le (direction : Plane)
    (transverse : orient 0
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val)
        direction ≠ 0) :
    InnerProductGeometry.angle
      (D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K B.entranceFace direction))
      (polarRay (-R.completedSubtreeCurvature e.val) * D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K B.exitFace direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection B.entranceFace direction)
        (K.spatialDirection B.exitFace direction) := by
  have shared := K.spatialDirection_parent_banks R.spanningCompletion.selection e.val e.property
    (R.completedContour.cycle.point B.enter) (R.completedContour.cycle.point B.leave)
    B.side B.first_named B.last_named B.outside B.inside
  exact R.section_angle_le_of_frame_rotation D _ _ _ shared _ B.rotation direction transverse

/-- Traversing the same actual two banks in reverse negates the phase. -/
theorem reverse_section_turn_le (direction : Plane)
    (transverse : orient 0
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val)
        direction ≠ 0) :
    InnerProductGeometry.angle
      (D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K B.exitFace direction))
      (polarRay (R.completedSubtreeCurvature e.val) * D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K B.entranceFace direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection B.exitFace direction)
        (K.spatialDirection B.entranceFace direction) := by
  have previous := B.section_turn_le direction transverse
  have cancel : polarRay (R.completedSubtreeCurvature e.val) * polarRay
    (-R.completedSubtreeCurvature e.val) = 1 := by
    rw [← polarRay_add, add_neg_cancel, polarRay_zero]
  have rotated := (Complex.angle_mul_left (polarRay_ne_zero (R.completedSubtreeCurvature e.val))
    (D.boundaryCycleFrame R.completedContour.cycle
      (D.developedDirection K B.entranceFace direction))
    (polarRay (-R.completedSubtreeCurvature e.val) * D.boundaryCycleFrame R.completedContour.cycle
      (D.developedDirection K B.exitFace direction)))
  rw [← mul_assoc, cancel, one_mul, InnerProductGeometry.angle_comm] at rotated
  rw [rotated, InnerProductGeometry.angle_comm
    (K.spatialDirection B.exitFace direction) (K.spatialDirection B.entranceFace direction)]
  exact previous

end ParentBankOpening
end Unfoldings.ConvexCap.RadialCutForest
