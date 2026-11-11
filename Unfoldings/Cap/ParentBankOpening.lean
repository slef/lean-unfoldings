module

public import Unfoldings.Cap.PhaseSectionTurn

/-!
# Constructed actual oriented parent-bank opening data

This packages the actual contour entrances and exits already constructed from
the original-edge forest. It is output data, with its rigid rotation proved;
no opening or safe-bank certificate is added to the input cap.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Actual distinctly named banks, with endpoint order and rigid curvature phase proved. -/
structure ParentBankOpening (D : FacewiseDevelopment C M.retain)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) where
  enter : Fin (M.projectionContour.length + 1)
  leave : Fin (M.projectionContour.length + 1)
  side : Bool
  first_named : (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point enter)).1 =
    C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e.val e.property) side
  last_named : (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point leave)).1 =
    C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e.val e.property) (!side)
  outside : ¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e.val enter
  inside : C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e.val leave
  rotation : D.boundaryCycleFrame M.projectionContour.cycle
      (D.developedDirection K (M.projectionContour.cycle.point leave).val.1.1
        (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)) =
    polarRay (M.subtreeCurvature e.val) *
      D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (M.projectionContour.cycle.point enter).val.1.1
          (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val))

/-- Construct actual opening data from the forest and the actual rigid development. -/
def parentBankOpening (D : FacewiseDevelopment C M.retain)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) : M.ParentBankOpening D e :=
  Classical.choice (by
    obtain ⟨enter, leave, side, first, last, outside, inside, rotation⟩ :=
      M.exists_parent_direction_rotation D e.val e.property
    exact ⟨⟨enter, leave, side, first, last, outside, inside, rotation⟩⟩)

namespace ParentBankOpening

variable {M} {D : FacewiseDevelopment C M.retain}
  {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}} (B : M.ParentBankOpening D e)

def entranceFace : Face := (M.projectionContour.cycle.point B.enter).val.1.1

def exitFace : Face := (M.projectionContour.cycle.point B.leave).val.1.1

theorem entranceFace_eq : B.entranceFace = (C.seamSide (M.selection.edge e) B.side).face := by
  exact congrArg (fun bank : C.BoundaryBank M.retain => bank.val.face) B.first_named

theorem exitFace_eq : B.exitFace = (C.seamSide (M.selection.edge e) (!B.side)).face := by
  exact congrArg (fun bank : C.BoundaryBank M.retain => bank.val.face) B.last_named

/-- Transverse sections from the entrance face to the exit face have positive subtree phase. -/
theorem section_turn_le (direction : Plane)
    (transverse : orient 0
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) direction ≠ 0) :
    InnerProductGeometry.angle
      (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K B.entranceFace direction))
      (polarRay (-M.subtreeCurvature e.val) * D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K B.exitFace direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection B.entranceFace direction)
        (K.spatialDirection B.exitFace direction) := by
  have shared := K.spatialDirection_parent_banks M.selection e.val e.property
    (M.projectionContour.cycle.point B.enter) (M.projectionContour.cycle.point B.leave)
    B.side B.first_named B.last_named B.outside B.inside
  exact M.section_angle_le_of_frame_rotation D _ _ _ shared _ B.rotation direction transverse

/-- Traversing the same actual two banks in reverse negates the phase. -/
theorem reverse_section_turn_le (direction : Plane)
    (transverse : orient 0
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) direction ≠ 0) :
    InnerProductGeometry.angle
      (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K B.exitFace direction))
      (polarRay (M.subtreeCurvature e.val) * D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K B.entranceFace direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection B.exitFace direction)
        (K.spatialDirection B.entranceFace direction) := by
  have previous := B.section_turn_le direction transverse
  have cancel : polarRay (M.subtreeCurvature e.val) * polarRay (-M.subtreeCurvature e.val) = 1 := by
    rw [← polarRay_add, add_neg_cancel, polarRay_zero]
  have rotated := (Complex.angle_mul_left (polarRay_ne_zero (M.subtreeCurvature e.val))
    (D.boundaryCycleFrame M.projectionContour.cycle
      (D.developedDirection K B.entranceFace direction))
    (polarRay (-M.subtreeCurvature e.val) * D.boundaryCycleFrame M.projectionContour.cycle
      (D.developedDirection K B.exitFace direction)))
  rw [← mul_assoc, cancel, one_mul, InnerProductGeometry.angle_comm] at rotated
  rw [rotated, InnerProductGeometry.angle_comm
    (K.spatialDirection B.exitFace direction) (K.spatialDirection B.entranceFace direction)]
  exact previous

end ParentBankOpening
end Unfoldings.ConvexCap.SectorForest
