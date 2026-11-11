module

public import Unfoldings.Cap.CompletedSectorQuadrants
public import Unfoldings.Cap.CompletedParentBankOpening
public import Unfoldings.Geometry.QuadrantRotationOrder

/-! Actual completed-parent vectors are ordered by their signed subtree curvature in any sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem completed_parent_direction_ne_zero (w : C.Vertex Set.univ)
    (nonroot : w ∉ R.spanningCompletion.parents.roots) :
    K.projectedVertex (R.spanningCompletion.parents.parent w) - K.projectedVertex w ≠ 0 := by
  intro zero
  have equal := K.projectedVertex_injective (sub_eq_zero.mp zero)
  have ascending := R.spanningCompletion.parents.ascending w nonroot
  rw [equal] at ascending
  exact lt_irrefl _ ascending

namespace FiveSectorFrameData

variable {R} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {D : FacewiseDevelopment C R.completedRetain} (B : R.FiveSectorFrameData positive small D)

def framedDirection (i : FiveSector) (f : Face) (direction : Plane) : ℂ :=
  (Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place)
    (R.calibratedFrame D B.anchor B.reference (D.developedDirection K f direction))

/-- Numerical sector coordinates preserve the actual positive whole-subtree bank rotation. -/
theorem parent_rotation (i : FiveSector)
    {e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots}}
    (O : R.ParentBankOpening D e) :
    B.framedDirection i O.exitFace
        (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val) =
      polarRay (R.completedSubtreeCurvature e.val) *
        B.framedDirection i O.entranceFace
          (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex
            e.val) := by
  let direction := K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
    K.projectedVertex e.val
  let L := R.calibratedFrame D B.anchor B.reference
  let S := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place
  have calibrated : L (D.developedDirection K O.exitFace direction) =
      polarRay (R.completedSubtreeCurvature e.val) *
        L (D.developedDirection K O.entranceFace direction) := by
    change polarRay (R.calibrationAngle D B.anchor B.reference) *
      D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K O.exitFace direction) = _
    have rotation := O.rotation
    change D.boundaryCycleFrame R.completedContour.cycle
      (D.developedDirection K O.exitFace direction) =
        polarRay (R.completedSubtreeCurvature e.val) *
          D.boundaryCycleFrame R.completedContour.cycle
            (D.developedDirection K O.entranceFace direction) at rotation
    rw [rotation]
    change _ = polarRay (R.completedSubtreeCurvature e.val) *
      (polarRay (R.calibrationAngle D B.anchor B.reference) *
        D.boundaryCycleFrame R.completedContour.cycle
          (D.developedDirection K O.entranceFace direction))
    ring
  have transformed := congrArg S calibrated
  rw [fiveSectorFrame_commutes_mul t positive small i] at transformed
  exact transformed

/-- A nonnegative curvature opening between two actual quadrant vectors orders their coordinates. -/
theorem parent_vector_order (i : FiveSector)
    {e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots}}
    (O : R.ParentBankOpening D e)
    (inside : K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    (B.framedDirection i O.exitFace
        (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex
          e.val)).re ≤
      (B.framedDirection i O.entranceFace
        (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex
          e.val)).re ∧
    (B.framedDirection i O.entranceFace
        (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex
          e.val)).im ≤
      (B.framedDirection i O.exitFace
        (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex
          e.val)).im := by
  have genuine := R.completed_parent_direction_ne_zero e.val e.property
  have first := B.quadrants i O.entranceFace _ inside genuine
  have last := B.quadrants i O.exitFace _ inside genuine
  exact quadrant_rotation_coordinate_order (R.completedSubtreeCurvature_nonneg e.val)
    ((R.completedSubtreeCurvature_le_total e.val).trans budget) (B.parent_rotation i O)
    first.1.le first.2.le last.1.le last.2.le

end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
