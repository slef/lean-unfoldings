module

public import Unfoldings.Roof.SectorQuadrants
public import Unfoldings.Roof.ParentBankOpening
public import Unfoldings.Geometry.QuadrantRotationOrder
public import Unfoldings.Geometry.WedgeRotationFrame

/-!
# Actual branching parent-bank vector order in common sector quadrants

The calibrated frame and the three numerical sector frames preserve the actual
signed subtree rotation. Both directed parent-bank vectors lie in one open
quadrant. Their exact nonnegative curvature opening therefore orders their
coordinates, including every attached branch and zero-curvature contact.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

/-- One sector's fixed quadrant coordinates, using the same global actual calibration. -/
def framedDirection (i : Fin 3) (f : Face) (direction : Plane) : ℂ :=
  (Complex.orthonormalBasisOneI.repr.trans (threeSectorFrame t positive small i).place)
    (B.frame (D.roofDirection K f direction))

/-- Every developed parent direction lies strictly in its sector quadrant. -/
theorem parent_quadrants (f : Face) (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    0 < (B.framedDirection (K.sourceSectorLabel t origin e) f
      (K.projectedVertex (M.parents.parent e) - K.projectedVertex e)).re ∧
    0 < (B.framedDirection (K.sourceSectorLabel t origin e) f
      (K.projectedVertex (M.parents.parent e) - K.projectedVertex e)).im :=
  B.quadrants _ f _ (strictThreeSector_subset_closed t _ (M.direction e nonroot))
    (M.parent_direction_ne_zero e nonroot)

/-- The fixed quadrant frame preserves the actual positive whole-subtree bank rotation. -/
theorem parent_rotation {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}}
    (O : M.ParentBankOpening D e) :
    B.framedDirection (K.sourceSectorLabel t origin e.val) O.exitFace
        (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) =
      polarRay (M.subtreeCurvature e.val) *
        B.framedDirection (K.sourceSectorLabel t origin e.val) O.entranceFace
          (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
  let i := K.sourceSectorLabel t origin e.val
  let direction := K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val
  let R := B.frame
  let S := Complex.orthonormalBasisOneI.repr.trans (threeSectorFrame t positive small i).place
  have calibrated : R (D.roofDirection K O.exitFace direction) =
      polarRay (M.subtreeCurvature e.val) *
        R (D.roofDirection K O.entranceFace direction) := by
    let A := D.boundaryCycleFrame M.projectionContour.cycle
    have opening := congrArg (fun z : ℂ => B.frame (A.symm z)) O.rotation
    rw [B.frame_commutes_mul] at opening
    simpa only [A, R, direction, ParentBankOpening.exitFace, ParentBankOpening.entranceFace,
      LinearIsometryEquiv.symm_apply_apply] using opening
  have transformed := congrArg S calibrated
  have commutes := (threeSectorFrame t positive small i).complex_frame_commutes_mul
    (threeSector_banks_orient_pos positive small i) (polarRay (M.subtreeCurvature e.val))
    (R (D.roofDirection K O.entranceFace direction))
  rw [commutes] at transformed
  exact transformed

/-- Actual matched parent-bank vectors are ordered left/up by their entire descendant curvature. -/
theorem parent_vector_order {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}}
    (O : M.ParentBankOpening D e) (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    (B.framedDirection (K.sourceSectorLabel t origin e.val) O.exitFace
        (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)).re ≤
      (B.framedDirection (K.sourceSectorLabel t origin e.val) O.entranceFace
        (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)).re ∧
    (B.framedDirection (K.sourceSectorLabel t origin e.val) O.entranceFace
        (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)).im ≤
      (B.framedDirection (K.sourceSectorLabel t origin e.val) O.exitFace
        (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)).im := by
  have first := B.parent_quadrants O.entranceFace e.val e.property
  have last := B.parent_quadrants O.exitFace e.val e.property
  exact quadrant_rotation_coordinate_order (M.subtreeCurvature_nonneg e.val)
    ((M.subtreeCurvature_le_total e.val).trans budget) (B.parent_rotation O)
    first.1.le first.2.le last.1.le last.2.le

end Unfoldings.ConvexRoof.SectorForest.SectorFrameData
