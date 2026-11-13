module

public import Unfoldings.Roof.ParentBankOpening
public import Unfoldings.Geometry.ThreeSectorFrames
public import Unfoldings.Geometry.ComplexRotationFrame

/-! Projection-preserving common frames for original roof developments and their sector banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

/-- A common frame retains its actual orientation and strict quadrants. Its construction may
use a distant completion anchor; no horizontal original rim anchor is required. -/
structure SectorFrameData (positive : 0 < t) (small : t < 1)
    (D : FacewiseDevelopment C M.retain) where
  frame : Plane ≃ₗᵢ[ℝ] ℂ
  projection_positive : ∀ (f : Face) (a b : Plane), 0 < orient 0 a b →
    0 < (starRingEnd ℂ (frame (D.roofDirection K f a)) * frame (D.roofDirection K f b)).im
  quadrants : ∀ (i : Fin 3) (f : Face) (direction : Plane),
    direction ∈ closedThreeSector t i → direction ≠ 0 →
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place) (frame (D.roofDirection K f direction))).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place) (frame (D.roofDirection K f direction))).im

theorem parent_direction_ne_zero (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    K.projectedVertex (M.parents.parent e) - K.projectedVertex e ≠ 0 := by
  intro zero
  have strict := M.direction e nonroot
  rw [zero] at strict
  change 0 < threeSectorCoordinates t (K.sourceSectorLabel t origin e) 0 0 ∧ _ at strict
  simp only [map_zero, PiLp.zero_apply, lt_self_iff_false, false_and] at strict

namespace SectorFrameData

variable {M} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

/-- The actual common frame preserves complex bank rotations of the oriented boundary frame. -/
theorem frame_commutes_mul (z w : ℂ) :
    B.frame ((D.boundaryCycleFrame M.projectionContour.cycle).symm (z * w)) =
      z * B.frame ((D.boundaryCycleFrame M.projectionContour.cycle).symm w) := by
  let A := D.boundaryCycleFrame M.projectionContour.cycle
  let F := A.symm.trans B.frame
  obtain ⟨f⟩ := K.nonempty_face
  let a : Plane := WithLp.toLp 2 ![1, 0]
  let b : Plane := WithLp.toLp 2 ![0, 1]
  have positive_area : 0 < orient 0 a b := by norm_num [a, b, orient]
  have original := M.projectionContour_frame_positive D f a b positive_area
  have mapped := B.projection_positive f a b positive_area
  have mapped' : 0 ≤ (starRingEnd ℂ (F (A (D.roofDirection K f a))) *
      F (A (D.roofDirection K f b))).im := by
    simpa only [F, LinearIsometryEquiv.trans_apply, A.symm_apply_apply] using mapped.le
  exact complex_isometry_commutes_mul_of_cross F (A (D.roofDirection K f a))
    (A (D.roofDirection K f b)) original mapped' z w

end SectorFrameData
end Unfoldings.ConvexRoof.SectorForest
