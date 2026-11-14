module

public import Unfoldings.Geometry.GnomonicCollinearNull
public import Unfoldings.Roof.AngularCurvature
public import Unfoldings.Roof.CurvatureNonnegative

/-! Positive intrinsic curvature forces a genuinely two-dimensional original normal polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MeasureTheory

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem interiorCurvature_eq_zero_of_normalPolygon_collinear (v : C.Vertex Set.univ)
    (collinear : Collinear ℝ (K.normalPolygon v)) : C.interiorAngularDefect Set.univ v = 0 := by
  classical
  by_cases boundary : C.IsBoundaryVertex Set.univ v
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
  · have nonempty : (K.normalPolygon v).Nonempty := by
      obtain ⟨⟨f, i⟩, equal⟩ := C.vertexOfCorner_surjective Set.univ v
      exact ⟨K.normalSlope f, subset_convexHull ℝ _ ⟨f, i, equal, rfl⟩⟩
    have null := solidAngle_gnomonic_eq_zero_of_compact_convex_collinear
      (K.compact_normalPolygon v) (convex_convexHull ℝ _) nonempty collinear
    change solidAngleMeasure (K.sphericalNormalPolygon v) = 0 at null
    have identity := K.angular_defect_eq_solid_normal v boundary
    rw [null] at identity
    have nonpositive : C.interiorAngularDefect Set.univ v ≤ 0 := by
      rw [TriangleComplex.interiorAngularDefect, ite_eq_right boundary]
      exact ENNReal.ofReal_eq_zero.mp identity
    exact le_antisymm nonpositive (K.interiorCurvature_nonneg v)

/-- No small-tilt or minimum-normal-height assumption is needed. -/
theorem normalPolygon_interior_nonempty_of_positive_curvature (v : C.Vertex Set.univ)
    (curved : 0 < C.interiorAngularDefect Set.univ v) :
    (interior (K.normalPolygon v)).Nonempty := by
  by_contra empty
  have collinear := convex_collinear_of_empty_interior (convex_convexHull ℝ _)
    (Set.not_nonempty_iff_eq_empty.mp empty)
  exact curved.ne' (K.interiorCurvature_eq_zero_of_normalPolygon_collinear v collinear)

end Unfoldings.ConvexRoof
