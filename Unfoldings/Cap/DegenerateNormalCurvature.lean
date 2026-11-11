module

public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Geometry.CollinearNull

/-! Collinear incident normal slopes give zero curvature at planar and crease subdivisions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A zero-area normal polygon gives zero intrinsic curvature, including boundary vertices. -/
theorem interiorCurvature_eq_zero_of_normalPolygon_null
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (v : C.Vertex Set.univ)
    (null : volume (K.normalPolygon v) = 0) : C.interiorAngularDefect Set.univ v = 0 := by
  classical
  by_cases boundary : C.IsBoundaryVertex Set.univ v
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
  · have solid := K.solidNormalPolygon_area_le height v
    rw [null, mul_zero] at solid
    have area_zero := le_antisymm solid bot_le
    have equal : ENNReal.ofReal (C.interiorAngularDefect Set.univ v) = 0 := by
      rw [TriangleComplex.interiorAngularDefect, ite_eq_right boundary,
        K.angular_defect_eq_solid_normal v boundary, area_zero]
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp equal) (K.interiorCurvature_nonneg v)

/-- Collinear incident slopes include the one-plane and two-plane crease cases. -/
theorem interiorCurvature_eq_zero_of_incidentSlopes_collinear
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (v : C.Vertex Set.univ)
    (collinear : Collinear ℝ (K.incidentSlopes v)) : C.interiorAngularDefect Set.univ v = 0 :=
  K.interiorCurvature_eq_zero_of_normalPolygon_null height v
    (volume_convexHull_eq_zero_of_collinear collinear)

/-- One planar face or two crease planes give no curvature at a subdivision vertex. -/
theorem interiorCurvature_eq_zero_of_two_incidentSlopes
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (v : C.Vertex Set.univ) (a b : Plane)
    (incident : ∀ f i, C.vertexOfCorner Set.univ (f, i) = v →
      K.normalSlope f = a ∨ K.normalSlope f = b) : C.interiorAngularDefect Set.univ v = 0 := by
  apply K.interiorCurvature_eq_zero_of_incidentSlopes_collinear height v
  apply Collinear.subset ?_ (collinear_pair ℝ a b)
  rintro x ⟨f, i, at_vertex, rfl⟩
  exact (incident f i at_vertex).elim
    (fun same => Set.mem_insert_iff.mpr (Or.inl same))
    (fun same => Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr same)))

end Unfoldings.ConvexCap
