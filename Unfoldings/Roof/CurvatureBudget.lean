module

public import Unfoldings.Roof.CurvatureNonnegative

public import Unfoldings.Roof.AngularCurvature
public import Unfoldings.Roof.SolidNormalArea
public import Unfoldings.Complex.Curvature

/-! Nonnegative intrinsic curvature and its mesh-independent small-tilt budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Actual curvature is bounded by the checked packing of all actual normal cones. -/
theorem ofReal_totalCurvature_le_solid_normal_area :
    ENNReal.ofReal (C.totalInteriorAngularDefect Set.univ) ≤
      ∑ v : C.Vertex Set.univ, solidAngleMeasure (K.sphericalNormalPolygon v) := by
  classical
  rw [TriangleComplex.totalInteriorAngularDefect,
    ENNReal.ofReal_sum_of_nonneg (fun v _ => K.interiorCurvature_nonneg v)]
  apply Finset.sum_le_sum
  intro v _
  by_cases boundary : C.IsBoundaryVertex Set.univ v
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary,
      ENNReal.ofReal_zero, zero_le]
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_right boundary,
      K.angular_defect_eq_solid_normal v boundary, le_refl]

/-- The positive threshold is chosen before the cap and is independent of its mesh size. -/
theorem exists_tilt_totalCurvature_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ K : ConvexRoof C, K.TiltBound φ →
      C.totalInteriorAngularDefect Set.univ < ε := by
  obtain ⟨φ, bounds, budget⟩ := exists_tilt_solid_normal_area_lt (C := C) positive
  refine ⟨φ, bounds, fun K tilt => ?_⟩
  have bound := K.ofReal_totalCurvature_le_solid_normal_area.trans_lt (budget K tilt)
  exact (ENNReal.ofReal_lt_ofReal_iff positive).mp bound

end Unfoldings.ConvexRoof
