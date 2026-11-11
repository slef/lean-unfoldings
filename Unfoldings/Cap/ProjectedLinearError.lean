module

public import Unfoldings.Cap.DevelopedDirectionNorm
public import Unfoldings.Geometry.AngleNormError

/-! Derive uniform linear chart error from actual angular calibration and normal bounds. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

theorem exists_coordinatePlacement_linear_error_threshold {ε : ℝ} (positive : 0 < ε) :
    ∃ δ > 0, ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
      {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)
      (calibration : Plane ≃ₗᵢ[ℝ] ℂ),
      (∀ f, (1 + δ)⁻¹ ≤ K.normal f 2) →
      (∀ f (direction : Plane), direction ≠ 0 →
        InnerProductGeometry.angle (calibration (D.developedDirection K f direction))
          (Complex.orthonormalBasisOneI.repr.symm direction) < δ) →
      ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f (z : ℂ),
        ‖(D.coordinatePlacement K calibration frame f).linear z - z‖ ≤ ε * ‖z‖ := by
  obtain ⟨δ, δpositive, control⟩ := exists_angle_norm_error_threshold (E := ℂ) positive
  refine ⟨δ, δpositive, fun D K calibration normal close frame f z => ?_⟩
  by_cases zero : z = 0
  · simp only [zero, map_zero, sub_zero, norm_zero, mul_zero, le_refl]
  · have lengths := D.coordinatePlacement_norm_bounds K calibration frame f z
    have positive_factor : 0 < 1 + δ := by linarith
    have normal_bound := (mul_le_mul_of_nonneg_right (normal f)
      (norm_nonneg ((D.coordinatePlacement K calibration frame f).linear z))).trans lengths.2
    have upper : ‖(D.coordinatePlacement K calibration frame f).linear z‖ ≤
        (1 + δ) * ‖z‖ := by
      calc
        _ = (1 + δ) * ((1 + δ)⁻¹ *
            ‖(D.coordinatePlacement K calibration frame f).linear z‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ positive_factor.ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left normal_bound positive_factor.le
    apply control _ _ lengths.1 upper
    rw [InnerProductGeometry.angle_comm]
    exact (D.coordinatePlacement_angle K calibration frame close f z zero).le

end Unfoldings.FacewiseDevelopment
