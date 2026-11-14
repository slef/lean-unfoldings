module

public import Unfoldings.Geometry.SphericalConvex
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Explicit orthogonal frames put any chosen unit hemisphere center at the north pole. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

theorem northLift_zero_unit : ‖northLift 0‖ = 1 := by
  have square : ‖northLift 0‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    norm_num [northLift]
  nlinarith [norm_nonneg (northLift 0)]

/-- A Householder reflection suffices; orientation is immaterial to normal selection topology. -/
def northFrame (center : Space) : Space ≃ₗᵢ[ℝ] Space :=
  (ℝ ∙ (center - northLift 0))ᗮ.reflection

theorem northFrame_center (center : Space) (unit : ‖center‖ = 1) :
    northFrame center center = northLift 0 :=
  Submodule.reflection_sub (unit.trans northLift_zero_unit.symm)

theorem northFrame_height (center : Space) (unit : ‖center‖ = 1) (z : Space) :
    northFrame center z 2 = inner ℝ center z := by
  have pairing := (northFrame center).inner_map_map center z
  rw [northFrame_center center unit, horizontal_inner, northLift_horizontal,
    northLift_height] at pairing
  simpa only [inner_zero_left, one_mul, zero_add] using pairing

end Unfoldings.Cap
