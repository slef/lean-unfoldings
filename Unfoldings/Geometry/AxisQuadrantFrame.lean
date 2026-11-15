module

public import Unfoldings.Geometry.RobustQuadrant
public import Mathlib.Analysis.Complex.Basic

/-! A rigid frame puts an entire acute angular neighborhood of one ray in an open quadrant. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Rotate a prescribed actual complex axis to the middle of the first quadrant. -/
def complexAxisQuadrantFrame (axis : ℂ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  _root_.rotation (Circle.exp (Real.pi / 4 - axis.arg))

theorem complexAxisQuadrantFrame_axis (axis : ℂ) :
    complexAxisQuadrantFrame axis axis = (‖axis‖ : ℂ) * polarRay (Real.pi / 4) := by
  have polar := (Complex.norm_mul_exp_arg_mul_I axis).symm
  change axis = (‖axis‖ : ℂ) * polarRay axis.arg at polar
  change polarRay (Real.pi / 4 - axis.arg) * axis = _
  calc
    _ = polarRay (Real.pi / 4 - axis.arg) * ((‖axis‖ : ℂ) * polarRay axis.arg) :=
      congrArg (fun z => polarRay (Real.pi / 4 - axis.arg) * z) polar
    _ = (‖axis‖ : ℂ) * polarRay ((Real.pi / 4 - axis.arg) + axis.arg) := by
      rw [polarRay_add]
      ring
    _ = _ := by rw [sub_add_cancel]

/-- The same frame works for every ray in the open angular neighborhood, without an ordering. -/
theorem complexAxisQuadrantFrame_positive {axis ray : ℂ} (nonzero : axis ≠ 0)
    (close : InnerProductGeometry.angle axis ray < Real.pi / 4) :
    0 < (complexAxisQuadrantFrame axis ray).re ∧
      0 < (complexAxisQuadrantFrame axis ray).im := by
  let L := complexAxisQuadrantFrame axis
  have first : InnerProductGeometry.angle (1 : ℂ) (L axis) = Real.pi / 4 := by
    rw [complexAxisQuadrantFrame_axis]
    exact angle_one_mul_polarRay (norm_pos_iff.mpr nonzero) (by positivity)
      (by linarith [Real.pi_pos])
  have last : InnerProductGeometry.angle Complex.I (L axis) = Real.pi / 4 := by
    rw [complexAxisQuadrantFrame_axis,
      angle_I_mul_polarRay (norm_pos_iff.mpr nonzero) (by positivity)
        (by linarith [Real.pi_pos])]
    ring
  have mapped : InnerProductGeometry.angle (L axis) (L ray) < Real.pi / 4 := by
    exact (L.toLinearIsometry.angle_map axis ray).trans_lt close
  have real_positive := inner_pos_of_angle_close first.le mapped (by linarith)
  have imaginary_positive := inner_pos_of_angle_close last.le mapped (by linarith)
  constructor
  · simpa only [Complex.inner, map_one, mul_one] using real_positive
  · simpa [Complex.inner] using imaginary_positive

/-- Planar linear coordinates in the form required by radial closure construction. -/
def axisQuadrantFrame (axis : Plane) : (ℝ × ℝ) ≃ₗ[ℝ] Plane :=
  ((Complex.orthonormalBasisOneI.repr.symm.trans
    (complexAxisQuadrantFrame (Complex.orthonormalBasisOneI.repr.symm axis))).toLinearEquiv.trans
      Complex.equivRealProdCLM.toLinearEquiv).symm

/-- Every actual planar ray within a quarter-turn margin has two strictly positive coordinates. -/
theorem axisQuadrantFrame_positive {axis ray : Plane} (nonzero : axis ≠ 0)
    (close : InnerProductGeometry.angle axis ray < Real.pi / 4) :
    0 < ((axisQuadrantFrame axis).symm ray).1 ∧
      0 < ((axisQuadrantFrame axis).symm ray).2 := by
  let L := Complex.orthonormalBasisOneI.repr.symm
  have axis_ne : L axis ≠ 0 := by simpa only [map_zero] using L.injective.ne nonzero
  have angle : InnerProductGeometry.angle (L axis) (L ray) < Real.pi / 4 := by
    exact (L.toLinearIsometry.angle_map axis ray).trans_lt close
  exact complexAxisQuadrantFrame_positive axis_ne angle

end Unfoldings
