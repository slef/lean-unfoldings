module

public import Unfoldings.Geometry.RadialCornerSector

/-! Convert angular deviation bounds to literal heading intervals away from the branch cut. -/

@[expose] public section

namespace Unfoldings

open InnerProductGeometry Real

/-- A deviation from a prescribed heading gives a real interval of arguments
when the entire interval misses the branch cut. -/
theorem arg_mem_Icc_of_angle_polarRay_le {z : ℂ} (nonzero : z ≠ 0) {heading radius : ℝ}
    (above : -π < heading - radius) (below : heading + radius ≤ π)
    (near : angle (polarRay heading) z ≤ radius) :
    z.arg ∈ Set.Icc (heading - radius) (heading + radius) := by
  let w := z / polarRay heading
  have w_ne : w ≠ 0 := div_ne_zero nonzero (polarRay_ne_zero _)
  have bound : |w.arg| ≤ radius := by
    rw [angle_comm, Complex.angle_eq_abs_arg nonzero (polarRay_ne_zero _)] at near
    exact near
  have lower : heading - radius ≤ w.arg + heading := by linarith only [(abs_le.mp bound).1]
  have upper : w.arg + heading ≤ heading + radius := by linarith only [(abs_le.mp bound).2]
  have representation : (‖w‖ : ℂ) * polarRay (w.arg + heading) = z := by
    rw [polarRay_add, ← mul_assoc]
    have form : (‖w‖ : ℂ) * polarRay w.arg = w := Complex.norm_mul_exp_arg_mul_I w
    rw [form]
    exact div_mul_cancel₀ _ (polarRay_ne_zero _)
  have argument : z.arg = w.arg + heading := by
    rw [← representation]
    convert Complex.arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr w_ne)
      ⟨above.trans_le lower, upper.trans below⟩ using 2
    change (‖w‖ : ℂ) * Complex.exp (((w.arg + heading : ℝ) : ℂ) * Complex.I) = _
    rw [Complex.ofReal_add, Complex.exp_mul_I]
  exact ⟨argument ▸ lower, argument ▸ upper⟩

end Unfoldings
