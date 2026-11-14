module

public import Unfoldings.Geometry.ChordPerturbation
public import Unfoldings.Geometry.ComplexRotation

/-! Aligned chord control transports radial margins and length constants to actual bank frames. -/

@[expose] public section

namespace Unfoldings

theorem radial_margin_of_aligned_chord_error {r q v : ℂ} (anchor : ℝ) {δ d : ℝ}
    (nonnegative : 0 ≤ δ) (small : δ < d)
    (error : ‖polarRay (-anchor) * q - r‖ ≤ δ * ‖r‖)
    (margin : d * (‖r‖ * ‖v‖) ≤ inner ℝ r v) :
    ((d - δ) / (1 + δ)) * (‖q‖ * ‖polarRay anchor * v‖) ≤
      inner ℝ q (polarRay anchor * v) := by
  have estimate := radial_margin_of_chord_error nonnegative small error margin
  have inner_equal := (complexRotation (-anchor)).inner_map_map q (complexRotation anchor v)
  rw [complexRotation_neg_cancel] at inner_equal
  simp only [complexRotation_apply] at inner_equal
  rw [inner_equal] at estimate
  simpa only [norm_mul, norm_polarRay, one_mul] using estimate

theorem length_constant_of_aligned_chord_error {r q : ℂ} (anchor : ℝ) {δ length D : ℝ}
    (nonnegative : 0 ≤ D) (small : δ < 1)
    (error : ‖polarRay (-anchor) * q - r‖ ≤ δ * ‖r‖)
    (length_bound : length ≤ D * ‖r‖) : length ≤ (D / (1 - δ)) * ‖q‖ := by
  have estimate := length_constant_of_chord_error nonnegative small error length_bound
  simpa only [norm_mul, norm_polarRay, one_mul] using estimate

end Unfoldings
