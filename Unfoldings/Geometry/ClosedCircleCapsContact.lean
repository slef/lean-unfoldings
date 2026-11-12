module

public import Unfoldings.Geometry.WeakCircleCaps
public import Unfoldings.Geometry.BankRadialOrder

/-! Ordered closed circle portions can meet only at their common named endpoint. -/

@[expose] public section

namespace Unfoldings

theorem weak_circle_caps_contact_eq_of_horizontal_order (frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (center upper lower : Plane) {radius : ℝ}
    (upper_radius : ‖upper - center‖ = radius) (lower_radius : ‖lower - center‖ = radius)
    (upper_quadrant : 0 ≤ (frame (upper - center)).re ∧ 0 ≤ (frame (upper - center)).im)
    (lower_quadrant : 0 ≤ (frame (lower - center)).re ∧ 0 ≤ (frame (lower - center)).im)
    (ordered : (frame (upper - center)).re ≤ (frame (lower - center)).re)
    {p : Plane}
    (first : p ∈ weakCircleUpperCap frame center radius (frame (upper - center)).re)
    (last : p ∈ weakCircleLowerCap frame center radius (frame (lower - center)).im) :
    p = upper ∧ upper = lower := by
  have size : ‖frame (lower - center)‖ = ‖frame (p - center)‖ := by
    simpa only [frame.norm_map] using lower_radius.trans first.2.2.2.symm
  have squares := congrArg (fun r : ℝ => r ^ 2) size
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at squares
  have reverse := (quadrant_circle_order lower_quadrant.1 lower_quadrant.2
    first.1 first.2.1.le (by simpa only [pow_two] using squares)
    (Or.inr last.2.2.1)).1
  have horizontal : (frame (p - center)).re = (frame (upper - center)).re :=
    le_antisymm first.2.2.1 (ordered.trans reverse)
  have first_equal : frame (p - center) = frame (upper - center) := by
    apply complex_eq_of_norm_re_eq
    · simpa only [frame.norm_map] using first.2.2.2.trans upper_radius.symm
    · exact horizontal
    · exact first.2.1.le
    · exact upper_quadrant.2
  have last_equal : frame (upper - center) = frame (lower - center) := by
    apply complex_eq_of_norm_re_eq
    · simpa only [frame.norm_map] using upper_radius.trans lower_radius.symm
    · exact le_antisymm ordered (by rw [← horizontal]; exact reverse)
    · exact upper_quadrant.2
    · exact lower_quadrant.2
  have first_displacement : p - center = upper - center := frame.injective first_equal
  have last_displacement : upper - center = lower - center := frame.injective last_equal
  exact ⟨sub_left_inj.mp first_displacement, sub_left_inj.mp last_displacement⟩

end Unfoldings
