module

public import Unfoldings.Geometry.CircleCoordinateCaps

/-! Circle portions with weak bank bounds retain potential endpoint contacts. -/

@[expose] public section

namespace Unfoldings

def weakCircleUpperCap (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius bound : ℝ) : Set Plane :=
  {p | 0 ≤ (frame (p - center)).re ∧ 0 < (frame (p - center)).im ∧
    (frame (p - center)).re ≤ bound ∧ ‖p - center‖ = radius}

def weakCircleLowerCap (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius bound : ℝ) : Set Plane :=
  {p | 0 ≤ (frame (p - center)).re ∧ 0 < (frame (p - center)).im ∧
    (frame (p - center)).im ≤ bound ∧ ‖p - center‖ = radius}

theorem circleUpperCap_subset_weak (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius bound : ℝ) :
    circleUpperCap frame center radius bound ⊆ weakCircleUpperCap frame center radius bound :=
  fun _ member => ⟨member.1, member.2.1, member.2.2.1.le, member.2.2.2⟩

theorem circleLowerCap_subset_weak (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius bound : ℝ) :
    circleLowerCap frame center radius bound ⊆ weakCircleLowerCap frame center radius bound :=
  fun _ member => ⟨member.1, member.2.1, member.2.2.1.le, member.2.2.2⟩

theorem weakCircleUpperCap_mono (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius : ℝ)
    {a b : ℝ} (ordered : a ≤ b) :
    weakCircleUpperCap frame center radius a ⊆ weakCircleUpperCap frame center radius b :=
  fun _ member => ⟨member.1, member.2.1, member.2.2.1.trans ordered, member.2.2.2⟩

theorem weakCircleLowerCap_mono (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius : ℝ)
    {a b : ℝ} (ordered : a ≤ b) :
    weakCircleLowerCap frame center radius a ⊆ weakCircleLowerCap frame center radius b :=
  fun _ member => ⟨member.1, member.2.1, member.2.2.1.trans ordered, member.2.2.2⟩

/-- A circle has at most one point of a given real coordinate in the upper half-plane. -/
theorem complex_eq_of_norm_re_eq {z w : ℂ} (size : ‖z‖ = ‖w‖)
    (horizontal : z.re = w.re) (above_z : 0 ≤ z.im) (above_w : 0 ≤ w.im) : z = w := by
  have squares := congrArg (fun r : ℝ => r ^ 2) size
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at squares
  rw [horizontal] at squares
  apply Complex.ext horizontal
  nlinarith

/-- A circle has at most one point of a given imaginary coordinate in the right half-plane. -/
theorem complex_eq_of_norm_im_eq {z w : ℂ} (size : ‖z‖ = ‖w‖)
    (vertical : z.im = w.im) (right_z : 0 ≤ z.re) (right_w : 0 ≤ w.re) : z = w := by
  have squares := congrArg (fun r : ℝ => r ^ 2) size
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at squares
  rw [vertical] at squares
  apply Complex.ext _ vertical
  nlinarith

end Unfoldings
