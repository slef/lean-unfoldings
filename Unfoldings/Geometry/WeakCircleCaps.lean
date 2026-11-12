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

end Unfoldings
