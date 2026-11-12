module

public import Unfoldings.Geometry.OrientedInnerBarriers
public import Unfoldings.Geometry.ComplexArea

/-! Circle portions bounded by one actual bank coordinate. -/

@[expose] public section

namespace Unfoldings

def circleUpperCap (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius bound : ℝ) : Set Plane :=
  {p | 0 ≤ (frame (p - center)).re ∧ 0 < (frame (p - center)).im ∧
    (frame (p - center)).re < bound ∧ ‖p - center‖ = radius}

def circleLowerCap (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius bound : ℝ) : Set Plane :=
  {p | 0 ≤ (frame (p - center)).re ∧ 0 < (frame (p - center)).im ∧
    (frame (p - center)).im < bound ∧ ‖p - center‖ = radius}

theorem circleUpperCap_mono (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius : ℝ)
    {a b : ℝ} (ordered : a ≤ b) :
    circleUpperCap frame center radius a ⊆ circleUpperCap frame center radius b :=
  fun _ member => ⟨member.1, member.2.1, member.2.2.1.trans_le ordered, member.2.2.2⟩

theorem circleLowerCap_mono (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (radius : ℝ)
    {a b : ℝ} (ordered : a ≤ b) :
    circleLowerCap frame center radius a ⊆ circleLowerCap frame center radius b :=
  fun _ member => ⟨member.1, member.2.1, member.2.2.1.trans_le ordered, member.2.2.2⟩

end Unfoldings
