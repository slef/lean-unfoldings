module

public import Unfoldings.Cone.Sector

/-! Real-linear isometries for the actual unit complex rotations used by bank headings. -/

@[expose] public section

namespace Unfoldings

noncomputable def complexRotation (θ : ℝ) : ℂ →ₗᵢ[ℝ] ℂ where
  toLinearMap := LinearMap.mulLeft ℝ (polarRay θ)
  norm_map' z := by rw [LinearMap.mulLeft_apply, norm_mul, norm_polarRay, one_mul]

@[simp] theorem complexRotation_apply (θ : ℝ) (z : ℂ) :
    complexRotation θ z = polarRay θ * z := rfl

theorem complexRotation_neg_cancel (θ : ℝ) (z : ℂ) :
    complexRotation (-θ) (complexRotation θ z) = z := by
  rw [complexRotation_apply, complexRotation_apply, ← mul_assoc, ← polarRay_add,
    neg_add_cancel, polarRay_zero, one_mul]

end Unfoldings
