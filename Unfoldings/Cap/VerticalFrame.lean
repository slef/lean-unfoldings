module

public import Unfoldings.Cap.VerticalProduct

/-! Extend any planar orthogonal frame to space while fixing the vertical coordinate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

def verticalFrame (L : Plane ≃ₗᵢ[ℝ] Plane) : Space ≃ₗᵢ[ℝ] Space :=
  (verticalProduct.trans (LinearIsometryEquiv.withLpProdCongr 2 L
    (LinearIsometryEquiv.refl ℝ ℝ))).trans verticalProduct.symm

theorem verticalFrame_coordinates (L : Plane ≃ₗᵢ[ℝ] Plane) (z : Space) :
    verticalProduct (verticalFrame L z) =
      (LinearIsometryEquiv.withLpProdCongr 2 L
        (LinearIsometryEquiv.refl ℝ ℝ)) (verticalProduct z) := by
  simp only [verticalFrame, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem horizontal_verticalFrame (L : Plane ≃ₗᵢ[ℝ] Plane) (z : Space) :
    horizontal (verticalFrame L z) = L (horizontal z) :=
  congrArg (fun p : WithLp 2 (Plane × ℝ) => p.ofLp.1) (verticalFrame_coordinates L z)

@[simp] theorem height_verticalFrame (L : Plane ≃ₗᵢ[ℝ] Plane) (z : Space) :
    verticalFrame L z 2 = z 2 :=
  congrArg (fun p : WithLp 2 (Plane × ℝ) => p.ofLp.2) (verticalFrame_coordinates L z)

end Unfoldings.Cap
