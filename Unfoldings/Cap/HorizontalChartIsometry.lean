module

public import Unfoldings.Cap.VerticalProduct
public import Unfoldings.Cap.Gnomonic

/-! Reorienting the horizontal chart preserves the vertical coordinate and the gnomonic map. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

/-- Extend a planar linear isometry to space, fixing heights. -/
def horizontalChartIsometry (E : Plane ≃ₗᵢ[ℝ] Plane) : Space ≃ₗᵢ[ℝ] Space :=
  (verticalProduct.trans (LinearIsometryEquiv.withLpProdCongr 2 E
    (LinearIsometryEquiv.refl ℝ ℝ))).trans verticalProduct.symm

theorem horizontalChartIsometry_apply (E : Plane ≃ₗᵢ[ℝ] Plane) (p : Space) :
    horizontalChartIsometry E p = horizontalAtHeight (E (horizontal p)) (p 2) := rfl

@[simp] theorem horizontalChartIsometry_height (E : Plane ≃ₗᵢ[ℝ] Plane) (p : Space) :
    horizontalChartIsometry E p 2 = p 2 := rfl

@[simp] theorem horizontal_horizontalChartIsometry (E : Plane ≃ₗᵢ[ℝ] Plane) (p : Space) :
    horizontal (horizontalChartIsometry E p) = E (horizontal p) :=
  horizontal_horizontalAtHeight _ _

/-- Gnomonic projection commutes with arbitrary planar rotations or reflections. -/
@[simp] theorem horizontalChartIsometry_gnomonicNormal (E : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    horizontalChartIsometry E (gnomonicNormal p) = gnomonicNormal (E p) := by
  have lift : horizontalChartIsometry E (northLift p) = northLift (E p) := by
    rw [horizontalChartIsometry_apply, northLift_horizontal, northLift_height]
    rfl
  unfold gnomonicNormal NormedSpace.normalize
  rw [map_smul, ← lift, (horizontalChartIsometry E).norm_map]

end Unfoldings.Cap
