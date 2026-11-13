module

public import Unfoldings.Cap.VerticalProduct

/-! Upward unit normals of affine height graphs. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The upward unit normal to a height graph with negative gradient `slope`. -/
def graphNormal (slope : Plane) : Space :=
  (Real.sqrt (1 + ‖slope‖ ^ 2))⁻¹ • Cap.horizontalAtHeight slope 1

theorem graphNormal_unit (slope : Plane) : ‖graphNormal slope‖ = 1 := by
  have positive : 0 < Real.sqrt (1 + ‖slope‖ ^ 2) := by positivity
  have normed : ‖Cap.horizontalAtHeight slope 1‖ = Real.sqrt (1 + ‖slope‖ ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) positive.le).mp
    rw [Real.sq_sqrt (by positivity)]
    have squared := Cap.horizontal_norm_sq (Cap.horizontalAtHeight slope 1)
    rw [Cap.horizontal_horizontalAtHeight, Cap.height_horizontalAtHeight] at squared
    linarith
  rw [graphNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive),
    normed, inv_mul_cancel₀ positive.ne']

@[simp] theorem graphNormal_vertical (slope : Plane) :
    graphNormal slope 2 = (Real.sqrt (1 + ‖slope‖ ^ 2))⁻¹ := by
  change (Real.sqrt (1 + ‖slope‖ ^ 2))⁻¹ * 1 = _
  exact mul_one _

theorem graphNormal_upward (slope : Plane) : 0 < graphNormal slope 2 := by
  rw [graphNormal_vertical]
  positivity

theorem graphNormal_inner (slope : Plane) (z : Space) :
    inner ℝ (graphNormal slope) z =
      (Real.sqrt (1 + ‖slope‖ ^ 2))⁻¹ * (inner ℝ slope (Cap.horizontal z) + z 2) := by
  rw [graphNormal, real_inner_smul_left, Cap.horizontal_inner,
    Cap.horizontal_horizontalAtHeight, Cap.height_horizontalAtHeight, one_mul]

/-- A squared slope bound gives the corresponding lower vertical normal bound. -/
theorem graphNormal_vertical_ge {slope : Plane} {c : ℝ} (nonnegative : 0 ≤ c)
    (bound : (1 + ‖slope‖ ^ 2) * c ^ 2 ≤ 1) : c ≤ graphNormal slope 2 := by
  let d := Real.sqrt (1 + ‖slope‖ ^ 2)
  have positive : 0 < d := by dsimp [d]; positivity
  have squared : d ^ 2 = 1 + ‖slope‖ ^ 2 := Real.sq_sqrt (by positivity)
  have product : c * d ≤ 1 := by
    apply (sq_le_sq₀ (mul_nonneg nonnegative positive.le) zero_le_one).mp
    nlinarith [bound]
  rw [graphNormal_vertical, inv_eq_one_div, le_div_iff₀ positive]
  exact product

end Unfoldings
