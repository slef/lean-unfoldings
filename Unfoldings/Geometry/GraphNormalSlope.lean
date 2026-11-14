module

public import Unfoldings.Geometry.SpatialPlaneSlopes

/-! Gnomonic normal slopes recover the exact parameters of constructed spatial graph planes. -/

@[expose] public section

namespace Unfoldings

theorem graphNormal_normalSlope (slope : Plane) :
    (graphNormal slope 2)⁻¹ • Cap.horizontal (graphNormal slope) = slope := by
  rw [graphNormal_vertical, inv_inv, graphNormal, map_smul, Cap.horizontal_horizontalAtHeight,
    smul_smul, mul_inv_cancel₀ (by positivity : Real.sqrt (1 + ‖slope‖ ^ 2) ≠ 0), one_smul]

theorem SpatialPlane.ofGraph_normalSlope (c : ℝ) (slope : Plane) :
    (SpatialPlane.ofGraph c slope).normalSlope = slope := graphNormal_normalSlope slope

end Unfoldings
