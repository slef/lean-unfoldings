module

public import Unfoldings.Geometry.NorthFrame
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! The norm of the slope in a centered gnomonic chart is the tangent of its angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry

def centeredSlope (center x : Space) : Plane :=
  (northFrame center x 2)⁻¹ • horizontal (northFrame center x)

theorem centeredSlope_norm {center x : Space} (hc : ‖center‖ = 1) (hx : ‖x‖ = 1)
    (near : angle center x < Real.pi / 2) :
    ‖centeredSlope center x‖ = Real.tan (angle center x) := by
  let y := northFrame center x
  have height : y 2 = Real.cos (angle center x) :=
    (northFrame_height center hc x).trans (inner_eq_cos_angle_of_norm_eq_one hc hx)
  have ypos : 0 < Real.cos (angle center x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [angle_nonneg center x, Real.pi_pos], near⟩
  have sq := horizontal_norm_sq y
  have yu : ‖y‖ = 1 := ((northFrame center).norm_map x).trans hx
  rw [yu, height] at sq
  have sine : 0 ≤ Real.sin (angle center x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _) (angle_le_pi _ _)
  have hnorm : ‖horizontal y‖ = Real.sin (angle center x) := by
    apply (sq_eq_sq₀ (norm_nonneg _) sine).mp
    linarith only [sq, Real.sin_sq_add_cos_sq (angle center x)]
  change ‖(y 2)⁻¹ • horizontal y‖ = _
  rw [norm_smul, height, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ypos), hnorm,
    Real.tan_eq_sin_div_cos, div_eq_inv_mul]

theorem centeredSlope_height_pos {center x : Space} (hc : ‖center‖ = 1) (hx : ‖x‖ = 1)
    (near : angle center x < Real.pi / 2) : 0 < northFrame center x 2 := by
  rw [northFrame_height center hc, inner_eq_cos_angle_of_norm_eq_one hc hx]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [angle_nonneg center x, Real.pi_pos], near⟩

theorem gnomonicNormal_centeredSlope {center x : Space} (hc : ‖center‖ = 1) (hx : ‖x‖ = 1)
    (near : angle center x < Real.pi / 2) :
    gnomonicNormal (centeredSlope center x) = northFrame center x :=
  gnomonicNormal_slope _ (((northFrame center).norm_map x).trans hx)
    (centeredSlope_height_pos hc hx near)

theorem gnomonicNormal_zero : gnomonicNormal 0 = northLift 0 :=
  NormedSpace.normalize_eq_self_of_norm_eq_one northLift_zero_unit

theorem northLift_cornerCombination (p q : Plane) (a b : ℝ) :
    northLift (a • p + b • q) =
      (1 - (a + b)) • northLift 0 + a • northLift p + b • northLift q := by
  ext j
  fin_cases j
  · change a * p 0 + b * q 0 = (1 - (a + b)) * 0 + a * p 0 + b * q 0
    ring
  · change a * p 1 + b * q 1 = (1 - (a + b)) * 0 + a * p 1 + b * q 1
    ring
  · change (1 : ℝ) = (1 - (a + b)) * 1 + a * 1 + b * 1
    ring

/-- Site comparisons are unchanged by moving an upward unit point to height one. -/
theorem inner_northLift_centeredSlope {center x : Space} (hc : ‖center‖ = 1) (hx : ‖x‖ = 1)
    (near : angle center x < Real.pi / 2) (z : Space) :
    inner ℝ (northLift (centeredSlope center x)) (northFrame center z) =
      (northFrame center x 2)⁻¹ * inner ℝ x z := by
  rw [centeredSlope, northLift_slope _ (centeredSlope_height_pos hc hx near),
    real_inner_smul_left, LinearIsometryEquiv.inner_map_map]

end Unfoldings.Cap
