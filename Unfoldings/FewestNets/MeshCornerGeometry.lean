module

public import Unfoldings.FewestNets.MeshBisectors
public import Unfoldings.Geometry.MinorArcArclength

/-! Gnomonic corner rays give the true incident angles of a spherical network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

/-- An outward gnomonic corner ray is the genuine minor-arc tangent scaled
by the tangent of its arc length. -/
theorem meshGnomonic_eq_smul_minorArcTangent {u v : Space}
    (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
    (positive : 0 < angle u v) (short : angle u v < π / 2) :
    meshGnomonic u v = (sin (angle u v) / cos (angle u v)) • minorArcTangent u v := by
  have cos_pos := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], short⟩
  have sin_pos := sin_pos_of_pos_of_lt_pi positive (short.trans (by linarith [pi_pos]))
  calc
    _ = (cos (angle u v))⁻¹ • (v - cos (angle u v) • u) := by
      rw [meshGnomonic, inner_eq_cos_angle_of_norm_eq_one uu vu, smul_sub,
        smul_smul, inv_mul_cancel₀ cos_pos.ne', one_smul]
    _ = _ := by
      rw [minorArcTangent, smul_smul, div_eq_inv_mul, mul_assoc, mul_inv_cancel₀ sin_pos.ne',
        mul_one]

/-- The angle checked at a gnomonic corner is its spherical incident angle. -/
theorem angle_meshGnomonic_eq_incident {u v w : Space}
    (uu : ‖u‖ = 1) (vu : ‖v‖ = 1) (wu : ‖w‖ = 1)
    (pv : 0 < angle u v) (pw : 0 < angle u w)
    (sv : angle u v < π / 2) (sw : angle u w < π / 2) :
    angle (meshGnomonic u v) (meshGnomonic u w) =
      angle (minorArcTangent u v) (minorArcTangent u w) := by
  have scale {x : Space} (positive : 0 < angle u x) (short : angle u x < π / 2) :
      0 < sin (angle u x) / cos (angle u x) :=
    div_pos (sin_pos_of_pos_of_lt_pi positive (short.trans (by linarith [pi_pos])))
      (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], short⟩)
  rw [meshGnomonic_eq_smul_minorArcTangent uu vu pv sv,
    meshGnomonic_eq_smul_minorArcTangent uu wu pw sw,
    angle_smul_left_of_pos _ _ (scale pv sv), angle_smul_right_of_pos _ _ (scale pw sw)]

end Unfoldings.FewestNets
