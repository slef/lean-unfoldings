module

public import Unfoldings.Geometry.AcuteWedgeFrame

/-! The quadrant margin is exactly half the angular slack of an acute wedge. -/

@[expose] public section

namespace Unfoldings.AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem angle_eq_pi_div_two_sub_two_margin :
    InnerProductGeometry.angle u v = Real.pi / 2 - 2 * B.margin := by
  have mapped := B.place.toLinearIsometry.angle_map u v
  change InnerProductGeometry.angle (B.place u) (B.place v) =
    InnerProductGeometry.angle u v at mapped
  rw [B.first, B.last, ← Complex.real_smul, ← Complex.real_smul,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (norm_pos_iff.mpr B.first_ne),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (norm_pos_iff.mpr B.last_ne)] at mapped
  have angle := angle_polarRay B.margin (Real.pi / 2 - B.margin)
    (by linarith [B.small]) (by linarith [B.positive, Real.pi_pos])
  linarith

theorem margin_lt_pi_div_four (genuine : 0 < orient 0 u v) : B.margin < Real.pi / 4 := by
  by_contra large
  have equal : B.margin = Real.pi / 4 := le_antisymm B.small (not_lt.mp large)
  have angle_zero : InnerProductGeometry.angle u v = 0 := by
    rw [B.angle_eq_pi_div_two_sub_two_margin, equal]
    ring
  obtain ⟨_, a, _, scaled⟩ := InnerProductGeometry.angle_eq_zero_iff.mp angle_zero
  have vanish : orient 0 u (a • u) = 0 := by
    simp only [orient, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply, sub_zero]
    ring
  rw [scaled, vanish] at genuine
  exact (lt_irrefl _ genuine)

end Unfoldings.AcuteWedgeFrame
