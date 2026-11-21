module

public import Unfoldings.FewestNets.DevelopmentScalarRecord
public import Unfoldings.Roof.SharpAngleProjection
public import Unfoldings.Cap.SharpSectionFans

/-! From each checked scalar row to the actual projected-angle and routing margins. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.DevelopmentScalarRecord

open Real

def visualAngle (r : DevelopmentScalarRecord) : ℝ := (r.visualAngleDegrees : ℝ) * π / 180

def projectedAngle (r : DevelopmentScalarRecord) (target : ℚ) : ℝ :=
  (target : ℝ) * π / 180 + 2 * arcsin (tan ((r.tilt : ℝ) / 2) ^ 2)

theorem visualAngle_pos (r : DevelopmentScalarRecord) {target : ℚ} (nonnegative : 0 ≤ target)
    (valid : r.ValidFor target) : 0 < r.visualAngle := by
  have angle_positive : 0 < r.visualAngleDegrees := nonnegative.trans_lt valid.2.2.1
  unfold visualAngle
  exact div_pos (mul_pos (by exact_mod_cast angle_positive) pi_pos) (by norm_num)

theorem visualAngle_lt_pi_div_two (r : DevelopmentScalarRecord) {target : ℚ}
    (valid : r.ValidFor target) : r.visualAngle < π / 2 := by
  have angle_small : (r.visualAngleDegrees : ℝ) < 90 := by exact_mod_cast valid.2.2.2.1
  unfold visualAngle
  have h := mul_lt_mul_of_pos_right angle_small pi_pos
  linarith only [h]

theorem cotangent_lt_of_gap (r : DevelopmentScalarRecord) (gap : 0 < r.cotangentGap) :
    (r.cotangent : ℝ) * sin r.visualAngle < cos r.visualAngle := by
  change 0 < sin ((90 - (r.visualAngleDegrees : ℝ)) * π / 180) -
    (r.cotangent : ℝ) * cos ((90 - (r.visualAngleDegrees : ℝ)) * π / 180) at gap
  rw [show (90 - (r.visualAngleDegrees : ℝ)) * π / 180 = π / 2 - r.visualAngle by
    unfold visualAngle
    ring, sin_pi_div_two_sub, cos_pi_div_two_sub] at gap
  exact sub_pos.mp gap

theorem projectedAngle_nonneg (r : DevelopmentScalarRecord) {target : ℚ}
    (nonnegative : 0 ≤ target) : 0 ≤ r.projectedAngle target := by
  have target_pos : (0 : ℝ) ≤ target := by exact_mod_cast nonnegative
  have h := arcsin_nonneg.mpr (sq_nonneg (tan ((r.tilt : ℝ) / 2)))
  unfold projectedAngle
  positivity

theorem interiorMarginGap_eq (r : DevelopmentScalarRecord) (target : ℚ) :
    r.interiorMarginGap target =
      cos ((π - r.visualAngle + r.projectedAngle target) / 2) - r.margin := by
  unfold interiorMarginGap visualAngle projectedAngle
  rw [show ((r.visualAngleDegrees : ℝ) - (target : ℝ)) * π / 360 -
      arcsin (tan ((r.tilt : ℝ) / 2) ^ 2) =
      π / 2 - (π - (r.visualAngleDegrees : ℝ) * π / 180 +
        ((target : ℝ) * π / 180 + 2 * arcsin (tan ((r.tilt : ℝ) / 2) ^ 2))) / 2 by ring,
    sin_pi_div_two_sub]

theorem projectedAngle_lt_visualAngle_of_gap (r : DevelopmentScalarRecord) {target : ℚ}
    (nonnegative : 0 ≤ target) (valid : r.ValidFor target)
    (gap : 0 < r.interiorMarginGap target) : r.projectedAngle target < r.visualAngle := by
  let mid := (r.visualAngle - r.projectedAngle target) / 2
  have adjust : mid = ((r.visualAngleDegrees : ℝ) - (target : ℝ)) * π / 360 -
      arcsin (tan ((r.tilt : ℝ) / 2) ^ 2) := by
    dsimp [mid, visualAngle, projectedAngle]
    ring
  have margin := r.margin_nonneg valid
  have sin_positive : 0 < sin mid := by
    rw [adjust]
    have h := sub_pos.mp gap
    exact margin.trans_lt h
  have half :
      arcsin (tan ((r.tilt : ℝ) / 2) ^ 2) < π / 2 :=
    arcsin_lt_pi_div_two.mpr (r.tan_half_sq_lt_one valid)
  have htarget : (target : ℝ) ≤ r.visualAngleDegrees := by exact_mod_cast valid.2.2.1.le
  have spread := div_nonneg (mul_nonneg (sub_nonneg.mpr htarget) pi_pos.le)
    (by norm_num : (0 : ℝ) ≤ 360)
  have lower : -π ≤ mid := by rw [adjust]; linarith only [half, spread, pi_pos]
  by_contra! large
  have negative : mid ≤ 0 := by dsimp [mid]; linarith
  exact (not_lt_of_ge (sin_nonpos_of_nonpos_of_neg_pi_le negative lower)) sin_positive

universe u v

/-- A verified cell row provides the projected input angle bound whenever
the selected physical face has the row's certified normal height. -/
theorem projected_cornerAngle_le_of_normalHeight (r : DevelopmentScalarRecord) {target : ℚ}
    (valid : r.ValidFor target) {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C) (f : Face)
    (height : cos r.tilt ≤ K.normal f 2) (i : Fin 3)
    (angles : (C.triangle f).cornerAngle i ≤ (target : ℝ) * π / 180) :
    (K.projectedTriangle f).cornerAngle i ≤ r.projectedAngle target := by
  have phi_pos : (0 : ℝ) < r.tilt := by exact_mod_cast valid.1
  have phi_small : (r.tilt : ℝ) < 1 := by exact_mod_cast valid.2.1
  have pos : 0 < cos r.tilt :=
    cos_pos_of_mem_Ioo ⟨by linarith only [phi_pos, pi_pos], by linarith only [phi_small, pi_gt_three]⟩
  have h := K.projected_cornerAngle_le_of_normal_height pos f height i angles
  rwa [ConvexCap.cos_ratio_eq_tan_half_sq pos] at h

end Unfoldings.FewestNets.DevelopmentScalarRecord
