module

public import Unfoldings.FewestNets.TightLatitudeSelectorCharge
public import Unfoldings.FewestNets.TightLatitudeCountScalars
public import Unfoldings.FewestNets.TightLatitudeAreaCount
public import Unfoldings.FewestNets.RevisedLatitudeAllowances

/-! Sum the refined analytic selector charges for margins up to 0.42 radians. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real
open AcuteLatitudeGrid (tightAnalyticPrefactorScale tightAnalyticPrefactorScale_pos)

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small in
theorem tightApexCoefficient_excess_le :
    (∑ i : AnnularTriangle a, (tightApexCoefficient i - 1.189)) ≤
      (0.03 * 29 + 1.545 * 6.3) / a := by
  refine (Finset.sum_le_sum (fun i _ => ?_)).trans
    ((annularApexCoefficient_excess_lt positive small).le.trans_eq (by ring))
  unfold tightApexCoefficient annularApexCoefficient apexCountCoefficient
  split_ifs <;> norm_num

include positive small in
set_option maxHeartbeats 1000000 in
theorem analyticAnnularCharge_sum_lt (analytic : a ≤ 0.42) :
    2 + 4.90 / a ^ 2 + (tightAnalyticPrefactorScale a / a) * (∑ i : AnnularTriangle a, analyticAnnularCharge i) <
      246.3 / a ^ 4 := by
  let d := rowStep a
  let b := spacing a
  let r := radius a
  let m : ℝ := triangleCount a
  let E := ∑ i : AnnularTriangle a, (tightApexCoefficient i - 1.189)
  let e : ℝ := 0.03 * 29 + 1.545 * 6.3
  let c : ℝ := 1.189 - 0.089 * a
  have cp : 0 ≤ c := by dsimp only [c]; linarith only [analytic]
  have Ep : 0 ≤ E := Finset.sum_nonneg (fun i _ => by unfold tightApexCoefficient; split_ifs <;> norm_num)
  have bp : 0 < b := spacing_pos positive
  have rp : 0 < r := radius_pos positive
  have step := (rowStep_bounds positive small).2
  have scale : r / b = 1 / (0.51 * a) := by
    dsimp only [b]
    rw [spacing]
    change r / (0.51 * a * r) = _
    field_simp [positive.ne', rp.ne']
  have small_d : d / b ≤ 1 / (0.51 * a) :=
    (div_le_div_of_nonneg_right step bp.le).trans_eq scale
  have first : m * (d / b) ≤ ((99.71 - 3.22 * a) / a ^ 2) * (1 / (0.51 * a)) := by
    have h := triangleCount_times_relative_step_lt positive small
    change m * d / r < _ at h
    calc
      _ = (m * d / r) * (r / b) := by field_simp [rp.ne', bp.ne']
      _ ≤ _ := by rw [scale]; exact mul_le_mul_of_nonneg_right h.le (by positivity)
  have second : E * (d / b) ≤ (e / a) * (1 / (0.51 * a)) :=
    (mul_le_mul_of_nonneg_left small_d Ep).trans
      (mul_le_mul_of_nonneg_right (tightApexCoefficient_excess_le positive small) (by positivity))
  have third : m ≤ tightAnalyticTriangleCountCoefficient a / a ^ 2 := by
    apply (le_div_iff₀ (pow_pos positive 2)).mpr
    by_cases first : a ≤ 0.38
    · rw [tightAnalyticTriangleCountCoefficient, ite_eq_left first]
      exact (triangleCount_mul_sq_lt a positive small).le
    · rw [tightAnalyticTriangleCountCoefficient, ite_eq_right first]
      exact (triangleCount_mul_sq_lt_seven_bands a (lt_of_not_ge first).le analytic).le
  have exact_coeff : (∑ i : AnnularTriangle a, (tightApexCoefficient i - 0.089 * a)) = m * c + E := by
    unfold E
    simp_rw [show ∀ i : AnnularTriangle a, tightApexCoefficient i - 0.089 * a =
      c + (tightApexCoefficient i - 1.189) from fun i => by dsimp [c]; ring]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, LatitudeRings.card_annularTriangle]
    rfl
  have allowance : (∑ i : AnnularTriangle a, analyticAnnularCharge i) =
      0.674 * (c * (m * (d / b)) + E * (d / b) + m * (2 + 0.2212 * a ^ 2)) := by
    unfold analyticAnnularCharge
    simp_rw [add_assoc]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, exact_coeff]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, LatitudeRings.card_annularTriangle]
    change 0.674 * ((m * c + E) * (d / b) + m * (2 + 0.2212 * a ^ 2)) = _
    ring
  let w := ((99.71 - 3.22 * a) / a ^ 2) * (1 / (0.51 * a))
  have upper : (∑ i : AnnularTriangle a, analyticAnnularCharge i) ≤
      0.674 * (c * w + (e / a) * (1 / (0.51 * a)) + (tightAnalyticTriangleCountCoefficient a / a ^ 2) * (2 + 0.2212 * a ^ 2)) := by
    rw [allowance]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left first cp) second)
        (mul_le_mul_of_nonneg_right third (by positivity))) (by norm_num)
  apply (lt_div_iff₀ (pow_pos positive 4)).mpr
  refine (mul_le_mul_of_nonneg_right
    (add_le_add (le_refl (2 + 4.90 / a ^ 2)) (mul_le_mul_of_nonneg_left upper (div_nonneg (tightAnalyticPrefactorScale_pos a).le positive.le)))
    (pow_nonneg positive.le 4)).trans_lt ?_
  convert tightLatitude_small_coefficient_lt positive analytic using 1
  unfold tightAnalyticCountPolynomial
  dsimp only [w, c, e]
  field_simp [positive.ne']
  <;> ring

end Unfoldings.FewestNets.RevisedLatitudeGrid
