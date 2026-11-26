module

public import Unfoldings.FewestNets.TightLatitudeApexCharge

/-! Use the same validated selector metric in the analytic range and in the interval range. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real SphericalSelectorBoundary

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

def analyticAnnularCharge (i : AnnularTriangle a) : ℝ :=
  0.674 * ((tightApexCoefficient i - 0.089 * a) * (rowStep a / spacing a) + 2 + 0.2212 * a ^ 2)

/-- The literal selector metric evaluates to the two raw charge alternatives. -/
theorem tightAnnularSelectorMetric_crossingBudget_eq (i : AnnularTriangle a) :
    (tightAnnularSelectorMetric positive small i).crossingBudget =
      max ((∑ j : Fin 3, (2 * annularLongestSide i / (π * sin (annularLongestSide i))) /
        sin (min (annularCornerAngle i j) (π / 2)))) (annularPerimeter i / (π * 0.115)) := by
  let l := annularLongestSide i
  change max ((∑ p : Fin 3 × Bool, l / (sin l *
      sin (min (annularCornerAngle i (if p.2 then p.1 + 1 else p.1)) (π / 2)))) / π)
    (annularPerimeter i / (π * 0.115)) = _
  have s := sum_endpointFactors_of_permutation l (annularCornerAngle i) (finRotate 3)
  rw [show (∑ p : Fin 3 × Bool, l / (sin l *
      sin (min (annularCornerAngle i (if p.2 then p.1 + 1 else p.1)) (π / 2)))) / π =
      _ by simpa only [finRotate_apply] using s]

theorem tightAnnularSelectorMetric_crossingBudget_le (analytic : a ≤ 0.40) (i : AnnularTriangle a) :
    (tightAnnularSelectorMetric positive small i).crossingBudget ≤ analyticAnnularCharge i := by
  rw [tightAnnularSelectorMetric_crossingBudget_eq, analyticAnnularCharge]
  apply max_le
  · let l := annularLongestSide i
    let k j := sin (min (annularCornerAngle i j) (π / 2))
    have k_nonneg (j : Fin 3) : 0 ≤ k j :=
      sin_nonneg_of_nonneg_of_le_pi (le_min (annular_corner_pos positive small i j).le pi_div_two_pos.le)
        ((min_le_right _ _).trans (by linarith only [pi_pos]))
    have factor := (annular_longestSide_factor positive small i).2
    have costs : (∑ j : Fin 3, 1 / k j) ≤
        (tightApexCoefficient i - 0.089 * a) * (rowStep a / spacing a) + 2 + 0.2212 * a ^ 2 := by
      rw [Fin.sum_univ_three]
      have apex := annular_apex_reciprocal_le_of_analytic positive small analytic i
      have base := annular_joint_base_reciprocal_le positive small i
      change 1 / k 2 ≤ _ at apex
      change 1 / k 0 + 1 / k 1 ≤ _ at base
      linarith only [apex, base]
    calc
      _ ≤ ∑ j : Fin 3, (0.674 : ℝ) / k j := Finset.sum_le_sum fun j _ =>
        div_le_div_of_nonneg_right factor (k_nonneg j)
      _ = 0.674 * (∑ j : Fin 3, 1 / k j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left costs (by norm_num)
  · have perim := (annular_metric_bounds positive small i).2
    have max_perim : annularPerimeter i / (π * 0.115) ≤ 3.68 := by
      apply (div_le_iff₀ (by positivity)).mpr
      norm_num1 at perim ⊢
      linarith only [perim, pi_gt_d4, radius_lt small]
    have m : 4 ≤ rowStep a / spacing a := by
      apply (le_div_iff₀ (spacing_pos positive)).mpr
      linarith only [spacing_le_of_analytic analytic, radius_pos positive, (rowStep_bounds positive small).1]
    have coefficient : 1.14 ≤ tightApexCoefficient i - 0.089 * a := by
      unfold tightApexCoefficient
      split_ifs <;> linarith only [analytic]
    have h := mul_le_mul coefficient m (by norm_num : (0 : ℝ) ≤ 4)
      ((by norm_num : (0 : ℝ) ≤ 1.14).trans coefficient)
    exact max_perim.trans (by nlinarith only [h, sq_nonneg a])

/-- The interval branch bounds the same actual selector metric. -/
theorem tightAnnularSelectorMetric_crossingBudget_le_algebraic (i : AnnularTriangle a) :
    (tightAnnularSelectorMetric positive small i).crossingBudget ≤ annularAlgebraicCharge i := by
  rw [tightAnnularSelectorMetric_crossingBudget_eq]
  exact annular_raw_charge_le_algebraic positive small i

end Unfoldings.FewestNets.RevisedLatitudeGrid
