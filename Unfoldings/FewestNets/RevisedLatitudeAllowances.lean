module

public import Unfoldings.FewestNets.RevisedLatitudeSurcharges
public import Unfoldings.FewestNets.RevisedLatitudeCountArithmetic
public import Unfoldings.FewestNets.RevisedLatitudeSelectors

/-! Sum the revised local allowances using the actual number of each triangle type. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

variable {a : ℝ}

/-- Excess above the area contribution in the single-selector count. -/
def selectorCountAllowance (key : Selector a) : ℝ :=
  key.elim (fun _ => 2.45 / a ^ 2) (fun i =>
    (1.215 * 0.675) / a *
      ((annularApexCoefficient i - 0.073 * a) * (rowStep a / spacing a) + 2 / 0.932))

theorem selectorCountAllowance_sum_lt (positive : 0 < a) (small : a ≤ π / 6) :
    2 + (∑ key : Selector a, selectorCountAllowance key) < 296 / a ^ 4 := by
  let d := rowStep a
  let b := spacing a
  let r := radius a
  let m : ℝ := triangleCount a
  let E := ∑ i : AnnularTriangle a, (annularApexCoefficient i - 1.225)
  let e : ℝ := 1.545 * 6.3 + 0.03 * 29
  let c : ℝ := 1.225 - 0.073 * a
  have cp : 0 < c := by dsimp only [c]; linarith only [small, pi_lt_d6]
  have Ep : 0 ≤ E := Finset.sum_nonneg (fun i _ => by
    unfold annularApexCoefficient apexCountCoefficient
    split_ifs <;> norm_num)
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
      _ ≤ _ := by
        rw [scale]
        exact mul_le_mul_of_nonneg_right h.le (by positivity)
  have second : E * (d / b) ≤ (e / a) * (1 / (0.51 * a)) :=
    (mul_le_mul_of_nonneg_left small_d Ep).trans
      (mul_le_mul_of_nonneg_right (annularApexCoefficient_excess_lt positive small).le (by positivity))
  have third : m ≤ 55.9 / a ^ 3 := (le_div_iff₀ (pow_pos positive 3)).mpr
    (triangleCount_mul_cube_lt positive small).le
  have exact_coeff : (∑ i : AnnularTriangle a, (annularApexCoefficient i - 0.073 * a)) =
      m * c + E := by
    unfold E
    simp_rw [show ∀ i : AnnularTriangle a, annularApexCoefficient i - 0.073 * a =
      c + (annularApexCoefficient i - 1.225) from fun i => by dsimp [c]; ring]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, LatitudeRings.card_annularTriangle]
    rfl
  have allowance : (∑ key : Selector a, selectorCountAllowance key) =
      4.90 / a ^ 2 + (1.215 * 0.675) / a *
        ((m * c + E) * (d / b) + m * (2 / 0.932)) := by
    rw [Fintype.sum_sum_type]
    simp only [selectorCountAllowance, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, exact_coeff]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      LatitudeRings.card_annularTriangle]
    change (2 : ℝ) * (2.45 / a ^ 2) + (1.215 * 0.675) / a *
      ((m * c + E) * (d / b) + m * (2 / 0.932)) = _
    ring
  rw [allowance]
  refine lt_of_le_of_lt ?_ (acute_latitude_revised_count_lt positive small)
  calc
    _ = 2 + 4.90 / a ^ 2 + (1.215 * 0.675) / a *
      (c * (m * (d / b)) + E * (d / b) + m * (2 / 0.932)) := by ring
    _ ≤ 2 + 4.90 / a ^ 2 + (1.215 * 0.675) / a *
        (c * (((99.71 - 3.22 * a) / a ^ 2) * (1 / (0.51 * a))) +
          (e / a) * (1 / (0.51 * a)) + (55.9 / a ^ 3) * (2 / 0.932)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left first cp.le) second)
          (mul_le_mul_of_nonneg_right third (show (0 : ℝ) ≤ 2 / 0.932 by norm_num)))
          (show (0 : ℝ) ≤ (1.215 * 0.675) / a by positivity))
    _ = _ := by
      unfold c e
      field_simp [positive.ne']
      <;> ring

end Unfoldings.FewestNets.RevisedLatitudeGrid
