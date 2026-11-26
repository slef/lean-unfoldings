module

public import Unfoldings.FewestNets.RevisedLatitudeChartBudget
public import Unfoldings.Geometry.ArctanScalars
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Sharp scalar estimates for the annular corner charges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

private theorem cos_le_fourth (x : ℝ) (h : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t
  have derive (t : ℝ) : HasDerivAt f (-t + t ^ 3 / 6 + sin t) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
      ((hasDerivAt_pow 4 t).div_const 24)).sub (hasDerivAt_cos t) using 1 <;> ring
  have mono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun t _ => (derive t).continuousAt.continuousWithinAt)
      (fun t _ => (derive t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(derive t).deriv]
    have tp : 0 ≤ t := interior_subset ht
    linarith only [sin_ge_sub_cube tp]
  have value := mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  have zero : f 0 = 0 := by simp [f]
  rw [zero] at value
  exact sub_nonneg.mp value

private theorem sin_le_fifth (x : ℝ) (h : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - sin t
  have derive (t : ℝ) : HasDerivAt f (1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t) t := by
    convert (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
      ((hasDerivAt_pow 5 t).div_const 120)).sub (hasDerivAt_sin t) using 1
    · funext u
      simp only [f, Pi.sub_apply, Pi.add_apply, id_eq]
    · ring
  have mono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun t _ => (derive t).continuousAt.continuousWithinAt)
      (fun t _ => (derive t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(derive t).deriv]
    exact sub_nonneg.mpr (cos_le_fourth t (interior_subset ht))
  have value := mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  have zero : f 0 = 0 := by simp [f]
  rw [zero] at value
  exact sub_nonneg.mp value

theorem sine_rowStep_le {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    sin (rowStep a) ≤ rowStep a * (1 - 0.061 * a) := by
  let d := rowStep a
  have dp : 0 < d := rowStep_pos positive small
  have bounds := rowStep_bounds positive small
  have ds := pow_le_pow_left₀ dp.le (bounds.2.trans (radius_lt small).le) 2
  have lower := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.852) (radius_pos positive).le) bounds.1.le 2
  have rsq : radius a ^ 2 = 0.72 ^ 2 * a := by rw [radius, mul_pow, sq_sqrt positive.le]
  have le_low : 0.061 * a ≤ 0.163 * d ^ 2 := by
    rw [mul_pow, rsq] at lower
    nlinarith only [lower, positive]
  have hi : d ^ 5 / 120 ≤ (1 / 6 - 0.163) * d ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right ds (pow_nonneg dp.le 3), pow_nonneg dp.le 3]
  have sine := sin_le_fifth d dp.le
  change sin d ≤ d * (1 - 0.061 * a)
  nlinarith only [sine, hi, mul_le_mul_of_nonneg_left le_low dp.le]

/-- The three choices distinguish the refined base from the adjacent ordinary base. -/
def apexCountCoefficient (polarStrip polarBase : Bool) : ℝ :=
  if polarBase then 2.77 else if polarStrip then 1.255 else 1.225

theorem apexCountCoefficient_pos {a : ℝ} (small : a ≤ π / 6) (strip base : Bool) :
    0 < apexCountCoefficient strip base - 0.073 * a := by
  cases strip <;> cases base <;> norm_num [apexCountCoefficient] <;> linarith only [small, pi_lt_d6]

/-- The cosine-weighted chart height retains the exact meridional leading term. -/
theorem apex_height_mul_cos_le {a H q : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (polarStrip : Bool)
    (spacing_cap : spacing a ≤ q * radius a)
    (height : H ≤ 2 * sin (rowStep a / 2) / 0.9612 +
      ordinateErrorFactor polarStrip * spacing a ^ 2 / radius a) :
    H * cos (rowStep a / 2) ≤ rowStep a *
      ((1 - 0.061 * a) / 0.9612 + ordinateErrorFactor polarStrip * q ^ 2 / 0.852) := by
  let z : ℝ := 0.9612
  let b := spacing a
  let d := rowStep a
  let r := radius a
  let E := ordinateErrorFactor polarStrip
  let c := cos (d / 2)
  have dp : 0 < d := rowStep_pos positive small
  have bp : 0 < b := spacing_pos positive
  have rp : 0 < r := radius_pos positive
  have ep : 0 ≤ E := ordinateErrorFactor_nonneg _
  have cp : 0 < c := cos_pos_of_mem_Ioo
    ⟨by linarith only [dp, pi_pos],
      by linarith only [(rowStep_bounds positive small).2, radius_lt small, pi_gt_d2]⟩
  have en : 0 ≤ E * b ^ 2 / r := by positivity
  let S := (1 - 0.061 * a) / z + E * q ^ 2 / 0.852
  have S_err : E * b ^ 2 / r ≤ d * (E * q ^ 2 / 0.852) := by
    have sq := pow_le_pow_left₀ bp.le (spacing_cap) 2
    have h := (div_le_iff₀ rp).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left sq ep] :
        E * b ^ 2 ≤ (E * q ^ 2 * r) * r)
    have sc := mul_le_mul_of_nonneg_right (rowStep_bounds positive small).1.le
      (div_nonneg (mul_nonneg ep (sq_nonneg _)) (by norm_num) :
        0 ≤ E * q ^ 2 / 0.852)
    change 0.852 * r * (E * q ^ 2 / 0.852) ≤ d * (E * q ^ 2 / 0.852) at sc
    change E * b ^ 2 / r ≤ _ at h
    ring_nf at sc h ⊢
    exact h.trans sc
  change H * c ≤ d * S
  have h := mul_le_mul_of_nonneg_right height cp.le
  change H * c ≤ (2 * sin (d / 2) / z + E * b ^ 2 / r) * c at h
  have c_le : c ≤ 1 := cos_le_one (d / 2)
  have signed := (sin_two_mul (d / 2)).symm
  rw [show 2 * (d / 2) = d by ring] at signed
  change 2 * sin (d / 2) * c = sin d at signed
  have err := mul_le_of_le_one_right en c_le
  have sn := sine_rowStep_le positive small
  change sin d ≤ d * (1 - 0.061 * a) at sn
  dsimp only [S, z] at h ⊢
  ring_nf at signed h sn err S_err ⊢
  linarith only [h, signed, err, sn, S_err]

/-- A bound on the reciprocal apex sine from the actual chart height and base length. -/
theorem apex_height_to_sine_budget {a B H J : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (polarStrip polarBase : Bool)
    (is_strip : polarBase = true → polarStrip = true) (Bp : 0 < B) (Hp : 0 < H)
    (base : (if polarBase then 0.432 else 0.952) * spacing a < B * cos (rowStep a / 2))
    (height : H ≤ 2 * sin (rowStep a / 2) / 0.9612 +
      ordinateErrorFactor polarStrip * spacing a ^ 2 / radius a)
    (factor : J ≤ if polarStrip then 1.059 else 1.0562) :
    H * J ≤ (apexCountCoefficient polarStrip polarBase - 0.073 * a) *
      (rowStep a / spacing a) * (0.955 * B) := by
  let z : ℝ := 0.9612
  let b := spacing a
  let d := rowStep a
  let r := radius a
  let E := ordinateErrorFactor polarStrip
  let C := apexCountCoefficient polarStrip polarBase
  let B₀ : ℝ := if polarBase then 0.432 else 0.952
  let J₀ : ℝ := if polarStrip then 1.059 else 1.0562
  let c := cos (d / 2)
  have dp : 0 < d := rowStep_pos positive small
  have bp : 0 < b := spacing_pos positive
  have jp : 0 < J₀ := by dsimp [J₀]; split_ifs <;> norm_num
  have rn : 0 < B₀ * b := mul_pos (by dsimp [B₀]; split_ifs <;> norm_num) bp
  let S := (1 - 0.061 * a) / z + E * 0.268 ^ 2 / 0.852
  have Hc : H * c ≤ d * S :=
    apex_height_mul_cos_le positive small polarStrip (spacing_lt positive small).le height
  have HB : H * (B₀ * b) ≤ B * (d * S) := by
    calc
      _ ≤ H * (B * c) := mul_le_mul_of_nonneg_left base.le Hp.le
      _ = B * (H * c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left Hc Bp.le
  have scalar : J₀ * S ≤ (C - 0.073 * a) * (0.955 * B₀) := by
    cases polarStrip <;> cases polarBase
    · norm_num [S, J₀, C, B₀, z, E, ordinateErrorFactor, apexCountCoefficient] <;>
        linarith only [positive]
    · cases is_strip rfl
    · norm_num [S, J₀, C, B₀, z, E, ordinateErrorFactor, apexCountCoefficient] <;>
        linarith only [positive]
    · norm_num [S, J₀, C, B₀, z, E, ordinateErrorFactor, apexCountCoefficient] <;>
        linarith only [positive]
  have top : (H * J) * (B₀ * b) ≤ (B * d) * ((C - 0.073 * a) * (0.955 * B₀)) := by
    calc
      _ ≤ (H * J₀) * (B₀ * b) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left factor Hp.le) rn.le
      _ = J₀ * (H * (B₀ * b)) := by ring
      _ ≤ J₀ * (B * (d * S)) := mul_le_mul_of_nonneg_left HB jp.le
      _ = (B * d) * (J₀ * S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left scalar (mul_nonneg Bp.le dp.le)
  apply le_of_mul_le_mul_right _ rn
  change (H * J) * (B₀ * b) ≤ ((C - 0.073 * a) * (d / b) * (0.955 * B)) * (B₀ * b)
  convert top using 1
  field_simp [bp.ne'] <;> ring

end Unfoldings.FewestNets.RevisedLatitudeGrid
