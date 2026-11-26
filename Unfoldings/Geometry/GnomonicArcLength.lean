module

public import Unfoldings.Geometry.GnomonicDistanceBounds

/-! A sharper length bound for the spherical lift of a short chart segment. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real InnerProductGeometry

/-- A chart chord of length at most two has largest angle when centered
at the chart origin. -/
theorem angle_gnomonicNormal_le_centered (p q : Plane) (short : ‖p - q‖ ≤ 2) :
    angle (gnomonicNormal p) (gnomonicNormal q) ≤ 2 * arctan (‖p - q‖ / 2) := by
  let u := northLift p
  let v := northLift q
  let U := ‖u‖
  let V := ‖v‖
  let d := ‖p - q‖ / 2
  let H := (U ^ 2 + V ^ 2) / 2
  have up : 0 < U := norm_pos_iff.mpr (northLift_ne_zero p)
  have vp : 0 < V := norm_pos_iff.mpr (northLift_ne_zero q)
  have dp : 0 ≤ d := by dsimp only [d]; positivity
  have dmax : d ≤ 1 := by dsimp only [d]; linarith only [short]
  have hd : 0 < H := by dsimp only [H]; positivity
  have den : U * V ≤ H := by
    dsimp only [H]
    nlinarith only [sq_nonneg (U - V)]
  have hnorm₀ : U ^ 2 = ‖p‖ ^ 2 + 1 := by
    rw [show U = ‖northLift p‖ from rfl, horizontal_norm_sq, northLift_horizontal, northLift_height, one_pow]
  have hnorm₁ : V ^ 2 = ‖q‖ ^ 2 + 1 := by
    rw [show V = ‖northLift q‖ from rfl, horizontal_norm_sq, northLift_horizontal, northLift_height, one_pow]
  have hmin : 1 + d ^ 2 ≤ H := by
    have par := parallelogram_law_with_norm ℝ p q
    dsimp only [H, d]
    rw [hnorm₀, hnorm₁, div_pow]
    nlinarith only [par, sq_nonneg ‖p + q‖]
  have diff : ‖u - v‖ ^ 2 = 4 * d ^ 2 := by
    dsimp only [u, v, d]
    rw [horizontal_norm_sq, map_sub, northLift_horizontal, northLift_horizontal]
    change ‖p - q‖ ^ 2 + (1 - 1) ^ 2 = 4 * (‖p - q‖ / 2) ^ 2
    ring
  have dot : inner ℝ u v = H - 2 * d ^ 2 := by
    have h := norm_sub_sq_real u v
    rw [diff] at h
    dsimp only [H]
    change 4 * d ^ 2 = U ^ 2 - 2 * inner ℝ u v + V ^ 2 at h
    linarith only [h]
  have angleCos : cos (angle (gnomonicNormal p) (gnomonicNormal q)) =
      (H - 2 * d ^ 2) / (U * V) := by
    rw [← inner_eq_cos_angle_of_norm_eq_one (gnomonicNormal_unit p) (gnomonicNormal_unit q)]
    change inner ℝ (U⁻¹ • u) (V⁻¹ • v) = _
    rw [real_inner_smul_left, real_inner_smul_right, dot]
    field_simp [up.ne', vp.ne']
  have centered : cos (2 * arctan d) = 1 - 2 * d ^ 2 / (1 + d ^ 2) := by
    rw [cos_two_mul, cos_arctan, div_pow, sq_sqrt (by positivity)]
    have pos : 1 + d ^ 2 ≠ 0 := by positivity
    norm_num
    field_simp [pos]
    ring
  have arctan_nonneg := arctan_nonneg.mpr dp
  have t_range : 2 * arctan d ∈ Set.Icc 0 π :=
    ⟨by positivity, by linarith only [arctan_lt_pi_div_two d]⟩
  apply (strictAntiOn_cos.le_iff_ge t_range ⟨angle_nonneg _ _, angle_le_pi _ _⟩).mp
  rw [angleCos, centered]
  have square := pow_le_pow_left₀ dp dmax 2
  have numerator : 0 ≤ H - 2 * d ^ 2 := by linarith only [square, hmin]
  calc
    _ ≤ 1 - 2 * d ^ 2 / H := by
      have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * d ^ 2)
        (by positivity : 0 < 1 + d ^ 2) hmin
      linarith only [h]
    _ = (H - 2 * d ^ 2) / H := by rw [sub_div, div_self hd.ne']
    _ ≤ _ := div_le_div_of_nonneg_left numerator (mul_pos up vp) den

end Unfoldings.Cap
