module

public import Unfoldings.FewestNets.LatitudeFrame
public import Unfoldings.FewestNets.LatitudeMetricRows
public import Unfoldings.Geometry.GnomonicDistanceBounds
public import Unfoldings.Geometry.NorthFrame

/-! The latitude chart's explicit uniform coordinate and tilt bounds. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real InnerProductGeometry

/-- The spherical frame and the paper's angular and longitude estimates put
every assigned triangle vertex within the stated gnomonic rectangle. -/
theorem latitude_vertex_coordinate_bounds {r b ell ell' w : ℝ}
    (r_pos : 0 < r) (r_small : r < 0.116)
    (b_pos : 0 < b) (b_small : b < 0.236 * r)
    (delta : |ell' - ell| ≤ r / 2) (mid_sine : 0 ≤ sin ell)
    (row_sine : 0.999 * (r / 2) < sin ell')
    (longitude_mid : sin ell * |w| ≤ 1.005 * b)
    (longitude_row : sin ell' * |w| ≤ b / 2) :
    let Z := latitudeDenominator ell ell' w
    let X := sin ell' * sin w / Z
    let Y := (sin (ell' - ell) - cos ell * sin ell' * (1 - cos w)) / Z
    0.998 < Z ∧ |X| < 0.502 * b ∧
      |Y - sin (ell' - ell) / Z| ≤ 0.251 * b ^ 2 / r ∧ |Y| < 0.516 * r := by
  let Z := latitudeDenominator ell ell' w
  let X := sin ell' * sin w / Z
  let Y := (sin (ell' - ell) - cos ell * sin ell' * (1 - cos w)) / Z
  have row_pos : 0 < sin ell' := by linarith only [row_sine, r_pos]
  have b_cap : b < 0.236 * 0.116 := by linarith only [r_small, b_small]
  have cos_drop : 1 - cos w ≤ w ^ 2 / 2 := by
    linarith only [one_sub_sq_div_two_le_cos (x := w)]
  have cos_drop_nonneg : 0 ≤ 1 - cos w := sub_nonneg.mpr (cos_le_one _)
  have drop : sin ell' * sin ell * (1 - cos w) ≤ 0.25125 * b ^ 2 := by
    have factor := mul_le_mul_of_nonneg_left cos_drop (mul_nonneg row_pos.le mid_sine)
    have product := mul_le_mul longitude_row longitude_mid
      (mul_nonneg mid_sine (abs_nonneg _)) (by positivity : 0 ≤ b / 2)
    rw [← sq_abs w] at factor
    nlinarith only [factor, product]
  have step_sq := pow_le_pow_left₀ (abs_nonneg (ell' - ell)) delta 2
  rw [sq_abs] at step_sq
  have z_lower : 0.998 < Z := by
    have radius_sq := pow_le_pow_left₀ r_pos.le r_small.le 2
    have spacing_sq := pow_le_pow_left₀ b_pos.le b_cap.le 2
    change 0.998 < cos (ell' - ell) - sin ell' * sin ell * (1 - cos w)
    nlinarith only [drop, step_sq, radius_sq, spacing_sq, one_sub_sq_div_two_le_cos (x := ell' - ell)]
  have z_pos : 0 < Z := by linarith only [z_lower]
  have x_bound : |X| < 0.502 * b := by
    change |sin ell' * sin w / Z| < _
    rw [abs_div, abs_mul, abs_of_pos z_pos, abs_of_pos row_pos]
    apply (div_lt_iff₀ z_pos).mpr
    have limit := (mul_le_mul_of_nonneg_left (abs_sin_le_abs (x := w)) row_pos.le).trans longitude_row
    have strict := mul_lt_mul_of_pos_left z_lower (by positivity : 0 < 0.502 * b)
    linarith only [limit, strict, b_pos]
  have y_correction : |Y - sin (ell' - ell) / Z| ≤ 0.251 * b ^ 2 / r := by
    have error : Y - sin (ell' - ell) / Z = -(cos ell * sin ell' * (1 - cos w)) / Z := by
      change (sin (ell' - ell) - cos ell * sin ell' * (1 - cos w)) / Z - sin (ell' - ell) / Z = _
      rw [← sub_div, sub_sub_cancel_left]
    rw [error, abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos z_pos, abs_of_pos row_pos,
      abs_of_nonneg cos_drop_nonneg]
    have cos_cap := abs_cos_le_one ell
    have max_drop := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right cos_cap row_pos.le) cos_drop_nonneg
    rw [one_mul] at max_drop
    have numerator : sin ell' * (1 - cos w) ≤ b ^ 2 / (8 * sin ell') := by
      apply (le_div_iff₀ (by positivity : 0 < 8 * sin ell')).mpr
      have square := pow_le_pow_left₀ (mul_nonneg row_pos.le (abs_nonneg w)) longitude_row 2
      have fall := mul_le_mul_of_nonneg_left cos_drop
        (by positivity : 0 ≤ 8 * sin ell' ^ 2)
      rw [← sq_abs w] at fall
      nlinarith only [square, fall]
    have final : (b ^ 2 / (8 * sin ell')) / Z ≤ 0.251 * b ^ 2 / r := by
      rw [div_div]
      apply (div_le_div_iff₀ (by positivity) r_pos).mpr
      have strong := mul_lt_mul (show 0.999 * (r / 2) < sin ell' from row_sine)
        z_lower.le (by norm_num : (0 : ℝ) < 0.998) row_pos.le
      have balance : r ≤ 0.251 * (8 * sin ell' * Z) := by
        linarith only [strong, r_pos]
      have scaled := mul_le_mul_of_nonneg_right balance (sq_nonneg b)
      linarith only [scaled]
    exact (div_le_div_of_nonneg_right (max_drop.trans numerator) z_pos.le).trans final
  have y_bound : |Y| < 0.516 * r := by
    have triangle := abs_sub_le Y (sin (ell' - ell) / Z) 0
    simp only [sub_zero] at triangle
    have height : |sin (ell' - ell) / Z| ≤ r / (2 * 0.998) := by
      rw [abs_div, abs_of_pos z_pos]
      calc
        _ ≤ (r / 2) / Z := div_le_div_of_nonneg_right
          (abs_sin_le_abs.trans delta) z_pos.le
        _ ≤ (r / 2) / 0.998 := div_le_div_of_nonneg_left (by positivity) (by norm_num) z_lower.le
        _ = _ := by ring
    have b_ratio : b ^ 2 / r ≤ 0.236 ^ 2 * r := by
      apply (div_le_iff₀ r_pos).mpr
      have square := pow_le_pow_left₀ b_pos.le b_small.le 2
      nlinarith only [square]
    have scaled := mul_le_mul_of_nonneg_left b_ratio (by norm_num : (0 : ℝ) ≤ 0.251)
    have correction' : |Y - sin (ell' - ell) / Z| ≤ 0.014 * r := by
      have bound : 0.251 * (0.236 ^ 2 * r) ≤ 0.014 * r := by
        nlinarith only [r_pos]
      exact y_correction.trans (by simpa only [mul_div_assoc] using scaled.trans bound)
    have room : |sin (ell' - ell) / Z| < 0.502 * r :=
      height.trans_lt (by
        have eq : r / (2 * 0.998) = (250 / 499 : ℝ) * r := by ring
        rw [eq]
        linarith only [r_pos])
    linarith only [triangle, room, correction']
  exact ⟨z_lower, x_bound, y_correction, y_bound⟩

/-- The actual angular distance of an assigned site to the chart center, as in
the latitude tilt estimate. The longitude hypotheses are the respective row bounds. -/
theorem latitude_vertex_tilt_lt {r b ell ell' longitude w : ℝ}
    (r_pos : 0 < r) (r_small : r < 0.116)
    (b_pos : 0 < b) (b_small : b < 0.236 * r)
    (delta : |ell' - ell| ≤ r / 2) (mid_sine : 0 ≤ sin ell)
    (row_sine : 0.999 * (r / 2) < sin ell')
    (longitude_mid : sin ell * |w| ≤ 1.005 * b)
    (longitude_row : sin ell' * |w| ≤ b / 2) :
    angle (latitudeSite ell longitude) (latitudeSite ell' (longitude + w)) < 0.53 * r := by
  let z := latitudeFrame ell longitude (latitudeSite ell' (longitude + w))
  let p := (z 2)⁻¹ • Cap.horizontal z
  obtain ⟨above, x_small, _, y_small⟩ := latitude_vertex_coordinate_bounds
    r_pos r_small b_pos b_small delta mid_sine row_sine longitude_mid longitude_row
  have z_pos : 0 < z 2 := by
    unfold z
    rw [latitudeFrame_site]
    exact (by norm_num : (0 : ℝ) < 0.998).trans above
  have x_small' : |p 0| < 0.119 * r := by
    unfold p z
    rw [latitude_gnomonic_site]
    exact x_small.trans (by linarith only [r_pos, b_small])
  have y_small' : |p 1| < 0.516 * r := by
    unfold p z
    rw [latitude_gnomonic_site]
    exact y_small
  have norm_bound : ‖p‖ < 0.53 * r := by
    apply (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have x := pow_le_pow_left₀ (abs_nonneg (p 0)) x_small'.le 2
    have y := pow_le_pow_left₀ (abs_nonneg (p 1)) y_small'.le 2
    rw [sq_abs] at x y
    nlinarith only [x, y, sq_pos_of_pos r_pos]
  have centered : latitudeFrame ell longitude (latitudeSite ell longitude) = Cap.northLift 0 := by
    simpa [latitudeDenominator, Cap.northLift] using latitudeFrame_site ell ell longitude 0
  have norm_z : ‖z‖ = 1 := by
    unfold z
    rw [LinearIsometryEquiv.norm_map, latitudeSite_unit]
  have image := Cap.gnomonicNormal_slope z norm_z z_pos
  change Cap.gnomonicNormal p = z at image
  have origin : Cap.gnomonicNormal 0 = Cap.northLift 0 :=
    NormedSpace.normalize_eq_self_of_norm_eq_one Cap.northLift_zero_unit
  rw [← (latitudeFrame ell longitude).toLinearIsometry.angle_map,
    LinearIsometryEquiv.coe_toLinearIsometry, centered,
    show latitudeFrame ell longitude (latitudeSite ell' (longitude + w)) = z from rfl,
    ← origin, ← image]
  exact (Cap.angle_gnomonicNormal_le_dist 0 p).trans_lt (by simpa only [dist_zero_left] using norm_bound)

end Unfoldings.FewestNets
