module

public import Unfoldings.FewestNets.LatitudeSupportingGap

/-! A normal of a straightened latitude triangle cannot support any distant row. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- A site evaluated in another latitude direction has the exact longitude penalty. -/
theorem latitudeSite_inner (ell row longitude w : ℝ) :
    inner ℝ (latitudeSite ell longitude) (latitudeSite row (longitude + w)) =
      cos (row - ell) - sin row * sin ell * (1 - cos w) := by
  have height := congrArg (fun p : Space => p 2) (latitudeFrame_site ell row longitude w)
  change latitudeFrame ell longitude (latitudeSite row (longitude + w)) 2 =
    latitudeDenominator ell row w at height
  rwa [latitudeFrame_coordinate, show latitudeAxes ell longitude 2 = latitudeSite ell longitude from rfl]
    at height

/-- A meridional chart tilt changes its normal by the actual sine and cosine of that tilt. -/
theorem latitudeSite_sub_colatitude (ell longitude θ : ℝ) :
    latitudeSite (ell - θ) longitude =
      cos θ • latitudeSite ell longitude - sin θ • latitudeSouth ell longitude := by
  ext i
  fin_cases i <;>
    simp [latitudeSite, latitudeSouth, PiLp.sub_apply, PiLp.smul_apply, sin_sub, cos_sub] <;> ring

/-- The signed north-south tilt tests a chord plane by its unnormalized chart coordinates. -/
theorem latitudeSupport_eq_chart (ell longitude θ : ℝ) (x : Space) :
    inner ℝ (latitudeSite (ell - θ) longitude) x =
      cos θ * latitudeFrame ell longitude x 2 - sin θ * latitudeFrame ell longitude x 1 := by
  rw [latitudeSite_sub_colatitude, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    latitudeFrame_coordinate, latitudeFrame_coordinate]
  rfl

/-- After the support normal is shifted by the chord plane's small tilt,
all farther rows lie strictly below a nearby row vertex. -/
theorem latitudeSite_far_support_lt {r b ell near far longitude w z θ : ℝ}
    (r_pos : 0 < r) (b_pos : 0 < b) (b_small : b < 0.236 * r)
    (tilt : |θ| ≤ 0.016 * r) (shifted : ell - θ ∈ Set.Icc 0 π)
    (near_row : |near - ell| ≤ r / 2) (far_row : 0.956 * r ≤ |far - ell|)
    (far_range : far ∈ Set.Icc 0 π)
    (near_sine : 0.999 * (r / 2) < sin near)
    (longitude_near : sin near * |w| ≤ b / 2)
    (longitude_chart : sin ell * |w| ≤ 1.005 * b) :
    inner ℝ (latitudeSite (ell - θ) longitude) (latitudeSite far (longitude + z)) <
      inner ℝ (latitudeSite (ell - θ) longitude) (latitudeSite near (longitude + w)) := by
  have sin_pos : 0 < sin near := by linarith only [near_sine, r_pos]
  have shifted_sin : 0 ≤ sin (ell - θ) := sin_nonneg_of_nonneg_of_le_pi shifted.1 shifted.2
  have longitude_size : r * |w| ≤ 1.002 * b := by
    have product := mul_le_mul_of_nonneg_right near_sine.le (abs_nonneg w)
    linarith only [product, longitude_near, b_pos]
  have sine_shift : sin (ell - θ) - sin ell ≤ 0.016 * r := by
    have diff := (le_abs_self (sin (ell - θ) - sin ell)).trans (abs_sin_sub_sin_le (ell - θ) ell)
    rw [sub_sub_cancel_left, abs_neg] at diff
    exact diff.trans tilt
  have weighted_shift : sin (ell - θ) * |w| ≤ 1.022 * b := by
    have product := mul_le_mul_of_nonneg_right sine_shift (abs_nonneg w)
    linarith only [product, longitude_size, longitude_chart, b_pos]
  let loss := sin near * sin (ell - θ) * (1 - cos w)
  have bound : loss ≤ 0.02 * r ^ 2 := by
    have exact_loss : loss ≤ 0.2555 * b ^ 2 := by
      have cos_drop : 1 - cos w ≤ w ^ 2 / 2 := by
        linarith only [one_sub_sq_div_two_le_cos (x := w)]
      have scaled := mul_le_mul_of_nonneg_left cos_drop (mul_nonneg sin_pos.le shifted_sin)
      rw [← sq_abs w] at scaled
      have product := mul_le_mul longitude_near weighted_shift
        (mul_nonneg shifted_sin (abs_nonneg w)) (by positivity : 0 ≤ b / 2)
      dsimp only [loss]
      nlinarith only [product, scaled]
    have square := pow_le_pow_left₀ b_pos.le b_small.le 2
    linarith only [exact_loss, square, sq_nonneg r]
  have near_bound : |near - (ell - θ)| ≤ 0.516 * r := by
    rw [show near - (ell - θ) = near - ell + θ by ring]
    exact (abs_add_le _ _).trans (by linarith only [near_row, tilt])
  have far_bound : 0.94 * r ≤ |far - (ell - θ)| := by
    have triangle := abs_add_le (far - (ell - θ)) (-θ)
    rw [show far - (ell - θ) + -θ = far - ell by ring, abs_neg] at triangle
    linarith only [triangle, far_row, tilt]
  have range : |far - (ell - θ)| ≤ π := abs_le.mpr
    ⟨by linarith only [far_range.1, shifted.2], by linarith only [far_range.2, shifted.1]⟩
  have lower := latitude_far_cosine_lt_near r_pos near_bound far_bound range bound
  rw [latitudeSite_inner, latitudeSite_inner]
  have loss_far : 0 ≤ sin far * sin (ell - θ) * (1 - cos z) := mul_nonneg
    (mul_nonneg (sin_nonneg_of_nonneg_of_le_pi far_range.1 far_range.2) shifted_sin)
    (sub_nonneg.mpr (cos_le_one _))
  exact (sub_le_self _ loss_far).trans_lt lower

end Unfoldings.FewestNets
