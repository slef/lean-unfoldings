module

public import Unfoldings.Geometry.SphericalTriangleGram
public import Unfoldings.FewestNets.LatitudeSiteSupport

/-! Exact chord lengths and oriented determinant in the latitude coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real InnerProductGeometry

private theorem two_sin_half_sq (x : ℝ) : 2 * sin (x / 2) ^ 2 = 1 - cos x := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  linarith only [h, sin_sq_add_cos_sq (x / 2)]

/-- Separating the exact meridional and longitudinal contributions avoids
subtractive cancellation in the chord comparisons. -/
theorem latitudeSite_chord_sq (b a lon lon₂ : ℝ) :
    ‖latitudeSite b lon - latitudeSite a lon₂‖ ^ 2 =
      4 * sin ((a - b) / 2) ^ 2 + 4 * sin b * sin a * sin ((lon₂ - lon) / 2) ^ 2 := by
  have pair : inner ℝ (latitudeSite b lon) (latitudeSite a lon₂) =
      cos (a - b) - sin a * sin b * (1 - cos (lon₂ - lon)) := by
    have h := latitudeSite_inner b a lon (lon₂ - lon)
    rwa [show lon + (lon₂ - lon) = lon₂ by ring] at h
  rw [norm_sub_pow_two_real, latitudeSite_unit, latitudeSite_unit, pair]
  linear_combination -2 * two_sin_half_sq (a - b) - (2 * sin a * sin b) * two_sin_half_sq (lon₂ - lon)

/-- Determinant of the two symmetric bases and the actual offset apex.
The leading sine is the signed difference of the two colatitudes. -/
theorem latitudeSite_det_of_base (b a lon s t : ℝ) :
    spatialRayDet (latitudeSite b (lon - s)) (latitudeSite b (lon + s)) (latitudeSite a (lon + t)) =
      2 * sin b * sin s * (sin (b - a) + cos b * sin a * (1 - cos t) -
        sin b * cos a * (1 - cos s)) := by
  calc
    _ = (sin lon ^ 2 + cos lon ^ 2) * (2 * sin b * sin s *
        (sin (b - a) + cos b * sin a * (1 - cos t) - sin b * cos a * (1 - cos s))) := by
      simp only [spatialRayDet, latitudeSite, sin_add, sin_sub, cos_add, cos_sub]
      change
        (sin b * (cos lon * cos s + sin lon * sin s)) *
            (sin b * (sin lon * cos s + cos lon * sin s) * cos a -
             cos b * (sin a * (sin lon * cos t + cos lon * sin t))) -
          (sin b * (sin lon * cos s - cos lon * sin s)) *
            (sin b * (cos lon * cos s - sin lon * sin s) * cos a -
             cos b * (sin a * (cos lon * cos t - sin lon * sin t))) +
          cos b * ((sin b * (cos lon * cos s - sin lon * sin s)) *
            (sin a * (sin lon * cos t + cos lon * sin t)) -
             (sin b * (sin lon * cos s + cos lon * sin s)) *
              (sin a * (cos lon * cos t - sin lon * sin t))) = _
      ring
    _ = _ := by rw [sin_sq_add_cos_sq, one_mul]

end Unfoldings.FewestNets
