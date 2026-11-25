module

public import Unfoldings.FewestNets.LatitudeSiteSupport
public import Unfoldings.FewestNets.LatitudeNearestSupport

/-! The chord plane's meridional normal is exact, including at midpoint ties. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- Two points with distinct meridional coordinates lie on the same exact
support plane after tilting the chart by their signed secant angle. -/
theorem latitudeSecant_support_eq (ell longitude : ℝ) (x y : Space)
    (different : latitudeFrame ell longitude y 1 ≠ latitudeFrame ell longitude x 1) :
    let k := (latitudeFrame ell longitude y 2 - latitudeFrame ell longitude x 2) /
      (latitudeFrame ell longitude y 1 - latitudeFrame ell longitude x 1)
    inner ℝ (latitudeSite (ell - arctan k) longitude) x =
      inner ℝ (latitudeSite (ell - arctan k) longitude) y := by
  let Z (p : Space) := latitudeFrame ell longitude p 2
  let Y (p : Space) := latitudeFrame ell longitude p 1
  let k := (Z y - Z x) / (Y y - Y x)
  have exact_secant : k * (Y y - Y x) = Z y - Z x :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr different)
  have sine : sin (arctan k) = k * cos (arctan k) := by
    rw [sin_arctan, cos_arctan, mul_one_div]
  change inner ℝ (latitudeSite (ell - arctan k) longitude) x =
    inner ℝ (latitudeSite (ell - arctan k) longitude) y
  rw [latitudeSupport_eq_chart, latitudeSupport_eq_chart, sine]
  change cos (arctan k) * Z x - k * cos (arctan k) * Y x =
    cos (arctan k) * Z y - k * cos (arctan k) * Y y
  have equality := congrArg (fun t : ℝ => cos (arctan k) * t) exact_secant
  linarith only [equality]

/-- Longitude symmetry gives equal support values at both endpoints of a
row edge centered on this meridian, for any meridional tilt. -/
theorem latitudeSymmetric_support_eq (ell row longitude w : ℝ) :
    inner ℝ (latitudeSite ell longitude) (latitudeSite row (longitude - w)) =
      inner ℝ (latitudeSite ell longitude) (latitudeSite row (longitude + w)) := by
  rw [sub_eq_add_neg, latitudeSite_inner, latitudeSite_inner, cos_neg]

/-- An actual longitude choice within half a step maximizes support on
its entire row, at any supporting colatitude in the correct hemisphere. -/
theorem latitudeNearest_support_ge {k j₀ : ℕ} (positive : 0 < k)
    {ell row longitude : ℝ} (ell_range : ell ∈ Set.Icc 0 π) (row_range : row ∈ Set.Icc 0 π)
    (closest : |longitude - rowLongitude k j₀| ≤ π / k) (j : ℕ) :
    inner ℝ (latitudeSite ell longitude) (latitudeSite row (rowLongitude k j)) ≤
      inner ℝ (latitudeSite ell longitude) (latitudeSite row (rowLongitude k j₀)) := by
  have value (i : ℕ) :
      inner ℝ (latitudeSite ell longitude) (latitudeSite row (rowLongitude k i)) =
        cos (row - ell) - sin row * sin ell * (1 - cos (longitude - rowLongitude k i)) := by
    have exact_value := latitudeSite_inner ell row longitude (rowLongitude k i - longitude)
    rw [show longitude + (rowLongitude k i - longitude) = rowLongitude k i by ring,
      show rowLongitude k i - longitude = -(longitude - rowLongitude k i) by ring,
      cos_neg] at exact_value
    exact exact_value
  rw [value j, value j₀]
  have upright : 0 ≤ sin row * sin ell :=
    mul_nonneg (sin_nonneg_of_nonneg_of_le_pi row_range.1 row_range.2)
      (sin_nonneg_of_nonneg_of_le_pi ell_range.1 ell_range.2)
  exact sub_le_sub_left
    (mul_le_mul_of_nonneg_left (sub_le_sub_left (cos_longitude_le_of_nearest positive closest j) 1)
      upright) _

end Unfoldings.FewestNets
