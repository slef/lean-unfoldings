module

public import Unfoldings.FewestNets.AcuteLatitudeChartSites

/-! The signed gnomonic height fixes the meridional determinant of an annular cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- The meridional cross product of any two assigned row sites is strictly positive. -/
theorem latitude_strip_meridional_cross_pos {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (strip : j < stripCount a) (longitude : ℝ) (lo hi : ℕ)
    (closest₀ : |longitude - rowLongitude (rowSize a j) lo| ≤ π / rowSize a j)
    (closest₁ : |longitude - rowLongitude (rowSize a (j + 1)) hi| ≤ π / rowSize a (j + 1)) :
    let ell := chartColatitude a j
    let p := latitudeFrame ell longitude (rowSite a j lo)
    let q := latitudeFrame ell longitude (rowSite a (j + 1) hi)
    0 < q 1 * p 2 - p 1 * q 2 := by
  let ell := chartColatitude a j
  let w₀ := rowLongitude (rowSize a j) lo - longitude
  let w₁ := rowLongitude (rowSize a (j + 1)) hi - longitude
  have half (k : ℕ) : longitudeStep a k / 2 = π / rowSize a k := by
    unfold longitudeStep
    ring
  have offset₀ : |w₀| ≤ longitudeStep a j / 2 := by
    rw [half, show |w₀| = |longitude - rowLongitude (rowSize a j) lo| from abs_sub_comm _ _]
    exact closest₀
  have offset₁ : |w₁| ≤ longitudeStep a (j + 1) / 2 := by
    rw [half, show |w₁| = |longitude - rowLongitude (rowSize a (j + 1)) hi| from abs_sub_comm _ _]
    exact closest₁
  have h := (chartSite_height_bounds positive small strip w₀ w₁ offset₀ offset₁).1
  have order : chartY ell (colatitude a j) w₀ < chartY ell (colatitude a (j + 1)) w₁ := by
    change 0.883 * radius a < chartY ell (colatitude a (j + 1)) w₁ -
      chartY ell (colatitude a j) w₀ at h
    linarith only [h, radius_pos positive]
  have p_positive : 0 < latitudeDenominator ell (colatitude a j) w₀ :=
    (by norm_num : (0 : ℝ) < 0.991).trans
      (chartSite_bounds positive small strip (Or.inl rfl) longitude w₀ offset₀).1
  have q_positive : 0 < latitudeDenominator ell (colatitude a (j + 1)) w₁ :=
    (by norm_num : (0 : ℝ) < 0.991).trans
      (chartSite_bounds positive small strip (Or.inr rfl) longitude w₁ offset₁).1
  change 0 < latitudeFrame ell longitude (rowSite a (j + 1) hi) 1 *
    latitudeFrame ell longitude (rowSite a j lo) 2 -
    latitudeFrame ell longitude (rowSite a j lo) 1 *
    latitudeFrame ell longitude (rowSite a (j + 1) hi) 2
  unfold rowSite
  rw [show rowLongitude (rowSize a j) lo = longitude + w₀ by dsimp [w₀]; ring,
    show rowLongitude (rowSize a (j + 1)) hi = longitude + w₁ by dsimp [w₁]; ring,
    latitudeFrame_site, latitudeFrame_site]
  change 0 < (sin (colatitude a (j + 1) - ell) -
    cos ell * sin (colatitude a (j + 1)) * (1 - cos w₁)) *
      latitudeDenominator ell (colatitude a j) w₀ -
    (sin (colatitude a j - ell) - cos ell * sin (colatitude a j) * (1 - cos w₀)) *
      latitudeDenominator ell (colatitude a (j + 1)) w₁
  exact sub_pos.mpr ((div_lt_div_iff₀ p_positive q_positive).mp order)

end Unfoldings.FewestNets.AcuteLatitudeGrid
