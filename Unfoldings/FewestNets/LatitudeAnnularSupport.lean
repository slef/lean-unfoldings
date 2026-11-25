module

public import Unfoldings.FewestNets.LatitudeStripSupport

/-! The nearest rows have an actual common supporting plane of the sampled sphere. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

private theorem latitude_denominator_drop {b ell row w : ℝ} (b_nonneg : 0 ≤ b)
    (sin_ell : 0 ≤ sin ell) (sin_row : 0 ≤ sin row)
    (chart : sin ell * |w| ≤ 1.005 * b) (local_row : sin row * |w| ≤ b / 2) :
    cos (row - ell) - 0.25125 * b ^ 2 ≤ latitudeDenominator ell row w ∧
      latitudeDenominator ell row w ≤ cos (row - ell) := by
  have penalty := mul_nonneg (mul_nonneg sin_row sin_ell) (sub_nonneg.mpr (cos_le_one w))
  refine ⟨?_, sub_le_self _ penalty⟩
  have drop : 1 - cos w ≤ w ^ 2 / 2 := by
    linarith only [one_sub_sq_div_two_le_cos (x := w)]
  have scaled := mul_le_mul_of_nonneg_left drop (mul_nonneg sin_row sin_ell)
  have product := mul_le_mul local_row chart (mul_nonneg sin_ell (abs_nonneg w))
    (by positivity : 0 ≤ b / 2)
  rw [← sq_abs w] at scaled
  unfold latitudeDenominator
  nlinarith only [scaled, product]

set_option maxHeartbeats 850000 in
-- The two actual sampled sites share the center longitude and preserve the physical coordinates.
/-- At the strip center the signed secant tilt that equalizes the two
nearest support values is smaller than 0.016 times the meridional scale. -/
theorem latitude_strip_secant_tilt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (strip : j < latitudeStripCount a) (longitude : ℝ) {w₀ w₁ : ℝ}
    (close₀ : |w₀| ≤ latitudeLongitudeStep a j / 2)
    (close₁ : |w₁| ≤ latitudeLongitudeStep a (j + 1) / 2) :
    let ell := latitudeStripMid a j
    let x := latitudeFrame ell longitude (latitudeSite (latitudeColatitude a j) (longitude + w₀))
    let y := latitudeFrame ell longitude (latitudeSite (latitudeColatitude a (j + 1)) (longitude + w₁))
    0 < y 1 - x 1 ∧ |arctan ((y 2 - x 2) / (y 1 - x 1))| ≤ 0.016 * latitudeRadius a := by
  let r := latitudeRadius a
  let b := latitudeSpacing a
  let ell := latitudeStripMid a j
  let t := latitudeRowStep a / 2
  let row₀ := latitudeColatitude a j
  let row₁ := latitudeColatitude a (j + 1)
  let Z₀ := latitudeDenominator ell row₀ w₀
  let Z₁ := latitudeDenominator ell row₁ w₁
  let V₀ := sin (row₀ - ell) - cos ell * sin row₀ * (1 - cos w₀)
  let V₁ := sin (row₁ - ell) - cos ell * sin row₁ * (1 - cos w₁)
  let Y₀ := V₀ / Z₀
  let Y₁ := V₁ / Z₁
  have r_pos : 0 < r := latitudeRadius_pos positive
  have b_pos : 0 < b := by unfold b latitudeSpacing; positivity
  have b_small : b < 0.236 * r := latitudeSpacing_lt positive small
  have z_bound := latitudeStripMid_bounds positive small strip
  have sine_ell : 0 ≤ sin ell := sin_nonneg_of_nonneg_of_le_pi
    (by linarith only [z_bound.1, r_pos]) (by linarith only [z_bound.2, r_pos])
  have before : row₀ - ell = -t := by
    have h := latitudeStripMid_sub_lower a j
    dsimp only [row₀, ell, t]
    linarith only [h]
  have after : row₁ - ell = t := latitudeStripMid_sub_upper a j
  have step := latitudeRowStep_bounds positive small
  have half_step : 0.963 * (r / 2) < t ∧ t ≤ r / 2 := by
    dsimp only [r, t]
    constructor <;> linarith only [step.1, step.2]
  have t_pos : 0 < t := by linarith only [half_step.1, r_pos]
  have latitude₀ : |row₀ - ell| ≤ r / 2 := by
    rw [before, abs_neg, abs_of_pos t_pos]
    exact half_step.2
  have latitude₁ : |row₁ - ell| ≤ r / 2 := by
    rw [after, abs_of_pos t_pos]
    exact half_step.2
  obtain ⟨lower₀, upper₀⟩ := latitudeColatitude_bounds positive small strip.le
  obtain ⟨lower₁, upper₁⟩ := latitudeColatitude_bounds positive small (Nat.succ_le_of_lt strip)
  have sine₀ := latitude_sin_lower positive small lower₀ upper₀
  have sine₁ := latitude_sin_lower positive small lower₁ upper₁
  obtain ⟨chart₀, near₀⟩ := latitude_weighted_longitude_bounds positive small strip.le
    (by rwa [abs_sub_comm]) close₀
  obtain ⟨chart₁, near₁⟩ := latitude_weighted_longitude_bounds positive small (Nat.succ_le_of_lt strip)
    (by rwa [abs_sub_comm]) close₁
  obtain ⟨up₀, _, err₀, y₀⟩ := latitude_vertex_coordinate_bounds r_pos (latitudeRadius_lt small)
    b_pos b_small latitude₀ sine_ell sine₀ chart₀ near₀
  obtain ⟨up₁, _, err₁, y₁⟩ := latitude_vertex_coordinate_bounds r_pos (latitudeRadius_lt small)
    b_pos b_small latitude₁ sine_ell sine₁ chart₁ near₁
  have pos₀ : 0 < Z₀ := by linarith only [up₀]
  have pos₁ : 0 < Z₁ := by linarith only [up₁]
  have drop₀ := latitude_denominator_drop b_pos.le sine_ell
    (by linarith only [sine₀, r_pos]) chart₀ near₀
  have drop₁ := latitude_denominator_drop b_pos.le sine_ell
    (by linarith only [sine₁, r_pos]) chart₁ near₁
  change cos (row₀ - ell) - _ ≤ Z₀ ∧ Z₀ ≤ cos (row₀ - ell) at drop₀
  change cos (row₁ - ell) - _ ≤ Z₁ ∧ Z₁ ≤ cos (row₁ - ell) at drop₁
  rw [before, cos_neg] at drop₀
  rw [after] at drop₁
  have upper₀' : Z₀ ≤ 1 := drop₀.2.trans (cos_le_one t)
  have upper₁' : Z₁ ≤ 1 := drop₁.2.trans (cos_le_one t)
  change |Y₀ - sin (row₀ - ell) / Z₀| ≤ _ at err₀
  change |Y₁ - sin (row₁ - ell) / Z₁| ≤ _ at err₁
  rw [before, sin_neg, neg_div, sub_neg_eq_add] at err₀
  rw [after] at err₁
  have H := latitude_chart_height_bounds r_pos (latitudeRadius_lt small) b_pos b_small
    half_step.1 half_step.2 up₀ upper₀' up₁ upper₁' err₀ err₁
  have h_eq : V₁ - V₀ = Y₁ * Z₁ - Y₀ * Z₀ := by
    dsimp only [Y₀, Y₁]
    rw [div_mul_cancel₀ _ pos₀.ne', div_mul_cancel₀ _ pos₁.ne']
  obtain ⟨raw_gap, tilt⟩ := latitude_support_tilt_of_chart r_pos b_pos b_small H.1 h_eq
    y₀.le y₁.le ⟨up₀.le, upper₀'⟩ ⟨up₁.le, upper₁'⟩ drop₀ drop₁
  dsimp only
  rw [latitudeFrame_site, latitudeFrame_site]
  change 0 < V₁ - V₀ ∧ |arctan ((Z₁ - Z₀) / (V₁ - V₀))| ≤ 0.016 * r
  exact ⟨(mul_pos (by norm_num) r_pos).trans raw_gap, tilt.le⟩

set_option maxHeartbeats 1000000 in
-- Use one and the same tilted unit normal for both rows and both poles.
/-- The two nearest vertices at the meridian lie in a plane supporting all
sampled annular sites and both poles. The normal is the actual secant normal. -/
theorem exists_latitudeAnnular_support {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (strip : j < latitudeStripCount a) (longitude : ℝ) (lo hi : ℕ)
    (nearest₀ : |longitude - rowLongitude (latitudeRowSize a j) lo| ≤ π / latitudeRowSize a j)
    (nearest₁ : |longitude - rowLongitude (latitudeRowSize a (j + 1)) hi| ≤
      π / latitudeRowSize a (j + 1)) :
    ∃ θ : ℝ, |θ| ≤ 0.016 * latitudeRadius a ∧
      let n := latitudeSite (latitudeStripMid a j - θ) longitude
      let d := inner ℝ n (latitudeRowSite a j lo)
      d = inner ℝ n (latitudeRowSite a (j + 1) hi) ∧
      (∀ i ≤ latitudeStripCount a, ∀ k, inner ℝ n (latitudeRowSite a i k) ≤ d) ∧
      inner ℝ n (latitudeSite 0 longitude) < d ∧ inner ℝ n (latitudeSite π longitude) < d := by
  let ell := latitudeStripMid a j
  let w₀ := rowLongitude (latitudeRowSize a j) lo - longitude
  let w₁ := rowLongitude (latitudeRowSize a (j + 1)) hi - longitude
  have half (i : ℕ) : latitudeLongitudeStep a i / 2 = π / latitudeRowSize a i := by
    unfold latitudeLongitudeStep
    ring
  have close₀ : |w₀| ≤ latitudeLongitudeStep a j / 2 := by
    dsimp only [w₀]
    rwa [half, abs_sub_comm]
  have close₁ : |w₁| ≤ latitudeLongitudeStep a (j + 1) / 2 := by
    dsimp only [w₁]
    rwa [half, abs_sub_comm]
  have longitude₀ : longitude + w₀ = rowLongitude (latitudeRowSize a j) lo := by
    dsimp only [w₀]
    ring
  have longitude₁ : longitude + w₁ = rowLongitude (latitudeRowSize a (j + 1)) hi := by
    dsimp only [w₁]
    ring
  have bounds := latitude_strip_secant_tilt positive small strip longitude close₀ close₁
  dsimp only at bounds
  rw [longitude₀, longitude₁] at bounds
  let x := latitudeRowSite a j lo
  let y := latitudeRowSite a (j + 1) hi
  let X := latitudeFrame ell longitude x
  let Y := latitudeFrame ell longitude y
  let θ := arctan ((Y 2 - X 2) / (Y 1 - X 1))
  have diff : 0 < Y 1 - X 1 := bounds.1
  have tilt : |θ| ≤ 0.016 * latitudeRadius a := bounds.2
  have same := latitudeSecant_support_eq ell longitude x y (sub_ne_zero.mp diff.ne')
  change inner ℝ (latitudeSite (ell - θ) longitude) x =
    inner ℝ (latitudeSite (ell - θ) longitude) y at same
  refine ⟨θ, tilt, same, ?_, ?_, ?_⟩
  · intro i row k
    exact latitude_strip_support_all_rows positive small strip lo hi tilt nearest₀ nearest₁ same row k
  · have pole := latitude_strip_support_excludes_poles positive small strip (longitude := longitude) tilt close₀ 0 (Or.inl rfl)
    rwa [longitude₀] at pole
  · have pole := latitude_strip_support_excludes_poles positive small strip (longitude := longitude) tilt close₀ π (Or.inr rfl)
    rwa [longitude₀] at pole

end Unfoldings.FewestNets
