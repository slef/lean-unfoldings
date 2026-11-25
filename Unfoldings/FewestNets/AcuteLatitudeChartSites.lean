module

public import Unfoldings.FewestNets.AcuteLatitudeTriangleShape
public import Unfoldings.FewestNets.LatitudeSweepEdges

/-! The shape estimates apply to each actual vertex chosen by the midpoint sweep. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real InnerProductGeometry

/-- The midpoint colatitude from which an annular triangle is projected. -/
def chartColatitude (a : ℝ) (j : ℕ) : ℝ := colatitude a j + rowStep a / 2

theorem lower_colatitude_eq (a : ℝ) (j : ℕ) :
    colatitude a j = chartColatitude a j - rowStep a / 2 := by
  unfold chartColatitude
  ring

theorem upper_colatitude_eq (a : ℝ) (j : ℕ) :
    colatitude a (j + 1) = chartColatitude a j + rowStep a / 2 := by
  rw [colatitude_succ]
  unfold chartColatitude
  ring

/-- The horizontal east coordinate of a site displaced by `w` in longitude. -/
def chartX (ell row w : ℝ) : ℝ := sin row * sin w / latitudeDenominator ell row w

/-- The south coordinate of a site displaced by `w` in longitude. -/
def chartY (ell row w : ℝ) : ℝ :=
  (sin (row - ell) - cos ell * sin row * (1 - cos w)) / latitudeDenominator ell row w

theorem chartX_neg (ell row w : ℝ) : chartX ell row (-w) = -chartX ell row w := by
  simp [chartX, latitudeDenominator, sin_neg, cos_neg, mul_neg, neg_div]

theorem chartY_neg (ell row w : ℝ) : chartY ell row (-w) = chartY ell row w := by
  simp [chartY, latitudeDenominator, cos_neg]

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small in
/-- At a half-step or shorter longitude displacement, the actual row site lies
in the chart rectangle and has the required altitude correction and angular radius. -/
theorem chartSite_bounds {j k : ℕ} (strip : j < stripCount a) (which : k = j ∨ k = j + 1)
    (longitude w : ℝ) (offset : |w| ≤ longitudeStep a k / 2) :
    let ell := chartColatitude a j
    let row := colatitude a k
    let Z := latitudeDenominator ell row w
    0.991 < Z ∧ Z ≤ 1 ∧ |chartX ell row w| < 0.505 * spacing a ∧
      |chartY ell row w - sin (row - ell) / Z| ≤ 0.489 * spacing a ^ 2 / radius a ∧
      |chartY ell row w| < 0.547 * radius a ∧
      angle (latitudeSite ell longitude) (latitudeSite row (longitude + w)) < 0.568 * radius a := by
  let ell := chartColatitude a j
  let row := colatitude a k
  have valid : k ≤ stripCount a := by rcases which with rfl | rfl <;> omega
  have step := rowStep_pos positive small
  have delta : |row - ell| ≤ radius a / 2 := by
    rcases which with same | same
    · subst k
      change |colatitude a j - chartColatitude a j| ≤ _
      conv_lhs => rw [lower_colatitude_eq a j]
      rw [show chartColatitude a j - rowStep a / 2 - chartColatitude a j =
        -(rowStep a / 2) by ring, abs_neg, abs_of_nonneg (by positivity)]
      linarith only [(rowStep_bounds positive small).2]
    · subst k
      change |colatitude a (j + 1) - chartColatitude a j| ≤ _
      conv_lhs => rw [upper_colatitude_eq a j]
      rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
      linarith only [(rowStep_bounds positive small).2]
  have north := colatitude_mem positive small strip.le
  have south := colatitude_mem positive small (Nat.succ_le_of_lt strip)
  have middle : ell ∈ Set.Icc 0 π := by
    change 0 ≤ chartColatitude a j ∧ chartColatitude a j ≤ π
    have low := lower_colatitude_eq a j
    have high := upper_colatitude_eq a j
    exact ⟨by linarith only [north.1, step, low], by linarith only [south.2, step, high]⟩
  have sine : (0.999 / 3.864) * radius a < sin row := by
    rw [radius_eq_polarRadius]
    have h := row_sine_lower positive small valid
    change 0.999 * polarRadius a < sin row at h
    linarith only [h]
  obtain ⟨mid_weight, row_weight⟩ := weighted_longitude_bounds positive small valid
    (abs_sub_comm row ell ▸ delta) offset
  have mid_sine := sin_nonneg_of_nonneg_of_le_pi middle.1 middle.2
  obtain ⟨z_lower, z_upper, x, corr, y⟩ := vertex_coordinate_bounds
    (radius_pos positive) (radius_lt small) (spacing_pos positive) (spacing_lt positive small)
    delta mid_sine sine mid_weight.le row_weight
  have tilt := vertex_tilt_lt (longitude := longitude)
    (radius_pos positive) (radius_lt small) (spacing_pos positive) (spacing_lt positive small)
    delta mid_sine sine mid_weight.le row_weight
  exact ⟨z_lower, z_upper, x, corr, y, tilt⟩

include positive small in
/-- The actual two-row separation has the signed chart height required to
straighten the triangles with their original orientation. -/
theorem chartSite_height_bounds {j : ℕ} (strip : j < stripCount a) (w₀ w₁ : ℝ)
    (offset₀ : |w₀| ≤ longitudeStep a j / 2) (offset₁ : |w₁| ≤ longitudeStep a (j + 1) / 2) :
    let ell := chartColatitude a j
    let height := chartY ell (colatitude a (j + 1)) w₁ - chartY ell (colatitude a j) w₀
    0.883 * radius a < height ∧ height < 1.052 * radius a := by
  let ell := chartColatitude a j
  let t := rowStep a / 2
  have north : colatitude a j = ell - t := lower_colatitude_eq a j
  have south : colatitude a (j + 1) = ell + t := upper_colatitude_eq a j
  obtain ⟨Z₀, Z₀_le, _, error₀, _, _⟩ := chartSite_bounds positive small strip (Or.inl rfl) 0 w₀ offset₀
  obtain ⟨Z₁, Z₁_le, _, error₁, _, _⟩ := chartSite_bounds positive small strip (Or.inr rfl) 0 w₁ offset₁
  change 0.991 < latitudeDenominator ell (colatitude a j) w₀ at Z₀
  change latitudeDenominator ell (colatitude a j) w₀ ≤ 1 at Z₀_le
  change 0.991 < latitudeDenominator ell (colatitude a (j + 1)) w₁ at Z₁
  change latitudeDenominator ell (colatitude a (j + 1)) w₁ ≤ 1 at Z₁_le
  have y_identity (row w : ℝ) :
      chartY ell row w = sin (row - ell) / latitudeDenominator ell row w +
        -(cos ell * sin row * (1 - cos w)) / latitudeDenominator ell row w := by
    rw [chartY, sub_eq_add_neg, add_div]
  have north_pos := sin_pos_of_mem_Ioo (colatitude_mem positive small strip.le)
  have south_pos := sin_pos_of_mem_Ioo (colatitude_mem positive small (Nat.succ_le_of_lt strip))
  have step_lower : 0.928 * (radius a / 2) < t := by
    change _ < rowStep a / 2
    linarith only [(rowStep_bounds positive small).1]
  have step_upper : t ≤ radius a / 2 := by
    change rowStep a / 2 ≤ _
    linarith only [(rowStep_bounds positive small).2]
  change |chartY ell (colatitude a j) w₀ -
    sin (colatitude a j - ell) / latitudeDenominator ell (colatitude a j) w₀| ≤ _ at error₀
  change |chartY ell (colatitude a (j + 1)) w₁ -
    sin (colatitude a (j + 1) - ell) / latitudeDenominator ell (colatitude a (j + 1)) w₁| ≤ _ at error₁
  rw [y_identity, add_sub_cancel_left] at error₀ error₁
  rw [north] at Z₀ Z₀_le error₀ north_pos
  rw [south] at Z₁ Z₁_le error₁ south_pos
  have bound := chart_height_bounds (ell := ell) (w₀ := w₀) (w₁ := w₁)
    (radius_pos positive) (radius_lt small)
    (spacing_pos positive) (spacing_lt positive small) step_lower step_upper
    north_pos.le south_pos.le Z₀ Z₀_le Z₁ Z₁_le error₀ error₁
  dsimp only
  change 0.883 * radius a < chartY ell (colatitude a (j + 1)) w₁ -
    chartY ell (colatitude a j) w₀ ∧
    chartY ell (colatitude a (j + 1)) w₁ - chartY ell (colatitude a j) w₀ < 1.052 * radius a
  simp only [y_identity, north, south, add_sub_cancel_left,
    show ell - t - ell = -t by ring, sin_neg]
  exact bound

end Unfoldings.FewestNets.AcuteLatitudeGrid
