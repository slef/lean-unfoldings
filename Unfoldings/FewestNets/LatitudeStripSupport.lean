module

public import Unfoldings.FewestNets.LatitudeChordSupport
public import Unfoldings.FewestNets.LatitudeTriangleShape

/-! The other rings and both poles are separated from an annular triangle's meridional support. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- Midpoint colatitude used by the chart on an annular strip. -/
def latitudeStripMid (a : ℝ) (j : ℕ) : ℝ :=
  latitudeColatitude a j + latitudeRowStep a / 2

theorem latitudeStripMid_sub_lower (a : ℝ) (j : ℕ) :
    latitudeStripMid a j - latitudeColatitude a j = latitudeRowStep a / 2 := by
  unfold latitudeStripMid
  ring

theorem latitudeStripMid_sub_upper (a : ℝ) (j : ℕ) :
    latitudeColatitude a (j + 1) - latitudeStripMid a j = latitudeRowStep a / 2 := by
  simp only [latitudeStripMid, latitudeColatitude, Nat.cast_add, Nat.cast_one]
  ring

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small in
theorem latitudeStripMid_bounds {j : ℕ} (strip : j < latitudeStripCount a) :
    0.9815 * latitudeRadius a < latitudeStripMid a j ∧
      latitudeStripMid a j < π - 0.9815 * latitudeRadius a := by
  have step := (latitudeRowStep_bounds positive small).1
  have below := (latitudeColatitude_bounds positive small strip.le).1
  have above := (latitudeColatitude_bounds positive small (Nat.succ_le_of_lt strip)).2
  exact ⟨by linarith only [below, step, latitudeStripMid_sub_lower a j],
    by linarith only [above, step, latitudeStripMid_sub_upper a j]⟩

include positive small in
theorem latitude_other_row_far (j i : ℕ) (different₀ : i ≠ j) (different₁ : i ≠ j + 1) :
    0.956 * latitudeRadius a ≤ |latitudeColatitude a i - latitudeStripMid a j| := by
  have step := (latitudeRowStep_bounds positive small).1
  have r_pos := latitudeRadius_pos positive
  have d_pos : 0 < latitudeRowStep a := (mul_pos (by norm_num) r_pos).trans step
  have difference : latitudeColatitude a i - latitudeStripMid a j =
      ((i : ℝ) - (j : ℝ) - 1 / 2) * latitudeRowStep a := by
    unfold latitudeStripMid latitudeColatitude
    ring
  rw [difference, abs_mul, abs_of_pos d_pos]
  have coefficient : (3 / 2 : ℝ) ≤ |(i : ℝ) - (j : ℝ) - 1 / 2| := by
    rcases lt_or_ge i j with before | after
    · have order : (i : ℝ) + 1 ≤ j := by exact_mod_cast before
      have bound : (i : ℝ) - j - 1 / 2 ≤ -(3 / 2 : ℝ) := by linarith only [order]
      exact (le_neg_of_le_neg bound).trans (neg_le_abs _)
    · have after_two : j + 2 ≤ i := by omega
      have order : (j : ℝ) + 2 ≤ i := by exact_mod_cast after_two
      exact (by linarith only [order] : (3 / 2 : ℝ) ≤ (i : ℝ) - j - 1 / 2).trans
        (le_abs_self _)
  exact (show 0.956 * latitudeRadius a ≤ (3 / 2 : ℝ) * latitudeRowStep a by
    linarith only [step, r_pos]).trans (mul_le_mul_of_nonneg_right coefficient d_pos.le)

include positive small in
/-- A nearby row vertex strictly dominates every far colatitude in the tilted support direction. -/
theorem latitude_strip_support_excludes_far {j : ℕ} (strip : j < latitudeStripCount a)
    {far : ℝ} (far_range : far ∈ Set.Icc 0 π)
    (far_row : 0.956 * latitudeRadius a ≤ |far - latitudeStripMid a j|)
    {longitude w θ : ℝ} (tilt : |θ| ≤ 0.016 * latitudeRadius a)
    (near : ℕ) (near_row : near = j ∨ near = j + 1)
    (closest : |w| ≤ latitudeLongitudeStep a near / 2)
    (z : ℝ) :
    inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude)
      (latitudeSite far (longitude + z)) <
    inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude)
      (latitudeSite (latitudeColatitude a near) (longitude + w)) := by
  have bounds := latitudeStripMid_bounds positive small strip
  have r_pos := latitudeRadius_pos positive
  have chart_range : latitudeStripMid a j - θ ∈ Set.Icc 0 π :=
    ⟨by linarith only [bounds.1, (abs_le.mp tilt).2, r_pos],
      by linarith only [bounds.2, (abs_le.mp tilt).1, r_pos]⟩
  have near_valid : near ≤ latitudeStripCount a := by
    rcases near_row with rfl | rfl
    · exact strip.le
    · exact Nat.succ_le_of_lt strip
  have step := latitudeRowStep_bounds positive small
  have d_pos : 0 < latitudeRowStep a := by linarith only [step.1, r_pos]
  have close : |latitudeColatitude a near - latitudeStripMid a j| ≤ latitudeRadius a / 2 := by
    rcases near_row with rfl | rfl
    · rw [abs_sub_comm, latitudeStripMid_sub_lower, abs_of_nonneg (by positivity)]
      linarith only [step.2]
    · rw [latitudeStripMid_sub_upper, abs_of_nonneg (by positivity)]
      linarith only [step.2]
  have latitude_sine := latitudeColatitude_bounds positive small near_valid
  have near_sine := latitude_sin_lower positive small latitude_sine.1 latitude_sine.2
  obtain ⟨mid_bound, row_bound⟩ := latitude_weighted_longitude_bounds positive small near_valid
    (by rwa [abs_sub_comm]) closest
  exact latitudeSite_far_support_lt r_pos (by unfold latitudeSpacing; positivity)
    (latitudeSpacing_lt positive small) tilt chart_range close
    far_row far_range
    near_sine row_bound mid_bound


/-- The actual unit site at a numbered row longitude, with periodic indices. -/
def latitudeRowSite (a : ℝ) (j k : ℕ) : Space :=
  latitudeSite (latitudeColatitude a j) (rowLongitude (latitudeRowSize a j) k)

include positive small in
/-- Two nearest sites of equal support on the adjacent rows support all
annular row sites at the same level. -/
theorem latitude_strip_support_all_rows {j : ℕ} (strip : j < latitudeStripCount a)
    (lo hi : ℕ) {longitude θ : ℝ} (tilt : |θ| ≤ 0.016 * latitudeRadius a)
    (near₀ : |longitude - rowLongitude (latitudeRowSize a j) lo| ≤ π / latitudeRowSize a j)
    (near₁ : |longitude - rowLongitude (latitudeRowSize a (j + 1)) hi| ≤
      π / latitudeRowSize a (j + 1))
    (equal : inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude) (latitudeRowSite a j lo) =
      inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude) (latitudeRowSite a (j + 1) hi))
    {i : ℕ} (row : i ≤ latitudeStripCount a) (k : ℕ) :
    inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude) (latitudeRowSite a i k) ≤
      inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude) (latitudeRowSite a j lo) := by
  let ell := latitudeStripMid a j - θ
  let w := rowLongitude (latitudeRowSize a j) lo - longitude
  let z := rowLongitude (latitudeRowSize a i) k - longitude
  have bound := latitudeStripMid_bounds positive small strip
  have r_pos := latitudeRadius_pos positive
  have ell_range : ell ∈ Set.Icc 0 π :=
    ⟨by dsimp only [ell]; linarith only [bound.1, (abs_le.mp tilt).2, r_pos],
      by dsimp only [ell]; linarith only [bound.2, (abs_le.mp tilt).1, r_pos]⟩
  have row_range : latitudeColatitude a i ∈ Set.Icc 0 π := by
    obtain ⟨low, high⟩ := latitudeColatitude_bounds positive small row
    exact ⟨by linarith only [low, r_pos], by linarith only [high, r_pos]⟩
  by_cases lower : i = j
  · subst i
    exact latitudeNearest_support_ge (latitude_row_size_pos positive small row)
      ell_range row_range near₀ k
  by_cases upper : i = j + 1
  · subst i
    exact (latitudeNearest_support_ge (latitude_row_size_pos positive small row)
      ell_range row_range near₁ k).trans_eq equal.symm
  have near_w : |w| ≤ latitudeLongitudeStep a j / 2 := by
    dsimp only [w, latitudeLongitudeStep]
    rw [abs_sub_comm, show (2 * π / (latitudeRowSize a j : ℝ)) / 2 =
      π / (latitudeRowSize a j : ℝ) by ring]
    exact near₀
  have far := latitude_strip_support_excludes_far positive small strip row_range (longitude := longitude)
    (latitude_other_row_far positive small j i lower upper) tilt j (Or.inl rfl) near_w z
  have far_longitude : longitude + z = rowLongitude (latitudeRowSize a i) k := by
    dsimp only [z]
    ring
  have near_longitude : longitude + w = rowLongitude (latitudeRowSize a j) lo := by
    dsimp only [w]
    ring
  rw [far_longitude, near_longitude] at far
  exact far.le

include positive small in
/-- The two poles are strictly outside the supporting plane of an interior strip. -/
theorem latitude_strip_support_excludes_poles {j : ℕ} (strip : j < latitudeStripCount a)
    {longitude w θ : ℝ} (tilt : |θ| ≤ 0.016 * latitudeRadius a)
    (closest : |w| ≤ latitudeLongitudeStep a j / 2)
    (pole : ℝ) (polar : pole = 0 ∨ pole = π) :
    inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude) (latitudeSite pole longitude) <
      inner ℝ (latitudeSite (latitudeStripMid a j - θ) longitude)
        (latitudeSite (latitudeColatitude a j) (longitude + w)) := by
  have r_pos := latitudeRadius_pos positive
  have mid := latitudeStripMid_bounds positive small strip
  have pole_range : pole ∈ Set.Icc 0 π := by rcases polar with rfl | rfl <;> simp [pi_pos.le]
  have away : 0.956 * latitudeRadius a ≤ |pole - latitudeStripMid a j| := by
    rcases polar with rfl | rfl
    · exact (show 0.956 * latitudeRadius a ≤ -(0 - latitudeStripMid a j) by
        linarith only [mid.1, r_pos]).trans (neg_le_abs _)
    · exact (show 0.956 * latitudeRadius a ≤ π - latitudeStripMid a j by
        linarith only [mid.2, r_pos]).trans (le_abs_self _)
  simpa only [add_zero] using latitude_strip_support_excludes_far positive small strip pole_range
    away tilt j (Or.inl rfl) closest 0

end Unfoldings.FewestNets
