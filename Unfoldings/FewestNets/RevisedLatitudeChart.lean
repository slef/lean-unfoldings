module

public import Unfoldings.FewestNets.RevisedLatitudeHeightBounds
public import Unfoldings.FewestNets.LatitudeRingsOrientation

/-! The taller bands give admissible rows and signed meridional chart coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Module

/-- The revised samples, with no geometry hidden in the indexing type. -/
abbrev rings (a : ℝ) : LatitudeRings where
  stripCount := stripCount a
  colatitude := colatitude a
  rowSize := rowSize a

variable {a : ℝ}

theorem rings_admissible (positive : 0 < a) (small : a ≤ π / 6) : (rings a).Admissible where
  validColatitude := fun _ valid => colatitude_mem positive small valid
  rowSize_ge_three := fun _ valid => rowSize_ge_three positive small valid
  southern := by
    change cos (colatitude a (stripCount a)) < 0
    rw [colatitude_last positive small, cos_pi_sub, neg_lt_zero]
    apply cos_pos_of_mem_Ioo
    exact ⟨by linarith only [AcuteLatitudeGrid.polarRadius_pos positive, pi_pos],
      by linarith only [AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2]⟩

/-- The center of the chart lies halfway between the two actual rows. -/
def stripMidpoint (a : ℝ) (j : ℕ) : ℝ := colatitude a j + rowStep a / 2

theorem colatitude_sub_midpoint (a : ℝ) (j : ℕ) :
    colatitude a j - stripMidpoint a j = -(rowStep a / 2) ∧
      colatitude a (j + 1) - stripMidpoint a j = rowStep a / 2 := by
  unfold stripMidpoint
  rw [colatitude_succ]
  constructor <;> ring

theorem stripMidpoint_mem (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < stripCount a) : stripMidpoint a j ∈ Set.Ioo 0 π := by
  have low := colatitude_mem positive small valid.le
  have high := colatitude_mem positive small (Nat.succ_le_of_lt valid)
  rw [colatitude_succ] at high
  have step := rowStep_pos positive small
  change 0 < colatitude a j + rowStep a / 2 ∧ colatitude a j + rowStep a / 2 < π
  exact ⟨by linarith only [low.1, step], by linarith only [high.2, step]⟩

/-- The exact projected site relative to the strip and base midpoint. -/
def slopeSite (a : ℝ) (strip row : ℕ) (w : ℝ) : Plane :=
  let m := stripMidpoint a strip
  let l := colatitude a row
  let z := latitudeDenominator m l w
  WithLp.toLp 2 ![sin l * sin w / z, (sin (l - m) - cos m * sin l * (1 - cos w)) / z]

/-- Whether the row has the refined polar spacing. -/
def isPolarRow (a : ℝ) (j : ℕ) : Bool := decide (j = 0 ∨ j = stripCount a)

/-- Every attached row has its own sharp east bound and the common positive denominator. -/
theorem slopeSite_bounds (positive : 0 < a) (small : a ≤ π / 6)
    {strip row : ℕ} (valid : strip < stripCount a) (on_row : row = strip ∨ row = strip + 1)
    {w : ℝ} (near : |w| ≤ longitudeStep a row / 2) :
    let Z := latitudeDenominator (stripMidpoint a strip) (colatitude a row) w
    let p := slopeSite a strip row w
    let polar := isPolarRow a row
    0.9612 < Z ∧ Z ≤ cos (colatitude a row - stripMidpoint a strip) ∧
      |p 0| < widthFactor polar * spacing a / (2 * 0.9612) ∧
      |p 1 - sin (colatitude a row - stripMidpoint a strip) / Z| ≤
        ordinateErrorFactor polar * spacing a ^ 2 / radius a := by
  have row_valid : row ≤ stripCount a := by rcases on_row with rfl | rfl <;> omega
  have abs_sub : |colatitude a row - stripMidpoint a strip| ≤ radius a / 2 := by
    have dp := rowStep_pos positive small
    have upper := (rowStep_bounds positive small).2
    rcases on_row with eq | eq
    · rw [eq, (colatitude_sub_midpoint a strip).1, abs_neg, abs_of_pos (half_pos dp)]
      exact div_le_div_of_nonneg_right upper (by norm_num)
    · rw [eq, (colatitude_sub_midpoint a strip).2, abs_of_pos (half_pos dp)]
      exact div_le_div_of_nonneg_right upper (by norm_num)
  have circumference :
      radius a ≤ inverseSineFactor (isPolarRow a row) * sin (colatitude a row) := by
    by_cases polar : row = 0 ∨ row = stripCount a
    · simpa only [isPolarRow, decide_eq_true polar, inverseSineFactor, ite_true] using
        (polar_sine_bound positive small polar).le
    · have not_polar := not_or.mp polar
      have low : 0 < row := Nat.pos_of_ne_zero not_polar.1
      have high : row < stripCount a := lt_of_le_of_ne row_valid not_polar.2
      simpa only [isPolarRow, decide_eq_false_iff_not.mpr polar, inverseSineFactor,
        Bool.false_eq_true, ite_false] using (interior_sine_bound positive small low high).le
  have weighted := weighted_longitude_bound positive small row_valid near
  have width : localSpacing a row = widthFactor (isPolarRow a row) * spacing a := by
    by_cases polar : row = 0 ∨ row = stripCount a <;>
      simp [localSpacing, widthFactor, isPolarRow, polar]
  rw [width] at weighted
  exact vertex_coordinates (isPolarRow a row) (radius_pos positive) (radius_lt small)
    (spacing_pos positive) (spacing_lt positive small) abs_sub
    (sin_pos_of_mem_Ioo (stripMidpoint_mem positive small valid)).le
    (sin_pos_of_mem_Ioo (colatitude_mem positive small row_valid)) circumference weighted

end Unfoldings.FewestNets.RevisedLatitudeGrid
