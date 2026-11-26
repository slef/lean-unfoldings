module

public import Unfoldings.FewestNets.AcuteLatitudeCountScalars

/-! The final arithmetic of the latitude count with the revised band and polar weights. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real

/-- After the band heights cancel in the summed apex charge, the revised
latitude estimates give the paper's strict coefficient. -/
theorem acute_latitude_revised_count_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    2 + 15.32 / a ^ 2 + (1.215 * 0.677) / a ^ 4 *
      (1.225 * 100 / 0.51 + 2 * 117 * a / 0.905 +
        (0.03 * 29 + 1.545 * 6.3) * a / 0.51) < 323 / a ^ 4 := by
  have upper : a ≤ 11 / 21 := by linarith only [small, Real.pi_lt_d6]
  have fourth : 0 < a ^ 4 := pow_pos positive _
  have h₂ : a ^ 2 ≤ (11 / 21 : ℝ) ^ 2 := pow_le_pow_left₀ positive.le upper _
  have h₄ : a ^ 4 ≤ (11 / 21 : ℝ) ^ 4 := pow_le_pow_left₀ positive.le upper _
  apply (lt_div_iff₀ fourth).mpr
  calc
    _ = 2 * a ^ 4 + 15.32 * a ^ 2 + 1.215 * 0.677 *
        (1.225 * 100 / 0.51 + 2 * 117 * a / 0.905 +
          (0.03 * 29 + 1.545 * 6.3) * a / 0.51) := by
      field_simp
    _ ≤ 2 * (11 / 21 : ℝ) ^ 4 + 15.32 * (11 / 21 : ℝ) ^ 2 + 1.215 * 0.677 *
        (1.225 * 100 / 0.51 + 2 * 117 * (11 / 21 : ℝ) / 0.905 +
          (0.03 * 29 + 1.545 * 6.3) * (11 / 21 : ℝ) / 0.51) := by
      gcongr
    _ < 323 := by norm_num

end Unfoldings.FewestNets
