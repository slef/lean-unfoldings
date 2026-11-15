module

public import Unfoldings.Geometry.TwoBankGapLocalSide
public import Unfoldings.Geometry.BankInitialSegment

/-! The actual second bank uses the opposite side of its own source-centered frame. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)

/-- Exact inverse coordinates of the actual bank frame, including its source. -/
theorem bankFrame_symm_apply (z : ℂ) :
    (R.bankFrame first_outward first_nonzero).symm z =
      star (R.radialCoefficient first_outward first_nonzero ‖z - R.start‖₊) *
        (z - R.start) := by
  change star (R.radialCoefficient first_outward first_nonzero ‖-R.start + z‖₊) *
    (-R.start + z) = _
  rw [neg_add_eq_sub]

/-- The second side test is precisely the negative imaginary coordinate in that bank's frame. -/
theorem twoBankSecondSide_eq_neg_im (common : Q.start = R.start) (z : ℂ) :
    R.twoBankSecondSide Q first_outward first_nonzero last_outward last_nonzero z =
      -((Q.bankFrame last_outward last_nonzero).symm z).im := by
  by_cases source : z = R.start
  · subst z
    simp [twoBankSecondSide, variableSectorSecondSide, bankFrame_symm_apply, common]
  · let r : ℝ≥0 := ‖z - R.start‖₊
    have positive : 0 < r := nnnorm_pos.mpr (sub_ne_zero.mpr source)
    have radius : ‖(R.bankFrame first_outward first_nonzero).symm z‖₊ = r :=
      NNReal.eq (R.norm_bankFrame_symm first_outward first_nonzero z)
    let ratio := R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r
    have unit : ‖ratio‖ = 1 :=
      R.norm_twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r positive
    have ratio_nonzero : ratio ≠ 0 := norm_ne_zero_iff.mp (unit ▸ one_ne_zero)
    have cos_angle : Real.cos
        (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r) = ratio.re := by
      rw [twoBankAngle, ite_eq_right positive.ne', Complex.cos_arg ratio_nonzero, unit, div_one]
    have sin_angle : Real.sin
        (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r) = ratio.im := by
      rw [twoBankAngle, ite_eq_right positive.ne', Complex.sin_arg, unit, div_one]
    have nonzero : R.radialCoefficient first_outward first_nonzero r ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [R.radialCoefficient_unit first_outward first_nonzero r positive]
      exact one_ne_zero
    have coordinates : star ratio * (R.bankFrame first_outward first_nonzero).symm z =
        (Q.bankFrame last_outward last_nonzero).symm z := by
      rw [R.bankFrame_symm_apply, Q.bankFrame_symm_apply, common]
      change star (Q.radialCoefficient last_outward last_nonzero r /
        R.radialCoefficient first_outward first_nonzero r) *
          (star (R.radialCoefficient first_outward first_nonzero r) * (z - R.start)) = _
      rw [star_div₀, ← mul_assoc, div_mul_cancel₀ _ (star_ne_zero.mpr nonzero)]
    rw [twoBankSecondSide, variableSectorSecondSide, radius, sin_angle, cos_angle,
      ← coordinates]
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- The actual gap lies locally to the right of its second oriented polygonal bank. -/
theorem eventually_mem_twoBankGap_iff_opposite_side
    (positive_phase : ∀ r : ℝ≥0, 0 < r →
      0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)
    (common : Q.start = R.start) (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ z in 𝓝 (Q.radialPoint last_outward last_nonzero r),
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        ((Q.bankFrame last_outward last_nonzero).symm z).im ≤ 0 := by
  filter_upwards [R.eventually_mem_twoBankGap_iff_second_side Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r positive] with z hz
  simpa only [R.twoBankSecondSide_eq_neg_im Q first_outward first_nonzero last_outward
    last_nonzero common z, neg_nonneg] using hz

end Unfoldings.PolygonalRay
