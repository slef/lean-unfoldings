module

public import Unfoldings.Geometry.TwoBankGapInteriorSide
public import Unfoldings.Geometry.SourceRotation

/-! Small circular motions into the gap supply actual interior witnesses at both polygonal banks. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- Positive circular motion at fixed source radius enters the actual gap along its first bank. -/
theorem eventually_rotate_first_bank_mem_gap_interior (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      sourceRotation R.start θ (R.radialPoint first_outward first_nonzero r) ∈
        interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
          positive_phase) := by
  let p := R.radialPoint first_outward first_nonzero r
  let H := R.bankFrame first_outward first_nonzero
  have continuous_f : Continuous (fun θ => sourceRotation R.start θ p) := by
    simp only [sourceRotation_apply, complexRotation_apply, polarRay]
    fun_prop
  have at_zero : sourceRotation R.start 0 p = p := by
    simp [sourceRotation_apply, complexRotation_apply]
  have tends : Tendsto (fun θ => sourceRotation R.start θ p) (𝓝[>] 0) (𝓝 p) := by
    have at_center := continuous_f.tendsto (0 : ℝ)
    rw [at_zero] at at_center
    exact at_center.mono_left nhdsWithin_le_nhds
  have near := R.eventually_mem_interior_twoBankGap_iff_first_side Q first_outward first_nonzero
    last_outward last_nonzero positive_phase r positive
  have lower : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  have upper : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < Real.pi :=
    (show ∀ᶠ θ in 𝓝 (0 : ℝ), θ < Real.pi from Iio_mem_nhds Real.pi_pos).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [tends.eventually near, lower, upper] with θ local_match θpos θsmall
  apply local_match.mpr
  have coordinates : sourceRotation R.start θ p = H (polarRay θ * (r : ℂ)) := by
    simpa only [sourceRotation_apply] using
      (R.bankFrame_rotated_ray first_outward first_nonzero r θ).symm
  rw [coordinates]
  change 0 < (H.symm (H (polarRay θ * (r : ℂ)))).im
  rw [H.symm_apply_apply]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, polarRay_im]
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi θpos θsmall) (show (0 : ℝ) < r from positive)

/-- Negative circular motion enters along the second bank, in its opposite actual orientation. -/
theorem eventually_rotate_second_bank_mem_gap_interior (common : Q.start = R.start)
    (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      sourceRotation Q.start (-θ) (Q.radialPoint last_outward last_nonzero r) ∈
        interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
          positive_phase) := by
  let p := Q.radialPoint last_outward last_nonzero r
  let H := Q.bankFrame last_outward last_nonzero
  have continuous_f : Continuous (fun θ => sourceRotation Q.start (-θ) p) := by
    simp only [sourceRotation_apply, complexRotation_apply, polarRay]
    fun_prop
  have at_zero : sourceRotation Q.start (-(0 : ℝ)) p = p := by
    simp [sourceRotation_apply, complexRotation_apply]
  have tends : Tendsto (fun θ => sourceRotation Q.start (-θ) p) (𝓝[>] 0) (𝓝 p) := by
    have at_center := continuous_f.tendsto (0 : ℝ)
    rw [at_zero] at at_center
    exact at_center.mono_left nhdsWithin_le_nhds
  have near := R.eventually_mem_interior_twoBankGap_iff_second_side Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r positive
  have lower : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  have upper : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < Real.pi :=
    (show ∀ᶠ θ in 𝓝 (0 : ℝ), θ < Real.pi from Iio_mem_nhds Real.pi_pos).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [tends.eventually near, lower, upper] with θ local_match θpos θsmall
  apply local_match.mpr
  have coordinates : sourceRotation Q.start (-θ) p = H (polarRay (-θ) * (r : ℂ)) := by
    simpa only [sourceRotation_apply] using
      (Q.bankFrame_rotated_ray last_outward last_nonzero r (-θ)).symm
  rw [coordinates]
  change (H.symm (H (polarRay (-θ) * (r : ℂ)))).im < 0
  rw [H.symm_apply_apply]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    polarRay_im, Real.sin_neg, neg_mul, neg_lt_zero]
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi θpos θsmall) (show (0 : ℝ) < r from positive)

end Unfoldings.PolygonalRay
