module

public import Unfoldings.Geometry.TwoBankGap
public import Unfoldings.Geometry.VariableSectorLocalSide

/-! Actual one-sided geometric neighborhoods of both frontier banks of a Jordan gap. -/

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

include positive_phase in
theorem sin_twoBankAngle_pos (r : ℝ≥0) :
    0 < Real.sin (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r) := by
  by_cases zero : r = 0
  · simp [twoBankAngle, zero]
  · have positive : 0 < r := lt_of_le_of_ne zero_le (Ne.symm zero)
    rw [twoBankAngle, ite_eq_right zero, Complex.sin_arg,
      R.norm_twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r positive,
      div_one]
    exact positive_phase r positive

/-- The actual radius-dependent sector test, in the first bank's ambient coordinates. -/
theorem mem_twoBankGap_iff_variable (z : ℂ) :
    z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
      (R.bankFrame first_outward first_nonzero).symm z ∈
        variableSectorGap (Real.pi / 2) (by simp)
          (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero)
          (R.sin_twoBankAngle_ne_zero Q first_outward first_nonzero last_outward last_nonzero
            positive_phase)
          (R.continuousOn_twoBankAngle Q first_outward first_nonzero last_outward last_nonzero
            positive_phase) := by
  let H := R.bankFrame first_outward first_nonzero
  have image : R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
      H '' variableSectorGap (Real.pi / 2) (by simp)
        (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero)
        (R.sin_twoBankAngle_ne_zero Q first_outward first_nonzero last_outward last_nonzero
          positive_phase)
        (R.continuousOn_twoBankAngle Q first_outward first_nonzero last_outward last_nonzero
          positive_phase) := by
    rw [twoBankGap, variableSectorGap, Set.image_image]
    rfl
  rw [image]
  constructor
  · rintro ⟨w, member, equal⟩
    rw [← equal, H.symm_apply_apply]
    exact member
  · intro member
    exact ⟨H.symm z, member, H.apply_symm_apply z⟩

/-- Away from the source, the actual gap occupies precisely the first bank's positive side. -/
theorem eventually_mem_twoBankGap_iff_first_side (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ z in 𝓝 (R.radialPoint first_outward first_nonzero r),
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        0 ≤ ((R.bankFrame first_outward first_nonzero).symm z).im := by
  let H := R.bankFrame first_outward first_nonzero
  have unframe : H.symm (R.radialPoint first_outward first_nonzero r) = (r : ℂ) := by
    rw [← R.bankFrame_real first_outward first_nonzero r]
    exact H.symm_apply_apply _
  have near := eventually_mem_variableSectorGap_iff_first_side
    (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero)
    (R.continuousOn_twoBankAngle Q first_outward first_nonzero last_outward last_nonzero
      positive_phase) (Real.pi / 2) (by simp)
    (R.sin_twoBankAngle_ne_zero Q first_outward first_nonzero last_outward last_nonzero
      positive_phase)
    r positive
    (R.sin_twoBankAngle_pos Q first_outward first_nonzero last_outward last_nonzero
      positive_phase r)
  have tends : Tendsto H.symm (𝓝 (R.radialPoint first_outward first_nonzero r)) (𝓝 (r : ℂ)) := by
    rw [← unframe]
    exact H.symm.continuous.continuousAt.tendsto
  filter_upwards [tends.eventually near] with z hz
  rw [R.mem_twoBankGap_iff_variable Q first_outward first_nonzero last_outward last_nonzero
    positive_phase]
  exact hz

/-- The upper signed side is computed in the same actual source-centered bank frame. -/
def twoBankSecondSide (z : ℂ) : ℝ :=
  variableSectorSecondSide
    (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero)
    ((R.bankFrame first_outward first_nonzero).symm z)

/-- The second bank has the complementary one-sided test, on the actual geometric region. -/
theorem eventually_mem_twoBankGap_iff_second_side (common : Q.start = R.start)
    (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ z in 𝓝 (Q.radialPoint last_outward last_nonzero r),
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        0 ≤ R.twoBankSecondSide Q first_outward first_nonzero last_outward last_nonzero z := by
  let H := R.bankFrame first_outward first_nonzero
  let width := R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero
  have fixed : H (polarRay (width r) * (r : ℂ)) = Q.radialPoint last_outward last_nonzero r := by
    have actual := R.twoBankFrame_upper Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common r
    change H (variableSectorHomeomorph _ _ _ _ _
      (polarRay (Real.pi / 2) * (r : ℂ))) = _ at actual
    rwa [variableSectorHomeomorph_upper] at actual
  have unframe : H.symm (Q.radialPoint last_outward last_nonzero r) =
      polarRay (width r) * (r : ℂ) := by
    rw [← fixed, H.symm_apply_apply]
  have radius : ‖H.symm (Q.radialPoint last_outward last_nonzero r)‖₊ = r := by
    rw [unframe]
    apply NNReal.eq
    simp only [coe_nnnorm, norm_mul, norm_polarRay, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
  have sin_pos := R.sin_twoBankAngle_pos Q first_outward first_nonzero last_outward last_nonzero
    positive_phase r
  have imaginary : 0 < (H.symm (Q.radialPoint last_outward last_nonzero r)).im := by
    rw [unframe]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      polarRay_im]
    exact mul_pos sin_pos (show (0 : ℝ) < r from positive)
  have near := eventually_mem_variableSectorGap_iff_second_side width
    (R.continuousOn_twoBankAngle Q first_outward first_nonzero last_outward last_nonzero
      positive_phase) (Real.pi / 2) (by simp)
    (R.sin_twoBankAngle_ne_zero Q first_outward first_nonzero last_outward last_nonzero
      positive_phase)
    (H.symm (Q.radialPoint last_outward last_nonzero r)) imaginary (by rwa [radius])
  filter_upwards [H.symm.continuous.continuousAt.tendsto.eventually near] with z hz
  rw [R.mem_twoBankGap_iff_variable Q first_outward first_nonzero last_outward last_nonzero
    positive_phase]
  exact hz

end Unfoldings.PolygonalRay
