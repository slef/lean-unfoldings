module

public import Unfoldings.Geometry.PolygonalRotationGap
public import Unfoldings.Geometry.VariableSectorBanks

/-! A continuous positive angular opening between two actual source-radial polygonal banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)

/-- The unit relative phase of the two actual contacts on a common positive-radius circle. -/
def twoBankRatio (r : ℝ≥0) : ℂ :=
  Q.radialCoefficient last_outward last_nonzero r /
    R.radialCoefficient first_outward first_nonzero r

/-- The radius-zero value is arbitrary and keeps the auxiliary linear change invertible there. -/
def twoBankAngle (r : ℝ≥0) : ℝ :=
  if r = 0 then Real.pi / 2 else
    Complex.arg (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r)

include first_outward first_nonzero last_outward last_nonzero in
theorem norm_twoBankRatio (r : ℝ≥0) (positive : 0 < r) :
    ‖R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r‖ = 1 := by
  rw [twoBankRatio, norm_div, R.radialCoefficient_unit first_outward first_nonzero r positive,
    Q.radialCoefficient_unit last_outward last_nonzero r positive, div_self one_ne_zero]

variable (positive_phase : ∀ r : ℝ≥0, 0 < r →
  0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

include positive_phase in
theorem sin_twoBankAngle_ne_zero (r : ℝ≥0) :
    Real.sin (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r) ≠ 0 := by
  by_cases zero : r = 0
  · simp [twoBankAngle, zero]
  · have positive : 0 < r := lt_of_le_of_ne zero_le (Ne.symm zero)
    rw [twoBankAngle, ite_eq_right zero, Complex.sin_arg,
      R.norm_twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r positive,
      div_one]
    exact (positive_phase r positive).ne'

include positive_phase in
theorem continuousOn_twoBankAngle :
    ContinuousOn (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero)
      (Set.Ioi 0) := by
  have ratio : ContinuousOn
      (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero) (Set.Ioi 0) := by
    apply Q.continuousOn_radialCoefficient last_outward last_nonzero |>.div
      (R.continuousOn_radialCoefficient first_outward first_nonzero)
    intro r positive
    apply norm_ne_zero_iff.mp
    rw [R.radialCoefficient_unit first_outward first_nonzero r positive]
    exact one_ne_zero
  have argument := Complex.continuousOn_arg.comp ratio (fun r positive =>
    Complex.mem_slitPlane_iff.mpr (Or.inr (positive_phase r positive).ne'))
  apply argument.congr
  intro r positive
  simp only [twoBankAngle, ite_eq_right (ne_of_gt (show (0 : ℝ≥0) < r from positive)),
    Function.comp_def]

include first_outward first_nonzero last_outward last_nonzero in
theorem polarRay_twoBankAngle (r : ℝ≥0) (positive : 0 < r) :
    polarRay (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r) =
      R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r := by
  rw [twoBankAngle, ite_eq_right positive.ne']
  have equal := Complex.norm_mul_exp_arg_mul_I
    (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r)
  rw [R.norm_twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r positive,
    Complex.ofReal_one, one_mul] at equal
  exact equal

end Unfoldings.PolygonalRay
