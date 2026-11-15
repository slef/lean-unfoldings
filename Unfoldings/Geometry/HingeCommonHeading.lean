module

public import Unfoldings.Geometry.BankCircleDirection
public import Unfoldings.Geometry.HingeHeadingComparison

/-! One continuous common-frame heading is monotone through active and inactive hinge openings. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (r : ℝ≥0) (radius_positive : 0 < r) (reference : Circle)

/-- Use one fixed reference direction for the whole sequence of actual banks. -/
def hingeCommonHeading (θ : Set.Icc 0 angle) : ℝ :=
  Complex.arg (R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ / reference)

include nonzero radial in
theorem continuous_hingeCommonHeading
    (halfplane : ∀ θ, 0 < ((R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ /
      reference : Circle) : ℂ).re) :
    Continuous (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference) := by
  have direction :=
    (R.continuous_hingeSweepDirection hinge nonzero angle radial r radius_positive).div'
    (continuous_const (y := reference))
  apply continuous_iff_continuousAt.mpr
  intro θ
  have slit : (((R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ /
      reference : Circle) : ℂ)) ∈ Complex.slitPlane := by
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (halfplane θ))
  exact (Complex.continuousAt_arg slit).comp
    (f := fun ψ => ((R.hingeSweepDirection hinge nonzero angle radial r radius_positive ψ /
      reference : Circle) : ℂ))
    (continuous_subtype_val.comp direction).continuousAt

@[simp] theorem exp_hingeCommonHeading (θ : Set.Icc 0 angle) :
    Circle.exp (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference θ) =
      R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ / reference := by
  unfold hingeCommonHeading
  simpa only [Circle.coe_div] using Circle.exp_arg
    (R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ / reference)

variable (outward : R.Outward) (suffix_outward : (R.suffix hinge).Outward)
  (positive : 0 < angle) (small : angle < Real.pi)

include suffix_outward positive small radial in
theorem strictMono_hingeCommonHeading_of_above
    (halfplane : ∀ θ, 0 < ((R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ /
      reference : Circle) : ℂ).re)
    (above : dist R.start (R.chain.vertex hinge) < (r : ℝ)) :
    StrictMono (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference) := by
  apply R.strictMono_hinge_heading hinge nonzero angle radial positive suffix_outward small
    ⟨r, above⟩ reference _
    (R.continuous_hingeCommonHeading hinge nonzero angle radial r radius_positive
      reference halfplane)
  intro θ
  rw [R.exp_hingeCommonHeading,
    R.hingeSweepDirection_eq_exterior hinge nonzero angle radial ⟨r, above⟩ radius_positive θ]

include outward suffix_outward positive small radial in
/-- The common-frame heading is constant on inactive circles and strictly increasing on active
ones. It is therefore monotone on every positive source circle. -/
theorem monotone_hingeCommonHeading
    (halfplane : ∀ θ, 0 < ((R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ /
      reference : Circle) : ℂ).re) :
    Monotone (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference) := by
  by_cases above : dist R.start (R.chain.vertex hinge) < (r : ℝ)
  · exact (R.strictMono_hingeCommonHeading_of_above hinge nonzero angle radial r radius_positive
      reference suffix_outward positive small halfplane above).monotone
  · intro θ ψ _
    unfold hingeCommonHeading
    rw [R.hingeSweepDirection_eq_of_below hinge nonzero angle radial outward r radius_positive
        (le_of_not_gt above) θ,
      R.hingeSweepDirection_eq_of_below hinge nonzero angle radial outward r radius_positive
        (le_of_not_gt above) ψ]

end Unfoldings.PolygonalRay
