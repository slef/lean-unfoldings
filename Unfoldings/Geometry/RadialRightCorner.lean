module

public import Unfoldings.Geometry.RadialCornerSector

/-! The original right bank occupies the complementary oriented corner. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Reverse the original bank to measure its occupied right-side corner. -/
def radialRightCornerWidth (radial incoming outgoing : ℂ) : ℝ :=
  radialLeftCornerWidth (-radial) (-outgoing) (-incoming)

/-- The reversed incoming edge is the initial oriented axis of the right corner. -/
def radialRightCornerFrame (radial incoming : ℂ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  radialLeftCornerFrame (-radial) (-incoming)

/-- The two actual side apertures sum to one full turn, with their original edge labels. -/
theorem radialCornerWidths_add (radial incoming outgoing : ℂ) :
    radialLeftCornerWidth radial incoming outgoing +
      radialRightCornerWidth radial incoming outgoing = 2 * Real.pi := by
  simp only [radialRightCornerWidth, radialLeftCornerWidth, neg_div_neg_eq]
  ring

/-- Both original right-side bank rays determine a genuine sector below a full turn. -/
theorem radialRightCornerWidth_bounds (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    0 < radialRightCornerWidth radial incoming outgoing ∧
      radialRightCornerWidth radial incoming outgoing < 2 * Real.pi := by
  exact radialLeftCornerWidth_bounds (-radial) (-outgoing) (-incoming)
    (by simpa only [inner_neg_neg] using last) (by simpa only [inner_neg_neg] using first)

/-- The clockwise source-circle tangent selects the actual right-side corner. -/
theorem radialRightCorner_normal_mem (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    -(Complex.I * radial) ∈ interior (radialRightCornerFrame radial incoming ''
      closedAngularSector (radialRightCornerWidth radial incoming outgoing)) := by
  simpa only [mul_neg, radialRightCornerFrame, radialRightCornerWidth] using
    radialLeftCorner_normal_mem (-radial) (-outgoing) (-incoming)
    (by simpa only [inner_neg_neg] using last) (by simpa only [inner_neg_neg] using first)

/-- The right-side oriented banks are the reversed incoming and original outgoing rays. -/
theorem radialRightCorner_bank_rays (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    nonnegativeRay (-incoming) ∪ nonnegativeRay outgoing =
      radialRightCornerFrame radial incoming ''
        (Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪ Set.range (fun r : ℝ≥0 =>
          (r : ℂ) * polarRay (radialRightCornerWidth radial incoming outgoing))) := by
  simpa only [neg_neg, Set.union_comm, radialRightCornerFrame, radialRightCornerWidth] using
    radialLeftCorner_bank_rays (-radial) (-outgoing) (-incoming)
      (by simpa only [inner_neg_neg] using last) (by simpa only [inner_neg_neg] using first)

/-- Recover the right aperture from the named physical edge vectors. -/
theorem radialRightCornerWidth_eq_positiveGapAngle (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    radialRightCornerWidth radial incoming outgoing = positiveGapAngle (-incoming) outgoing := by
  simpa only [neg_neg, radialRightCornerWidth] using
    radialLeftCornerWidth_eq_positiveGapAngle (-radial) (-outgoing) (-incoming)
      (by simpa only [inner_neg_neg] using last) (by simpa only [inner_neg_neg] using first)

end Unfoldings
