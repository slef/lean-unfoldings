module

public import Unfoldings.Geometry.HingeGapCircleContacts

/-! Actual gap interiors lie strictly between their two banks in a common angular frame. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (r : ℝ≥0) (radius_positive : 0 < r) (reference : Circle)

@[simp] theorem hingeCommonHeading_eq_contact (θ : Set.Icc 0 angle) :
    R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference θ =
      Complex.arg ((R.hingeCirclePoint hinge nonzero angle radial r θ - R.start) /
        (r : ℂ) / (reference : ℂ)) := by
  unfold hingeCommonHeading
  rw [R.hingeSweepDirection_coe]

variable (outward : R.Outward) (suffix_outward : (R.suffix hinge).Outward)
  (positive : 0 < angle) (small : angle < Real.pi)
  (halfplane : ∀ θ, 0 < ((R.hingeSweepDirection hinge nonzero angle radial r radius_positive θ /
    reference : Circle) : ℂ).re)

include outward suffix_outward positive small radial halfplane in
/-- Every actual gap point is between the common-frame headings of the original and final banks. -/
theorem hingeGap_heading_bounds {z : ℂ}
    (member : z ∈ (R.suffix hinge).rotationGap suffix_outward nonzero angle)
    (radius : dist R.start z = (r : ℝ)) :
    Complex.arg ((z - R.start) / (r : ℂ) / (reference : ℂ)) ∈
      Set.Icc
        (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference
          ⟨0, le_rfl, positive.le⟩)
        (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference
          ⟨angle, positive.le, le_rfl⟩) := by
  obtain ⟨θ, equal⟩ := R.hingeGap_circle_contact hinge nonzero angle radial suffix_outward
    positive small r member radius
  have monotone := R.monotone_hingeCommonHeading hinge nonzero angle radial r radius_positive
    reference outward suffix_outward positive small halfplane
  have first := monotone (show (⟨0, le_rfl, positive.le⟩ : Set.Icc 0 angle) ≤ θ from θ.property.1)
  have last := monotone
    (show θ ≤ (⟨angle, positive.le, le_rfl⟩ : Set.Icc 0 angle) from θ.property.2)
  rw [R.hingeCommonHeading_eq_contact hinge nonzero angle radial r
    radius_positive reference θ, equal] at first last
  exact ⟨first, last⟩

include suffix_outward positive small radial halfplane in
/-- An interior point has strict angular inequalities on both actual banks. -/
theorem hingeGap_interior_heading_bounds {z : ℂ}
    (member : z ∈ interior ((R.suffix hinge).rotationGap suffix_outward nonzero angle))
    (radius : dist R.start z = (r : ℝ)) :
    Complex.arg ((z - R.start) / (r : ℂ) / (reference : ℂ)) ∈
      Set.Ioo
        (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference
          ⟨0, le_rfl, positive.le⟩)
        (R.hingeCommonHeading hinge nonzero angle radial r radius_positive reference
          ⟨angle, positive.le, le_rfl⟩) := by
  obtain ⟨θ, first_angle, last_angle, equal⟩ :=
    R.hingeGap_interior_circle_contact hinge nonzero angle radial suffix_outward
      positive small r member radius
  have above : dist R.start (R.chain.vertex hinge) < (r : ℝ) :=
    radius ▸ R.hingeGap_interior_radius_gt_hinge hinge nonzero angle radial
      suffix_outward positive small member
  have strict := R.strictMono_hingeCommonHeading_of_above hinge nonzero angle radial r
    radius_positive reference suffix_outward positive small halfplane above
  have first := strict
    (show (⟨0, le_rfl, positive.le⟩ : Set.Icc 0 angle) < θ from first_angle)
  have last := strict
    (show θ < (⟨angle, positive.le, le_rfl⟩ : Set.Icc 0 angle) from last_angle)
  rw [R.hingeCommonHeading_eq_contact hinge nonzero angle radial r
    radius_positive reference θ, equal] at first last
  exact ⟨first, last⟩

end Unfoldings.PolygonalRay
