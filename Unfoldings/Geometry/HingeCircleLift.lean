module

public import Unfoldings.Geometry.HingeCircleOrder
public import Unfoldings.Topology.CircleRealLift

/-! Continuous positive real angular lifts of actual complete hinge-circle arcs. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (positive : 0 < angle)

/-- Include the saved starting bank with real angular displacement zero. -/
def hingeCircleLift (r : Set.Ioi (nndist R.start (R.chain.vertex hinge)))
    (θ : Set.Icc 0 angle) : ℝ :=
  if after_start : 0 < θ.val then
    R.hingeCircleAngle hinge nonzero angle radial positive
      (⟨θ.val, after_start, θ.property.2⟩, r)
  else 0

@[simp] theorem hingeCircleLift_zero (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    R.hingeCircleLift hinge nonzero angle radial positive r ⟨0, le_rfl, positive.le⟩ = 0 := by
  simp [hingeCircleLift]

@[simp] theorem hingeCircleLift_last (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    R.hingeCircleLift hinge nonzero angle radial positive r ⟨angle, positive.le, le_rfl⟩ =
      R.hingeCircleAngle hinge nonzero angle radial positive (⟨angle, positive, le_rfl⟩, r) := by
  simp only [hingeCircleLift, dite_eq_left positive]

theorem exp_hingeCircleLift (r : Set.Ioi (nndist R.start (R.chain.vertex hinge)))
    (θ : Set.Icc 0 angle) :
    Circle.exp (R.hingeCircleLift hinge nonzero angle radial positive r θ) =
      R.hingeExteriorDirection hinge nonzero angle radial (θ, r) /
        R.hingeExteriorDirection hinge nonzero angle radial (⟨0, le_rfl, positive.le⟩, r) := by
  by_cases after_start : 0 < θ.val
  · rw [hingeCircleLift, dite_eq_left after_start]
    exact circle_exp_positiveAngle _
  · have zero : θ = ⟨0, le_rfl, positive.le⟩ :=
      Subtype.ext (le_antisymm (le_of_not_gt after_start) θ.property.1)
    rw [zero, R.hingeCircleLift_zero, Circle.exp_zero]
    exact (div_self' _).symm

variable (outward : (R.suffix hinge).Outward) (small : angle < Real.pi)

include outward small radial in
theorem hingeCircleLift_bounds (r : Set.Ioi (nndist R.start (R.chain.vertex hinge)))
    (θ : Set.Icc 0 angle) :
    R.hingeCircleLift hinge nonzero angle radial positive r θ ∈
      Set.Icc 0 (R.hingeCircleAngle hinge nonzero angle radial positive
        (⟨angle, positive, le_rfl⟩, r)) := by
  by_cases after_start : 0 < θ.val
  · rw [hingeCircleLift, dite_eq_left after_start]
    exact ⟨(R.hingeCircleAngle_bounds hinge nonzero angle radial outward positive small _).1.le,
      (R.strictMono_hingeCircleAngle hinge nonzero angle radial outward positive small r).monotone
        θ.property.2⟩
  · rw [hingeCircleLift, dite_eq_right after_start]
    exact ⟨le_rfl,
      (R.hingeCircleAngle_bounds hinge nonzero angle radial outward positive small _).1.le⟩

include outward small radial in
theorem continuous_hingeCircleLift (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    Continuous (R.hingeCircleLift hinge nonzero angle radial positive r) := by
  apply continuous_of_continuous_circle_exp_of_mem_Icc
    (by simpa only [sub_zero] using
      (R.hingeCircleAngle_bounds hinge nonzero angle radial outward positive small
        (⟨angle, positive, le_rfl⟩, r)).2)
    (R.hingeCircleLift_bounds hinge nonzero angle radial positive outward small r)
  simp_rw [R.exp_hingeCircleLift]
  apply Continuous.div'
  · exact (R.continuous_hingeExteriorDirection hinge nonzero angle radial).comp
      (continuous_id.prodMk continuous_const)
  · exact continuous_const

include outward small radial in
theorem strictMono_hingeCircleLift (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    StrictMono (R.hingeCircleLift hinge nonzero angle radial positive r) := by
  intro θ ψ before
  have last_positive : 0 < ψ.val := θ.property.1.trans_lt before
  by_cases first_positive : 0 < θ.val
  · simp only [hingeCircleLift, dite_eq_left first_positive, dite_eq_left last_positive]
    exact R.strictMono_hingeCircleAngle hinge nonzero angle radial outward positive small r before
  · simp only [hingeCircleLift, dite_eq_right first_positive, dite_eq_left last_positive]
    exact (R.hingeCircleAngle_bounds hinge nonzero angle radial outward positive small _).1

end Unfoldings.PolygonalRay
