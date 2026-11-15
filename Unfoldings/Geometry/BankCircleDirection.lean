module

public import Unfoldings.Geometry.HingeCircleBelow
public import Unfoldings.Geometry.HingeCircleDirections

/-! Actual contact directions on every positive source circle, including circles below a hinge. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Normalize the unique actual whole-bank point on a positive source circle. -/
def circleDirection (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (r : ℝ≥0) (positive : 0 < r) : Circle :=
  ⟨R.radialCoefficient outward nonzero r,
    mem_sphere_zero_iff_norm.mpr (R.radialCoefficient_unit outward nonzero r positive)⟩

@[simp] theorem circleDirection_coe (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (r : ℝ≥0) (positive : 0 < r) :
    (R.circleDirection outward nonzero r positive : ℂ) =
      (R.radialPoint outward nonzero r - R.start) / (r : ℂ) := rfl

variable (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0) (angle : ℝ)
  (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)

/-- The true normalized contact throughout an opening, on active and inactive circles alike. -/
def hingeSweepDirection (r : ℝ≥0) (positive : 0 < r) (θ : Set.Icc 0 angle) : Circle :=
  (R.rotateSuffix hinge θ.val).circleDirection (radial θ.val θ.property)
    (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r positive

@[simp] theorem hingeSweepDirection_coe (r : ℝ≥0) (positive : 0 < r) (θ : Set.Icc 0 angle) :
    (R.hingeSweepDirection hinge nonzero angle radial r positive θ : ℂ) =
      (R.hingeCirclePoint hinge nonzero angle radial r θ - R.start) / (r : ℂ) := by
  rw [hingeSweepDirection, circleDirection_coe, R.rotateSuffix_start]
  rfl

include nonzero radial in
theorem continuous_hingeSweepDirection (r : ℝ≥0) (positive : 0 < r) :
    Continuous (R.hingeSweepDirection hinge nonzero angle radial r positive) := by
  apply Continuous.subtype_mk
  have point := (R.continuous_hingeSweepPoint hinge nonzero angle radial).comp
    (continuous_id.prodMk (continuous_const (y := r)))
  simp only [radialCoefficient, R.rotateSuffix_start]
  exact (point.sub (continuous_const (y := R.start))).div_const (r : ℂ)

include nonzero radial in
theorem hingeSweepDirection_eq_exterior
    (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) (positive : 0 < r.val)
    (θ : Set.Icc 0 angle) :
    R.hingeSweepDirection hinge nonzero angle radial r.val positive θ =
      R.hingeExteriorDirection hinge nonzero angle radial (θ, r) := by
  apply Circle.ext
  rw [R.hingeSweepDirection_coe, R.hingeExteriorDirection_coe]

include nonzero radial in
theorem hingeSweepDirection_eq_of_below (outward : R.Outward) (r : ℝ≥0) (positive : 0 < r)
    (below : (r : ℝ) ≤ dist R.start (R.chain.vertex hinge)) (θ : Set.Icc 0 angle) :
    R.hingeSweepDirection hinge nonzero angle radial r positive θ =
      R.circleDirection outward nonzero r positive := by
  apply Circle.ext
  rw [R.hingeSweepDirection_coe, R.circleDirection_coe,
    R.hingeCirclePoint_eq_of_below outward nonzero hinge angle radial r below θ]

end Unfoldings.PolygonalRay
