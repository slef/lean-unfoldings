module

public import Unfoldings.Geometry.HingeCircleLift

/-! Actual positive circle order transfers to every continuous real heading in a common frame. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (positive : 0 < angle) (outward : (R.suffix hinge).Outward) (small : angle < Real.pi)

include outward small radial positive in
/-- Covering-space uniqueness identifies the actual unreduced angular increment in any
continuous common frame; no modulo-angle choice is left in the result. -/
theorem hinge_heading_eq_lift (r : Set.Ioi (nndist R.start (R.chain.vertex hinge)))
    (reference : Circle) (heading : Set.Icc 0 angle → ℝ) (continuous_heading : Continuous heading)
    (phase : ∀ θ, Circle.exp (heading θ) =
      R.hingeExteriorDirection hinge nonzero angle radial (θ, r) / reference)
    (θ : Set.Icc 0 angle) :
    heading θ = heading ⟨0, le_rfl, positive.le⟩ +
      R.hingeCircleLift hinge nonzero angle radial positive r θ := by
  let initial : Set.Icc 0 angle := ⟨0, le_rfl, positive.le⟩
  let : PreconnectedSpace (Set.Icc 0 angle) := Subtype.preconnectedSpace isPreconnected_Icc
  have lifted (ψ : Set.Icc 0 angle) :
      Circle.exp (heading initial + R.hingeCircleLift hinge nonzero angle radial positive r ψ) =
        Circle.exp (heading ψ) := by
    rw [Circle.exp_add, R.exp_hingeCircleLift, phase initial, phase ψ]
    rw [mul_comm, div_mul_div_cancel]
  have equal := Circle.isCoveringMap_exp.eq_of_comp_eq continuous_heading
    (continuous_const.add
      (R.continuous_hingeCircleLift hinge nonzero angle radial positive outward small r))
    (funext (fun ψ => (lifted ψ).symm)) initial (by
      change heading initial = heading initial +
        R.hingeCircleLift hinge nonzero angle radial positive r initial
      simp only [initial, R.hingeCircleLift_zero, add_zero])
  exact congrFun equal θ

include outward small radial positive in
/-- Every continuous common-frame heading increases strictly throughout the actual active gap. -/
theorem strictMono_hinge_heading (r : Set.Ioi (nndist R.start (R.chain.vertex hinge)))
    (reference : Circle) (heading : Set.Icc 0 angle → ℝ) (continuous_heading : Continuous heading)
    (phase : ∀ θ, Circle.exp (heading θ) =
      R.hingeExteriorDirection hinge nonzero angle radial (θ, r) / reference) :
    StrictMono heading := by
  intro θ ψ before
  rw [R.hinge_heading_eq_lift hinge nonzero angle radial positive outward small r
      reference heading continuous_heading phase θ,
    R.hinge_heading_eq_lift hinge nonzero angle radial positive outward small r
      reference heading continuous_heading phase ψ]
  exact add_lt_add_right
    (R.strictMono_hingeCircleLift hinge nonzero angle radial positive outward small r before) _

end Unfoldings.PolygonalRay
