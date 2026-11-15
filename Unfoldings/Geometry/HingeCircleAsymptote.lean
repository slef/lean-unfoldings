module

public import Unfoldings.Geometry.HingeCircleDirections
public import Unfoldings.Geometry.PolygonalRayAsymptote

/-! The actual real circle-contact displacement tends to the true hinge opening at infinity. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)

include nonzero radial in
theorem tendsto_hingeExteriorDirection_coe (θ : Set.Icc 0 angle) :
    Tendsto (fun r : Set.Ioi (nndist R.start (R.chain.vertex hinge)) =>
      (R.hingeExteriorDirection hinge nonzero angle radial (θ, r) : ℂ)) atTop
      (𝓝 (polarRay θ.val * R.direction / (‖R.direction‖ : ℂ))) := by
  have equal (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
      (R.hingeExteriorDirection hinge nonzero angle radial (θ, r) : ℂ) =
        (R.rotateSuffix hinge θ.val).radialCoefficient (radial θ.val θ.property)
          (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r.val := by
    rw [R.hingeExteriorDirection_coe]
    change (_ - R.start) / _ = (_ - (R.rotateSuffix hinge θ.val).start) / _
    rw [R.rotateSuffix_start]
    rfl
  simp_rw [equal]
  have limit := (R.rotateSuffix hinge θ.val).tendsto_radialCoefficient
    (radial θ.val θ.property) (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero)
  have norm_direction : ‖(R.rotateSuffix hinge θ.val).direction‖ = ‖R.direction‖ :=
    (complexRotation θ.val).norm_map _
  rw [norm_direction] at limit
  exact tendsto_comp_val_Ioi_atTop.mpr limit

variable (positive : 0 < angle) (small : angle < Real.pi)

include radial in
theorem tendsto_hingeRelativeDirection (θ : Set.Ioc 0 angle) :
    Tendsto (fun r : Set.Ioi (nndist R.start (R.chain.vertex hinge)) =>
      R.hingeRelativeDirection hinge nonzero angle radial positive (θ, r)) atTop
      (𝓝 (Circle.exp θ.val)) := by
  let first : Set.Icc 0 angle := ⟨θ.val, θ.property.1.le, θ.property.2⟩
  let initial : Set.Icc 0 angle := ⟨0, le_rfl, positive.le⟩
  have first_limit := R.tendsto_hingeExteriorDirection_coe hinge nonzero angle radial first
  have initial_limit := R.tendsto_hingeExteriorDirection_coe hinge nonzero angle radial initial
  simp only [initial, polarRay_zero, one_mul] at initial_limit
  have nonzero_norm : (‖R.direction‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero)
  have ratio_limit := first_limit.div initial_limit (div_ne_zero nonzero nonzero_norm)
  have ratio : (polarRay first.val * R.direction / (‖R.direction‖ : ℂ)) /
      (R.direction / (‖R.direction‖ : ℂ)) = polarRay θ.val := by
    dsimp only [first]
    field_simp
  rw [ratio] at ratio_limit
  apply tendsto_subtype_rng.mpr
  exact ratio_limit

include small radial in
theorem tendsto_hingeCircleAngle (θ : Set.Ioc 0 angle) :
    Tendsto (fun r : Set.Ioi (nndist R.start (R.chain.vertex hinge)) =>
      R.hingeCircleAngle hinge nonzero angle radial positive (θ, r)) atTop (𝓝 θ.val) := by
  have short : θ.val < 2 * Real.pi := θ.property.2.trans_lt (by linarith [Real.pi_pos])
  have different : Circle.exp θ.val ≠ 1 := by
    intro equal
    have same := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      ⟨θ.property.1.le, short⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩
      (equal.trans Circle.exp_zero.symm)
    exact θ.property.1.ne' same
  have limit := (continuousAt_circlePositiveAngle different).tendsto.comp
    (R.tendsto_hingeRelativeDirection hinge nonzero angle radial positive θ)
  simpa only [hingeCircleAngle, Function.comp_def,
    circlePositiveAngle_exp θ.property.1 short] using limit

end Unfoldings.PolygonalRay
