module

public import Unfoldings.Geometry.HingeSweepContinuity
public import Unfoldings.Topology.CirclePositiveAngle

/-! Continuous actual unit directions and positive angular coordinates of hinge-circle contacts. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)

/-- The actual contact direction from the original source, normalized on its own source circle. -/
def hingeExteriorDirection
    (p : Set.Icc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) : Circle :=
  ⟨(R.hingeCirclePoint hinge nonzero angle radial p.2.val p.1 - R.start) / (p.2.val : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,
      ← dist_eq_norm', R.hingeCirclePoint_radius, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg p.2.val.coe_nonneg]
    exact div_self (ne_of_gt (lt_of_le_of_lt dist_nonneg p.2.property))⟩

@[simp] theorem hingeExteriorDirection_coe
    (p : Set.Icc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    (R.hingeExteriorDirection hinge nonzero angle radial p : ℂ) =
      (R.hingeCirclePoint hinge nonzero angle radial p.2.val p.1 - R.start) / (p.2.val : ℂ) := rfl

include nonzero radial in
theorem continuous_hingeExteriorDirection :
    Continuous (R.hingeExteriorDirection hinge nonzero angle radial) := by
  apply Continuous.subtype_mk
  have base : Continuous (fun p : Set.Icc 0 angle ×
      Set.Ioi (nndist R.start (R.chain.vertex hinge)) => (p.1, p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have point := (R.continuous_hingeSweepPoint hinge nonzero angle radial).comp base
  apply (point.sub continuous_const).div (by fun_prop)
  intro p
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt dist_nonneg p.2.property))

variable (outward : (R.suffix hinge).Outward) (positive : 0 < angle) (small : angle < Real.pi)

include outward positive small radial in
theorem hingeExteriorDirection_injective
    (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    Function.Injective (fun θ => R.hingeExteriorDirection hinge nonzero angle radial (θ, r)) := by
  intro θ ψ same
  have nonzero_radius : (r.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt dist_nonneg r.property))
  have equal := congrArg (fun z : Circle => (z : ℂ) * (r.val : ℂ)) same
  simp only [R.hingeExteriorDirection_coe, div_mul_cancel₀ _ nonzero_radius] at equal
  apply R.hingeCirclePoint_injective hinge outward nonzero angle
    positive small radial r.val r.property
  exact sub_left_inj.mp equal

/-- Compare each contact with the actual unrotated bank at the same original-source radius. -/
def hingeRelativeDirection
    (p : Set.Ioc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) : Circle :=
  R.hingeExteriorDirection hinge nonzero angle radial
    (⟨p.1.val, p.1.property.1.le, p.1.property.2⟩, p.2) /
  R.hingeExteriorDirection hinge nonzero angle radial (⟨0, le_rfl, positive.le⟩, p.2)

include nonzero radial in
theorem continuous_hingeRelativeDirection :
    Continuous (R.hingeRelativeDirection hinge nonzero angle radial positive) := by
  unfold hingeRelativeDirection
  apply Continuous.div'
  · apply (R.continuous_hingeExteriorDirection hinge nonzero angle radial).comp
    apply Continuous.prodMk _ continuous_snd
    exact continuous_subtype_val.comp continuous_fst |>.subtype_mk _
  · apply (R.continuous_hingeExteriorDirection hinge nonzero angle radial).comp
    exact continuous_const.prodMk continuous_snd

include outward small radial in
theorem hingeRelativeDirection_ne_one
    (p : Set.Ioc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    R.hingeRelativeDirection hinge nonzero angle radial positive p ≠ 1 := by
  intro equal
  have same := div_eq_one.mp equal
  have angles := R.hingeExteriorDirection_injective hinge nonzero angle radial outward
    positive small p.2 same
  have zero : p.1.val = 0 := congrArg Subtype.val angles
  exact p.1.property.1.ne' zero

/-- Positive real angular displacement, with the cut at the saved starting bank. -/
def hingeCircleAngle
    (p : Set.Ioc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) : ℝ :=
  circlePositiveAngle (R.hingeRelativeDirection hinge nonzero angle radial positive p)

include outward small radial in
theorem continuous_hingeCircleAngle :
    Continuous (R.hingeCircleAngle hinge nonzero angle radial positive) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (continuousAt_circlePositiveAngle
    (R.hingeRelativeDirection_ne_one hinge nonzero angle radial outward positive small p)).comp
    (R.continuous_hingeRelativeDirection hinge nonzero angle radial positive).continuousAt

include outward small radial in
theorem hingeCircleAngle_bounds
    (p : Set.Ioc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    R.hingeCircleAngle hinge nonzero angle radial positive p ∈ Set.Ioo 0 (2 * Real.pi) :=
  ⟨circlePositiveAngle_pos _, circlePositiveAngle_lt_two_pi
    (R.hingeRelativeDirection_ne_one hinge nonzero angle radial outward positive small p)⟩

include outward small radial in
theorem hingeCircleAngle_injective
    (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    Function.Injective (fun θ =>
      R.hingeCircleAngle hinge nonzero angle radial positive (θ, r)) := by
  intro θ ψ equal
  have same := circlePositiveAngle_injective equal
  have contacts := div_left_inj.mp same
  have angles := R.hingeExteriorDirection_injective hinge nonzero angle radial outward
    positive small r contacts
  exact Subtype.ext (congrArg (fun θ : Set.Icc 0 angle => θ.val) angles)

end Unfoldings.PolygonalRay
