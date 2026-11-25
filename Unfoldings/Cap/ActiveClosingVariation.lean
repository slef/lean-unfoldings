module

public import Unfoldings.Cap.ActiveSectionVariation
public import Unfoldings.Roof.ActiveClosingVariation
public import Unfoldings.Roof.CapBridge

/-! The inclinations on both links of a closing path telescope through its common support face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Real InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

private theorem closing_toRoof_normalSlope (f : Face) :
    K.toRoof.normalSlope f = K.normalSlope f := rfl

/-- A bend in an actual support face changes its inclination by at most the
normal-slope norm times the change of direction. -/
theorem abs_faceInclination_sub_le (f : Face) (d e : Plane) :
    |K.faceInclination f d - K.faceInclination f e| ≤ ‖K.normalSlope f‖ * ‖d - e‖ :=
  K.toRoof.abs_faceInclination_sub_le f d e

/-- Contacts on one straight link occupy disjoint inclination intervals inside
the actual endpoint range. -/
theorem sum_active_section_angles_le_bounds {I : Type*} [Fintype I] (origin direction : Plane)
    (unit : ‖direction‖ = 1) (time : I → ℝ) (distinct : Function.Injective time)
    (face : I → Bool → Face)
    (active : ∀ i b, K.supportHeight (face i b) (origin + time i • direction) =
      K.roofHeight (origin + time i • direction))
    {lower upper : ℝ} (ordered : lower ≤ upper)
    (bounds : ∀ i side, K.faceInclination (face i side) direction ∈ Set.Icc lower upper) :
    (∑ i, angle (K.spatialDirection (face i false) direction)
      (K.spatialDirection (face i true) direction)) ≤ upper - lower := by
  have estimate := K.toRoof.sum_active_section_angles_le_bounds origin direction unit time distinct
    face active ordered bounds
  simpa only [K.spatialDirection_eq_section, ConvexRoof.sectionDirection, K.closing_toRoof_normalSlope] using estimate

/-- The absolute bends on two closing links share one tilt budget. Their extra
cost tends to zero as the two unit directions coalesce. -/
theorem sum_active_closing_angles_le {I J : Type*} [Fintype I] [Fintype J]
    (origin d e : Plane) (d_unit : ‖d‖ = 1) (e_unit : ‖e‖ = 1)
    (bendTime : ℝ) (middle : Face)
    (bend_active : K.supportHeight middle (origin + bendTime • d) =
      K.roofHeight (origin + bendTime • d))
    (s : I → ℝ) (s_distinct : Function.Injective s) (before : ∀ i, s i < bendTime)
    (t : J → ℝ) (t_distinct : Function.Injective t) (after : ∀ j, 0 < t j)
    (f : I → Bool → Face) (g : J → Bool → Face)
    (f_active : ∀ i b, K.supportHeight (f i b) (origin + s i • d) =
      K.roofHeight (origin + s i • d))
    (g_active : ∀ j b, K.supportHeight (g j b) (origin + bendTime • d + t j • e) =
      K.roofHeight (origin + bendTime • d + t j • e))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    (∑ i, angle (K.spatialDirection (f i false) d) (K.spatialDirection (f i true) d)) +
      (∑ j, angle (K.spatialDirection (g j false) e) (K.spatialDirection (g j true) e)) ≤
      2 * φ + tan φ * ‖d - e‖ := by
  have estimate := K.toRoof.sum_active_closing_angles_le origin d e d_unit e_unit bendTime middle
    bend_active s s_distinct before t t_distinct after f g f_active g_active nonnegative small tilt
  simpa only [K.spatialDirection_eq_section, ConvexRoof.sectionDirection, K.closing_toRoof_normalSlope] using estimate

end Unfoldings.ConvexCap
