module

public import Unfoldings.Cap.GnomonicArea
public import Unfoldings.Cap.VerticalProduct
public import Unfoldings.Geometry.EuclideanMeasure
public import Unfoldings.Geometry.SolidAngle

/-!
# Solid-angle bounds from actual gnomonic slope polygons

A uniform Lipschitz bound on a conical parametrization compares spatial cone
volume to the area of its planar base. The resulting conservative constant is
sufficient for a positive near-flat curvature threshold; no exact surface-area
change-of-variables formula is needed here.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory
open scoped Pointwise ENNReal NNReal

theorem vertical_abs_le_norm (z : Space) : |z 2| ≤ ‖z‖ := by
  have split := horizontal_norm_sq z
  nlinarith [sq_abs (z 2), abs_nonneg (z 2), norm_nonneg z, sq_nonneg ‖horizontal z‖]

/-- Scale a height-one lift by the vertical parameter stored in the input. -/
def coneParam (z : Space) : Space := z 2 • northLift (horizontal z)

theorem coneParam_difference (x y : Space) :
    coneParam x - coneParam y = x 2 • horizontalLift (horizontal (x - y)) +
      (x 2 - y 2) • northLift (horizontal y) := by
  ext i
  fin_cases i
  · change x 2 * x 0 - y 2 * y 0 = x 2 * (x 0 - y 0) + (x 2 - y 2) * y 0
    ring
  · change x 2 * x 1 - y 2 * y 1 = x 2 * (x 1 - y 1) + (x 2 - y 2) * y 1
    ring
  · change x 2 * 1 - y 2 * 1 = x 2 * 0 + (x 2 - y 2) * 1
    ring

/-- On unit horizontal bases and unit vertical intervals, the conical map is 3-Lipschitz. -/
theorem coneParam_lipschitzOn {s : Set Plane} (small : s ⊆ Metric.closedBall (0 : Plane) 1) :
    LipschitzOnWith 3 coneParam (verticalPrism s 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have height : |x 2| ≤ 1 := by
    rw [abs_of_nonneg hx.2.1]
    exact hx.2.2
  have base : ‖horizontal y‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using small hy.1
  have lift : ‖northLift (horizontal y)‖ ≤ 2 := by
    have split := horizontal_norm_sq (northLift (horizontal y))
    rw [northLift_horizontal, northLift_height] at split
    nlinarith [norm_nonneg (northLift (horizontal y)), norm_nonneg (horizontal y)]
  have projected := horizontal_norm_le (x - y)
  have vertical := vertical_abs_le_norm (x - y)
  change |x 2 - y 2| ≤ ‖x - y‖ at vertical
  rw [dist_eq_norm, dist_eq_norm, coneParam_difference]
  calc
    _ ≤ ‖x 2 • horizontalLift (horizontal (x - y))‖ +
        ‖(x 2 - y 2) • northLift (horizontal y)‖ := norm_add_le _ _
    _ = |x 2| * ‖horizontal (x - y)‖ +
        |x 2 - y 2| * ‖northLift (horizontal y)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, horizontalLift_norm]
    _ ≤ 1 * ‖x - y‖ + ‖x - y‖ * 2 :=
      add_le_add (mul_le_mul height projected (norm_nonneg _) (by norm_num))
        (mul_le_mul vertical lift (norm_nonneg _) (by positivity))
    _ = (3 : ℝ≥0) * ‖x - y‖ := by norm_num; ring

/-- Every unit-ball cone point occurs in the actual parametrized horizontal prism. -/
theorem gnomonic_cone_subset_param (s : Set Plane) :
    Set.Ioo (0 : ℝ) 1 • (gnomonicNormal '' s) ⊆ coneParam '' verticalPrism s 0 1 := by
  rintro z ⟨r, bounds, _, ⟨g, inside, rfl⟩, rfl⟩
  let t : ℝ := r * ‖northLift g‖⁻¹
  have normpos : 0 < ‖northLift g‖ := norm_pos_iff.mpr (northLift_ne_zero g)
  have tpos : 0 < t := mul_pos bounds.1 (inv_pos.mpr normpos)
  have tsmall : t ≤ 1 := by
    change r * ‖northLift g‖⁻¹ ≤ 1
    rw [← div_eq_mul_inv]
    exact (div_le_one normpos).mpr (bounds.2.le.trans (northLift_norm_lower g))
  refine ⟨horizontalAtHeight g t, ⟨by simpa using inside, by simpa using And.intro tpos.le tsmall⟩,
    ?_⟩
  rw [coneParam, horizontal_horizontalAtHeight, height_horizontalAtHeight,
    gnomonicNormal, NormedSpace.normalize]
  change t • northLift g = r • (‖northLift g‖⁻¹ • northLift g)
  rw [smul_smul]

/-- A rigorous conservative solid-angle estimate, uniform in the shape of the base polygon. -/
theorem solidAngle_gnomonic_le {s : Set Plane} (compact : IsCompact s)
    (small : s ⊆ Metric.closedBall (0 : Plane) 1) :
    solidAngleMeasure (gnomonicNormal '' s) ≤ 81 * volume s := by
  have unit : gnomonicNormal '' s ⊆ Metric.sphere (0 : Space) 1 := by
    rintro z ⟨g, _, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using gnomonicNormal_unit g
  rw [solidAngleMeasure_apply
    (compact.image gnomonicNormal_lipschitz.continuous).measurableSet unit]
  have estimate := (coneParam_lipschitzOn small).euclideanHausdorffMeasure_image_le 3
  simp only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at estimate
  rw [volume_verticalPrism s compact.measurableSet, sub_zero, ENNReal.ofReal_one, mul_one]
    at estimate
  calc
    _ ≤ 3 * volume (coneParam '' verticalPrism s 0 1) :=
      mul_le_mul_of_nonneg_left (measure_mono (gnomonic_cone_subset_param s)) (by positivity)
    _ ≤ 3 * ((3 : ℝ≥0∞) ^ 3 * volume s) := by
      exact mul_le_mul_of_nonneg_left (by simpa using estimate) (by positivity)
    _ = 81 * volume s := by norm_num [← mul_assoc]

end Unfoldings.Cap
