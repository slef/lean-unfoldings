module

public import Unfoldings.Geometry.PolygonalRayFrame
public import Unfoldings.Geometry.ComplexNormalization

/-! Actual circle contacts approach the direction of the original straight terminal ray. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

include outward nonzero in
/-- The finite bank prefix contributes an explicit error decaying inversely with radius. -/
theorem radialCoefficient_tail_error (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex (Fin.last n)) < (r : ℝ)) :
    ‖R.radialCoefficient outward nonzero r - R.direction / (‖R.direction‖ : ℂ)‖ ≤
      2 * ‖R.chain.vertex (Fin.last n) - R.start‖ / (r : ℝ) := by
  have member := R.radialPoint_mem outward nonzero r
  rcases member with prefix_member | ⟨t, equal⟩
  · have bound := R.prefix_radius_le outward prefix_member
    have radius : dist R.start (R.radialPoint outward nonzero r) = (r : ℝ) := by
      rw [dist_eq_norm', R.norm_radialPoint_sub_start]
    rw [radius] at bound
    exact (higher.not_ge bound).elim
  · have radius : ‖R.tail t - R.start‖ = (r : ℝ) := by
      rw [equal, R.norm_radialPoint_sub_start]
    have positive : (0 : ℝ) < t := by
      by_contra not_positive
      have zero : t = 0 := NNReal.eq (le_antisymm (le_of_not_gt not_positive) t.coe_nonneg)
      rw [zero, R.tail_zero, ← dist_eq_norm'] at radius
      exact higher.ne radius
    have direction_positive := norm_pos_iff.mpr nonzero
    have unit : ((t : ℝ) • R.direction) / (‖(t : ℝ) • R.direction‖ : ℂ) =
        R.direction / (‖R.direction‖ : ℂ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos positive, Complex.real_smul]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr positive.ne',
        Complex.ofReal_ne_zero.mpr direction_positive.ne']
    have actual_nonzero : R.tail t - R.start ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [radius]
      exact ne_of_gt (dist_nonneg.trans_lt higher)
    have estimate := complex_normalized_sub_le (R.tail t - R.start) ((t : ℝ) • R.direction)
      actual_nonzero (smul_ne_zero positive.ne' nonzero)
    have difference : R.tail t - R.start - (t : ℝ) • R.direction =
        R.chain.vertex (Fin.last n) - R.start := by
      rw [tail]
      abel
    rw [radius, unit, difference] at estimate
    simpa only [radialCoefficient, ← equal] using estimate

include outward nonzero in
/-- The limit uses actual points on the infinite bank, not a replacement parallel ray. -/
theorem tendsto_radialCoefficient :
    Tendsto (R.radialCoefficient outward nonzero) atTop
      (𝓝 (R.direction / (‖R.direction‖ : ℂ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  let a := dist R.start (R.chain.vertex (Fin.last n))
  have large : ∀ᶠ r : ℝ≥0 in atTop, max a (2 * a / ε) < (r : ℝ) :=
    (NNReal.tendsto_coe_atTop.mpr tendsto_id).eventually (eventually_gt_atTop _)
  filter_upwards [large] with r bound
  have higher : a < (r : ℝ) := (le_max_left _ _).trans_lt bound
  have radius_positive : 0 < (r : ℝ) := dist_nonneg.trans_lt higher
  have ratio : 2 * a / (r : ℝ) < ε := by
    apply (div_lt_iff₀ radius_positive).mpr
    have far : 2 * a / ε < (r : ℝ) := (le_max_right _ _).trans_lt bound
    simpa only [mul_comm] using (div_lt_iff₀ positive).mp far
  rw [dist_eq_norm]
  exact (R.radialCoefficient_tail_error outward nonzero r higher).trans_lt
    (by simpa only [a, dist_eq_norm'] using ratio)

end Unfoldings.PolygonalRay
