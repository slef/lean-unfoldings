module

public import Unfoldings.Cap.SharpAngleProjection
public import Unfoldings.Geometry.GnomonicTraceTransport

/-! Real headings of the horizontal section in the pole-aligned frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real

/-- The forward horizontal section's heading after radial alignment to the pole. -/
def radialSectionHeading (p q : ℝ) : ℝ :=
  arctan (p * q / (√(1 + p ^ 2 + q ^ 2) + 1 + p ^ 2))

theorem alignedHorizontal_section_coordinates (p q : ℝ) :
    let n := gnomonicNormal (WithLp.toLp 2 ![p, q])
    let d := √(1 + p ^ 2 + q ^ 2)
    let v : Space := WithLp.toLp 2 ![1, 0, -p]
    alignedHorizontal n v = WithLp.toLp 2 ![1 + p ^ 2 / (d + 1), p * q / (d + 1)] := by
  let d := √(1 + p ^ 2 + q ^ 2)
  let n := gnomonicNormal (WithLp.toLp 2 ![p, q])
  let v : Space := WithLp.toLp 2 ![1, 0, -p]
  have norm_lift : ‖northLift (WithLp.toLp 2 ![p, q])‖ = d := by
    unfold d
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_three]
    change |p| ^ 2 + |q| ^ 2 + |(1 : ℝ)| ^ 2 = _
    simp only [sq_abs, abs_one, one_pow]
    ring
  have dp : 0 < d := sqrt_pos.mpr (by positivity)
  have ncoord (k : Fin 3) :
      n k = d⁻¹ * (northLift (WithLp.toLp 2 ![p, q])) k := by
    unfold n gnomonicNormal NormedSpace.normalize
    rw [norm_lift]
    rfl
  have hp : n 0 = d⁻¹ * p := ncoord 0
  have hq : n 1 = d⁻¹ * q := ncoord 1
  have hz : n 2 = d⁻¹ := (ncoord 2).trans (mul_one _)
  change alignedHorizontal n v = _
  ext k
  fin_cases k
  · change 1 - (-p / (1 + n 2)) * n 0 = 1 + p ^ 2 / (d + 1)
    rw [hp, hz]
    have pn : 0 < 1 + d⁻¹ := by positivity
    field_simp [dp.ne', pn.ne', show d + 1 ≠ 0 by positivity]
    <;> ring
  · change 0 - (-p / (1 + n 2)) * n 1 = p * q / (d + 1)
    rw [hq, hz]
    have pn : 0 < 1 + d⁻¹ := by positivity
    field_simp [dp.ne', pn.ne', show d + 1 ≠ 0 by positivity]
    <;> ring

/-- Radial alignment agrees with the transport integral on each slope ray.
The formula is real and also applies when the ray points to decreasing abscissa. -/
theorem radialSectionHeading_eq_hingeAngleChange (m p : ℝ) :
    radialSectionHeading p (m * p) = hingeAngleChange m 0 0 p := by
  let d := √(1 + p ^ 2 + (m * p) ^ 2)
  have dp : 0 < d := sqrt_pos.mpr (by positivity)
  have ds : d ^ 2 = 1 + p ^ 2 + (m * p) ^ 2 := sq_sqrt (by positivity)
  have at_zero : gnomonicHingeRatio m 0 0 = -m := by simp [gnomonicHingeRatio]
  have at_last : gnomonicHingeRatio m 0 p = -m / d := by
    simp [gnomonicHingeRatio, d]
  unfold radialSectionHeading hingeAngleChange
  rw [at_zero, at_last, arctan_neg, sub_neg_eq_add, add_comm (arctan (-m / d)) (arctan m)]
  have product : m * (-m / d) < 1 := by
    have eq : m * (-m / d) = -(m ^ 2 / d) := by ring
    rw [eq]
    exact (neg_nonpos.mpr (div_nonneg (sq_nonneg m) dp.le)).trans_lt zero_lt_one
  rw [arctan_add product]
  congr 1
  change p * (m * p) / (d + 1 + p ^ 2) = (m + -m / d) / (1 - m * (-m / d))
  have q : 0 < 1 - m * (-m / d) := sub_pos.mpr product
  have w : 0 < d + 1 + p ^ 2 := by positivity
  apply (div_eq_div_iff w.ne' q.ne').mpr
  field_simp [dp.ne']
  linear_combination -m * ds

/-- At a vertical normal radius the horizontal tangent itself is fixed. -/
@[simp] theorem radialSectionHeading_zero (q : ℝ) : radialSectionHeading 0 q = 0 := by
  simp [radialSectionHeading]

end Unfoldings.Cap
