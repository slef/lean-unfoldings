module

public import Unfoldings.Geometry.PolygonalRayEmbedding
public import Unfoldings.Geometry.RadialTwist

/-! Straighten an actual radially monotone polygonal bank by a homeomorphism of the whole plane. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- The unique actual bank point at a specified source-centered radius. -/
def radialPoint (r : ℝ≥0) : ℂ := (R.radialHomeomorph outward nonzero).symm r

theorem radialPoint_mem (r : ℝ≥0) : R.radialPoint outward nonzero r ∈ R.carrier :=
  ((R.radialHomeomorph outward nonzero).symm r).property

@[simp] theorem norm_radialPoint_sub_start (r : ℝ≥0) :
    ‖R.radialPoint outward nonzero r - R.start‖ = (r : ℝ) := by
  have equality := congrArg ((↑) : ℝ≥0 → ℝ)
    ((R.radialHomeomorph outward nonzero).apply_symm_apply r)
  change dist R.start (R.radialPoint outward nonzero r) = (r : ℝ) at equality
  simpa only [dist_eq_norm'] using equality

@[simp] theorem radialPoint_zero : R.radialPoint outward nonzero 0 = R.start := by
  exact sub_eq_zero.mp (norm_eq_zero.mp (R.norm_radialPoint_sub_start outward nonzero 0))

theorem continuous_radialPoint : Continuous (R.radialPoint outward nonzero) :=
  continuous_subtype_val.comp (R.radialHomeomorph outward nonzero).symm.continuous

def radialCoefficient (r : ℝ≥0) : ℂ :=
  (R.radialPoint outward nonzero r - R.start) / (r : ℂ)

theorem radialCoefficient_unit (r : ℝ≥0) (positive : 0 < r) :
    ‖R.radialCoefficient outward nonzero r‖ = 1 := by
  rw [radialCoefficient, norm_div, R.norm_radialPoint_sub_start, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
  exact div_self (NNReal.coe_ne_zero.mpr positive.ne')

theorem continuousOn_radialCoefficient :
    ContinuousOn (R.radialCoefficient outward nonzero) (Set.Ioi 0) := by
  apply ((R.continuous_radialPoint outward nonzero).sub continuous_const).continuousOn.div
    (by fun_prop)
  intro r positive
  exact Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ne_of_gt positive))

/-- This global ambient homeomorphism carries the positive real ray exactly onto the bank. -/
def bankFrame : ℂ ≃ₜ ℂ :=
  (radialTwistHomeomorph (R.radialCoefficient outward nonzero)
    (R.radialCoefficient_unit outward nonzero)
    (R.continuousOn_radialCoefficient outward nonzero)).trans
    (Homeomorph.addLeft R.start)

@[simp] theorem bankFrame_apply (z : ℂ) :
    R.bankFrame outward nonzero z = R.start + R.radialCoefficient outward nonzero ‖z‖₊ * z := rfl

private theorem nnnorm_of_nonnegative_real (r : ℝ≥0) : ‖(r : ℂ)‖₊ = r := by
  apply NNReal.eq
  simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg r.coe_nonneg]

/-- The full actual bank is retained, rather than just its vertices or asymptotic direction. -/
@[simp] theorem bankFrame_real (r : ℝ≥0) :
    R.bankFrame outward nonzero (r : ℂ) = R.radialPoint outward nonzero r := by
  rw [R.bankFrame_apply, nnnorm_of_nonnegative_real]
  by_cases zero : r = 0
  · simp [zero]
  · rw [radialCoefficient, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr zero))]
    abel

/-- All constant-angle rays become the actual rigidly rotated banks. -/
theorem bankFrame_rotated_ray (r : ℝ≥0) (angle : ℝ) :
    R.bankFrame outward nonzero (polarRay angle * (r : ℂ)) =
      R.start + complexRotation angle (R.radialPoint outward nonzero r - R.start) := by
  have radius : ‖polarRay angle * (r : ℂ)‖₊ = r := by
    rw [nnnorm_mul]
    have unit : ‖polarRay angle‖₊ = 1 := NNReal.eq (norm_polarRay angle)
    rw [unit, one_mul, nnnorm_of_nonnegative_real]
  have base := R.bankFrame_real outward nonzero r
  rw [R.bankFrame_apply] at base
  rw [R.bankFrame_apply, radius, complexRotation_apply]
  rw [nnnorm_of_nonnegative_real] at base
  linear_combination polarRay angle * base

end Unfoldings.PolygonalRay
