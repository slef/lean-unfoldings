module

public import Unfoldings.Geometry.VariableSectorMembership

/-! Exact local sides of the actual variable-opening region along its two banks. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings

/-- The actual signed test for the upper boundary at the point's own radius. -/
def variableSectorSecondSide (width : ℝ≥0 → ℝ) (z : ℂ) : ℝ :=
  z.re * Real.sin (width ‖z‖₊) - z.im * Real.cos (width ‖z‖₊)

variable (width : ℝ≥0 → ℝ) (regular : ContinuousOn width (Set.Ioi 0))

include regular in
theorem continuousAt_variableSectorAngle {z : ℂ} (nonzero : z ≠ 0) :
    ContinuousAt (fun w : ℂ => width ‖w‖₊) z :=
  (regular.continuousAt (isOpen_Ioi.mem_nhds (nnnorm_pos.mpr nonzero))).comp
    continuous_nnnorm.continuousAt

include regular in
theorem continuousAt_variableSectorSecondSide {z : ℂ} (nonzero : z ≠ 0) :
    ContinuousAt (variableSectorSecondSide width) z := by
  have angle := continuousAt_variableSectorAngle width regular nonzero
  exact (Complex.continuous_re.continuousAt.mul
    (Real.continuous_sin.continuousAt.comp angle)).sub
    (Complex.continuous_im.continuousAt.mul (Real.continuous_cos.continuousAt.comp angle))

variable (α : ℝ) (first : Real.sin α ≠ 0) (sine : ∀ r, Real.sin (width r) ≠ 0)

/-- At a positive point on the first bank the exact region has its upper-halfplane side. -/
theorem eventually_mem_variableSectorGap_iff_first_side (r : ℝ≥0) (positive : 0 < r)
    (positive_sine : 0 < Real.sin (width r)) :
    ∀ᶠ z in 𝓝 (r : ℂ),
      z ∈ variableSectorGap α first width sine regular ↔ 0 ≤ z.im := by
  have radius : ‖(r : ℂ)‖₊ = r := by
    apply NNReal.eq
    simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
  have nonzero : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr positive.ne')
  have angular := continuousAt_variableSectorAngle width regular nonzero
  have sine_near : ∀ᶠ z in 𝓝 (r : ℂ), 0 < Real.sin (width ‖z‖₊) :=
    (Real.continuous_sin.continuousAt.comp angular).eventually
      (isOpen_Ioi.mem_nhds (by
        change 0 < Real.sin (width ‖(r : ℂ)‖₊)
        rwa [radius]))
  have upper_positive : 0 < variableSectorSecondSide width (r : ℂ) := by
    simp only [variableSectorSecondSide, radius, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_pos (show (0 : ℝ) < r from positive) positive_sine
  have upper_near := (continuousAt_variableSectorSecondSide width regular nonzero).eventually
    (isOpen_Ioi.mem_nhds upper_positive)
  filter_upwards [sine_near, upper_near] with z sin_pos upper
  rw [mem_variableSectorGap_iff, mem_planarSector_iff_halfplanes _ sin_pos]
  exact and_iff_left upper.le

/-- At a positive point on the second side the first halfplane has positive clearance. -/
theorem eventually_mem_variableSectorGap_iff_second_side (z : ℂ)
    (imaginary : 0 < z.im) (positive_sine : 0 < Real.sin (width ‖z‖₊)) :
    ∀ᶠ w in 𝓝 z,
      w ∈ variableSectorGap α first width sine regular ↔ 0 ≤ variableSectorSecondSide width w := by
  have nonzero : z ≠ 0 := by
    intro zero
    rw [zero, Complex.zero_im] at imaginary
    exact lt_irrefl _ imaginary
  have angular := continuousAt_variableSectorAngle width regular nonzero
  have sine_near := (Real.continuous_sin.continuousAt.comp angular).eventually
    (isOpen_Ioi.mem_nhds positive_sine)
  have imaginary_near := Complex.continuous_im.continuousAt.eventually
    (isOpen_Ioi.mem_nhds imaginary)
  filter_upwards [sine_near, imaginary_near] with w sin_pos im_pos
  rw [mem_variableSectorGap_iff, mem_planarSector_iff_halfplanes _ sin_pos]
  exact and_iff_right im_pos.le

end Unfoldings
