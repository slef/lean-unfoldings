module

public import Unfoldings.Geometry.AngleMonotone
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Positive-span cones preserve acute angular bounds from a fixed axis. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine angular bound is exactly its homogeneous scalar-product inequality. -/
theorem angle_le_iff_cos_mul_norm_le {axis x : E} (axis_ne : axis ≠ 0) (xne : x ≠ 0)
    {θ : ℝ} (nonnegative : 0 ≤ θ) (small : θ ≤ Real.pi) :
    InnerProductGeometry.angle axis x ≤ θ ↔
      Real.cos θ * (‖axis‖ * ‖x‖) ≤ inner ℝ axis x := by
  have positive := mul_pos (norm_pos_iff.mpr axis_ne) (norm_pos_iff.mpr xne)
  constructor
  · intro bound
    have cosine := Real.cos_le_cos_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg axis x) small bound
    exact (mul_le_mul_of_nonneg_right cosine positive.le).trans_eq
      (InnerProductGeometry.cos_angle_mul_norm_mul_norm axis x)
  · intro scalar
    by_contra outside
    have cosine := Real.cos_lt_cos_of_nonneg_of_le_pi nonnegative
      (InnerProductGeometry.angle_le_pi axis x) (lt_of_not_ge outside)
    have strict := mul_lt_mul_of_pos_right cosine positive
    rw [InnerProductGeometry.cos_angle_mul_norm_mul_norm] at strict
    exact not_lt_of_ge scalar strict

/-- A nonobtuse angular cap is stable under all nonnegative combinations of its two banks. -/
theorem angle_le_of_inDirectionWedge_axis_bounds {axis u v x : E}
    (axis_ne : axis ≠ 0) (une : u ≠ 0) (vne : v ≠ 0) (xne : x ≠ 0)
    {θ : ℝ} (nonnegative : 0 ≤ θ) (small : θ ≤ Real.pi / 2)
    (first : InnerProductGeometry.angle axis u ≤ θ)
    (last : InnerProductGeometry.angle axis v ≤ θ) (inside : InDirectionWedge u v x) :
    InnerProductGeometry.angle axis x ≤ θ := by
  have below_pi : θ ≤ Real.pi := small.trans (by linarith [Real.pi_pos])
  have first_scalar := (angle_le_iff_cos_mul_norm_le axis_ne une nonnegative below_pi).mp first
  have last_scalar := (angle_le_iff_cos_mul_norm_le axis_ne vne nonnegative below_pi).mp last
  have cosine_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], small⟩
  obtain ⟨a, b, apos, bpos, expression⟩ := inside
  have norm_bound : ‖x‖ ≤ a * ‖u‖ + b * ‖v‖ := by
    rw [expression]
    calc
      _ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg apos, Real.norm_of_nonneg bpos]
  apply (angle_le_iff_cos_mul_norm_le axis_ne xne nonnegative below_pi).mpr
  calc
    _ = (Real.cos θ * ‖axis‖) * ‖x‖ := by ring
    _ ≤ (Real.cos θ * ‖axis‖) * (a * ‖u‖ + b * ‖v‖) :=
      mul_le_mul_of_nonneg_left norm_bound (mul_nonneg cosine_nonneg (norm_nonneg _))
    _ = a * (Real.cos θ * (‖axis‖ * ‖u‖)) +
        b * (Real.cos θ * (‖axis‖ * ‖v‖)) := by ring
    _ ≤ a * inner ℝ axis u + b * inner ℝ axis v :=
      add_le_add (mul_le_mul_of_nonneg_left first_scalar apos)
        (mul_le_mul_of_nonneg_left last_scalar bpos)
    _ = _ := by rw [expression, inner_add_right, real_inner_smul_right, real_inner_smul_right]

/-- Small angular perturbations preserve a strict side when the original cone has margin. -/
theorem inner_pos_of_angle_close {axis x y : E} {θ δ : ℝ}
    (inside : InnerProductGeometry.angle axis x ≤ θ)
    (close : InnerProductGeometry.angle x y < δ) (margin : θ + δ ≤ Real.pi / 2) :
    0 < inner ℝ axis y := by
  have triangle := InnerProductGeometry.angle_le_angle_add_angle axis x y
  by_contra nonpositive
  have outside := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp
    (le_of_not_gt nonpositive)
  linarith

end Unfoldings
