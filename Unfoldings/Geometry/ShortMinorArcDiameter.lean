module

public import Unfoldings.Geometry.MinorArcCone
public import Unfoldings.Geometry.AngleConeBound

/-! Angular extent of a short arc inside the hemisphere of either endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

theorem angle_left_le_side_angle_of_mem_closedMinorArc {u v x : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (short : angle u v ≤ π / 2)
    (hx : x ∈ closedMinorArc u v) : angle u x ≤ angle u v := by
  have nu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have nonnegative : 0 ≤ inner ℝ u v := by
    rw [inner_eq_cos_angle_of_norm_eq_one hu hv]
    apply cos_nonneg_of_mem_Icc
    exact ⟨by linarith [angle_nonneg u v, pi_pos], short⟩
  have upper : inner ℝ u v ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rw [hu, hv, one_mul] at h
    exact (le_abs_self _).trans h
  have nonantipodal : u + v ≠ 0 := by
    intro eq
    have contra := congrArg (inner ℝ u) eq
    rw [inner_add_right, nu, inner_zero_right] at contra
    linarith only [contra, nonnegative]
  obtain ⟨unit, a, b, ap, bp, position⟩ :=
    (mem_closedMinorArc_iff_nonnegative_combination hu hv nonantipodal).mp hx
  have sum : 1 ≤ a + b := by
    have length := norm_add_le (a • u) (b • v)
    rw [← position, unit, norm_smul, norm_smul, hu, hv, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ap, abs_of_nonneg bp, mul_one, mul_one] at length
    exact length
  have inner_le : inner ℝ u v ≤ inner ℝ u x := by
    rw [position, inner_add_right, real_inner_smul_right, real_inner_smul_right, nu, mul_one]
    have h := mul_le_mul_of_nonneg_right sum nonnegative
    have h' := mul_le_mul_of_nonneg_left upper ap
    nlinarith only [h, h']
  simp only [angle, hu, hv, unit, one_mul, div_one]
  exact Real.arccos_le_arccos inner_le

theorem angle_le_twice_side_angle_of_mem_closedMinorArc {u v x y : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (short : angle u v ≤ π / 2)
    (hx : x ∈ closedMinorArc u v) (hy : y ∈ closedMinorArc u v) :
    angle x y ≤ 2 * angle u v := by
  have first := angle_left_le_side_angle_of_mem_closedMinorArc hu hv short hx
  have last := angle_left_le_side_angle_of_mem_closedMinorArc hu hv short hy
  have triangle := angle_le_angle_add_angle x u y
  rw [angle_comm x u] at triangle
  linarith only [first, last, triangle]

end Unfoldings
