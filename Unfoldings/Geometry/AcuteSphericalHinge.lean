module

public import Unfoldings.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Tactic

/-! Two adjacent acute chord triangles of a spherical triangulation meet convexly. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

/-- An acute opposite angle places a unit vertex strictly below the plane
through the shared chord perpendicular to its midpoint vector. -/
theorem inner_midpoint_lt_self_of_acute_opposite {a b c : Space}
    (au : ‖a‖ = 1) (bu : ‖b‖ = 1) (cu : ‖c‖ = 1)
    (acute : angle (a - c) (b - c) < π / 2) :
    let m := (1 / 2 : ℝ) • (a + b)
    inner ℝ m c < inner ℝ m m := by
  have aa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, au, one_pow]
  have bb : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, bu, one_pow]
  have cc : inner ℝ c c = 1 := by rw [real_inner_self_eq_norm_sq, cu, one_pow]
  have pos : 0 < inner ℝ (a - c) (b - c) :=
    lt_of_not_ge (fun h => acute.not_ge (inner_nonpos_iff_pi_div_two_le_angle.mp h))
  rw [inner_sub_left, inner_sub_right, inner_sub_right, cc, real_inner_comm b c] at pos
  dsimp only
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    aa, bb, real_inner_comm a b]
  linarith only [pos]

/-- At two acute chord triangles on opposite radial sides of their shared chord,
the support plane of the first triangle strictly separates the second vertex.
This is the local convexity test for the radially subdivided mesh. -/
theorem exists_strict_support_of_acute_spherical_hinge {a b c d v : Space}
    (au : ‖a‖ = 1) (bu : ‖b‖ = 1) (cu : ‖c‖ = 1) (du : ‖d‖ = 1)
    (not_antipodal : a + b ≠ 0)
    (ortho_a : inner ℝ v a = 0) (ortho_b : inner ℝ v b = 0)
    (side_c : 0 < inner ℝ v c) (side_d : inner ℝ v d < 0)
    (acute_c : angle (a - c) (b - c) < π / 2)
    (acute_d : angle (a - d) (b - d) < π / 2) :
    ∃ n : Space, 0 < inner ℝ n a ∧ inner ℝ n a = inner ℝ n b ∧
      inner ℝ n a = inner ℝ n c ∧ inner ℝ n d < inner ℝ n a := by
  let m := (1 / 2 : ℝ) • (a + b)
  let k := (inner ℝ m m - inner ℝ m c) / inner ℝ v c
  have lower_c : inner ℝ m c < inner ℝ m m :=
    inner_midpoint_lt_self_of_acute_opposite au bu cu acute_c
  have lower_d : inner ℝ m d < inner ℝ m m :=
    inner_midpoint_lt_self_of_acute_opposite au bu du acute_d
  have kp : 0 < k := div_pos (sub_pos.mpr lower_c) side_c
  have aa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, au, one_pow]
  have bb : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, bu, one_pow]
  have ma : inner ℝ m a = inner ℝ m m := by
    simp only [m, real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      aa, bb, real_inner_comm a b]
    ring
  have mb : inner ℝ m b = inner ℝ m m := by
    simp only [m, real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      aa, bb, real_inner_comm a b]
    ring
  have m_ne : m ≠ 0 := smul_ne_zero (by norm_num) not_antipodal
  have mpos : 0 < inner ℝ m m := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr m_ne)
  refine ⟨m + k • v, ?_⟩
  simp only [inner_add_left, real_inner_smul_left, ortho_a, ortho_b, mul_zero, add_zero, ma, mb,
    true_and, mpos]
  have kc : k * inner ℝ v c = inner ℝ m m - inner ℝ m c :=
    div_mul_cancel₀ _ side_c.ne'
  exact ⟨by linarith only [kc], by linarith only [lower_d, mul_neg_of_pos_of_neg kp side_d]⟩

end Unfoldings
