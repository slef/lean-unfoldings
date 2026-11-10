module

public import Unfoldings.Geometry.TriangleAffine
public import Unfoldings.Geometry.AcuteProgress

/-!
# Uniformly small shears preserve an acute angle margin

The inverse image of a quadrant under a positive shear is narrower than a
right angle. A uniform acute-margin estimate therefore turns quadrant progress
into strict acute-wedge progress without a bound depending on the mesh size.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A shear whose positive quadrant pulls back to the wedge `y > 0`, `x > t*y`. -/
def quadrantShear (t : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun v := WithLp.toLp 2 ![v 0 - t * v 1, v 1]
  map_add' _ _ := by ext i; fin_cases i <;> simp; ring
  map_smul' _ _ := by ext i; fin_cases i <;> simp; ring

@[simp] theorem quadrantShear_zero (t : ℝ) (v : Plane) :
    quadrantShear t v 0 = v 0 - t * v 1 := rfl

@[simp] theorem quadrantShear_one (t : ℝ) (v : Plane) : quadrantShear t v 1 = v 1 := rfl

theorem quadrantShear_injective (t : ℝ) : Function.Injective (quadrantShear t) := by
  intro v w equal
  have first := congrArg (fun p : Plane => p 0) equal
  have last := congrArg (fun p : Plane => p 1) equal
  simp only [quadrantShear_zero, quadrantShear_one] at first last
  ext i
  fin_cases i
  · change v 0 = w 0
    rw [last] at first
    linarith
  · exact last

theorem unit_plane_coordinate_bound (v : Plane) (unit : ‖v‖ = 1) (i : Fin 2) : |v i| ≤ 1 := by
  have identity : (v 0) ^ 2 + (v 1) ^ 2 = 1 := by
    have norm := EuclideanSpace.real_norm_sq_eq v
    rw [unit, Fin.sum_univ_two] at norm
    simpa only [one_pow] using norm.symm
  fin_cases i
  · change |v 0| ≤ 1
    nlinarith [sq_nonneg (v 1), sq_abs (v 0), abs_nonneg (v 0)]
  · change |v 1| ≤ 1
    nlinarith [sq_nonneg (v 0), sq_abs (v 1), abs_nonneg (v 1)]

/-- A mesh-independent scalar-product error for unit directions. -/
theorem quadrantShear_inner_lower (u v : Plane) (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
    {t : ℝ} (nonnegative : 0 ≤ t) :
    inner ℝ u v - (2 * t + t ^ 2) ≤ inner ℝ (quadrantShear t u) (quadrantShear t v) := by
  have product (i j : Fin 2) : |u i * v j| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (unit_plane_coordinate_bound u uu i)
      (unit_plane_coordinate_bound v vu j) (abs_nonneg _) zero_le_one
  have cross : u 0 * v 1 + u 1 * v 0 ≤ 2 := by
    linarith [(le_abs_self (u 0 * v 1)).trans (product 0 1),
      (le_abs_self (u 1 * v 0)).trans (product 1 0)]
  have lower : -1 ≤ u 1 * v 1 := (abs_le.mp (product 1 1)).1
  have first := mul_le_mul_of_nonneg_left cross nonnegative
  have last := mul_le_mul_of_nonneg_left lower (sq_nonneg t)
  have expression : inner ℝ (quadrantShear t u) (quadrantShear t v) =
      inner ℝ u v - t * (u 0 * v 1 + u 1 * v 0) + t ^ 2 * (u 1 * v 1) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
      quadrantShear_zero, quadrantShear_one]
    ring
  linarith

/-- One positive shear works for every pair of directions with a prescribed acute margin. -/
theorem exists_acute_quadrantShear {α : ℝ} (positive : 0 < α) (small : α < Real.pi / 2) :
    ∃ t > 0, ∀ u v : Plane, u ≠ 0 → v ≠ 0 →
      InnerProductGeometry.angle u v ≤ Real.pi / 2 - α →
      0 < inner ℝ (quadrantShear t u) (quadrantShear t v) := by
  have sinpos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi positive (by linarith)
  let t : ℝ := min (Real.sin α / 8) (1 / 4)
  have tpos : 0 < t := lt_min (by positivity) (by norm_num)
  have tone : t ≤ 1 / 4 := min_le_right _ _
  have tsin : t ≤ Real.sin α / 8 := min_le_left _ _
  have error : 2 * t + t ^ 2 < Real.sin α := by
    nlinarith [mul_le_mul_of_nonneg_left tone tpos.le]
  have unit_bound (u v : Plane) (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
      (acute : InnerProductGeometry.angle u v ≤ Real.pi / 2 - α) :
      0 < inner ℝ (quadrantShear t u) (quadrantShear t v) := by
    have cosine := Real.cos_le_cos_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg u v) (by linarith [Real.pi_pos]) acute
    rw [Real.cos_pi_div_two_sub] at cosine
    rw [← InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one uu vu] at cosine
    linarith [quadrantShear_inner_lower u v uu vu tpos.le]
  refine ⟨t, tpos, fun u v un vn acute => ?_⟩
  have result := unit_bound (NormedSpace.normalize u) (NormedSpace.normalize v)
    (NormedSpace.norm_normalize un) (NormedSpace.norm_normalize vn)
    (by simpa only [InnerProductGeometry.angle_normalize_left,
      InnerProductGeometry.angle_normalize_right] using acute)
  simp only [NormedSpace.normalize, map_smul, real_inner_smul_left, inner_smul_right] at result
  by_contra nonpositive
  have bound := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg u))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg v))
      (le_of_not_gt nonpositive))
  exact (not_lt_of_ge bound) (by simpa only [mul_left_comm] using result)

end Unfoldings
