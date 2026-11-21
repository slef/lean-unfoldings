module

public import Unfoldings.FewestNets.MeshBisectors
public import Unfoldings.FewestNets.CountConstants

/-! Metric identities for the representative icosahedral face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

private theorem faceHeightSq_pos : 0 < faceHeightSq := by
  unfold faceHeightSq
  positivity

private theorem faceHeightSq_lt_one : faceHeightSq < 1 := by
  unfold faceHeightSq
  have h : Real.sqrt 5 < 5 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  linarith

theorem faceHeight_squared : faceHeight ^ 2 = faceHeightSq :=
  Real.sq_sqrt faceHeightSq_pos.le

theorem faceScale_squared : faceScale ^ 2 = (1 - faceHeightSq) / 4 :=
  Real.sq_sqrt (by linarith [faceHeightSq_lt_one])

private theorem sum_face_corner_sq :
    (Real.sqrt 3 * faceScale) ^ 2 + faceScale ^ 2 + faceHeight ^ 2 = 1 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), faceScale_squared, faceHeight_squared]
  ring

theorem cornerA_unit : ‖cornerA‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change (-(Real.sqrt 3 * faceScale)) ^ 2 + (-faceScale) ^ 2 + faceHeight ^ 2 = 1 ^ 2
  simpa only [neg_sq, one_pow] using sum_face_corner_sq

theorem cornerB_unit : ‖cornerB‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change (Real.sqrt 3 * faceScale) ^ 2 + (-faceScale) ^ 2 + faceHeight ^ 2 = 1 ^ 2
  simpa only [neg_sq, one_pow] using sum_face_corner_sq

theorem cornerC_unit : ‖cornerC‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change (0 : ℝ) ^ 2 + (2 * faceScale) ^ 2 + faceHeight ^ 2 = 1 ^ 2
  rw [mul_pow, faceScale_squared, faceHeight_squared]
  ring

private theorem face_inner_constant : faceHeight ^ 2 - 2 * faceScale ^ 2 = Real.sqrt 5 / 5 := by
  rw [faceScale_squared, faceHeight_squared, faceHeightSq]
  ring

/-- The three pairs have the same angular distance on the unit sphere. -/
theorem corner_pair_inner :
    inner ℝ cornerA cornerB = Real.sqrt 5 / 5 ∧
      inner ℝ cornerB cornerC = Real.sqrt 5 / 5 ∧
      inner ℝ cornerC cornerA = Real.sqrt 5 / 5 := by
  simp only [inner_eq_coordinate_dotProduct, dotProduct, Fin.sum_univ_three]
  change (-(Real.sqrt 3 * faceScale) * (Real.sqrt 3 * faceScale) +
      (-faceScale) * (-faceScale) + faceHeight * faceHeight = _) ∧
    ((Real.sqrt 3 * faceScale) * 0 + (-faceScale) * (2 * faceScale) +
      faceHeight * faceHeight = _) ∧
    (0 * (-(Real.sqrt 3 * faceScale)) + (2 * faceScale) * (-faceScale) +
      faceHeight * faceHeight = _)
  have sq3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have prod : (Real.sqrt 3 * faceScale) ^ 2 = 3 * faceScale ^ 2 := by rw [mul_pow, sq3]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [prod, face_inner_constant]

/-- The step used in the side-length certificates is the original face edge
divided by the subdivision frequency. -/
theorem norm_stepU (q : ℕ) : ‖stepU q‖ = icosahedronEdge / q := by
  rw [stepU, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
  congr 1
  apply (sq_eq_sq₀ (norm_nonneg _) (by unfold icosahedronEdge; positivity)).mp
  rw [norm_sub_pow_two_real, cornerA_unit, cornerB_unit,
    real_inner_comm cornerA cornerB, corner_pair_inner.1, icosahedronEdge, div_pow,
    Real.sq_sqrt (by positivity)]
  have sq5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have positive : 0 < 10 + 2 * Real.sqrt 5 := by positivity
  apply (eq_div_iff positive.ne').mpr
  nlinarith only [sq5]

end Unfoldings.FewestNets.MeshStar
