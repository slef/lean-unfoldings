module

public import Unfoldings.FewestNets.IcosahedronModelGrid
public import Unfoldings.Geometry.RadialEquilateralAcute

/-! Every chord triangle used by either endpoint mesh is acute. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real MeshStar NormedSpace InnerProductGeometry

private theorem model_height_bounds :
    3 / 5 ≤ faceHeight ^ 2 ∧ (3 / 4 : ℝ) < faceHeight ∧ faceHeight ≤ 1 := by
  have sqrt_lower : (2 : ℝ) ≤ √5 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have sqrt_upper : √(5 : ℝ) ≤ 5 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsq := faceHeight_squared
  rw [faceHeightSq] at hsq
  have lower : 3 / 5 ≤ faceHeight ^ 2 := by linarith only [hsq, sqrt_lower]
  have nonnegative : 0 ≤ faceHeight := Real.sqrt_nonneg _
  refine ⟨lower, ?_, ?_⟩
  · apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) nonnegative).mp
    linarith only [lower]
  · apply (sq_le_sq₀ nonnegative (by norm_num : (0 : ℝ) ≤ 1)).mp
    linarith only [hsq, sqrt_upper]

private theorem icosahedronEdge_bounds : 0 < icosahedronEdge ∧ icosahedronEdge < 2 := by
  have sqr : (2 : ℝ) < √(10 + 2 * √5) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith only [Real.sqrt_nonneg 5]
  unfold icosahedronEdge
  exact ⟨div_pos (by norm_num) (by linarith only [sqr]),
    (div_lt_iff₀ (by linarith only [sqr])).mpr (by linarith only [sqr])⟩

private theorem mesh_edge_small {q : ℕ} (hq : 100 ≤ q) :
    2 * faceHeight ^ 2 * (icosahedronEdge / q) < (2 * faceHeight ^ 2 - 1) * faceHeight := by
  obtain ⟨hsq, h_lower, h_upper⟩ := model_height_bounds
  obtain ⟨edge_pos, edge_upper⟩ := icosahedronEdge_bounds
  have qlo : (100 : ℝ) ≤ q := by exact_mod_cast hq
  have qpos : (0 : ℝ) < q := by linarith only [qlo]
  have length : icosahedronEdge / q ≤ (1 / 50 : ℝ) := by
    rw [div_le_iff₀ qpos]
    linarith only [edge_upper, qlo]
  have height_square : faceHeight ^ 2 ≤ 1 :=
    (sq_le_sq₀ (by linarith only [h_lower]) (by norm_num : (0 : ℝ) ≤ 1)).mpr h_upper |>.trans_eq
      (by norm_num)
  have left : 2 * faceHeight ^ 2 * (icosahedronEdge / q) ≤ 2 * 1 * (1 / 50 : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left height_square (by norm_num)) length
      (div_nonneg edge_pos.le qpos.le) (by norm_num)
  have right : (1 / 5 : ℝ) * (3 / 4 : ℝ) ≤ (2 * faceHeight ^ 2 - 1) * faceHeight :=
    mul_le_mul (by linarith only [hsq]) h_lower.le (by norm_num) (by linarith only [hsq])
  linarith only [left, right]

/-- All three angles of every normalized fine triangle are acute for both
frequencies in the paper, by one uniform analytic inequality. -/
theorem angle_inscribedCorners_lt_pi_div_two {q : ℕ} (hq : 100 ≤ q)
    (t : MeshFace q) (a b c : Fin 3) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    angle (inscribedCorners t b - inscribedCorners t a)
      (inscribedCorners t c - inscribedCorners t a) < π / 2 := by
  have qpos : 0 < q := by omega
  obtain ⟨_, h_lower, h_upper⟩ := model_height_bounds
  have model := angle_normalized_edges_lt_pi_div_two_of_equilateral modelNormal_unit
    (inner_modelNormal_modelGridCorners t.2 a) (inner_modelNormal_modelGridCorners t.2 b)
    (inner_modelNormal_modelGridCorners t.2 c)
    (norm_modelGridCorners_le_one qpos t.2 a) (norm_modelGridCorners_le_one qpos t.2 b)
    (norm_modelGridCorners_le_one qpos t.2 c)
    (by linarith only [h_lower]) h_upper (div_pos icosahedronEdge_bounds.1 (by exact_mod_cast qpos))
    (norm_sub_modelGridCorners t.2 ab.symm) (norm_sub_modelGridCorners t.2 ac.symm)
    (norm_sub_modelGridCorners t.2 bc) (mesh_edge_small hq)
  obtain ⟨e, he⟩ := exists_modelGrid_isometry t
  rw [← he a, ← he b, ← he c, ← map_sub, ← map_sub]
  exact (e.toLinearIsometry.angle_map _ _).trans_lt model

end Unfoldings.FewestNets.Icosahedron
