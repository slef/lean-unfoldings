module

public import Unfoldings.Geometry.ThreeSectorRays

/-! One positive sector parameter preserves every triangle with the supplied acute margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def threeSectorDerivative (i : Fin 3) : Plane →ₗ[ℝ] Plane :=
  threeSectorCoordinates 1 i - threeSectorCoordinates 0 i

theorem threeSectorCoordinates_decompose (t : ℝ) (i : Fin 3) (v : Plane) :
    threeSectorCoordinates t i v =
      threeSectorCoordinates 0 i v + t • threeSectorDerivative i v := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [threeSectorDerivative, threeSectorCoordinates] <;> ring

theorem threeSectorCoordinates_zero_inner (i : Fin 3) (u v : Plane) :
    inner ℝ (threeSectorCoordinates 0 i u) (threeSectorCoordinates 0 i v) = 2 * inner ℝ u v := by
  fin_cases i <;> norm_num [threeSectorCoordinates, PiLp.inner_apply, Fin.sum_univ_two] <;> ring

theorem threeSectorCoordinates_zero_norm_le (i : Fin 3) {v : Plane} (unit : ‖v‖ = 1) :
    ‖threeSectorCoordinates 0 i v‖ ≤ 2 := by
  have square := threeSectorCoordinates_zero_inner i v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, unit] at square
  nlinarith [norm_nonneg (threeSectorCoordinates 0 i v)]

theorem threeSectorDerivative_norm_le (i : Fin 3) {v : Plane} (unit : ‖v‖ = 1) :
    ‖threeSectorDerivative i v‖ ≤ 2 := by
  have coords : (v 0) ^ 2 + (v 1) ^ 2 = 1 := by
    have norm := EuclideanSpace.real_norm_sq_eq v
    rw [unit, Fin.sum_univ_two] at norm
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using norm.symm
  have bound : ‖threeSectorDerivative i v‖ ^ 2 ≤ 4 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    fin_cases i <;> norm_num [threeSectorDerivative, threeSectorCoordinates,
      Real.norm_eq_abs, sq_abs]
    all_goals nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 + v 1)]
  nlinarith [norm_nonneg (threeSectorDerivative i v)]

theorem threeSector_inner_lower (i : Fin 3) (u v : Plane) (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
    {t : ℝ} (nonnegative : 0 ≤ t) :
    2 * inner ℝ u v - (8 * t + 4 * t ^ 2) ≤
      inner ℝ (threeSectorCoordinates t i u) (threeSectorCoordinates t i v) := by
  have pairing (x y : Plane) (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) : -4 ≤ inner ℝ x y := by
    have absolute := abs_real_inner_le_norm x y
    have product : ‖x‖ * ‖y‖ ≤ 4 := by
      simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using
        mul_le_mul hx hy (norm_nonneg y) (by norm_num : (0 : ℝ) ≤ 2)
    linarith [neg_abs_le (inner ℝ x y)]
  have first := mul_le_mul_of_nonneg_left (pairing _ _
    (threeSectorCoordinates_zero_norm_le i uu) (threeSectorDerivative_norm_le i vu)) nonnegative
  have second := mul_le_mul_of_nonneg_left (pairing _ _
    (threeSectorDerivative_norm_le i uu) (threeSectorCoordinates_zero_norm_le i vu)) nonnegative
  have third := mul_le_mul_of_nonneg_left (pairing _ _
    (threeSectorDerivative_norm_le i uu) (threeSectorDerivative_norm_le i vu)) (sq_nonneg t)
  rw [threeSectorCoordinates_decompose t i u, threeSectorCoordinates_decompose t i v,
    inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    threeSectorCoordinates_zero_inner]
  nlinarith

/-- A positive parameter below one quarter works before any triangle or mesh is supplied. -/
theorem exists_acute_threeSectorCoordinates {α : ℝ} (positive : 0 < α) (small : α < Real.pi / 2) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ (i : Fin 3) (u v : Plane), u ≠ 0 → v ≠ 0 →
      InnerProductGeometry.angle u v ≤ Real.pi / 2 - α →
        0 < inner ℝ (threeSectorCoordinates t i u) (threeSectorCoordinates t i v) := by
  have sinpos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi positive (by linarith)
  let t : ℝ := min (Real.sin α / 16) (1 / 8)
  have tpos : 0 < t := lt_min (by positivity) (by norm_num)
  have smallt : t ≤ 1 / 8 := min_le_right _ _
  have tsin : t ≤ Real.sin α / 16 := min_le_left _ _
  have error : 8 * t + 4 * t ^ 2 < Real.sin α := by
    nlinarith [mul_le_mul_of_nonneg_left smallt tpos.le]
  have unit_bound (i : Fin 3) (u v : Plane) (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
      (acute : InnerProductGeometry.angle u v ≤ Real.pi / 2 - α) :
      0 < inner ℝ (threeSectorCoordinates t i u) (threeSectorCoordinates t i v) := by
    have cosine := Real.cos_le_cos_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg u v) (by linarith [Real.pi_pos]) acute
    rw [Real.cos_pi_div_two_sub, ← InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one uu vu]
      at cosine
    linarith [threeSector_inner_lower i u v uu vu tpos.le]
  refine ⟨t, ⟨tpos, by linarith⟩, fun i u v un vn acute => ?_⟩
  have result := unit_bound i (NormedSpace.normalize u) (NormedSpace.normalize v)
    (NormedSpace.norm_normalize un) (NormedSpace.norm_normalize vn)
    (by simpa only [InnerProductGeometry.angle_normalize_left,
      InnerProductGeometry.angle_normalize_right] using acute)
  simp only [NormedSpace.normalize, map_smul, real_inner_smul_left, real_inner_smul_right] at result
  by_contra nonpositive
  have bound := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg u))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg v)) (le_of_not_gt nonpositive))
  exact (not_lt_of_ge bound) (by simpa only [mul_left_comm] using result)

end Unfoldings
