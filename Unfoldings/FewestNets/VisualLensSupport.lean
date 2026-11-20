module

public import Unfoldings.FewestNets.VisualCertificate

/-! Sound analytic support bounds for the closed forbidden lenses. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

/-- Points in the closed forbidden lens obey both the parent-disk bound and,
when the side normal is sufficiently close to the chord, the endpoint bound.
The parent-disk bound is valid even if an interval comparison cannot select a branch. -/
theorem visualLens_support_bounds {m v p n : E} {c : ℝ} (c_nonneg : 0 ≤ c) (v_ne : v ≠ 0)
    (inside : inner ℝ (p - (m - v)) (p - (m + v)) +
      c * |o.areaForm (p - (m - v)) (p - (m + v))| ≤ 0) :
    (inner ℝ n p ≤ inner ℝ n m + (‖v‖ * Real.sqrt (1 + c ^ 2)) * ‖n‖ -
      c * |o.areaForm v n|) ∧
    (|o.areaForm v n| ≤ c * |inner ℝ n v| →
      inner ℝ n p ≤ inner ℝ n m + |inner ℝ n v|) := by
  let z := p - m
  let R := ‖v‖ ^ 2
  let X := |inner ℝ v z|
  let Y := |o.areaForm v z|
  let A := |inner ℝ n v|
  let B := |o.areaForm v n|
  have R_pos : 0 < R := pow_pos (norm_pos_iff.mpr v_ne) _
  have x_nonneg : 0 ≤ X := abs_nonneg _
  have y_nonneg : 0 ≤ Y := abs_nonneg _
  have a_nonneg : 0 ≤ A := abs_nonneg _
  have b_nonneg : 0 ≤ B := abs_nonneg _
  have symmetry : inner ℝ v n = inner ℝ n v := real_inner_comm n v
  have pythagoras : X ^ 2 + Y ^ 2 = R * ‖z‖ ^ 2 := by
    simpa only [X, Y, sq_abs, R] using o.inner_sq_add_areaForm_sq v z
  have normal_pythagoras : A ^ 2 + B ^ 2 = R * ‖n‖ ^ 2 := by
    simpa only [A, B, sq_abs, ← symmetry, R] using o.inner_sq_add_areaForm_sq v n
  have lens : ‖z‖ ^ 2 - R + 2 * c * Y ≤ 0 := by
    rw [show p - (m - v) = z + v by dsimp [z]; abel,
      show p - (m + v) = z - v by dsimp [z]; abel] at inside
    have dot : inner ℝ (z + v) (z - v) = ‖z‖ ^ 2 - R := by
      simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_comm z v, R]
      ring
    have det : o.areaForm (z + v) (z - v) = 2 * o.areaForm v z := by
      simp only [map_add, LinearMap.add_apply, map_sub, o.areaForm_apply_self,
        o.areaForm_swap z v]
      ring
    rw [dot, det, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at inside
    unfold Y
    linarith
  have ellipse : X ^ 2 + Y ^ 2 + 2 * c * R * Y ≤ R ^ 2 := by
    rw [pythagoras]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos R_pos.le lens]
  have dot_bound : R * inner ℝ n z ≤ A * X + B * Y := by
    rw [← o.inner_mul_inner_add_areaForm_mul_areaForm v n z, symmetry]
    exact add_le_add (le_abs_self _ |>.trans_eq (abs_mul _ _))
      (le_abs_self _ |>.trans_eq (abs_mul _ _))
  have center : inner ℝ n p = inner ℝ n m + inner ℝ n z := by
    rw [show p = m + z by dsimp [z]; abel, inner_add_right]
  rw [center]
  constructor
  · let H := Y + c * R
    have H_nonneg : 0 ≤ H := add_nonneg y_nonneg (mul_nonneg c_nonneg R_pos.le)
    have squared : X ^ 2 + H ^ 2 ≤ (1 + c ^ 2) * R ^ 2 := by
      dsimp [H]
      nlinarith [ellipse]
    have cs : (A * X + B * H) ^ 2 ≤ (A ^ 2 + B ^ 2) * (X ^ 2 + H ^ 2) := by
      nlinarith [sq_nonneg (A * H - B * X)]
    have target : (A * X + B * H) ^ 2 ≤
        (R * ((‖v‖ * Real.sqrt (1 + c ^ 2)) * ‖n‖)) ^ 2 := by
      apply cs.trans
      rw [normal_pythagoras, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        show ‖v‖ ^ 2 = R from rfl]
      have h := mul_le_mul_of_nonneg_left squared (show 0 ≤ R * ‖n‖ ^ 2 by positivity)
      nlinarith only [h]
    have support := (sq_le_sq₀ (add_nonneg (mul_nonneg a_nonneg x_nonneg)
      (mul_nonneg b_nonneg H_nonneg)) (by positivity)).mp target
    have bound : R * inner ℝ n z ≤ R * ((‖v‖ * Real.sqrt (1 + c ^ 2)) * ‖n‖ - c * B) := by
      dsimp [H] at support
      nlinarith [dot_bound, support]
    have result := le_of_mul_le_mul_left bound R_pos
    change inner ℝ n m + inner ℝ n z ≤
      inner ℝ n m + (‖v‖ * Real.sqrt (1 + c ^ 2)) * ‖n‖ - c * B
    linarith
  · intro branch
    change B ≤ c * A at branch
    have X_le : X ≤ R := by
      apply (sq_le_sq₀ x_nonneg R_pos.le).mp
      nlinarith [sq_nonneg Y, mul_nonneg (mul_nonneg c_nonneg R_pos.le) y_nonneg]
    have slope : c * Y ≤ R - X := by
      apply le_of_mul_le_mul_left (a := 2 * R) _ (by positivity)
      nlinarith [ellipse, sq_nonneg Y, sq_nonneg (R - X)]
    have bound : A * X + B * Y ≤ R * A := by
      calc
        _ ≤ A * X + (c * A) * Y := add_le_add_right
          (mul_le_mul_of_nonneg_right branch y_nonneg) _
        _ = A * (X + c * Y) := by ring
        _ ≤ A * R := mul_le_mul_of_nonneg_left (by linarith) a_nonneg
        _ = _ := mul_comm _ _
    exact add_le_add_right (le_of_mul_le_mul_left (dot_bound.trans bound) R_pos) _

end Unfoldings.FewestNets
