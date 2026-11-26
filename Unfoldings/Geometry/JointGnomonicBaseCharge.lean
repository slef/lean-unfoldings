module

public import Unfoldings.Geometry.GnomonicBaseCorner

/-! Joint base-corner estimate retaining the cancellation between symmetric endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real InnerProductGeometry

/-- The analytic upper bound on a capped reciprocal sine in terms of its cotangent. -/
theorem cappedReciprocalSine_le_cotangent {θ : ℝ} (positive : 0 < θ) :
    1 / sin (min θ (π / 2)) ≤ 1 + (|cos θ| / sin θ) ^ 2 / 2 := by
  by_cases right : π / 2 ≤ θ
  · rw [min_eq_right right, sin_pi_div_two, div_one]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_left (le_of_not_ge right)]
    have sp := sin_pos_of_pos_of_lt_pi positive (by linarith only [lt_of_not_ge right, pi_pos])
    let c := (|cos θ| / sin θ) ^ 2
    have exact_sq : (1 / sin θ) ^ 2 = 1 + c := by
      dsimp only [c]
      rw [div_pow, div_pow, sq_abs, one_pow]
      field_simp [sp.ne']
      nlinarith only [sin_sq_add_cos_sq θ]
    have rhs : 0 ≤ 1 + c / 2 := by dsimp only [c]; positivity
    change 1 / sin θ ≤ 1 + c / 2
    apply (sq_le_sq₀ (by positivity) rhs).mp
    rw [exact_sq]
    nlinarith only [sq_nonneg c]

local notation "site" => fun x y : ℝ => gnomonicNormal (WithLp.toLp 2 ![x, y] : Plane)

/-- Symmetric base endpoints cancel the mixed terms in their squared cotangents. -/
theorem joint_gnomonic_base_cotangent_bound (X Y A B : ℝ)
    (Xp : 0 < X) (height : B ≠ Y) (cross : |1 + Y * B| ≤ 1) :
    let L := site (-X) Y
    let R := site X Y
    let P := site A B
    let θ := angle (minorArcTangent L R) (minorArcTangent L P)
    let ψ := angle (minorArcTangent R L) (minorArcTangent R P)
    ((|cos θ| / sin θ) ^ 2 + (|cos ψ| / sin ψ) ^ 2) / 2 ≤
      (A ^ 2 * (1 + Y ^ 2) + X ^ 2) / (B - Y) ^ 2 := by
  have width : (2 * X : ℝ) ≠ 0 := (mul_pos (by norm_num) Xp).ne'
  have l := abs_cot_gnomonic_baseCorner (-X) Y A B (2 * X) width height
  have r := abs_cot_gnomonic_baseCorner X Y A B (-2 * X)
    (by linarith only [Xp]) height
  dsimp only at l r ⊢
  rw [show -X + 2 * X = X by ring, neg_sq] at l
  rw [show X + -2 * X = -X by ring] at r
  rw [l, r]
  simp only [div_pow, mul_pow, sq_abs, sq_sqrt (by positivity : 0 ≤ 1 + X ^ 2 + Y ^ 2)]
  let d := (B - Y) ^ 2
  let h := 1 + X ^ 2 + Y ^ 2
  let p := A ^ 2 * (1 + Y ^ 2) + X ^ 2
  have dp : 0 < d := sq_pos_of_ne_zero (sub_ne_zero.mpr height)
  have hp : 0 < h := by dsimp only [h]; positivity
  have pp : 0 ≤ p := by dsimp only [p]; positivity
  have form : (((A * (1 + Y ^ 2) - -X * (1 + Y * B)) ^ 2 / (d * h)) +
      ((A * (1 + Y ^ 2) - X * (1 + Y * B)) ^ 2 / (d * h))) / 2 =
      (A ^ 2 * (1 + Y ^ 2) ^ 2 + X ^ 2 * (1 + Y * B) ^ 2) / (d * h) := by ring
  change _ ≤ p / d
  rw [form]
  have bounded : (1 + Y * B) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) cross 2
    simpa only [sq_abs, one_pow] using h
  have h₁ : 1 + Y ^ 2 ≤ h := by dsimp only [h]; nlinarith only [sq_nonneg X]
  have h₂ : 1 ≤ h := by dsimp only [h]; linarith only [sq_nonneg X, sq_nonneg Y]
  have a_mul := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ A ^ 2 * (1 + Y ^ 2) by positivity)
  have x_mul := mul_le_mul_of_nonneg_left (bounded.trans h₂) (sq_nonneg X)
  have bound : A ^ 2 * (1 + Y ^ 2) ^ 2 + X ^ 2 * (1 + Y * B) ^ 2 ≤ p * h := by
    dsimp only [p]
    nlinarith only [a_mul, x_mul]
  apply (div_le_iff₀ (mul_pos dp hp)).mpr
  convert bound using 1
  field_simp [dp.ne']

end Unfoldings.Cap
