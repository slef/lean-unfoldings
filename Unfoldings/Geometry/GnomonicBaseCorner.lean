module

public import Unfoldings.Geometry.GnomonicCornerAngles

/-! Exact inverse-gnomonic base angles for a horizontal chart edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real InnerProductGeometry

local notation "point" => fun x y : ℝ => (WithLp.toLp 2 ![x, y] : Plane)

/-- The absolute cotangent is independent of the length and direction of
the outgoing horizontal base edge. -/
theorem abs_cot_gnomonic_baseCorner (X Y A B k : ℝ) (kn : k ≠ 0) (hn : B ≠ Y) :
    let p := point X Y
    let q := point (X + k) Y
    let r := point A B
    let n := gnomonicNormal p
    let θ := angle (minorArcTangent n (gnomonicNormal q)) (minorArcTangent n (gnomonicNormal r))
    |cos θ| / sin θ =
      |A * (1 + Y ^ 2) - X * (1 + Y * B)| / (|B - Y| * √(1 + X ^ 2 + Y ^ 2)) := by
  let p := point X Y
  let q := point (X + k) Y
  let r := point A B
  let n := gnomonicNormal p
  let d := √(1 + X ^ 2 + Y ^ 2)
  have dp : 0 < d := sqrt_pos.mpr (by positivity)
  have d_sq : d ^ 2 = 1 + X ^ 2 + Y ^ 2 := sq_sqrt (by positivity)
  have nx : q ≠ p := by
    intro eq
    have h := congrArg (fun z : Plane => z 0) eq
    change X + k = X at h
    exact kn (by linarith only [h])
  have ny : r ≠ p := fun eq => hn (congrArg (fun z : Plane => z 1) eq)
  have base : q - p = point k 0 := by
    ext i
    fin_cases i
    · change X + k - X = k
      ring
    · change Y - Y = 0
      ring
  have side : r - p = point (A - X) (B - Y) := by ext i; fin_cases i <;> rfl
  have det : orient 0 (q - p) (r - p) = k * (B - Y) := by
    rw [base, side]
    simp [orient]
  have norm_eq : ‖northLift p‖ = d := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    change √(|X| ^ 2 + |Y| ^ 2 + |(1 : ℝ)| ^ 2) = d
    rw [sq_abs, sq_abs, abs_one, one_pow]
    congr 1
    ring
  have scale : n = d⁻¹ • northLift p := by unfold n gnomonicNormal NormedSpace.normalize; rw [norm_eq]
  have height : n 2 = d⁻¹ := by rw [scale]; exact mul_one _
  have h : horizontal n = d⁻¹ • p := by rw [scale, map_smul, northLift_horizontal]
  have metric :
      inner ℝ (q - p) (r - p) - inner ℝ (horizontal n) (q - p) * inner ℝ (horizontal n) (r - p) =
        (k / d ^ 2) * (A * (1 + Y ^ 2) - X * (1 + Y * B)) := by
    rw [base, side, h, real_inner_smul_left, real_inner_smul_left]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
    change k * (A - X) + 0 * (B - Y) - (d⁻¹ * (X * k + Y * 0)) *
      (d⁻¹ * (X * (A - X) + Y * (B - Y))) = _
    field_simp [dp.ne']
    linear_combination k * (A - X) * d_sq
  have exact_angle := abs_cot_gnomonic_corner p q r nx ny (det.symm ▸ mul_ne_zero kn (sub_ne_zero.mpr hn))
  dsimp only at exact_angle
  change _ = _
  rw [exact_angle]
  change |inner ℝ (q - p) (r - p) - inner ℝ (horizontal n) (q - p) * inner ℝ (horizontal n) (r - p)| /
      (n 2 * |orient 0 (q - p) (r - p)|) = _
  rw [metric, height, det, abs_mul, abs_mul, abs_div, abs_of_pos (pow_pos dp _)]
  field_simp [dp.ne', abs_ne_zero.mpr kn, abs_ne_zero.mpr (sub_ne_zero.mpr hn)]
  <;> ring

end Unfoldings.Cap
