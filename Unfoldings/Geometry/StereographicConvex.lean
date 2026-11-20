module

public import Unfoldings.Geometry.NorthFrame

/-! The north-centered stereographic chart takes hemispheres through or
containing its center to convex planar regions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open scoped BigOperators

/-- The paper's normalization of inverse stereographic projection from the south pole. -/
def inverseStereographic (x : Plane) : Space :=
  (2 / (1 + ‖x‖ ^ 2)) • horizontalLift x +
    ((1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2)) • northLift 0

theorem horizontal_inverseStereographic (x : Plane) :
    horizontal (inverseStereographic x) = (2 / (1 + ‖x‖ ^ 2)) • x := by
  rw [inverseStereographic, map_add, map_smul, map_smul, northLift_horizontal, smul_zero, add_zero]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem inverseStereographic_height (x : Plane) :
    inverseStereographic x 2 = (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2) := by
  change (2 / (1 + ‖x‖ ^ 2)) * (0 : ℝ) +
    ((1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2)) * 1 = _
  ring

theorem inverseStereographic_unit (x : Plane) : ‖inverseStereographic x‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [horizontal_norm_sq, horizontal_inverseStereographic, norm_smul,
    Real.norm_of_nonneg (by positivity), inverseStereographic_height]
  field_simp [show 1 + ‖x‖ ^ 2 ≠ 0 by positivity]
  ring

theorem inverseStereographic_origin : inverseStereographic 0 = northLift 0 := by
  simp [inverseStereographic]

/-- Only the unit disk maps to the open north-centered hemisphere. -/
theorem inverseStereographic_upward_iff (x : Plane) :
    0 < inverseStereographic x 2 ↔ ‖x‖ < 1 := by
  rw [inverseStereographic_height,
    div_pos_iff_of_pos_right (show 0 < 1 + ‖x‖ ^ 2 by positivity), sub_pos]
  simpa only [one_pow] using (sq_lt_sq₀ (norm_nonneg x) (zero_le_one : (0 : ℝ) ≤ 1))

theorem inverseStereographic_inner (n : Space) (x : Plane) :
    inner ℝ n (inverseStereographic x) =
      (2 * inner ℝ (horizontal n) x + n 2 * (1 - ‖x‖ ^ 2)) / (1 + ‖x‖ ^ 2) := by
  rw [horizontal_inner, horizontal_inverseStereographic, inverseStereographic_height,
    real_inner_smul_right]
  ring

/-- The preimage of a hemisphere containing the north pole is convex.
Its defining quadratic has a nonnegative coefficient on squared norm. -/
theorem convex_inverseStereographic_hemisphere (n : Space) (up : 0 ≤ n 2) :
    Convex ℝ {x | 0 ≤ inner ℝ n (inverseStereographic x)} := by
  have equal : {x | 0 ≤ inner ℝ n (inverseStereographic x)} =
      {x | n 2 * ‖x‖ ^ 2 ≤ 2 * inner ℝ (horizontal n) x + n 2} := by
    ext x
    simp only [Set.mem_ofPred_eq, inverseStereographic_inner]
    have den : 0 < 1 + ‖x‖ ^ 2 := by positivity
    constructor
    · intro h
      have hh : 0 / (1 + ‖x‖ ^ 2) ≤
          (2 * inner ℝ (horizontal n) x + n 2 * (1 - ‖x‖ ^ 2)) / (1 + ‖x‖ ^ 2) := by
        simpa only [zero_div] using h
      nlinarith only [(div_le_div_iff_of_pos_right den).mp hh]
    · intro h
      exact div_nonneg (by nlinarith only [h]) den.le
  rw [equal]
  intro x hx y hy a b ha hb total
  have norm_convex :
      ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
    have bound : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      simpa only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using
        norm_add_le (a • x) (b • y)
    have square := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 bound
    have cross := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖x‖ - ‖y‖))
    have weights := congrArg (fun t : ℝ => t * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2)) total
    nlinarith only [square, cross, weights]
  change n 2 * ‖x‖ ^ 2 ≤ 2 * inner ℝ (horizontal n) x + n 2 at hx
  change n 2 * ‖y‖ ^ 2 ≤ 2 * inner ℝ (horizontal n) y + n 2 at hy
  change n 2 * ‖a • x + b • y‖ ^ 2 ≤
    2 * inner ℝ (horizontal n) (a • x + b • y) + n 2
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have weight := congrArg (fun t : ℝ => t * n 2) total
  nlinarith only [mul_le_mul_of_nonneg_left norm_convex up,
    mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb, weight]

/-- Any intersection of hemispheres containing the chart center has a convex preimage. -/
theorem convex_inverseStereographic_region {I : Sort*} (normal : I → Space)
    (up : ∀ i, 0 ≤ normal i 2) :
    Convex ℝ {x | ∀ i, 0 ≤ inner ℝ (normal i) (inverseStereographic x)} := by
  rw [show {x | ∀ i, 0 ≤ inner ℝ (normal i) (inverseStereographic x)} =
    ⋂ i, {x | 0 ≤ inner ℝ (normal i) (inverseStereographic x)} by ext x; simp]
  exact convex_iInter (fun i => convex_inverseStereographic_hemisphere (normal i) (up i))

end Unfoldings.Cap
