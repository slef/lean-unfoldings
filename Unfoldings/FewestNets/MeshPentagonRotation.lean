module

public import Unfoldings.FewestNets.MeshFaceGeometry
public import Mathlib.NumberTheory.Real.GoldenRatio

/-! Exact metric identities for the positive one-fifth turn around the model vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open Real NormedSpace Matrix

private theorem cross_cornerA_cornerB :
    spatialCross cornerA cornerB =
      (WithLp.toLp 2 ![0, 2 * √3 * faceScale * faceHeight, 2 * √3 * faceScale ^ 2] : Space) := by
  ext j
  fin_cases j <;> simp [spatialCross, crossProduct, cornerA, cornerB] <;> ring

/-- The chosen positive turn maps the first adjacent macrovertex to the second. -/
theorem fifthTurn_cornerB : fifthTurn cornerB = cornerC := by
  let c : ℝ := (√5 - 1) / 4
  let s : ℝ := √(1 - c ^ 2)
  let h := faceHeight
  let b := faceScale
  have sqrt5_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have sqrt5_hi : √(5 : ℝ) < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have cp : 0 ≤ c := by
    have l : (1 : ℝ) ≤ √5 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    dsimp only [c]
    linarith only [l]
  have cl : c < 1 := by dsimp only [c]; linarith only [sqrt5_hi]
  have hpos : 0 < h := by
    exact Real.sqrt_pos.2 (by unfold faceHeightSq; positivity)
  have angleSq : s ^ 2 = 1 - c ^ 2 :=
    Real.sq_sqrt (by nlinarith only [cp, cl, mul_pos (sub_pos.mpr cl) (by linarith : 0 < 1 + c)])
  have heightSq : h ^ 2 = faceHeightSq := faceHeight_squared
  have scaleSq : b ^ 2 = (1 - faceHeightSq) / 4 := faceScale_squared
  have axial : (1 - c) * (√5 / 5) = c := by
    dsimp only [c]
    linear_combination -sqrt5_sq / 20
  have factor : s * √3 * h = 1 + c := by
    apply (sq_eq_sq₀ (by dsimp only [s]; positivity) (by linarith only [cp])).mp
    rw [mul_pow, mul_pow, angleSq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), heightSq]
    dsimp only [c, faceHeightSq]
    linear_combination -((6 + 2 * √5) / 80) * sqrt5_sq
  have vertical : (1 - 2 * c) * h ^ 2 = 2 * (1 + c) * b ^ 2 := by
    rw [heightSq, scaleSq]
    dsimp only [c, faceHeightSq]
    linear_combination -sqrt5_sq / 20
  have value : fifthTurn cornerB =
      c • cornerB + s • spatialCross cornerA cornerB + c • cornerA := by
    simp only [fifthTurn, normalize_eq_self_of_norm_eq_one cornerA_unit, corner_pair_inner.1]
    change c • cornerB + s • spatialCross cornerA cornerB + ((1 - c) * (√5 / 5)) • cornerA = _
    rw [axial]
  rw [value, cross_cornerA_cornerB]
  ext j
  fin_cases j
  · change c * (√3 * b) + s * 0 + c * (-(√3 * b)) = 0
    ring
  · change c * (-b) + s * (2 * √3 * b * h) + c * (-b) = 2 * b
    linear_combination (2 * b) * factor
  · change c * h + s * (2 * √3 * b ^ 2) + c * h = h
    apply (mul_left_injective₀ hpos.ne')
    linear_combination (2 * b ^ 2) * factor - vertical

private theorem spatialCross_add_right (u v w : Space) :
    spatialCross u (v + w) = spatialCross u v + spatialCross u w := by
  change WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v + WithLp.ofLp w)) = _
  rw [map_add]
  rfl

private theorem spatialCross_smul_right (u v : Space) (a : ℝ) :
    spatialCross u (a • v) = a • spatialCross u v := by
  change WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (a • WithLp.ofLp v)) = _
  rw [map_smul]
  rfl

theorem fifthTurn_add (v w : Space) : fifthTurn (v + w) = fifthTurn v + fifthTurn w := by
  simp only [fifthTurn, spatialCross_add_right, inner_add_right]
  module

theorem fifthTurn_smul (a : ℝ) (v : Space) : fifthTurn (a • v) = a • fifthTurn v := by
  simp only [fifthTurn, spatialCross_smul_right, real_inner_smul_right]
  module

@[simp] theorem fifthTurn_cornerA : fifthTurn cornerA = cornerA := by
  simp only [fifthTurn, normalize_eq_self_of_norm_eq_one cornerA_unit,
    real_inner_self_eq_norm_sq, cornerA_unit, one_pow, mul_one]
  have zero : spatialCross cornerA cornerA = 0 := by
    change WithLp.toLp 2 (crossProduct (WithLp.ofLp cornerA) (WithLp.ofLp cornerA)) = 0
    rw [cross_self]
    rfl
  rw [zero, smul_zero]
  module

private theorem spatialCross_axis_twice (x : Space) :
    spatialCross cornerA (spatialCross cornerA x) = inner ℝ cornerA x • cornerA - x := by
  have h := congrArg (WithLp.toLp 2)
    (cross_cross_eq_smul_sub_smul' (WithLp.ofLp cornerA) (WithLp.ofLp cornerA) (WithLp.ofLp x))
  rw [← inner_eq_coordinate_dotProduct cornerA x, ← inner_eq_coordinate_dotProduct cornerA cornerA,
    real_inner_self_eq_norm_sq, cornerA_unit, one_pow, one_smul] at h
  exact h

private theorem spatialCross_axis_self : spatialCross cornerA cornerA = 0 := by
  change WithLp.toLp 2 (crossProduct (WithLp.ofLp cornerA) (WithLp.ofLp cornerA)) = 0
  rw [cross_self]
  rfl

/-- The turn preserves the component along the chosen original vertex. -/
theorem inner_cornerA_fifthTurn (x : Space) :
    inner ℝ cornerA (fifthTurn x) = inner ℝ cornerA x := by
  simp only [fifthTurn, normalize_eq_self_of_norm_eq_one cornerA_unit, inner_add_right,
    real_inner_smul_right, inner_left_spatialCross, mul_zero, add_zero, real_inner_self_eq_norm_sq,
    cornerA_unit, one_pow, mul_one]
  ring

/-- The orbit of a neighboring original vertex obeys the exact golden-ratio recurrence. -/
theorem fifthTurn_twice_of_neighbor (x : Space) (neighbor : inner ℝ cornerA x = √5 / 5) :
    fifthTurn (fifthTurn x) = (goldenRatio - 1) • (fifthTurn x + cornerA) - x := by
  let c : ℝ := (√5 - 1) / 4
  let s : ℝ := √(1 - c ^ 2)
  let a := inner ℝ cornerA x
  have cpp : 0 ≤ c := by
    have l : (1 : ℝ) ≤ √5 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    dsimp only [c]
    linarith only [l]
  have clt : c < 1 := by
    have h : √(5 : ℝ) < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
    dsimp only [c]
    linarith only [h]
  have sq : s ^ 2 = 1 - c ^ 2 :=
    Real.sq_sqrt (by nlinarith only [mul_pos (sub_pos.mpr clt) (by linarith : 0 < 1 + c)])
  have form (y : Space) :
      fifthTurn y = c • y + s • spatialCross cornerA y +
        ((1 - c) * inner ℝ cornerA y) • cornerA := by
    simp only [fifthTurn, normalize_eq_self_of_norm_eq_one cornerA_unit, c, s]
  have cross :
      spatialCross cornerA (fifthTurn x) =
        c • spatialCross cornerA x + s • (a • cornerA - x) := by
    rw [form, spatialCross_add_right, spatialCross_add_right, spatialCross_smul_right,
      spatialCross_smul_right, spatialCross_smul_right, spatialCross_axis_twice,
      spatialCross_axis_self, smul_zero, add_zero]
  have recur :
      fifthTurn (fifthTurn x) = (2 * c) • fifthTurn x - x + (2 * (1 - c) * a) • cornerA := by
    calc
      _ = c • fifthTurn x + (s * c) • spatialCross cornerA x +
          s ^ 2 • (a • cornerA - x) + ((1 - c) * a) • cornerA := by
            rw [form (fifthTurn x), inner_cornerA_fifthTurn, cross, pow_two]
            module
      _ = _ := by rw [sq, form x]; module
  have two_c : 2 * c = goldenRatio - 1 := by
    dsimp [c, goldenRatio]
    ring
  have axis : 2 * (1 - c) * a = goldenRatio - 1 := by
    dsimp only [a]
    rw [neighbor]
    dsimp [c, goldenRatio]
    linear_combination -(Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)) / 10
  rw [recur, two_c, axis, smul_add]
  abel

end Unfoldings.FewestNets.MeshStar
