module

public import Unfoldings.Geometry.RadialClosureSegments

/-! Construct outward closing directions strictly beyond a supporting side of a pointed wedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A small move across a wedge side preserves a strictly positive terminal scalar product. -/
theorem exists_outward_opposite_direction (height : E →ₗ[ℝ] ℝ) (b u v : E)
    (on_side : height u = 0) (across : height v = 1) (outward : 0 < inner ℝ b u) :
    ∃ direction : E, height direction < 0 ∧ 0 < inner ℝ b direction := by
  let ε := inner ℝ b u / (2 * (|inner ℝ b v| + 1))
  have denominator : 0 < 2 * (|inner ℝ b v| + 1) := by positivity
  have positive : 0 < ε := div_pos outward denominator
  have product : ε * (2 * (|inner ℝ b v| + 1)) = inner ℝ b u :=
    div_mul_cancel₀ _ denominator.ne'
  refine ⟨u - ε • v, ?_, ?_⟩
  · rw [map_sub, map_smul, smul_eq_mul, on_side, across, mul_one, zero_sub]
    exact neg_neg_of_pos positive
  · rw [inner_sub_right, real_inner_smul_right]
    have bound := mul_le_mul_of_nonneg_left (le_abs_self (inner ℝ b v)) positive.le
    nlinarith

/-- In positive coordinates, at least one side has a positive terminal scalar product. -/
theorem exists_wedge_closing_direction (frame : (ℝ × ℝ) ≃ₗ[ℝ] E) (b : E)
    (nonzero : b ≠ 0) (coordinates : 0 ≤ (frame.symm b).1 ∧ 0 ≤ (frame.symm b).2) :
    ∃ height : E →ₗ[ℝ] ℝ, (∀ x, 0 ≤ (frame.symm x).1 → 0 ≤ (frame.symm x).2 → 0 ≤ height x) ∧
      ∃ direction : E, height direction < 0 ∧ 0 < inner ℝ b direction := by
  let u := frame (1, 0)
  let v := frame (0, 1)
  let left : E →ₗ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap
  let right : E →ₗ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap
  have left_u : left u = 1 := by simp [left, u]
  have left_v : left v = 0 := by simp [left, v]
  have right_u : right u = 0 := by simp [right, u]
  have right_v : right v = 1 := by simp [right, v]
  have representation : b = (frame.symm b).1 • u + (frame.symm b).2 • v := by
    calc
      b = frame (frame.symm b) := (frame.apply_symm_apply b).symm
      _ = frame ((frame.symm b).1 • (1, 0) + (frame.symm b).2 • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = _ := by rw [map_add, map_smul, map_smul]
  have norm_positive : 0 < inner ℝ b b := real_inner_self_pos.mpr nonzero
  have expansion : inner ℝ b b =
      (frame.symm b).1 * inner ℝ b u + (frame.symm b).2 * inner ℝ b v := by
    nth_rw 2 [representation]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  by_cases first : 0 < inner ℝ b u
  · refine ⟨right, (fun x _ second => second), ?_⟩
    exact exists_outward_opposite_direction right b u v right_u right_v first
  · have second : 0 < inner ℝ b v := by
      have first_product := mul_nonpos_of_nonneg_of_nonpos coordinates.1 (le_of_not_gt first)
      by_contra not_second
      have second_product := mul_nonpos_of_nonneg_of_nonpos coordinates.2 (le_of_not_gt not_second)
      linarith
    refine ⟨left, (fun x first _ => first), ?_⟩
    exact exists_outward_opposite_direction left b v u left_v left_u second

end Unfoldings
