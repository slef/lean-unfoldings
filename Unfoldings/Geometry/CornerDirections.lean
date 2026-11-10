module

public import Unfoldings.Geometry.ConeOrientation
public import Unfoldings.Geometry.CornerSpan

/-! Disjoint triangle interiors have disjoint open direction cones at a common corner. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem cornerCombination_mem_interior (T : Triangle) (i : Fin 3) {a b : ℝ}
    (apos : 0 < a) (bpos : 0 < b) (small : a + b < 1) :
    T.cornerCombination i a b ∈ interior T.carrier := by
  rw [T.interior_eq_pos_coord]
  intro j
  rcases corner_cases i j with same | same | same
  · rw [same]
    have sum := T.coord_sum_edge i (T.cornerCombination i a b)
    rw [T.coord_next_cornerCombination, T.coord_prev_cornerCombination] at sum
    linarith
  · rw [same, T.coord_next_cornerCombination]
    exact apos
  · rw [same, T.coord_prev_cornerCombination]
    exact bpos

/-- Strict direction cones cannot overlap when the actual triangle interiors do not. -/
theorem disjoint_cornerDirections (T U : Triangle) (i j : Fin 3)
    (apex : T.vertex i = U.vertex j)
    (separated : Disjoint (interior T.carrier) (interior U.carrier)) :
    Disjoint (strictRayCone (T.vertex (next i) - T.vertex i)
        (T.vertex (next (next i)) - T.vertex i))
      (strictRayCone (U.vertex (next j) - U.vertex j)
        (U.vertex (next (next j)) - U.vertex j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, apos, b, bpos, first⟩ ⟨c, cpos, d, dpos, last⟩
  let denominator : ℝ := a + b + c + d + 1
  have positive : 0 < denominator := by dsimp [denominator]; linarith
  let t : ℝ := denominator⁻¹
  have tpos : 0 < t := inv_pos.mpr positive
  have leftsmall : t * a + t * b < 1 := by
    change denominator⁻¹ * a + denominator⁻¹ * b < 1
    rw [← mul_add, ← div_eq_inv_mul]
    apply (div_lt_one positive).mpr
    dsimp [denominator]
    linarith
  have rightsmall : t * c + t * d < 1 := by
    change denominator⁻¹ * c + denominator⁻¹ * d < 1
    rw [← mul_add, ← div_eq_inv_mul]
    apply (div_lt_one positive).mpr
    dsimp [denominator]
    linarith
  have in_left := T.cornerCombination_mem_interior i
    (mul_pos tpos apos) (mul_pos tpos bpos) leftsmall
  have in_right := U.cornerCombination_mem_interior j
    (mul_pos tpos cpos) (mul_pos tpos dpos) rightsmall
  have point_left : T.cornerCombination i (t * a) (t * b) = t • z + T.vertex i := by
    rw [first]
    simp only [cornerCombination, smul_add, smul_smul]
  have point_right : U.cornerCombination j (t * c) (t * d) = t • z + T.vertex i := by
    rw [last, apex]
    simp only [cornerCombination, smul_add, smul_smul]
  rw [point_left] at in_left
  rw [point_right] at in_right
  exact Set.disjoint_left.mp separated in_left in_right

end Unfoldings.Triangle
