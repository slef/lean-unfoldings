module

public import Unfoldings.FewestNets.VisualCertificate

/-! Soundness of the two exterior witnesses used in a finite routing certificate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

private theorem exterior_margin_of_coordinates {x y length a b A δ η : ℝ}
    (length_nonneg : 0 ≤ length) (δ_pos : 0 < δ) (η_nonneg : 0 ≤ η)
    (a_pos : 0 < a) (a_bound : a ≤ A)
    (opposing : b * y ≤ -(δ * |y|)) (half_plane : 0 ≤ a * x + b * y)
    (norm_sq : x ^ 2 + y ^ 2 = length ^ 2)
    (margin : η ^ 2 * (A ^ 2 + δ ^ 2) ≤ δ ^ 2) :
    η * length ≤ x := by
  have control : δ * |y| ≤ a * x := by linarith
  have inward : 0 ≤ x :=
    nonneg_of_mul_nonneg_right ((mul_nonneg δ_pos.le (abs_nonneg y)).trans control) a_pos
  have abs_bound := control.trans (mul_le_mul_of_nonneg_right a_bound inward)
  have square := (sq_le_sq₀ (by positivity : 0 ≤ δ * |y|)
    (mul_nonneg (a_pos.le.trans a_bound) inward)).mpr abs_bound
  simp only [mul_pow, sq_abs] at square
  have norm_bound : δ ^ 2 * length ^ 2 ≤ (A ^ 2 + δ ^ 2) * x ^ 2 := by
    rw [← norm_sq]
    nlinarith only [square]
  have positive : 0 < A ^ 2 + δ ^ 2 := by positivity
  have scaled := (mul_le_mul_of_nonneg_right margin (sq_nonneg length)).trans norm_bound
  have required : (η * length) ^ 2 ≤ x ^ 2 := by
    apply le_of_mul_le_mul_left (a := A ^ 2 + δ ^ 2) _ positive
    simpa only [mul_pow, mul_left_comm, mul_comm, mul_assoc] using scaled
  exact (sq_le_sq₀ (mul_nonneg η_nonneg length_nonneg) inward).mp required

/-- Opposite tangent witnesses with bounded positive normal coordinates give
a uniform positive polar margin. The two comparisons use squared quantities
so the final exterior margin check requires no division or square root. -/
theorem exterior_margin_of_witnesses
    {n d wMinus wPlus : E} (unit : ‖n‖ = 1)
    {AMinus APlus δMinus δPlus η : ℝ}
    (η_nonneg : 0 ≤ η) (δMinus_pos : 0 < δMinus) (δPlus_pos : 0 < δPlus)
    (normalMinus : 0 < inner ℝ n wMinus) (normalPlus : 0 < inner ℝ n wPlus)
    (normalMinus_le : inner ℝ n wMinus ≤ AMinus) (normalPlus_le : inner ℝ n wPlus ≤ APlus)
    (tangentMinus : δMinus ≤ o.areaForm n wMinus)
    (tangentPlus : o.areaForm n wPlus ≤ -δPlus)
    (coneMinus : 0 ≤ inner ℝ wMinus d) (conePlus : 0 ≤ inner ℝ wPlus d)
    (boundMinus : η ^ 2 * (AMinus ^ 2 + δMinus ^ 2) ≤ δMinus ^ 2)
    (boundPlus : η ^ 2 * (APlus ^ 2 + δPlus ^ 2) ≤ δPlus ^ 2) :
    η * ‖d‖ ≤ inner ℝ n d := by
  have norm_sq : inner ℝ n d ^ 2 + o.areaForm n d ^ 2 = ‖d‖ ^ 2 := by
    simpa only [unit, one_pow, one_mul] using o.inner_sq_add_areaForm_sq n d
  have coordinates (w : E) :
      inner ℝ n w * inner ℝ n d + o.areaForm n w * o.areaForm n d = inner ℝ w d := by
    simpa only [unit, one_pow, one_mul] using o.inner_mul_inner_add_areaForm_mul_areaForm n w d
  by_cases nonnegative : 0 ≤ o.areaForm n d
  · have opposing : o.areaForm n wPlus * o.areaForm n d ≤ -(δPlus * |o.areaForm n d|) := by
      rw [abs_of_nonneg nonnegative, ← neg_mul]
      exact mul_le_mul_of_nonneg_right tangentPlus nonnegative
    exact exterior_margin_of_coordinates (norm_nonneg d) δPlus_pos η_nonneg
      normalPlus normalPlus_le opposing ((coordinates wPlus).symm ▸ conePlus) norm_sq boundPlus
  · have nonpositive := (lt_of_not_ge nonnegative).le
    have opposing : o.areaForm n wMinus * o.areaForm n d ≤ -(δMinus * |o.areaForm n d|) := by
      rw [abs_of_nonpos nonpositive, mul_neg, neg_neg]
      exact mul_le_mul_of_nonpos_right tangentMinus nonpositive
    exact exterior_margin_of_coordinates (norm_nonneg d) δMinus_pos η_nonneg
      normalMinus normalMinus_le opposing ((coordinates wMinus).symm ▸ coneMinus) norm_sq boundMinus

end Unfoldings.FewestNets
