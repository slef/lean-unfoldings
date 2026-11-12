module

public import Unfoldings.Geometry.BankRadialOrder

/-! Paired banks keep their circle order through right/down and left/up branch-gap steps. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (L R : PolygonalChain E n)

/-- Only the right bank's horizontal and left bank's vertical coordinates need increase.
The other coordinate may decrease along a straight segment across a branch gap. -/
theorem left_or_above_of_mixed_increments (horizontal vertical : E →ₗ[ℝ] ℝ)
    (start : L.vertex 0 = R.vertex 0)
    (horizontal_increments : ∀ i, horizontal (L.edge i) ≤ horizontal (R.edge i))
    (vertical_increments : ∀ i, vertical (R.edge i) ≤ vertical (L.edge i))
    (right_horizontal : ∀ i, 0 ≤ horizontal (R.edge i))
    (left_vertical : ∀ i, 0 ≤ vertical (L.edge i))
    (i j : Fin n) (t s : unitInterval) :
    horizontal (L.point i t) ≤ horizontal (R.point j s) ∨
      vertical (R.point j s) ≤ vertical (L.point i t) := by
  rcases before_total i j t s with before | before
  · left
    exact (L.linear_point_le_of_increments R horizontal (by rw [start])
      horizontal_increments i t).trans
      (R.linear_point_le horizontal
        ((R.monotone_linear_vertices_iff horizontal).mpr right_horizontal) i j t s before)
  · right
    exact (R.linear_point_le_of_increments L vertical (by rw [start])
      vertical_increments j s).trans
      (L.linear_point_le vertical
        ((L.monotone_linear_vertices_iff vertical).mpr left_vertical) j i s t before)

theorem circle_order_of_mixed_increments {n : ℕ} (L R : PolygonalChain ℂ n)
    (start : L.vertex 0 = R.vertex 0)
    (horizontal_increments : ∀ i, (L.edge i).re ≤ (R.edge i).re)
    (vertical_increments : ∀ i, (R.edge i).im ≤ (L.edge i).im)
    (right_horizontal : ∀ i, 0 ≤ (R.edge i).re)
    (left_vertical : ∀ i, 0 ≤ (L.edge i).im)
    (center : ℂ) (i j : Fin n) (t s : unitInterval)
    (left_quadrant : 0 ≤ (L.point i t - center).re ∧ 0 ≤ (L.point i t - center).im)
    (right_quadrant : 0 ≤ (R.point j s - center).re ∧ 0 ≤ (R.point j s - center).im)
    (same_radius : ‖L.point i t - center‖ = ‖R.point j s - center‖) :
    (L.point i t - center).re ≤ (R.point j s - center).re ∧
      (R.point j s - center).im ≤ (L.point i t - center).im := by
  have alternative := L.left_or_above_of_mixed_increments R Complex.reCLM.toLinearMap
    Complex.imCLM.toLinearMap start horizontal_increments vertical_increments right_horizontal
    left_vertical i j t s
  change (L.point i t).re ≤ (R.point j s).re ∨
    (R.point j s).im ≤ (L.point i t).im at alternative
  have relative : (L.point i t - center).re ≤ (R.point j s - center).re ∨
      (R.point j s - center).im ≤ (L.point i t - center).im := by
    simpa only [Complex.sub_re, Complex.sub_im, sub_le_sub_iff_right] using alternative
  have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have radii : (L.point i t - center).re ^ 2 + (L.point i t - center).im ^ 2 =
      (R.point j s - center).re ^ 2 + (R.point j s - center).im ^ 2 := by
    rw [← identity, ← identity, same_radius]
  exact quadrant_circle_order left_quadrant.1 left_quadrant.2 right_quadrant.1 right_quadrant.2
    radii relative

end Unfoldings.PolygonalChain
