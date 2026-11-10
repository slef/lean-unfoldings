module

public import Unfoldings.Geometry.PairedChains
public import Unfoldings.Cone.Sector

/-!
# Noncrossing matched banks inside a common open quadrant

The strict acute slack lets a cap proof use this stronger direction condition.
This proves an order certificate from edge lengths and unreduced headings,
without assuming noncrossing or a globally safe forest.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

variable {n : ℕ} (L R : PolygonalChain ℂ n)

/-- Matched cut-edge lengths with right and left headings in one open quadrant. -/
structure QuadrantBanks where
  length : Fin n → ℝ
  positive_length : ∀ i, 0 < length i
  rightHeading : Fin n → ℝ
  leftHeading : Fin n → ℝ
  right_bounds : ∀ i, rightHeading i ∈ Set.Ioo 0 (Real.pi / 2)
  left_bounds : ∀ i, leftHeading i ∈ Set.Ioo 0 (Real.pi / 2)
  heading_order : ∀ i, rightHeading i ≤ leftHeading i
  right_edge : ∀ i, R.edge i = (length i : ℂ) * polarRay (rightHeading i)
  left_edge : ∀ i, L.edge i = (length i : ℂ) * polarRay (leftHeading i)
  start : L.vertex 0 = R.vertex 0

namespace QuadrantBanks

variable {L R} (B : QuadrantBanks L R)

include B

theorem horizontal_increments (i : Fin n) : (L.edge i).re ≤ (R.edge i).re := by
  rw [B.left_edge, B.right_edge]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, polarRay_re]
  exact mul_le_mul_of_nonneg_left
    (Real.cos_le_cos_of_nonneg_of_le_pi (B.right_bounds i).1.le
      (by linarith [(B.left_bounds i).2, Real.pi_pos]) (B.heading_order i))
    (B.positive_length i).le

theorem vertical_increments (i : Fin n) : (R.edge i).im ≤ (L.edge i).im := by
  rw [B.left_edge, B.right_edge]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, polarRay_im]
  exact mul_le_mul_of_nonneg_left
    (Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [(B.right_bounds i).1, Real.pi_pos]) (B.left_bounds i).2.le (B.heading_order i))
    (B.positive_length i).le

theorem right_horizontal (i : Fin n) : 0 < (R.edge i).re := by
  rw [B.right_edge]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, polarRay_re]
  exact mul_pos (B.positive_length i)
    (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [(B.right_bounds i).1, Real.pi_pos], (B.right_bounds i).2⟩)

theorem right_vertical (i : Fin n) : 0 ≤ (R.edge i).im := by
  rw [B.right_edge]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, polarRay_im]
  exact mul_nonneg (B.positive_length i).le (Real.sin_nonneg_of_nonneg_of_le_pi
    (B.right_bounds i).1.le (by linarith [(B.right_bounds i).2, Real.pi_pos]))

/-- Every actual left-bank point lies above the right bank at the same horizontal coordinate. -/
theorem vertical_order (i j : Fin n) (t s : unitInterval)
    (same_horizontal : (L.point i t).re = (R.point j s).re) :
    (R.point j s).im ≤ (L.point i t).im :=
  L.vertical_order_of_increments R Complex.reCLM.toLinearMap Complex.imCLM.toLinearMap
    B.start B.horizontal_increments B.vertical_increments B.right_horizontal B.right_vertical
    i j t s same_horizontal

end QuadrantBanks
end Unfoldings.Cap
