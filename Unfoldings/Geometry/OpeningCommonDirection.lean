module

public import Unfoldings.Geometry.BankCircleDirection
public import Unfoldings.Geometry.OpeningCircleThreshold

/-! The actual opening budget supplies a common open-halfplane angular frame. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

theorem complex_div_re_pos_of_inner_pos {x z : ℂ} (positive : 0 < inner ℝ x z) :
    0 < (z / x).re := by
  have nonzero : x ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at positive
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at positive
  rw [Complex.div_re, ← add_div]
  exact div_pos (by nlinarith) (Complex.normSq_pos.mpr nonzero)

namespace PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- The common frame is constructed from the original bank's actual contact. -/
theorem openings_circleDirection_halfplane (events : List (Opening n))
    (radial : (R.openings events).Outward) (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
    (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
    (r : ℝ≥0) (radius_positive : 0 < r) :
    0 < (((R.openings events).circleDirection radial
      (R.openings_direction_ne_zero events nonzero) r radius_positive /
        R.circleDirection outward nonzero r radius_positive : Circle) : ℂ).re := by
  rw [Circle.coe_div, circleDirection_coe, R.circleDirection_coe, R.openings_start]
  have nonzero_radius : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < r from radius_positive).ne'
  have actual : R.radialPoint outward nonzero r - R.start ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [R.norm_radialPoint_sub_start]
    exact (show (0 : ℝ) < r from radius_positive).ne'
  have cancel (z : ℂ) : (z / (r : ℂ)) /
      ((R.radialPoint outward nonzero r - R.start) / (r : ℂ)) =
        z / (R.radialPoint outward nonzero r - R.start) := by
    field_simp
  rw [cancel]
  exact complex_div_re_pos_of_inner_pos
    (R.openings_radial_contact_inner_pos outward nonzero events radial γ positive small
      budget margin tail_margin r radius_positive)

end PolygonalRay
end Unfoldings
