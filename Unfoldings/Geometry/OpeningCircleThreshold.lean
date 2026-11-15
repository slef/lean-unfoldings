module

public import Unfoldings.Geometry.OpeningMatchedError

/-! A uniform opening budget keeps actual equal-circle contacts in one source-centered halfplane. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- A convenient sufficient threshold, with no edge-count dependence. -/
theorem opening_contact_coefficient_lt_one {γ ε : ℝ} (positive : 0 < γ) (small : γ ≤ 1)
    (nonnegative : 0 ≤ ε) (budget : 3 * ε < γ ^ 2) :
    ε / γ < 1 ∧ ((1 + γ⁻¹) * (ε / γ) / (1 - ε / γ)) < 1 := by
  have square_le : γ ^ 2 ≤ γ := by nlinarith
  have error_lt : ε < γ := by nlinarith
  have ratio : ε / γ < 1 := (div_lt_one positive).mpr error_lt
  refine ⟨ratio, ?_⟩
  apply (div_lt_one (sub_pos.mpr ratio)).mpr
  have algebra_first : ((1 + γ⁻¹) * (ε / γ)) * γ ^ 2 = (γ + 1) * ε := by
    field_simp
  have algebra_last : (1 - ε / γ) * γ ^ 2 = γ ^ 2 - γ * ε := by
    field_simp
  apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos positive)).mp
  rw [algebra_first, algebra_last]
  nlinarith [mul_nonneg (sub_nonneg.mpr small) nonnegative]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A contact closer than the original radius lies in its original direction's open halfplane. -/
theorem inner_pos_of_norm_sub_lt_norm {x z : E} (close : ‖z - x‖ < ‖x‖) :
    0 < inner ℝ x z := by
  have identity := norm_sub_sq_real x z
  rw [norm_sub_rev x z] at identity
  have positive : 0 < ‖x‖ := (norm_nonneg _).trans_lt close
  nlinarith [sq_nonneg ‖z‖, norm_nonneg (z - x)]

namespace PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- A mesh-independent sufficient budget keeps the actual opened bank contact close to its
original contact at every positive source radius. -/
theorem openings_radial_contact_close (events : List (Opening n))
    (radial : (R.openings events).Outward) (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
    (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
    (r : ℝ≥0) (radius_positive : 0 < r) :
    ‖(R.openings events).radialPoint radial (R.openings_direction_ne_zero events nonzero) r -
      R.radialPoint outward nonzero r‖ < (r : ℝ) := by
  have bounds := opening_contact_coefficient_lt_one (show (0 : ℝ) < γ from positive)
    small (openingBudget_nonneg events) budget
  have error := R.openings_radial_contact_error outward nonzero events radial γ positive small
    bounds.1 margin tail_margin r
  exact error.trans_lt (by simpa only [one_mul] using
    mul_lt_mul_of_pos_right bounds.2 (show (0 : ℝ) < r from radius_positive))

/-- All contacts stay in the same open source-centered halfplane, including intermediate openings
whenever they satisfy the same cumulative budget. -/
theorem openings_radial_contact_inner_pos (events : List (Opening n))
    (radial : (R.openings events).Outward) (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
    (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
    (r : ℝ≥0) (radius_positive : 0 < r) :
    0 < inner ℝ (R.radialPoint outward nonzero r - R.start)
      ((R.openings events).radialPoint radial (R.openings_direction_ne_zero events nonzero) r -
        R.start) := by
  apply inner_pos_of_norm_sub_lt_norm
  rw [sub_sub_sub_cancel_right, R.norm_radialPoint_sub_start]
  exact R.openings_radial_contact_close outward nonzero events radial γ positive small
    budget margin tail_margin r radius_positive

end PolygonalRay
end Unfoldings
