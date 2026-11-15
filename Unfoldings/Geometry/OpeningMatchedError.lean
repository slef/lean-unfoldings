module

public import Unfoldings.Geometry.RadialMatchedError
public import Unfoldings.Geometry.RadialContactPerturbation
public import Unfoldings.Geometry.PolygonalRayOpening

/-! Uniform equal-circle control for actual finite sequences of hinge-fixed suffix openings. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

theorem abs_openingHeading_le_budget (events : List (Opening n)) (i : Fin n) :
    |openingHeading events i| ≤ openingBudget events := by
  induction events with
  | nil => simp [openingHeading, openingBudget]
  | cons event events ih =>
    have single : |if event.hinge ≤ i.castSucc then event.angle else 0| ≤ |event.angle| := by
      split_ifs <;> simp [abs_nonneg]
    change |(if event.hinge ≤ i.castSucc then event.angle else 0) + openingHeading events i| ≤
      |event.angle| + openingBudget events
    exact (abs_add_le _ _).trans (add_le_add single ih)

theorem abs_openingTailHeading_le_budget (events : List (Opening n)) :
    |openingTailHeading events| ≤ openingBudget events := by
  induction events with
  | nil => simp [openingTailHeading, openingBudget]
  | cons event events ih =>
    change |event.angle + openingTailHeading events| ≤ |event.angle| + openingBudget events
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem openings_edge_error (P : PolygonalChain ℂ n) (events : List (Opening n)) (i : Fin n) :
    ‖(P.openings events).edge i - P.edge i‖ ≤ openingBudget events * ‖P.edge i‖ := by
  rw [P.openings_edge]
  have equal : polarRay (openingHeading events i) * P.edge i - P.edge i =
      (polarRay (openingHeading events i) - 1) * P.edge i := by ring
  rw [equal, norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((norm_polarRay_sub_one_le _).trans (abs_openingHeading_le_budget events i)) (norm_nonneg _)

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

theorem openings_direction_error (events : List (Opening n)) :
    ‖(R.openings events).direction - R.direction‖ ≤ openingBudget events * ‖R.direction‖ := by
  rw [R.openings_direction]
  have equal : polarRay (openingTailHeading events) * R.direction - R.direction =
      (polarRay (openingTailHeading events) - 1) * R.direction := by ring
  rw [equal, norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((norm_polarRay_sub_one_le _).trans (abs_openingTailHeading_le_budget events)) (norm_nonneg _)

/-- Every point of the final bank is matched to the original bank, with all true hinge translations
and partial original edges retained. -/
theorem exists_openings_matched_point (events : List (Opening n)) {γ : ℝ}
    (positive : 0 < γ) (small : γ ≤ 1)
    (margin : ∀ i, γ * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
    (tail_margin : γ * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
    {z : ℂ} (member : z ∈ (R.openings events).carrier) :
    ∃ x ∈ R.carrier, ‖z - x‖ ≤ (openingBudget events / γ) * ‖x - R.start‖ := by
  apply R.exists_radial_matched_point (R.openings events) positive small
    (openingBudget_nonneg events)
    (R.openings_start events) margin tail_margin _ (R.openings_direction_error events) member
  intro i
  rw [R.openings_chain]
  exact R.chain.openings_edge_error events i

/-- Actual contacts on the original source circle obey one uniform quantitative bound. -/
theorem openings_radial_contact_error (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (events : List (Opening n)) (radial : (R.openings events).Outward)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (budget : openingBudget events / (γ : ℝ) < 1)
    (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
    (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction) (r : ℝ≥0) :
    ‖(R.openings events).radialPoint radial (R.openings_direction_ne_zero events nonzero) r -
      R.radialPoint outward nonzero r‖ ≤
      ((1 + (γ : ℝ)⁻¹) * (openingBudget events / (γ : ℝ)) /
        (1 - openingBudget events / (γ : ℝ))) * (r : ℝ) := by
  obtain ⟨x, member, error⟩ :=
    R.exists_openings_matched_point events positive small margin tail_margin
    ((R.openings events).radialPoint_mem radial (R.openings_direction_ne_zero events nonzero) r)
  apply R.radial_contact_error outward nonzero
    (R.lipschitz_radialPoint outward nonzero γ positive small margin tail_margin)
    (div_nonneg (openingBudget_nonneg events) positive.le) budget member error r
  have radius := (R.openings events).norm_radialPoint_sub_start radial
    (R.openings_direction_ne_zero events nonzero) r
  rwa [R.openings_start] at radius

end Unfoldings.PolygonalRay
