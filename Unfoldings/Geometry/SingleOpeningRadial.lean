module

public import Unfoldings.Geometry.PolygonalRayOpening

/-! One budget controls every partial angle of an actual hinge opening. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- The same constants work throughout the continuous opening, including both endpoint banks. -/
theorem rotateSuffix_outward_of_budget (hinge : Fin (n + 1)) (angle : ℝ) {D d budget : ℝ}
    (constant : 0 ≤ D) (bound : |angle| ≤ budget) (small : D * budget < d)
    (interval_length : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (R.chain.interval j.val (i.val - j.val) (by omega)).projectedLength ≤
        D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      d * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (length_bound : R.chain.projectedLength ≤
      D * ‖R.chain.vertex (Fin.last n) - R.chain.vertex 0‖)
    (tail_margin : d * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction) :
    (R.rotateSuffix hinge angle).Outward := by
  let event : PolygonalChain.Opening n := ⟨hinge, angle⟩
  have budget_bound : D * PolygonalChain.openingBudget [event] < d := by
    simpa only [PolygonalChain.openingBudget, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] using
      (mul_le_mul_of_nonneg_left bound constant).trans_lt small
  exact R.openings_outward [event] constant budget_bound
    interval_length margin length_bound tail_margin

end Unfoldings.PolygonalRay
