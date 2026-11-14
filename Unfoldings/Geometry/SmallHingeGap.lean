module

public import Unfoldings.Geometry.HingeGapPrefix
public import Unfoldings.Geometry.SingleOpeningRadial

/-! Quantitative radial margins construct hinge gaps disjoint from the prefix held fixed. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Radial hypotheses on the original bank suffice; intermediate embeddings are proved. -/
theorem hingeGap_prefix_inter_of_small_opening (hinge : Fin (n + 1))
    (outward : (R.suffix hinge).Outward) (nonzero : R.direction ≠ 0)
    (angle : ℝ) (positive : 0 < angle) (half_turn : angle < Real.pi) {D d : ℝ}
    (constant : 0 ≤ D) (small : D * angle < d)
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
    Set.range (R.chain.interval 0 hinge.val (by omega)).path ∩
      (R.suffix hinge).rotationGap outward nonzero angle = {R.chain.vertex hinge} := by
  apply R.hingeGap_prefix_inter hinge outward nonzero angle positive half_turn
  intro θ heading
  apply R.rotateSuffix_outward_of_budget hinge θ constant
    (by simpa only [abs_of_nonneg heading.1] using heading.2) small
    interval_length margin length_bound tail_margin

end Unfoldings.PolygonalRay
