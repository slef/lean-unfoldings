module

public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Convex.ActiveRayProgress
public import Unfoldings.Convex.CommonPotential

/-! Uniform radial margins at arbitrary fine compatible vertices, without a coarse-vertex split. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- Any genuine partial step has an actual initial maximizing slope with the uniform gain. -/
theorem followsStep_active_progress (positive : 0 < a) (beta : 0 ≤ β)
    (acute : β ≤ Real.pi / 2) (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    {x y : Plane} (step : R.FollowsStep x y) :
    ∃ p, (G.boundaryEnvelope boundary).Active x p ∧
      (a * Real.cos β) * ‖y - x‖ ≤ inner ℝ p (y - x) := by
  rcases step with ⟨v, s, t, hs, ordered, _last, rfl, rfl⟩ |
    ⟨r, s, t, hs, ordered, rfl, rfl⟩
  · obtain ⟨p, active, gain⟩ := R.parent_local_progress positive beta acute inner_disk v.property
    exact (G.boundaryEnvelope boundary).exists_active_ray_segment_progress active gain hs ordered
  · obtain ⟨p, active, gain⟩ := R.terminal_local_progress positive inner_disk r
    simp only [SlopeEnvelope.ExteriorPlan.ray, R.exterior_points]
    exact (G.boundaryEnvelope boundary).exists_active_ray_segment_progress active gain hs ordered

/-- Every partial compatible history has a radial margin against its next fine step.
The stronger two-history-angle condition permits arbitrary fine endpoints and terminal tails. -/
theorem follows_radial_margin_at_fine_step (positive : 0 < a) (beta : 0 ≤ β)
    (acute : β < Real.pi / 2) {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)
    {n : ℕ} (P : PolygonalChain Plane n) (follows : R.Follows P) (y : Plane)
    (step : R.FollowsStep (P.vertex (Fin.last n)) y) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖P.vertex (Fin.last n) - P.vertex 0‖ * ‖y - P.vertex (Fin.last n)‖) ≤
      inner ℝ (P.vertex (Fin.last n) - P.vertex 0) (y - P.vertex (Fin.last n)) := by
  by_cases same : P.vertex (Fin.last n) = P.vertex 0
  · simp only [same, sub_self, norm_zero, zero_mul, mul_zero, inner_zero_left, le_refl]
  by_cases constant : y = P.vertex (Fin.last n)
  · simp only [constant, sub_self, norm_zero, mul_zero, inner_zero_right, le_refl]
  obtain ⟨p, active, outgoing⟩ :=
    R.followsStep_active_progress positive beta acute.le inner_disk step
  have cosine : 0 < Real.cos β :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩
  have pne : p ≠ 0 := by
    intro zero
    rw [zero, inner_zero_left] at outgoing
    exact (not_lt_of_ge outgoing) (mul_pos (mul_pos positive cosine)
      (norm_pos_iff.mpr (sub_ne_zero.mpr constant)))
  have coefficient : a * Real.cos β ≤ b :=
    (mul_le_of_le_one_right positive.le (Real.cos_le_one β)).trans ratio
  have expression : (a * Real.cos β) / b = (a / b) * Real.cos β := by ring
  have margin := (G.boundaryEnvelope boundary).history_radial_margin_of_active_progress bpos
    (mul_nonneg positive.le cosine.le) coefficient
    (fun p hp => upper p (G.compact.isClosed.frontier_subset hp)) active pne same
    (sub_ne_zero.mpr constant) (R.follows_progress positive beta acute.le inner_disk P follows)
    P.chord_le_projectedLength outgoing (by
      rw [expression]
      change 2 * annularHistoryAngle (a / b) β ≤ Real.pi
      linarith [Real.pi_pos])
  simpa only [expression, annularHistoryAngle] using margin

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
