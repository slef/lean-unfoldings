module

public import Unfoldings.Convex.ActiveForwardGain
public import Unfoldings.Roof.CommonPotentialForest
public import Unfoldings.Roof.CompatiblePotentialRouting
public import Unfoldings.Roof.CompatibleAdaptivePaths

/-! An adaptive forest can use the existing common-potential geometric constructions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}

namespace AdaptivePotentialRouting

variable {U : Set Face} {E : SlopeEnvelope} {L : Set Plane} {r margin : ℝ}
  (R : K.AdaptivePotentialRouting U E L r margin)

/-- The same original parents have a common-potential description with a
uniform acute bound. This description is used for geometric cut construction. -/
def asCommonPotentialRouting (positive : 0 < r)
    (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b)
    (upper : ∀ p ∈ E.slopes, ‖p‖ ≤ b) : K.CommonPotentialRouting U E r (arccos (r / b)) where
  parents := R.parents
  roots_eq := R.roots_eq
  height_eq := R.height_eq
  selection := R.selection
  step v nonroot := by
    let x := K.projectedVertex v
    let d := K.projectedVertex (R.parents.parent v) - x
    have genuine : d ≠ 0 := by
      intro zero
      have h := R.parents.ascending v nonroot
      change K.projectedVertex (R.parents.parent v) - x = 0 at zero
      rw [R.height_eq] at h
      change E.height x < E.height (K.projectedVertex (R.parents.parent v)) at h
      rw [sub_eq_zero.mp zero] at h
      exact lt_irrefl _ h
    have progress (t : ℝ) (time : 0 < t) :
        t * (r * ‖d‖) ≤ E.height (x + t • d) - E.height x := by
      have h := R.along v nonroot 0 t le_rfl time.le
      change E.HistoryProgress L (x + (0 : ℝ) • d) (x + t • d) at h
      rw [zero_smul, add_zero] at h
      have norm_bound := h.norm_le E positive disk
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos time] at norm_bound
      simpa only [mul_assoc, mul_comm, mul_left_comm] using norm_bound
    obtain ⟨p, active, forward⟩ := E.exists_active_of_forward_gain x d progress
    have p_nonzero : p ≠ 0 := by
      intro zero
      rw [zero, inner_zero_left] at forward
      exact (mul_pos positive (norm_pos_iff.mpr genuine)).not_ge forward
    refine ⟨p, active, E.active_angle_bound_of_progress bound_pos positive.le ratio upper active
      p_nonzero genuine forward, ?_, R.endpoint v nonroot⟩
    have weaker := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right positive.le (cos_le_one (arccos (r / b)))) (norm_nonneg d)
    exact weaker.trans (R.ascent v nonroot)

end AdaptivePotentialRouting

namespace CompatibleAdaptiveRouting

variable {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty}
  {L : Set Plane} {r margin η : ℝ} (R : K.CompatibleAdaptiveRouting U G boundary L r margin η)

/-- Use the existing geometric cut construction with exactly the same
adaptive original seams and exterior rays. -/
def asCommonPotentialRouting (positive : 0 < r)
    (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b) :
    K.CompatiblePotentialRouting U G boundary r (arccos (r / b)) where
  original := R.original.asCommonPotentialRouting positive disk bound_pos ratio
    (fun p hp => upper p (G.compact.isClosed.frontier_subset hp))
  exterior := R.exterior
  exterior_points := R.exterior_points
  exterior_height := R.exterior_height

end CompatibleAdaptiveRouting
end Unfoldings.ConvexRoof
