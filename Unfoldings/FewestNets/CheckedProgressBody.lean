module

public import Unfoldings.FewestNets.CheckedPlane
public import Unfoldings.Geometry.PolygonInradius
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Check the inradius of the convex hull of a saved progress body. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

variable {D n : ℕ} (hD : 0 < D) {body : Fin (n + 1) → Plane}
  (cb : ∀ i, CheckedPlane D (body i))

/-- Test consecutive turns and the distance of every oriented side from the origin. -/
def checkProgressBodyInradius {radius : ℝ} (cr : CheckedReal D radius) : Bool :=
  let next := finRotate (n + 1)
  (List.finRange (n + 1)).all fun i =>
    let left := CheckedPlane.sub (cb i) (cb (next.symm i))
    let right := CheckedPlane.sub (cb (next i)) (cb i)
    (CheckedPlane.det hD left right).isPositive &&
      (cr.mul hD (CheckedPlane.norm hD right)).isLT (CheckedPlane.det hD (cb i) (cb (next i)))

theorem closedBall_subset_progressBody_of_check {radius : ℝ} (cr : CheckedReal D radius)
    (nonnegative : 0 ≤ radius) (check : checkProgressBodyInradius hD cb cr = true) :
    Metric.closedBall (0 : Plane) radius ⊆ convexHull ℝ (Set.range body) := by
  let next := finRotate (n + 1)
  have tested (i : Fin (n + 1)) :
      0 < orient 0 (body i - body (next.symm i)) (body (next i) - body i) ∧
        radius * ‖body (next i) - body i‖ < orient 0 (body i) (body (next i)) := by
    have pass := List.all_eq_true.mp check i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at pass
    obtain ⟨left, right⟩ := pass
    exact ⟨by simpa only [orient, PiLp.zero_apply, sub_zero] using
        CheckedReal.positive_of_isPositive hD _ left,
      by simpa only [orient, PiLp.zero_apply, sub_zero] using
        CheckedReal.lt_of_isLT hD _ _ right⟩
  exact closedBall_subset_convexHull_of_edge_distances body next nonnegative
    (fun i => (tested i).1) (fun i => (tested i).2.le)

end Unfoldings.FewestNets
