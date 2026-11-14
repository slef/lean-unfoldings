module

public import Unfoldings.Geometry.RayAvoidance
public import Unfoldings.Geometry.Edge

/-! Every planar segment, including a single point, lies on a proper affine equation. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Classical in
def segmentEquation (a b : Plane) : Plane →ᵃ[ℝ] ℝ :=
  if a = b then (EuclideanSpace.proj 0).toLinearMap.toAffineMap - AffineMap.const ℝ Plane (a 0)
  else orientMap a b

theorem segmentEquation_ne_zero (a b : Plane) : segmentEquation a b ≠ 0 := by
  classical
  by_cases same : a = b
  · intro zero
    have at_point := congrArg (fun l : Plane →ᵃ[ℝ] ℝ => l (a + WithLp.toLp 2 ![1, 0])) zero
    norm_num [segmentEquation, same, PiLp.add_apply] at at_point
  · simpa only [segmentEquation, ite_eq_right same] using orientMap_ne_zero same

theorem segmentEquation_eq_zero {a b x : Plane} (member : x ∈ segment ℝ a b) :
    segmentEquation a b x = 0 := by
  classical
  by_cases same : a = b
  · have point : x = a := by simpa only [same, segment_same, Set.mem_singleton_iff] using member
    rw [point]
    simp [segmentEquation, same]
  · simpa only [segmentEquation, ite_eq_right same, orientMap_apply] using
      orient_eq_zero_of_mem_segment member

end Unfoldings
