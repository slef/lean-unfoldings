module

public import Unfoldings.Path.Subpath
public import Mathlib.Topology.Order.DenselyOrdered

/-! Strict bounds for affine subpath times and density of proper unit-interval times. -/

@[expose] public section

namespace Path

theorem intervalParam_lt_right {s t : unitInterval} (ordered : s < t) {u : unitInterval}
    (before : u < 1) : intervalParam s t u < t := by
  change AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ) < (t : ℝ)
  rw [AffineMap.lineMap_apply_ring']
  have positive : 0 < (t : ℝ) - (s : ℝ) := sub_pos.mpr ordered
  have less := mul_lt_mul_of_pos_right (show (u : ℝ) < 1 from before) positive
  linarith

theorem dense_proper_unitInterval_times : Dense (Set.Iio (1 : unitInterval)) := by
  intro t
  apply closure_mono (Set.Ico_subset_Iio_self : Set.Ico (0 : unitInterval) 1 ⊆ Set.Iio 1)
  rw [closure_Ico zero_ne_one]
  exact t.property

end Path
