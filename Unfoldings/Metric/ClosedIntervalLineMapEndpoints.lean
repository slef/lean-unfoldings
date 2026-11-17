module

public import Unfoldings.Metric.PositiveClosedInterval

/-! Original endpoint values of affine maps between closed nonnegative subintervals. -/

@[expose] public section

namespace Unfoldings

@[simp] theorem closedIntervalLineMap_zero {T : ℝ} (s t : Set.Icc (0 : ℝ) T)
    (forward : s ≤ t) :
    closedNonnegativeIntervalLineMap s.val t.val T s.property.1 forward t.property.2 0 = s := by
  apply Subtype.ext
  simp only [closedNonnegativeIntervalLineMap, nonnegativeIntervalLineMap,
    Set.Icc.coe_zero, zero_mul, add_zero]

@[simp] theorem closedIntervalLineMap_one {T : ℝ} (s t : Set.Icc (0 : ℝ) T)
    (forward : s ≤ t) :
    closedNonnegativeIntervalLineMap s.val t.val T s.property.1 forward t.property.2 1 = t := by
  apply Subtype.ext
  simp only [closedNonnegativeIntervalLineMap, nonnegativeIntervalLineMap,
    Set.Icc.coe_one, one_mul, add_sub_cancel]

end Unfoldings
