module

public import Unfoldings.Metric.PositiveClosedInterval

/-! Original unit interval coordinates for a forward closed subsegment. -/

@[expose] public section

namespace Unfoldings

/-- The closed subinterval uses its actual original unit interval coordinates. -/
def closedUnitIntervalLineMap (s t : unitInterval) (forward : s.val ≤ t.val)
    (u : unitInterval) : unitInterval :=
  closedNonnegativeIntervalLineMap s.val t.val 1 s.property.1 forward t.property.2 u

theorem continuous_closedUnitIntervalLineMap (s t : unitInterval) (forward : s.val ≤ t.val) :
    Continuous (closedUnitIntervalLineMap s t forward) :=
  continuous_closedNonnegativeIntervalLineMap s.val t.val 1 s.property.1 forward t.property.2

@[simp] theorem closedUnitIntervalLineMap_zero (s t : unitInterval) (forward : s.val ≤ t.val) :
    closedUnitIntervalLineMap s t forward 0 = s := by
  apply Subtype.ext
  change s.val + 0 * (t.val - s.val) = s.val
  ring

@[simp] theorem closedUnitIntervalLineMap_one (s t : unitInterval) (forward : s.val ≤ t.val) :
    closedUnitIntervalLineMap s t forward 1 = t := by
  apply Subtype.ext
  change s.val + 1 * (t.val - s.val) = t.val
  ring

/-- Every interior time stays strictly between the original endpoints. -/
theorem closedUnitIntervalLineMap_strict (s t : unitInterval) (forward : s.val < t.val)
    (u : unitInterval) (interior_time : u ∈ Set.Ioo (0 : unitInterval) 1) :
    0 < (closedUnitIntervalLineMap s t forward.le u).val ∧
      (closedUnitIntervalLineMap s t forward.le u).val < 1 := by
  have positive : 0 < u.val := interior_time.1
  have small : u.val < 1 := interior_time.2
  change 0 < s.val + u.val * (t.val - s.val) ∧ s.val + u.val * (t.val - s.val) < 1
  constructor
  · exact lt_of_le_of_lt s.property.1
      (lt_add_of_pos_right s.val (mul_pos positive (sub_pos.mpr forward)))
  · nlinarith [t.property.2, mul_pos (sub_pos.mpr small) (sub_pos.mpr forward)]

theorem dense_unitInterval_interior : Dense (Set.Ioo (0 : unitInterval) 1) := by
  rw [dense_iff_closure_eq, closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
  apply Set.eq_univ_of_forall
  intro u
  exact ⟨u.property.1, u.property.2⟩

end Unfoldings
