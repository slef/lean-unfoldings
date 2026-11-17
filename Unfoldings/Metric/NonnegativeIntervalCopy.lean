module

public import Mathlib.Topology.MetricSpace.Dilation
public import Mathlib.Basic.NNReal.Basic

/-! Closed real parameter intervals retain their exact nonnegative ray coordinates. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings

/-- The literal original time, including both interval endpoints. -/
def nonnegativeIntervalCopy (first last : ℝ≥0) (u : Set.Icc (first : ℝ) (last : ℝ)) : ℝ≥0 :=
  ⟨u.val, first.property.trans u.property.1⟩

/-- Restricting nonnegative ray time to a closed real interval changes no distance. -/
theorem isometry_nonnegativeIntervalCopy (first last : ℝ≥0) :
    Isometry (nonnegativeIntervalCopy first last) := fun _ _ => rfl

end Unfoldings
