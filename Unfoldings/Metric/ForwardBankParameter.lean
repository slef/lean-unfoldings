module

public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Forward half-line parameters retain the exact original bank speed. -/

@[expose] public section

open scoped NNReal ENNReal

namespace Unfoldings

/-- Start at an actual original junction, then continue at a fixed nonnegative speed. -/
def forwardBankParameter (start speed t : ℝ≥0) : ℝ≥0 := start + speed * t

@[simp] theorem forwardBankParameter_zero (start speed : ℝ≥0) :
    forwardBankParameter start speed 0 = start := by simp [forwardBankParameter]

theorem edist_forwardBankParameter (start speed s t : ℝ≥0) :
    edist (forwardBankParameter start speed s) (forwardBankParameter start speed t) =
      (speed : ℝ≥0∞) * edist s t := by
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal |(start.val + speed.val * s.val) -
    (start.val + speed.val * t.val)| = (speed : ℝ≥0∞) * ENNReal.ofReal |s.val - t.val|
  rw [show (start.val + speed.val * s.val) - (start.val + speed.val * t.val) =
    speed.val * (s.val - t.val) by ring, abs_mul, abs_of_nonneg speed.property,
    ENNReal.ofReal_mul speed.property]
  exact congrArg (fun r => r * ENNReal.ofReal |s.val - t.val|)
    (show ENNReal.ofReal speed.val = (speed : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)

end Unfoldings
