module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Signed Gaussian polygon charges for a single normal cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

namespace SingleCellCharge

/-- The number of changes across one binary labeled side, as a real number. -/
def crossing (side : Bool × Bool) : ℝ := if side.1 = side.2 then 0 else 1

/-- Count both endpoints, preserving multiplicity when two marked sides meet. -/
def endpoints (side : Bool × Bool) : ℝ :=
  (if side.1 then 1 else 0) + (if side.2 then 1 else 0)

/-- The two marked sides carry probability mass one quarter at each endpoint. -/
def charge (changes : ℝ) (first second : Bool × Bool) (contained : Bool) : ℝ :=
  (changes - endpoints first - endpoints second) / 4 + if contained then 1 else 0

theorem crossing_le_endpoints (side : Bool × Bool) :
    crossing side ≤ endpoints side := by
  rcases side with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [crossing, endpoints]

/-- For a mixed polygon, deleting its two marked sides gives an upper bound
on the signed charge by one quarter of the remaining change count. -/
theorem charge_le_unmarked (unmarked : ℝ) (first second : Bool × Bool) :
    charge (unmarked + crossing first + crossing second) first second false ≤ unmarked / 4 := by
  simp [charge]
  linarith [crossing_le_endpoints first, crossing_le_endpoints second]

/-- A homogeneous polygon contributes zero to the single-cell estimate. -/
theorem charge_homogeneous (member : Bool) :
    charge 0 (member, member) (member, member) member = 0 := by
  cases member <;> norm_num [charge, endpoints]

private theorem endpoints_complement (a b : Bool) :
    endpoints (a, b) + endpoints (!a, !b) = 2 := by
  cases a <;> cases b <;> norm_num [endpoints]

/-- A half-turn reversing the labels of a mixed two-crossing polygon
pairs its charge with the opposite charge. -/
theorem charge_complement (a b c d : Bool) :
    charge 2 (a, b) (c, d) false + charge 2 (!a, !b) (!c, !d) false = 0 := by
  simp [charge]
  linarith [endpoints_complement a b, endpoints_complement c d]

end SingleCellCharge

end Unfoldings.FewestNets
