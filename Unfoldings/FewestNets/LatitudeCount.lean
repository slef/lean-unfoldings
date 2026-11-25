module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Numerical aggregation of the triangular and polar selector contributions. -/

@[expose] public section

namespace Unfoldings.FewestNets

/-- The area term and the two types of selector contributions give the
paper's strict coefficient in the general acute-angle theorem. -/
theorem latitude_component_bound {a : ℝ} (positive : 0 < a) (small : a ≤ Real.pi / 6) :
    2 + 72 / a ^ 2 + (2283 / a ^ 2) * (5.6475 / a ^ 2) < 13000 / a ^ 4 := by
  have a_le : a ≤ 1 := by linarith only [small, Real.pi_lt_d4]
  have sq : a ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ positive.le a_le 2
  have fourth : a ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ positive.le a_le 4
  apply (lt_div_iff₀ (pow_pos positive 4)).mpr
  calc
    _ = 2 * a ^ 4 + 72 * a ^ 2 + 2283 * 5.6475 := by
      field_simp [positive.ne']
    _ < _ := by linarith only [sq, fourth]

end Unfoldings.FewestNets
