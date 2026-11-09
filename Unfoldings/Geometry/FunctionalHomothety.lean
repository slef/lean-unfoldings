module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Tactic.Linarith

/-! Positive homotheties about a support-level point preserve levels and half-spaces. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem functional_lineMap_level_iff (f : E →L[ℝ] ℝ) {v : E} {a : ℝ}
    (at_vertex : f v = a) (z : E) {t : ℝ} (positive : 0 < t) :
    f (AffineMap.lineMap v z t) = a ↔ f z = a := by
  rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, at_vertex]
  change t * (f z - a) + a = a ↔ f z = a
  constructor
  · intro equal
    have product : t * (f z - a) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left positive.ne')
  · intro equal
    rw [equal, sub_self, mul_zero, zero_add]

theorem functional_lineMap_le_iff (f : E →L[ℝ] ℝ) {v : E} {a : ℝ}
    (at_vertex : f v = a) (z : E) {t : ℝ} (positive : 0 < t) :
    f (AffineMap.lineMap v z t) ≤ a ↔ f z ≤ a := by
  rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, at_vertex]
  change t * (f z - a) + a ≤ a ↔ f z ≤ a
  constructor
  · intro bound
    by_contra outside
    have product := mul_pos positive (sub_pos.mpr (lt_of_not_ge outside))
    linarith
  · intro bound
    have product := mul_nonpos_of_nonneg_of_nonpos positive.le (sub_nonpos.mpr bound)
    linarith

end Unfoldings
