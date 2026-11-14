module

public import Unfoldings.Basic
public import Unfoldings.Geometry.UnitLine
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Distinct unit-normal lines at positive support levels meet in at most one slope. -/

@[expose] public section

namespace Unfoldings

theorem positive_unit_sides_intersection_unique {u v p q : Plane} {c d : ℝ}
    (uunit : ‖u‖ = 1) (vunit : ‖v‖ = 1) (different : u ≠ v) (cpos : 0 < c) (dpos : 0 < d)
    (up : inner ℝ u p = c) (uq : inner ℝ u q = c)
    (vp : inner ℝ v p = d) (vq : inner ℝ v q = d) : p = q := by
  by_contra distinct
  have unz : u ≠ 0 := by intro zero; rw [zero, norm_zero] at uunit; norm_num at uunit
  have vnz : v ≠ 0 := by intro zero; rw [zero, norm_zero] at vunit; norm_num at vunit
  let : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩
  have du : inner ℝ (p - q) u = 0 := by
    have pu : inner ℝ p u = c := (real_inner_comm _ _).trans up
    have qu : inner ℝ q u = c := (real_inner_comm _ _).trans uq
    rw [inner_sub_left, pu, qu, sub_self]
  have dv : inner ℝ (p - q) v = 0 := by
    have pv : inner ℝ p v = d := (real_inner_comm _ _).trans vp
    have qv : inner ℝ q v = d := (real_inner_comm _ _).trans vq
    rw [inner_sub_left, pv, qv, sub_self]
  have parallel : v ∈ Submodule.span ℝ {u} :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      (sub_ne_zero.mpr distinct) unz dv du
  have directions := inv_norm_smul_eq_or_eq_neg_of_mem_span vnz unz parallel
  simp only [uunit, vunit, inv_one, one_smul] at directions
  rcases directions with same | opposite
  · exact different same
  · rw [opposite, inner_neg_left, vp] at up
    linarith

end Unfoldings
