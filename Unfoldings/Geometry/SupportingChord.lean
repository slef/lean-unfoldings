module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith

/-! A supporting functional is constant on a chord whose interior point attains its bound. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem supporting_functional_eq_endpoints (f : E →L[ℝ] ℝ) {a : ℝ} {x y z : E}
    (hx : f x ≤ a) (hy : f y ≤ a) (between : z ∈ openSegment ℝ x y) (level : f z = a) :
    f x = a ∧ f y = a := by
  obtain ⟨r, t, hr, ht, sum, equal⟩ := between
  have combination : r * f x + t * f y = a := by
    rw [← equal, map_add, map_smul, map_smul] at level
    exact level
  have weighted : r * (a - f x) + t * (a - f y) = 0 := by
    calc
      _ = (r + t) * a - (r * f x + t * f y) := by ring
      _ = 0 := by rw [sum, combination, one_mul, sub_self]
  have first_nonnegative := mul_nonneg hr.le (sub_nonneg.mpr hx)
  have second_nonnegative := mul_nonneg ht.le (sub_nonneg.mpr hy)
  have first_zero : r * (a - f x) = 0 := by linarith
  have second_zero : t * (a - f y) = 0 := by linarith
  exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp first_zero).resolve_left hr.ne')).symm,
    (sub_eq_zero.mp ((mul_eq_zero.mp second_zero).resolve_left ht.ne')).symm⟩

end Unfoldings
