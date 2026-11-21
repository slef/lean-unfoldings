module

public import Unfoldings.Basic
public import Unfoldings.Geometry.Triangle
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.Convex.Combination

/-! The altitude of the corner triangle bounds the disk in its angular sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A vector inside a corner sector and closer to the apex than the opposite
line has barycentric coefficients summing to less than one. -/
theorem sum_coeff_lt_one_of_corner_altitude (o : Orientation ℝ Plane (Fin 2))
    {p q x : Plane} (genuine : o.areaForm p q ≠ 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (direction : x = a • p + b • q)
    (near : ‖x‖ < |o.areaForm p q| / ‖q - p‖) :
    a + b < 1 := by
  have dpos : 0 < ‖q - p‖ := by
    apply norm_pos_iff.mpr
    intro zero
    have same := sub_eq_zero.mp zero
    exact genuine (same ▸ o.areaForm_apply_self p)
  let L := o.areaForm (q - p)
  have first : L p = -o.areaForm p q := by
    change o.areaForm (q - p) p = _
    rw [map_sub, LinearMap.sub_apply, o.areaForm_apply_self, sub_zero, o.areaForm_swap q p]
  have last : L q = -o.areaForm p q := by
    change o.areaForm (q - p) q = _
    rw [map_sub, LinearMap.sub_apply, o.areaForm_apply_self, zero_sub]
  have normal : |L x| = (a + b) * |o.areaForm p q| := by
    rw [direction, map_add, map_smul, map_smul, first, last, smul_eq_mul, smul_eq_mul,
      ← add_mul, abs_mul, abs_of_nonneg (add_nonneg ha hb), abs_neg]
  have bound := o.abs_areaForm_le (q - p) x
  change |L x| ≤ _ at bound
  rw [normal] at bound
  have strict := (lt_div_iff₀ dpos).mp near
  rw [mul_comm] at strict
  apply (mul_lt_mul_iff_of_pos_right (abs_pos.mpr genuine)).mp
  rw [one_mul]
  exact bound.trans_lt strict

/-- The sector portion of the open altitude disk lies in the closed corner triangle. -/
theorem mem_corner_triangle_of_altitude (o : Orientation ℝ Plane (Fin 2))
    {p q x : Plane} (genuine : o.areaForm p q ≠ 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (direction : x = a • p + b • q)
    (near : ‖x‖ < |o.areaForm p q| / ‖q - p‖) :
    x ∈ convexHull ℝ (Set.range (![0, p, q] : Fin 3 → Plane)) := by
  have sum := sum_coeff_lt_one_of_corner_altitude o genuine ha hb direction near
  refine mem_convexHull_of_exists_fintype (![1 - (a + b), a, b] : Fin 3 → ℝ) ![0, p, q]
    ?_ ?_ (fun k => Set.mem_range_self k) ?_
  · intro k
    fin_cases k
    · exact sub_nonneg.mpr sum.le
    · exact ha
    · exact hb
  · rw [Fin.sum_univ_three]
    change 1 - (a + b) + a + b = 1
    ring
  · rw [Fin.sum_univ_three]
    change (1 - (a + b)) • (0 : Plane) + a • p + b • q = x
    rw [smul_zero, zero_add, ← direction]

end Unfoldings
