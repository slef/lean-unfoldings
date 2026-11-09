module

public import Unfoldings.Cone.SectorCoordinates
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Strict shortcuts in pointed planar sectors

The two supporting half-plane inequalities give a linear functional strictly
positive on every nonzero point of a sector with positive boundary-ray sine.
Consequently, the segment between two nonzero sector points avoids the apex
and is strictly shorter than the route through it.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem zero_not_mem_segment_of_mem_planarSector (α : ℝ) (sine : 0 < Real.sin α)
    {z w : ℂ} (left : z ∈ planarSector α) (right : w ∈ planarSector α)
    (left_nonzero : z ≠ 0) (right_nonzero : w ≠ 0) :
    (0 : ℂ) ∉ segment ℝ z w := by
  let height : ℂ →ₗ[ℝ] ℝ :=
    Complex.imCLM.toLinearMap + (Real.sin α) • Complex.reCLM.toLinearMap -
      (Real.cos α) • Complex.imCLM.toLinearMap
  have height_eq (x : ℂ) :
      height x = x.im + (x.re * Real.sin α - x.im * Real.cos α) := by
    simp only [height, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, Complex.imCLM_apply,
      Complex.reCLM_apply, smul_eq_mul]
    ring
  have positive (x : ℂ) (inside : x ∈ planarSector α) (nonzero : x ≠ 0) :
      0 < height x := by
    obtain ⟨imaginary, halfplane⟩ := (mem_planarSector_iff_halfplanes α sine x).mp inside
    rw [height_eq]
    have nonnegative := add_nonneg imaginary halfplane
    apply lt_of_le_of_ne nonnegative
    intro equal
    have imaginary_zero : x.im = 0 := by linarith
    have real_zero : x.re = 0 := by
      have product : x.re * Real.sin α = 0 := by
        rw [imaginary_zero] at equal halfplane
        linarith
      exact (mul_eq_zero.mp product).resolve_right sine.ne'
    exact nonzero (Complex.ext real_zero imaginary_zero)
  rintro ⟨a, b, ha, hb, sum, equal⟩
  have left_height := positive z left left_nonzero
  have right_height := positive w right right_nonzero
  have zero_height := congrArg height equal
  rw [map_add, map_smul, map_smul, map_zero] at zero_height
  change a * height z + b * height w = 0 at zero_height
  have first := mul_nonneg ha left_height.le
  have last := mul_nonneg hb right_height.le
  have a_zero : a = 0 := by nlinarith
  have b_zero : b = 0 := by nlinarith
  linarith

/-- Every pair of nonzero points in a pointed sector has a strict chord
shortcut relative to their two radial segments through the apex. -/
theorem dist_lt_via_zero_of_mem_planarSector (α : ℝ) (sine : 0 < Real.sin α)
    {z w : ℂ} (left : z ∈ planarSector α) (right : w ∈ planarSector α)
    (left_nonzero : z ≠ 0) (right_nonzero : w ≠ 0) :
    dist z w < dist z 0 + dist 0 w :=
  dist_lt_dist_add_dist_iff.mpr (fun between =>
    zero_not_mem_segment_of_mem_planarSector α sine left right left_nonzero right_nonzero
      (mem_segment_iff_wbtw.mpr between))

end Unfoldings
