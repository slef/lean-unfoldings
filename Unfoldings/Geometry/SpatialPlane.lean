module

public import Unfoldings.Geometry.FunctionalPlane
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A rigid two-dimensional spatial plane is the whole nonzero functional level that contains it. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem affineIsometry_linear_range_eq_kernel (place : Plane →ᵃⁱ[ℝ] Space)
    (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) (a : ℝ) (level : ∀ p, f (place p) = a) :
    LinearMap.range place.linear = f.toLinearMap.ker := by
  have contained : LinearMap.range place.linear ≤ f.toLinearMap.ker := by
    rintro d ⟨p, rfl⟩
    change f (place.linear p) = 0
    have difference : place.linear p = place p - place 0 := by
      have mapped := place.toAffineMap.linear_apply_vsub p 0
      change place.linear (p - 0) = place p - place 0 at mapped
      simpa only [sub_zero] using mapped
    rw [difference, map_sub, level, level, sub_self]
  apply Submodule.eq_of_le_of_finrank_eq contained
  have injective : Function.Injective place.linear := place.linearIsometry.injective
  rw [LinearMap.finrank_range_of_inj injective, functionalKernel_finrank f nonzero]
  norm_num [Plane]

theorem range_affineIsometry_eq_level (place : Plane →ᵃⁱ[ℝ] Space)
    (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) (a : ℝ) (level : ∀ p, f (place p) = a) :
    Set.range place = {z | f z = a} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact level p
  · intro height
    have kernel : z - place 0 ∈ f.toLinearMap.ker := by
      change f (z - place 0) = 0
      rw [map_sub, height, level, sub_self]
    rw [← affineIsometry_linear_range_eq_kernel place f nonzero a level] at kernel
    obtain ⟨p, hp⟩ := kernel
    refine ⟨p, ?_⟩
    have decomposition := congrFun place.toAffineMap.decomp p
    change place p = place.linear p + place 0 at decomposition
    rw [decomposition, hp, sub_add_cancel]

end Unfoldings
