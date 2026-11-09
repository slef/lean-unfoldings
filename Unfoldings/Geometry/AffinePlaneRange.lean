module

public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Affine planes through a common point agree when their linear directions agree. -/

@[expose] public section

namespace Unfoldings

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem affineMap_range_eq_at (place : E →ᵃ[ℝ] F) (p : E) :
    Set.range place = {z | z - place p ∈ LinearMap.range place.linear} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x - p, place.linear_apply_vsub x p⟩
  · rintro ⟨d, hd⟩
    refine ⟨d + p, ?_⟩
    have mapped := place.map_vadd p d
    change place (d + p) = place.linear d + place p at mapped
    rw [mapped, hd, sub_add_cancel]

theorem affineMap_range_eq_of_linear_range_eq (place other : E →ᵃ[ℝ] F) (p q : E)
    (common : place p = other q) (directions : LinearMap.range place.linear =
      LinearMap.range other.linear) : Set.range place = Set.range other := by
  rw [affineMap_range_eq_at place p, affineMap_range_eq_at other q, common, directions]

end Unfoldings
