module

public import Unfoldings.Geometry.PlanarConeOrientation

/-! Same directed boundary rays with the same occupied side cannot bound disjoint corner cones. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Positive rescaling changes the endpoint length but preserves its open direction cone. -/
theorem strictRayCone_smul_left {r : ℝ} (positive : 0 < r) (x y : E) :
    strictRayCone (r • x) y = strictRayCone x y := by
  ext z
  constructor
  · rintro ⟨a, apos, b, bpos, rfl⟩
    exact ⟨a * r, mul_pos apos positive, b, bpos, by rw [smul_smul]⟩
  · rintro ⟨a, apos, b, bpos, rfl⟩
    exact ⟨a / r, div_pos apos positive, b, bpos, by
      rw [smul_smul, div_mul_cancel₀ _ positive.ne']⟩

/-- Genuine corners on the same oriented side of a common initial ray overlap. -/
theorem not_disjoint_strictRayCones_of_same_initial_ray {x y z : Plane}
    (sign : 0 < orient 0 x y * orient 0 x z) :
    ¬ Disjoint (strictRayCone x y) (strictRayCone x z) := by
  intro separated
  rw [strictRayCone_comm x y] at separated
  have reverse : orient 0 y x = -orient 0 x y := by
    simp only [orient, PiLp.zero_apply, sub_zero]
    ring
  have product := orient_mul_pos_of_disjoint_strictRayCones
    (by rw [reverse]; exact neg_ne_zero.mpr (left_ne_zero_of_mul sign.ne'))
    (right_ne_zero_of_mul sign.ne') separated
  rw [reverse] at product
  nlinarith

/-- The same conclusion holds when the two initial bank vectors have different lengths. -/
theorem not_disjoint_strictRayCones_of_positive_scaled_ray {x y z : Plane} {r : ℝ}
    (positive : 0 < r) (first : 0 < orient 0 (r • x) y) (last : 0 < orient 0 x z) :
    ¬ Disjoint (strictRayCone (r • x) y) (strictRayCone x z) := by
  rw [strictRayCone_smul_left positive]
  have area : orient 0 (r • x) y = r * orient 0 x y := by
    simp only [orient, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, sub_zero]
    ring
  apply not_disjoint_strictRayCones_of_same_initial_ray
  rw [area] at first
  exact mul_pos ((mul_pos_iff_of_pos_left positive).mp first) last

end Unfoldings
