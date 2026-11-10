module

public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.Angles

/-! Nondegenerate triangles and their full carriers under injective affine maps. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Injective affine maps preserve the signed-area nondegeneracy test. -/
theorem orient_affine_map_ne_zero (A : Plane →ᵃ[ℝ] Plane) (injective : Function.Injective A)
    {a b c : Plane} (nonzero : orient a b c ≠ 0) : orient (A a) (A b) (A c) ≠ 0 := by
  have different : a ≠ b := by
    intro equal
    exact nonzero (by simp [orient, equal])
  intro zero
  obtain ⟨t, image⟩ := exists_lineMap_of_orient_eq_zero (injective.ne different) zero
  have expression : c = AffineMap.lineMap a b t := injective (by
    rw [image]
    exact (A.apply_lineMap a b t).symm)
  exact nonzero (expression ▸ orient_lineMap a b t)

namespace Triangle

variable (T : Triangle) (A : Plane →ᵃ[ℝ] Plane) (injective : Function.Injective A)

def affineImage : Triangle where
  vertex i := A (T.vertex i)
  nondegenerate := orient_affine_map_ne_zero A injective T.nondegenerate

@[simp] theorem affineImage_vertex (i : Fin 3) :
    (T.affineImage A injective).vertex i = A (T.vertex i) := rfl

theorem affineImage_carrier : (T.affineImage A injective).carrier = A '' T.carrier := by
  change convexHull ℝ (Set.range (A ∘ T.vertex)) = A '' convexHull ℝ (Set.range T.vertex)
  rw [AffineMap.image_convexHull, Set.range_comp]

theorem affineImage_edge (e : Fin 3) : (T.affineImage A injective).edge e = A '' T.edge e :=
  (image_segment ℝ A _ _).symm

end Triangle
end Unfoldings
