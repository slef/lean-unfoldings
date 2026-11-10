module

public import Unfoldings.Examples.Tetrahedron.Body
public import Unfoldings.Geometry.EdgeSides

/-! Relate the global supporting coordinates to actual face barycentric coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

theorem corner_injective (f : Fin 4) : Function.Injective (corner f) := by
  fin_cases f <;> decide

theorem corner_surjective_away (f i : Fin 4) (different : i ≠ f) : ∃ j, corner f j = i := by
  fin_cases f <;> fin_cases i <;> simp_all [corner, Fin.exists_fin_succ]

theorem weight_corner_placement (f : Fin 4) (i : Fin 3) (x : Plane) :
    weight (corner f i) (placement f x) = (triangle f).coord i x := by
  have maps : (weight (corner f i)).comp (placement f).toAffineMap = (triangle f).coord i := by
    apply (triangle f).affine_ext
    intro j
    change weight (corner f i) (placement f ((triangle f).vertex j)) = _
    rw [placement_vertex, weight_vertex, Triangle.coord_vertex]
    exact if_congr (corner_injective f).eq_iff rfl rfl
  exact congrArg (fun map : Plane →ᵃ[ℝ] ℝ => map x) maps

theorem weight_omitted_placement (f : Fin 4) (x : Plane) : weight f (placement f x) = 0 := by
  have maps : (weight f).comp (placement f).toAffineMap = AffineMap.const ℝ Plane 0 := by
    apply (triangle f).affine_ext
    intro j
    change weight f (placement f ((triangle f).vertex j)) = 0
    rw [placement_vertex, weight_vertex, ite_eq_right (corner_ne f j).symm]
  exact congrArg (fun map : Plane →ᵃ[ℝ] ℝ => map x) maps

end Unfoldings.Examples.Tetrahedron
