module

public import Unfoldings.Geometry.EdgeSides

/-! The unique affine equivalence matching the three corners of two genuine planar triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- A genuine triangle is determined by its three ordered corners. -/
theorem eq_of_vertex_eq {T U : Triangle} (equal : ∀ i, T.vertex i = U.vertex i) : T = U := by
  cases T
  cases U
  congr
  exact funext equal

/-- Barycentric interpolation is the affine map matching corresponding corners. -/
def cornerMap (T U : Triangle) : Plane →ᵃ[ℝ] Plane :=
  ∑ i : Fin 3, ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (U.vertex i)).toAffineMap.comp (T.coord i)

@[simp] theorem cornerMap_vertex (T U : Triangle) (i : Fin 3) :
    T.cornerMap U (T.vertex i) = U.vertex i := by
  simp only [cornerMap, Fin.sum_univ_three]
  change T.coord 0 (T.vertex i) • U.vertex 0 + T.coord 1 (T.vertex i) • U.vertex 1 +
    T.coord 2 (T.vertex i) • U.vertex 2 = U.vertex i
  fin_cases i <;> simp

@[simp] theorem cornerMap_comp (T U : Triangle) :
    (U.cornerMap T).comp (T.cornerMap U) = AffineMap.id ℝ Plane := by
  apply T.affine_ext
  intro i
  simp only [AffineMap.comp_apply, cornerMap_vertex, AffineMap.id_apply]

/-- Every pair of nondegenerate planar triangles has a canonical corner-matching affine map. -/
def cornerEquiv (T U : Triangle) : Plane ≃ᵃ[ℝ] Plane :=
  AffineEquiv.ofBijective (φ := T.cornerMap U) ⟨by
    intro x y same
    have equal := congrArg (U.cornerMap T) same
    simpa only [← AffineMap.comp_apply, cornerMap_comp, AffineMap.id_apply] using equal,
    fun y => ⟨U.cornerMap T y, by
      have equal := congrArg (fun f : Plane →ᵃ[ℝ] Plane => f y) (U.cornerMap_comp T)
      exact equal⟩⟩

@[simp] theorem cornerEquiv_vertex (T U : Triangle) (i : Fin 3) :
    T.cornerEquiv U (T.vertex i) = U.vertex i := T.cornerMap_vertex U i

end Unfoldings.Triangle
