module

public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.EdgeSides

/-! Moving a triangle, its full edges, and barycentric coordinates by a rigid motion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

variable (T : Triangle) (A : Plane ≃ᵃⁱ[ℝ] Plane)

def move : Triangle where
  vertex i := A (T.vertex i)
  nondegenerate := orient_map_ne_zero A T.nondegenerate

@[simp] theorem move_vertex (i : Fin 3) : (T.move A).vertex i = A (T.vertex i) := rfl

@[simp] theorem move_opposite (e : Fin 3) : (T.move A).opposite e = A (T.opposite e) := rfl

theorem move_carrier : (T.move A).carrier = A '' T.carrier := by
  change convexHull ℝ (Set.range (A ∘ T.vertex)) =
    A.toAffineMap '' convexHull ℝ (Set.range T.vertex)
  rw [AffineMap.image_convexHull, Set.range_comp]
  rfl

theorem move_edge (e : Fin 3) : (T.move A).edge e = A '' T.edge e :=
  (image_segment ℝ A.toAffineMap _ _).symm

def moveEdge (e : Fin 3) : T.Edge e ≃ᵢ (T.move A).Edge e where
  toEquiv :=
    { toFun x := ⟨A x.val, (T.move_edge A e).symm.subset ⟨x.val, x.property, rfl⟩⟩
      invFun y := ⟨A.symm y.val, by
        obtain ⟨x, hx, equal⟩ := (T.move_edge A e).subset y.property
        simpa only [← equal, A.symm_apply_apply] using hx⟩
      left_inv _ := Subtype.ext (A.symm_apply_apply _)
      right_inv _ := Subtype.ext (A.apply_symm_apply _) }
  isometry_toFun x y := A.isometry x.val y.val

@[simp] theorem coord_move (i : Fin 3) (x : Plane) : (T.move A).coord i (A x) = T.coord i x := by
  have equal : ((T.move A).coord i).comp A.toAffineMap = T.coord i := by
    apply T.affine_ext
    intro j
    change (T.move A).coord i ((T.move A).vertex j) = T.coord i (T.vertex j)
    rw [coord_vertex, coord_vertex]
  exact congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h x) equal

end Unfoldings.Triangle
