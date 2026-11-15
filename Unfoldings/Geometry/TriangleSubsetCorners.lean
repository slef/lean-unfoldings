module

public import Unfoldings.Geometry.MarkedPointConstraints
public import Unfoldings.Geometry.CornerSpan

/-! Contained triangles cannot hide an original extreme corner in an edge or face interior. -/

@[expose] public section

namespace Unfoldings.Triangle

/-- A triangle contained in another triangle preserves any original corner it contains. -/
theorem isVertex_of_contained_corner (T U : Triangle) (contained : T.carrier ⊆ U.carrier)
    (i : Fin 3) (member : U.vertex i ∈ T.carrier) : T.IsVertex (U.vertex i) := by
  apply T.isVertex_of_two_supports (U.coord (next i)) (U.coord (next (next i)))
    (U.coord_ne_zero _) (fun x hx => U.carrier_eq_nonneg_coord.le (contained hx) _)
    (fun x hx => U.carrier_eq_nonneg_coord.le (contained hx) _) member
    (by fin_cases i <;> simp [next, U.coord_vertex])
    (by fin_cases i <;> simp [next, U.coord_vertex])
  intro x first last
  have coordinates := U.reconstruct_corner i x
  rw [first, last] at coordinates
  simpa only [cornerCombination, zero_smul, zero_add] using coordinates.symm

end Unfoldings.Triangle
