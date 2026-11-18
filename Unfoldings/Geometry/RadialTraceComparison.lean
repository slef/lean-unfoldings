module

public import Unfoldings.Geometry.RadialGraphArc

/-! Radial coordinates identify whole subpath carriers and transport their order. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (P : PolygonalChain E n) (source : E) (radial : P.RadialFrom source 0)
  (positive : 0 < n)

include radial positive

/-- A radial subpath contains every ambient path point between its endpoint radii. -/
theorem mem_path_range_of_radius_bounds {m : ℕ} (Q : PolygonalChain E m)
    (radial_Q : Q.RadialFrom source 0) (contained : Set.range Q.path ⊆ Set.range P.path)
    {x : E} (member : x ∈ Set.range P.path)
    (bounds : dist source (Q.vertex 0) ≤ dist source x ∧
      dist source x ≤ dist source (Q.vertex (Fin.last m))) : x ∈ Set.range Q.path := by
  obtain ⟨t, at_radius⟩ := (Q.path_radius_range source radial_Q).symm.subset bounds
  have same := P.path_radius_injOn source radial positive member
    (contained (Set.mem_range_self t)) at_radius.symm
  exact ⟨t, same.symm⟩

/-- Two radial subpaths in one ambient radial carrier agree if both endpoints agree.
Their subdivisions, vertex counts and parametrizations may all differ. -/
theorem path_range_eq_of_radial_subsets {m k : ℕ} (Q : PolygonalChain E m)
    (S : PolygonalChain E k) (radial_Q : Q.RadialFrom source 0)
    (radial_S : S.RadialFrom source 0)
    (contained_Q : Set.range Q.path ⊆ Set.range P.path)
    (contained_S : Set.range S.path ⊆ Set.range P.path)
    (first : Q.vertex 0 = S.vertex 0) (last : Q.vertex (Fin.last m) = S.vertex (Fin.last k)) :
    Set.range Q.path = Set.range S.path := by
  apply Set.Subset.antisymm
  · intro x member
    apply P.mem_path_range_of_radius_bounds source radial positive S radial_S contained_S
      (contained_Q member)
    have bounds := Q.path_radius_bounds source radial_Q member
    rwa [first, last] at bounds
  · intro x member
    apply P.mem_path_range_of_radius_bounds source radial positive Q radial_Q contained_Q
      (contained_S member)
    have bounds := S.path_radius_bounds source radial_S member
    rwa [← first, ← last] at bounds

/-- On a radial carrier, any other radial source respects the controlling radial order.
Flat edges and repeated parameters do not affect this comparison of actual points. -/
theorem dist_le_of_control_radius_le (other : E) (other_radial : P.RadialFrom other 0)
    {x y : E} (first : x ∈ Set.range P.path) (last : y ∈ Set.range P.path)
    (ordered : dist source x ≤ dist source y) : dist other x ≤ dist other y := by
  obtain ⟨s, at_x⟩ := first
  obtain ⟨t, at_y⟩ := last
  obtain ⟨i, a, first_piece⟩ := P.path_point_covered positive s
  obtain ⟨j, b, last_piece⟩ := P.path_point_covered positive t
  have first_point : P.point i a = x := first_piece.symm.trans at_x
  have last_point : P.point j b = y := last_piece.symm.trans at_y
  rcases before_total i j a b with before | before
  · simpa only [first_point, last_point] using
      other_radial.dist_point_le P i j a b (Nat.zero_le _) before
  · have reverse := radial.dist_point_le P j i b a (Nat.zero_le _) before
    rw [first_point, last_point] at reverse
    have same := P.path_radius_injOn source radial positive ⟨s, at_x⟩ ⟨t, at_y⟩
      (le_antisymm ordered reverse)
    rw [same]

end Unfoldings.PolygonalChain
