module

public import Unfoldings.Geometry.EdgeSides

/-! A closed triangle point outside its interior lies on an actual local edge. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem exists_edge_of_not_mem_interior (T : Triangle) (x : T.Cell)
    (outside : x.val ∉ interior T.carrier) : ∃ e : Fin 3, x.val ∈ T.edge e := by
  have nonnegative := T.carrier_eq_nonneg_coord.le x.property
  have zero : ∃ i, T.coord i x = 0 := by
    by_contra none
    apply outside
    rw [T.interior_eq_pos_coord]
    intro i
    exact lt_of_le_of_ne (nonnegative i) (fun equal => none ⟨i, equal.symm⟩)
  obtain ⟨i, hi⟩ := zero
  refine ⟨next i, (T.mem_edge_iff (next i) x.val).mpr ⟨x.property, ?_⟩⟩
  have cycle : next (next (next i)) = i := by fin_cases i <;> rfl
  rwa [cycle]

end Unfoldings.Triangle
