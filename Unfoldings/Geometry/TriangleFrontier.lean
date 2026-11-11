module

public import Unfoldings.Geometry.TriangleBoundary

/-! The actual frontier of a genuine triangle is exactly the union of its three entire edges. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem edge_subset_frontier (T : Triangle) (e : Fin 3) : T.edge e ⊆ frontier T.carrier := by
  intro x on_edge
  refine ⟨subset_closure (T.edge_subset e on_edge), ?_⟩
  intro inside
  have positive := T.interior_eq_pos_coord.le inside (next (next e))
  rw [T.coord_edge_eq_zero e ⟨x, on_edge⟩] at positive
  exact lt_irrefl _ positive

theorem frontier_eq_union_edges (T : Triangle) : frontier T.carrier = ⋃ e : Fin 3, T.edge e := by
  ext x
  constructor
  · intro boundary
    obtain ⟨e, member⟩ := T.exists_edge_of_not_mem_interior
      ⟨x, T.compact_carrier.isClosed.frontier_subset boundary⟩ boundary.2
    exact Set.mem_iUnion.mpr ⟨e, member⟩
  · intro member
    obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp member
    exact T.edge_subset_frontier e on_edge

end Unfoldings.Triangle
