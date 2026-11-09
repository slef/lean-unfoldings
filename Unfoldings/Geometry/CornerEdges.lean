module

public import Unfoldings.Geometry.Corner
public import Unfoldings.Geometry.EdgeSides

/-! Radial edge lines stay on the actual edge whenever they remain in the triangle. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem lineMap_mem_edge_of_mem_carrier (T : Triangle) (e : Fin 3) (a b : T.Edge e) (t : ℝ)
    (inside : AffineMap.lineMap a.val b.val t ∈ T.carrier) :
    AffineMap.lineMap a.val b.val t ∈ T.edge e := by
  apply (T.mem_edge_iff e _).mpr
  refine ⟨inside, ?_⟩
  rw [(T.coord (next (next e))).apply_lineMap,
    T.coord_edge_eq_zero e a, T.coord_edge_eq_zero e b]
  simp

end Unfoldings.Triangle
