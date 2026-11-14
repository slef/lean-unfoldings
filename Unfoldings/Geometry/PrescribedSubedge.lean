module

public import Unfoldings.Geometry.ConstrainedEdgeSubdivision

/-! A respected constraint segment containing a fine edge's nonvertex point contains that edge. -/

@[expose] public section

namespace Unfoldings.Triangle

open AffineArrangement

theorem edge_subset_of_signed_coords (U T : Triangle) (signs : Fin 3 → Bool)
    (side : ∀ k p, p ∈ T.carrier → 0 ≤ signed (U.coord k) (signs k) p)
    (old_edge fine_edge : Fin 3) (x : T.Edge fine_edge) (regular : ¬ T.IsVertex x)
    (member : x.val ∈ U.edge old_edge) : T.edge fine_edge ⊆ U.edge old_edge := by
  let k := next (next old_edge)
  have zero : signed (U.coord k) (signs k) x.val = 0 :=
    (signed_eq_zero_iff _ _ _).mpr (U.coord_edge_eq_zero old_edge ⟨x.val, member⟩)
  have zero_edge := T.affine_zero_on_edge_of_nonnegative (signed (U.coord k) (signs k))
    (fun p hp => side k p hp) fine_edge x regular zero
  intro p hp
  apply (U.mem_edge_iff old_edge p).mpr
  constructor
  · apply U.carrier_eq_nonneg_coord.ge
    intro j
    exact T.affine_nonnegative_on_edge_of_signed (U.coord j) (signs j)
      (fun p hp => side j p hp) fine_edge x regular
      (U.carrier_eq_nonneg_coord.le (U.edge_subset old_edge member) j) p hp
  · exact (signed_eq_zero_iff _ _ _).mp (zero_edge p hp)

end Unfoldings.Triangle
