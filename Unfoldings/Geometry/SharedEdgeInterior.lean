module

public import Unfoldings.Geometry.SharedEdgeOpening
public import Unfoldings.Geometry.HingePatch

/-! Shared nonvertex edge points lie inside any region containing both geometric triangles. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem shared_edge_mem_interior_union (T U : Triangle) (e f : Fin 3)
    (same : T.edge e = U.edge f)
    (disjoint : Disjoint (interior T.carrier) (interior U.carrier))
    (x : T.Edge e) (regular : ¬ T.IsVertex x) :
    x.val ∈ interior (T.carrier ∪ U.carrier) := by
  let H : HingePlacement T U e f (T.sharedEdgeIdentification U e f same) :=
    { place := AffineIsometryEquiv.refl ℝ Plane
      joined := fun _ => rfl
      opposite := T.opposite_of_shared_edge U e f same disjoint }
  obtain ⟨r, positive, covered⟩ := H.exists_ball_cover x regular
  have cover : Metric.ball x.val r ⊆ T.carrier ∪ U.carrier := by
    simpa only [H, AffineIsometryEquiv.coe_refl, Set.image_id] using covered
  apply interior_mono cover
  rw [Metric.isOpen_ball.interior_eq]
  exact Metric.mem_ball_self positive

theorem shared_edge_mem_interior_of_subsets (T U : Triangle) (e f : Fin 3)
    (same : T.edge e = U.edge f)
    (disjoint : Disjoint (interior T.carrier) (interior U.carrier))
    {region : Set Plane} (first : T.carrier ⊆ region) (last : U.carrier ⊆ region)
    (x : T.Edge e) (regular : ¬ T.IsVertex x) : x.val ∈ interior region :=
  interior_mono (Set.union_subset first last)
    (T.shared_edge_mem_interior_union U e f same disjoint x regular)

end Unfoldings.Triangle
