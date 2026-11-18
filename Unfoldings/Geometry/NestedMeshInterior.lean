module

public import Unfoldings.Geometry.NestedSpatialSubdivision
public import Unfoldings.Geometry.ConvexCellRegion

/-! Every new face incident inside the old footprint belongs to its complete subdivision. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

/-- A full fine triangle touching the interior of the old footprint has an original parent. -/
theorem nestedPiece_of_incident_interior (cover : T.FaceRefinement U) (i : U.Index) {p : Plane}
    (inside : p ∈ interior (clip family Z)) (incident : p ∈ (U.projectedTriangle i).carrier) :
    i ∈ T.nestedPieceSet U := by
  obtain ⟨q, in_fine, in_old⟩ := ConvexCellRegion.selected_of_incident_interior
    (fun i => (U.projectedTriangle i).carrier) (clip family Z) i
    (U.projectedTriangle i).compact_carrier.isClosed (U.projectedTriangle i).convex_carrier
    (U.projectedTriangle i).interior_nonempty inside incident
  obtain ⟨f, old_member⟩ := Set.mem_iUnion.mp (T.cover.subset (interior_subset in_old))
  obtain ⟨j, contained, member⟩ := cover f q old_member
  by_cases same : i = j
  · subst j
    exact ⟨f, contained⟩
  · have separated := (U.separated same).closure_right isOpen_interior
    rw [(U.projectedTriangle j).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (U.projectedTriangle j).interior_nonempty,
      (U.projectedTriangle j).compact_carrier.isClosed.closure_eq] at separated
    exact (Set.disjoint_left.mp separated in_fine member).elim

end Unfoldings.SpatialEnvelope.Triangulation
