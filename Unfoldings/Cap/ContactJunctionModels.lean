module

public import Unfoldings.Cap.SelectedJunctionModels
public import Unfoldings.Topology.ParentFrontierContact

/-! Constructed fresh-branch contacts supply the actual selected junction models. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (frontier : P.ParentFrontier) (seed : C.Vertex Set.univ)
  (nonempty : 0 < frontier.contactTime seed)
  (w : C.Vertex (C.selectedRetain S))
  (nonroot : C.vertexForgetCuts (Set.subset_univ _) w ∉ P.roots)
  (original : C.vertexForgetCuts (Set.subset_univ _) w = P.parent^[frontier.contactTime seed] seed)

include K roots Q nonroot nonempty original in
/-- A nonempty constructed fresh branch gives a genuine split fan at its actual nonroot
contact, without a supplied incoming-child or splitting certificate. -/
theorem contact_junction_totalAngle_lt_full :
    C.totalAngle (C.selectedRetain S) w < 2 * Real.pi := by
  have incoming : P.parent (frontier.contactPredecessor seed) =
      C.vertexForgetCuts (Set.subset_univ _) w :=
    (frontier.parent_contactPredecessor seed nonempty).trans original.symm
  exact K.selected_junction_totalAngle_lt_full S roots Q w nonroot
    (frontier.contactPredecessor seed) incoming

include K roots Q nonroot nonempty original in
/-- The first-contact history supplies the original incoming edge for the local metric
remainder model. Its angle increment is actual cap curvature, including flat contacts.
The theorem does not identify an actual physical saved-frontier bank with the model. -/
theorem exists_contact_junction_remainder_model :
    let original := C.totalAngle Set.univ
      (C.vertexForgetCuts (Set.subset_univ (C.selectedRetain S)) w)
    let untouched := C.totalAngle (C.selectedRetain S) w
    ∃ F : CompletedCornerRemainder original untouched ≃ᵢ
      PolygonalPoint (closedAngularSector (2 * Real.pi - untouched)),
      (∀ x : MetricGluing.Total (fun i => PolygonalPoint
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original) i)),
        (F (MetricGluing.point _ (MetricGluing.polygonalCoincident
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original))) x)).val =
            x.2.val) ∧
      (2 * Real.pi - untouched) - (original - untouched) =
        C.interiorAngularDefect Set.univ
          (C.vertexForgetCuts (Set.subset_univ (C.selectedRetain S)) w) ∧
      (2 * Real.pi - untouched) - (original - untouched) ≤
        C.totalInteriorAngularDefect Set.univ := by
  have incoming : P.parent (frontier.contactPredecessor seed) =
      C.vertexForgetCuts (Set.subset_univ _) w :=
    (frontier.parent_contactPredecessor seed nonempty).trans original.symm
  exact K.exists_selected_junction_remainder_model S roots Q w nonroot
    (frontier.contactPredecessor seed) incoming

end Unfoldings.ConvexCap
