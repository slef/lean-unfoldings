module

public import Unfoldings.Cap.JunctionRemainderModel
public import Unfoldings.Complex.SelectedJunctionCopies

/-! Actual selected parent-child junctions supply their own split-fan and remainder models. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (w : C.Vertex (C.selectedRetain S))
  (nonroot : C.vertexForgetCuts (Set.subset_univ _) w ∉ P.roots)
  (child : C.Vertex Set.univ)
  (parent : P.parent child = C.vertexForgetCuts (Set.subset_univ _) w)

include roots nonroot in
private theorem selected_junction_internal :
    ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ _) w) := by
  simpa only [roots, TriangleComplex.relativeCutRoots, Set.mem_ofPred_eq] using nonroot

include K roots Q nonroot child parent in
/-- An actual selected incoming child and outgoing parent force a genuine complementary
aperture at every named cut copy, with no splitting certificate. -/
theorem selected_junction_totalAngle_lt_full :
    C.totalAngle (C.selectedRetain S) w < 2 * Real.pi := by
  obtain ⟨z, distinct, same⟩ :=
    C.exists_other_selected_junction_copy S roots Q w nonroot child parent
  exact K.split_bank_totalAngle_lt_full w z distinct same
    (selected_junction_internal S roots w nonroot)

include K roots Q nonroot child parent in
/-- The actual cut-cap junction has its own whole intrinsic sector chart. -/
theorem exists_selected_junction_corner_chart :
    ∃ r : ℝ, 0 < r ∧ ∃ a : PolygonalPoint (closedAngularSector
      (C.totalAngle (C.selectedRetain S) w)),
      a.val = 0 ∧ Nonempty (Metric.eball (C.vertexPoint (C.selectedRetain S) w)
        (ENNReal.ofReal r) ≃ᵢ Metric.eball a (ENNReal.ofReal r)) := by
  obtain ⟨z, distinct, same⟩ :=
    C.exists_other_selected_junction_copy S roots Q w nonroot child parent
  exact K.exists_split_bank_corner_chart w z distinct same
    (selected_junction_internal S roots w nonroot)

include K roots Q nonroot child parent in
/-- The actual selected junction supplies the complementary local surgery model and its
curvature charge from original edge incidence, allowing flat original junctions. Physical
saved-frontier placement is not assumed or concluded. -/
theorem exists_selected_junction_remainder_model :
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
  obtain ⟨z, distinct, same⟩ :=
    C.exists_other_selected_junction_copy S roots Q w nonroot child parent
  exact K.exists_split_junction_remainder_model w z distinct same
    (selected_junction_internal S roots w nonroot)

end Unfoldings.ConvexCap
