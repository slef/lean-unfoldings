module

public import Unfoldings.Cap.Topology
public import Unfoldings.Cap.JunctionRemainderModel
public import Unfoldings.Complex.RootwardBoundaryStep
public import Unfoldings.Complex.ProcessedJunctionCopies

/-! Actual rootward ancestor banks supply their own intrinsic sector and junction models. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1)) (j k : C.RootwardBank S Q i)
  (parent : P.parent (C.contourOriginalVertex S Q j.val) = C.contourOriginalVertex S Q k.val)

include K roots starts parent in
/-- The actual current rootward corner is genuinely split. Both original edge incidence
and the covering current contour are constructed, without a supplied sibling-copy choice. -/
theorem exists_rootward_fan_sibling :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    let w := C.boundaryEndVertex retain
      (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1)
    ∃ z : C.Vertex retain, w ≠ z ∧
      C.vertexForgetCuts (Set.subset_univ _) z = C.vertexForgetCuts (Set.subset_univ _) w := by
  have first := C.future_current_bank_rootward S roots Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  have last := C.future_current_bank_rootward S roots Q starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  let frontier := C.contourFrontier S Q i
  let current := K.folding.processedParentBoundaryContour S roots frontier K.diskHomeomorph
  exact C.exists_other_processed_junction_copy S frontier roots current _ last.1 last.2.1
    (C.contourOriginalVertex S Q j.val) first.2.1 parent

include roots starts in
private theorem rootward_fan_internal :
    ¬ C.IsBoundaryVertex Set.univ (C.contourOriginalVertex S Q k.val) := by
  have data := C.future_current_bank_rootward S roots Q starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  exact fun boundary => data.1 (roots.symm ▸ boundary)

include K roots starts parent in
/-- A strict full-turn bound for the actual rootward fan, including flat original vertices. -/
theorem rootward_fan_totalAngle_lt_full :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    C.totalAngle retain (C.boundaryEndVertex retain
      (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1)) < 2 * Real.pi := by
  obtain ⟨z, distinct, same⟩ := K.exists_rootward_fan_sibling S roots Q starts i j k parent
  exact K.split_bank_totalAngle_lt_full _ z distinct same
    (rootward_fan_internal S roots Q starts i k)

include K roots starts parent in
/-- The original incident corner fan gives an actual whole-ball metric sector chart at
the current rootward junction. No global current development is assumed. -/
theorem exists_rootward_fan_corner_chart :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    let w := C.boundaryEndVertex retain
      (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1)
    ∃ r : ℝ, 0 < r ∧ ∃ a : PolygonalPoint (closedAngularSector (C.totalAngle retain w)),
      a.val = 0 ∧ Nonempty (Metric.eball (C.vertexPoint retain w) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball a (ENNReal.ofReal r)) := by
  obtain ⟨z, distinct, same⟩ := K.exists_rootward_fan_sibling S roots Q starts i j k parent
  exact K.exists_split_bank_corner_chart _ z distinct same
    (rootward_fan_internal S roots Q starts i k)

include K roots starts parent in
/-- Complete this actual original rootward fan by its original defect sector. The remainder
has the complementary width and charges exactly the junction's original curvature. Matching
this local construction through the physically attached gap patches remains separate. -/
theorem exists_rootward_fan_remainder_model :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    let original := C.totalAngle Set.univ (C.contourOriginalVertex S Q k.val)
    let untouched := C.totalAngle retain (C.boundaryEndVertex retain
      (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1))
    ∃ E : CompletedCornerRemainder original untouched ≃ᵢ
      PolygonalPoint (closedAngularSector (2 * Real.pi - untouched)),
      (∀ x : MetricGluing.Total (fun b => PolygonalPoint
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original) b)),
        (E (MetricGluing.point _ (MetricGluing.polygonalCoincident
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original))) x)).val =
            x.2.val) ∧
      (2 * Real.pi - untouched) - (original - untouched) =
        C.interiorAngularDefect Set.univ (C.contourOriginalVertex S Q k.val) ∧
      (2 * Real.pi - untouched) - (original - untouched) ≤
        C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨z, distinct, same⟩ := K.exists_rootward_fan_sibling S roots Q starts i j k parent
  simpa only [TriangleComplex.contourOriginalVertex,
    TriangleComplex.survivingBoundaryEnd, TriangleComplex.boundaryEndVertex,
    C.vertexForgetCuts_vertexOfCorner] using!
      K.exists_split_junction_remainder_model _ z distinct same
        (rootward_fan_internal S roots Q starts i k)

end Unfoldings.ConvexCap
