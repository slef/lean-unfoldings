module

public import Unfoldings.Cap.JunctionRemainderModel
public import Unfoldings.Cap.Topology
public import Unfoldings.Complex.ProcessedJunctionCopies
public import Unfoldings.Topology.ParentFrontierContact

/-! The actual intermediate cut disk supplies its own original first-contact junction models. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (frontier : P.ParentFrontier) (seed : C.Vertex Set.univ) (fresh : seed ∉ frontier.processed)
  (w : C.Vertex (C.processedParentRetain S (frontier.process seed)))
  (nonroot : C.vertexForgetCuts (Set.subset_univ _) w ∉ P.roots)
  (original : C.vertexForgetCuts (Set.subset_univ _) w = P.parent^[frontier.contactTime seed] seed)

include K roots fresh nonroot original in
private theorem processed_contact_sibling :
    ∃ z : C.Vertex (C.processedParentRetain S (frontier.process seed)), w ≠ z ∧
      C.vertexForgetCuts (Set.subset_univ _) z = C.vertexForgetCuts (Set.subset_univ _) w := by
  let next := frontier.process seed
  have nonempty : 0 < frontier.contactTime seed := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact fresh ((frontier.contactTime_eq_zero_iff seed).mp zero)
  have processed : C.vertexForgetCuts (Set.subset_univ _) w ∈ next.processed :=
    Or.inl (original.symm ▸ frontier.contact_mem seed)
  have child_processed : frontier.contactPredecessor seed ∈ next.processed :=
    (frontier.mem_process_iff seed _).mpr (Or.inr ⟨frontier.contactTime seed - 1, rfl⟩)
  have incoming : P.parent (frontier.contactPredecessor seed) =
      C.vertexForgetCuts (Set.subset_univ _) w :=
    (frontier.parent_contactPredecessor seed nonempty).trans original.symm
  let Q := K.folding.processedParentBoundaryContour S roots next K.diskHomeomorph
  exact C.exists_other_processed_junction_copy S next roots Q w nonroot processed
    (frontier.contactPredecessor seed) child_processed incoming

include roots nonroot in
private theorem processed_contact_internal :
    ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ _) w) := by
  simpa only [roots, TriangleComplex.relativeCutRoots, Set.mem_ofPred_eq] using nonroot

include K roots fresh nonroot original in
/-- The actual cut-cap contact has a strict complementary aperture at this intermediate
stage, without a supplied contour, child edge or splitting certificate. -/
theorem processed_contact_totalAngle_lt_full :
    C.totalAngle (C.processedParentRetain S (frontier.process seed)) w < 2 * Real.pi := by
  obtain ⟨z, distinct, same⟩ :=
    K.processed_contact_sibling S roots frontier seed fresh w nonroot original
  exact K.split_bank_totalAngle_lt_full w z distinct same
    (processed_contact_internal S roots frontier seed w nonroot)

include K roots fresh nonroot original in
/-- The constructed first-contact history supplies the local remainder model of the
actual intermediate original cut disk. The covering bank contour and current sibling copy
are constructed. Identifying the physical saved-frontier region remains separate. -/
theorem exists_processed_contact_remainder_model :
    let original := C.totalAngle Set.univ
      (C.vertexForgetCuts (Set.subset_univ (C.processedParentRetain S (frontier.process seed))) w)
    let untouched := C.totalAngle (C.processedParentRetain S (frontier.process seed)) w
    ∃ F : CompletedCornerRemainder original untouched ≃ᵢ
      PolygonalPoint (closedAngularSector (2 * Real.pi - untouched)),
      (∀ x : MetricGluing.Total (fun i => PolygonalPoint
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original) i)),
        (F (MetricGluing.point _ (MetricGluing.polygonalCoincident
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original))) x)).val =
            x.2.val) ∧
      (2 * Real.pi - untouched) - (original - untouched) =
        C.interiorAngularDefect Set.univ
          (C.vertexForgetCuts
            (Set.subset_univ (C.processedParentRetain S (frontier.process seed))) w) ∧
      (2 * Real.pi - untouched) - (original - untouched) ≤
        C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨z, distinct, same⟩ :=
    K.processed_contact_sibling S roots frontier seed fresh w nonroot original
  exact K.exists_split_junction_remainder_model w z distinct same
    (processed_contact_internal S roots frontier seed w nonroot)

end Unfoldings.ConvexCap
