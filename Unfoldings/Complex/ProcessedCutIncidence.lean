module

public import Unfoldings.Complex.ProcessedCutBoundary
public import Unfoldings.Complex.WeightedBoundaryIncidence

/-!
# Weighted counts of actual intermediate cut copies

When weights vanish on the original rim, summing them over actual cut copies
is exactly summing both ends of each currently processed original parent edge.
This accounts for branching without a planar embedding or an Euler premise.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier) (roots : P.roots = C.relativeCutRoots Set.univ)

/-- Actual original nonroot selectors whose parent seams are currently cut. -/
abbrev ProcessedParentSelector :=
  {e : {v : C.Vertex Set.univ // v ∉ P.roots} // e.val ∈ frontier.processed}

instance processedParentSelector_fintype : Fintype (C.ProcessedParentSelector frontier) :=
  Fintype.ofFinite _

/-- Every intermediate cut keeps the actual original active selector and seam label. -/
def processedCutSeamEquiv : C.ProcessedParentSelector frontier ≃
    C.RelativeCutSeam (C.processedParentRetain S frontier) Set.univ :=
  Equiv.ofBijective (fun e => ⟨S.edge e.val, Set.mem_univ _,
    (C.not_mem_processedParentRetain_iff S frontier _).mpr ⟨e.val, e.property, rfl⟩⟩) ⟨by
    intro a b equal
    apply Subtype.ext
    exact S.edge_injective (congrArg Subtype.val equal), by
    intro s
    obtain ⟨e, processed, named⟩ :=
      (C.not_mem_processedParentRetain_iff S frontier s.val).mp s.property.2
    exact ⟨⟨e, processed⟩, Subtype.ext named⟩⟩

/-- Intermediate bank endpoints are the actual endpoints of their original selected edge. -/
theorem processedParentCut_endpoint_weights (weight : C.Vertex Set.univ → ℝ)
    (e : C.ProcessedParentSelector frontier) (side : Bool) :
    weight (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.processedParentRetain S frontier)).left
        (C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
          (C.processedCutSeamEquiv S frontier e) side))) +
    weight (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.processedParentRetain S frontier)).right
        (C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
          (C.processedCutSeamEquiv S frontier e) side))) =
      weight e.val.val + weight (P.parent e.val.val) := by
  have link := C.relativeCutGraph_bank_link (Set.subset_univ _)
    (C.processedCutSeamEquiv S frontier e) side
  change C.seamGraph.IsLink (S.edge e.val) _ _ at link
  rcases link.eq_and_eq_or_eq_and_eq (S.link e.val) with ⟨first, last⟩ | ⟨first, last⟩
  · rw [first, last]
  · rw [first, last, add_comm]

include roots in
/-- Actual cut-copy multiplicity equals selected-edge endpoint multiplicity away from the rim. -/
theorem sum_processed_vertex_weights {n : ℕ}
    (cycle : (C.boundarySystem (C.processedParentRetain S frontier)).Chain n)
    (closes : C.boundaryMate (C.processedParentRetain S frontier)
      (C.boundaryTurn (C.processedParentRetain S frontier) cycle.last) = cycle.first)
    (covers : ∀ p, cycle.Visited p)
    (weight : C.Vertex Set.univ → ℝ) (zero_roots : ∀ v ∈ P.roots, weight v = 0)
    (zero_unprocessed : ∀ v, v ∉ frontier.processed → weight v = 0) :
    (∑ w : C.Vertex (C.processedParentRetain S frontier),
      weight (C.vertexForgetCuts (Set.subset_univ _) w)) =
        ∑ e : C.ProcessedParentSelector frontier,
          (weight e.val.val + weight (P.parent e.val.val)) := by
  classical
  let small := C.processedParentRetain S frontier
  let := C.finite_boundaryBank small
  let := C.finite_boundaryBank Set.univ
  let := Fintype.ofFinite (C.BoundaryBank small)
  let := Fintype.ofFinite (C.BoundaryBank Set.univ)
  let bank_weight (bank : C.BoundaryBank small) : ℝ :=
    weight (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph small).left bank)) +
    weight (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph small).right bank))
  have old_zero (bank : C.BoundaryBank Set.univ) :
      bank_weight (C.oldBoundaryBank (Set.subset_univ small) bank) = 0 := by
    have left_root := C.relativeBoundaryVertex_old_left (Set.subset_univ small)
      (C.oldBoundaryBank (Set.subset_univ small) bank) bank.property
    have right_root := C.relativeBoundaryVertex_old_right (Set.subset_univ small)
      (C.oldBoundaryBank (Set.subset_univ small) bank) bank.property
    exact show weight _ + weight _ = 0 by
      rw [zero_roots _ (roots.symm ▸ left_root), zero_roots _ (roots.symm ▸ right_root), add_zero]
  have new_sum : (∑ s : C.RelativeCutSeam small Set.univ,
      ∑ side : Bool, bank_weight (C.relativeCutBank small Set.univ s side)) =
        2 * ∑ v : C.ProcessedParentSelector frontier,
          (weight v.val.val + weight (P.parent v.val.val)) := by
    rw [← (C.processedCutSeamEquiv S frontier).sum_comp
      (fun s => ∑ side : Bool, bank_weight (C.relativeCutBank small Set.univ s side))]
    change (∑ v : C.ProcessedParentSelector frontier,
      ∑ side : Bool, bank_weight (C.relativeCutBank small Set.univ
        (C.processedCutSeamEquiv S frontier v) side)) = _
    have per (v : C.ProcessedParentSelector frontier) (side : Bool) :
        bank_weight (C.relativeCutBank small Set.univ
          (C.processedCutSeamEquiv S frontier v) side) =
            weight v.val.val + weight (P.parent v.val.val) :=
      C.processedParentCut_endpoint_weights S frontier weight v side
    simp only [per, Fintype.sum_bool]
    rw [Finset.sum_add_distrib]
    ring
  have banks := (C.relativeBoundaryBankEquiv (Set.subset_univ small)).sum_comp bank_weight
  change (∑ a : C.BoundaryBank Set.univ ⊕ (C.RelativeCutSeam small Set.univ × Bool),
    bank_weight (Sum.elim (C.oldBoundaryBank (Set.subset_univ small))
      (fun p => C.relativeCutBank small Set.univ p.1 p.2) a)) = ∑ bank, bank_weight bank at banks
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    old_zero, Finset.sum_const_zero, zero_add] at banks
  rw [new_sum] at banks
  have zero_internal (w : C.Vertex small) (internal : ¬ C.IsBoundaryVertex small w) :
      weight (C.vertexForgetCuts (Set.subset_univ small) w) = 0 := by
    apply zero_unprocessed
    intro processed
    exact internal (C.processedCut_boundary_of_processed S frontier roots w processed)
  have incidence := C.sum_boundaryBank_weighted_incidence small cycle closes covers
    (fun w => weight (C.vertexForgetCuts (Set.subset_univ small) w)) zero_internal
  change (∑ bank, bank_weight bank) =
    2 * ∑ w, weight (C.vertexForgetCuts (Set.subset_univ small) w) at incidence
  rw [← banks] at incidence
  linarith

end Unfoldings.TriangleComplex
