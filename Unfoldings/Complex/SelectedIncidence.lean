module

public import Unfoldings.Complex.SelectedSubtreeBoundary
public import Unfoldings.Complex.BoundaryIncidence

/-!
# Weighted counts of actual selected-cut vertex copies

When weights vanish on the original rim, summing them over actual cut copies
is exactly summing the weights of both ends of each selected original edge.
This accounts for branching without a planar embedding or an Euler premise.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

/-- The actual new cut seams are in bijection with their nonroot selectors. -/
def selectedCutSeamEquiv : {v : C.Vertex Set.univ // v ∉ P.roots} ≃
    C.RelativeCutSeam (C.selectedRetain S) Set.univ :=
  Equiv.ofBijective (fun v => C.selectedParentCut S v.val v.property) ⟨by
    intro a b equal
    exact S.edge_injective (congrArg Subtype.val equal), by
    intro s
    obtain ⟨v, same⟩ := not_not.mp s.property.2
    exact ⟨v, Subtype.ext same⟩⟩

theorem selectedParentCut_endpoint_weights (weight : C.Vertex Set.univ → ℝ)
    (v : {v : C.Vertex Set.univ // v ∉ P.roots}) (side : Bool) :
    weight (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.selectedRetain S)).left
        (C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S v.val v.property) side))) +
    weight (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.selectedRetain S)).right
        (C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S v.val v.property) side))) =
      weight v.val + weight (P.parent v.val) := by
  have link := (C.selectedCut_link_iff S _ _ _).mp
    (C.relativeCutGraph_bank_link (Set.subset_univ _)
      (C.selectedParentCut S v.val v.property) side)
  rcases link.eq_and_eq_or_eq_and_eq (S.link v) with ⟨first, last⟩ | ⟨first, last⟩
  · rw [first, last]
  · rw [first, last, add_comm]

include roots in
/-- Actual cut-copy multiplicity equals selected-edge endpoint multiplicity away from the rim. -/
theorem sum_selected_vertex_weights {n : ℕ}
    (cycle : (C.boundarySystem (C.selectedRetain S)).Chain n)
    (closes : C.boundaryMate (C.selectedRetain S)
      (C.boundaryTurn (C.selectedRetain S) cycle.last) = cycle.first)
    (covers : ∀ p, cycle.Visited p)
    (weight : C.Vertex Set.univ → ℝ) (zero_roots : ∀ v ∈ P.roots, weight v = 0) :
    (∑ w : C.Vertex (C.selectedRetain S),
      weight (C.vertexForgetCuts (Set.subset_univ _) w)) =
        ∑ v : C.Vertex Set.univ, (weight v + weight (P.parent v)) := by
  classical
  let small := C.selectedRetain S
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
        2 * ∑ v : {v : C.Vertex Set.univ // v ∉ P.roots},
          (weight v.val + weight (P.parent v.val)) := by
    rw [← (C.selectedCutSeamEquiv S).sum_comp
      (fun s => ∑ side : Bool, bank_weight (C.relativeCutBank small Set.univ s side))]
    change (∑ v : {v : C.Vertex Set.univ // v ∉ P.roots},
      ∑ side : Bool, bank_weight (C.relativeCutBank small Set.univ
        (C.selectedParentCut S v.val v.property) side)) = _
    have per (v : {v : C.Vertex Set.univ // v ∉ P.roots}) (side : Bool) :
        bank_weight (C.relativeCutBank small Set.univ
          (C.selectedParentCut S v.val v.property) side) =
            weight v.val + weight (P.parent v.val) :=
      C.selectedParentCut_endpoint_weights S weight v side
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
  have incidence := C.sum_boundaryBank_incidence_all small cycle closes covers
    (C.selectedCut_all_vertices_boundary S roots)
    (fun w => weight (C.vertexForgetCuts (Set.subset_univ small) w))
  have nonroots : (∑ v : C.Vertex Set.univ, (weight v + weight (P.parent v))) =
      ∑ v : {v : C.Vertex Set.univ // v ∉ P.roots},
        (weight v.val + weight (P.parent v.val)) := by
    rw [← Finset.sum_subtype (p := fun v => v ∉ P.roots)
      (Finset.univ.filter (fun v => v ∉ P.roots)) (by simp)
      (fun v => weight v + weight (P.parent v))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases root : v ∈ P.roots
    · simp only [root, not_true_eq_false, ite_false, P.fixed_root v root, zero_roots v root,
        add_zero]
    · simp only [root, not_false_eq_true, ite_true]
  rw [nonroots]
  change (∑ w, weight (C.vertexForgetCuts (Set.subset_univ small) w)) = _
  change (∑ bank, bank_weight bank) =
    2 * ∑ w, weight (C.vertexForgetCuts (Set.subset_univ small) w) at incidence
  linarith [banks]

end Unfoldings.TriangleComplex
