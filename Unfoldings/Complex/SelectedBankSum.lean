module

public import Unfoldings.Complex.SelectedIncidence

/-!
# Summing actual selected banks in contour order

Weights vanishing on original rim banks can be summed as one pair per selected
original edge. The weights may depend on the actual directed contour bank.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  {n : ℕ} (cycle : (C.boundarySystem (C.selectedRetain S)).Chain n)
  (covers : ∀ p, cycle.Visited p)

include covers in
open scoped Classical in
/-- Sum directed bank weights by their distinctly named original parent seams. -/
theorem sum_selected_bank_weights {V : Type*} [AddCommMonoid V]
    (weight : Fin (n + 1) → V)
    (old_zero : ∀ i, C.IsBoundaryEdge Set.univ
      (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point i)).1.val → weight i = 0)
    (first last : {v : C.Vertex Set.univ // v ∉ P.roots} → Fin (n + 1))
    (side : {v : C.Vertex Set.univ // v ∉ P.roots} → Bool)
    (first_named : ∀ e, (C.boundaryEndEquiv (C.selectedRetain S)
      (cycle.point (first e))).1 = C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S e.val e.property) (side e))
    (last_named : ∀ e, (C.boundaryEndEquiv (C.selectedRetain S)
      (cycle.point (last e))).1 = C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S e.val e.property) (!(side e))) :
    (∑ i, weight i) = ∑ e, (weight (first e) + weight (last e)) := by
  classical
  let small := C.selectedRetain S
  let := C.finite_boundaryBank small
  let := C.finite_boundaryBank Set.univ
  let := Fintype.ofFinite (C.BoundaryBank small)
  let := Fintype.ofFinite (C.BoundaryBank Set.univ)
  let Q := C.boundaryCycleBankEquiv small cycle covers
  let bankWeight (bank : C.BoundaryBank small) := weight (Q.symm bank)
  have old (bank : C.BoundaryBank Set.univ) :
      bankWeight (C.oldBoundaryBank (Set.subset_univ small) bank) = 0 := by
    apply old_zero
    have same := Q.apply_symm_apply (C.oldBoundaryBank (Set.subset_univ small) bank)
    exact (congrArg (fun b : C.BoundaryBank small => b.val) same).symm ▸ bank.property
  have first_eq (e : {v : C.Vertex Set.univ // v ∉ P.roots}) :
      Q.symm (C.relativeCutBank small Set.univ
        (C.selectedParentCut S e.val e.property) (side e)) = first e :=
    Q.symm_apply_eq.mpr (first_named e).symm
  have last_eq (e : {v : C.Vertex Set.univ // v ∉ P.roots}) :
      Q.symm (C.relativeCutBank small Set.univ
        (C.selectedParentCut S e.val e.property) (!(side e))) = last e :=
    Q.symm_apply_eq.mpr (last_named e).symm
  have pair (e : {v : C.Vertex Set.univ // v ∉ P.roots}) :
      (∑ b : Bool, bankWeight (C.relativeCutBank small Set.univ
        (C.selectedParentCut S e.val e.property) b)) =
      weight (first e) + weight (last e) := by
    have a := first_eq e
    have b := last_eq e
    cases h : side e <;> simp only [h, Bool.not_false, Bool.not_true] at a b
    · simp only [Fintype.sum_bool, bankWeight, a, b, add_comm]
    · simp only [Fintype.sum_bool, bankWeight, a, b]
  have banks := (C.relativeBoundaryBankEquiv (Set.subset_univ small)).sum_comp bankWeight
  change (∑ a : C.BoundaryBank Set.univ ⊕ (C.RelativeCutSeam small Set.univ × Bool),
    bankWeight (Sum.elim (C.oldBoundaryBank (Set.subset_univ small))
      (fun p => C.relativeCutBank small Set.univ p.1 p.2) a)) = ∑ bank, bankWeight bank at banks
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    old, Finset.sum_const_zero, zero_add] at banks
  rw [← (C.selectedCutSeamEquiv S).sum_comp
    (fun s => ∑ b : Bool, bankWeight (C.relativeCutBank small Set.univ s b))] at banks
  change (∑ e : {v : C.Vertex Set.univ // v ∉ P.roots},
    ∑ b : Bool, bankWeight (C.relativeCutBank small Set.univ
      (C.selectedParentCut S e.val e.property) b)) = _ at banks
  simp only [pair] at banks
  have ordered := Q.sum_comp bankWeight
  change (∑ i, bankWeight (Q i)) = _ at ordered
  simp only [bankWeight, Q.symm_apply_apply] at ordered
  exact ordered.trans banks.symm

end Unfoldings.TriangleComplex
