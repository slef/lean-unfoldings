module

public import Unfoldings.Complex.RootwardBankOrder
public import Unfoldings.Topology.AncestorInterval

/-! Consecutive original parent-path banks have no surviving current contour bank between them. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include roots starts in
/-- All intervening original contour banks are restored. Their entire fresh subtrees can
therefore be skipped when constructing the actual current rootward boundary chain. -/
theorem consecutive_rootward_banks_restored (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val)
    (l : Fin (Q.length + 1)) (after : j.val.val < l.val) (before : l.val < k.val.val) :
    ¬ C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.germEdge (Q.cycle.point l).val) := by
  intro current
  have future : i.val ≤ l.val := j.property.1.trans after.le
  have last_data := C.future_current_bank_rootward S roots Q starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  by_cases rim : C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point l).val)
  · let original_end : C.BoundaryEnd Set.univ := ⟨(Q.cycle.point l).val, rim⟩
    have root : C.contourOriginalVertex S Q l ∈ P.roots :=
      roots.symm ▸ (C.boundaryEndAsVertex Set.univ original_end).property
    have inside := C.contour_subtree_no_reentry S roots Q starts
      (C.contourOriginalVertex S Q k.val) last_data.1 j.val l k.val after.le before.le
      (parent ▸ P.ancestor_parent _) (P.ancestor_refl _)
    exact P.descendant_nonroot last_data.1 inside root
  · let middle : C.RootwardBank S Q i := ⟨l, future, current, rim⟩
    have first := (C.rootward_bank_index_lt_iff S roots Q starts i j middle).mp after
    have last := (C.rootward_bank_index_lt_iff S roots Q starts i middle k).mp before
    have step : P.Ancestor (C.contourOriginalVertex S Q middle.val)
        (P.parent (C.contourOriginalVertex S Q j.val)) := parent.symm ▸ last.1
    rcases P.ancestor_between_parent first.1 step with at_child | at_parent
    · exact first.2 at_child.symm
    · exact last.2 (at_parent.trans parent)

end Unfoldings.TriangleComplex
