module

public import Unfoldings.Complex.ReturnSourceBank

/-! The returning source bank joins the actual untouched parent stem after restored excursions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include F roots starts in
/-- The return case uses the literal new source bank and the parent's actual upcoming exit. -/
theorem returnSource_boundary_step (j : Fin Q.length)
    (returns : P.parent (C.contourOriginalVertex S Q j.castSucc) =
      C.contourOriginalVertex S Q j.succ)
    (k : C.RootwardBank S Q j.succ)
    (at_parent : C.contourOriginalVertex S Q k.val = C.contourOriginalVertex S Q j.succ) :
    let retain := C.processedParentRetain S (C.contourFrontier S Q j.succ)
    C.boundaryMate retain (C.boundaryTurn retain (C.returnSourceBank S Q j returns)) =
      C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1 := by
  let retain := C.processedParentRetain S (C.contourFrontier S Q j.succ)
  let inclusion := C.selectedRetain_subset_processed S (C.contourFrontier S Q j.succ)
  have ordered : j.val < k.val.val := by
    have bound := k.property.1
    change j.val + 1 ≤ k.val.val at bound
    omega
  have next_vertex (l : Fin (Q.length + 1)) :
      C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point l)) =
      C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) l)) :=
    congrArg Subtype.val (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes l)
  have same_original : C.contourOriginalVertex S Q (finRotate (Q.length + 1) j.castSucc) =
      C.contourOriginalVertex S Q k.val := by
    rw [show finRotate (Q.length + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt]
    exact at_parent.symm
  have no_bank (l : Fin (Q.length + 1)) (after : j.val < l.val) (before : l.val < k.val.val) :
      ¬ C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point l).val) := by
    intro current
    have future : j.succ.val ≤ l.val := by change j.val + 1 ≤ l.val; omega
    have last_data := C.future_current_bank_rootward_of_boundary_roots S roots Q starts j.succ k.val
      k.property.1 k.property.2.1 k.property.2.2
    by_cases rim : C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point l).val)
    · let original_end : C.BoundaryEnd Set.univ := ⟨(Q.cycle.point l).val, rim⟩
      have root : C.contourOriginalVertex S Q l ∈ P.roots :=
        roots (C.boundaryEndAsVertex Set.univ original_end).property
      have ancestor : P.Ancestor (C.contourOriginalVertex S Q j.castSucc)
          (C.contourOriginalVertex S Q k.val) := by
        rw [at_parent]
        exact ⟨1, returns⟩
      have inside := C.contour_subtree_no_reentry_of_boundary_roots S roots Q starts
        (C.contourOriginalVertex S Q k.val) last_data.1 j.castSucc l k.val after.le before.le
        ancestor (P.ancestor_refl _)
      exact P.descendant_nonroot last_data.1 inside root
    · let middle : C.RootwardBank S Q j.succ := ⟨l, future, current, rim⟩
      have before_parent :=
        (C.rootward_bank_index_lt_iff_of_boundary_roots S roots Q starts j.succ middle k).mp before
      have data := C.future_current_bank_rootward_of_boundary_roots S roots Q starts j.succ l
        future current rim
      have reverse : P.Ancestor (C.contourOriginalVertex S Q k.val)
          (C.contourOriginalVertex S Q middle.val) := at_parent.symm ▸ data.2.2.1
      exact before_parent.2 (P.ancestor_antisymm before_parent.1 reverse)
  by_cases separated : j.val + 1 < k.val.val
  · obtain ⟨b, _before, next_b, different, enters, leaves, stable⟩ :=
      finRotate_open_bank_interval j.castSucc k.val separated
    have restored (l : Fin (Q.length + 1)) (inside : j.val < l.val ∧ l.val < k.val.val) :
        ¬ C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point l).val) :=
      no_bank l inside.1 inside.2
    have original : C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) j.castSucc))) =
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) b))) := by
      rw [next_b]
      exact same_original
    have outgoing : C.IsBoundaryEdge retain
        (C.germEdge (Q.cycle.point (finRotate (Q.length + 1) b)).val) :=
      next_b.symm ▸ k.property.2.1
    have step := F.pruned_contour_boundary_step_of_boundary_roots S roots Q inclusion
      (fun l => j.val < l.val ∧ l.val < k.val.val) j.castSucc b different
      enters leaves stable original restored (C.returnSourceBank_survives S Q j returns) outgoing
    simpa only [next_b, TriangleComplex.returnSourceBank] using step
  · have next_j : finRotate (Q.length + 1) j.castSucc = k.val := by
      rw [show finRotate (Q.length + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt]
      apply Fin.ext
      change j.val + 1 = k.val.val
      omega
    let p := C.boundaryTurn retain
      (C.survivingBoundaryEnd (Q.cycle.point j.castSucc)
        (C.returnSourceBank_survives S Q j returns))
    let q := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    have same : C.boundaryEndVertex retain q = C.boundaryEndVertex retain p := by
      change C.vertexForgetCuts inclusion (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point k.val)) = C.vertexForgetCuts inclusion
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j.castSucc)))
      rw [next_vertex, next_j]
    have distinct : q ≠ p := by
      intro equal
      apply Q.cycle.disjoint k.val j.castSucc
      exact Subtype.ext (congrArg (fun e : C.BoundaryEnd retain => e.val) equal)
    exact ((C.exists_unique_other_boundaryEnd retain p).unique ⟨distinct, same⟩
      (C.boundaryMate_spec retain p)).symm


end Unfoldings.SpatialFolding
