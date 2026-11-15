module

public import Unfoldings.Complex.ConsecutiveRootwardBanks
public import Unfoldings.Complex.PrunedContourStep
public import Unfoldings.Topology.LinearBankInterval

/-! Consecutive original ancestor edges form an actual directed bank path in the current cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include F roots starts in
/-- Adjacency is the actual current boundary successor after skipping restored excursions.
The original bank lengths, endpoint flags and full bank parametrizations are retained. -/
theorem rootward_boundary_step (i : Fin (Q.length + 1)) (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    C.boundaryMate retain
        (C.boundaryTurn retain (C.survivingBoundaryEnd (Q.cycle.point j.val) j.property.2.1)) =
      C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1 := by
  let retain := C.processedParentRetain S (C.contourFrontier S Q i)
  let inclusion := C.selectedRetain_subset_processed S (C.contourFrontier S Q i)
  have ordered := C.rootward_bank_order_of_parent S roots Q starts i j k parent
  have at_child := C.future_current_bank_rootward S roots Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  have next_vertex (l : Fin (Q.length + 1)) :
      C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point l)) =
      C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) l)) :=
    congrArg Subtype.val (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes l)
  have same_original : C.contourOriginalVertex S Q (finRotate (Q.length + 1) j.val) =
      C.contourOriginalVertex S Q k.val := by
    change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) j.val))) = _
    rw [← next_vertex]
    exact at_child.2.2.2.trans parent
  by_cases separated : j.val.val + 1 < k.val.val
  · obtain ⟨b, _before, next_b, different, enters, leaves, stable⟩ :=
      finRotate_open_bank_interval j.val k.val separated
    have restored (l : Fin (Q.length + 1)) (inside : j.val.val < l.val ∧ l.val < k.val.val) :
        ¬ C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point l).val) :=
      C.consecutive_rootward_banks_restored S roots Q starts i j k parent l inside.1 inside.2
    have original : C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) j.val))) =
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) b))) := by
      rw [next_b]
      exact same_original
    have outgoing : C.IsBoundaryEdge retain
        (C.germEdge (Q.cycle.point (finRotate (Q.length + 1) b)).val) :=
      next_b.symm ▸ k.property.2.1
    have step := F.pruned_contour_boundary_step S roots Q inclusion
      (fun l => j.val.val < l.val ∧ l.val < k.val.val) j.val b different
      enters leaves stable original restored j.property.2.1 outgoing
    simpa only [next_b] using step
  · have next_j : finRotate (Q.length + 1) j.val = k.val := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (by
        intro at_last
        have values := congrArg Fin.val at_last
        simp only [Fin.val_last] at values
        omega)]
      omega
    let p := C.boundaryTurn retain
      (C.survivingBoundaryEnd (Q.cycle.point j.val) j.property.2.1)
    let q := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    have same : C.boundaryEndVertex retain q = C.boundaryEndVertex retain p := by
      change C.vertexForgetCuts inclusion (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point k.val)) = C.vertexForgetCuts inclusion
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j.val)))
      rw [next_vertex, next_j]
    have distinct : q ≠ p := by
      intro equal
      apply Q.cycle.disjoint k.val j.val
      exact Subtype.ext (congrArg (fun e : C.BoundaryEnd retain => e.val) equal)
    exact ((C.exists_unique_other_boundaryEnd retain p).unique ⟨distinct, same⟩
      (C.boundaryMate_spec retain p)).symm

end Unfoldings.SpatialFolding
