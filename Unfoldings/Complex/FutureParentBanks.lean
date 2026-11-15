module

public import Unfoldings.Complex.LinearSubtreeBanks
public import Unfoldings.Complex.RimStartedContour
public import Unfoldings.Complex.CurrentBankSelectors

/-! Surviving future parent banks follow the original ancestor path. -/

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
/-- A still upcoming bank whose original selector is processed must be the rootward exit
of an ancestor of the current source. An already completed side branch cannot occur here. -/
theorem future_processed_parent_bank (i j : Fin (Q.length + 1)) (future : i.val ≤ j.val)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ (C.contourFrontier S Q i).processed) (other : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S vertex nonroot) other) :
    P.Ancestor (C.contourOriginalVertex S Q i) vertex ∧
      C.contourOriginalVertex S Q j = vertex ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j))) = P.parent vertex := by
  obtain ⟨enter, leave, side, ordered, interval, first, last⟩ :=
    C.exists_named_linear_subtree_interval S roots Q starts vertex nonroot
  obtain root | ⟨before, past, at_vertex⟩ :=
    (C.rim_contour_processed_iff S roots Q starts i vertex).mp processed
  · exact (nonroot root).elim
  · have before_bounds := (interval before).mp (at_vertex.symm ▸ P.ancestor_refl vertex)
    have after_entry : enter.val < i.val := before_bounds.1.trans past
    have at_exit : j = leave := by
      rcases C.named_parent_bank_index_eq S Q vertex nonroot enter leave j side other
          first last named with at_entry | at_leave
      · have values := congrArg Fin.val at_entry
        omega
      · exact at_leave
    have inside : P.Ancestor (C.contourOriginalVertex S Q i) vertex :=
      (interval i).mpr ⟨after_entry, by simpa only [at_exit] using future⟩
    have at_leave : P.Ancestor (C.contourOriginalVertex S Q leave) vertex :=
      (interval leave).mpr ⟨ordered, le_rfl⟩
    have endpoints := C.selected_parent_bank_leaves S vertex nonroot
      (Q.cycle.point leave) (!side) last at_leave
    exact ⟨inside, by simpa only [at_exit, contourOriginalVertex] using endpoints.1,
      by simpa only [at_exit] using endpoints.2⟩

include roots starts in
/-- Every processed nonroot ancestor supplies exactly one upcoming original parent bank.
It is already a bank of the actual current cut, with its original side label. -/
theorem existsUnique_future_parent_bank (i : Fin (Q.length + 1))
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (_processed : vertex ∈ (C.contourFrontier S Q i).processed)
    (ancestor : P.Ancestor (C.contourOriginalVertex S Q i) vertex) :
    ∃! j : Fin (Q.length + 1), i.val ≤ j.val ∧
      ∃ side, (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side := by
  obtain ⟨enter, leave, side, _ordered, interval, first, last⟩ :=
    C.exists_named_linear_subtree_interval S roots Q starts vertex nonroot
  have bounds := (interval i).mp ancestor
  refine ⟨leave, ⟨bounds.2, !side, last⟩, ?_⟩
  rintro j ⟨future, other, named⟩
  rcases C.named_parent_bank_index_eq S Q vertex nonroot enter leave j side other
      first last named with at_entry | at_leave
  · have values := congrArg Fin.val at_entry
    omega
  · exact at_leave

include roots starts in
/-- An upcoming nonrim bank survives in the current cut exactly when it is the rootward
original parent bank of a processed ancestor. Both original endpoints are identified. -/
theorem future_current_bank_rootward (i j : Fin (Q.length + 1)) (future : i.val ≤ j.val)
    (current : C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.germEdge (Q.cycle.point j).val))
    (not_rim : ¬ C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point j).val)) :
    let vertex := C.contourOriginalVertex S Q j
    vertex ∉ P.roots ∧ vertex ∈ (C.contourFrontier S Q i).processed ∧
      P.Ancestor (C.contourOriginalVertex S Q i) vertex ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j))) = P.parent vertex := by
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with old | ⟨s, side, named⟩
  · exact (not_rim old).elim
  · obtain ⟨e, same⟩ := (C.selectedCutSeamEquiv S).surjective s
    rw [← same] at named
    have processed := (C.selected_parent_bank_current_iff S (C.contourFrontier S Q i)
      e.val e.property (Q.cycle.point j) side named).mp current
    obtain ⟨ancestor, at_vertex, endpoint⟩ := C.future_processed_parent_bank S roots Q starts
      i j future e.val e.property processed side named
    dsimp only
    rw [at_vertex]
    exact ⟨e.property, processed, ancestor, endpoint⟩

include roots starts in
/-- The rootward selector is the actual original vertex at the bank's starting endpoint. -/
theorem future_current_bank_named (i j : Fin (Q.length + 1)) (future : i.val ≤ j.val)
    (current : C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.germEdge (Q.cycle.point j).val))
    (not_rim : ¬ C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point j).val)) :
    ∃ nonroot : C.contourOriginalVertex S Q j ∉ P.roots, ∃ side,
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S (C.contourOriginalVertex S Q j) nonroot) side := by
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with old | ⟨s, side, named⟩
  · exact (not_rim old).elim
  · obtain ⟨e, same⟩ := (C.selectedCutSeamEquiv S).surjective s
    rw [← same] at named
    have processed := (C.selected_parent_bank_current_iff S (C.contourFrontier S Q i)
      e.val e.property (Q.cycle.point j) side named).mp current
    have at_vertex := (C.future_processed_parent_bank S roots Q starts
      i j future e.val e.property processed side named).2.1
    rw [at_vertex]
    exact ⟨e.property, side, named⟩

end Unfoldings.TriangleComplex
