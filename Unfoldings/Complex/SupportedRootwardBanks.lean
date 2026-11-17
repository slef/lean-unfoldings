module

public import Unfoldings.Complex.SupportedSubtreeContour
public import Unfoldings.Complex.RootwardBankOrder

/-! Actual surviving banks enumerate processed ancestors even with unused isolated roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include boundary_roots starts in
/-- A still upcoming bank whose original selector is processed must be the rootward exit
of an ancestor of the current source. An already completed side branch cannot occur here. -/
theorem future_processed_parent_bank_of_boundary_roots (i j : Fin (Q.length + 1)) (future : i.val
  ≤ j.val)
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
    C.exists_named_linear_subtree_interval_of_boundary_roots S boundary_roots Q starts vertex
      nonroot
  obtain root | ⟨before, past, at_vertex⟩ :=
    (C.rim_contour_processed_iff_of_boundary_roots S boundary_roots Q starts i vertex).mp processed
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

include boundary_roots starts in
/-- Every processed nonroot ancestor supplies exactly one upcoming original parent bank.
It is already a bank of the actual current cut, with its original side label. -/
theorem existsUnique_future_parent_bank_of_boundary_roots (i : Fin (Q.length + 1))
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (_processed : vertex ∈ (C.contourFrontier S Q i).processed)
    (ancestor : P.Ancestor (C.contourOriginalVertex S Q i) vertex) :
    ∃! j : Fin (Q.length + 1), i.val ≤ j.val ∧
      ∃ side, (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side := by
  obtain ⟨enter, leave, side, _ordered, interval, first, last⟩ :=
    C.exists_named_linear_subtree_interval_of_boundary_roots S boundary_roots Q starts vertex
      nonroot
  have bounds := (interval i).mp ancestor
  refine ⟨leave, ⟨bounds.2, !side, last⟩, ?_⟩
  rintro j ⟨future, other, named⟩
  rcases C.named_parent_bank_index_eq S Q vertex nonroot enter leave j side other
      first last named with at_entry | at_leave
  · have values := congrArg Fin.val at_entry
    omega
  · exact at_leave

include boundary_roots starts in
/-- An upcoming nonrim bank survives in the current cut exactly when it is the rootward
original parent bank of a processed ancestor. Both original endpoints are identified. -/
theorem future_current_bank_rootward_of_boundary_roots (i j : Fin (Q.length + 1)) (future : i.val
  ≤ j.val)
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
    obtain ⟨ancestor, at_vertex, endpoint⟩ := C.future_processed_parent_bank_of_boundary_roots S
      boundary_roots Q starts
      i j future e.val e.property processed side named
    dsimp only
    rw [at_vertex]
    exact ⟨e.property, processed, ancestor, endpoint⟩

include boundary_roots starts in
/-- The rootward selector is the actual original vertex at the bank's starting endpoint. -/
theorem future_current_bank_named_of_boundary_roots (i j : Fin (Q.length + 1)) (future : i.val ≤
  j.val)
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
    have at_vertex := (C.future_processed_parent_bank_of_boundary_roots S boundary_roots Q starts
      i j future e.val e.property processed side named).2.1
    rw [at_vertex]
    exact ⟨e.property, side, named⟩


/-- Restore precisely the original selector of the actual future bank. -/
def rootwardBankAncestor_of_boundary_roots (i : Fin (Q.length + 1)) (j : C.RootwardBank S Q i) :
    C.RootwardAncestor S Q i :=
  ⟨C.contourOriginalVertex S Q j.val,
    (C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val j.property.1
      j.property.2.1 j.property.2.2).1,
    (C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val j.property.1
      j.property.2.1 j.property.2.2).2.1,
    (C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val j.property.1
      j.property.2.1 j.property.2.2).2.2.1⟩

/-- This is a bijection of actual bank indices with original path vertices: every surviving
bank occurs once, and no original nonroot ancestor is omitted. -/
def rootwardBankEquiv_of_boundary_roots (i : Fin (Q.length + 1)) :
    C.RootwardBank S Q i ≃ C.RootwardAncestor S Q i :=
  Equiv.ofBijective (C.rootwardBankAncestor_of_boundary_roots S boundary_roots Q starts i) ⟨by
    intro j k same
    have labels : C.contourOriginalVertex S Q j.val = C.contourOriginalVertex S Q k.val :=
      congrArg Subtype.val same
    obtain ⟨nonroot, side, first⟩ := C.future_current_bank_named_of_boundary_roots S
      boundary_roots Q starts i j.val
      j.property.1 j.property.2.1 j.property.2.2
    obtain ⟨_, other, last⟩ := C.future_current_bank_named_of_boundary_roots S boundary_roots Q
      starts i k.val
      k.property.1 k.property.2.1 k.property.2.2
    simp only [← labels] at last
    have data := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val
      j.property.1 j.property.2.1 j.property.2.2
    obtain ⟨index, _property, unique⟩ := C.existsUnique_future_parent_bank_of_boundary_roots S
      boundary_roots Q starts i
      (C.contourOriginalVertex S Q j.val) nonroot data.2.1 data.2.2.1
    exact Subtype.ext ((unique j.val ⟨j.property.1, side, first⟩).trans
      (unique k.val ⟨k.property.1, other, last⟩).symm), by
    intro vertex
    obtain ⟨j, ⟨future, side, named⟩, _unique⟩ :=
      C.existsUnique_future_parent_bank_of_boundary_roots S boundary_roots Q starts i
      vertex.val vertex.property.1 vertex.property.2.1 vertex.property.2.2
    have current := (C.selected_parent_bank_current_iff S (C.contourFrontier S Q i)
      vertex.val vertex.property.1 (Q.cycle.point j) side named).mpr vertex.property.2.1
    have not_rim : ¬ C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point j).val) := by
      have raw := congrArg (fun b : C.BoundaryBank (C.selectedRetain S) => b.val) named
      exact fun old => C.relativeCutBank_not_old
        (C.selectedParentCut S vertex.val vertex.property.1) side (raw ▸ old)
    refine ⟨⟨j, future, current, not_rim⟩, Subtype.ext ?_⟩
    exact (C.future_processed_parent_bank_of_boundary_roots S boundary_roots Q starts i j future
      vertex.val
      vertex.property.1 vertex.property.2.1 side named).2.1⟩


end Unfoldings.TriangleComplex
