module

public import Unfoldings.Complex.SelectedContourNeighbors
public import Unfoldings.Complex.ProcessedParentCuts

/-! Each later fresh contour step removes exactly one original parent seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- A singleton fresh branch cuts exactly its own original parent seam. -/
theorem processedParentRetain_single_step (frontier : P.ParentFrontier)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (single : frontier.contactTime vertex = 1) :
    C.processedParentRetain S (frontier.process vertex) =
      C.processedParentRetain S frontier \ {S.edge ⟨vertex, nonroot⟩} := by
  ext s
  constructor
  · intro kept
    refine ⟨C.processedParentRetain_process_subset S frontier vertex kept, ?_⟩
    intro member
    have same := Set.mem_singleton_iff.mp member
    exact C.parent_cut_at_new_source S frontier vertex nonroot (same ▸ kept)
  · rintro ⟨old, not_parent⟩ e member equal
    rw [frontier.process_processed_eq_insert single] at member
    rcases Set.mem_insert_iff.mp member with same | earlier
    · have labels : e = ⟨vertex, nonroot⟩ := Subtype.ext same
      exact not_parent (Set.mem_singleton_iff.mpr (equal.symm.trans (congrArg S.edge labels)))
    · exact old e earlier equal

variable (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include roots in
/-- Every actual later fresh contour step removes exactly one original seam, whose parent
is the preceding original contour vertex. Coverage, first-contact length and parent identity
are consequences of the original cyclic bank order. -/
theorem fresh_contour_cut_step (i : Fin Q.length)
    (fresh : C.contourOriginalVertex S Q i.succ ∉ (C.contourFrontier S Q i.succ).processed) :
    let vertex := C.contourOriginalVertex S Q i.succ
    let frontier := C.contourFrontier S Q i.succ
    ∃ nonroot : vertex ∉ P.roots,
      C.processedParentRetain S (frontier.process vertex) =
        C.processedParentRetain S frontier \ {S.edge ⟨vertex, nonroot⟩} ∧
      P.parent vertex = C.contourOriginalVertex S Q i.castSucc := by
  have nonroot : C.contourOriginalVertex S Q i.succ ∉ P.roots :=
    fun root => fresh ((C.contourFrontier S Q i.succ).roots root)
  exact ⟨nonroot, C.processedParentRetain_single_step S _ _ nonroot
    (C.fresh_contour_contactTime S roots Q i fresh), C.fresh_contour_parent S roots Q i fresh⟩

end Unfoldings.TriangleComplex
