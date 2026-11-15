module

public import Unfoldings.Complex.SelectedContourHistory
public import Unfoldings.Complex.ParentBankEndpoints
public import Unfoldings.Topology.ParentFrontierNeighbor

/-! The original cyclic contour processes each later fresh source from its actual parent. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

include roots in
/-- Consecutive original vertices of an actual cut bank are original parent neighbors,
or both original boundary roots. -/
theorem selected_bank_original_neighbors (p : C.BoundaryEnd (C.selectedRetain S)) :
    let a := C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p)
    let b := C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) (C.boundaryTurn (C.selectedRetain S) p))
    P.parent b = a ∨ P.parent a = b ∨ (a ∈ P.roots ∧ b ∈ P.roots) := by
  dsimp only
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) p).1
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with old | ⟨s, side, named⟩
  · have left_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).left bank) ∈ P.roots :=
      roots.symm ▸ C.relativeBoundaryVertex_old_left (Set.subset_univ _) bank old
    have right_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).right bank) ∈ P.roots :=
      roots.symm ▸ C.relativeBoundaryVertex_old_right (Set.subset_univ _) bank old
    refine Or.inr (Or.inr ?_)
    change C.relativeBoundaryVertex (Set.subset_univ _)
        (C.boundaryEndAsVertex (C.selectedRetain S) p) ∈ P.roots ∧
      C.relativeBoundaryVertex (Set.subset_univ _)
        (C.boundaryEndAsVertex (C.selectedRetain S) (C.boundaryTurn (C.selectedRetain S) p)) ∈
          P.roots
    rcases C.boundaryGraph_bank_link (C.selectedRetain S) p with
      ⟨first, last⟩ | ⟨first, last⟩
    · rw [first, last]
      exact ⟨left_root, right_root⟩
    · rw [first, last]
      exact ⟨right_root, left_root⟩
  · obtain ⟨e, same⟩ := (C.selectedCutSeamEquiv S).surjective s
    rw [← same] at named
    rcases C.selected_parent_bank_endpoints S e.val e.property p side named with forward | backward
    · exact Or.inr (Or.inl (by rw [forward.1, forward.2]))
    · exact Or.inl (by rw [backward.1, backward.2])

variable (Q : C.BoundaryContour (C.selectedRetain S))

/-- The original vertex label at a named actual bank-contour position. -/
def contourOriginalVertex (i : Fin (Q.length + 1)) : C.Vertex Set.univ :=
  C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i))

@[simp] theorem selectedContourSeeds_getElem (i : Fin (Q.length + 1)) :
    (C.selectedContourSeeds S Q)[i.val]'(by
      simp only [selectedContourSeeds, List.length_ofFn]
      exact i.isLt) = C.contourOriginalVertex S Q i := by
  simp only [selectedContourSeeds, List.getElem_ofFn]
  rfl

include roots in
/-- The actual original cyclic bank order traverses only parent edges and original rim edges. -/
theorem contourOriginalVertex_neighbors (i : Fin Q.length) :
    P.parent (C.contourOriginalVertex S Q i.succ) = C.contourOriginalVertex S Q i.castSucc ∨
      P.parent (C.contourOriginalVertex S Q i.castSucc) = C.contourOriginalVertex S Q i.succ ∨
      (C.contourOriginalVertex S Q i.castSucc ∈ P.roots ∧
        C.contourOriginalVertex S Q i.succ ∈ P.roots) := by
  have next := C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes i.castSucc
  rw [show finRotate (Q.length + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt] at next
  have actual := congrArg (C.relativeBoundaryVertex (Set.subset_univ _)) next
  have neighbors := C.selected_bank_original_neighbors S roots (Q.cycle.point i.castSucc)
  change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point i.castSucc))) =
    C.contourOriginalVertex S Q i.succ at actual
  rw [actual] at neighbors
  exact neighbors

/-- The constructed processed state immediately before an actual original contour position. -/
def contourFrontier (i : Fin (Q.length + 1)) : P.ParentFrontier :=
  P.initialFrontier.run ((C.selectedContourSeeds S Q).take i.val)

theorem contourFrontier_succ (i : Fin Q.length) :
    C.contourFrontier S Q i.succ =
      (C.contourFrontier S Q i.castSucc).process (C.contourOriginalVertex S Q i.castSucc) := by
  have step := (P.initialFrontier).run_take_succ (C.selectedContourSeeds S Q)
    ⟨i.val, by simp only [selectedContourSeeds, List.length_ofFn]; omega⟩
  dsimp only at step
  have at_index := C.selectedContourSeeds_getElem S Q i.castSucc
  dsimp only [Fin.val_castSucc] at at_index
  rw [at_index] at step
  simpa only [contourFrontier, Fin.val_succ, Fin.val_castSucc] using step

theorem previous_contour_vertex_processed (i : Fin Q.length) :
    C.contourOriginalVertex S Q i.castSucc ∈ (C.contourFrontier S Q i.succ).processed := by
  rw [C.contourFrontier_succ S Q i]
  exact ((C.contourFrontier S Q i.castSucc).mem_process_iff _ _).mpr
    (Or.inr (P.ancestor_refl _))

include roots in
/-- Every fresh original source after the first contour position has its actual predecessor
as parent, so no unprocessed internal junction is hidden in the fresh branch. -/
theorem fresh_contour_parent (i : Fin Q.length)
    (fresh : C.contourOriginalVertex S Q i.succ ∉ (C.contourFrontier S Q i.succ).processed) :
    P.parent (C.contourOriginalVertex S Q i.succ) = C.contourOriginalVertex S Q i.castSucc :=
  (C.contourFrontier S Q i.succ).parent_eq_of_fresh_neighbor
    (C.previous_contour_vertex_processed S Q i) fresh
    (C.contourOriginalVertex_neighbors S roots Q i)

include roots in
/-- After the initial branch, the actual original contour schedules only singleton fresh
branches. Existing saved stems still need their physical identification. -/
theorem fresh_contour_contactTime (i : Fin Q.length)
    (fresh : C.contourOriginalVertex S Q i.succ ∉ (C.contourFrontier S Q i.succ).processed) :
    (C.contourFrontier S Q i.succ).contactTime (C.contourOriginalVertex S Q i.succ) = 1 :=
  (C.contourFrontier S Q i.succ).contactTime_eq_one_of_fresh_neighbor
    (C.previous_contour_vertex_processed S Q i) fresh
    (C.contourOriginalVertex_neighbors S roots Q i)

end Unfoldings.TriangleComplex
