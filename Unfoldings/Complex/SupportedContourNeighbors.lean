module

public import Unfoldings.Complex.SupportedContourHistory
public import Unfoldings.Complex.RimStartedContour

/-! Original contour neighbors and singleton fresh steps allow unused isolated roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)

include boundary_roots in
/-- Consecutive original vertices of an actual cut bank are original parent neighbors,
or both original boundary roots. -/
theorem selected_bank_original_neighbors_of_boundary_roots
    (p : C.BoundaryEnd (C.selectedRetain S)) :
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
      boundary_roots (C.relativeBoundaryVertex_old_left (Set.subset_univ _) bank old)
    have right_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).right bank) ∈ P.roots :=
      boundary_roots (C.relativeBoundaryVertex_old_right (Set.subset_univ _) bank old)
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

include boundary_roots in
/-- The actual original cyclic bank order traverses only parent edges and original rim edges. -/
theorem contourOriginalVertex_neighbors_of_boundary_roots (i : Fin Q.length) :
    P.parent (C.contourOriginalVertex S Q i.succ) = C.contourOriginalVertex S Q i.castSucc ∨
      P.parent (C.contourOriginalVertex S Q i.castSucc) = C.contourOriginalVertex S Q i.succ ∨
      (C.contourOriginalVertex S Q i.castSucc ∈ P.roots ∧
        C.contourOriginalVertex S Q i.succ ∈ P.roots) := by
  have next := C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes i.castSucc
  rw [show finRotate (Q.length + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt] at next
  have actual := congrArg (C.relativeBoundaryVertex (Set.subset_univ _)) next
  have neighbors := C.selected_bank_original_neighbors_of_boundary_roots S boundary_roots
    (Q.cycle.point i.castSucc)
  change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point i.castSucc))) =
    C.contourOriginalVertex S Q i.succ at actual
  rw [actual] at neighbors
  exact neighbors

include boundary_roots in
/-- Every fresh original source after the first contour position has its actual predecessor
as parent, so no unprocessed internal junction is hidden in the fresh branch. -/
theorem fresh_contour_parent_of_boundary_roots (i : Fin Q.length)
    (fresh : C.contourOriginalVertex S Q i.succ ∉ (C.contourFrontier S Q i.succ).processed) :
    P.parent (C.contourOriginalVertex S Q i.succ) = C.contourOriginalVertex S Q i.castSucc :=
  (C.contourFrontier S Q i.succ).parent_eq_of_fresh_neighbor
    (C.previous_contour_vertex_processed S Q i) fresh
    (C.contourOriginalVertex_neighbors_of_boundary_roots S boundary_roots Q i)

include boundary_roots in
/-- After the initial branch, the actual original contour schedules only singleton fresh
branches. Existing saved stems still need their physical identification. -/
theorem fresh_contour_contactTime_of_boundary_roots (i : Fin Q.length)
    (fresh : C.contourOriginalVertex S Q i.succ ∉ (C.contourFrontier S Q i.succ).processed) :
    (C.contourFrontier S Q i.succ).contactTime (C.contourOriginalVertex S Q i.succ) = 1 :=
  (C.contourFrontier S Q i.succ).contactTime_eq_one_of_fresh_neighbor
    (C.previous_contour_vertex_processed S Q i) fresh
    (C.contourOriginalVertex_neighbors_of_boundary_roots S boundary_roots Q i)

variable (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include boundary_roots starts in
/-- Every step, including the first, has at most one fresh original parent seam. -/
theorem rim_contour_contactTime_le_one_of_boundary_roots (i : Fin (Q.length + 1)) :
    (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have processed : C.contourOriginalVertex S Q 0 ∈ (C.contourFrontier S Q 0).processed :=
      (C.contourFrontier S Q 0).roots starts
    rw [(C.contourFrontier S Q 0).contactTime_eq_zero_iff _ |>.mpr processed]
    exact Nat.zero_le _
  · by_cases old : C.contourOriginalVertex S Q j.succ ∈
        (C.contourFrontier S Q j.succ).processed
    · rw [(C.contourFrontier S Q j.succ).contactTime_eq_zero_iff _ |>.mpr old]
      exact Nat.zero_le _
    · exact (C.fresh_contour_contactTime_of_boundary_roots S boundary_roots Q j old).le

include boundary_roots starts in
/-- The intermediate processed set is exactly the marked roots and the already visited
original contour vertices. Unused isolated roots require no contour visit. -/
theorem rim_contour_processed_iff_of_boundary_roots
    (i : Fin (Q.length + 1)) (w : C.Vertex Set.univ) :
    w ∈ (C.contourFrontier S Q i).processed ↔
      w ∈ P.roots ∨ ∃ j : Fin (Q.length + 1),
        j.val < i.val ∧ C.contourOriginalVertex S Q j = w := by
  induction i using Fin.induction with
  | zero =>
    change w ∈ P.roots ↔ _
    simp only [Fin.val_zero, Nat.not_lt_zero, false_and, exists_false, or_false]
  | succ k ih =>
    rw [C.contourFrontier_succ S Q k,
      (C.contourFrontier S Q k.castSucc).process_processed_eq_insert_of_le_one
        (C.rim_contour_contactTime_le_one_of_boundary_roots S boundary_roots Q starts k.castSucc)]
    change w = C.contourOriginalVertex S Q k.castSucc ∨
      w ∈ (C.contourFrontier S Q k.castSucc).processed ↔ _
    rw [ih]
    constructor
    · rintro (same | root | ⟨j, before, at_vertex⟩)
      · exact Or.inr ⟨k.castSucc, by simp, same.symm⟩
      · exact Or.inl root
      · exact Or.inr ⟨j, by simpa only [Fin.val_succ, Fin.val_castSucc] using
          (Nat.lt_succ_of_lt before), at_vertex⟩
    · rintro (root | ⟨j, before, at_vertex⟩)
      · exact Or.inr (Or.inl root)
      · by_cases earlier : j.val < k.val
        · exact Or.inr (Or.inr ⟨j, earlier, at_vertex⟩)
        · have same : j = k.castSucc := Fin.ext (by
            simp only [Fin.val_succ, Fin.val_castSucc] at before ⊢
            omega)
          exact Or.inl (by simpa only [same] using at_vertex.symm)

end Unfoldings.TriangleComplex
