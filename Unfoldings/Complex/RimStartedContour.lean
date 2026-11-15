module

public import Unfoldings.Complex.SelectedContourNeighbors
public import Unfoldings.Complex.BoundaryContourRotation
public import Unfoldings.Topology.ParentFrontierSingleton

/-! Starting an actual cut contour at the original rim removes the exceptional first branch. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include roots Q in
/-- Rotation retains the actual directed banks and can start at any original boundary root. -/
theorem exists_rim_started_contour (vertex : C.Vertex Set.univ) (_root : vertex ∈ P.roots) :
    ∃ R : C.BoundaryContour (C.selectedRetain S),
      C.contourOriginalVertex S R 0 = vertex := by
  obtain ⟨i, at_vertex⟩ := List.mem_ofFn.mp (C.mem_selectedContourSeeds S roots Q vertex)
  refine ⟨Q.rotate C i, ?_⟩
  change C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ ((Q.rotate C i).cycle.first)) = vertex
  rw [BoundaryContour.rotate_first]
  exact at_vertex

variable (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include roots starts in
/-- Every step, including the first, has at most one fresh original parent seam. -/
theorem rim_contour_contactTime_le_one (i : Fin (Q.length + 1)) :
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
    · exact (C.fresh_contour_contactTime S roots Q j old).le

include roots starts in
/-- The intermediate processed set is exactly the original rim and the already visited
original contour vertices. No unseen ancestors need to be marked in advance. -/
theorem rim_contour_processed_iff (i : Fin (Q.length + 1)) (w : C.Vertex Set.univ) :
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
        (C.rim_contour_contactTime_le_one S roots Q starts k.castSucc)]
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
