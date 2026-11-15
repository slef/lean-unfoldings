module

public import Unfoldings.Complex.OrientedParentBanks
public import Unfoldings.Complex.RestoredBankEndpoints
public import Unfoldings.Complex.ProcessedParentCuts

/-! Unprocessed original parent banks close at both endpoints in every actual intermediate cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S)) (frontier : P.ParentFrontier)
  (vertex : C.Vertex Set.univ) (fresh : vertex ∉ frontier.processed)

include F roots fresh in
/-- The actual entry and exit of an unprocessed subtree have the same child and parent
copies after restoration. This is equality in the current intrinsic cut, not coincidence
in a planar layout, and permits positive original curvature throughout the fresh subtree. -/
theorem exists_unprocessed_parent_banks_closed :
    ∃ enter leave : Fin (Q.length + 1), enter ≠ leave ∧
      (¬ C.SubtreeBoundaryInside S Q.cycle vertex enter ∧
        C.SubtreeBoundaryInside S Q.cycle vertex (finRotate (Q.length + 1) enter)) ∧
      (C.SubtreeBoundaryInside S Q.cycle vertex leave ∧
        ¬ C.SubtreeBoundaryInside S Q.cycle vertex (finRotate (Q.length + 1) leave)) ∧
      C.vertexForgetCuts (C.selectedRetain_subset_processed S frontier)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) enter))) =
        C.vertexForgetCuts (C.selectedRetain_subset_processed S frontier)
          (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point leave)) ∧
      C.vertexForgetCuts (C.selectedRetain_subset_processed S frontier)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) leave))) =
        C.vertexForgetCuts (C.selectedRetain_subset_processed S frontier)
          (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point enter)) := by
  have nonroot : vertex ∉ P.roots := fun root => fresh (frontier.roots root)
  obtain ⟨enter, leave, different, enters, leaves, _stable⟩ :=
    C.exists_oriented_subtree_exits S roots Q.cycle Q.closes Q.covers vertex nonroot
  obtain ⟨side, first, last⟩ :=
    C.opposite_parent_banks_of_exits S roots Q vertex nonroot enter leave different enters leaves
  have entry := C.selected_parent_bank_enters S vertex nonroot (Q.cycle.point enter) side
    first enters.1
  have exit := C.selected_parent_bank_leaves S vertex nonroot (Q.cycle.point leave) (!side)
    last leaves.1
  have kept : S.edge ⟨vertex, nonroot⟩ ∈ C.processedParentRetain S frontier := by
    by_contra cut
    exact C.no_processed_cut_at_fresh S frontier vertex fresh _ cut _ (S.link ⟨vertex, nonroot⟩)
  have turn_bank (j : Fin (Q.length + 1)) :
      (C.boundaryEndEquiv (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j))).1 =
        (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1 := by
    simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  have next (j : Fin (Q.length + 1)) :
      C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j)) =
          C.boundaryEndVertex (C.selectedRetain S)
            (Q.cycle.point (finRotate (Q.length + 1) j)) :=
    congrArg Subtype.val (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes j)
  refine ⟨enter, leave, different, enters, leaves, ?_, ?_⟩
  · rw [← next enter]
    apply F.boundary_end_forgetCuts_eq_of_restored_seam
      (C.selectedRetain_subset_processed S frontier)
      (C.selectedParentCut S vertex nonroot) kept _ _ side
    · exact (turn_bank enter).trans first
    · exact last
    · exact entry.2.trans exit.1.symm
  · rw [← next leave]
    apply F.boundary_end_forgetCuts_eq_of_restored_seam
      (C.selectedRetain_subset_processed S frontier)
      (C.selectedParentCut S vertex nonroot) kept _ _ (!side)
    · exact (turn_bank leave).trans last
    · simpa only [Bool.not_not] using first
    · exact exit.2.trans entry.1.symm

end Unfoldings.SpatialFolding
