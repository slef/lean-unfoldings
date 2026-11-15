module

public import Unfoldings.Complex.SelectedCuts
public import Unfoldings.Complex.SelectedContourHistory
public import Unfoldings.Topology.ParentFrontierReach

/-! Actual retained original seams at intermediate first-contact processing stages. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- Cut exactly the original parent seams whose selectors have already been processed. -/
def processedParentRetain (frontier : P.ParentFrontier) : Set C.Seam :=
  {s | ∀ e : {v : C.Vertex Set.univ // v ∉ P.roots},
    e.val ∈ frontier.processed → S.edge e ≠ s}

/-- Each current cut retains its actual original selector and seam identity. -/
theorem not_mem_processedParentRetain_iff (frontier : P.ParentFrontier) (s : C.Seam) :
    s ∉ C.processedParentRetain S frontier ↔
      ∃ e : {v : C.Vertex Set.univ // v ∉ P.roots},
        e.val ∈ frontier.processed ∧ S.edge e = s := by
  classical
  simp only [processedParentRetain, Set.mem_ofPred_eq, not_forall, not_not, exists_prop]

/-- Before any branch is processed no original seam has been cut. -/
theorem processedParentRetain_initial : C.processedParentRetain S P.initialFrontier = Set.univ := by
  apply Set.eq_univ_of_forall
  intro s e member
  exact (e.property member).elim

/-- Every intermediate retained-seam set restores only seams from the final original forest. -/
theorem selectedRetain_subset_processed (frontier : P.ParentFrontier) :
    C.selectedRetain S ⊆ C.processedParentRetain S frontier := by
  rintro s kept e _ equal
  exact kept ⟨e, equal⟩

/-- Processing more vertices only removes seams; the intrinsic cut spaces are the actual
retained-seam realizations, with the usual forgetting-cuts maps between them. -/
theorem processedParentRetain_antitone {first last : P.ParentFrontier}
    (more : first.processed ⊆ last.processed) :
    C.processedParentRetain S last ⊆ C.processedParentRetain S first :=
  fun _ kept e member => kept e (more member)

/-- Once the whole original forest is processed its retained set is exactly the final cut. -/
theorem processedParentRetain_eq_selected (frontier : P.ParentFrontier)
    (all : frontier.processed = Set.univ) :
    C.processedParentRetain S frontier = C.selectedRetain S := by
  apply Set.Subset.antisymm ?_ (C.selectedRetain_subset_processed S frontier)
  rintro s kept ⟨e, equal⟩
  exact kept e (all ▸ Set.mem_univ _) equal

/-- The constructed processing step removes only its genuinely fresh original seams. -/
theorem processedParentRetain_process_subset (frontier : P.ParentFrontier)
    (vertex : C.Vertex Set.univ) :
    C.processedParentRetain S (frontier.process vertex) ⊆ C.processedParentRetain S frontier :=
  C.processedParentRetain_antitone S (fun _ member => Or.inl member)

/-- The original contour's actual complete schedule ends at the exact original selected cut. -/
theorem processedParentRetain_contour_final
    (roots : P.roots = C.relativeCutRoots Set.univ)
    (Q : C.BoundaryContour (C.selectedRetain S)) :
    C.processedParentRetain S ((P.initialFrontier).run (C.selectedContourSeeds S Q)) =
      C.selectedRetain S :=
  C.processedParentRetain_eq_selected S _ (C.initial_run_selectedContourSeeds S roots Q)

/-- No already processed parent edge is incident to a fresh original source. -/
theorem no_processed_cut_at_fresh (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ)
    (fresh : vertex ∉ frontier.processed) (s : C.Seam)
    (cut : s ∉ C.processedParentRetain S frontier) (w : C.Vertex Set.univ)
    (link : C.seamGraph.IsLink s vertex w) : False := by
  obtain ⟨e, member, named⟩ := (C.not_mem_processedParentRetain_iff S frontier s).mp cut
  have original := S.link e
  rw [named] at original
  rcases link.eq_and_eq_or_eq_and_eq original with same | reverse
  · exact fresh (same.1 ▸ member)
  · exact fresh (reverse.1 ▸ frontier.closed e.val member)

/-- After adjoining a fresh branch, its source has exactly its own outgoing parent seam cut.
Other final-forest children are still unprocessed; no final-forest leaf premise is needed. -/
theorem unique_processed_cut_at_new_source (frontier : P.ParentFrontier)
    (vertex : C.Vertex Set.univ) (fresh : vertex ∉ frontier.processed)
    (nonroot : vertex ∉ P.roots) (s : C.Seam)
    (cut : s ∉ C.processedParentRetain S (frontier.process vertex)) (w : C.Vertex Set.univ)
    (link : C.seamGraph.IsLink s vertex w) : s = S.edge ⟨vertex, nonroot⟩ := by
  obtain ⟨e, member, named⟩ :=
    (C.not_mem_processedParentRetain_iff S (frontier.process vertex) s).mp cut
  have original := S.link e
  rw [named] at original
  have selector : e.val = vertex := by
    rcases link.eq_and_eq_or_eq_and_eq original with same | reverse
    · exact same.1.symm
    · rcases (frontier.mem_process_iff vertex e.val).mp member with old | ancestor
      · exact (fresh (reverse.1 ▸ frontier.closed e.val old)).elim
      · have returns : P.Ancestor (P.parent e.val) e.val := by
          rw [← reverse.1]
          exact ancestor
        exact (P.not_ancestor_parent_self e.property returns).elim
  have labels : e = ⟨vertex, nonroot⟩ := Subtype.ext selector
  exact named.symm.trans (congrArg S.edge labels)

/-- The new source's parent seam really is cut at that processing step. -/
theorem parent_cut_at_new_source (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    S.edge ⟨vertex, nonroot⟩ ∉ C.processedParentRetain S (frontier.process vertex) := by
  apply (C.not_mem_processedParentRetain_iff S (frontier.process vertex) _).mpr
  exact ⟨⟨vertex, nonroot⟩,
    (frontier.mem_process_iff vertex vertex).mpr (Or.inr (P.ancestor_refl vertex)), rfl⟩

end Unfoldings.TriangleComplex
