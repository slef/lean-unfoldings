module

public import Unfoldings.Complex.SubtreeContour

/-!
# Original endpoint order on actual parent banks

A parent bank starting outside its descendant subtree runs from the parent to
the child. Starting inside gives the reverse order. These are actual original
vertex classes, before any planar placement is chosen.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- Reversing a boundary bank moves its raw corner to the far corner of its germ. -/
theorem boundaryTurn_corner {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    (C.boundaryTurn retain p).val.1 = C.germFarCorner p.val := by
  obtain ⟨⟨bank, b⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  exact (C.germFarCorner_germOfEndpoint bank.val b).symm

/-- Both endpoints of an actual parent bank are the child and its original parent. -/
theorem selected_parent_bank_endpoints (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side) :
    (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex (C.selectedRetain S) p) = e ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S) (C.boundaryTurn (C.selectedRetain S) p)) =
          P.parent e) ∨
    (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex (C.selectedRetain S) p) =
        P.parent e ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) p)) = e) := by
  have link := C.relativeCutGraph_bank_link
    (Set.subset_univ (C.selectedRetain S))
    (C.selectedParentCut S e nonroot) side
  rw [← named] at link
  have selected := (S.graph_isLink_iff.mp (C.selectedCut_to_selection_link S link)).2
  have actual : C.seamGraph.IsLink (S.edge ⟨e, nonroot⟩)
      (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex (C.selectedRetain S) p))
      (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) p))) := by
    rcases C.boundaryGraph_bank_link (C.selectedRetain S) p with
      ⟨first, last⟩ | ⟨first, last⟩
    · rw [← first, ← last] at selected
      exact selected
    · rw [← first, ← last] at selected
      exact selected.symm
  exact actual.eq_and_eq_or_eq_and_eq (S.link ⟨e, nonroot⟩)

/-- The entrance bank points from the original parent to the original child. -/
theorem selected_parent_bank_enters (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side)
    (outside : ¬ P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p)) e) :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex (C.selectedRetain S) p) =
        P.parent e ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S) (C.boundaryTurn (C.selectedRetain S) p)) = e := by
  rcases C.selected_parent_bank_endpoints S e nonroot p side named with first | last
  · exact (outside (first.1 ▸ P.ancestor_refl e)).elim
  · exact last

/-- The exit bank points from the original child to the original parent. -/
theorem selected_parent_bank_leaves (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side)
    (inside : P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p)) e) :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex (C.selectedRetain S) p) = e ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S) (C.boundaryTurn (C.selectedRetain S) p)) =
          P.parent e := by
  rcases C.selected_parent_bank_endpoints S e nonroot p side named with first | last
  · exact first
  · exact (P.not_ancestor_parent_self nonroot (last.1 ▸ inside)).elim

end Unfoldings.TriangleComplex
