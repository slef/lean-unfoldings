module

public import Unfoldings.Cap.ProcessedParentBankHeading

/-! Variation of actual intermediate original parent-bank holonomies stays within curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

/-- Enlarging the actual processed set can only increase its measured parent-bank holonomy. -/
theorem processedParentBankHeading_mono (first last : P.ParentFrontier)
    (more : first.processed ⊆ last.processed) (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (processed : vertex ∈ first.processed) :
    K.processedParentBankHeading S roots first vertex nonroot processed ≤
      K.processedParentBankHeading S roots last vertex nonroot (more processed) := by
  rw [K.processedParentBankHeading_eq, K.processedParentBankHeading_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w member
    have actual := (first.mem_processedDescendants vertex w).mp member
    exact (last.mem_processedDescendants vertex w).mpr ⟨more actual.1, actual.2⟩
  · intro w _ _
    exact K.interiorCurvature_nonneg w

/-- Along the original parent path the measured current subtree holonomies are monotone. -/
theorem processedParentBankHeading_ancestor_mono (frontier : P.ParentFrontier)
    (child parent : C.Vertex Set.univ) (ancestor : P.Ancestor child parent)
    (child_nonroot : child ∉ P.roots) (parent_nonroot : parent ∉ P.roots)
    (child_processed : child ∈ frontier.processed)
    (parent_processed : parent ∈ frontier.processed) :
    K.processedParentBankHeading S roots frontier child child_nonroot child_processed ≤
      K.processedParentBankHeading S roots frontier parent parent_nonroot parent_processed := by
  rw [K.processedParentBankHeading_eq, K.processedParentBankHeading_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w member
    have actual := (frontier.mem_processedDescendants child w).mp member
    exact (frontier.mem_processedDescendants parent w).mpr
      ⟨actual.1, actual.2.trans P ancestor⟩
  · intro w _ _
    exact K.interiorCurvature_nonneg w

/-- Arbitrary measured intermediate parent banks have oscillation at most the original
curvature budget. No path multiplicity or signed-charge certificate is supplied. -/
theorem abs_processedParentBankHeading_sub_le
    (first last : P.ParentFrontier) (a b : C.Vertex Set.univ)
    (a_nonroot : a ∉ P.roots) (b_nonroot : b ∉ P.roots)
    (a_processed : a ∈ first.processed) (b_processed : b ∈ last.processed) :
    |K.processedParentBankHeading S roots first a a_nonroot a_processed -
      K.processedParentBankHeading S roots last b b_nonroot b_processed| ≤
        C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨first_nonnegative, first_bound⟩ :=
    K.processedParentBankHeading_bounds S roots first a a_nonroot a_processed
  obtain ⟨last_nonnegative, last_bound⟩ :=
    K.processedParentBankHeading_bounds S roots last b b_nonroot b_processed
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Unfoldings.ConvexCap
