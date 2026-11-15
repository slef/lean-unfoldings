module

public import Unfoldings.Cap.Topology
public import Unfoldings.Complex.ContourCutSteps
public import Unfoldings.Complex.ProcessedCutBoundary
public import Unfoldings.Complex.SingleBoundaryCopySplit

/-! A singleton fresh branch splits an actual parent corner into two angle-conserving copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ) (fresh : vertex ∉ frontier.processed)
  (single : frontier.contactTime vertex = 1)

include K roots fresh single in
/-- A one-edge fresh branch determines the old parent copy it splits. Its two new copies
are derived from the actual intermediate cut disks and carry exactly the old corner angle.
No old parent-copy choice, splitting multiplicity or angle-conservation premise is supplied. -/
theorem exists_processed_parent_copy_split :
    let old := C.processedParentRetain S frontier
    let next := C.processedParentRetain S (frontier.process vertex)
    let inclusion := C.processedParentRetain_process_subset S frontier vertex
    ∃ parent : C.Vertex old,
      C.vertexForgetCuts (Set.subset_univ old) parent = P.parent vertex ∧
      ∃ a b : C.Vertex next, a ≠ b ∧
        (∀ w, C.vertexForgetCuts inclusion w = parent ↔ w = a ∨ w = b) ∧
        C.totalAngle next a + C.totalAngle next b = C.totalAngle old parent := by
  classical
  dsimp only
  let old := C.processedParentRetain S frontier
  let next := C.processedParentRetain S (frontier.process vertex)
  let inclusion := C.processedParentRetain_process_subset S frontier vertex
  have nonroot : vertex ∉ P.roots := fun root => fresh (frontier.roots root)
  let edge := S.edge ⟨vertex, nonroot⟩
  have kept : edge ∈ old := by
    by_contra cut
    exact C.no_processed_cut_at_fresh S frontier vertex fresh edge cut (P.parent vertex)
      (S.link ⟨vertex, nonroot⟩)
  let s : C.RelativeCutSeam next old :=
    ⟨edge, kept, C.parent_cut_at_new_source S frontier vertex nonroot⟩
  have single_cut : next = old \ {s.val} :=
    C.processedParentRetain_single_step S frontier vertex nonroot single
  have parent_processed : P.parent vertex ∈ frontier.processed := by
    have member := frontier.contact_mem vertex
    simpa only [single, Function.iterate_one] using member
  have genuine : vertex ≠ P.parent vertex := by
    intro same
    exact (ne_of_lt (P.ascending vertex nonroot)) (congrArg P.height same)
  let before := K.folding.processedParentBoundaryContour S roots frontier K.diskHomeomorph
  let after := K.folding.processedParentBoundaryContour S roots (frontier.process vertex)
    K.diskHomeomorph
  have mapped (b : Bool) : C.vertexForgetCuts (Set.subset_univ old)
      (C.relativeCutVertex next old s b) = C.seamVertex edge b := rfl
  have build (side : Bool)
      (parent_at : C.vertexForgetCuts (Set.subset_univ old)
        (C.relativeCutVertex next old s side) = P.parent vertex)
      (child_at : C.vertexForgetCuts (Set.subset_univ old)
        (C.relativeCutVertex next old s (!side)) = vertex) :
      ∃ parent : C.Vertex old,
        C.vertexForgetCuts (Set.subset_univ old) parent = P.parent vertex ∧
        ∃ a b : C.Vertex next, a ≠ b ∧
          (∀ w, C.vertexForgetCuts inclusion w = parent ↔ w = a ∨ w = b) ∧
          C.totalAngle next a + C.totalAngle next b = C.totalAngle old parent := by
    let parent := C.relativeCutVertex next old s side
    have different : C.relativeCutVertex next old s (!side) ≠ parent := by
      intro same
      have original := congrArg (C.vertexForgetCuts (Set.subset_univ old)) same
      rw [child_at, parent_at] at original
      exact genuine original
    have boundary : C.IsBoundaryVertex old parent :=
      C.processedCut_boundary_of_processed S frontier roots parent
        (parent_at.symm ▸ parent_processed)
    have endpoint :
        (C.relativeCutVertex next old s false = parent ∧
          C.relativeCutVertex next old s true ≠ parent) ∨
        (C.relativeCutVertex next old s true = parent ∧
          C.relativeCutVertex next old s false ≠ parent) := by
      cases side
      · exact Or.inl ⟨rfl, different⟩
      · exact Or.inr ⟨rfl, different⟩
    obtain ⟨a, b, distinct, copies, angles⟩ :=
      C.exists_two_boundary_copies_of_single_cut inclusion after before s single_cut parent
        boundary endpoint
    exact ⟨parent, parent_at, a, b, distinct, copies, angles⟩
  rcases S.link ⟨vertex, nonroot⟩ with forward | backward
  · exact build true ((mapped true).trans forward.2.symm) ((mapped false).trans forward.1.symm)
  · exact build false ((mapped false).trans backward.2.symm) ((mapped true).trans backward.1.symm)

end Unfoldings.ConvexCap
