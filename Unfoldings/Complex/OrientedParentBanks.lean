module

public import Unfoldings.Complex.ParentBankEndpoints
public import Unfoldings.Complex.BoundaryContour

/-! Name opposite original parent banks using actual oriented subtree entry and exit. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include roots in
/-- Orientation fixes the two distinctly named sides without a planar development. -/
theorem opposite_parent_banks_of_exits (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (enter leave : Fin (Q.length + 1)) (different : enter ≠ leave)
    (enters : ¬ C.SubtreeBoundaryInside S Q.cycle vertex enter ∧
      C.SubtreeBoundaryInside S Q.cycle vertex (finRotate (Q.length + 1) enter))
    (leaves : C.SubtreeBoundaryInside S Q.cycle vertex leave ∧
      ¬ C.SubtreeBoundaryInside S Q.cycle vertex (finRotate (Q.length + 1) leave)) :
    ∃ side,
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) (!side) := by
  obtain ⟨first, named_first⟩ := (C.subtreeCrossingBank_iff S roots vertex nonroot _).mp
    ((C.subtree_boundary_change_iff S Q.cycle Q.closes vertex enter).mpr
      (Or.inr ⟨enters.2, enters.1⟩))
  obtain ⟨last, named_last⟩ := (C.subtreeCrossingBank_iff S roots vertex nonroot _).mp
    ((C.subtree_boundary_change_iff S Q.cycle Q.closes vertex leave).mpr (Or.inl leaves))
  have sides_different : first ≠ last := by
    intro same
    apply different
    apply C.boundaryChain_banks_injective (C.selectedRetain S) Q.cycle
    dsimp only
    rw [named_first, named_last, same]
  have opposite : last = !first := by
    cases first <;> cases last <;> first | rfl | exact (sides_different rfl).elim
  exact ⟨first, named_first, opposite ▸ named_last⟩

end Unfoldings.TriangleComplex
