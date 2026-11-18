module

public import Unfoldings.Complex.AncestorPathCuts

/-! Original directed parent endpoints recognize banks surviving in the source-path cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (p : C.BoundaryEnd (C.selectedRetain S)) (base : C.Vertex Set.univ)

local notation "vertex" => C.vertexForgetCuts (Set.subset_univ _)
  (C.boundaryEndVertex (C.selectedRetain S) p)

include roots in
/-- The original directed parent bank is retained precisely on its named ancestor path. -/
theorem parent_bank_survives_source_path
    (nonroot : vertex ∉ P.roots)
    (parent : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ p)) = P.parent vertex)
    (ancestor : P.Ancestor base vertex) :
    C.IsBoundaryEdge (C.ancestorPathRetain S base) (C.germEdge p.val) := by
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) p).1
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with rim | ⟨s, side, named⟩
  · let original : C.BoundaryEnd Set.univ := ⟨p.val, rim⟩
    exact (nonroot (roots (C.boundaryEndAsVertex Set.univ original).property)).elim
  · obtain ⟨e, same⟩ := (C.selectedCutSeamEquiv S).surjective s
    rw [← same] at named
    rcases C.selected_parent_bank_endpoints S e.val e.property p side named with forward | reverse
    · apply (C.selected_parent_bank_ancestorPath_iff S base e.val e.property p side named).mpr
      exact forward.1 ▸ ancestor
    · have desired : P.parent vertex = e.val := parent.symm.trans reverse.2
      have up := P.ascending vertex nonroot
      rw [desired] at up
      have down := P.ascending e.val e.property
      rw [← reverse.1] at down
      exact (lt_asymm up down).elim

end Unfoldings.TriangleComplex
