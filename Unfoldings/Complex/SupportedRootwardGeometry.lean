module

public import Unfoldings.Complex.SupportedRootwardChain

/-! Both original endpoints of every actual surviving rootward bank are parent iterates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

variable (i : Fin (Q.length + 1))
  (single : (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) = 1)
  (m : ℕ) (length : P.distanceToRoot (C.contourOriginalVertex S Q i) = m + 2)

/-- The far endpoint of every actual current bank is the next original parent iterate. -/
theorem rootwardParentBankChain_far_original_of_boundary_roots (k : Fin (m + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        (C.boundaryTurn _
          ((F.rootwardParentBankChain_of_boundary_roots S boundary_roots Q starts i single m
            length).point k))) =
      P.parent^[k.val + 2] (C.contourOriginalVertex S Q i) := by
  let bank := rootwardParentBank_of_boundary_roots S boundary_roots Q starts i single m length k
  have data := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i bank.val
    bank.property.1 bank.property.2.1 bank.property.2.2
  have original := rootwardParentBank_original_of_boundary_roots S boundary_roots Q starts i single
    m length k
  exact data.2.2.2.trans ((congrArg P.parent original).trans
    (Function.iterate_succ_apply' P.parent (k.val + 1) (C.contourOriginalVertex S Q i)).symm)

end Unfoldings.SpatialFolding
