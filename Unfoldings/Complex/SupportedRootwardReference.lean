module

public import Unfoldings.Complex.SupportedRootwardFans
public import Unfoldings.Complex.RootwardReferenceChain
public import Unfoldings.Complex.RootwardPathFans
public import Unfoldings.Complex.SurvivingBoundaryChain

/-! The constructed current rootward chain has exactly its original path-reference roll. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1))
  (fresh : C.contourOriginalVertex S Q i ∉ (C.contourFrontier S Q i).processed)
  (single : (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) = 1)
  (m : ℕ) (length : P.distanceToRoot (C.contourOriginalVertex S Q i) = m + 2)

/-- The same original parent banks, now in the original cut along just their ancestor path. -/
def rootwardReferenceBankChain_of_boundary_roots :
    (C.boundarySystem (C.ancestorPathRetain S
      (P.parent (C.contourOriginalVertex S Q i)))).Chain m :=
  C.survivingBoundaryChain (C.rootwardPathInclusion S Q i single)
    (F.rootwardParentBankChain_of_boundary_roots S boundary_roots Q starts i single m length)
    (fun k => C.rootward_bank_survives_ancestorPath_of_boundary_roots S boundary_roots Q starts i
      fresh
      (rootwardParentBank_of_boundary_roots S boundary_roots Q starts i single m length k))

/-- The reference follows the same original parent iterates, with no extra or omitted edge. -/
theorem rootwardReferenceBankChain_original_of_boundary_roots (k : Fin (m + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        ((F.rootwardReferenceBankChain_of_boundary_roots S boundary_roots Q starts i fresh single
          m length).point k)) =
      P.parent^[k.val + 1] (C.contourOriginalVertex S Q i) :=
  rootwardParentBank_original_of_boundary_roots S boundary_roots Q starts i single m length k

/-- Equality holds for every unreduced real heading prefix. -/
theorem rootwardReferenceBankChain_rollHeading_of_boundary_roots (k : Fin (m + 1)) :
    C.boundaryChainRollHeading
        (F.rootwardReferenceBankChain_of_boundary_roots S boundary_roots Q starts i fresh single
          m length) k =
      C.boundaryChainRollHeading (F.rootwardParentBankChain_of_boundary_roots S boundary_roots Q
        starts i single m length) k :=
  C.survivingBoundaryChain_rollHeading _ _ _ k

/-- The whole normalized rolls agree point for point, including all hinge positions.
This concerns actual original cut banks; transport through inserted gap patches is separate. -/
theorem rootwardReferenceBankChain_roll_of_boundary_roots :
    C.boundaryChainRoll (F.rootwardReferenceBankChain_of_boundary_roots S boundary_roots Q starts
      i fresh single m length) =
      C.boundaryChainRoll (F.rootwardParentBankChain_of_boundary_roots S boundary_roots Q starts
        i single m length) :=
  C.survivingBoundaryChain_roll _ _ _

end Unfoldings.SpatialFolding
