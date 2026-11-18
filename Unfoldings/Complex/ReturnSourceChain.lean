module

public import Unfoldings.Complex.ReturnSourceBoundaryStep
public import Unfoldings.Topology.ChainConcatenation
public import Unfoldings.Topology.ChainCast

/-! Actual source-to-root chains on contour returns include the newly exposed source edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots) (j : Fin Q.length)
  (returns : P.parent (C.contourOriginalVertex S Q j.castSucc) =
    C.contourOriginalVertex S Q j.succ)

/-- Join the literal returning source edge to the actual untouched parent stem. -/
def returnSourceBankChain (m : ℕ)
    (span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m + 1) :
    (C.boundarySystem
      (C.processedParentRetain S (C.contourFrontier S Q j.succ))).Chain (m + 1) := by
  let retain := C.processedParentRetain S (C.contourFrontier S Q j.succ)
  let base := C.contourOriginalVertex S Q j.succ
  have processed : base ∈ (C.contourFrontier S Q j.succ).processed := by
    dsimp only [base]
    rw [← returns]
    exact (C.contourFrontier S Q j.succ).closed _
      (C.previous_contour_vertex_processed S Q j)
  let stem := F.supportedProcessedBankChain S roots Q starts j.succ base processed
    (P.ancestor_refl base) m span
  let first := (C.boundarySystem retain).singleton (C.returnSourceBank S Q j returns)
  have separated : ∀ i k, first.point i ≠ stem.point k ∧
      first.point i ≠ (C.boundarySystem retain).turn (stem.point k) := by
    intro i k
    let bank := supportedProcessedBank S roots Q starts j.succ base processed
      (P.ancestor_refl base) m span k
    constructor
    · intro same
      have raw := congrArg (fun p : C.BoundaryEnd retain => p.val) same
      have index := Q.cycle.injective (Subtype.ext raw)
      have equal := congrArg Fin.val index
      change j.val = bank.val.val at equal
      have future := bank.property.1
      change j.val + 1 ≤ bank.val.val at future
      omega
    · intro same
      apply Q.cycle.disjoint j.castSucc bank.val
      exact Subtype.ext (congrArg (fun p : C.BoundaryEnd retain => p.val) same)
  have joined : (C.boundarySystem retain).mate ((C.boundarySystem retain).turn first.last) =
      stem.first := by
    let bank := supportedProcessedBank S roots Q starts j.succ base processed
      (P.ancestor_refl base) m span 0
    have named : C.contourOriginalVertex S Q bank.val = C.contourOriginalVertex S Q j.succ := by
      exact supportedProcessedBank_original S roots Q starts j.succ base processed
        (P.ancestor_refl base) m span 0
    exact F.returnSource_boundary_step S roots Q starts j returns bank named
  exact (first.concat stem separated joined).cast (by omega)

/-- The first bank begins at the actual original source. -/
theorem returnSourceBankChain_first_original (m : ℕ)
    (span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m + 1) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        (F.returnSourceBankChain S roots Q starts j returns m span).first) =
      C.contourOriginalVertex S Q j.castSucc := by
  unfold returnSourceBankChain
  erw [PairedInvolutions.System.Chain.cast_first,
    PairedInvolutions.System.Chain.concat_first]
  rfl

/-- Every return-chain bank keeps its exact original source-parent iterate. -/
theorem returnSourceBankChain_original (m : ℕ)
    (span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m + 1)
    (k : Fin (m + 2)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        ((F.returnSourceBankChain S roots Q starts j returns m span).point k)) =
      P.parent^[k.val] (C.contourOriginalVertex S Q j.castSucc) := by
  by_cases zero : k.val = 0
  · have same : k = 0 := Fin.ext zero
    subst k
    exact F.returnSourceBankChain_first_original S roots Q starts j returns m span
  · unfold returnSourceBankChain
    erw [PairedInvolutions.System.Chain.cast_point]
    change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        (PairedInvolutions.System.Chain.concatenatedPoint _ _ _)) = _
    rw [PairedInvolutions.System.Chain.concatenatedPoint, dite_eq_right (by
      change ¬ k.val < 0 + 1
      omega)]
    erw [supportedProcessedBankChain_original]
    rw [← returns, ← Function.iterate_succ_apply]
    congr 1
    change k.val - 1 + 1 = k.val
    omega

/-- The return chain reaches the true original root, without stopping at its parent. -/
theorem returnSourceBankChain_terminal_original (m : ℕ)
    (span : P.distanceToRoot (C.contourOriginalVertex S Q j.succ) = m + 1) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _
        (F.returnSourceBankChain S roots Q starts j returns m span).last)) =
      P.root (C.contourOriginalVertex S Q j.castSucc) := by
  have same_root : P.root (C.contourOriginalVertex S Q j.succ) =
      P.root (C.contourOriginalVertex S Q j.castSucc) := by
    apply P.ancestor_root_unique
      ((show P.Ancestor (C.contourOriginalVertex S Q j.castSucc)
          (C.contourOriginalVertex S Q j.succ) from ⟨1, returns⟩).trans P
        (P.ancestor_root _)) (P.ancestor_root _)
      (P.root_mem _) (P.root_mem _)
  unfold returnSourceBankChain
  erw [PairedInvolutions.System.Chain.cast_last,
    PairedInvolutions.System.Chain.concat_last]
  exact (F.supportedProcessedBankChain_terminal_original S roots Q starts j.succ
    (C.contourOriginalVertex S Q j.succ) _ _ m span).trans same_root

/-- A source whose parent is already a root has its complete finite bank in one edge. -/
def returnSourceRootBankChain :
    (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q j.succ))).Chain 0 :=
  (C.boundarySystem _).singleton (C.returnSourceBank S Q j returns)

/-- The singleton return bank starts at the literal original source. -/
theorem returnSourceRootBankChain_first_original :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (returnSourceRootBankChain S Q j returns).first) =
      C.contourOriginalVertex S Q j.castSucc := rfl

/-- In the one-edge root case the true far endpoint is the original root of the source. -/
theorem returnSourceRootBankChain_terminal_original
    (parent_root : C.contourOriginalVertex S Q j.succ ∈ P.roots) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _
        (returnSourceRootBankChain S Q j returns).last)) =
      P.root (C.contourOriginalVertex S Q j.castSucc) := by
  have far := C.contourBank_finish_original S Q j
  have root := P.ancestor_root_unique (show P.Ancestor
      (C.contourOriginalVertex S Q j.castSucc) (C.contourOriginalVertex S Q j.succ) from
        ⟨1, returns⟩) (P.ancestor_root (C.contourOriginalVertex S Q j.castSucc))
    parent_root (P.root_mem _)
  exact far.trans root

end Unfoldings.SpatialFolding
