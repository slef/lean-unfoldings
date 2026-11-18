module

public import Unfoldings.Complex.ContourParentBanks
public import Unfoldings.Complex.RootwardChainLabels

/-! Source-bank contour tags recover their literal original rootward sides and closed paths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  {retain : Set C.Seam} (included : C.selectedRetain S ⊆ retain) {m : ℕ}
  (chain : (C.boundarySystem retain).Chain m) (source : C.Vertex Set.univ)
  (span : P.distanceToRoot source = m + 1)
  (labels : ∀ k, C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (chain.point k)) = P.parent^[k.val] source)
  (terminal : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (C.boundaryTurn _ chain.last)) = P.root source)
  (tags : ∀ k, ∃ i : Fin (Q.length + 1), (chain.point k).val = (Q.cycle.point i).val)

include included span labels terminal tags in
/-- Every actual source-bank edge is the original rootward exit-side bank, even at the source.
This identifies literal face/corner tags rather than merely folded endpoint positions. -/
theorem sourceBank_original_exit (k : Fin (m + 1)) :
    (chain.point k).val =
      (C.contourParentBank S Q roots starts (P.parent^[k.val] source)
        (P.iterate_lt_distanceToRoot_not_mem source (by rw [span]; exact k.isLt)) false).val := by
  let p : C.BoundaryEnd (C.selectedRetain S) := ⟨(chain.point k).val,
    C.isBoundaryEdge_antitone included (chain.point k).property⟩
  obtain ⟨i, raw⟩ := tags k
  have named : p = Q.cycle.point i := Subtype.ext raw
  have first : C.contourOriginalVertex S Q i = P.parent^[k.val] source := by
    change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (Q.cycle.point i)) = _
    rw [← named]
    exact labels k
  have last : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (Q.cycle.point i))) =
        P.parent (P.parent^[k.val] source) := by
    rw [← named]
    exact (C.rootwardChain_finish_original chain source span labels terminal k).trans
      (Function.iterate_succ_apply' P.parent k.val source)
  exact raw.trans (congrArg Subtype.val
    (C.contourParentBank_eq_of_contour S Q roots starts _ _ i first last))

include included span labels terminal tags in
/-- Matching literal original tags also matches the complete intrinsic bank length. -/
theorem sourceBank_original_exit_length (k : Fin (m + 1)) :
    C.boundaryBankLength (chain.point k) = C.boundaryBankLength
      (C.contourParentBank S Q roots starts (P.parent^[k.val] source)
        (P.iterate_lt_distanceToRoot_not_mem source (by rw [span]; exact k.isLt)) false) := by
  have raw := C.sourceBank_original_exit S Q roots starts included chain source span labels
    terminal tags k
  unfold boundaryBankLength
  rw [raw]

include included span labels terminal tags in
/-- Restoring the original full-cut exit bank gives exactly the current source-bank path,
including both actual endpoint copies. There is no supplied metric-side correspondence. -/
theorem sourceBank_original_exit_path (k : Fin (m + 1)) (t : unitInterval) :
    C.forgetCuts included (C.directedBoundaryPath
      (C.contourParentBank S Q roots starts (P.parent^[k.val] source)
        (P.iterate_lt_distanceToRoot_not_mem source (by rw [span]; exact k.isLt)) false) t) =
      C.directedBoundaryPath (chain.point k) t := by
  let original := C.contourParentBank S Q roots starts (P.parent^[k.val] source)
    (P.iterate_lt_distanceToRoot_not_mem source (by rw [span]; exact k.isLt)) false
  have raw := C.sourceBank_original_exit S Q roots starts included chain source span labels
    terminal tags k
  have survives : C.IsBoundaryEdge retain (C.germEdge original.val) :=
    raw ▸ (chain.point k).property
  have current : C.survivingBoundaryEnd original survives = chain.point k := Subtype.ext raw.symm
  exact (C.survivingBoundaryEnd_path included original survives t).symm.trans
    (congrArg (fun p => C.directedBoundaryPath p t) current)

end Unfoldings.TriangleComplex
