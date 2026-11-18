module

public import Unfoldings.Complex.RootwardBoundaryStep
public import Unfoldings.Topology.ParentOrbitPath

/-! Actual current rootward banks may start at any processed ancestor, including its first edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (stage : Fin (Q.length + 1)) (base : C.Vertex Set.univ)
  (processed : base ∈ (C.contourFrontier S Q stage).processed)
  (ancestor : P.Ancestor (C.contourOriginalVertex S Q stage) base)
  (m : ℕ) (length : P.distanceToRoot base = m + 1)

/-- Choose every original outgoing parent bank beginning with the named processed base. -/
def processedRootwardBank (k : Fin (m + 1)) : C.RootwardBank S Q stage :=
  (C.rootwardBankEquiv S roots Q starts stage).symm
    ⟨P.parent^[k.val] base, P.iterate_lt_distanceToRoot_not_mem base (by rw [length]; omega),
      (C.contourFrontier S Q stage).iterate_mem_of_mem processed k.val,
      ancestor.trans P ⟨k.val, rfl⟩⟩

/-- The base is included as the first actual bank; no source edge is omitted. -/
theorem processedRootwardBank_original (k : Fin (m + 1)) :
    C.contourOriginalVertex S Q
      (processedRootwardBank S roots Q starts stage base processed ancestor m length k).val =
        P.parent^[k.val] base :=
  congrArg Subtype.val ((C.rootwardBankEquiv S roots Q starts stage).apply_symm_apply _)

/-- The selected actual banks follow every original parent in its true order. -/
theorem processedRootwardBank_parent (k : Fin m) :
    P.parent (C.contourOriginalVertex S Q
      (processedRootwardBank S roots Q starts stage base processed ancestor m length
        k.castSucc).val) =
      C.contourOriginalVertex S Q
        (processedRootwardBank S roots Q starts stage base processed ancestor m length
          k.succ).val := by
  rw [processedRootwardBank_original, processedRootwardBank_original]
  exact (Function.iterate_succ_apply' P.parent k.val base).symm

/-- Construct the complete actual current parent-bank chain from an already processed base. -/
def processedRootwardBankChain :
    (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q stage))).Chain m where
  point k := C.survivingBoundaryEnd
    (Q.cycle.point (processedRootwardBank S roots Q starts stage base processed ancestor m
      length k).val)
    (processedRootwardBank S roots Q starts stage base processed ancestor m length k).property.2.1
  injective := by
    intro j k same
    have raw := congrArg (fun p : C.BoundaryEnd
      (C.processedParentRetain S (C.contourFrontier S Q stage)) => p.val) same
    have original := Q.cycle.injective (Subtype.ext raw)
    have labels := congrArg (C.contourOriginalVertex S Q) original
    rw [processedRootwardBank_original, processedRootwardBank_original] at labels
    let a : Fin (P.distanceToRoot base + 1) := ⟨j.val, by rw [length]; omega⟩
    let b : Fin (P.distanceToRoot base + 1) := ⟨k.val, by rw [length]; omega⟩
    have ordered : a = b := (P.strictMono_height_rootOrbit base).injective
      (show P.height (P.parent^[a.val] base) = P.height (P.parent^[b.val] base) from
        congrArg P.height labels)
    apply Fin.ext
    exact congrArg (fun t : Fin (P.distanceToRoot base + 1) => t.val) ordered
  disjoint j k same := by
    apply Q.cycle.disjoint
      (processedRootwardBank S roots Q starts stage base processed ancestor m length j).val
      (processedRootwardBank S roots Q starts stage base processed ancestor m length k).val
    exact Subtype.ext (congrArg (fun p : C.BoundaryEnd
      (C.processedParentRetain S (C.contourFrontier S Q stage)) => p.val) same)
  next k := F.rootward_boundary_step S roots Q starts stage
    (processedRootwardBank S roots Q starts stage base processed ancestor m length k.castSucc)
    (processedRootwardBank S roots Q starts stage base processed ancestor m length k.succ)
    (processedRootwardBank_parent S roots Q starts stage base processed ancestor m length k)

/-- Every bank in the constructed chain retains its exact original parent-orbit label. -/
theorem processedRootwardBankChain_original (k : Fin (m + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        ((F.processedRootwardBankChain S roots Q starts stage base processed ancestor m
          length).point k)) = P.parent^[k.val] base :=
  processedRootwardBank_original S roots Q starts stage base processed ancestor m length k

/-- The actual far endpoint of the final bank is the named original root. -/
theorem processedRootwardBankChain_terminal_original :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _
        (F.processedRootwardBankChain S roots Q starts stage base processed ancestor m
          length).last)) =
      P.root base := by
  let bank := processedRootwardBank S roots Q starts stage base processed ancestor m length
    (Fin.last m)
  have far := (C.future_current_bank_rootward S roots Q starts stage bank.val bank.property.1
    bank.property.2.1 bank.property.2.2).2.2.2
  have label := processedRootwardBank_original S roots Q starts stage base processed ancestor m
    length (Fin.last m)
  change C.contourOriginalVertex S Q bank.val = P.parent^[m] base at label
  rw [label] at far
  have reaches : P.parent (P.parent^[m] base) = P.root base := by
    rw [← Function.iterate_succ_apply' P.parent m base]
    change P.parent^[m + 1] base = P.root base
    rw [← length]
    exact P.iterate_distanceToRoot_eq_root base
  exact far.trans reaches

/-- On a contour descent, the newly processed source supplies the complete actual rootward chain.
Its own outgoing edge is included; no previously proposed chain or successor is supplied. -/
def sourceAtDescentBankChain (j : Fin Q.length)
    (child : P.parent (C.contourOriginalVertex S Q j.succ) =
      C.contourOriginalVertex S Q j.castSucc)
    (d : ℕ) (span : P.distanceToRoot (C.contourOriginalVertex S Q j.castSucc) = d + 1) :
    (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q j.succ))).Chain d :=
  F.processedRootwardBankChain S roots Q starts j.succ (C.contourOriginalVertex S Q j.castSucc)
    (C.previous_contour_vertex_processed S Q j) ⟨1, child⟩ d span

/-- The descent construction begins at the named original source and follows every parent. -/
theorem sourceAtDescentBankChain_original (j : Fin Q.length)
    (child : P.parent (C.contourOriginalVertex S Q j.succ) =
      C.contourOriginalVertex S Q j.castSucc)
    (d : ℕ) (span : P.distanceToRoot (C.contourOriginalVertex S Q j.castSucc) = d + 1)
    (k : Fin (d + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        ((F.sourceAtDescentBankChain S roots Q starts j child d span).point k)) =
      P.parent^[k.val] (C.contourOriginalVertex S Q j.castSucc) :=
  F.processedRootwardBankChain_original S roots Q starts j.succ
    (C.contourOriginalVertex S Q j.castSucc) (C.previous_contour_vertex_processed S Q j)
    ⟨1, child⟩ d span k

end Unfoldings.SpatialFolding
