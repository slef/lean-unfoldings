module

public import Unfoldings.Complex.SupportedRootwardChain
public import Unfoldings.Topology.ParentOrbitPath

/-! Processed-source chains allow unused isolated roots outside the actual cutting forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (stage : Fin (Q.length + 1)) (base : C.Vertex Set.univ)
  (processed : base ∈ (C.contourFrontier S Q stage).processed)
  (ancestor : P.Ancestor (C.contourOriginalVertex S Q stage) base)
  (m : ℕ) (length : P.distanceToRoot base = m + 1)

/-- Choose every original outgoing parent bank beginning with the named processed base. -/
def supportedProcessedBank (k : Fin (m + 1)) : C.RootwardBank S Q stage :=
  (C.rootwardBankEquiv_of_boundary_roots S roots Q starts stage).symm
    ⟨P.parent^[k.val] base, P.iterate_lt_distanceToRoot_not_mem base (by rw [length]; omega),
      (C.contourFrontier S Q stage).iterate_mem_of_mem processed k.val,
      ancestor.trans P ⟨k.val, rfl⟩⟩

/-- The base is included as the first actual bank; no source edge is omitted. -/
theorem supportedProcessedBank_original (k : Fin (m + 1)) :
    C.contourOriginalVertex S Q
      (supportedProcessedBank S roots Q starts stage base processed ancestor m length k).val =
        P.parent^[k.val] base :=
  congrArg Subtype.val
    ((C.rootwardBankEquiv_of_boundary_roots S roots Q starts stage).apply_symm_apply _)

/-- The selected actual banks follow every original parent in its true order. -/
theorem supportedProcessedBank_parent (k : Fin m) :
    P.parent (C.contourOriginalVertex S Q
      (supportedProcessedBank S roots Q starts stage base processed ancestor m length
        k.castSucc).val) =
      C.contourOriginalVertex S Q
        (supportedProcessedBank S roots Q starts stage base processed ancestor m length
          k.succ).val := by
  rw [supportedProcessedBank_original, supportedProcessedBank_original]
  exact (Function.iterate_succ_apply' P.parent k.val base).symm

/-- Construct the complete actual current parent-bank chain from an already processed base. -/
def supportedProcessedBankChain :
    (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q stage))).Chain m where
  point k := C.survivingBoundaryEnd
    (Q.cycle.point (supportedProcessedBank S roots Q starts stage base processed ancestor m
      length k).val)
    (supportedProcessedBank S roots Q starts stage base processed ancestor m length k).property.2.1
  injective := by
    intro j k same
    have raw := congrArg (fun p : C.BoundaryEnd
      (C.processedParentRetain S (C.contourFrontier S Q stage)) => p.val) same
    have original := Q.cycle.injective (Subtype.ext raw)
    have labels := congrArg (C.contourOriginalVertex S Q) original
    rw [supportedProcessedBank_original, supportedProcessedBank_original] at labels
    let a : Fin (P.distanceToRoot base + 1) := ⟨j.val, by rw [length]; omega⟩
    let b : Fin (P.distanceToRoot base + 1) := ⟨k.val, by rw [length]; omega⟩
    have ordered : a = b := (P.strictMono_height_rootOrbit base).injective
      (show P.height (P.parent^[a.val] base) = P.height (P.parent^[b.val] base) from
        congrArg P.height labels)
    apply Fin.ext
    exact congrArg (fun t : Fin (P.distanceToRoot base + 1) => t.val) ordered
  disjoint j k same := by
    apply Q.cycle.disjoint
      (supportedProcessedBank S roots Q starts stage base processed ancestor m length j).val
      (supportedProcessedBank S roots Q starts stage base processed ancestor m length k).val
    exact Subtype.ext (congrArg (fun p : C.BoundaryEnd
      (C.processedParentRetain S (C.contourFrontier S Q stage)) => p.val) same)
  next k := F.rootward_boundary_step_of_boundary_roots S roots Q starts stage
    (supportedProcessedBank S roots Q starts stage base processed ancestor m length k.castSucc)
    (supportedProcessedBank S roots Q starts stage base processed ancestor m length k.succ)
    (supportedProcessedBank_parent S roots Q starts stage base processed ancestor m length k)

/-- Every bank in the constructed chain retains its exact original parent-orbit label. -/
theorem supportedProcessedBankChain_original (k : Fin (m + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        ((F.supportedProcessedBankChain S roots Q starts stage base processed ancestor m
          length).point k)) = P.parent^[k.val] base :=
  supportedProcessedBank_original S roots Q starts stage base processed ancestor m length k

/-- The actual far endpoint of the final bank is the named original root. -/
theorem supportedProcessedBankChain_terminal_original :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _
        (F.supportedProcessedBankChain S roots Q starts stage base processed ancestor m
          length).last)) =
      P.root base := by
  let bank := supportedProcessedBank S roots Q starts stage base processed ancestor m length
    (Fin.last m)
  have far := (C.future_current_bank_rootward_of_boundary_roots S roots Q starts stage bank.val
    bank.property.1
    bank.property.2.1 bank.property.2.2).2.2.2
  have label := supportedProcessedBank_original S roots Q starts stage base processed ancestor m
    length (Fin.last m)
  change C.contourOriginalVertex S Q bank.val = P.parent^[m] base at label
  rw [label] at far
  have reaches : P.parent (P.parent^[m] base) = P.root base := by
    rw [← Function.iterate_succ_apply' P.parent m base]
    change P.parent^[m + 1] base = P.root base
    rw [← length]
    exact P.iterate_distanceToRoot_eq_root base
  exact far.trans reaches

end Unfoldings.SpatialFolding
