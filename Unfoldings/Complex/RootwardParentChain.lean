module

public import Unfoldings.Complex.RootwardBoundaryStep

/-! Construct the actual current rootward bank chain from original parent iterates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1)) (single : (C.contourFrontier S Q i).contactTime
    (C.contourOriginalVertex S Q i) = 1)
  (m : ℕ) (length : P.distanceToRoot (C.contourOriginalVertex S Q i) = m + 2)

/-- The actual bank with the original `(k+1)`st parent as its child endpoint. -/
def rootwardParentBank (k : Fin (m + 1)) : C.RootwardBank S Q i :=
  (C.rootwardBankEquiv S roots Q starts i).symm
    ⟨P.parent^[k.val + 1] (C.contourOriginalVertex S Q i),
      P.iterate_lt_distanceToRoot_not_mem _ (by rw [length]; omega),
      ((C.contourFrontier S Q i).contactTime_le_iff _ (k.val + 1)).mp (by rw [single]; omega),
      k.val + 1, rfl⟩

/-- The bank's original starting point is exactly the named parent iterate. -/
theorem rootwardParentBank_original (k : Fin (m + 1)) :
    C.contourOriginalVertex S Q
      (rootwardParentBank S roots Q starts i single m length k).val =
        P.parent^[k.val + 1] (C.contourOriginalVertex S Q i) :=
  congrArg Subtype.val ((C.rootwardBankEquiv S roots Q starts i).apply_symm_apply _)

/-- The bank family follows actual original parent edges, with no chosen path certificate. -/
theorem rootwardParentBank_parent (k : Fin m) :
    P.parent (C.contourOriginalVertex S Q
      (rootwardParentBank S roots Q starts i single m length k.castSucc).val) =
    C.contourOriginalVertex S Q
      (rootwardParentBank S roots Q starts i single m length k.succ).val := by
  rw [rootwardParentBank_original, rootwardParentBank_original]
  exact (Function.iterate_succ_apply' P.parent (k.val + 1) _).symm

/-- A nonempty rootward stem is the actual directed chain in the intermediate cut boundary.
Every original bank, orientation and meeting point is constructed from the original contour. -/
def rootwardParentBankChain :
    (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q i))).Chain m where
  point k := C.survivingBoundaryEnd
    (Q.cycle.point (rootwardParentBank S roots Q starts i single m length k).val)
    (rootwardParentBank S roots Q starts i single m length k).property.2.1
  injective := by
    intro j k same
    have raw := congrArg (fun p : C.BoundaryEnd
      (C.processedParentRetain S (C.contourFrontier S Q i)) => p.val) same
    have original := Q.cycle.injective (Subtype.ext raw)
    have labels := congrArg (C.contourOriginalVertex S Q) original
    rw [rootwardParentBank_original, rootwardParentBank_original] at labels
    let a : Fin (P.distanceToRoot (C.contourOriginalVertex S Q i) + 1) :=
      ⟨j.val + 1, by rw [length]; omega⟩
    let b : Fin (P.distanceToRoot (C.contourOriginalVertex S Q i) + 1) :=
      ⟨k.val + 1, by rw [length]; omega⟩
    have ordered : a = b :=
      (P.strictMono_height_rootOrbit (C.contourOriginalVertex S Q i)).injective
        (congrArg P.height labels)
    have values := congrArg (fun t : Fin (P.distanceToRoot
      (C.contourOriginalVertex S Q i) + 1) => t.val) ordered
    apply Fin.ext
    dsimp only [a, b] at values
    omega
  disjoint j k same := by
    apply Q.cycle.disjoint
      (rootwardParentBank S roots Q starts i single m length j).val
      (rootwardParentBank S roots Q starts i single m length k).val
    exact Subtype.ext (congrArg (fun p : C.BoundaryEnd
      (C.processedParentRetain S (C.contourFrontier S Q i)) => p.val) same)
  next k := F.rootward_boundary_step S roots Q starts i
    (rootwardParentBank S roots Q starts i single m length k.castSucc)
    (rootwardParentBank S roots Q starts i single m length k.succ)
    (rootwardParentBank_parent S roots Q starts i single m length k)

end Unfoldings.SpatialFolding
