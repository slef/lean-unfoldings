module

public import Unfoldings.Cap.PositiveRimContour
public import Unfoldings.Cap.CompletedBankPhysicalSides
public import Unfoldings.Cap.RootwardProjectedBanks

/-! Construct the physical incident-face side of every actual rootward original bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

/-- Every incident original face lies on the left of its actual rootward original parent
segment. The entire positive rim-started contour is constructed from the original cap. -/
theorem positive_rootward_bank_face_left
    (i : Fin ((K.positiveRimContour S roots).length + 1))
    (j : C.RootwardBank S (K.positiveRimContour S roots) i) {x : Plane}
    (member : x ∈ (K.projectedTriangle
      ((K.positiveRimContour S roots).cycle.point j.val).val.1.1).carrier) :
    0 ≤ orient
      (K.projectedVertex (C.contourOriginalVertex S (K.positiveRimContour S roots) j.val))
      (K.projectedVertex (P.parent
        (C.contourOriginalVertex S (K.positiveRimContour S roots) j.val))) x := by
  let Q := K.positiveRimContour S roots
  have data := C.future_current_bank_rootward S roots Q (K.positiveRimContour_starts S roots)
    i j.val j.property.1 j.property.2.1 j.property.2.2
  have side := K.projected_bank_side_nonneg (Q.cycle.point j.val)
    (K.positiveRimContour_positive S roots j.val) member
  change 0 ≤ orient (K.projectedVertex (C.contourOriginalVertex S Q j.val))
    (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j.val))))) x at side
  rw [data.2.2.2] at side
  exact side

/-- Along the constructed parent chain, the side statement uses the actual projected chain
vertices and actual incident original faces, including the terminal segment to the rim. -/
theorem rootwardProjectedParentChain_face_left
    (i : Fin ((K.positiveRimContour S roots).length + 1))
    (single : (C.contourFrontier S (K.positiveRimContour S roots) i).contactTime
      (C.contourOriginalVertex S (K.positiveRimContour S roots) i) = 1)
    (m : ℕ) (length : P.distanceToRoot
      (C.contourOriginalVertex S (K.positiveRimContour S roots) i) = m + 2)
    (k : Fin (m + 1)) {x : Plane}
    (member : x ∈ (K.projectedTriangle
      ((K.folding.rootwardParentBankChain S roots (K.positiveRimContour S roots)
        (K.positiveRimContour_starts S roots) i single m length).point k).val.1.1).carrier) :
    0 ≤ orient
      ((K.rootwardProjectedParentChain S (K.positiveRimContour S roots) i m).vertex k.castSucc)
      ((K.rootwardProjectedParentChain S (K.positiveRimContour S roots) i m).vertex k.succ) x := by
  have side := K.positive_rootward_bank_face_left S roots i
    (SpatialFolding.rootwardParentBank S roots (K.positiveRimContour S roots)
      (K.positiveRimContour_starts S roots) i single m length k) member
  rw [SpatialFolding.rootwardParentBank_original] at side
  simpa only [rootwardProjectedParentChain, Fin.val_castSucc, Fin.val_succ,
    Function.iterate_succ_apply'] using! side

end Unfoldings.ConvexCap
