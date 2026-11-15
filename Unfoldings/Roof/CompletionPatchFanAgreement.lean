module

public import Unfoldings.Cap.RestrictedCutFanAgreement
public import Unfoldings.Roof.CompletionBankRolling
public import Unfoldings.Roof.SpatialEnvelopeCoordinates

/-! Recover original cut-fan angles in actual physical completion patches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionPatchFanIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The physical fine-bank endpoint in the completed cap has its literal original projection. -/
theorem originalBankEndProjection_eq_cap {retain : Set C.Seam}
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain)) :
    Cap.horizontal ((E.cap.folding.restrictFaces E.originalPieceSet).boundaryPosition p) =
      E.originalBankEndProjection p := by
  have position := congrArg Cap.horizontal
    ((E.cap.folding.restrictFaces E.originalPieceSet).boundaryPosition_raw p)
  exact position.trans
    (E.partition.normalizedCap_projectFace E.conforming E.interior_nonempty _ _)

open Classical in
/-- A physical completion patch between the same directed banks has exactly the original
one-sided cut angle at an old corner. This applies in particular to a Jordan comparison
patch; no old-to-new fan-angle or regional weight certificate is supplied. -/
theorem patch_fan_totalAngle_at_old_corner (retain : Set C.Seam)
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain)) (f : Face) (k : Fin 3)
    (parent : E.originalParent p.val.1.1 = f)
    (old_position : E.originalBankEndProjection p = (K.projectedTriangle f).vertex k)
    (U : Set E.partition.Index)
    (q : (E.partition.pairedComplex.restrictFaces U).BoundaryEnd Set.univ)
    (position : E.originalBankEndProjection p =
      Cap.horizontal ((E.cap.folding.restrictFaces U).boundaryPosition q))
    (outgoing :
      Cap.horizontal ((E.cap.folding.restrictFaces E.originalPieceSet).germDirection p.val) =
        Cap.horizontal ((E.cap.folding.restrictFaces U).germDirection q.val))
    (incoming : Cap.horizontal ((E.cap.folding.restrictFaces E.originalPieceSet).germDirection
        (E.originalComplex.boundaryMate (E.originalRetain retain) p).val) =
      Cap.horizontal ((E.cap.folding.restrictFaces U).germDirection
        ((E.partition.pairedComplex.restrictFaces U).boundaryMate Set.univ q).val))
    (positive_p : 0 < E.cap.projectedGermOrientation
      (E.partition.pairedComplex.includeRestrictedGerm E.originalPieceSet p.val))
    (positive_q : 0 < E.cap.projectedGermOrientation
      (E.partition.pairedComplex.includeRestrictedGerm U q.val)) :
    (E.partition.pairedComplex.restrictFaces U).totalAngle Set.univ
        ((E.partition.pairedComplex.restrictFaces U).boundaryEndVertex Set.univ q) =
      C.totalAngle retain (C.vertexOfCorner retain (f, k)) := by
  have matched := E.cap.restricted_totalAngle_eq_of_projected_banks E.originalPieceSet U p q
    ((E.originalBankEndProjection_eq_cap p).trans position)
    outgoing incoming positive_p positive_q
  exact matched.symm.trans
    (E.original_bankEnd_totalAngle_at_old_corner retain p f k parent old_position)

end Unfoldings.ConvexRoof.CompletionMesh
