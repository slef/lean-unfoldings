module

public import Unfoldings.Geometry.SpatialEnvelopeRefinement
public import Unfoldings.Geometry.SpatialEnvelopeFaceSideBall

/-! Actual whole-roof subdivisions preserve complete cut metrics and their original physical copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition.Refinement

universe u

variable {I A B : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {P : WholePartition family A} {Q : WholePartition family B} [Finite A] [Finite B]
  (R : P.Refinement Q) (cuts : Set Plane) (cut_closed : IsClosed cuts)
  (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts)

/-- A genuine whole-roof subdivision preserves the complete original cut metric.
Only physical containment, covers and original boundary cuts are supplied. -/
def cutRefinementEquiv : Q.Cut cuts ≃ᵢ P.Cut cuts :=
  ((Q.cutIsometryEquiv cuts).trans
    ((R.physicalCutRefinement cuts cut_closed outside).isometryEquiv P.isClosed_spatialCell)).trans
      (P.cutIsometryEquiv cuts).symm

/-- The metric equivalence is the original physical parent-cell map in spatial coordinates. -/
theorem cutIsometryEquiv_cutRefinementEquiv (x : Q.Cut cuts) :
    P.cutIsometryEquiv cuts (R.cutRefinementEquiv cuts cut_closed outside x) =
      (R.physicalCutRefinement cuts cut_closed outside).isometryEquiv P.isClosed_spatialCell
        (Q.cutIsometryEquiv cuts x) :=
  (P.cutIsometryEquiv cuts).apply_symm_apply _

/-- Changing the physical subdivision preserves the exact original roof point. -/
theorem restoreCut_cutRefinementEquiv (x : Q.Cut cuts) :
    P.restoreCut cuts (R.cutRefinementEquiv cuts cut_closed outside x) = Q.restoreCut cuts x := by
  apply PolygonalPoint.ext
  exact (P.fold_cutIsometryEquiv cuts _).symm.trans
    ((congrArg (P.cutPhysicalSeams cuts).fold
      (R.cutIsometryEquiv_cutRefinementEquiv cuts cut_closed outside x)).trans
        (((R.physicalCutRefinement cuts cut_closed outside).fold_isometryEquiv
          P.isClosed_spatialCell (Q.cutIsometryEquiv cuts x)).trans
            (Q.fold_cutIsometryEquiv cuts x)))

/-- Each specified original fine-cell copy goes to that same point in its original parent cell. -/
theorem cutRefinementEquiv_of (b : B) (x : Q.planarCell b) :
    P.cutIsometryEquiv cuts (R.cutRefinementEquiv cuts cut_closed outside
      (MetricGluing.of (fun b => Q.planarCell b) (Q.cutGlue cuts) b x)) =
      MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation (R.parent b)
        ⟨(Q.cellIsometryEquiv b x).val,
          (R.physicalCutRefinement cuts cut_closed outside).included b
            (Q.cellIsometryEquiv b x).property⟩ :=
  (R.cutIsometryEquiv_cutRefinementEquiv cuts cut_closed outside _).trans
    ((congrArg ((R.physicalCutRefinement cuts cut_closed outside).isometryEquiv
      P.isClosed_spatialCell) (Q.cutIsometryEquiv_of cuts b x)).trans
        ((R.physicalCutRefinement cuts cut_closed outside).isometryEquiv_of P.isClosed_spatialCell
          b (Q.cellIsometryEquiv b x)))

end Unfoldings.SpatialEnvelope.WholePartition.Refinement
