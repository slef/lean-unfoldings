module

public import Unfoldings.Geometry.SpatialEnvelopeCommonRefinement
public import Unfoldings.Geometry.SpatialEnvelopeCutRefinement
public import Unfoldings.Metric.CommonModelTransport

/-! Actual complete roof cut metrics are independent of the boundary-aligned physical partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition.Refinement

universe u

variable {I A B : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {P : WholePartition family A} {Q : WholePartition family B} [Finite A] [Finite B]
  (R : P.Refinement Q) (cuts : Set Plane) (cut_closed : IsClosed cuts)
  (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts)

/-- A fine metric lift becomes the exact original physical parent-cell lift. -/
theorem cutRefinementEquiv_liftCell (b : B) (p : Q.footprint b) :
    R.cutRefinementEquiv cuts cut_closed outside (Q.liftCell cuts b p) =
      P.liftCell cuts (R.parent b) ⟨p.val, R.included b p.property⟩ := by
  apply (P.cutIsometryEquiv cuts).injective
  exact (R.cutRefinementEquiv_of cuts cut_closed outside b
    ⟨(family (Q.support b)).project.symm p.val, p.val, p.property, rfl⟩).trans
      (congrArg (MetricGluing.of (fun a => P.spatialCell a)
        (P.cutPhysicalSeams cuts).relation (R.parent b))
        (Subtype.ext ((point_eq_place family (Q.support b) (Q.active b p.val p.property)).symm.trans
          (point_eq_place family (P.support (R.parent b))
            (P.active (R.parent b) p.val (R.included b p.property))))))

end Unfoldings.SpatialEnvelope.WholePartition.Refinement

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A B : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) (Q : WholePartition family B) [Finite A] [Finite B]
  (cuts : Set Plane) (cut_closed : IsClosed cuts)
  (outside_P : ∀ a, Disjoint (interior (P.footprint a)) cuts)
  (outside_Q : ∀ b, Disjoint (interior (Q.footprint b)) cuts)

/-- Any two boundary-aligned actual whole-roof partitions give the same complete cut metric.
The common physical subdivision, every metric comparison and its inverse are constructed. -/
def cutPartitionEquiv : P.Cut cuts ≃ᵢ Q.Cut cuts :=
  ((P.commonRefinementLeft Q).cutRefinementEquiv cuts cut_closed outside_P).symm.trans
    ((P.commonRefinementRight Q).cutRefinementEquiv cuts cut_closed outside_Q)

theorem restoreCut_cutPartitionEquiv (x : P.Cut cuts) :
    Q.restoreCut cuts (P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q x) =
      P.restoreCut cuts x := by
  exact map_common_model_isometry
    ((P.commonRefinementLeft Q).cutRefinementEquiv cuts cut_closed outside_P)
    ((P.commonRefinementRight Q).cutRefinementEquiv cuts cut_closed outside_Q)
    (P.restoreCut cuts) (Q.restoreCut cuts) ((P.commonPartition Q).restoreCut cuts)
    ((P.commonRefinementLeft Q).restoreCut_cutRefinementEquiv cuts cut_closed outside_P)
    ((P.commonRefinementRight Q).restoreCut_cutRefinementEquiv cuts cut_closed outside_Q) x

/-- On every full common piece, the isometry preserves the actual original cell copies. -/
theorem cutPartitionEquiv_liftCell (i : P.CommonIndex Q)
    (p : ↥(P.footprint i.val.1 ∩ Q.footprint i.val.2)) :
    P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q
      (P.liftCell cuts i.val.1 ⟨p.val, p.property.1⟩) =
        Q.liftCell cuts i.val.2 ⟨p.val, p.property.2⟩ := by
  let L := (P.commonRefinementLeft Q).cutRefinementEquiv cuts cut_closed outside_P
  let R := (P.commonRefinementRight Q).cutRefinementEquiv cuts cut_closed outside_Q
  let x := (P.commonPartition Q).liftCell cuts i p
  have left : L x = P.liftCell cuts i.val.1 ⟨p.val, p.property.1⟩ :=
    (P.commonRefinementLeft Q).cutRefinementEquiv_liftCell cuts cut_closed outside_P i p
  have right : R x = Q.liftCell cuts i.val.2 ⟨p.val, p.property.2⟩ :=
    (P.commonRefinementRight Q).cutRefinementEquiv_liftCell cuts cut_closed outside_Q i p
  exact common_model_isometry_copy L R x left right

end Unfoldings.SpatialEnvelope.WholePartition
