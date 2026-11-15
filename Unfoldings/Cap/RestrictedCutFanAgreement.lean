module

public import Unfoldings.Cap.ProjectedFanAgreement
public import Unfoldings.Complex.RestrictedCutFanAgreement

/-! Physical banks compare cut fans in independent face restrictions of a cap mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Cutting seams inside a whole-face restriction preserves the opposite terminal signs. -/
theorem projected_restricted_cut_boundaryMate_negative (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (p : (C.restrictFaces U).BoundaryEnd retain)
    (positive : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U p.val)) :
    K.projectedGermOrientation (C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate retain p).val) < 0 := by
  let R := C.restrictFaces U
  obtain ⟨n, c, first, last, _covers⟩ := R.exists_boundary_link retain p
  let d := C.includeRestrictedLinkChain U (R.restoreLinkChain (Set.subset_univ retain) c)
  have start : 0 < K.projectedGermOrientation d.first.val := by
    change 0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val)
    rw [first]
    exact positive
  have finish := (K.projected_chain_orientation_sign d (Fin.last n)).mpr start
  change 0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.last.val) at finish
  have terminal : C.turnGerm (C.includeRestrictedGerm U c.last.val) =
      C.includeRestrictedGerm U (R.boundaryMate retain p).val :=
    congrArg (C.includeRestrictedGerm U) last
  rw [← terminal, K.projectedGermOrientation_turn]
  exact neg_neg_of_pos finish

open Classical in
/-- Physical terminal bank positions and directions identify every original corner
weight, even when the two patches have independently cut seams. -/
theorem sum_restricted_fan_weights_eq_of_projected_banks (U V : Set Face)
    {leftRetain : Set (C.restrictFaces U).Seam}
    {rightRetain : Set (C.restrictFaces V).Seam}
    (p : (C.restrictFaces U).BoundaryEnd leftRetain)
    (q : (C.restrictFaces V).BoundaryEnd rightRetain)
    (position : Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) =
      Cap.horizontal ((K.folding.restrictFaces V).boundaryPosition q))
    (outgoing : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) =
      Cap.horizontal ((K.folding.restrictFaces V).germDirection q.val))
    (incoming : Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate leftRetain p).val) =
      Cap.horizontal ((K.folding.restrictFaces V).germDirection
        ((C.restrictFaces V).boundaryMate rightRetain q).val))
    (positive_p : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U p.val))
    (positive_q : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V q.val))
    (weight : C.Corner → ℝ) :
    (∑ a : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner leftRetain a =
        (C.restrictFaces U).boundaryEndVertex leftRetain p then weight (a.1.val, a.2) else 0) =
    ∑ b : (C.restrictFaces V).Corner,
      if (C.restrictFaces V).vertexOfCorner rightRetain b =
        (C.restrictFaces V).boundaryEndVertex rightRetain q then weight (b.1.val, b.2) else 0 := by
  have apex : (K.projectedTriangle p.val.1.1.val).vertex p.val.1.2 =
      (K.projectedTriangle q.val.1.1.val).vertex q.val.1.2 := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! position
  have first := K.projected_raw_germ_unique (C.includeRestrictedGerm U p.val)
    (C.includeRestrictedGerm V q.val) apex (mul_pos positive_p positive_q) outgoing
  have mate_position : Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
        ((C.restrictFaces U).boundaryMate leftRetain p)) =
      Cap.horizontal ((K.folding.restrictFaces V).boundaryPosition
        ((C.restrictFaces V).boundaryMate rightRetain q)) := by
    rw [(K.folding.restrictFaces U).boundaryPosition_mate,
      (K.folding.restrictFaces V).boundaryPosition_mate]
    exact position
  have mate_apex :
      (K.projectedTriangle ((C.restrictFaces U).boundaryMate leftRetain p).val.1.1.val).vertex
          ((C.restrictFaces U).boundaryMate leftRetain p).val.1.2 =
        (K.projectedTriangle ((C.restrictFaces V).boundaryMate rightRetain q).val.1.1.val).vertex
          ((C.restrictFaces V).boundaryMate rightRetain q).val.1.2 := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! mate_position
  have last := K.projected_raw_germ_unique
    (C.includeRestrictedGerm U ((C.restrictFaces U).boundaryMate leftRetain p).val)
    (C.includeRestrictedGerm V ((C.restrictFaces V).boundaryMate rightRetain q).val)
    mate_apex (mul_pos_of_neg_of_neg
      (K.projected_restricted_cut_boundaryMate_negative U p positive_p)
      (K.projected_restricted_cut_boundaryMate_negative V q positive_q)) incoming
  exact C.sum_restricted_fan_weights_eq_of_terminal_germs U V p q first last weight

open Classical in
/-- Actual physical bank data determine the unreduced one-sided intrinsic fan angle. -/
theorem restricted_totalAngle_eq_of_projected_banks (U V : Set Face)
    {leftRetain : Set (C.restrictFaces U).Seam}
    {rightRetain : Set (C.restrictFaces V).Seam}
    (p : (C.restrictFaces U).BoundaryEnd leftRetain)
    (q : (C.restrictFaces V).BoundaryEnd rightRetain)
    (position : Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) =
      Cap.horizontal ((K.folding.restrictFaces V).boundaryPosition q))
    (outgoing : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) =
      Cap.horizontal ((K.folding.restrictFaces V).germDirection q.val))
    (incoming : Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate leftRetain p).val) =
      Cap.horizontal ((K.folding.restrictFaces V).germDirection
        ((C.restrictFaces V).boundaryMate rightRetain q).val))
    (positive_p : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U p.val))
    (positive_q : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V q.val)) :
    (C.restrictFaces U).totalAngle leftRetain
        ((C.restrictFaces U).boundaryEndVertex leftRetain p) =
      (C.restrictFaces V).totalAngle rightRetain
        ((C.restrictFaces V).boundaryEndVertex rightRetain q) :=
  K.sum_restricted_fan_weights_eq_of_projected_banks U V p q
    position outgoing incoming positive_p positive_q
    (fun a => (C.triangle a.1).cornerAngle a.2)

end Unfoldings.ConvexCap
