module

public import Unfoldings.Cap.ProjectedFanOrientation
public import Unfoldings.Complex.RestrictedFanAgreement
public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Polyhedron.BoundaryDirections

/-! Physical directed banks identify the complete original one-sided fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {retain : Set C.Seam} (U : Set Face)

open Classical in
/-- Physical positions and directed bank vectors identify both raw terminal germs.
The incoming orientation is derived from the actual fans, rather than assumed. -/
theorem restricted_terminal_germs_of_projected_banks
    (p : C.BoundaryEnd retain) (q : (C.restrictFaces U).BoundaryEnd Set.univ)
    (position : Cap.horizontal (K.folding.boundaryPosition p) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition q))
    (outgoing : Cap.horizontal (K.folding.germDirection p.val) =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection q.val))
    (incoming : Cap.horizontal (K.folding.germDirection (C.boundaryMate retain p).val) =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ q).val))
    (positive_p : 0 < K.projectedGermOrientation p.val)
    (positive_q : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U q.val)) :
    p.val = C.includeRestrictedGerm U q.val ∧
      (C.boundaryMate retain p).val = C.includeRestrictedGerm U
        ((C.restrictFaces U).boundaryMate Set.univ q).val := by
  have apex : (K.projectedTriangle p.val.1.1).vertex p.val.1.2 =
      (K.projectedTriangle q.val.1.1.val).vertex q.val.1.2 := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! position
  have first := K.projected_raw_germ_unique p.val (C.includeRestrictedGerm U q.val)
    apex (mul_pos positive_p positive_q) outgoing
  have mate_position : Cap.horizontal (K.folding.boundaryPosition (C.boundaryMate retain p)) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
        ((C.restrictFaces U).boundaryMate Set.univ q)) := by
    rw [K.folding.boundaryPosition_mate, (K.folding.restrictFaces U).boundaryPosition_mate]
    exact position
  have mate_apex :
      (K.projectedTriangle (C.boundaryMate retain p).val.1.1).vertex
          (C.boundaryMate retain p).val.1.2 =
        (K.projectedTriangle ((C.restrictFaces U).boundaryMate Set.univ q).val.1.1.val).vertex
          ((C.restrictFaces U).boundaryMate Set.univ q).val.1.2 := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! mate_position
  have last := K.projected_raw_germ_unique (C.boundaryMate retain p).val
    (C.includeRestrictedGerm U ((C.restrictFaces U).boundaryMate Set.univ q).val)
    mate_apex (mul_pos_of_neg_of_neg (K.projected_boundaryMate_negative p positive_p)
      (K.projected_restricted_boundaryMate_negative U q positive_q)) incoming
  exact ⟨first, last⟩

open Classical in
/-- Every original corner weight agrees with the physical restricted patch fan. In
particular, angle agreement is a conclusion, rather than a comparison certificate. -/
theorem sum_fan_weights_eq_restricted_of_projected_banks
    (p : C.BoundaryEnd retain) (q : (C.restrictFaces U).BoundaryEnd Set.univ)
    (position : Cap.horizontal (K.folding.boundaryPosition p) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition q))
    (outgoing : Cap.horizontal (K.folding.germDirection p.val) =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection q.val))
    (incoming : Cap.horizontal (K.folding.germDirection (C.boundaryMate retain p).val) =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ q).val))
    (positive_p : 0 < K.projectedGermOrientation p.val)
    (positive_q : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U q.val))
    (weight : C.Corner → ℝ) :
    (∑ a : C.Corner, if C.vertexOfCorner retain a = C.boundaryEndVertex retain p
      then weight a else 0) =
    ∑ b : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner Set.univ b =
        (C.restrictFaces U).boundaryEndVertex Set.univ q then weight (b.1.val, b.2) else 0 := by
  obtain ⟨first, last⟩ := K.restricted_terminal_germs_of_projected_banks U p q
    position outgoing incoming positive_p positive_q
  exact C.sum_fan_weights_eq_restricted_of_terminal_germs U p q first last weight

open Classical in
/-- The actual one-sided intrinsic angle is recovered from physical directed bank data. -/
theorem totalAngle_eq_restricted_of_projected_banks
    (p : C.BoundaryEnd retain) (q : (C.restrictFaces U).BoundaryEnd Set.univ)
    (position : Cap.horizontal (K.folding.boundaryPosition p) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition q))
    (outgoing : Cap.horizontal (K.folding.germDirection p.val) =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection q.val))
    (incoming : Cap.horizontal (K.folding.germDirection (C.boundaryMate retain p).val) =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ q).val))
    (positive_p : 0 < K.projectedGermOrientation p.val)
    (positive_q : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U q.val)) :
    C.totalAngle retain (C.boundaryEndVertex retain p) =
      (C.restrictFaces U).totalAngle Set.univ
        ((C.restrictFaces U).boundaryEndVertex Set.univ q) :=
  K.sum_fan_weights_eq_restricted_of_projected_banks U p q
    position outgoing incoming positive_p positive_q _

end Unfoldings.ConvexCap
