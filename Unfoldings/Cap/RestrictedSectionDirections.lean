module

public import Unfoldings.Cap.BoundarySectionConstruction
public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Geometry.OppositeRayAngles

/-! Actual straight restricted-bank directions and their active original face directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Inverse face projection recovers the genuine spatial germ, including its length. -/
theorem spatialDirection_horizontal_germ (p : C.Germ) :
    K.spatialDirection p.1.1 (Cap.horizontal (K.folding.germDirection p)) =
      K.folding.germDirection p := by
  unfold SpatialFolding.germDirection SpatialFolding.germFarPoint
  rw [map_sub]
  exact K.spatialDirection_chord p.1.1 _ _

open Classical in
/-- Each actual restricted bank's original face is active at its physical initial position. -/
theorem restricted_bank_face_active (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    K.supportHeight p.val.1.1.val
        (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p)) =
      K.roofHeight (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p)) := by
  rw [(K.folding.restrictFaces U).boundaryPosition_raw]
  exact (K.supportHeight_face p.val.1.1.val ((C.triangle p.val.1.1.val).vertex p.val.1.2)).trans
    (K.roofHeight_face p.val.1.1.val
      ⟨(C.triangle p.val.1.1.val).vertex p.val.1.2,
        (C.triangle p.val.1.1.val).vertex_mem p.val.1.2⟩).symm

open Classical in
/-- Literal horizontal scaling determines the whole spatial bank vector on its original face. -/
theorem restricted_germDirection_eq_smul (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (direction : Plane) (a : ℝ)
    (projected : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) =
      a • direction) :
    (K.folding.restrictFaces U).germDirection p.val =
      a • K.spatialDirection p.val.1.1.val direction := by
  have recovered := K.spatialDirection_horizontal_germ (C.includeRestrictedGerm U p.val)
  change K.spatialDirection p.val.1.1.val
    (Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val)) =
      (K.folding.restrictFaces U).germDirection p.val at recovered
  rw [projected] at recovered
  simpa only [spatialDirection, pullbackDirection, map_smul] using recovered.symm

open Classical in
/-- The actual fan error is bounded by the two active original support inclinations. -/
theorem restricted_fan_error_le_active_angle (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (direction : Plane) (nonzero : direction ≠ 0)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (a b : ℝ) (opposite : a * b < 0)
    (outgoing : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • direction)
    (incoming : Cap.horizontal ((K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate Set.univ p).val) = b • direction) :
    |(Real.pi - (C.restrictFaces U).totalAngle Set.univ
        ((C.restrictFaces U).boundaryEndVertex Set.univ p)) -
      (Real.pi - (C.restrictFaces U).regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
        ((C.restrictFaces U).boundaryEndVertex Set.univ p))| ≤
      InnerProductGeometry.angle (K.spatialDirection p.val.1.1.val direction)
        (K.spatialDirection
          ((C.restrictFaces U).boundaryMate Set.univ p).val.1.1.val direction) := by
  have straight : InnerProductGeometry.angle
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val))
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val)) = Real.pi := by
    rw [outgoing, incoming]
    exact angle_smul_self_of_mul_neg nonzero opposite
  have bound := K.abs_restricted_straight_turn_error_le_spatial_bend U p internal straight
  rw [K.restricted_germDirection_eq_smul U p direction a outgoing,
    K.restricted_germDirection_eq_smul U ((C.restrictFaces U).boundaryMate Set.univ p)
      direction b incoming, angle_neg_smul_smul_of_mul_neg _ _ opposite] at bound
  exact bound

end Unfoldings.ConvexCap
