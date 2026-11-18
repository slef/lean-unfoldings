module

public import Unfoldings.Complex.FaceRestrictionVertices
public import Unfoldings.Roof.FaceRestriction

/-! Canonical nonexpanding inclusions of retained whole-face subcomplexes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- Include every selected physical face copy with its original retained seam attachments. -/
def includeRestricted (U : Set Face) (retain : Set C.Seam) :
    (C.restrictFaces U).Realization (C.restrictRetain U retain) → C.Realization retain :=
  MetricGluing.lift (C.restrictFaces U).Cell ((C.restrictFaces U).glue (C.restrictRetain U retain))
    (fun f => C.faceMap retain f.val) (fun f => C.faceMap_lipschitz retain f.val)
    (by
      intro a b joined
      exact (C.point_eq_iff retain _ _).mpr
        (Relation.EqvGen.rel _ _ (C.included_glue_of_restricted U retain joined)))

open Classical in
@[simp] theorem includeRestricted_faceMap (U : Set Face) (retain : Set C.Seam)
    (f : {f : Face // f ∈ U}) (y : (C.restrictFaces U).Cell f) :
    C.includeRestricted U retain ((C.restrictFaces U).faceMap (C.restrictRetain U retain) f y) =
      C.faceMap retain f.val y := rfl

open Classical in
theorem includeRestricted_lipschitz (U : Set Face) (retain : Set C.Seam) :
    LipschitzWith 1 (C.includeRestricted U retain) := MetricGluing.lift_lipschitz _ _ _ _ _

open Classical in
@[simp] theorem includeRestricted_vertexPoint (U : Set Face) (retain : Set C.Seam)
    (w : (C.restrictFaces U).Vertex (C.restrictRetain U retain)) :
    C.includeRestricted U retain ((C.restrictFaces U).vertexPoint (C.restrictRetain U retain) w) =
      C.vertexPoint retain (C.includeRestrictedVertex U retain w) := by
  obtain ⟨c, rfl⟩ := (C.restrictFaces U).vertexOfCorner_surjective (C.restrictRetain U retain) w
  rfl

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

open Classical in
theorem toSpace_includeRestricted (U : Set Face) (retain : Set C.Seam)
    (x : (C.restrictFaces U).Realization (C.restrictRetain U retain)) :
    F.toSpace retain (C.includeRestricted U retain x) =
      (F.restrictFaces U).toSpace (C.restrictRetain U retain) x := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective (C.restrictFaces U).Cell
    ((C.restrictFaces U).glue (C.restrictRetain U retain)) x
  rfl

end Unfoldings.SpatialFolding
