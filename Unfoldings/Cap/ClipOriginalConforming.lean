module

public import Unfoldings.Cap.ClipOriginalSeamMap
public import Unfoldings.Cap.ClipOriginalRespects

/-! The actual original-face subdivision preserves exactly all retained original seam classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalConformingIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
def originalTotalMap (lower : Z < 0) (retain : Set C.Seam) (a : C.Total) :
    L.originalComplex.Realization (L.originalRetain retain) :=
  L.originalFaceMap lower retain a.1 ⟨K.projectFace a.1 a.2.val, by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨a.2.val, a.2.property, rfl⟩⟩

open Classical in
theorem originalTotalMap_parentPoint (lower : Z < 0) (retain : Set C.Seam)
    (a : L.originalComplex.Total) :
    L.originalTotalMap lower retain ((L.originalSubdivision lower).parentPoint a) =
      MetricGluing.point L.originalComplex.Cell
        (L.originalComplex.glue (L.originalRetain retain)) a := by
  obtain ⟨i, y⟩ := a
  let p := K.projectFace (L.partition.face i.val) y.val
  have fine_member := L.partition.projected_member i.val y.property
  have old_member := L.originalParent_contains i fine_member
  have projected : K.projectFace (L.originalParent i)
      ((L.originalSubdivision lower).parentCell i y).val = p :=
    L.partition.originalPlace_projection i.val (L.originalParent i)
      (L.originalParent_contains i) y.val
  calc
    _ = L.originalFaceMap lower retain (L.originalParent i) ⟨p, old_member⟩ :=
      congrArg (L.originalFaceMap lower retain (L.originalParent i)) (Subtype.ext projected)
    _ = L.originalPointCopy retain i p fine_member :=
      L.originalFaceMap_eq lower retain (L.originalParent i) ⟨p, old_member⟩ i rfl fine_member
    _ = L.originalComplex.faceMap (L.originalRetain retain) i y := by
      apply congrArg (L.originalComplex.faceMap (L.originalRetain retain) i)
      exact Subtype.ext ((K.projectFaceEquiv (L.partition.face i.val)).symm_apply_apply y.val)

open Classical in
theorem originalTotalMap_glue (lower : Z < 0) (retain : Set C.Seam) (a b : C.Total)
    (joined : C.glue retain a b) :
    L.originalTotalMap lower retain a = L.originalTotalMap lower retain b := by
  obtain ⟨s, kept, x, rfl, rfl⟩ := joined
  let p : (K.projectedTriangle (C.left s).face).Edge (C.left s).edge :=
    ⟨K.projectFace (C.left s).face x.val, by
      rw [projectedTriangle, Triangle.affineImage_edge]
      exact ⟨x.val, x.property, rfl⟩⟩
  apply (L.originalFaceMap_eq_across_seam lower retain s kept p).trans
  apply congrArg (L.originalFaceMap lower retain (C.right s).face)
  exact Subtype.ext (K.projectedTriangle_joined s x)

open Classical in
theorem originalSubdivision_conforming (lower : Z < 0) (retain : Set C.Seam) :
    (L.originalSubdivision lower).Conforming retain (L.originalRetain retain) := by
  refine ⟨L.originalSubdivision_respects lower retain, ?_⟩
  intro a b related
  have compatible (x y : C.Total) (related : Relation.EqvGen (C.glue retain) x y) :
      L.originalTotalMap lower retain x = L.originalTotalMap lower retain y := by
    induction related with
    | rel x y joined => exact L.originalTotalMap_glue lower retain x y joined
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ first last => exact first.trans last
  have equal := compatible _ _ related
  rw [L.originalTotalMap_parentPoint, L.originalTotalMap_parentPoint] at equal
  exact (L.originalComplex.point_eq_iff (L.originalRetain retain) a b).mp equal

open Classical in
def originalMetricEquiv (lower : Z < 0) (retain : Set C.Seam) :
    L.originalComplex.Realization (L.originalRetain retain) ≃ᵢ C.Realization retain :=
  (L.originalSubdivision_conforming lower retain).metricEquiv

end Unfoldings.ConvexCap.LineAlignedClip
