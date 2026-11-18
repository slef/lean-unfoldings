module

public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Complex.FaceRestrictionVertices
public import Unfoldings.Complex.PhysicalCutClasses

/-! Restricting faces preserves every retained copy at a point whose incident faces are kept. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

open Classical in
/-- All retained attachment chains at a fully kept physical star remain in the restriction. -/
theorem restrict_eqvGen_of_incident_faces (U : Set Face) (retain : Set C.Seam)
    (position : Space) (incident : ∀ a : C.Total, F.place a.1 a.2.val = position → a.1 ∈ U)
    {a b : (C.restrictFaces U).Total}
    (at_point : F.place a.1.val a.2.val = position)
    (related : Relation.EqvGen (C.glue retain) (C.includedTotal U a) (C.includedTotal U b)) :
    Relation.EqvGen ((C.restrictFaces U).glue (C.restrictRetain U retain)) a b := by
  have lift {a b : C.Total} (h : Relation.EqvGen (C.glue retain) a b) :
      ∀ (ha : a.1 ∈ U) (hb : b.1 ∈ U), F.place a.1 a.2.val = position →
        Relation.EqvGen ((C.restrictFaces U).glue (C.restrictRetain U retain))
          ⟨⟨a.1, ha⟩, a.2⟩ ⟨⟨b.1, hb⟩, b.2⟩ := by
    induction h with
    | rel a b h =>
      intro ha hb _
      exact Relation.EqvGen.rel _ _ (C.restrict_glue_of_included U retain
        (a := ⟨⟨a.1, ha⟩, a.2⟩) (b := ⟨⟨b.1, hb⟩, b.2⟩) h)
    | refl a =>
      intro ha hb _
      exact Relation.EqvGen.refl _
    | symm a b h ih =>
      intro ha hb at_point
      exact (ih hb ha ((F.place_eq_of_eqvGen h).trans at_point)).symm
    | trans a b c first last ih_first ih_last =>
      intro ha hc at_point
      have at_middle := (F.place_eq_of_eqvGen first).symm.trans at_point
      have hb := incident b at_middle
      exact Relation.EqvGen.trans _ _ _ (ih_first ha hb at_point) (ih_last hb hc at_middle)
  exact lift related a.1.property b.1.property at_point

open Classical in
/-- A whole retained vertex star cannot split when every incident physical face is retained. -/
theorem includeRestrictedVertex_injective_at (U : Set Face) (retain : Set C.Seam)
    (position : Space) (incident : ∀ a : C.Total, F.place a.1 a.2.val = position → a.1 ∈ U)
    (w z : (C.restrictFaces U).Vertex (C.restrictRetain U retain))
    (at_point : (F.restrictFaces U).toSpace (C.restrictRetain U retain)
      ((C.restrictFaces U).vertexPoint (C.restrictRetain U retain) w) = position)
    (same : C.includeRestrictedVertex U retain w = C.includeRestrictedVertex U retain z) :
    w = z := by
  let R := C.restrictFaces U
  obtain ⟨c, rfl⟩ := R.vertexOfCorner_surjective (C.restrictRetain U retain) w
  obtain ⟨d, rfl⟩ := R.vertexOfCorner_surjective (C.restrictRetain U retain) z
  apply (R.vertexOfCorner_eq_iff _ _ _).mpr
  apply F.restrict_eqvGen_of_incident_faces U retain position incident at_point
  exact (C.vertexOfCorner_eq_iff retain _ _).mp same

open Classical in
/-- Including a restricted retained vertex preserves its literal spatial point. -/
theorem toSpace_includeRestrictedVertex (U : Set Face) (retain : Set C.Seam)
    (w : (C.restrictFaces U).Vertex (C.restrictRetain U retain)) :
    F.toSpace retain (C.vertexPoint retain (C.includeRestrictedVertex U retain w)) =
      (F.restrictFaces U).toSpace (C.restrictRetain U retain)
        ((C.restrictFaces U).vertexPoint (C.restrictRetain U retain) w) := by
  obtain ⟨c, rfl⟩ := (C.restrictFaces U).vertexOfCorner_surjective (C.restrictRetain U retain) w
  rfl

end Unfoldings.SpatialFolding
