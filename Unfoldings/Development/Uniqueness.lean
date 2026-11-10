module

public import Unfoldings.Geometry.HingeRigidity
public import Unfoldings.Geometry.HingeConverse
public import Unfoldings.Geometry.Hinge
public import Unfoldings.Complex.Connectivity
public import Unfoldings.Complex.Classes

/-! Fixing one face determines every outward development of a dually connected complex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (E F : FacewiseDevelopment C retain)

theorem joined_side (s : C.Seam) (kept : s ∈ retain) (side : Bool)
    (x : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge) :
    E.place (C.seamSide s side).face x.val =
      E.place (C.seamSide s (!side)).face (C.across s side x).val := by
  cases side
  · exact E.joined s kept x
  · have joined := E.joined s kept ((C.identify s).symm x)
    change E.place (C.right s).face x.val = E.place (C.left s).face ((C.identify s).symm x).val
    exact (congrArg (fun y => E.place (C.right s).face y.val)
      ((C.identify s).apply_symm_apply x)).symm.trans joined.symm

theorem hinge_nonoverlap_side (s : C.Seam) (kept : s ∈ retain) (side : Bool) :
    Disjoint (interior (E.faceImage (C.seamSide s side).face))
      (interior (E.faceImage (C.seamSide s (!side)).face)) := by
  cases side
  · exact E.hinge_nonoverlap s kept
  · exact (E.hinge_nonoverlap s kept).symm

/-- Strict edge opening propagates equality of rigid motions in either direction. -/
theorem place_eq_across (s : C.Seam) (kept : s ∈ retain) (side : Bool)
    (same : E.place (C.seamSide s side).face = F.place (C.seamSide s side).face) :
    E.place (C.seamSide s (!side)).face = F.place (C.seamSide s (!side)).face := by
  let T := C.triangle (C.seamSide s side).face
  let U := C.triangle (C.seamSide s (!side)).face
  let e := (C.seamSide s side).edge
  let f := (C.seamSide s (!side)).edge
  let L := E.place (C.seamSide s side).face
  let A := E.place (C.seamSide s (!side)).face
  let B := F.place (C.seamSide s (!side)).face
  have joinedB (x : T.Edge e) : L x.val = B (C.across s side x).val := by
    change E.place _ x.val = F.place _ _
    rw [same]
    exact F.joined_side s kept side x
  have first := T.placed_opposite_of_disjoint U e f (C.across s side) L A
    (E.joined_side s kept side) (E.hinge_nonoverlap_side s kept side)
  have last := T.placed_opposite_of_disjoint U e f (C.across s side) L B joinedB (by
    change Disjoint (interior (E.faceImage _)) (interior (F.faceImage _))
    simpa only [faceImage, same] using F.hinge_nonoverlap_side s kept side)
  apply rigid_eq_of_joined_edge_and_side T U e f (C.across s side) L A B
    (E.joined_side s kept side) joinedB
  rcases mul_neg_iff.mp first with ⟨positive, negative⟩ | ⟨negative, positive⟩ <;>
    rcases mul_neg_iff.mp last with ⟨positive', negative'⟩ | ⟨negative', positive'⟩
  · exact mul_pos_of_neg_of_neg negative negative'
  · exact (lt_asymm positive negative').elim
  · exact (lt_asymm negative positive').elim
  · exact mul_pos positive positive'

theorem place_eq_iff_of_related {f g : Face} (related : Relation.EqvGen (C.FaceGlue retain) f g) :
    E.place f = F.place f ↔ E.place g = F.place g := by
  induction related with
  | rel f g joined =>
    obtain ⟨s, kept, rfl, rfl⟩ := joined
    exact ⟨E.place_eq_across F s kept false, E.place_eq_across F s kept true⟩
  | refl f => rfl
  | symm f g _ ih => exact ih.symm
  | trans f g h _ _ first last => exact first.trans last

/-- Normalization on any one face makes the development unique; global overlap is allowed. -/
theorem places_eq_of_root (connected : C.DuallyConnected retain) (root : Face)
    (normalized : E.place root = F.place root) (f : Face) : E.place f = F.place f :=
  (E.place_eq_iff_of_related F (connected root f)).mp normalized

@[ext] theorem ext (same : ∀ f, E.place f = F.place f) : E = F := by
  cases E
  cases F
  congr
  exact funext same

theorem eq_of_root (connected : C.DuallyConnected retain) (root : Face)
    (normalized : E.place root = F.place root) : E = F :=
  E.ext F (E.places_eq_of_root F connected root normalized)

end Unfoldings.FacewiseDevelopment
