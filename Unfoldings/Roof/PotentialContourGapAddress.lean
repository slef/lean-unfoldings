module

public import Unfoldings.Roof.PotentialContourStack
public import Unfoldings.Complex.ContourGapBankSurjectivity
public import Unfoldings.Geometry.BankGapBoundaryMap

/-! Every finite and continued gap address has the matching original stack attachment. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (F : K.PotentialCutForest f cuts)
  (contour : C.BoundaryContour F.retain)

local notation "Event" => TriangleComplex.PositiveContourSource C F.selection contour
local notation "Stack" => contourAttachmentStack F contour
local notation "Param" => contourAttachmentParameter F
local notation "Length[" e "]" => TriangleComplex.positiveContourBankLength C F.selection contour e

/-- The original gap address at a finite bank mark or a mark on its true continuation. -/
def contourGapAddress (a : F.ContourAttachment) (e : Event) (member : e ∈ Stack a) (t : Param a) :
    PolygonalRay.Address (Length[e] + 1) := by
  cases a with
  | inl v =>
    have on_edge := (C.mem_contourEdgeGapStack F.selection contour v.val e).mpr
      ((C.mem_contourSavedGapStack F.selection contour v.val e).mp member)
    exact .inl (C.contourGapBankIndex F.selection contour v.val v.property e on_edge, t)
  | inr _ => exact .inr t

/-- Every address of a gap names an attachment whose saved stack contains that gap. -/
theorem exists_contourGapAddress_eq (e : Event) (p : PolygonalRay.Address (Length[e] + 1)) :
    ∃ (a : F.ContourAttachment) (member : e ∈ Stack a) (t : Param a),
      F.contourGapAddress contour a e member t = p := by
  rcases p with ⟨i, t⟩ | t
  · obtain ⟨v, nonroot, on_edge, equal⟩ := C.exists_contourGapBankIndex_eq F.selection contour e i
    let a : F.ContourAttachment := .inl ⟨v, nonroot⟩
    have saved : e ∈ Stack a := (C.mem_contourSavedGapStack F.selection contour v e).mpr
      ((C.mem_contourEdgeGapStack F.selection contour v e).mp on_edge)
    exact ⟨a, saved, t, congrArg (fun j => Sum.inl (j, t)) equal⟩
  · obtain ⟨edge, saved⟩ := C.exists_contourTerminalEdge_mem_gapStack F.selection contour e
    exact ⟨.inr edge, saved, t, rfl⟩

/-- The address retains the actual attachment label even when several original edges
occur along the same gap bank. The two sides use the same address convention. -/
theorem contourGapAddress_eq
    (event : Event)
    (bank other : F.ContourAttachment) (member : event ∈ Stack bank) (other_member : event ∈ Stack other)
    (t : Param bank) (s : Param other)
    (equal : F.contourGapAddress contour other event other_member s = F.contourGapAddress contour bank event member t) :
    (⟨other, s⟩ : Σ b, Param b) = ⟨bank, t⟩ := by
  cases bank with
  | inl vertex =>
    cases other with
    | inl other =>
      have named := Prod.mk.inj (Sum.inl.inj equal)
      have original := C.contourGapBankIndex_original F.selection contour vertex.val vertex.property
        event ((C.mem_contourEdgeGapStack F.selection contour vertex.val event).mpr
          ((C.mem_contourSavedGapStack F.selection contour vertex.val event).mp member))
      have other_original := C.contourGapBankIndex_original F.selection contour other.val
        other.property event ((C.mem_contourEdgeGapStack F.selection contour other.val event).mpr
          ((C.mem_contourSavedGapStack F.selection contour other.val event).mp other_member))
      have vertex_eq : other = vertex := Subtype.ext
        (other_original.symm.trans ((congrArg
          (fun i : Fin (Length[event] + 1) => F.parents.parent^[i.val]
            (C.positiveContourVertex F.selection contour event)) named.1).trans original))
      subst other
      exact congrArg (fun u : unitInterval => (⟨.inl vertex, u⟩ : Σ b, Param b)) named.2
    | inr other => cases equal
  | inr edge =>
    cases other with
    | inl other => cases equal
    | inr other =>
      have parameter := Sum.inr.inj equal
      have original := C.contourGap_last_child F.selection contour edge event
        ((C.mem_contourEdgeGapStack F.selection contour edge.val event).mpr
          ((C.mem_contourSavedGapStack F.selection contour edge.val event).mp member))
      have other_original := C.contourGap_last_child F.selection contour other event
        ((C.mem_contourEdgeGapStack F.selection contour other.val event).mpr
          ((C.mem_contourSavedGapStack F.selection contour other.val event).mp other_member))
      have edge_eq : other = edge := Subtype.ext (other_original.symm.trans original)
      subst other
      exact congrArg (fun u : ℝ≥0 => (⟨.inr edge, u⟩ : Σ b, Param b)) parameter

variable (starts : C.contourOriginalVertex F.selection contour 0 ∈ F.parents.roots)
  (models : ∀ e : Event, BankGapModel (F.contourSourceRay contour starts e)
    (F.contourSourceOpenedRay contour starts e))

/-- The named gap mark agrees with the bank's literal planar point at this address. -/
theorem contourGapMark_val_eq_addressFrontier (a : F.ContourAttachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) (t : Param a) :
    (F.contourGapMark contour starts models a e member side t).val =
      ((models e).addressFrontier (!side) (F.contourGapAddress contour a e member t)).val := by
  cases a <;> cases side <;> rfl

end Unfoldings.ConvexRoof.PotentialCutForest
