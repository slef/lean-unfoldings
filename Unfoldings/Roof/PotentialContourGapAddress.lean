module

public import Unfoldings.Roof.PotentialContourStack
public import Unfoldings.Complex.ContourGapBankSurjectivity
public import Unfoldings.Geometry.BankGapBoundaryMap

/-! Every finite and continued gap address has the matching original stack attachment. -/

@[expose] public section

noncomputable section

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
