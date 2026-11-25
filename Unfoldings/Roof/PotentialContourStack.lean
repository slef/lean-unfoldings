module

public import Unfoldings.Roof.PotentialContourGap
public import Unfoldings.Complex.ContourGapTerminalIndex
public import Unfoldings.Geometry.BankGapTailJoin

/-! The contour's finite edges and continued exits use the same ordered bank labels. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (F : K.PotentialCutForest f cuts)

/-- The finite parent edges and the tails of the terminal parent edges. -/
abbrev ContourAttachment :=
  {v : C.Vertex Set.univ // v ∉ F.parents.roots} ⊕ C.ContourTerminalEdge F.selection

/-- Marks on finite edges are normalized to the unit interval. Tail marks
use the entire nonnegative parameter of the final finite edge. -/
abbrev contourAttachmentParameter : F.ContourAttachment → Type
  | .inl _ => unitInterval
  | .inr _ => ℝ≥0

variable (contour : C.BoundaryContour F.retain)
  (starts : C.contourOriginalVertex F.selection contour 0 ∈ F.parents.roots)

/-- Each tail inherits the exact saved stack of its finite terminal edge. -/
def contourAttachmentStack : F.ContourAttachment → List (C.PositiveContourSource F.selection contour)
  | .inl vertex => C.contourSavedGapStack F.selection contour vertex.val
  | .inr edge => C.contourSavedGapStack F.selection contour edge.val

local notation "Event" => TriangleComplex.PositiveContourSource C F.selection contour
local notation "Stack" => contourAttachmentStack F contour
local notation "Param" => contourAttachmentParameter F

variable (models : ∀ event : C.PositiveContourSource F.selection contour,
  BankGapModel (F.contourSourceRay contour starts event)
    (F.contourSourceOpenedRay contour starts event))

local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex C F.selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack C F.selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack C F.selection contour v e) member))

/-- The count of previously saved banks fixes the actual finite gap edge.
The same stack then continues on the gap's true tail. -/
def contourGapMark (attach : F.ContourAttachment) (event : Event)
    (member : event ∈ Stack attach) (side : Bool) (t : Param attach) :
    PolygonalPoint (models event).region := by
  cases attach with
  | inl vertex =>
    exact (models event).edgePoint (!side) IndexAt[vertex.val,vertex.property,event,member] t
  | inr _ =>
    exact (models event).tailPoint (!side) t

/-- The finite and infinite attachments meet at the exact same gap vertex. -/
theorem contourGapMark_tail_zero (edge : C.ContourTerminalEdge F.selection)
    (event : Event) (member : event ∈ Stack (.inr edge)) (side : Bool) :
    F.contourGapMark contour starts models (.inr edge) event member side 0 =
      F.contourGapMark contour starts models (.inl ⟨edge.val, edge.property.1⟩)
        event member side 1 := by
  let gap := models event
  change gap.tailPoint (!side) 0 = gap.edgePoint (!side)
    IndexAt[edge.val,edge.property.1,event,member] 1
  rw [gap.tailPoint_zero_eq_edgePoint]
  exact congrArg (fun i => gap.edgePoint (!side) i 1)
    ((C.contourGapBankIndex_last F.selection contour edge event _).symm)

end Unfoldings.ConvexRoof.PotentialCutForest
