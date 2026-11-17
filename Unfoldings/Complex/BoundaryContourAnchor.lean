module

public import Unfoldings.Complex.BoundaryContourRotation

/-! Anchor an actual directed boundary contour at a specified original boundary vertex copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} (Q : C.BoundaryContour retain)
  (vertex : C.Vertex retain) (boundary : C.IsBoundaryVertex retain vertex)

/-- Rotate the original contour to the unique position of the named boundary copy. -/
def BoundaryContour.anchor : C.BoundaryContour retain :=
  Q.rotate C ((C.boundaryCycleVertexEquiv retain Q.cycle Q.closes Q.covers).symm
    ⟨vertex, boundary⟩)

/-- Anchoring retains the exact original vertex copy, rather than just its folded position. -/
@[simp] theorem BoundaryContour.anchor_first :
    C.boundaryEndVertex retain (Q.anchor C vertex boundary).cycle.first = vertex := by
  rw [BoundaryContour.anchor, BoundaryContour.rotate_first]
  exact congrArg Subtype.val
    ((C.boundaryCycleVertexEquiv retain Q.cycle Q.closes Q.covers).apply_symm_apply
      ⟨vertex, boundary⟩)

end Unfoldings.TriangleComplex
