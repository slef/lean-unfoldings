module

public import Unfoldings.Complex.ClosedBanks
public import Unfoldings.Complex.BoundaryOrdering

/-! Directed original cut banks, retaining their seam, side and starting endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Original seam and side are independent of its directed starting endpoint. -/
structure DirectedCutBank (retain : Set C.Seam) where
  seam : C.CutSeam retain
  side : Bool
  flag : Bool

namespace DirectedCutBank

variable {C} {retain : Set C.Seam} (tag : C.DirectedCutBank retain)

/-- The actual original bank, with its unpaired-edge proof. -/
def bank : C.BoundaryBank retain := C.cutBank retain tag.seam tag.side

/-- The actual directed starting bank end. -/
def start : C.BoundaryEnd retain := (C.boundaryEndEquiv retain).symm (tag.bank, tag.flag)

/-- The original retained corner tag at the directed start. -/
def startCorner : C.Corner := (C.germOfEndpoint (C.seamSide tag.seam.val tag.side) tag.flag).1

/-- The original retained corner tag at the directed far endpoint. -/
def finishCorner : C.Corner :=
  (C.germOfEndpoint (C.seamSide tag.seam.val tag.side) (!tag.flag)).1

@[simp] theorem start_vertex : C.boundaryEndVertex retain tag.start =
    C.vertexOfCorner retain tag.startCorner := rfl

@[simp] theorem finish_vertex :
    C.boundaryEndVertex retain (C.boundaryTurn retain tag.start) =
      C.vertexOfCorner retain tag.finishCorner := by
  simp only [start, TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  rfl

end DirectedCutBank
end Unfoldings.TriangleComplex
