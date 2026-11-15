module

public import Unfoldings.Roof.CompletionBankSubdivision
public import Unfoldings.Geometry.CommonSubedge

/-! Fine pieces of different actual original banks cannot coincide. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionDistinctBankIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The named fine bank retains its actual original incident face. -/
theorem subdividedCutBank_parent (retain : Set C.Seam) (s : C.CutSeam retain) (side : Bool)
    (a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge) :
    E.originalParent (E.subdividedCutBank retain s side a).val.face =
      (C.seamSide s.val side).face :=
  E.originalParent_eq _ a.val.1.property

open Classical in
/-- A single actual fine bank cannot be assigned to distinct original cut banks. This
uses its whole physical edge and parent face, not a presumed traversal ordering. -/
theorem original_cutBank_eq_of_subdivided_eq (retain : Set C.Seam)
    (s t : C.CutSeam retain) (side other : Bool)
    (a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge)
    (b : E.faceSidePieces (C.seamSide t.val other).face (C.seamSide t.val other).edge)
    (same : E.subdividedCutBank retain s side a = E.subdividedCutBank retain t other b) :
    C.cutBank retain s side = C.cutBank retain t other := by
  have faces := (E.subdividedCutBank_parent retain s side a).symm.trans
    ((congrArg (fun bank : E.originalComplex.BoundaryBank (E.originalRetain retain) =>
      E.originalParent bank.val.face) same).trans (E.subdividedCutBank_parent retain t other b))
  have fine_face : a.val.1.val = b.val.1.val := congrArg
    (fun bank : E.originalComplex.BoundaryBank (E.originalRetain retain) => bank.val.face.val) same
  have fine_edge : a.val.2 = b.val.2 := congrArg
    (fun bank : E.originalComplex.BoundaryBank (E.originalRetain retain) => bank.val.edge) same
  have edges : (C.seamSide s.val side).edge = (C.seamSide t.val other).edge := by
    apply (K.projectedTriangle (C.seamSide s.val side).face).edge_eq_of_common_subedge
      (E.partition.projectedTriangle a.val.1.val) _ _ a.val.2 a.property
    have contained : (E.partition.projectedTriangle b.val.1.val).edge b.val.2 ⊆
        (K.projectedTriangle (C.seamSide t.val other).face).edge
          (C.seamSide t.val other).edge := b.property
    simpa only [← fine_face, ← fine_edge, ← faces] using! contained
  exact Subtype.ext (congrArg₂ EdgeRef.mk faces edges)

end Unfoldings.ConvexRoof.CompletionMesh
