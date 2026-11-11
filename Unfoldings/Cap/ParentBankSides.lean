module

public import Unfoldings.Cap.ParentBankOpening
public import Unfoldings.Cap.SectionBankSides
public import Unfoldings.Cap.ProjectedOpening

/-!
# Actual parent-bank phases have the geometric section crossing sign

Approaching the entrance bank means moving from the right of the outward parent
edge to its left, and approaching its exit bank gives the reverse sign. These
signs follow from actual original-face containment along the constructed trace.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Either actual bank of an original seam has the same whole projected edge. -/
theorem projected_bank_edge_eq {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    (s : C.Seam) (side : Bool) (named : C.germEdge p.val = C.seamSide s side) :
    (K.projectedTriangle p.val.1.1).edge (C.germEdge p.val).edge =
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
  have edge := congrArg
    (fun edge : EdgeRef Face => (K.projectedTriangle edge.face).edge edge.edge) named
  change (K.projectedTriangle p.val.1.1).edge (C.germEdge p.val).edge =
    (K.projectedTriangle (C.seamSide s side).face).edge (C.seamSide s side).edge at edge
  rw [edge]
  cases side
  · rfl
  · exact (K.projected_seam_edges_eq s).symm

end Unfoldings.ConvexCap

namespace Unfoldings.ConvexCap.SectorForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {D : FacewiseDevelopment C M.retain}
  {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}} (B : M.ParentBankOpening D e)

/-- Positive outward determinant gives the actual positive curvature phase at the entrance. -/
theorem entrance_crossing_sign {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (first_face : T.face i.castSucc = B.entranceFace)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left (M.selection.edge e)).face).edge
        (C.left (M.selection.edge e)).edge) :
    0 < orient 0
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) (q - p) := by
  let bank := M.projectionContour.cycle.point B.enter
  have positive := D.projectedGermOrientation_cycle_positive K M.duallyConnected
    M.projectionContour.cycle M.projectionContour_positive B.enter
  have named := congrArg Subtype.val B.first_named
  have edge := K.projected_bank_edge_eq bank (M.selection.edge e) B.side named
  have cross : T.point i.castSucc.succ ∈
      (K.projectedTriangle bank.val.1.1).edge (C.germEdge bank.val).edge := edge.symm ▸ crossing
  have sign := T.bank_exit_sign different regular i bank.val first_face positive cross
  rw [K.projectedGermVector_parent_entrance M.selection e.val e.property
    bank B.side B.first_named B.outside] at sign
  have reverse (a b : Plane) : orient 0 (-a) b = -orient 0 a b := by
    simp only [orient, PiLp.neg_apply, PiLp.zero_apply, sub_zero]
    ring
  rw [reverse] at sign
  exact neg_neg_iff_pos.mp sign

/-- Negative outward determinant gives the actual negative curvature phase in reverse. -/
theorem exit_crossing_sign {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (first_face : T.face i.castSucc = B.exitFace)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left (M.selection.edge e)).face).edge
        (C.left (M.selection.edge e)).edge) :
    orient 0
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) (q - p) < 0 := by
  let bank := M.projectionContour.cycle.point B.leave
  have positive := D.projectedGermOrientation_cycle_positive K M.duallyConnected
    M.projectionContour.cycle M.projectionContour_positive B.leave
  have named := congrArg Subtype.val B.last_named
  have edge := K.projected_bank_edge_eq bank (M.selection.edge e) (!B.side) named
  have cross : T.point i.castSucc.succ ∈
      (K.projectedTriangle bank.val.1.1).edge (C.germEdge bank.val).edge := edge.symm ▸ crossing
  have sign := T.bank_exit_sign different regular i bank.val first_face positive cross
  rwa [K.projectedGermVector_parent_exit M.selection e.val e.property
    bank (!B.side) B.last_named B.inside] at sign

end Unfoldings.ConvexCap.SectorForest.ParentBankOpening
