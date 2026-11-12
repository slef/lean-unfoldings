module

public import Unfoldings.Complex.ParentBankEndpoints
public import Unfoldings.Complex.Folding

/-! A spatial folding keeps the two endpoints of every actual boundary bank distinct. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

include F in
/-- The two endpoint germs of a boundary bank represent distinct intrinsic vertices. -/
theorem boundaryEndVertex_ne_turn (retain : Set C.Seam) (p : C.BoundaryEnd retain) :
    C.boundaryEndVertex retain p ≠ C.boundaryEndVertex retain (C.boundaryTurn retain p) := by
  obtain ⟨⟨bank, b⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  intro same
  have equal := congrArg (C.vertexPoint retain) same
  simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply] at equal
  cases b
  · change C.faceMap retain bank.val.face
        ⟨(C.triangle bank.val.face).vertex bank.val.edge, _⟩ =
      C.faceMap retain bank.val.face
        ⟨(C.triangle bank.val.face).vertex (Triangle.next bank.val.edge), _⟩ at equal
    exact (C.triangle bank.val.face).edge_endpoints_ne bank.val.edge
      (congrArg Subtype.val ((F.faceMap_isometry retain bank.val.face).injective equal))
  · change C.faceMap retain bank.val.face
        ⟨(C.triangle bank.val.face).vertex (Triangle.next bank.val.edge), _⟩ =
      C.faceMap retain bank.val.face
        ⟨(C.triangle bank.val.face).vertex bank.val.edge, _⟩ at equal
    exact (C.triangle bank.val.face).edge_endpoints_ne bank.val.edge
      (congrArg Subtype.val ((F.faceMap_isometry retain bank.val.face).injective equal)).symm

include F in
/-- At a fixed intrinsic vertex, bank names distinguish its boundary ends. -/
theorem boundaryEnd_eq_of_same_bank_vertex (retain : Set C.Seam)
    (p q : C.BoundaryEnd retain)
    (bank : (C.boundaryEndEquiv retain p).1 = (C.boundaryEndEquiv retain q).1)
    (vertex : C.boundaryEndVertex retain p = C.boundaryEndVertex retain q) : p = q := by
  rcases (C.boundaryEnd_bank_eq_iff retain p q).mp bank with same | opposite
  · exact same
  · exact ((F.boundaryEndVertex_ne_turn retain q) ((congrArg
      (C.boundaryEndVertex retain) opposite).symm.trans vertex).symm).elim

end Unfoldings.SpatialFolding
