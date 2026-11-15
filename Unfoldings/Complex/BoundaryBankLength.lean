module

public import Unfoldings.Complex.BoundaryChainRolling

/-! The actual bank length depends only on its labeled edge, not its starting endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- Either directed bank end measures the full length of its same original edge. -/
theorem boundaryBankLength_eq_edge (p : C.BoundaryEnd retain) :
    C.boundaryBankLength p =
      dist ((C.triangle (C.germEdge p.val).face).vertex (C.germEdge p.val).edge)
        ((C.triangle (C.germEdge p.val).face).vertex (Triangle.next (C.germEdge p.val).edge)) := by
  obtain ⟨⟨bank, flag⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  rcases bank with ⟨⟨face, edge⟩, boundary⟩
  change dist ((C.triangle face).vertex
      (C.germFarCorner (C.germOfEndpoint ⟨face, edge⟩ flag)).2)
    ((C.triangle face).vertex (C.germOfEndpoint ⟨face, edge⟩ flag).1.2) = _
  rw [C.germFarCorner_germOfEndpoint]
  change _ = dist ((C.triangle (C.germEdge (C.germOfEndpoint ⟨face, edge⟩ flag)).face).vertex
    (C.germEdge (C.germOfEndpoint ⟨face, edge⟩ flag)).edge)
      ((C.triangle (C.germEdge (C.germOfEndpoint ⟨face, edge⟩ flag)).face).vertex
        (Triangle.next (C.germEdge (C.germOfEndpoint ⟨face, edge⟩ flag)).edge))
  rw [C.germEdge_germOfEndpoint]
  cases flag
  · exact dist_comm _ _
  · rfl

end Unfoldings.TriangleComplex
