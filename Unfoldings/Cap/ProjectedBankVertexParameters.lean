module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Complex.VertexCopyFibers

/-! A genuine bank interior cannot pass through any original full-mesh projected vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Every full-mesh vertex contact on an actual bank is at an actual bank endpoint.
The assertion also holds for face restrictions and independently cut seam copies. -/
theorem projectedBoundaryChain_parameter_endpoint_of_vertex (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (chain : ((C.restrictFaces U).boundarySystem retain).Chain n)
    (i : Fin (n + 1)) (t : unitInterval) (v : C.Vertex Set.univ)
    (same : (K.projectedBoundaryChain U chain).point i t = K.projectedVertex v) :
    t = 0 ∨ t = 1 := by
  by_cases zero : t.val = 0
  · exact Or.inl (Subtype.ext zero)
  by_cases one : t.val = 1
  · exact Or.inr (Subtype.ext one)
  have positive : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm zero)
  have small : t.val < 1 := lt_of_le_of_ne t.property.2 one
  let R := C.restrictFaces U
  let bank := (R.boundaryEndEquiv retain (chain.point i)).1
  let side := (R.boundaryEndEquiv retain (chain.point i)).2
  let x := R.bankParameterFromEnd bank side t
  let y : C.Cell bank.val.face.val := (R.triangle bank.val.face).edgeMap bank.val.edge x
  have regular := R.bankParameterFromEnd_nonvertex bank side t positive small
  rw [K.projectedBoundaryChain_point] at same
  change Cap.horizontal (K.folding.toSpace Set.univ
      (C.faceMap Set.univ bank.val.face.val y)) =
    Cap.horizontal (K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)) at same
  have original := K.projection_injective same
  have vertex := (C.mem_range_vertexPoint_iff Set.univ ⟨bank.val.face.val, y⟩).mp
    ⟨v, original.symm⟩
  exact (regular vertex).elim

end Unfoldings.ConvexCap
