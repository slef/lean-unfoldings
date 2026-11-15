module

public import Unfoldings.Complex.BoundaryRolling
public import Unfoldings.Complex.DirectedBoundaryPath

/-! Surviving original banks keep their endpoints, lengths and entire arclength parametrizations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

/-- View the very same original tagged bank end in a restored cut where it is still a bank. -/
def survivingBoundaryEnd (p : C.BoundaryEnd small)
    (survives : C.IsBoundaryEdge large (C.germEdge p.val)) : C.BoundaryEnd large :=
  ⟨p.val, survives⟩

@[simp] theorem survivingBoundaryEnd_vertex (p : C.BoundaryEnd small)
    (survives : C.IsBoundaryEdge large (C.germEdge p.val)) :
    C.boundaryEndVertex large (C.survivingBoundaryEnd p survives) =
      C.vertexForgetCuts inclusion (C.boundaryEndVertex small p) := rfl

@[simp] theorem survivingBoundaryEnd_length (p : C.BoundaryEnd small)
    (survives : C.IsBoundaryEdge large (C.germEdge p.val)) :
    C.boundaryBankLength (C.survivingBoundaryEnd p survives) = C.boundaryBankLength p := rfl

/-- Every point of the closed original bank is preserved by the canonical map. -/
theorem survivingBoundaryEnd_path (p : C.BoundaryEnd small)
    (survives : C.IsBoundaryEdge large (C.germEdge p.val)) (t : unitInterval) :
    C.directedBoundaryPath (C.survivingBoundaryEnd p survives) t =
      C.forgetCuts inclusion (C.directedBoundaryPath p t) := by
  obtain ⟨⟨bank, side⟩, rfl⟩ := (C.boundaryEndEquiv small).symm.surjective p
  change C.faceMap large bank.val.face _ = C.forgetCuts inclusion (C.faceMap small bank.val.face _)
  exact (C.forgetCuts_faceMap inclusion _ _).symm

end Unfoldings.TriangleComplex
