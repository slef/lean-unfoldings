module

public import Unfoldings.Complex.BoundaryContourPaths
public import Unfoldings.Complex.BoundaryChainTrace

/-! Every intrinsic boundary copy has an actual directed-bank parametrization. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Parametrize a specified boundary point without assuming a single global contour. -/
theorem exists_directedBoundaryPath_of_mem_boundary {retain : Set C.Seam}
    {x : C.Realization retain} (member : x ∈ C.bankBoundary retain) :
    ∃ (p : C.BoundaryEnd retain) (t : unitInterval), C.directedBoundaryPath p t = x := by
  obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp member
  let p := (C.boundaryEndEquiv retain).symm (bank, false)
  have on_path : C.bankMap retain bank y ∈ Set.range (C.directedBoundaryPath p) := by
    rw [C.directedBoundaryPath_range]
    have named : (C.boundaryEndEquiv retain p).1 = bank :=
      congrArg Prod.fst ((C.boundaryEndEquiv retain).apply_symm_apply (bank, false))
    rw [named]
    exact ⟨y, rfl⟩
  obtain ⟨t, at_point⟩ := on_path
  exact ⟨p, t, at_point⟩

end Unfoldings.TriangleComplex
