module

public import Unfoldings.Complex.BoundaryContourPaths

/-! The whole intrinsic trace of an actual bank chain, including all endpoint copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- All actual metric points on the named banks. Overlap is allowed after development. -/
def boundaryChainTrace {n : ℕ} (chain : (C.boundarySystem retain).Chain n) :
    Set (C.Realization retain) :=
  ⋃ i, Set.range (C.bankMap retain (C.boundaryEndEquiv retain (chain.point i)).1)

/-- Directed interpolation covers precisely its entire original closed bank. -/
theorem directedBoundaryPath_range (p : C.BoundaryEnd retain) :
    Set.range (C.directedBoundaryPath p) =
      Set.range (C.bankMap retain (C.boundaryEndEquiv retain p).1) :=
  by
    change Set.range (C.bankMap retain (C.boundaryEndEquiv retain p).1 ∘
      C.bankParameterFromEnd (C.boundaryEndEquiv retain p).1 (C.boundaryEndEquiv retain p).2) = _
    rw [Set.range_comp, (C.bankParameterFromEnd_surjective _ _).range_eq, Set.image_univ]

/-- The trace includes every point of every directed bank and both true endpoints. -/
theorem boundaryChainTrace_eq_union_paths {n : ℕ} (chain : (C.boundarySystem retain).Chain n) :
    C.boundaryChainTrace chain = ⋃ i, Set.range (C.directedBoundaryPath (chain.point i)) := by
  simp only [boundaryChainTrace, C.directedBoundaryPath_range]

end Unfoldings.TriangleComplex
