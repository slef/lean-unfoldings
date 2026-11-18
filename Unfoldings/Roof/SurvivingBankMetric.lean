module

public import Unfoldings.Roof.ProjectedBankMetric
public import Unfoldings.Complex.AffineProjectionRestoration

/-! Untouched surviving sides keep exact intrinsic rolls and real metric phase errors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {n : ℕ}
  (chain : (C.boundarySystem small).Chain n)
  (survives : ∀ i, C.IsBoundaryEdge large (C.germEdge (chain.point i).val))

/-- All actual real projected prefixes on an untouched side survive restoring other cuts. -/
theorem survivingBoundaryChain_projectedHeading (i : Fin (n + 1)) :
    K.projectedMetricHeading (C.survivingBoundaryChain inclusion chain survives) i =
      K.projectedMetricHeading chain i :=
  (congrArg (fun c => K.projectedMetricComplex.boundaryChainRollHeading c i)
    (C.affineProjectionChain_surviving K.projectFaceEquiv K.projectedTriangle_joined
      inclusion chain survives)).trans
    (K.projectedMetricComplex.survivingBoundaryChain_rollHeading inclusion
      (K.projectedMetricChain chain) (fun j => survives j) i)

/-- The numerical unreduced phase error belongs to the surviving original side. -/
theorem survivingBoundaryChain_phase_error (i : Fin (n + 1)) :
    K.projectedMetricHeadingError (C.survivingBoundaryChain inclusion chain survives) i =
      K.projectedMetricHeadingError chain i :=
  congrArg₂ (fun a b : ℝ => a - b)
    (C.survivingBoundaryChain_rollHeading inclusion chain survives i)
    (K.survivingBoundaryChain_projectedHeading inclusion chain survives i)

end Unfoldings.ConvexRoof
