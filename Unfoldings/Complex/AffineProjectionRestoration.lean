module

public import Unfoldings.Complex.AffineProjectionChains
public import Unfoldings.Complex.SurvivingBoundaryChain

/-! Projection and restoration commute on the same actual surviving directed banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {n : ℕ}
  (chain : (C.boundarySystem small).Chain n)
  (survives : ∀ i, C.IsBoundaryEdge large (C.germEdge (chain.point i).val))

/-- No reordering or metric-copy choice occurs when these two operations are interchanged. -/
theorem affineProjectionChain_surviving :
    C.affineProjectionChain A joined (C.survivingBoundaryChain inclusion chain survives) =
      (C.affineProjectionComplex A joined).survivingBoundaryChain inclusion
        (C.affineProjectionChain A joined chain) (fun i => survives i) := rfl

end Unfoldings.TriangleComplex
