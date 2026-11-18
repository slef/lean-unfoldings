module

public import Unfoldings.Roof.ProjectedBankFrames
public import Unfoldings.Geometry.PolygonalLength

/-! Quantitative accuracy of the actual intrinsic bank roll in its original physical frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Aligned chord error and length-to-chord control of the actual original intrinsic roll. -/
structure BankRollAccuracy (error lengthConstant : ℝ) (retain : Set C.Seam) {m : ℕ}
    (full : (C.boundarySystem retain).Chain m) : Prop where
  chord_error :
    let P := (K.folding.projectedBoundaryChain full).inComplexFrame (K.projectedBankFrame full)
    let Q := K.framedIntrinsicRoll full
    ‖polarRay (-K.projectedMetricHeadingError full (Fin.last m)) *
        (Q.vertex (Fin.last (m + 1)) - Q.vertex 0) -
      (P.vertex (Fin.last (m + 1)) - P.vertex 0)‖ ≤
      error * ‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖
  length_bound : (C.boundaryChainRoll full).projectedLength ≤ lengthConstant *
    ‖(C.boundaryChainRoll full).vertex (Fin.last (m + 1)) -
      (C.boundaryChainRoll full).vertex 0‖

end Unfoldings.ConvexRoof
