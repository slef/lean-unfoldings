module

public import Unfoldings.Roof.SurvivingBankMetric
public import Unfoldings.Polyhedron.SurvivingBankGeometry
public import Unfoldings.Roof.BankRollAccuracy

/-! Quantitative rolling bounds follow the same untouched side as other cuts are restored. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {n : ℕ}
  (chain : (C.boundarySystem small).Chain n)
  (survives : ∀ i, C.IsBoundaryEdge large (C.germEdge (chain.point i).val))

theorem survivingBoundaryChain_frame :
    K.projectedBankFrame (C.survivingBoundaryChain inclusion chain survives) =
      K.projectedBankFrame chain := rfl

theorem survivingBoundaryChain_phase :
    K.projectedBankPhase (C.survivingBoundaryChain inclusion chain survives) =
      K.projectedBankPhase chain := by
  let restored := C.survivingBoundaryChain inclusion chain survives
  have first : restored.first.val = chain.first.val := rfl
  calc
    _ = (K.projectedBankFrame restored
        (Cap.horizontal (K.folding.germDirection restored.first.val))).arg :=
      congrArg (fun x => (K.projectedBankFrame restored x).arg)
        (K.projectedMetric_boundaryRay restored.first)
    _ = (K.projectedBankFrame chain
        (Cap.horizontal (K.folding.germDirection chain.first.val))).arg := by
      rw [K.survivingBoundaryChain_frame, first]
    _ = _ := (congrArg (fun x => (K.projectedBankFrame chain x).arg)
      (K.projectedMetric_boundaryRay chain.first)).symm

/-- Neither rigid frame nor any point of the original intrinsic roll changes. -/
theorem survivingBoundaryChain_framedRoll :
    K.framedIntrinsicRoll (C.survivingBoundaryChain inclusion chain survives) =
      K.framedIntrinsicRoll chain :=
  congrArg₂ (fun (P : PolygonalChain ℂ (n + 1)) (phase : ℝ) =>
    P.affineMap (complexRotation phase).toLinearMap.toAffineMap)
    (C.survivingBoundaryChain_roll inclusion chain survives)
    (K.survivingBoundaryChain_phase inclusion chain survives)

/-- The same quantitative accuracy controls the exact surviving original side. -/
theorem survivingBoundaryChain_accuracy {error lengthConstant : ℝ}
    (data : K.BankRollAccuracy error lengthConstant small chain) :
    K.BankRollAccuracy error lengthConstant large
      (C.survivingBoundaryChain inclusion chain survives) := by
  constructor
  · simpa only [K.survivingBoundaryChain_phase_error, K.survivingBoundaryChain_frame,
      K.survivingBoundaryChain_framedRoll, K.folding.survivingBoundaryChain_projected]
      using data.chord_error
  · simpa only [C.survivingBoundaryChain_roll] using data.length_bound

end Unfoldings.ConvexRoof
