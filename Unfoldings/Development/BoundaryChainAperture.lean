module

public import Unfoldings.Development.BoundaryChainRolling
public import Unfoldings.Geometry.GapAngleRotation

/-! Actual finite developed boundary banks determine their complementary retained-fan aperture. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- The complementary corner angle uses the actual developed original bank vectors in
one common physical frame, with no separately chosen normalized bank rays. -/
theorem boundaryChain_complementary_angle (k : Fin n)
    (small : C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) <
      2 * Real.pi) :
    positiveGapAngle
      (-(D.boundaryCycleFrame chain (D.boundaryRay (chain.point k.castSucc))))
      (D.boundaryCycleFrame chain (D.boundaryRay (chain.point k.succ))) =
        2 * Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) := by
  rw [D.boundaryChainRoll_edge_in_frame, D.boundaryChainRoll_edge_in_frame, ← mul_neg,
    positiveGapAngle_mul_left _ _ _ (polarRay_ne_zero _)]
  exact C.boundaryChainRoll_complementary_angle chain k small

end Unfoldings.FacewiseDevelopment
