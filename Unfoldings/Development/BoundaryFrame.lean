module

public import Unfoldings.Development.BoundaryOrientation
public import Unfoldings.Geometry.PlanarConjugation

/-!
# One orthogonal frame for all actual boundary corner stars

The same frame orients every interval star starting at an outgoing bank of the
actual boundary cycle. It is chosen from one corner, with orientation then
propagated through the actual hinge and bank pairings. Overlap is allowed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)

def boundaryCycleFrame : Plane ≃ₗᵢ[ℝ] ℂ :=
  if 0 < D.germOrientation cycle.first.val then Complex.orthonormalBasisOneI.repr.symm
  else planeConjugation.trans Complex.orthonormalBasisOneI.repr.symm

/-- All actual boundary stars turn positively in one common frame. -/
theorem boundaryCycleFrame_positive (i : Fin (n + 1))
    {m : ℕ} (c : (C.linkSystem retain (C.boundaryEndVertex retain (cycle.point i))).Chain m)
    (starts : c.first.val = (cycle.point i).val) (k : Fin (m + 1)) :
    0 < (starRingEnd ℂ (D.boundaryCycleFrame cycle (D.intervalLinkRay c k.castSucc)) *
      D.boundaryCycleFrame cycle (D.intervalLinkRay c k.succ)).im := by
  let L : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have cross (x y : Plane) : (starRingEnd ℂ (L x) * L y).im = orient 0 x y := by
    have identity := orient_complex_repr_zero (L x) (L y)
    change orient 0 (L.symm (L x)) (L.symm (L y)) = _ at identity
    simpa only [L.symm_apply_apply] using identity.symm
  have signs : (0 < orient 0 (D.intervalLinkRay c k.castSucc) (D.intervalLinkRay c k.succ)) ↔
      0 < D.germOrientation cycle.first.val := by
    rw [D.intervalLinkRay_castSucc, D.intervalLinkRay_succ, ← D.germOrientation_eq]
    exact (D.link_germOrientation_sign c k).trans
      ((congrArg (fun p => 0 < D.germOrientation p) starts).to_iff.trans
        (D.boundaryCycle_orientation cycle i))
  by_cases first : 0 < D.germOrientation cycle.first.val
  · simp only [boundaryCycleFrame, ite_eq_left first]
    change 0 < (starRingEnd ℂ (L (D.intervalLinkRay c k.castSucc)) *
      L (D.intervalLinkRay c k.succ)).im
    rw [cross]
    exact signs.mpr first
  · simp only [boundaryCycleFrame, ite_eq_right first]
    change 0 < (starRingEnd ℂ (L (planeConjugation (D.intervalLinkRay c k.castSucc))) *
      L (planeConjugation (D.intervalLinkRay c k.succ))).im
    rw [cross, orient_planeConjugation]
    have nonpositive := le_of_not_gt (fun positive => first (signs.mp positive))
    exact neg_pos.mpr (lt_of_le_of_ne nonpositive (D.intervalLinkRay_genuine c k))

end Unfoldings.FacewiseDevelopment
