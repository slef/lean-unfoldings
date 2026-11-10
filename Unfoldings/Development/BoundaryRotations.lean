module

public import Unfoldings.Development.BoundaryFrame
public import Unfoldings.Development.BoundaryRays
public import Unfoldings.Development.FramedLinkHeadings
public import Unfoldings.Complex.BoundaryLink

/-!
# Actual boundary-bank rotations in one common frame

A full boundary corner star rotates the outgoing bank to the other bank by
its actual intrinsic angle, in the same frame for the entire boundary cycle.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)

/-- Exact rotations at every vertex of the actual boundary, with one shared frame. -/
theorem normalized_boundaryMate_rotation (i : Fin (n + 1)) :
    NormedSpace.normalize (D.boundaryCycleFrame cycle
      (D.boundaryRay (C.boundaryMate retain (cycle.point i)))) =
    polarRay (C.totalAngle retain (C.boundaryEndVertex retain (cycle.point i))) *
      NormedSpace.normalize (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point i))) := by
  obtain ⟨m, c, first, last, covers⟩ := C.exists_boundary_link retain (cycle.point i)
  have rotation := D.normalized_terminal_bank_in_frame c (D.boundaryCycleFrame cycle)
    (D.boundaryCycleFrame_positive cycle i c first) covers
  rw [D.germRay_eq_boundaryRay c.first (cycle.point i) first,
    D.germRay_eq_boundaryRay _ (C.boundaryMate retain (cycle.point i)) last] at rotation
  exact rotation

/-- A directed boundary step turns by the genuine exterior corner angle. -/
theorem normalized_boundary_step
    (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)
    (i : Fin (n + 1)) :
    NormedSpace.normalize (D.boundaryCycleFrame cycle
      (D.boundaryRay (cycle.point (finRotate (n + 1) i)))) =
    polarRay (Real.pi - C.totalAngle retain
      (C.boundaryEndVertex retain (cycle.point (finRotate (n + 1) i)))) *
      NormedSpace.normalize (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point i))) := by
  let θ := C.totalAngle retain
    (C.boundaryEndVertex retain (cycle.point (finRotate (n + 1) i)))
  have joined : C.boundaryMate retain (C.boundaryTurn retain (cycle.point i)) =
      cycle.point (finRotate (n + 1) i) := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [finRotate_last]
      exact closes
    · rw [show finRotate (n + 1) k.castSucc = k.succ from finRotate_of_lt k.isLt]
      exact cycle.next k
  have other := congrArg (C.boundaryMate retain) joined
  rw [C.boundaryMate_involutive] at other
  have rotation := D.normalized_boundaryMate_rotation cycle (finRotate (n + 1) i)
  rw [← other, D.boundaryRay_turn, map_neg, NormedSpace.normalize_neg] at rotation
  have inverse : polarRay (-θ) * polarRay θ = 1 := by
    rw [← polarRay_add, neg_add_cancel, polarRay_zero]
  have half_turn : polarRay Real.pi = -1 := by
    apply Complex.ext <;> simp
  have phase : polarRay (Real.pi - θ) = -polarRay (-θ) := by
    rw [sub_eq_add_neg, polarRay_add, half_turn, neg_one_mul]
  change NormedSpace.normalize (D.boundaryCycleFrame cycle
    (D.boundaryRay (cycle.point (finRotate (n + 1) i)))) =
      polarRay (Real.pi - θ) *
        NormedSpace.normalize (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point i)))
  calc
    _ = (polarRay (-θ) * polarRay θ) * NormedSpace.normalize
        (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point (finRotate (n + 1) i)))) := by
      rw [inverse, one_mul]
    _ = polarRay (-θ) * (-NormedSpace.normalize
        (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point i)))) := by
      rw [mul_assoc, ← rotation]
    _ = _ := by rw [phase]; ring

end Unfoldings.FacewiseDevelopment
