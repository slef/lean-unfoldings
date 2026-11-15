module

public import Unfoldings.Development.LinkHeadings
public import Unfoldings.Geometry.PositiveGapAngle

/-! Complementary geometric angles of actual terminal bank vectors, including reentrant gaps. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {w : C.Vertex retain} {n : ℕ} (c : (C.linkSystem retain w).Chain n)

/-- The complementary gap angle is derived from the actual original bank vectors and real
retained fan angle. The conclusion covers angles on either side of a half-turn. -/
theorem terminal_bank_complementary_angle (covers : ∀ p, c.Visited p)
    (small : C.totalAngle retain w < 2 * Real.pi) :
    positiveGapAngle
      (D.linkDevelopFrame c (D.germRay (C.linkTurn retain w c.last)))
      (D.linkDevelopFrame c (D.germRay c.first)) = 2 * Real.pi - C.totalAngle retain w := by
  let x := D.linkDevelopFrame c (D.germRay c.first)
  let y := D.linkDevelopFrame c (D.germRay (C.linkTurn retain w c.last))
  let θ := C.totalAngle retain w
  have nonzero : y ≠ 0 := by
    simpa only [map_zero] using (D.linkDevelopFrame c).injective.ne
      (D.germRay_ne_zero (C.linkTurn retain w c.last))
  have forward : y / (‖y‖ : ℂ) = polarRay θ * (x / (‖x‖ : ℂ)) := by
    have actual := D.normalized_terminal_bank c covers
    change NormedSpace.normalize y = polarRay θ * NormedSpace.normalize x at actual
    simpa only [NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv,
      mul_comm] using actual
  apply positiveGapAngle_of_normalized_rotation y x nonzero (sub_pos.mpr small)
    (by linarith [C.totalAngle_pos retain w])
  have period : polarRay (2 * Real.pi - θ) = polarRay (-θ) := by
    rw [sub_eq_add_neg, polarRay_add]
    simp [polarRay]
  rw [period, forward, ← mul_assoc, ← polarRay_add, neg_add_cancel, polarRay_zero, one_mul]

end Unfoldings.FacewiseDevelopment
