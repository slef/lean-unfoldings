module

public import Unfoldings.Development.LinkHeadings

/-!
# Actual terminal bank opening and zero-defect contact

The endpoint rotation follows from the original retained corner angles.
For a defect between zero and pi its genuine unoriented bank aperture is
exactly that defect. At zero the unit directions coincide; no injectivity or
strict separation is asserted.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {v : C.Vertex retain} {n : ℕ} (c : (C.linkSystem retain v).Chain n)

/-- The actual retained corner angle gives the complementary bank opening. -/
theorem normalized_bank_opening (covers : ∀ p, c.Visited p) {κ : ℝ}
    (angle : C.totalAngle retain v = 2 * Real.pi - κ) :
    NormedSpace.normalize (D.linkDevelopFrame c (D.germRay (C.linkTurn retain v c.last))) =
      polarRay (-κ) * NormedSpace.normalize (D.linkDevelopFrame c (D.germRay c.first)) := by
  have periodic : polarRay (2 * Real.pi - κ) = polarRay (-κ) := by
    have identity := congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_add_two_pi (-κ))
    change polarRay (-κ + 2 * Real.pi) = polarRay (-κ) at identity
    convert identity using 1
    congr 1
    ring
  rw [D.normalized_terminal_bank c covers, angle, periodic]

/-- Matched actual edge lengths upgrade the unit-direction relation to a rigid bank rotation. -/
theorem bank_rotation_of_equal_length (covers : ∀ p, c.Visited p) {κ : ℝ}
    (angle : C.totalAngle retain v = 2 * Real.pi - κ)
    (lengths : ‖D.germRay (C.linkTurn retain v c.last)‖ = ‖D.germRay c.first‖) :
    D.linkDevelopFrame c (D.germRay (C.linkTurn retain v c.last)) =
      polarRay (-κ) * D.linkDevelopFrame c (D.germRay c.first) := by
  let L := D.linkDevelopFrame c
  let a := D.germRay c.first
  let b := D.germRay (C.linkTurn retain v c.last)
  have same : ‖L b‖ = ‖L a‖ := by simpa only [L.norm_map] using lengths
  have opening := D.normalized_bank_opening c covers angle
  change NormedSpace.normalize (L b) = polarRay (-κ) * NormedSpace.normalize (L a) at opening
  calc
    L b = ‖L b‖ • NormedSpace.normalize (L b) := (NormedSpace.norm_smul_normalize _).symm
    _ = ‖L a‖ • (polarRay (-κ) * NormedSpace.normalize (L a)) := by rw [same, opening]
    _ = polarRay (-κ) * (‖L a‖ • NormedSpace.normalize (L a)) := by
      simp only [Complex.real_smul]
      ring
    _ = polarRay (-κ) * L a := by rw [NormedSpace.norm_smul_normalize]

/-- At zero opening, contact of the two actual unit bank directions is allowed. -/
theorem normalized_banks_eq_of_full_turn (covers : ∀ p, c.Visited p)
    (angle : C.totalAngle retain v = 2 * Real.pi) :
    NormedSpace.normalize (D.linkDevelopFrame c (D.germRay (C.linkTurn retain v c.last))) =
      NormedSpace.normalize (D.linkDevelopFrame c (D.germRay c.first)) := by
  simpa only [neg_zero, polarRay_zero, one_mul] using
    D.normalized_bank_opening c covers (κ := 0) (by simpa only [sub_zero] using angle)

/-- For small nonnegative defects, the actual endpoint aperture is the exact intrinsic defect. -/
theorem bank_aperture_eq_defect (covers : ∀ p, c.Visited p) {κ : ℝ}
    (nonnegative : 0 ≤ κ) (small : κ ≤ Real.pi)
    (angle : C.totalAngle retain v = 2 * Real.pi - κ) :
    InnerProductGeometry.angle (D.germRay c.first)
      (D.germRay (C.linkTurn retain v c.last)) = κ := by
  let L := D.linkDevelopFrame c
  let a := D.germRay c.first
  let b := D.germRay (C.linkTurn retain v c.last)
  let u := NormedSpace.normalize (L a)
  have genuine : L a ≠ 0 := by
    simpa only [map_zero] using L.injective.ne (D.germRay_ne_zero c.first)
  have une : u ≠ 0 := by
    have unit : ‖u‖ = 1 := NormedSpace.norm_normalize genuine
    intro zero
    rw [zero, norm_zero] at unit
    norm_num at unit
  have opening := D.normalized_bank_opening c covers angle
  calc
    _ = InnerProductGeometry.angle b a := InnerProductGeometry.angle_comm _ _
    _ = InnerProductGeometry.angle (L b) (L a) := (L.toLinearIsometry.angle_map _ _).symm
    _ = InnerProductGeometry.angle (NormedSpace.normalize (L b)) u := by
      simp only [u, InnerProductGeometry.angle_normalize_left,
        InnerProductGeometry.angle_normalize_right]
    _ = InnerProductGeometry.angle (polarRay (-κ) * u) u := by rw [opening]
    _ = InnerProductGeometry.angle (polarRay (-κ) * u) (1 * u) := by rw [one_mul]
    _ = InnerProductGeometry.angle (polarRay (-κ)) 1 := Complex.angle_mul_right une _ _
    _ = κ := by
      simpa only [polarRay_zero, sub_neg_eq_add, zero_add] using
        angle_polarRay (-κ) 0 (by linarith : 0 ≤ 0 - -κ) (by linarith : 0 - -κ ≤ Real.pi)

end Unfoldings.FacewiseDevelopment
