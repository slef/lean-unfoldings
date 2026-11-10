module

public import Unfoldings.Development.IntervalRays
public import Unfoldings.Geometry.ComplexTurn

/-!
# Link headings in a prescribed common frame

The frame is explicit, so exact rotations of different boundary stars can be
composed. Only positive orientation of the actual consecutive corners is needed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {v : C.Vertex retain} {n : ℕ} (c : (C.linkSystem retain v).Chain n)

variable (L : Plane ≃ₗᵢ[ℝ] ℂ)
  (positive : ∀ i : Fin (n + 1),
    0 < (starRingEnd ℂ (L (D.intervalLinkRay c i.castSucc)) *
      L (D.intervalLinkRay c i.succ)).im)

include positive

/-- These are real, unreduced headings, not just congruences modulo a full turn. -/
theorem intervalLinkRay_heading_in_frame (i : Fin (n + 2)) :
    L (D.intervalLinkRay c i) =
      (‖D.intervalLinkRay c i‖ : ℂ) * polarRay
        ((L (D.intervalLinkRay c 0)).arg +
          (C.linkAngularFan retain v c).heading i) := by
  let A := C.linkAngularFan retain v c
  change L (D.intervalLinkRay c i) = (‖D.intervalLinkRay c i‖ : ℂ) *
    polarRay ((L (D.intervalLinkRay c 0)).arg + A.heading i)
  refine Fin.induction ?_ (fun k previous => ?_) i
  · rw [A.heading_zero, add_zero]
    have polar := (Complex.norm_mul_exp_arg_mul_I (L (D.intervalLinkRay c 0))).symm
    change L (D.intervalLinkRay c 0) = (‖L (D.intervalLinkRay c 0)‖ : ℂ) *
      polarRay (L (D.intervalLinkRay c 0)).arg at polar
    simpa only [L.norm_map] using polar
  · have first : L (D.intervalLinkRay c k.castSucc) =
        (‖L (D.intervalLinkRay c k.castSucc)‖ : ℂ) *
          polarRay ((L (D.intervalLinkRay c 0)).arg + A.heading k.castSucc) := by
      simpa only [L.norm_map] using previous
    have successor := polar_successor_of_positive_cross _ first (positive k)
    have angle : InnerProductGeometry.angle (L (D.intervalLinkRay c k.castSucc))
        (L (D.intervalLinkRay c k.succ)) = A.angle k :=
      (L.toLinearIsometry.angle_map _ _).trans (D.intervalLinkRay_angle c k)
    rw [angle] at successor
    change L (D.intervalLinkRay c k.succ) = (‖L (D.intervalLinkRay c k.succ)‖ : ℂ) *
      polarRay ((L (D.intervalLinkRay c 0)).arg + A.heading k.castSucc + A.angle k) at successor
    rw [L.norm_map] at successor
    simpa only [A.heading_succ, add_assoc] using successor

theorem normalized_intervalLinkRay_heading_in_frame (i : Fin (n + 2)) :
    NormedSpace.normalize (L (D.intervalLinkRay c i)) =
      polarRay ((L (D.intervalLinkRay c 0)).arg +
        (C.linkAngularFan retain v c).heading i) := by
  have nonzero := norm_ne_zero_iff.mpr (D.intervalLinkRay_ne_zero c i)
  rw [NormedSpace.normalize, (L).norm_map, D.intervalLinkRay_heading_in_frame c L positive i]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ nonzero, Complex.ofReal_one, one_mul]

/-- The true terminal bank direction rotates by the full intrinsic retained angle. -/
theorem normalized_terminal_bank_in_frame (covers : ∀ p, c.Visited p) :
    NormedSpace.normalize (L (D.germRay (C.linkTurn retain v c.last))) =
      polarRay (C.totalAngle retain v) *
        NormedSpace.normalize (L (D.germRay c.first)) := by
  have first : D.intervalLinkRay c 0 = D.germRay c.first := by
    change D.intervalLinkRay c (0 : Fin (n + 1)).castSucc = _
    rw [D.intervalLinkRay_castSucc]
    rfl
  have start := D.normalized_intervalLinkRay_heading_in_frame c L positive 0
  have finish := D.normalized_intervalLinkRay_heading_in_frame c L positive (Fin.last (n + 1))
  rw [first, AngularFan.heading_zero, add_zero] at start
  rw [D.intervalLinkRay_last, C.linkAngularFan_last_heading retain v c covers, polarRay_add]
    at finish
  rw [start]
  exact finish.trans (mul_comm _ _)

end Unfoldings.FacewiseDevelopment
