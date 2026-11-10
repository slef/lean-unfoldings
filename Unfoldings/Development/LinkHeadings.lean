module

public import Unfoldings.Development.FramedLinkHeadings

/-!
# Exact unreduced headings of actual developed vertex links

Adjacent hinge separation gives a common orientation even if distant pieces
of the development overlap. Each real heading adds the original corner angle;
the terminal bank rotation therefore records the actual full intrinsic angle.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {v : C.Vertex retain} {n : ℕ} (c : (C.linkSystem retain v).Chain n)

def linkDevelopFrame : Plane ≃ₗᵢ[ℝ] ℂ := (D.exists_positive_link_frame c).choose

theorem linkDevelopFrame_positive (i : Fin (n + 1)) :
    0 < (starRingEnd ℂ (D.linkDevelopFrame c (D.intervalLinkRay c i.castSucc)) *
      D.linkDevelopFrame c (D.intervalLinkRay c i.succ)).im :=
  (D.exists_positive_link_frame c).choose_spec i

/-- These are real, unreduced headings, not just congruences modulo a full turn. -/
theorem intervalLinkRay_heading (i : Fin (n + 2)) :
    D.linkDevelopFrame c (D.intervalLinkRay c i) =
      (‖D.intervalLinkRay c i‖ : ℂ) * polarRay
        ((D.linkDevelopFrame c (D.intervalLinkRay c 0)).arg +
          (C.linkAngularFan retain v c).heading i) :=
  D.intervalLinkRay_heading_in_frame c (D.linkDevelopFrame c) (D.linkDevelopFrame_positive c) i

theorem normalized_intervalLinkRay_heading (i : Fin (n + 2)) :
    NormedSpace.normalize (D.linkDevelopFrame c (D.intervalLinkRay c i)) =
      polarRay ((D.linkDevelopFrame c (D.intervalLinkRay c 0)).arg +
        (C.linkAngularFan retain v c).heading i) :=
  D.normalized_intervalLinkRay_heading_in_frame c (D.linkDevelopFrame c)
    (D.linkDevelopFrame_positive c) i

/-- The true terminal bank direction rotates by the full intrinsic retained angle. -/
theorem normalized_terminal_bank (covers : ∀ p, c.Visited p) :
    NormedSpace.normalize (D.linkDevelopFrame c (D.germRay (C.linkTurn retain v c.last))) =
      polarRay (C.totalAngle retain v) *
        NormedSpace.normalize (D.linkDevelopFrame c (D.germRay c.first)) :=
  D.normalized_terminal_bank_in_frame c (D.linkDevelopFrame c)
    (D.linkDevelopFrame_positive c) covers

end Unfoldings.FacewiseDevelopment
