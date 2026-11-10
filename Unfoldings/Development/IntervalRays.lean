module

public import Unfoldings.Development.GermCones
public import Unfoldings.Complex.LinkSteps
public import Unfoldings.Cone.LinkAngles
public import Unfoldings.Geometry.IntervalConeOrientation

/-! Actual developed interval-link rays, without a global nonoverlap assumption. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {v : C.Vertex retain} {n : ℕ} (c : (C.linkSystem retain v).Chain n)

def intervalLinkRay : Fin (n + 2) → Plane :=
  Fin.snoc (fun i => D.germRay (c.point i)) (D.germRay (C.linkTurn retain v c.last))

@[simp] theorem intervalLinkRay_castSucc (i : Fin (n + 1)) :
    D.intervalLinkRay c i.castSucc = D.germRay (c.point i) := Fin.snoc_castSucc _ _ _

@[simp] theorem intervalLinkRay_last : D.intervalLinkRay c (Fin.last (n + 1)) =
    D.germRay (C.linkTurn retain v c.last) := Fin.snoc_last _ _

theorem intervalLinkRay_succ (i : Fin (n + 1)) :
    D.intervalLinkRay c i.succ = D.germRay (C.linkTurn retain v (c.point i)) := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · exact D.intervalLinkRay_last c
  · rw [← Fin.castSucc_succ, D.intervalLinkRay_castSucc]
    have equal := congrArg D.germRay (c.next k)
    change D.germRay (C.linkMate retain v (C.linkTurn retain v (c.point k.castSucc))) = _ at equal
    simpa only [D.germRay_mate] using equal.symm

theorem intervalLinkRay_ne_zero (i : Fin (n + 2)) : D.intervalLinkRay c i ≠ 0 := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [D.intervalLinkRay_last]
    exact D.germRay_ne_zero _
  · rw [D.intervalLinkRay_castSucc]
    exact D.germRay_ne_zero _

theorem intervalLinkRay_angle (i : Fin (n + 1)) :
    InnerProductGeometry.angle (D.intervalLinkRay c i.castSucc) (D.intervalLinkRay c i.succ) =
      (C.linkAngularFan retain v c).angle i := by
  rw [D.intervalLinkRay_castSucc, D.intervalLinkRay_succ]
  exact D.germRay_angle (c.point i)

theorem intervalLinkRay_genuine (i : Fin (n + 1)) :
    orient 0 (D.intervalLinkRay c i.castSucc) (D.intervalLinkRay c i.succ) ≠ 0 := by
  rw [D.intervalLinkRay_castSucc, D.intervalLinkRay_succ]
  exact D.germRay_orient_ne_zero (c.point i)

theorem intervalLinkRay_adjacent (k : Fin n) :
    Disjoint
      (strictRayCone (D.intervalLinkRay c k.castSucc.castSucc)
        (D.intervalLinkRay c k.castSucc.succ))
      (strictRayCone (D.intervalLinkRay c k.succ.castSucc) (D.intervalLinkRay c k.succ.succ)) := by
  rw [D.intervalLinkRay_castSucc, D.intervalLinkRay_succ,
    D.intervalLinkRay_castSucc, D.intervalLinkRay_succ]
  exact D.germCones_disjoint_of_crossing _ _ (C.chain_next_crosses retain v c k)

/-- This frame preserves all lengths and angles, and makes every genuine hinge turn positive. -/
theorem exists_positive_link_frame : ∃ L : Plane ≃ₗᵢ[ℝ] ℂ,
    ∀ i : Fin (n + 1),
      0 < (starRingEnd ℂ (L (D.intervalLinkRay c i.castSucc)) *
        L (D.intervalLinkRay c i.succ)).im :=
  exists_positive_interval_frame (D.intervalLinkRay c) (D.intervalLinkRay_genuine c)
    (D.intervalLinkRay_adjacent c)

end Unfoldings.FacewiseDevelopment
