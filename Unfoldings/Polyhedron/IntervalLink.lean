module

public import Unfoldings.Polyhedron.AngularLink
public import Unfoldings.Geometry.HalfplaneFan

/-! An actual interval link as a sequence of genuine spatial edge directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam} {v : C.Vertex retain} {n : ℕ}
  (c : (C.linkSystem retain v).Chain n)

/-- The sequence includes the actual far terminal bank direction. -/
def intervalLinkRay : Fin (n + 2) → Space :=
  Fin.snoc (fun i => F.germDirection (c.point i).val)
    (F.germDirection (C.linkTurn retain v c.last).val)

@[simp] theorem intervalLinkRay_castSucc (i : Fin (n + 1)) :
    F.intervalLinkRay c i.castSucc = F.germDirection (c.point i).val := Fin.snoc_castSucc _ _ _

@[simp] theorem intervalLinkRay_last : F.intervalLinkRay c (Fin.last (n + 1)) =
    F.germDirection (C.linkTurn retain v c.last).val := Fin.snoc_last _ _

theorem intervalLinkRay_succ (i : Fin (n + 1)) :
    F.intervalLinkRay c i.succ = F.germDirection (C.linkTurn retain v (c.point i)).val := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · exact F.intervalLinkRay_last c
  · rw [← Fin.castSucc_succ, F.intervalLinkRay_castSucc]
    have equal := congrArg (fun p : C.LinkGerm retain v => F.germDirection p.val) (c.next k)
    change F.germDirection (C.mateGerm retain
      (C.linkTurn retain v (c.point k.castSucc)).val) = _ at equal
    exact ((F.germDirection_mate retain _).symm.trans equal).symm

theorem sum_intervalLinkRay_angles (covers : ∀ p, c.Visited p) :
    (∑ i : Fin (n + 1), InnerProductGeometry.angle (F.intervalLinkRay c i.castSucc)
      (F.intervalLinkRay c i.succ)) = C.totalAngle retain v := by
  calc
    _ = ∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.intervalLinkRay_castSucc, F.intervalLinkRay_succ]
      exact F.germDirection_angle (c.point i).val
    _ = C.totalAngle retain v := C.sum_linkCornerAngle retain v c covers

/-- The actual terminal bank angle is at most the full intrinsic angle at the vertex. -/
theorem intervalLink_endpoint_angle_le (covers : ∀ p, c.Visited p) :
    InnerProductGeometry.angle (F.germDirection c.first.val)
      (F.germDirection (C.linkTurn retain v c.last).val) ≤ C.totalAngle retain v := by
  rw [← F.sum_intervalLinkRay_angles c covers]
  have first : F.intervalLinkRay c 0 = F.germDirection c.first.val := by
    change F.intervalLinkRay c (0 : Fin (n + 1)).castSucc = _
    rw [F.intervalLinkRay_castSucc]
    rfl
  have lower := angle_endpoint_le_sum (F.intervalLinkRay c)
    (by rw [first]; exact F.germDirection_ne_zero _)
  rw [first, F.intervalLinkRay_last] at lower
  exact lower

end Unfoldings.SpatialFolding
