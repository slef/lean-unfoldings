module

public import Unfoldings.Polyhedron.ComplementaryLinkAngles

/-! Actual convex vertex fan exterior turns contract the genuine spatial bend. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam} {v : C.Vertex retain} {n : ℕ}
  (c : (C.linkSystem retain v).Chain n)

/-- No covering hypothesis is needed for the endpoint bound of a partial original corner fan. -/
theorem link_endpoint_angle_le_corner_sum :
    InnerProductGeometry.angle (F.germDirection c.first.val)
      (F.germDirection (C.linkTurn retain v c.last).val) ≤
      ∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2 := by
  have first : F.intervalLinkRay c 0 = F.germDirection c.first.val := by
    change F.intervalLinkRay c (0 : Fin (n + 1)).castSucc = _
    rw [F.intervalLinkRay_castSucc]
    rfl
  have estimate := angle_endpoint_le_sum (F.intervalLinkRay c)
    (by rw [first]; exact F.germDirection_ne_zero _)
  rw [first, F.intervalLinkRay_last] at estimate
  calc
    _ ≤ _ := estimate
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.intervalLinkRay_castSucc, F.intervalLinkRay_succ]
      exact F.germDirection_angle (c.point i).val

/-- Either one-sided actual fan satisfies the same bound, including reflex fan angles. -/
theorem abs_link_exterior_turn_le_spatial_bend (internal : ¬ C.IsBoundaryVertex retain v)
    (convex : C.totalAngle retain v ≤ 2 * Real.pi) :
    |Real.pi - ∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2| ≤
      InnerProductGeometry.angle (-F.germDirection c.first.val)
        (F.germDirection (C.linkTurn retain v c.last).val) := by
  have first := F.link_endpoint_angle_le_corner_sum c
  have other := F.link_endpoint_angle_le_complement c internal
  rw [InnerProductGeometry.angle_neg_left, abs_le]
  constructor <;> linarith

end Unfoldings.SpatialFolding
