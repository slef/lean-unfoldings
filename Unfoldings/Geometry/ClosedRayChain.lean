module

public import Unfoldings.Geometry.HalfplaneFan

/-! The unused angular length of a closed ray chain controls its complementary endpoint angle. -/

@[expose] public section

namespace Unfoldings

/-- Follow the complementary part of the actual closed chain, rather than a principal angle lift. -/
theorem angle_le_remaining_closed_ray_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (ray : Fin (n + 2) → E) (genuine : ray 0 ≠ 0)
    (closed : ray (Fin.last (n + 1)) = ray 0) (j : Fin (n + 2)) :
    InnerProductGeometry.angle (ray j) (ray 0) ≤
      (∑ i : Fin (n + 1), InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)) -
        Fin.partialSum (fun i => InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)) j := by
  let turn (i : Fin (n + 1)) := InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)
  have total : Fin.partialSum turn (Fin.last (n + 1)) = ∑ i, turn i := by
    change ((List.ofFn turn).take (n + 1)).sum = ∑ i, turn i
    rw [List.take_of_length_le (by simp), List.sum_ofFn]
  change InnerProductGeometry.angle (ray j) (ray 0) ≤
    (∑ i, turn i) - Fin.partialSum turn j
  refine Fin.reverseInduction ?_ (fun i remaining => ?_) j
  · rw [closed, InnerProductGeometry.angle_self genuine, total, sub_self]
  · have triangle := InnerProductGeometry.angle_le_angle_add_angle
      (ray i.castSucc) (ray i.succ) (ray 0)
    rw [Fin.partialSum_succ] at remaining
    change _ ≤ (∑ i, turn i) - (Fin.partialSum turn i.castSucc + turn i) at remaining
    change InnerProductGeometry.angle (ray i.castSucc) (ray 0) ≤
      turn i + InnerProductGeometry.angle (ray i.succ) (ray 0) at triangle
    linarith

end Unfoldings
