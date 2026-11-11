module

public import Unfoldings.Cap.RoofClips
public import Mathlib.Topology.Order.Compact

/-! Lower roof clips contain any prescribed compact region strictly inside their footprints. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem exists_clip_interior_contains_compact {S : Set Plane} (compact : IsCompact S) :
    ∃ Z : ℝ, Z < 0 ∧ S ⊆ interior (K.clipFootprint Z) := by
  obtain ⟨b, bound⟩ := compact.bddBelow_image K.continuous_roofHeight.continuousOn
  refine ⟨min b 0 - 1, by linarith [min_le_right b 0], ?_⟩
  intro p member
  apply K.strict_level_mem_clip_interior
  have lower : b ≤ K.roofHeight p := bound ⟨p, member, rfl⟩
  linarith [min_le_left b 0]

theorem exists_clip_interior_contains_closedBall (q : Plane) (radius : ℝ) :
    ∃ Z : ℝ, Z < 0 ∧ Metric.closedBall q radius ⊆ interior (K.clipFootprint Z) :=
  K.exists_clip_interior_contains_compact (isCompact_closedBall q radius)

/-- All actual skirt tips are uniformly beyond a prescribed radius, independent of meshing. -/
theorem clip_frontier_distance_gt {Z : ℝ} {q p : Plane} {radius : ℝ}
    (inside : Metric.closedBall q radius ⊆ interior (K.clipFootprint Z))
    (boundary : p ∈ frontier (K.clipFootprint Z)) : radius < dist q p := by
  by_contra close
  apply boundary.2
  apply inside
  rw [Metric.mem_closedBall, dist_comm]
  exact le_of_not_gt close

/-- Choose a slab covering the entire original cap in every orthogonal sector frame,
then choose the clip strictly beyond it. Both choices precede auxiliary triangulation. -/
theorem exists_source_sweep_clip (q : Plane) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∃ Z : ℝ, Z < 0 ∧
      Metric.closedBall q cutoff ⊆ interior (K.clipFootprint Z) ∧
        ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) p, p ∈ K.footprint →
          (frame (p - q)).re + (frame (p - q)).im < cutoff := by
  obtain ⟨r, positive, cover⟩ := K.compact_footprint.isBounded.subset_ball_lt 0 q
  obtain ⟨Z, lower, inside⟩ := K.exists_clip_interior_contains_closedBall q (2 * r)
  refine ⟨2 * r, by positivity, Z, lower, inside, ?_⟩
  intro frame p member
  have distance : dist q p < r := by
    have close := cover member
    rwa [Metric.mem_ball, dist_comm] at close
  calc
    _ ≤ ‖frame (p - q)‖ + ‖frame (p - q)‖ :=
      add_le_add (Complex.re_le_norm _) (Complex.im_le_norm _)
    _ = 2 * dist q p := by rw [frame.norm_map, dist_eq_norm' q p]; ring
    _ < 2 * r := mul_lt_mul_of_pos_left distance (by norm_num)

end Unfoldings.ConvexCap
