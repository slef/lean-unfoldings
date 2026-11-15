module

public import Unfoldings.Geometry.SegmentInteriorDirections

/-! Strict interior points of an entire geometric ray have its full original direction line. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a positive ray parameter the exact unbounded ray locally fills its direction line. -/
theorem eventually_mem_ray_iff_direction_line_normed (a d : E) (nonzero : d ≠ 0)
    (t : ℝ) (positive : 0 < t) :
    ∀ᶠ z in 𝓝 (a + t • d), z - a ∈ nonnegativeRay d ↔
      z - (a + t • d) ∈ Set.range (fun s : ℝ => s • d) := by
  have dpos : 0 < ‖d‖ := norm_pos_iff.mpr nonzero
  filter_upwards [Metric.ball_mem_nhds (a + t • d) (mul_pos positive dpos)] with z near
  constructor
  · rintro ⟨s, _nonnegative, equal⟩
    refine ⟨s - t, ?_⟩
    dsimp only
    rw [sub_smul]
    rw [show z - (a + t • d) = (z - a) - t • d by abel, equal]
  · rintro ⟨s, equal⟩
    dsimp only at equal
    have distance : dist z (a + t • d) = |s| * ‖d‖ := by
      rw [dist_eq_norm, ← equal, norm_smul, Real.norm_eq_abs]
    have small : |s| < t := by
      have close := Metric.mem_ball.mp near
      rw [distance] at close
      exact (mul_lt_mul_iff_of_pos_right dpos).mp close
    refine ⟨t + s, by linarith [(abs_lt.mp small).1], ?_⟩
    rw [add_smul, equal]
    abel

end Unfoldings
