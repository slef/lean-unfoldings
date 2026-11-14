module

public import Unfoldings.Geometry.MeshProgress
public import Unfoldings.Geometry.OppositeRayAngles

/-! Local line containment of a genuine segment determines its entire direction. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One arbitrarily short positive segment point suffices to recover the direction line. -/
theorem exists_smul_of_locally_in_line (base ray direction : E) (curve : Set E)
    (segment : ∀ t ∈ Set.Icc (0 : ℝ) 1, base + t • ray ∈ curve)
    (locally : ∀ᶠ x in 𝓝 base, x ∈ curve → ∃ a : ℝ, x = base + a • direction) :
    ∃ a : ℝ, ray = a • direction := by
  have continuous : Continuous (fun t : ℝ => base + t • ray) := by fun_prop
  have tends : Tendsto (fun t : ℝ => base + t • ray) (𝓝 0) (𝓝 base) := by
    simpa only [zero_smul, add_zero] using continuous.continuousAt.tendsto (x := 0)
  have near := (tends.eventually locally).and (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨δ, dp, bound⟩ := Metric.eventually_nhds_iff.mp near
  let t := δ / 2
  have tp : 0 < t := half_pos dp
  have at_t := bound (show dist t 0 < δ by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos tp]
    dsimp [t]
    linarith)
  obtain ⟨a, equal⟩ := at_t.1 (segment t ⟨tp.le, at_t.2.le⟩)
  have scaled : t • ray = a • direction := add_left_cancel equal
  refine ⟨t⁻¹ * a, ?_⟩
  have divided := congrArg (fun z : E => t⁻¹ • z) scaled
  simpa only [smul_smul, inv_mul_cancel₀ tp.ne', one_smul] using divided

end Unfoldings
