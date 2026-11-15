module

public import Unfoldings.Geometry.LocalLineSegment
public import Unfoldings.Geometry.SegmentEndpointGerm

/-! Local containment in two incident rays determines a genuine bank direction. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine segment locally contained in two nonnegative rays follows one of their
positive directions. No angle or noncollinearity hypothesis is required. -/
theorem exists_pos_smul_of_locally_in_two_rays (base ray first last : E) (curve : Set E)
    (nonzero : ray ≠ 0)
    (segment : ∀ t ∈ Set.Icc (0 : ℝ) 1, base + t • ray ∈ curve)
    (locally : ∀ᶠ x in 𝓝 base, x ∈ curve →
      x - base ∈ nonnegativeRay first ∪ nonnegativeRay last) :
    (∃ a : ℝ, 0 < a ∧ ray = a • first) ∨ (∃ b : ℝ, 0 < b ∧ ray = b • last) := by
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
  have member := at_t.1 (segment t ⟨tp.le, at_t.2.le⟩)
  simp only [add_sub_cancel_left, Set.mem_union] at member
  rcases member with left | right
  · left
    obtain ⟨a, nonnegative, equal⟩ := (mem_nonnegativeRay_smul_iff first ray tp).mp left
    exact ⟨a, lt_of_le_of_ne nonnegative (fun zero => nonzero (by
      rw [← zero, zero_smul] at equal
      exact equal)), equal⟩
  · right
    obtain ⟨b, nonnegative, equal⟩ := (mem_nonnegativeRay_smul_iff last ray tp).mp right
    exact ⟨b, lt_of_le_of_ne nonnegative (fun zero => nonzero (by
      rw [← zero, zero_smul] at equal
      exact equal)), equal⟩

end Unfoldings
