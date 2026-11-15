module

public import Unfoldings.Geometry.RadialLocality

/-! Uniqueness of exact positively homogeneous local direction models. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive homogeneous direction model is determined by its arbitrarily small germ. -/
theorem eq_of_homogeneous_eventually_iff {s t : Set E}
    (radial_s : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ s ↔ v ∈ s))
    (radial_t : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ t ↔ v ∈ t))
    (near : ∀ᶠ v in 𝓝 (0 : E), v ∈ s ↔ v ∈ t) : s = t := by
  obtain ⟨r, positive, included⟩ := Metric.mem_nhds_iff.mp near
  apply eq_of_radial_local_eq (0 : E) _ _ positive
    (fun z hz => included (Metric.mem_ball.mpr hz))
  · intro z r positive
    simpa only [AffineMap.lineMap_apply_module', sub_zero, add_zero] using radial_s z r positive
  · intro z r positive
    simpa only [AffineMap.lineMap_apply_module', sub_zero, add_zero] using radial_t z r positive

/-- Two exact conical models of the same physical set at the same point agree globally. -/
theorem eq_of_local_homogeneous_models {region s t : Set E} (x : E)
    (radial_s : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ s ↔ v ∈ s))
    (radial_t : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ t ↔ v ∈ t))
    (first : ∀ᶠ z in 𝓝 x, z ∈ region ↔ z - x ∈ s)
    (last : ∀ᶠ z in 𝓝 x, z ∈ region ↔ z - x ∈ t) : s = t := by
  apply eq_of_homogeneous_eventually_iff radial_s radial_t
  have translated : Tendsto (fun v : E => x + v) (𝓝 0) (𝓝 x) := by
    have continuous : Continuous (fun v : E => x + v) := continuous_const.add continuous_id
    simpa only [add_zero] using continuous.tendsto (0 : E)
  filter_upwards [translated.eventually first, translated.eventually last] with v first last
  simp only [add_sub_cancel_left] at first last
  exact first.symm.trans last

end Unfoldings
