module

public import Unfoldings.Geometry.LocalConeFrontier

/-! Exact homogeneous models of regular closed polygonal regions are themselves regular closed. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem eventually_mem_closure_iff_of_local_eq {s t : Set E} {x : E}
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z ∈ t) :
    ∀ᶠ z in 𝓝 x, z ∈ closure s ↔ z ∈ closure t := by
  filter_upwards [near.eventually_nhds] with z at_z
  simp only [mem_closure_iff_frequently]
  exact frequently_congr at_z

omit [NormedSpace ℝ E] in
theorem eventually_mem_interior_iff_of_local_eq {s t : Set E} {x : E}
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z ∈ t) :
    ∀ᶠ z in 𝓝 x, z ∈ interior s ↔ z ∈ interior t := by
  filter_upwards [near.eventually_nhds] with z at_z
  exact at_z.set_eq.mem_interior_iff

/-- Regular closedness follows from the original physical region and the exact local model. -/
theorem closure_interior_local_cone_eq {s cone : Set E} (x : E)
    (regular : closure (interior s) = s)
    (radial : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z - x ∈ cone) : closure (interior cone) = cone := by
  let shift := Homeomorph.addRight (-x)
  have compare : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z ∈ shift ⁻¹' cone := by
    filter_upwards [near] with z hz
    change z ∈ s ↔ z + -x ∈ cone
    simpa only [sub_eq_add_neg] using hz
  have interior_near := eventually_mem_interior_iff_of_local_eq compare
  have closure_near := eventually_mem_closure_iff_of_local_eq interior_near
  rw [regular, ← shift.preimage_interior, ← shift.preimage_closure] at closure_near
  have first : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z - x ∈ closure (interior cone) := by
    filter_upwards [closure_near] with z hz
    change z ∈ s ↔ z + -x ∈ closure (interior cone) at hz
    simpa only [sub_eq_add_neg] using hz
  apply eq_of_local_homogeneous_models x _ radial first near
  intro v r positive
  let H : E ≃ₜ E := Homeomorph.smulOfNeZero r positive.ne'
  have same : H ⁻¹' cone = cone := Set.ext (fun w => radial w r positive)
  have regular_same : H ⁻¹' closure (interior cone) = closure (interior cone) := by
    rw [H.preimage_closure, H.preimage_interior, same]
  exact Set.ext_iff.mp regular_same v

end Unfoldings
