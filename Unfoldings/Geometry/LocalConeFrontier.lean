module

public import Unfoldings.Geometry.HomogeneousGerm
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Algebra.ConstMulAction

/-! The frontier of an exact local cone is determined by the original physical boundary germ. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Local equality of geometric regions also identifies their frontiers on a neighborhood. -/
theorem eventually_mem_frontier_iff_of_local_eq {s t : Set E} {x : E}
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z ∈ t) :
    ∀ᶠ z in 𝓝 x, z ∈ frontier s ↔ z ∈ frontier t := by
  filter_upwards [near.eventually_nhds] with z at_z
  have closure_iff : z ∈ closure s ↔ z ∈ closure t := by
    simp only [mem_closure_iff_frequently]
    exact frequently_congr at_z
  have interior_iff : z ∈ interior s ↔ z ∈ interior t := at_z.set_eq.mem_interior_iff
  simp only [frontier, Set.mem_sdiff, closure_iff, interior_iff]

/-- Every positive scaling preserves the frontier of an exact homogeneous region. -/
theorem mem_frontier_smul_iff_of_homogeneous {cone : Set E}
    (radial : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (v : E) {r : ℝ} (positive : 0 < r) : r • v ∈ frontier cone ↔ v ∈ frontier cone := by
  let H : E ≃ₜ E := Homeomorph.smulOfNeZero r positive.ne'
  have same : H ⁻¹' cone = cone := Set.ext (fun w => radial w r positive)
  have boundary : H ⁻¹' frontier cone = frontier cone := by rw [H.preimage_frontier, same]
  exact Set.ext_iff.mp boundary v

omit [NormedSpace ℝ E] in
/-- The actual region's frontier agrees locally with the translated frontier of its cone model. -/
theorem eventually_mem_frontier_iff_cone {s cone : Set E} (x : E)
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z - x ∈ cone) :
    ∀ᶠ z in 𝓝 x, z ∈ frontier s ↔ z - x ∈ frontier cone := by
  let H := Homeomorph.addRight (-x)
  have compare : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z ∈ H ⁻¹' cone := by
    filter_upwards [near] with z hz
    change z ∈ s ↔ z + -x ∈ cone
    simpa only [sub_eq_add_neg] using hz
  have boundary := eventually_mem_frontier_iff_of_local_eq compare
  filter_upwards [boundary] with z hz
  rw [← H.preimage_frontier] at hz
  change z ∈ frontier s ↔ z + -x ∈ frontier cone at hz
  simpa only [sub_eq_add_neg] using hz

/-- An exact cone model's boundary is forced by the actual original incident bank directions. -/
theorem frontier_local_cone_eq {s cone banks : Set E} (x : E)
    (radial : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (bank_radial : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ banks ↔ v ∈ banks))
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z - x ∈ cone)
    (boundary : ∀ᶠ z in 𝓝 x, z ∈ frontier s ↔ z - x ∈ banks) : frontier cone = banks :=
  eq_of_local_homogeneous_models x
    (fun v _r positive => mem_frontier_smul_iff_of_homogeneous radial v positive) bank_radial
    (eventually_mem_frontier_iff_cone x near) boundary

end Unfoldings
