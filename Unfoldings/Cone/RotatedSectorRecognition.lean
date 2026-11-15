module

public import Unfoldings.Cone.SectorRecognition

/-! The sector recognition theorem retains the actual oriented original edge frame. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings

/-- The original nonnegative rays in the real heading interval constitute the entire sector. -/
theorem closedAngularSector_eq_iUnion_rays (width : ℝ) :
    closedAngularSector width = ⋃ θ ∈ Set.Icc 0 width, nonnegativeRay (polarRay θ) := by
  ext z
  constructor
  · rintro ⟨r, θ, bounds, equal⟩
    exact Set.mem_iUnion₂.mpr ⟨θ, bounds, r, r.coe_nonneg,
      by simpa only [Complex.real_smul] using equal⟩
  · intro member
    obtain ⟨θ, bounds, r, nonnegative, equal⟩ := Set.mem_iUnion₂.mp member
    refine ⟨⟨r, nonnegative⟩, θ, bounds, ?_⟩
    change z = (r : ℂ) * polarRay θ
    simpa only [Complex.real_smul] using equal

theorem mem_closedAngularSector_smul_iff (width : ℝ) (v : ℂ) {r : ℝ} (positive : 0 < r) :
    r • v ∈ closedAngularSector width ↔ v ∈ closedAngularSector width := by
  simp only [closedAngularSector_eq_iUnion_rays, Set.mem_iUnion,
    mem_nonnegativeRay_smul_iff _ _ positive]

theorem mem_rotatedAngularSector_smul_iff (frame : ℂ ≃ₗᵢ[ℝ] ℂ) (width : ℝ) (v : ℂ)
    {r : ℝ} (positive : 0 < r) :
    r • v ∈ frame '' closedAngularSector width ↔ v ∈ frame '' closedAngularSector width := by
  have same : frame '' closedAngularSector width = frame.symm ⁻¹' closedAngularSector width := by
    ext z
    constructor
    · rintro ⟨w, member, rfl⟩
      simpa only [Set.mem_preimage, LinearIsometryEquiv.symm_apply_apply] using member
    · intro member
      exact ⟨frame.symm z, member, frame.apply_symm_apply z⟩
  rw [same]
  simp only [Set.mem_preimage, map_smul, mem_closedAngularSector_smul_iff _ _ positive]

/-- The original rigid edge frame is kept in the recognized geometric corner region. -/
theorem eq_rotatedSector_of_frontier_and_witness (frame : ℂ ≃ₗᵢ[ℝ] ℂ) (width : ℝ)
    (positive : 0 < width) (small : width < 2 * Real.pi) {cone : Set ℂ}
    (regular : closure (interior cone) = cone)
    (boundary : frontier cone = frame '' (Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
      Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width)))
    (witness : (interior (frame '' closedAngularSector width) ∩ interior cone).Nonempty) :
    cone = frame '' closedAngularSector width := by
  let H := frame.toHomeomorph
  have regular_image : closure (interior (H '' closedAngularSector width)) =
      H '' closedAngularSector width := by
    rw [← H.image_interior, ← H.image_closure,
      closure_interior_closedAngularSector width positive small]
  have inside_connected : IsPreconnected (interior (H '' closedAngularSector width)) := by
    rw [← H.image_interior]
    exact (isPreconnected_interior_closedAngularSector width positive small).image
      H H.continuous.continuousOn
  have outside_connected : IsPreconnected (H '' closedAngularSector width)ᶜ := by
    rw [← H.image_compl]
    exact (isPreconnected_compl_closedAngularSector width positive small).image
      H H.continuous.continuousOn
  have boundary_image : frontier (H '' closedAngularSector width) =
      H '' (Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
        Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width)) := by
    rw [← H.image_frontier, frontier_closedAngularSector width positive small]
  apply eq_of_regular_closed_frontier_eq regular_image regular inside_connected outside_connected
    _ _ witness
  · refine ⟨H 0, ?_⟩
    rw [boundary_image]
    exact ⟨0, Or.inl ⟨0, rfl⟩, rfl⟩
  · rw [boundary_image]
    exact boundary

/-- Arbitrarily near physical orientation samples determine the full rotated corner model. -/
theorem local_cone_eq_rotated_sector_of_frequent_witness {s cone : Set ℂ} (x : ℂ)
    (frame : ℂ ≃ₗᵢ[ℝ] ℂ) (width : ℝ) (positive : 0 < width) (small : width < 2 * Real.pi)
    (regular : closure (interior s) = s)
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z - x ∈ cone)
    (boundary : frontier cone = frame '' (Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
      Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width)))
    (samples : ∃ᶠ z in 𝓝 x,
      z ∈ interior s ∧ z - x ∈ interior (frame '' closedAngularSector width)) :
    cone = frame '' closedAngularSector width := by
  apply eq_rotatedSector_of_frontier_and_witness frame width positive small
    (closure_interior_local_cone_eq x regular radial near) boundary
  let shift := Homeomorph.addRight (-x)
  have compare : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z ∈ shift ⁻¹' cone := by
    filter_upwards [near] with z hz
    change z ∈ s ↔ z + -x ∈ cone
    simpa only [sub_eq_add_neg] using hz
  have int_near := eventually_mem_interior_iff_of_local_eq compare
  obtain ⟨z, geometry, local_match⟩ := (samples.and_eventually int_near).exists
  have member := local_match.mp geometry.1
  rw [← shift.preimage_interior] at member
  change z + -x ∈ interior cone at member
  refine ⟨z - x, geometry.2, ?_⟩
  simpa only [sub_eq_add_neg] using member

end Unfoldings
