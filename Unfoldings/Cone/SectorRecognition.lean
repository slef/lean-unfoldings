module

public import Unfoldings.Cone.ReentrantSectorBoundary
public import Unfoldings.Geometry.RegularClosedRecognition
public import Unfoldings.Geometry.LocalConeRegularClosed

/-! Recognize an actual sector corner from its original bank rays and one geometric side witness. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings

theorem interior_complementarySector_eq_compl (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : interior (complementarySector width) =
      (closedAngularSector width)ᶜ := by
  apply interior_eq_compl_of_regular_closed_cover
    (isClosed_closedAngularSector width positive small)
    (closure_interior_closedAngularSector width positive small)
  · rw [Set.union_comm]
    exact closedAngularSector_union_complementary width
  · rw [Set.inter_comm]
    exact interior_closedAngularSector_inter_complementary width positive small

theorem isPreconnected_compl_closedAngularSector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : IsPreconnected (closedAngularSector width)ᶜ := by
  rw [← interior_complementarySector_eq_compl width positive small]
  let H := (rotation (Circle.exp width)).toHomeomorph
  change IsPreconnected (interior (H '' closedAngularSector (2 * Real.pi - width)))
  rw [← H.image_interior]
  exact (isPreconnected_interior_closedAngularSector (2 * Real.pi - width) (sub_pos.mpr small)
    (by linarith)).image H H.continuous.continuousOn

/-- Actual bank rays and one interior orientation witness determine the entire corner sector. -/
theorem eq_closedAngularSector_of_frontier_and_witness (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) {cone : Set ℂ} (regular : closure (interior cone) = cone)
    (boundary : frontier cone = Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
      Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width))
    (witness : (interior (closedAngularSector width) ∩ interior cone).Nonempty) :
    cone = closedAngularSector width := by
  apply eq_of_regular_closed_frontier_eq
    (closure_interior_closedAngularSector width positive small) regular
    (isPreconnected_interior_closedAngularSector width positive small)
    (isPreconnected_compl_closedAngularSector width positive small) _ _ witness
  · refine ⟨0, ?_⟩
    rw [frontier_closedAngularSector width positive small]
    exact Or.inl ⟨0, rfl⟩
  · rwa [frontier_closedAngularSector width positive small]

/-- A geometric sample arbitrarily near the actual corner replaces a supplied aperture model.
The original region and bank frontier force the whole local cone to be the selected sector. -/
theorem local_cone_eq_sector_of_frequent_witness {s cone : Set ℂ} (x : ℂ)
    (width : ℝ) (positive : 0 < width) (small : width < 2 * Real.pi)
    (regular : closure (interior s) = s)
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (near : ∀ᶠ z in 𝓝 x, z ∈ s ↔ z - x ∈ cone)
    (boundary : frontier cone = Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
      Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width))
    (samples : ∃ᶠ z in 𝓝 x,
      z ∈ interior s ∧ z - x ∈ interior (closedAngularSector width)) :
    cone = closedAngularSector width := by
  apply eq_closedAngularSector_of_frontier_and_witness width positive small
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
