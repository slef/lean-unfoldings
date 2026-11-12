module

public import Unfoldings.Cap.NonadjacentSectorSeparation
public import Unfoldings.Cap.RadialStripPointOrder

/-! Nonadjacent actual closed strip images have no contact away from the developed source. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i j : Fin 5} {S T : MonotoneStrip} {ε cutoff : ℝ}

/-- This includes exceptional vertex and pinch radii: only positivity of the radius is needed. -/
theorem nonadjacent_sector_closed_circle_images_disjoint
    (data : N.RadialStripTraceData positive small D calibration (fiveSectorCycle i) S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration (fiveSectorCycle j) T ε cutoff)
    (different : i ≠ j) (not_next : finRotate 5 i ≠ j) (not_previous : finRotate 5 j ≠ i)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius) :
    Disjoint (data.outputFrame.symm '' (data.value '' closure (S.openSlab 0 cutoff) ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' closure (T.openSlab 0 cutoff) ∩
        {z | ‖z - other.center‖ = radius})) := by
  apply Set.disjoint_left.mpr
  intro p first last
  obtain ⟨_, ⟨⟨z, member, rfl⟩, size⟩, at_first⟩ := first
  obtain ⟨_, ⟨⟨w, other_member, rfl⟩, other_size⟩, at_last⟩ := last
  have first_subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_subset : T.openSlab 0 cutoff ⊆ other.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_closed := closure_mono first_subset member
  have last_closed := closure_mono last_subset other_member
  have first_height := data.closed_height_pos_of_norm first_closed
    (by rw [size]; exact radius_positive)
  have last_height := other.closed_height_pos_of_norm last_closed
    (by rw [other_size]; exact radius_positive)
  have first_quadrant := data.strict_quadrant_of_closed_margin first_error first_margin
    first_closed first_height
  have last_quadrant := other.strict_quadrant_of_closed_margin last_error last_margin
    last_closed last_height
  have first_value := data.complex_frame_centered_value z
  have last_value := other.complex_frame_centered_value w
  rw [at_first] at first_value
  rw [at_last] at last_value
  rw [← first_value] at first_quadrant
  rw [← last_value] at last_quadrant
  exact Set.disjoint_left.mp
    (fiveSectorComplexFrame_quadrants_disjoint_nonadjacent positive small i j
      different not_next not_previous) first_quadrant last_quadrant

/-- No finite exceptional-radius set is needed for this closed-image conclusion. -/
theorem nonadjacent_sector_closed_images_inter_subset_source
    (data : N.RadialStripTraceData positive small D calibration (fiveSectorCycle i) S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration (fiveSectorCycle j) T ε cutoff)
    (different : i ≠ j) (not_next : finRotate 5 i ≠ j) (not_previous : finRotate 5 j ≠ i)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    : data.outputFrame.symm '' (data.value '' closure (S.openSlab 0 cutoff)) ∩
        other.outputFrame.symm '' (other.value '' closure (T.openSlab 0 cutoff)) ⊆
      {D.projectedMap K source} := by
  rintro p ⟨⟨_, ⟨z, first, rfl⟩, first_value⟩, ⟨_, ⟨w, last, rfl⟩, last_value⟩⟩
  apply Set.mem_singleton_iff.mpr
  by_contra different_point
  have positive_radius : 0 < ‖p - D.projectedMap K source‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr different_point)
  have first_size : ‖data.value z - data.center‖ = ‖p - D.projectedMap K source‖ := by
    rw [← data.outputFrame_symm_source_distance, first_value]
  have last_size : ‖other.value w - other.center‖ = ‖p - D.projectedMap K source‖ := by
    rw [← other.outputFrame_symm_source_distance, last_value]
  exact Set.disjoint_left.mp
    (nonadjacent_sector_closed_circle_images_disjoint data other different not_next not_previous
      first_error last_error first_margin last_margin positive_radius)
    ⟨data.value z, ⟨⟨z, first, rfl⟩, first_size⟩, first_value⟩
    ⟨other.value w, ⟨⟨w, last, rfl⟩, last_size⟩, last_value⟩

end Unfoldings.ConvexCap.RadialCutForest
