module

public import Unfoldings.Cap.RadialStripPhysicalMap
public import Unfoldings.Cap.SectorPositionMargins
public import Unfoldings.Geometry.FiveSectorFrameRotation
public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Mathlib.Data.Fintype.Lattice

/-! Nonadjacent sectors' actual developed strip images are disjoint. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i j : Fin 5} {S T : MonotoneStrip} {ε cutoff : ℝ}

theorem RadialStripTraceData.complex_frame_centered_value
    (data : N.RadialStripTraceData positive small D calibration (fiveSectorCycle i) S ε cutoff)
    (z : ℂ) :
    fiveSectorComplexFrame positive small i
        (calibration (data.outputFrame.symm (data.value z) - D.projectedMap K source)) =
      data.value z - data.center := by
  change data.outputFrame (data.outputFrame.symm (data.value z) - D.projectedMap K source) = _
  rw [map_sub, LinearIsometryEquiv.apply_symm_apply, ← data.center_eq_outputFrame]

/-- The required quadrant margins are physical coordinate bounds, independently
proved for every cell of the actual enclosing-strip subdivision. No developed
separation or endpoint order is supplied. -/
theorem nonadjacent_sector_strip_images_disjoint
    (data : N.RadialStripTraceData positive small D calibration (fiveSectorCycle i) S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration (fiveSectorCycle j) T ε cutoff)
    (different : i ≠ j) (not_next : finRotate 5 i ≠ j) (not_previous : finRotate 5 j ≠ i)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff)) := by
  apply Set.disjoint_left.mpr
  intro p first last
  obtain ⟨_, ⟨z, member, rfl⟩, at_first⟩ := first
  obtain ⟨_, ⟨w, other_member, rfl⟩, at_last⟩ := last
  have first_quadrant := data.strict_quadrant_of_margin first_error first_margin member
  have last_quadrant := other.strict_quadrant_of_margin last_error last_margin other_member
  have first_value := data.complex_frame_centered_value z
  have last_value := other.complex_frame_centered_value w
  rw [at_first] at first_value
  rw [at_last] at last_value
  rw [← first_value] at first_quadrant
  rw [← last_value] at last_quadrant
  exact Set.disjoint_left.mp
    (fiveSectorComplexFrame_quadrants_disjoint_nonadjacent positive small i j
      different not_next not_previous) first_quadrant last_quadrant

theorem nonadjacent_sector_circle_images_disjoint
    (data : N.RadialStripTraceData positive small D calibration (fiveSectorCycle i) S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration (fiveSectorCycle j) T ε cutoff)
    (different : i ≠ j) (not_next : finRotate 5 i ≠ j) (not_previous : finRotate 5 j ≠ i)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im) (radius : ℝ) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) :=
  (nonadjacent_sector_strip_images_disjoint data other different not_next not_previous
    first_error last_error first_margin last_margin).mono
      (Set.image_mono Set.inter_subset_left) (Set.image_mono Set.inter_subset_left)

/-- The admissible trace error is positive and chosen before any mesh,
development, or subdivision. All physical cell margins are derived here. -/
theorem exists_uniform_nonadjacent_sector_separation (t : ℝ)
    (positive : 0 < t) (small : t < 1) :
    ∃ η > 0, ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
      {K : ConvexCap C} {source : Plane} {cuts : Set Plane}
      (N : K.RadialCutForest source cuts) (D : FacewiseDevelopment C N.retain)
      (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {ε cutoff : ℝ}, ε ≤ η →
      ∀ (P : ∀ k : Fin 5,
          (fiveSectorFrame t positive small (fiveSectorCycle k)).enclosingStrip.Subdivision)
        (traces : ∀ k, ∀ cell : {S : MonotoneStrip // S ∈ (P k).cells},
          N.RadialStripTraceData positive small D calibration (fiveSectorCycle k)
            cell.val ε cutoff)
        (i j : Fin 5) (first : {S : MonotoneStrip // S ∈ (P i).cells})
        (last : {S : MonotoneStrip // S ∈ (P j).cells}),
        i ≠ j → finRotate 5 i ≠ j → finRotate 5 j ≠ i →
        Disjoint ((traces i first).outputFrame.symm ''
          ((traces i first).value '' first.val.openSlab 0 cutoff))
          ((traces j last).outputFrame.symm ''
            ((traces j last).value '' last.val.openSlab 0 cutoff)) := by
  classical
  have margins := fun k : Fin 5 =>
    (fiveSectorFrame t positive small (fiveSectorCycle k)).exists_enclosingStrip_coordinate_margin
  choose μ positive_margin margin using margins
  obtain ⟨k, minimal⟩ := Finite.exists_min μ
  refine ⟨μ k / 2, div_pos (positive_margin k) (by norm_num), ?_⟩
  intro Face _ C K source cuts N D calibration ε cutoff error P traces i j first last
    different not_next not_previous
  have close (a : Fin 5) : ε < μ a :=
    error.trans_lt ((half_lt_self (positive_margin k)).trans_le (minimal a))
  have cell_margin (a : Fin 5) (cell : {S : MonotoneStrip // S ∈ (P a).cells})
      (z : ℂ) (member : z ∈ cell.val.carrier) (forward : 0 ≤ z.re + z.im) :
      μ a * (z.re + z.im) ≤ z.re ∧ μ a * (z.re + z.im) ≤ z.im := by
    have bounds := (P a).cell_bounds cell.property (z.re + z.im)
    exact margin a z ⟨bounds.1.trans member.1, member.2.trans bounds.2⟩ forward
  exact nonadjacent_sector_strip_images_disjoint (traces i first) (traces j last)
    different not_next not_previous (close i) (close j) (cell_margin i first) (cell_margin j last)

end Unfoldings.ConvexCap.RadialCutForest
