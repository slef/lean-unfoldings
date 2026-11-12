module

public import Unfoldings.Cap.RadialStripCircleBanks
public import Unfoldings.Cap.RadialStripPointOrder

/-! Nonempty controlled source-circle slices meet the banks at positive physical width. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- If either endpoint were a zero-width pinch, both banks would meet the circle
there. Radial uniqueness would identify the two slice endpoints, contradicting nonemptiness. -/
theorem circle_slice_width {radius : ℝ} (radius_positive : 0 < radius)
    (slice : S.BankCircleSlice data.value data.center cutoff radius) :
    S.lower.coordinate slice.lowerHeight < S.upper.coordinate slice.lowerHeight ∧
      S.lower.coordinate slice.upperHeight < S.upper.coordinate slice.upperHeight := by
  obtain ⟨active, member⟩ :=
    (show (closure data.strictDomain).Nonempty from
      ⟨S.lower.point slice.lowerHeight, slice.lower_closed⟩).of_closure
  have sources := data.source_bank_values member
  have point_equal {h : ℝ} (collapsed : S.lower.coordinate h = S.upper.coordinate h) :
      S.lower.point h = S.upper.point h := by
    apply Complex.ext
    · exact collapsed
    · change h - S.lower.coordinate h = h - S.upper.coordinate h
      rw [collapsed]
  constructor
  · by_contra nonpositive
    have point := point_equal (le_antisymm (S.ordered _) (le_of_not_gt nonpositive))
    have closed := slice.lower_closed
    have size := slice.lower_radius
    rw [point] at closed size
    have same := data.radial.closed_bank_circle_height_unique data.continuous S.upper
      (Or.inr rfl) sources.2 slice.lower_bounds.1 slice.upper_bounds.1 radius_positive
      closed slice.upper_closed size slice.upper_radius
    apply slice.distinct
    rw [point, same]
  · by_contra nonpositive
    have point := point_equal (le_antisymm (S.ordered _) (le_of_not_gt nonpositive))
    have closed := slice.upper_closed
    have size := slice.upper_radius
    rw [← point] at closed size
    have same := data.radial.closed_bank_circle_height_unique data.continuous S.lower
      (Or.inl rfl) sources.1 slice.lower_bounds.1 slice.upper_bounds.1 radius_positive
      slice.lower_closed closed slice.lower_radius size
    apply slice.distinct
    rw [same, point]

/-- Source and cutoff points do not occur as endpoints of a controlled positive-circle slice. -/
theorem circle_slice_heights {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius) :
    slice.lowerHeight ∈ Set.Ioo 0 cutoff ∧ slice.upperHeight ∈ Set.Ioo 0 cutoff := by
  obtain ⟨active, member⟩ :=
    (show (closure data.strictDomain).Nonempty from
      ⟨S.lower.point slice.lowerHeight, slice.lower_closed⟩).of_closure
  have first := data.closed_height_pos_of_norm slice.lower_closed
    (by rw [slice.lower_radius]; exact radius_positive)
  have last := data.closed_height_pos_of_norm slice.upper_closed
    (by rw [slice.upper_radius]; exact radius_positive)
  rw [S.lower.point_height] at first
  rw [S.upper.point_height] at last
  have lower_ne : slice.lowerHeight ≠ cutoff := by
    intro equal
    exact data.end_levels_avoid_circle member radius_positive far slice.lower_closed
      (Or.inr (by rw [S.lower.point_height, equal])) slice.lower_radius
  have upper_ne : slice.upperHeight ≠ cutoff := by
    intro equal
    exact data.end_levels_avoid_circle member radius_positive far slice.upper_closed
      (Or.inr (by rw [S.upper.point_height, equal])) slice.upper_radius
  exact ⟨⟨first, lt_of_le_of_ne slice.lower_bounds.2 lower_ne⟩,
    ⟨last, lt_of_le_of_ne slice.upper_bounds.2 upper_ne⟩⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
