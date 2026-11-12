module

public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.ClosedCirclePinches

/-! Every smaller source circle crosses the actual approached portion of either bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- The crossing stays below the original approached endpoint, even at a terminal pinch. -/
theorem exists_closed_bank_point_on_smaller_circle
    (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper)
    {h radius r : ℝ} (nonnegative : 0 ≤ h)
    (closed : H.point h ∈ closure data.strictDomain)
    (size : ‖data.value (H.point h) - data.center‖ = radius)
    (smaller : r ∈ Set.Ioo 0 radius) :
    ∃ k ∈ Set.Icc 0 h, H.point k ∈ closure data.strictDomain ∧
      ‖data.value (H.point k) - data.center‖ = r := by
  obtain ⟨_, active⟩ := closure_nonempty_iff.mp ⟨_, closed⟩
  have source_value : data.value (H.point 0) = data.center := by
    rcases wall with rfl | rfl
    · exact (data.source_bank_values active).1
    · exact (data.source_bank_values active).2
  have norm_continuous : Continuous (fun k : ℝ => ‖data.value (H.point k) - data.center‖) :=
    ((data.continuous.comp H.point_continuous).sub continuous_const).norm
  have norm_zero : ‖data.value (H.point 0) - data.center‖ = 0 := by
    rw [source_value, sub_self, norm_zero]
  obtain ⟨k, height, equal⟩ := intermediate_value_Icc nonnegative norm_continuous.continuousOn
    (show r ∈ Set.Icc _ _ from ⟨by rw [norm_zero]; exact smaller.1.le,
      by rw [size]; exact smaller.2.le⟩)
  refine ⟨k, height, ?_, equal⟩
  rcases wall with rfl | rfl
  · exact data.lower_bank_closed_before closed (by rwa [S.lower.point_height])
  · exact data.upper_bank_closed_before closed (by rwa [S.upper.point_height])

/-- Once a regular smaller circle has an open slice, its chosen bank endpoint stays below
any prescribed actual endpoint on a larger circle. -/
theorem circle_slice_upper_height_le_closed_height
    {h radius r : ℝ} (nonnegative : 0 ≤ h)
    (closed : S.upper.point h ∈ closure data.strictDomain)
    (size : ‖data.value (S.upper.point h) - data.center‖ = radius)
    (smaller : r ∈ Set.Ioo 0 radius)
    (slice : S.BankCircleSlice data.value data.center cutoff r) : slice.upperHeight ≤ h := by
  obtain ⟨_, active⟩ := closure_nonempty_iff.mp ⟨_, closed⟩
  obtain ⟨k, height, k_closed, k_size⟩ :=
    data.exists_closed_bank_point_on_smaller_circle S.upper (Or.inr rfl)
      nonnegative closed size smaller
  have equal := data.radial.closed_bank_circle_height_unique data.continuous S.upper
    (Or.inr rfl) (data.source_bank_values active).2 slice.upper_bounds.1 height.1 smaller.1
    slice.upper_closed k_closed slice.upper_radius k_size
  exact equal ▸ height.2

/-- The matching lower-bank bound also includes larger-circle terminal pinches. -/
theorem circle_slice_lower_height_le_closed_height
    {h radius r : ℝ} (nonnegative : 0 ≤ h)
    (closed : S.lower.point h ∈ closure data.strictDomain)
    (size : ‖data.value (S.lower.point h) - data.center‖ = radius)
    (smaller : r ∈ Set.Ioo 0 radius)
    (slice : S.BankCircleSlice data.value data.center cutoff r) : slice.lowerHeight ≤ h := by
  obtain ⟨_, active⟩ := closure_nonempty_iff.mp ⟨_, closed⟩
  obtain ⟨k, height, k_closed, k_size⟩ :=
    data.exists_closed_bank_point_on_smaller_circle S.lower (Or.inl rfl)
      nonnegative closed size smaller
  have equal := data.radial.closed_bank_circle_height_unique data.continuous S.lower
    (Or.inl rfl) (data.source_bank_values active).1 slice.lower_bounds.1 height.1 smaller.1
    slice.lower_closed k_closed slice.lower_radius k_size
  exact equal ▸ height.2

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
