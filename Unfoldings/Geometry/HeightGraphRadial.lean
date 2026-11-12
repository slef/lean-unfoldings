module

public import Unfoldings.Geometry.MonotoneHeightGraph
public import Unfoldings.Geometry.NearIdentityRadial

/-! Monotone height graphs give radial progress through arbitrary continuous chart switches. -/

@[expose] public section

namespace Unfoldings.MonotoneHeightGraph

theorem finite_near_identity_selection_radial (H : MonotoneHeightGraph)
    {ι : Type*} [Finite ι] (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (F : ℂ → ℂ) (Fcontinuous : Continuous F) (source : ℂ)
    {a b δ μ M r : ℝ} (ordered : a < b) (nonnegative : 0 ≤ δ)
    (positive : 0 < r) (small : δ * M < μ)
    (error : ∀ i z, ‖(A i).linear z - z‖ ≤ δ * ‖z‖)
    (horizontal_margin : μ * r ≤ (F (H.point a) - source).re)
    (vertical_margin : μ * r ≤ (F (H.point a) - source).im)
    (norm_bound : ‖F (H.point a) - source‖ ≤ M * r)
    (selection : ∀ h ∈ Set.Icc a b, ∃ i, F (H.point h) = A i (H.point h)) :
    ‖F (H.point a) - source‖ < ‖F (H.point b) - source‖ := by
  let input := fun t : unitInterval => a + (t : ℝ) * (b - a)
  let P : Path (H.point a) (H.point b) :=
    { toFun t := H.point (input t)
      continuous_toFun := H.point_continuous.comp
        (continuous_const.add (continuous_subtype_val.mul continuous_const))
      source' := by change H.point (a + (0 : ℝ) * (b - a)) = _; rw [zero_mul, add_zero]
      target' := by change H.point (a + (1 : ℝ) * (b - a)) = _; congr 1; ring }
  have monotone : Monotone input := by
    intro s t before
    have product := mul_le_mul_of_nonneg_right
      (show (s : ℝ) ≤ t from before) (sub_nonneg.mpr ordered.le)
    dsimp only [input]
    linarith
  have range (t : unitInterval) : input t ∈ Set.Icc a b := by
    have lower := mul_nonneg t.property.1 (sub_nonneg.mpr ordered.le)
    have upper := mul_le_mul_of_nonneg_right t.property.2 (sub_nonneg.mpr ordered.le)
    dsimp only [input]
    constructor <;> linarith
  apply Unfoldings.finite_near_identity_selection_radial A continuous source nonnegative
    positive small error horizontal_margin vertical_margin norm_bound P
    (Fcontinuous.comp P.continuous) (fun t => selection (input t) (range t))
  · exact H.coordinate_mono.comp monotone
  · exact H.complement_mono.comp monotone
  · rwa [H.point_height, H.point_height]

end Unfoldings.MonotoneHeightGraph
