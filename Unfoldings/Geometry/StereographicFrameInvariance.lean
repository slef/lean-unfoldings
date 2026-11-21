module

public import Unfoldings.Geometry.StereographicAngularDistance
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Orthogonal changes of the two planar coordinates preserve angle and area. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry MeasureTheory

/-- Reframing the chart leaves every inverse stereographic angular distance unchanged. -/
theorem angle_inverseStereographic_isometry (T : Plane ≃ₗᵢ[ℝ] Plane) (x y : Plane) :
    angle (inverseStereographic (T x)) (inverseStereographic (T y)) =
      angle (inverseStereographic x) (inverseStereographic y) := by
  have chord :
      ‖inverseStereographic (T x) - inverseStereographic (T y)‖ ^ 2 =
        ‖inverseStereographic x - inverseStereographic y‖ ^ 2 := by
    rw [inverseStereographic_chord_sq, inverseStereographic_chord_sq, ← map_sub,
      T.norm_map, T.norm_map, T.norm_map]
  have dot : inner ℝ (inverseStereographic (T x)) (inverseStereographic (T y)) =
      inner ℝ (inverseStereographic x) (inverseStereographic y) := by
    simp only [norm_sub_pow_two_real, inverseStereographic_unit] at chord
    linarith only [chord]
  simp only [angle, inverseStereographic_unit, mul_one, div_one, dot]

theorem volume_linearIsometryEquiv_image (T : Plane ≃ₗᵢ[ℝ] Plane) {K : Set Plane}
    (compact : IsCompact K) : volume (T '' K) = volume K := by
  calc
    _ = Measure.map T volume (T '' K) := by rw [T.measurePreserving.map_eq]
    _ = _ := by rw [Measure.map_apply T.continuous.measurable
      (compact.image T.continuous).measurableSet, T.injective.preimage_image]

end Unfoldings.Cap
