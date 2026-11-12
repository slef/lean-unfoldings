module

public import Unfoldings.Cap.BoundaryTerminalMargins
public import Unfoldings.Cap.RadialStripPointOrder

/-! Uniform face margins give strict comparison quadrants for actual circle bank points. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

theorem closed_circle_strict_quadrant_in_sector
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (positive_error : 0 < ε) (small_error : ε < 1 / 2)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    {radius : ℝ} (radius_positive : 0 < radius)
    (size : ‖data.value z - data.center‖ = radius)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (comparison : FiveSector) (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane)
    (face_bounds : ∀ f p, p ∈ (K.projectedTriangle f).carrier →
      p - source ∈ closedFiveSector t comparison →
      p ∈ sectorSweepInterior positive small source cutoff →
      ε * ‖p - source‖ ≤ (frame (D.projectedPlacement K f p - center)).re ∧
      ε * ‖p - source‖ ≤ (frame (D.projectedPlacement K f p - center)).im)
    (cone : (fiveSectorFrame t positive small i).place.symm z ∈
      closedFiveSector t comparison) :
    0 < (frame (data.outputFrame.symm (data.value z) - center)).re ∧
      0 < (frame (data.outputFrame.symm (data.value z) - center)).im := by
  have region := data.closed_circle_point_mem_sectorSweepInterior small_error closed size room
  have height := data.closed_height_pos_of_norm closed (by rw [size]; exact radius_positive)
  have nonzero : z ≠ 0 := by
    intro zero
    rw [zero, Complex.zero_re, Complex.zero_im, zero_add] at height
    exact (lt_irrefl _ height).elim
  apply data.closed_strict_physical_quadrant_margin closed nonzero frame center positive_error
  intro f member
  have bound := face_bounds f _ member (by simpa only [add_sub_cancel_left] using cone) region
  simpa only [add_sub_cancel_left] using bound

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
