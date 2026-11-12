module

public import Unfoldings.Cap.CrossFrameTraceQuadrants
public import Unfoldings.Cap.EmptyCircleContinuation

/-! Actual approached terminal copies inherit strict margins in either neighboring frame. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}

theorem RadialStripTraceData.closed_strict_physical_quadrant_margin
    {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain) (nonzero : z ≠ 0)
    (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) {μ : ℝ} (positive_margin : 0 < μ)
    (bounds : ∀ f, source + (fiveSectorFrame t positive small i).place.symm z ∈
        (K.projectedTriangle f).carrier →
      μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ ≤
        (frame (D.projectedPlacement K f
          (source + (fiveSectorFrame t positive small i).place.symm z) - center)).re ∧
      μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ ≤
        (frame (D.projectedPlacement K f
          (source + (fiveSectorFrame t positive small i).place.symm z) - center)).im) :
    0 < (frame (data.outputFrame.symm (data.value z) - center)).re ∧
      0 < (frame (data.outputFrame.symm (data.value z) - center)).im := by
  have lower := data.closed_physical_quadrant_margin closed frame center μ bounds
  have gap : 0 < μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact mul_pos positive_margin (norm_pos_iff.mpr nonzero)
  exact ⟨gap.trans_le lower.1, gap.trans_le lower.2⟩

namespace FiveSectorFrameData

variable (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (terminal : B.EmptyCircleContinuation i data physicalRadius radius)
  (actual : Plane)
  (value : data.value (S.lower.point terminal.height) = B.sectorFrame i actual)

include value

theorem terminal_actual_point_norm_lt : ‖actual - D.projectedMap K source‖ < radius := by
  have inside := terminal.inside
  have center : data.center = B.sectorFrame i (D.projectedMap K source) :=
    data.center_eq_outputFrame
  rw [value, center, ← map_sub, (B.sectorFrame i).norm_map] at inside
  exact inside

theorem terminal_actual_point_strict_margin
    (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) {μ : ℝ} (positive_margin : 0 < μ)
    (bounds : ∀ f, K.projectedVertex terminal.vertex ∈ (K.projectedTriangle f).carrier →
      μ * ‖K.projectedVertex terminal.vertex - source‖ ≤
        (frame (D.projectedPlacement K f (K.projectedVertex terminal.vertex) - center)).re ∧
      μ * ‖K.projectedVertex terminal.vertex - source‖ ≤
        (frame (D.projectedPlacement K f (K.projectedVertex terminal.vertex) - center)).im) :
    0 < (frame (actual - center)).re ∧ 0 < (frame (actual - center)).im := by
  have included : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono included terminal.lower_closed
  have nonzero : S.lower.point terminal.height ≠ 0 := by
    intro zero
    have height := S.lower.point_height terminal.height
    rw [zero, Complex.zero_re, Complex.zero_im, zero_add] at height
    exact terminal.height_bounds.1.ne' height.symm
  have margin := data.closed_strict_physical_quadrant_margin closed nonzero frame center
    positive_margin (fun f member => by
      have result := bounds f (terminal.physical ▸ member)
      rw [← terminal.physical, add_sub_cancel_left] at result
      exact result)
  have actual_value : data.outputFrame.symm (data.value (S.lower.point terminal.height)) =
      actual := by
    change (B.sectorFrame i).symm (data.value (S.lower.point terminal.height)) = _
    rw [value, LinearIsometryEquiv.symm_apply_apply]
  rwa [actual_value] at margin

end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
