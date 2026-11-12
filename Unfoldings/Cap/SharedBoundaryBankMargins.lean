module

public import Unfoldings.Cap.SharedBoundaryTraceMargins
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Cap.CrossFrameTraceQuadrants

/-! Actual terminal and circle bank copies on a shared ray have both comparison margins. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i l : FiveSector) (upper : Bool)
  (shared : if upper then fiveSectorFirst t i = fiveSectorLast t l
    else fiveSectorFirst t l = fiveSectorLast t i)
  {μ cutoff : ℝ} (positive_margin : 0 < μ)
  (face_bounds : ∀ a f p, p ∈ (K.projectedTriangle f).carrier →
    p - source ∈ closedFiveSector t a →
    p ∈ sectorSweepInterior positive small source cutoff →
    μ * ‖p - source‖ ≤
      (B.sectorFrame a (D.projectedPlacement K f p - D.projectedMap K source)).re ∧
    μ * ‖p - source‖ ≤
      (B.sectorFrame a (D.projectedPlacement K f p - D.projectedMap K source)).im)

include shared positive_margin face_bounds

theorem terminal_shared_bank_margins
    {S : MonotoneStrip} {ε physicalRadius radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (terminal : B.EmptyCircleContinuation i data physicalRadius radius)
    (physical_room : 2 * physicalRadius < cutoff)
    (contact : S.lower.point terminal.height =
      (if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
        else (fiveSectorFrame t positive small i).enclosingStrip.lower).point terminal.height) :
    ∀ a, a = i ∨ a = l →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.lower.point terminal.height)) -
        D.projectedMap K source)).re ∧
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.lower.point terminal.height)) -
        D.projectedMap K source)).im := by
  have included : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono included terminal.lower_closed
  have in_ball : source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point terminal.height) ∈ Metric.closedBall source physicalRadius := by
    rw [terminal.physical, Metric.mem_closedBall, dist_eq_norm]
    exact terminal.physical_inside.le
  have region := closedBall_subset_sectorSweepInterior positive small source physical_room in_ball
  exact B.shared_boundary_closed_trace_margins i l i upper shared data closed
    terminal.height_bounds.1 (congrArg (fiveSectorFrame t positive small i).place.symm contact)
    region positive_margin face_bounds

theorem circle_shared_bank_margins
    {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {S : MonotoneStrip} {ε radius : ℝ}
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (contact :
      (if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight) =
      (if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
        else (fiveSectorFrame t positive small i).enclosingStrip.lower).point
          (if upper then slice.upperHeight else slice.lowerHeight)) :
    let z := if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight
    ∀ a, a = i ∨ a = l →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value z) - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame a
        (data.outputFrame.symm (data.value z) - D.projectedMap K source)).im := by
  let z := if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight
  let h := if upper then slice.upperHeight else slice.lowerHeight
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  have heights := data.circle_slice_heights radius_positive far slice
  have height : 0 < h := by
    cases upper
    · exact heights.1.1
    · exact heights.2.1
  have closed : z ∈ closure data.strictDomain := by
    cases upper
    · change S.lower.point slice.lowerHeight ∈ closure data.strictDomain
      exact slice.lower_closed
    · change S.upper.point slice.upperHeight ∈ closure data.strictDomain
      exact slice.upper_closed
  have size : ‖data.value z - data.center‖ = radius := by
    cases upper
    · exact slice.lower_radius
    · exact slice.upper_radius
  have region := data.closed_circle_point_mem_sectorSweepInterior small_error closed size room
  exact B.shared_boundary_closed_trace_margins i l i upper shared data closed height
    (congrArg (fiveSectorFrame t positive small i).place.symm contact)
    region positive_margin face_bounds

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
