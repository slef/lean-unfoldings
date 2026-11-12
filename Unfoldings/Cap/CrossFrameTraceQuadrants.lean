module

public import Unfoldings.Cap.CoherentPhysicalTraceContact
public import Unfoldings.Cap.SectorSweepBall
public import Unfoldings.Geometry.MonotoneStripSourceError

/-! Actual approached trace copies inherit quantitative margins in any comparison frame. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- Bounds for all incident face copies also bound the particular approached
copy selected by a strip, in any specified developed comparison frame. -/
theorem closed_physical_quadrant_margin
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane) (μ : ℝ)
    (bounds : ∀ f, source + (fiveSectorFrame t positive small i).place.symm z ∈
        (K.projectedTriangle f).carrier →
      μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ ≤
        (frame (D.projectedPlacement K f
          (source + (fiveSectorFrame t positive small i).place.symm z) - center)).re ∧
      μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ ≤
        (frame (D.projectedPlacement K f
          (source + (fiveSectorFrame t positive small i).place.symm z) - center)).im) :
    μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ ≤
      (frame (data.outputFrame.symm (data.value z) - center)).re ∧
    μ * ‖(fiveSectorFrame t positive small i).place.symm z‖ ≤
      (frame (data.outputFrame.symm (data.value z) - center)).im := by
  obtain ⟨f, member, value⟩ := data.exists_physical_face_of_closed closed
  rw [value]
  exact bounds f member

/-- A controlled approached circle point lies in every sector's sweep,
independently of which sector supplies its trace coordinates. -/
theorem closed_circle_point_mem_sectorSweepInterior
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (small_error : ε < 1 / 2) {z : ℂ} (closed : z ∈ closure data.strictDomain)
    {radius : ℝ} (size : ‖data.value z - data.center‖ = radius)
    (room : 2 * radius < (1 / 2 - ε) * cutoff) :
    source + (fiveSectorFrame t positive small i).place.symm z ∈
      sectorSweepInterior positive small source cutoff := by
  have lower := data.closed_distance_lower closed
  rw [size] at lower
  have included : data.strictDomain ⊆ S.boundedCarrier 0 cutoff :=
    fun _ member => ⟨⟨member.1.1.le, member.1.2.le⟩, member.2⟩
  have bounded : z ∈ S.boundedCarrier 0 cutoff :=
    closure_minimal included (S.isClosed_boundedCarrier 0 cutoff) closed
  have coordinates := S.carrier_coordinates_nonnegative data.lower_source data.upper_source
    bounded.1 bounded.2.1
  have norm_bound : ‖z‖ ≤ z.re + z.im := by
    simpa only [abs_of_nonneg coordinates.1, abs_of_nonneg coordinates.2] using
      Complex.norm_le_abs_re_add_abs_im z
  have bound : 2 * ‖z‖ < cutoff := by
    have coefficient : 0 < 1 / 2 - ε := sub_pos.mpr small_error
    nlinarith [mul_le_mul_of_nonneg_left norm_bound coefficient.le]
  apply closedBall_subset_sectorSweepInterior positive small source bound
  simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
    (fiveSectorFrame t positive small i).place.symm.norm_map, le_refl]

/-- Uniform actual face margins supply the comparison quadrant for a circle
endpoint in another sector's coordinates. No trace-quadrant hypothesis is needed. -/
theorem closed_circle_quadrant_in_sector
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    {radius : ℝ} (size : ‖data.value z - data.center‖ = radius)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (comparison : FiveSector) (frame : Plane ≃ₗᵢ[ℝ] ℂ) (center : Plane)
    (face_bounds : ∀ f p, p ∈ (K.projectedTriangle f).carrier →
      p - source ∈ closedFiveSector t comparison →
      p ∈ sectorSweepInterior positive small source cutoff →
      ε * ‖p - source‖ ≤ (frame (D.projectedPlacement K f p - center)).re ∧
      ε * ‖p - source‖ ≤ (frame (D.projectedPlacement K f p - center)).im)
    (cone : (fiveSectorFrame t positive small i).place.symm z ∈
      closedFiveSector t comparison) :
    0 ≤ (frame (data.outputFrame.symm (data.value z) - center)).re ∧
      0 ≤ (frame (data.outputFrame.symm (data.value z) - center)).im := by
  have region := data.closed_circle_point_mem_sectorSweepInterior small_error closed size room
  have margin := data.closed_physical_quadrant_margin closed frame center ε (fun f member => by
    have bound := face_bounds f _ member (by simpa only [add_sub_cancel_left] using cone) region
    simpa only [add_sub_cancel_left] using bound)
  have lower := mul_nonneg nonnegative
    (norm_nonneg ((fiveSectorFrame t positive small i).place.symm z))
  exact ⟨lower.trans margin.1, lower.trans margin.2⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
