module

public import Unfoldings.Cap.BoundaryTerminalMargins
public import Unfoldings.Cap.SectorBankRays
public import Unfoldings.Cap.SectorBoundaryCutPoints

/-! An actual approached copy on a shared bank has strict margins in both sector frames. -/

@[expose] public section

namespace Unfoldings

theorem shared_sector_bank_mem_both_cones {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i l : FiveSector) (upper : Bool)
    (shared : if upper then fiveSectorFirst t i = fiveSectorLast t l
      else fiveSectorFirst t l = fiveSectorLast t i)
    {h : ℝ} (height_positive : 0 < h) :
    let x := (fiveSectorFrame t positive small i).place.symm
      ((if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
        else (fiveSectorFrame t positive small i).enclosingStrip.lower).point h)
    x ∈ closedFiveSector t i ∧ x ∈ closedFiveSector t l := by
  constructor
  · have banks := fiveSector_enclosingStrip_bank_closed positive small i height_positive.le
    cases upper
    · exact banks.1
    · exact banks.2
  · cases upper
    · obtain ⟨a, apositive, ray⟩ :=
        (fiveSectorFrame t positive small i).enclosingStrip_lower_point_on_last_ray height_positive
      refine ⟨a, 0, apositive.le, le_rfl, ?_⟩
      change (fiveSectorFrame t positive small i).place.symm
          ((fiveSectorFrame t positive small i).enclosingStrip.lower.point h) =
        a • fiveSectorFirst t l + 0 • fiveSectorLast t l
      simpa only [zero_smul, add_zero] using
        ray.trans (congrArg (fun v : Plane => a • v) shared.symm)
    · obtain ⟨a, apositive, ray⟩ :=
        (fiveSectorFrame t positive small i).enclosingStrip_upper_point_on_first_ray height_positive
      refine ⟨0, a, le_rfl, apositive.le, ?_⟩
      change (fiveSectorFrame t positive small i).place.symm
          ((fiveSectorFrame t positive small i).enclosingStrip.upper.point h) =
        0 • fiveSectorFirst t l + a • fiveSectorLast t l
      simpa only [zero_smul, zero_add] using
        ray.trans (congrArg (fun v : Plane => a • v) shared)

end Unfoldings

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

theorem shared_boundary_closed_trace_margins (i l k : FiveSector) (upper : Bool)
    (shared : if upper then fiveSectorFirst t i = fiveSectorLast t l
      else fiveSectorFirst t l = fiveSectorLast t i)
    {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {S : MonotoneStrip} {δ limit : ℝ}
    (data : N.RadialStripTraceData positive small D calibration k S δ limit)
    {z : ℂ} (closed : z ∈ closure data.strictDomain) {h cutoff : ℝ} (height_positive : 0 < h)
    (contact : (fiveSectorFrame t positive small k).place.symm z =
      (fiveSectorFrame t positive small i).place.symm
        ((if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
          else (fiveSectorFrame t positive small i).enclosingStrip.lower).point h))
    (region : source + (fiveSectorFrame t positive small k).place.symm z ∈
      sectorSweepInterior positive small source cutoff)
    {μ : ℝ} (positive_margin : 0 < μ)
    (face_bounds : ∀ a f p, p ∈ (K.projectedTriangle f).carrier →
      p - source ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small source cutoff →
      μ * ‖p - source‖ ≤
        (B.sectorFrame a (D.projectedPlacement K f p - D.projectedMap K source)).re ∧
      μ * ‖p - source‖ ≤
        (B.sectorFrame a (D.projectedPlacement K f p - D.projectedMap K source)).im) :
    ∀ a, a = i ∨ a = l →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value z) - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame a
        (data.outputFrame.symm (data.value z) - D.projectedMap K source)).im := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  have nonzero : z ≠ 0 := by
    intro zero
    have inverse_zero : frame.place.symm (H.point h) = 0 := by
      rw [← contact, zero, map_zero]
    have point_zero := congrArg frame.place inverse_zero
    rw [frame.place.apply_symm_apply, map_zero] at point_zero
    have height := congrArg (fun w : ℂ => w.re + w.im) point_zero
    rw [H.point_height, Complex.zero_re, Complex.zero_im, zero_add] at height
    exact height_positive.ne' height
  have cones := shared_sector_bank_mem_both_cones positive small i l upper shared height_positive
  intro a choice
  have cone : (fiveSectorFrame t positive small k).place.symm z ∈ closedFiveSector t a := by
    rw [contact]
    rcases choice with rfl | rfl
    · exact cones.1
    · exact cones.2
  apply data.closed_strict_physical_quadrant_margin closed nonzero (B.sectorFrame a)
    (D.projectedMap K source) positive_margin
  intro f member
  have bound := face_bounds a f _ member
    (by simpa only [add_sub_cancel_left] using cone) region
  simpa only [add_sub_cancel_left] using bound

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
