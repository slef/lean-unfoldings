module

public import Unfoldings.Cap.BoundaryRunSharedMargins
public import Unfoldings.Cap.ClosedSectionSharedBankMargins
public import Unfoldings.Cap.BoundaryRunApproachedBanks

/-! Collapsed physical boundary runs yield both neighboring comparison margins. -/

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
  {ε μ cutoff physicalRadius radius : ℝ} {n : ℕ}
  (cells : Fin (n + 1) → MonotoneStrip)
  (traces : ∀ k, N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i (cells k) ε cutoff)
  (contacts : ∀ k : Fin n, Set.EqOn (cells k.castSucc).upper.point
    (cells k.succ).lower.point (Set.Icc 0 cutoff))
  (terminals : ∀ k, B.EmptyCircleContinuation i (traces k) physicalRadius radius)
  (pivot : Fin (n + 1)) (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
  (outer : if upper then
    Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
    else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff))
  (positive_margin : 0 < μ)
  (face_bounds : ∀ a f p, p ∈ (K.projectedTriangle f).carrier →
    p - source ∈ closedFiveSector t a →
    p ∈ sectorSweepInterior positive small source cutoff →
    μ * ‖p - source‖ ≤
      (B.sectorFrame a (D.projectedPlacement K f p - D.projectedMap K source)).re ∧
    μ * ‖p - source‖ ≤
      (B.sectorFrame a (D.projectedPlacement K f p - D.projectedMap K source)).im)

include shared contacts highest outer positive_margin face_bounds

theorem closed_section_boundary_run_late_shared_margins {S : MonotoneStrip}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (slice : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (facing : if upper then Set.EqOn S.upper.point (cells 0).lower.point (Set.Icc 0 cutoff)
      else Set.EqOn S.lower.point (cells (Fin.last n)).upper.point (Set.Icc 0 cutoff))
    (late : (terminals pivot).height ≤ if upper then slice.upperHeight else slice.lowerHeight) :
    let z := if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight
    ∀ a, a = i ∨ a = l →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value z) - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame a
        (data.outputFrame.symm (data.value z) - D.projectedMap K source)).im := by
  let h := if upper then slice.upperHeight else slice.lowerHeight
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  have heights : slice.lowerHeight ∈ Set.Ioo 0 cutoff ∧
      slice.upperHeight ∈ Set.Ioo 0 cutoff := by
    constructor
    · simpa only [S.lower.point_height] using
        data.closed_circle_height_mem_Ioo radius_positive far slice.lower_closed slice.lower_radius
    · simpa only [S.upper.point_height] using
        data.closed_circle_height_mem_Ioo radius_positive far slice.upper_closed slice.upper_radius
  have height : h ∈ Set.Ioo 0 cutoff := by
    cases upper
    · exact heights.1
    · exact heights.2
  have collapsed (k : Fin (n + 1)) : (cells k).lower.coordinate h =
      (cells k).upper.coordinate h :=
    (terminals k).merged h ⟨(highest k).trans late, height.2.le⟩
  have coordinates := MonotoneStrip.collapsed_chain_points_of_contacts cells
    (fun k => congrArg Complex.re (contacts k ⟨height.1.le, height.2.le⟩)) collapsed
    0 (Fin.last n)
  apply B.closed_section_shared_bank_margins i l upper shared positive_margin face_bounds
    data slice radius_positive small_error room
  cases upper
  · exact (facing ⟨height.1.le, height.2.le⟩).trans
      (coordinates.symm.trans (outer ⟨height.1.le, height.2.le⟩).symm)
  · exact (facing ⟨height.1.le, height.2.le⟩).trans
      (coordinates.trans (outer ⟨height.1.le, height.2.le⟩))

theorem closed_section_boundary_run_candidate_shared_margins {S : MonotoneStrip}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (slice : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (physical_room : 2 * physicalRadius < cutoff)
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (facing : if upper then Set.EqOn S.upper.point (cells 0).lower.point (Set.Icc 0 cutoff)
      else Set.EqOn S.lower.point (cells (Fin.last n)).upper.point (Set.Icc 0 cutoff))
    (actual : Plane)
    (origin : (traces pivot).outputFrame.symm
        ((traces pivot).value ((cells pivot).lower.point (terminals pivot).height)) = actual ∨
      ((terminals pivot).height < (if upper then slice.upperHeight else slice.lowerHeight) ∧
        data.outputFrame.symm (data.value
          (if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight)) =
            actual)) :
    ∀ a, a = i ∨ a = l →
      0 < (B.sectorFrame a (actual - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame a (actual - D.projectedMap K source)).im := by
  rcases origin with terminal | ⟨late, circle⟩
  · have margins := B.boundary_run_terminal_shared_margins i l upper shared cells traces contacts
      terminals pivot highest outer positive_margin face_bounds physical_room
    rwa [terminal] at margins
  · have margins := B.closed_section_boundary_run_late_shared_margins i l upper shared cells
      traces contacts terminals pivot highest outer positive_margin face_bounds data slice
      radius_positive
      small_error room facing late.le
    dsimp only at margins
    rwa [circle] at margins

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
