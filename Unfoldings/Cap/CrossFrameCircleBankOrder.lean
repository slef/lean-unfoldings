module

public import Unfoldings.Cap.CirclePhysicalBankMatching
public import Unfoldings.Cap.CompletedBankCircleOrder

/-! Actual circle banks in different sector coordinates can be ordered in one comparison frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

/-- Each endpoint is matched using its own strip frame. The complete actual
bank chain is then compared in a third, specified frame. All positions are
transported through the common developed plane before the comparison. -/
theorem circle_parent_path_bank_order_across_frames
    (i j frame : FiveSector) {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
    (first_directions : ∀ k : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w k).val) -
        K.projectedVertex (N.completedBankChain w k).val ∈ closedFiveSector t i)
    (last_directions : ∀ k : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w k).val) -
        K.projectedVertex (N.completedBankChain w k).val ∈ closedFiveSector t j)
    (directions : ∀ k : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w k).val) -
        K.projectedVertex (N.completedBankChain w k).val ∈ closedFiveSector t frame)
    (sectors : ∀ k, N.CurvedSubtreeInSector (t := t) frame (N.completedBankChain w k))
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (a b : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    (first_regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) ≠ (K.projectedTriangle f).vertex k)
    (last_regular : ∀ f k, source + (fiveSectorFrame t positive small j).place.symm
      (T.lower.point last_slice.lowerHeight) ≠ (K.projectedTriangle f).vertex k)
    (first_physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) = (N.completedRootPath w).point a s)
    (last_physical : source + (fiveSectorFrame t positive small j).place.symm
      (T.lower.point last_slice.lowerHeight) = (N.completedRootPath w).point b r)
    (first_quadrant :
      0 ≤ (B.sectorFrame frame
        (data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) -
          D.projectedMap K source)).re ∧
      0 ≤ (B.sectorFrame frame
        (data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) -
          D.projectedMap K source)).im)
    (last_quadrant :
      0 ≤ (B.sectorFrame frame
        (other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) -
          D.projectedMap K source)).re ∧
      0 ≤ (B.sectorFrame frame
        (other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) -
          D.projectedMap K source)).im) :
    (B.sectorFrame frame
      (data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) -
        D.projectedMap K source)).re ≤
      (B.sectorFrame frame
        (other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) -
          D.projectedMap K source)).re ∧
    (B.sectorFrame frame
      (other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) -
        D.projectedMap K source)).im ≤
      (B.sectorFrame frame
        (data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) -
          D.projectedMap K source)).im := by
  have first := B.circle_upper_physical_eq_exit i data radius_positive far first_slice w on_cuts
    first_directions a s first_regular first_physical
  have last := B.circle_lower_physical_eq_entrance j other radius_positive far last_slice w on_cuts
    last_directions b r last_regular last_physical
  have first_radius :
      ‖N.parentExitPoint (N.completedDevelopment D) (N.completedBankChain w a) (1 - (s : ℝ)) -
        D.projectedMap K source‖ = radius := by
    rw [← first, ← data.outputFrame.norm_map, map_sub, data.outputFrame.apply_symm_apply,
      ← data.center_eq_outputFrame]
    exact first_slice.upper_radius
  have last_radius :
      ‖N.parentEntrancePoint (N.completedDevelopment D) (N.completedBankChain w b) (1 - (r : ℝ)) -
        D.projectedMap K source‖ = radius := by
    rw [← last, ← other.outputFrame.norm_map, map_sub, other.outputFrame.apply_symm_apply,
      ← other.center_eq_outputFrame]
    exact last_slice.lower_radius
  have gap := B.chain_circle_order frame (N.completedBankChain w) (N.completedBankChain_parent w)
    sectors directions budget (D.projectedMap K source) a b s r
    (by rw [← first]; exact first_quadrant) (by rw [← last]; exact last_quadrant)
    (first_radius.trans last_radius.symm)
  rw [← first, ← last] at gap
  exact gap

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
