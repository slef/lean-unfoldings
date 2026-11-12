module

public import Unfoldings.Cap.ClosedBankStartOrder
public import Unfoldings.Cap.ClosedParentPathProgress
public import Unfoldings.Geometry.ClosedChainTracking
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.RecoverableStripClosure

/-! Strict bank progress from the actual starting copy includes all closed vertex heights. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
  (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
  (directions : ∀ j, K.projectedVertex
    (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
      K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
  (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
  {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (pinches : S.ApproachedPinchesIn
    (Set.range (fun v : {v : C.Vertex Set.univ // K.projectedVertex v ∈ cuts} =>
      (fiveSectorFrame t positive small i).place (K.projectedVertex v.val - source))) 0 cutoff)
  {a b : ℝ} (start : 0 ≤ a) (ordered : a < b) (finish : b ≤ cutoff)

variable (nonnegative : 0 ≤ ε)
  (linear_error : ∀ f z,
    ‖(D.coordinatePlacement K
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference)
      (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
  {μ : ℝ} (numerical : 2 * ε < μ)
  (margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)

include on_cuts original directions sectors budget pinches start ordered finish
  nonnegative linear_error numerical margin

/-- Strict progress beyond the interval's first height has no exceptional vertex cases. -/
theorem lower_bank_start_strict_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.lower.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
          (N.completedRootPath w).point j s) :
    ∀ h ∈ Set.Ioc a b,
      (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
        (N.completedContour.cycle.point target))).re < (data.value (S.lower.point h)).re := by
  have closed_at : ∀ h ∈ Set.Icc a b, S.lower.point h ∈ closure data.strictDomain := by
    intro h member
    have approached : h ∈ closure (Set.Ioo a b) := (closure_Ioo ordered.ne).symm ▸ member
    exact closure_minimal closed
      (isClosed_closure.preimage S.lower.point_continuous) approached
  have tracked_at := (N.completedRootPath w).tracked_on_closed_interval
    (continuous_const.add ((fiveSectorFrame t positive small i).place.symm.continuous.comp
      S.lower.point_continuous)) ordered tracked
  have weak := B.lower_bank_start_order_on_closed_interval i w on_cuts target original directions
    sectors budget data pinches start ordered finish closed tracked a ⟨le_rfl, ordered.le⟩
  intro h member
  obtain ⟨j, s, first_physical⟩ := tracked_at a ⟨le_rfl, ordered.le⟩
  obtain ⟨k, r, last_physical⟩ := tracked_at h ⟨member.1.le, member.2⟩
  have strict := data.closed_coordinates_strict_on_completed_parent_path nonnegative linear_error
    w directions numerical margin j k s r (closed_at a ⟨le_rfl, ordered.le⟩)
    (closed_at h ⟨member.1.le, member.2⟩) first_physical last_physical
    (by simpa only [S.lower.point_height] using member.1)
  exact weak.trans_lt strict.1

/-- Strict progress beyond the interval's first height has no exceptional vertex cases. -/
theorem upper_bank_start_strict_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.upper.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
          (N.completedRootPath w).point j s) :
    ∀ h ∈ Set.Ioc a b,
      (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
        (N.completedContour.cycle.point target))).im < (data.value (S.upper.point h)).im := by
  have closed_at : ∀ h ∈ Set.Icc a b, S.upper.point h ∈ closure data.strictDomain := by
    intro h member
    have approached : h ∈ closure (Set.Ioo a b) := (closure_Ioo ordered.ne).symm ▸ member
    exact closure_minimal closed
      (isClosed_closure.preimage S.upper.point_continuous) approached
  have tracked_at := (N.completedRootPath w).tracked_on_closed_interval
    (continuous_const.add ((fiveSectorFrame t positive small i).place.symm.continuous.comp
      S.upper.point_continuous)) ordered tracked
  have weak := B.upper_bank_start_order_on_closed_interval i w on_cuts target original directions
    sectors budget data pinches start ordered finish closed tracked a ⟨le_rfl, ordered.le⟩
  intro h member
  obtain ⟨j, s, first_physical⟩ := tracked_at a ⟨le_rfl, ordered.le⟩
  obtain ⟨k, r, last_physical⟩ := tracked_at h ⟨member.1.le, member.2⟩
  have strict := data.closed_coordinates_strict_on_completed_parent_path nonnegative linear_error
    w directions numerical margin j k s r (closed_at a ⟨le_rfl, ordered.le⟩)
    (closed_at h ⟨member.1.le, member.2⟩) first_physical last_physical
    (by simpa only [S.upper.point_height] using member.1)
  exact weak.trans_lt strict.2

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
