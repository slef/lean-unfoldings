module

public import Unfoldings.Cap.PositiveWidthBankStartOrder
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.RecoverableStripClosure

/-! Bank progress extends through every branch vertex and terminal endpoint by continuity. -/

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

include on_cuts original directions sectors budget pinches start ordered finish

/-- Finite physical vertex heights are removed only for chart matching. The
actual lower trace and its endpoint values retain the resulting order everywhere. -/
theorem lower_bank_start_order_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.lower.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
          (N.completedRootPath w).point j s) :
    ∀ h ∈ Set.Icc a b,
      (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
        (N.completedContour.cycle.point target))).re ≤ (data.value (S.lower.point h)).re := by
  let frame := (fiveSectorFrame t positive small i).place
  let bound := (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
    (N.completedContour.cycle.point target))).re
  have closed_order : IsClosed {h : ℝ | bound ≤ (data.value (S.lower.point h)).re} :=
    isClosed_le continuous_const
      (Complex.continuous_re.comp (data.continuous.comp S.lower.point_continuous))
  have good : Set.Ioo a b \ K.framedVertexHeights source frame ⊆
      {h : ℝ | bound ≤ (data.value (S.lower.point h)).re} := by
    intro h member
    have regular := K.regular_of_not_framedVertexHeights source frame
      (z := S.lower.point h) (by simpa only [S.lower.point_height] using member.2)
    have height : h ∈ Set.Ioo 0 cutoff :=
      ⟨start.trans_lt member.1.1, member.1.2.trans_le finish⟩
    have width := data.width_pos_of_approached_regular pinches height (closed h member.1) regular
    obtain ⟨j, s, physical⟩ := tracked h member.1
    exact B.lower_bank_start_order i w on_cuts target original directions sectors budget data
      height width j s regular physical
  exact (Icc_subset_closure_Ioo_sdiff_finite ordered
    (K.finite_framedVertexHeights source frame)).trans (closure_minimal good closed_order)

/-- The corresponding upper trace is bounded vertically at all heights,
including vertices where its regular bank chart cannot be selected directly. -/
theorem upper_bank_start_order_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.upper.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
          (N.completedRootPath w).point j s) :
    ∀ h ∈ Set.Icc a b,
      (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
        (N.completedContour.cycle.point target))).im ≤ (data.value (S.upper.point h)).im := by
  let frame := (fiveSectorFrame t positive small i).place
  let bound := (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
    (N.completedContour.cycle.point target))).im
  have closed_order : IsClosed {h : ℝ | bound ≤ (data.value (S.upper.point h)).im} :=
    isClosed_le continuous_const
      (Complex.continuous_im.comp (data.continuous.comp S.upper.point_continuous))
  have good : Set.Ioo a b \ K.framedVertexHeights source frame ⊆
      {h : ℝ | bound ≤ (data.value (S.upper.point h)).im} := by
    intro h member
    have regular := K.regular_of_not_framedVertexHeights source frame
      (z := S.upper.point h) (by simpa only [S.upper.point_height] using member.2)
    have height : h ∈ Set.Ioo 0 cutoff :=
      ⟨start.trans_lt member.1.1, member.1.2.trans_le finish⟩
    have width := data.width_pos_of_upper_approached_regular pinches height
      (closed h member.1) regular
    obtain ⟨j, s, physical⟩ := tracked h member.1
    exact B.upper_bank_start_order i w on_cuts target original directions sectors budget data
      height width j s regular physical
  exact (Icc_subset_closure_Ioo_sdiff_finite ordered
    (K.finite_framedVertexHeights source frame)).trans (closure_minimal good closed_order)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
