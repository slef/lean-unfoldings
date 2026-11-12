module

public import Unfoldings.Cap.CompletedComparisonStartOrder
public import Unfoldings.Cap.MatchedBankAtHeight
public import Unfoldings.Cap.CompletedChartComparisonPoints
public import Unfoldings.Cap.RadialStripTraceData

/-! Actual regular bank traces progress from a named copy without a circle hypothesis. -/

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
  {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
  (width : S.lower.coordinate h < S.upper.coordinate h)
  (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval)

include on_cuts original directions sectors budget height width

/-- Branch-gap signs control every regular lower-bank point of positive width,
with no assumption about its radius or the rest of its developed strip. -/
theorem lower_bank_start_order
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point h) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
      (N.completedRootPath w).point j s) :
    (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
      (N.completedContour.cycle.point target))).re ≤ (data.value (S.lower.point h)).re := by
  have member : source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) ∈
      segment ℝ (K.projectedVertex (N.completedBankChain w j).val)
        (K.projectedVertex
          (N.spanningCompletion.parents.parent (N.completedBankChain w j).val)) := by
    rw [physical, N.completedRootPath_point_bankChain]
    exact lineMap_mem_segment ℝ _ _ s.property
  have matching := (data.bank_matching.at_positive_width height width (N.completedBankChain w j)
    (N.completedRootPath_vertex_mem on_cuts j.castSucc) (directions j)).1 regular member
  let origin := (N.completedDevelopment D).boundaryPosition (N.completedContour.cycle.point target)
  have value := matching.trans
    (B.centered_entrance_chart_eq_comparison_point i w origin j s _ physical)
  have bound := B.entranceComparisonChain_start_le i w target original sectors budget directions
    ⟨2 * j.val + 1, by omega⟩ s
  dsimp only at bound
  rw [← value] at bound
  exact bound

/-- The corresponding upper-bank trace never lies below the named starting copy. -/
theorem upper_bank_start_order
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
      (N.completedRootPath w).point j s) :
    (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
      (N.completedContour.cycle.point target))).im ≤ (data.value (S.upper.point h)).im := by
  have member : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) ∈
      segment ℝ (K.projectedVertex (N.completedBankChain w j).val)
        (K.projectedVertex
          (N.spanningCompletion.parents.parent (N.completedBankChain w j).val)) := by
    rw [physical, N.completedRootPath_point_bankChain]
    exact lineMap_mem_segment ℝ _ _ s.property
  have matching := (data.bank_matching.at_positive_width height width (N.completedBankChain w j)
    (N.completedRootPath_vertex_mem on_cuts j.castSucc) (directions j)).2 regular member
  let origin := (N.completedDevelopment D).boundaryPosition (N.completedContour.cycle.point target)
  have value := matching.trans
    (B.centered_exit_chart_eq_comparison_point i w origin j s _ physical)
  have bound := B.exitComparisonChain_start_le i w target original sectors budget directions
    ⟨2 * j.val + 1, by omega⟩ s
  dsimp only at bound
  rw [← value] at bound
  exact bound

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
