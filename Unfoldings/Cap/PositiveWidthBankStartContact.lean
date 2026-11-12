module

public import Unfoldings.Cap.PositiveWidthBankStartOrder

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

theorem lower_bank_start_contact
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point h) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
      (N.completedRootPath w).point j s)
    (equal : (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
      (N.completedContour.cycle.point target))).re =
        (data.value (S.lower.point h)).re) :
    data.value (S.lower.point h) =
      B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
        (N.completedContour.cycle.point target)) := by
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
  let start : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨0, by have bounded := j.isLt; omega⟩
  have start_value : (B.entranceComparisonChain i w origin).point start 0 =
      B.sectorFrame i origin := by simp [start, entranceComparisonChain]
  have coordinate : ((B.entranceComparisonChain i w origin).point
      ⟨2 * j.val + 1, by omega⟩ s).re =
      ((B.entranceComparisonChain i w origin).point start 0).re := by
    rw [← value, start_value]
    exact equal.symm
  have same := B.entranceComparisonChain_point_eq_of_horizontal_eq i w target original
    sectors budget directions ⟨2 * j.val + 1, by omega⟩ start s 0 coordinate
  exact value.trans (same.trans start_value)

theorem upper_bank_start_contact
    (regular : ∀ f k, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ≠ (K.projectedTriangle f).vertex k)
    (physical : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
      (N.completedRootPath w).point j s)
    (equal : (B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
      (N.completedContour.cycle.point target))).im =
        (data.value (S.upper.point h)).im) :
    data.value (S.upper.point h) =
      B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
        (N.completedContour.cycle.point target)) := by
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
  let start : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨0, by have bounded := j.isLt; omega⟩
  have start_value : (B.exitComparisonChain i w origin).point start 0 =
      B.sectorFrame i origin := by simp [start, exitComparisonChain]
  have coordinate : ((B.exitComparisonChain i w origin).point
      ⟨2 * j.val + 1, by omega⟩ s).im =
      ((B.exitComparisonChain i w origin).point start 0).im := by
    rw [← value, start_value]
    exact equal.symm
  have same := B.exitComparisonChain_point_eq_of_vertical_eq i w target original
    sectors budget directions ⟨2 * j.val + 1, by omega⟩ start s 0 coordinate
  exact value.trans (same.trans start_value)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
