module

public import Unfoldings.Cap.MatchedBankAtHeight
public import Unfoldings.Cap.RadialStripTraceData
public import Unfoldings.Cap.CompletedChartComparisonPoints

/-! Actual positive-width strip traces inherit the matched parent-bank gap order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

/-- The same physical parameter selects the exit chart on the left and entrance
chart on the right. Weak coordinate order permits a flat cut's bank contact. -/
theorem matched_strip_bank_point_order (i : FiveSector) {S T : MonotoneStrip} {ε cutoff : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (same_point : S.upper.point h = T.lower.point h)
    (first_width : S.lower.coordinate h < S.upper.coordinate h)
    (last_width : T.lower.coordinate h < T.upper.coordinate h)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (on_cuts : K.projectedVertex e.val ∈ cuts)
    (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sector : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (s : unitInterval)
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ≠ (K.projectedTriangle f).vertex j)
    (physical : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
      AffineMap.lineMap (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) (s : ℝ)) :
    (data.value (S.upper.point h)).re ≤ (other.value (T.lower.point h)).re ∧
      (other.value (T.lower.point h)).im ≤ (data.value (S.upper.point h)).im := by
  let completed := N.completedDevelopment D
  have member : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) ∈
      segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) := by
    rw [physical]
    exact lineMap_mem_segment ℝ _ _ s.property
  have first := (data.bank_matching.at_positive_width height first_width e on_cuts direction).2
    regular member
  have last := (other.bank_matching.at_positive_width height last_width e on_cuts direction).1
    (by rw [← same_point]; exact regular) (by rw [← same_point]; exact member)
  have exit_value : data.value (S.upper.point h) =
      B.sectorFrame i (N.parentExitPoint completed e (1 - (s : ℝ))) := by
    rw [first, B.centered_coordinate_eq_sectorFrame, physical,
      N.parentExitPoint_eq_projectedPlacement, AffineMap.lineMap_apply_one_sub]
  have entrance_value : other.value (T.lower.point h) =
      B.sectorFrame i (N.parentEntrancePoint completed e (1 - (s : ℝ))) := by
    rw [last, B.centered_coordinate_eq_sectorFrame, ← same_point, physical,
      N.parentEntrancePoint_eq_projectedPlacement, AffineMap.lineMap_apply_one_sub]
  rw [exit_value, entrance_value]
  exact B.matched_bank_points_order i e sector (1 - (s : ℝ)) (by linarith [s.property.1]) budget

/-- Retain the shared-whole-wall interface. -/
theorem matched_strip_bank_order (i : FiveSector) {S T : MonotoneStrip} {ε cutoff : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (wall : S.upper = T.lower) {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (first_width : S.lower.coordinate h < S.upper.coordinate h)
    (last_width : T.lower.coordinate h < T.upper.coordinate h)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (on_cuts : K.projectedVertex e.val ∈ cuts)
    (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sector : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (s : unitInterval)
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ≠ (K.projectedTriangle f).vertex j)
    (physical : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
      AffineMap.lineMap (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) (s : ℝ)) :
    (data.value (S.upper.point h)).re ≤ (other.value (T.lower.point h)).re ∧
      (other.value (T.lower.point h)).im ≤ (data.value (S.upper.point h)).im := by
  exact B.matched_strip_bank_point_order i data other height (by rw [wall])
    first_width last_width e on_cuts direction sector budget s regular physical

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
