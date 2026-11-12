module

public import Unfoldings.Cap.CompletedComparisonProgress

/-! Complete comparison banks progress from their own named contour copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)
  (i : FiveSector) (w : C.Vertex Set.univ) (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
  (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
  (directions : ∀ j, K.projectedVertex
    (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
      K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)

include original sectors budget directions

/-- The right comparison bank never goes left of its starting copy, including
points in the straight branch gaps. -/
theorem entranceComparisonChain_start_le
    (j : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    (B.sectorFrame i origin).re ≤ ((B.entranceComparisonChain i w origin).point j s).re := by
  let P := B.entranceComparisonChain i w
    (D.boundaryPosition (N.completedContour.cycle.point target))
  have monotone := (P.monotone_linear_vertices_iff Complex.reCLM.toLinearMap).mpr
    (fun k =>
      (B.comparisonChains_increment_order i w target original sectors budget directions k).1)
  have first := monotone (show (0 : Fin (_ + 1)) ≤ j.castSucc from Nat.zero_le _)
  have next := monotone (Fin.castSucc_le_succ j)
  have value := P.linear_point Complex.reCLM.toLinearMap j s
  have result : (P.vertex 0).re ≤ (P.point j s).re := by
    change (P.vertex 0).re ≤ (P.vertex j.castSucc).re at first
    change (P.vertex j.castSucc).re ≤ (P.vertex j.succ).re at next
    change (P.point j s).re =
      (1 - (s : ℝ)) * (P.vertex j.castSucc).re + (s : ℝ) * (P.vertex j.succ).re at value
    nlinarith [s.property.1]
  exact result

/-- The left comparison bank never goes below its starting copy. -/
theorem exitComparisonChain_start_le
    (j : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    (B.sectorFrame i origin).im ≤ ((B.exitComparisonChain i w origin).point j s).im := by
  let P := B.exitComparisonChain i w
    (D.boundaryPosition (N.completedContour.cycle.point target))
  have monotone := (P.monotone_linear_vertices_iff Complex.imCLM.toLinearMap).mpr
    (fun k =>
      (B.comparisonChains_increment_order i w target original sectors budget directions k).2.2.1)
  have first := monotone (show (0 : Fin (_ + 1)) ≤ j.castSucc from Nat.zero_le _)
  have next := monotone (Fin.castSucc_le_succ j)
  have value := P.linear_point Complex.imCLM.toLinearMap j s
  have result : (P.vertex 0).im ≤ (P.point j s).im := by
    change (P.vertex 0).im ≤ (P.vertex j.castSucc).im at first
    change (P.vertex j.castSucc).im ≤ (P.vertex j.succ).im at next
    change (P.point j s).im =
      (1 - (s : ℝ)) * (P.vertex j.castSucc).im + (s : ℝ) * (P.vertex j.succ).im at value
    nlinarith [s.property.1]
  exact result

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
