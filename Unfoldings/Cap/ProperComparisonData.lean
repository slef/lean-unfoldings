module

public import Unfoldings.Cap.ProperComparisonArcs

/-! Constructed finite proper comparison arcs retain their actual path and contour provenance. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- Output data for the proved proper-arc construction. The curves retain their
actual contour start and finite parent-bank images; no global strip separation is asserted. -/
structure ProperComparisonData (w : C.Vertex Set.univ)
    (target : Fin (N.completedContour.length + 1)) (center : Plane) (radius circle : ℝ) where
  sector : FiveSector
  terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)
  parameter : unitInterval
  original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w
  endpoint_radius : ‖(N.completedRootPath w).point terminal parameter - source‖ = radius
  positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
    (N.completedRootPath w).vertex j - source ∈ closedFiveSector t sector
  vertices_bounded : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
    j.val ≤ terminal.val → ‖(N.completedRootPath w).vertex j - source‖ ≤ radius
  points_bounded : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
    PolygonalChain.Before j r terminal parameter →
      ‖(N.completedRootPath w).point j r - source‖ ≤ radius
  right : SphereArc (B.sectorFrame sector center)
    (B.sectorFrame sector (D.boundaryPosition (N.completedContour.cycle.point target))) circle
  left : SphereArc (B.sectorFrame sector center)
    (B.sectorFrame sector (D.boundaryPosition (N.completedContour.cycle.point target))) circle
  right_image : Set.range right.curve ⊆ Set.range
    (B.entranceComparisonPrefix sector w
      (D.boundaryPosition (N.completedContour.cycle.point target))
      terminal parameter).path
  left_image : Set.range left.curve ⊆ Set.range
    (B.exitComparisonPrefix sector w
      (D.boundaryPosition (N.completedContour.cycle.point target))
      terminal parameter).path
  circle_order : ∀ s r : unitInterval,
    ‖left.curve s - B.sectorFrame sector center‖ = ‖right.curve r - B.sectorFrame sector center‖ →
    (left.curve s - B.sectorFrame sector center).re ≤
        (right.curve r - B.sectorFrame sector center).re ∧
      (right.curve r - B.sectorFrame sector center).im ≤
        (left.curve s - B.sectorFrame sector center).im

theorem ProperComparisonData.endpoint_order {w : C.Vertex Set.univ}
    {target : Fin (N.completedContour.length + 1)} {center : Plane} {radius circle : ℝ}
    (data : B.ProperComparisonData w target center radius circle) :
    (data.left.finish - B.sectorFrame data.sector center).re ≤
        (data.right.finish - B.sectorFrame data.sector center).re ∧
      (data.right.finish - B.sectorFrame data.sector center).im ≤
        (data.left.finish - B.sectorFrame data.sector center).im := by
  have left_on : ‖data.left.finish - B.sectorFrame data.sector center‖ = circle := by
    simpa only [dist_eq_norm, norm_sub_rev] using data.left.on_sphere
  have right_on : ‖data.right.finish - B.sectorFrame data.sector center‖ = circle := by
    simpa only [dist_eq_norm, norm_sub_rev] using data.right.on_sphere
  have order := data.circle_order 1 1 (by
    rw [data.left.curve.target, data.right.curve.target, left_on, right_on])
  simpa only [data.left.curve.target, data.right.curve.target] using order

theorem ProperComparisonData.quadrants {w : C.Vertex Set.univ}
    {target : Fin (N.completedContour.length + 1)} {center : Plane} {radius circle : ℝ}
    (data : B.ProperComparisonData w target center radius circle) (μ : ℝ) (nonnegative : 0 ≤ μ)
    (face_bounds : ∀ f (p : Plane), p ∈ (K.projectedTriangle f).carrier →
      ‖p - source‖ ≤ radius → p - source ∈ closedFiveSector t data.sector →
      μ * ‖p - source‖ ≤ (B.sectorFrame data.sector (D.projectedPlacement K f p - center)).re ∧
        μ * ‖p - source‖ ≤ (B.sectorFrame data.sector (D.projectedPlacement K f p - center)).im)
    (s : unitInterval) :
    (0 ≤ (data.right.curve s - B.sectorFrame data.sector center).re ∧
      0 ≤ (data.right.curve s - B.sectorFrame data.sector center).im) ∧
    (0 ≤ (data.left.curve s - B.sectorFrame data.sector center).re ∧
      0 ≤ (data.left.curve s - B.sectorFrame data.sector center).im) := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let R := B.entranceComparisonPrefix data.sector w origin data.terminal data.parameter
  let L := B.exitComparisonPrefix data.sector w origin data.terminal data.parameter
  have quarters := B.comparisonPrefixes_quadrant data.sector w center μ radius nonnegative
    data.positions face_bounds target data.original data.terminal data.parameter
    data.vertices_bounded data.points_bounded
  constructor
  · obtain ⟨u, value⟩ := data.right_image (Set.mem_range_self s)
    obtain ⟨j, r, covered⟩ := R.path_point_covered (by omega) u
    rw [← value, covered]
    exact (quarters j r).1
  · obtain ⟨u, value⟩ := data.left_image (Set.mem_range_self s)
    obtain ⟨j, r, covered⟩ := L.path_point_covered (by omega) u
    rw [← value, covered]
    exact (quarters j r).2

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
