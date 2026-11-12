module

public import Unfoldings.Cap.CompletedComparisonPrefixes
public import Unfoldings.Cap.CompletedComparisonProgress

/-! Actual bounded comparison prefixes have ordered source-circle intersections. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)
  (i : FiveSector) (w : C.Vertex Set.univ) (center : Plane) (μ radius : ℝ)
  (nonnegative : 0 ≤ μ)
  (positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
    (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i)
  (face_bounds : ∀ f (p : Plane), p ∈ (K.projectedTriangle f).carrier →
    ‖p - source‖ ≤ radius → p - source ∈ closedFiveSector t i →
    μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).re ∧
      μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).im)
  (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
  (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval)
  (vertices_bounded : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
    j.val ≤ terminal.val → ‖(N.completedRootPath w).vertex j - source‖ ≤ radius)
  (points_bounded : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
    PolygonalChain.Before j r terminal parameter →
      ‖(N.completedRootPath w).point j r - source‖ ≤ radius)

include nonnegative positions face_bounds original vertices_bounded points_bounded

/-- All source-circle intersections of the opposite finite comparison banks have
the proved order. Their quadrant hypotheses follow from the actual physical prefix. -/
theorem comparisonPrefixes_circle_order
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let left := B.exitComparisonPrefix i w origin terminal parameter
    let right := B.entranceComparisonPrefix i w origin terminal parameter
    let source := B.sectorFrame i center
    ∀ j k : Fin (2 * terminal.val + 1 + 1), ∀ s r : unitInterval,
      ‖left.point j s - source‖ = ‖right.point k r - source‖ →
      (left.point j s - source).re ≤ (right.point k r - source).re ∧
        (right.point k r - source).im ≤ (left.point j s - source).im := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  refine fun j k s r equal => ?_
  obtain ⟨a, u, left_before, left_point⟩ :=
    (B.exitComparisonChain i w origin).truncate_point_covered endpoint parameter j s
  obtain ⟨b, v, right_before, right_point⟩ :=
    (B.entranceComparisonChain i w origin).truncate_point_covered endpoint parameter k r
  have left_quadrant := (B.comparisonChains_before_quadrant i w center μ radius nonnegative
    positions face_bounds target original terminal parameter vertices_bounded points_bounded
    a u left_before).2
  have right_quadrant := (B.comparisonChains_before_quadrant i w center μ radius nonnegative
    positions face_bounds target original terminal parameter vertices_bounded points_bounded
    b v right_before).1
  change ‖((B.exitComparisonChain i w origin).truncate endpoint parameter).point j s -
    B.sectorFrame i center‖ =
      ‖((B.entranceComparisonChain i w origin).truncate endpoint parameter).point k r -
        B.sectorFrame i center‖ at equal
  rw [left_point, right_point] at equal
  have order := B.comparisonChains_circle_order i w target original sectors budget directions
    (B.sectorFrame i center) a b u v left_quadrant right_quadrant equal
  change ((((B.exitComparisonChain i w origin).truncate endpoint parameter).point j s -
      B.sectorFrame i center).re ≤
    (((B.entranceComparisonChain i w origin).truncate endpoint parameter).point k r -
      B.sectorFrame i center).re) ∧
    ((((B.entranceComparisonChain i w origin).truncate endpoint parameter).point k r -
      B.sectorFrame i center).im ≤
    (((B.exitComparisonChain i w origin).truncate endpoint parameter).point j s -
      B.sectorFrame i center).im)
  rw [left_point, right_point]
  exact order

omit nonnegative original vertices_bounded points_bounded in
/-- At the physical stopping radius, both developed endpoints retain a quantitative
source-quadrant margin. Choosing a far physical radius makes these endpoints far too. -/
theorem comparisonPrefixes_last_margin
    (at_radius : ‖(N.completedRootPath w).point terminal parameter - source‖ = radius) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let left := B.exitComparisonPrefix i w origin terminal parameter
    let right := B.entranceComparisonPrefix i w origin terminal parameter
    let center := B.sectorFrame i center
    (μ * radius ≤ (right.vertex (Fin.last (2 * terminal.val + 1 + 1)) - center).re ∧
      μ * radius ≤ (right.vertex (Fin.last (2 * terminal.val + 1 + 1)) - center).im) ∧
    (μ * radius ≤ (left.vertex (Fin.last (2 * terminal.val + 1 + 1)) - center).re ∧
      μ * radius ≤ (left.vertex (Fin.last (2 * terminal.val + 1 + 1)) - center).im) := by
  have bounds := B.comparisonChains_original_quadrant_margin i w center μ radius positions
    face_bounds
    (D.boundaryPosition (N.completedContour.cycle.point target)) terminal parameter at_radius.le
  dsimp only at bounds ⊢
  rw [at_radius] at bounds
  dsimp only [entranceComparisonPrefix, exitComparisonPrefix]
  rw [PolygonalChain.truncate_vertex_last, PolygonalChain.truncate_vertex_last]
  exact bounds

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
