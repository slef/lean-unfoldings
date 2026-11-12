module

public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Cap.ProperComparisonData

/-! Actual bounded parent banks construct proper comparison data in a specified sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- Both the chosen actual starting copy and the specified sector are retained. -/
theorem exists_proper_comparison_data_in_sector (i : FiveSector) (outward : N.Outward)
    (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
    (center : Plane) (μ radius : ℝ) (nonnegative : 0 ≤ μ)
    (start : ‖K.projectedVertex w - source‖ < radius)
    (deep : Metric.closedBall source radius ⊆ interior K.footprint)
    (positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
      (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i)
    (directions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
    (face_bounds : ∀ f (p : Plane), p ∈ (K.projectedTriangle f).carrier →
      ‖p - source‖ ≤ radius → p - source ∈ closedFiveSector t i →
      μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).re ∧
        μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).im)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (target : Fin (N.completedContour.length + 1))
    (original : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
    (circle : ℝ)
    (near : ‖D.boundaryPosition (N.completedContour.cycle.point target) - center‖ < circle)
    (far : circle < μ * radius) :
    ∃ data : B.ProperComparisonData w target center radius circle, data.sector = i := by
  have distance (p : Plane) : dist source p = ‖p - source‖ :=
    (dist_comm _ _).trans (dist_eq_norm _ _)
  obtain ⟨terminal, parameter, endpoint, vertices, points⟩ :=
    N.completedRootPath_exists_radius_prefix outward on_cuts radius
      (by rw [distance]; exact start) deep
  have endpoint_norm : ‖(N.completedRootPath w).point terminal parameter - source‖ = radius :=
    (distance _).symm.trans endpoint
  have vertices_norm : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
      j.val ≤ terminal.val → ‖(N.completedRootPath w).vertex j - source‖ ≤ radius :=
    fun j before => (distance _).symm.trans_le (vertices j before)
  have points_norm : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
      PolygonalChain.Before j r terminal parameter →
        ‖(N.completedRootPath w).point j r - source‖ ≤ radius :=
    fun j r before => (distance _).symm.trans_le (points j r before)
  obtain ⟨right, left, right_image, left_image, _, order⟩ := B.exists_proper_comparison_arcs
    i w center μ radius nonnegative positions face_bounds target original sectors budget directions
    terminal parameter endpoint_norm vertices_norm points_norm circle near far
  exact ⟨{
    sector := i
    terminal := terminal
    parameter := parameter
    original := original
    endpoint_radius := endpoint_norm
    positions := positions
    vertices_bounded := vertices_norm
    points_bounded := points_norm
    right := right
    left := left
    right_image := right_image
    left_image := left_image
    circle_order := order }, rfl⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
