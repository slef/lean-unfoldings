module

public import Unfoldings.Cap.CompletedComparisonQuadrants
public import Unfoldings.Geometry.ChainTruncation

/-! Finite comparison-bank prefixes stay in one actual developed source quadrant. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- End the right comparison bank at the same fraction of an actual outward edge
as the physical cut-path prefix. All earlier straight branch gaps are retained. -/
def entranceComparisonPrefix (i : FiveSector) (w : C.Vertex Set.univ) (origin : Plane)
    (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval) :
    PolygonalChain ℂ (2 * terminal.val + 1 + 1) :=
  (B.entranceComparisonChain i w origin).truncate ⟨2 * terminal.val + 1, by omega⟩ parameter

/-- The corresponding left prefix ends at the same actual edge and physical fraction. -/
def exitComparisonPrefix (i : FiveSector) (w : C.Vertex Set.univ) (origin : Plane)
    (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval) :
    PolygonalChain ℂ (2 * terminal.val + 1 + 1) :=
  (B.exitComparisonChain i w origin).truncate ⟨2 * terminal.val + 1, by omega⟩ parameter

variable (i : FiveSector) (w : C.Vertex Set.univ) (center : Plane) (μ radius : ℝ)
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

/-- Every whole comparison-bank point before the chosen physical stopping point lies
in the same source quadrant, including all intermediate branch-gap chords. -/
theorem comparisonChains_before_quadrant
    (k : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) (r : unitInterval)
    (before : PolygonalChain.Before k r ⟨2 * terminal.val + 1, by omega⟩ parameter) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let right := (B.entranceComparisonChain i w origin).point k r - B.sectorFrame i center
    let left := (B.exitComparisonChain i w origin).point k r - B.sectorFrame i center
    (0 ≤ right.re ∧ 0 ≤ right.im) ∧ (0 ≤ left.re ∧ 0 ≤ left.im) := by
  let j : Fin (N.spanningCompletion.parents.distanceToRoot w) := ⟨k.val / 2, by omega⟩
  by_cases even : k.val % 2 = 0
  · have index : k = ⟨2 * j.val, by dsimp only [j]; omega⟩ :=
      Fin.ext (by change k.val = 2 * (k.val / 2); omega)
    have prior : j.val ≤ terminal.val := by
      rcases before with before | ⟨same, _⟩
      · change k.val < 2 * terminal.val + 1 at before
        dsimp only [j]
        omega
      · have values := congrArg Fin.val same
        change k.val = 2 * terminal.val + 1 at values
        dsimp only [j]
        omega
    have bounded := vertices_bounded j.castSucc prior
    have bounds := B.comparisonChains_gap_quadrant_margin i w center μ radius positions
      face_bounds target original j r bounded
    have lower := mul_nonneg nonnegative
      (norm_nonneg (K.projectedVertex (N.completedBankChain w j).val - source))
    dsimp only at bounds ⊢
    rw [index]
    exact ⟨⟨lower.trans bounds.1.1, lower.trans bounds.1.2⟩,
      ⟨lower.trans bounds.2.1, lower.trans bounds.2.2⟩⟩
  · have index : k = ⟨2 * j.val + 1, by dsimp only [j]; omega⟩ :=
      Fin.ext (by change k.val = 2 * (k.val / 2) + 1; omega)
    have prior : PolygonalChain.Before j r terminal parameter := by
      rcases before with before | ⟨same, parameters⟩
      · left
        change k.val < 2 * terminal.val + 1 at before
        change j.val < terminal.val
        dsimp only [j]
        omega
      · right
        have values := congrArg Fin.val same
        change k.val = 2 * terminal.val + 1 at values
        exact ⟨Fin.ext (by change k.val / 2 = terminal.val; omega), parameters⟩
    have bounds := B.comparisonChains_original_quadrant_margin i w center μ radius positions
      face_bounds (D.boundaryPosition (N.completedContour.cycle.point target)) j r
      (points_bounded j r prior)
    have lower := mul_nonneg nonnegative (norm_nonneg ((N.completedRootPath w).point j r - source))
    dsimp only at bounds ⊢
    rw [index]
    exact ⟨⟨lower.trans bounds.1.1, lower.trans bounds.1.2⟩,
      ⟨lower.trans bounds.2.1, lower.trans bounds.2.2⟩⟩

/-- The actual finite prefixes inherit their quadrant bounds at every point, rather
than merely at their original vertices or named bank-edge points. -/
theorem comparisonPrefixes_quadrant (j : Fin (2 * terminal.val + 1 + 1)) (r : unitInterval) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let right := (B.entranceComparisonPrefix i w origin terminal parameter).point j r -
      B.sectorFrame i center
    let left := (B.exitComparisonPrefix i w origin terminal parameter).point j r -
      B.sectorFrame i center
    (0 ≤ right.re ∧ 0 ≤ right.im) ∧ (0 ≤ left.re ∧ 0 ≤ left.im) := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  dsimp only
  constructor
  · obtain ⟨a, u, before, point⟩ :=
      (B.entranceComparisonChain i w origin).truncate_point_covered endpoint parameter j r
    change (0 ≤ (((B.entranceComparisonChain i w origin).truncate endpoint parameter).point j r -
      B.sectorFrame i center).re) ∧
      (0 ≤ (((B.entranceComparisonChain i w origin).truncate endpoint parameter).point j r -
        B.sectorFrame i center).im)
    rw [point]
    exact (B.comparisonChains_before_quadrant i w center μ radius nonnegative positions face_bounds
      target original terminal parameter vertices_bounded points_bounded a u before).1
  · obtain ⟨a, u, before, point⟩ :=
      (B.exitComparisonChain i w origin).truncate_point_covered endpoint parameter j r
    change (0 ≤ (((B.exitComparisonChain i w origin).truncate endpoint parameter).point j r -
      B.sectorFrame i center).re) ∧
      (0 ≤ (((B.exitComparisonChain i w origin).truncate endpoint parameter).point j r -
        B.sectorFrame i center).im)
    rw [point]
    exact (B.comparisonChains_before_quadrant i w center μ radius nonnegative positions face_bounds
      target original terminal parameter vertices_bounded points_bounded a u before).2

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
