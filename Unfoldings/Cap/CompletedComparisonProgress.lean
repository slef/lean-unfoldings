module

public import Unfoldings.Cap.CompletedComparisonChains
public import Unfoldings.Geometry.WeakChainLinear
public import Unfoldings.Geometry.MixedBankOrder

/-! Complete actual comparison banks progress even through their straight branch gaps. -/

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

include original sectors budget

theorem entranceComparisonChain_gap_progress
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    let gap := (B.entranceComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).edge ⟨2 * j.val, by omega⟩
    0 ≤ gap.re ∧ gap.im ≤ 0 ∧ (gap.re = 0 → gap = 0) := by
  obtain ⟨a, vertex, gap⟩ := B.entranceComparisonChain_gap_copy i w target original j
  dsimp only
  rw [gap]
  have order := B.vertex_entrance_gap_order i (N.completedBankChain w j) (sectors j)
    budget.le a vertex
  have flat := B.vertex_entrance_horizontal_eq_iff i (N.completedBankChain w j)
    (sectors j) budget a vertex
  simp only [map_sub, Complex.sub_re, Complex.sub_im] at order ⊢
  refine ⟨by linarith [order.1], by linarith [order.2], ?_⟩
  intro zero
  have equal := flat.mp (by rw [map_sub, Complex.sub_re]; linarith)
  rw [equal, sub_self]

theorem exitComparisonChain_gap_progress
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    let gap := (B.exitComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).edge ⟨2 * j.val, by omega⟩
    gap.re ≤ 0 ∧ 0 ≤ gap.im ∧ (gap.im = 0 → gap = 0) := by
  obtain ⟨a, vertex, gap⟩ := B.exitComparisonChain_gap_copy i w target original j
  dsimp only
  rw [gap]
  have order := B.vertex_exit_gap_order i (N.completedBankChain w j) (sectors j)
    budget.le a vertex
  refine ⟨order.1, order.2, ?_⟩
  intro zero
  have equal := (B.vertex_exit_vertical_eq_iff i (N.completedBankChain w j)
    (sectors j) budget a vertex).mp zero
  rw [equal, sub_self, map_zero]

/-- Matched increments have mixed coordinate order, and a controlling-coordinate
zero step is genuinely flat. All signs and flatness follow from the actual contour. -/
theorem comparisonChains_increment_order
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (k : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let left := (B.exitComparisonChain i w origin).edge k
    let right := (B.entranceComparisonChain i w origin).edge k
    0 ≤ right.re ∧ (right.re = 0 → right = 0) ∧
      0 ≤ left.im ∧ (left.im = 0 → left = 0) ∧
      left.re ≤ right.re ∧ right.im ≤ left.im := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let relation := fun left right : ℂ =>
    0 ≤ right.re ∧ (right.re = 0 → right = 0) ∧
      0 ≤ left.im ∧ (left.im = 0 → left = 0) ∧
      left.re ≤ right.re ∧ right.im ≤ left.im
  change relation ((B.exitComparisonChain i w origin).edge k)
    ((B.entranceComparisonChain i w origin).edge k)
  apply PolygonalChain.interleavedSegments_paired_edges
  · intro j
    have right := B.entranceComparisonChain_gap_progress i w target original sectors budget j
    have left := B.exitComparisonChain_gap_progress i w target original sectors budget j
    dsimp only at right left
    rw [entranceComparisonChain, PolygonalChain.interleavedSegments_gap_edge] at right
    rw [exitComparisonChain, PolygonalChain.interleavedSegments_gap_edge] at left
    exact ⟨right.1, right.2.2, left.2.1, left.2.2,
      left.1.trans right.1, right.2.1.trans left.2.1⟩
  · intro j
    have right := B.entranceComparisonChain_original_edge i w origin j
    have left := B.exitComparisonChain_original_edge i w origin j
    rw [entranceComparisonChain, PolygonalChain.interleavedSegments_original_edge] at right
    rw [exitComparisonChain, PolygonalChain.interleavedSegments_original_edge] at left
    rw [right, left]
    have quadrants := B.parent_vectors_quadrant i (N.completedBankChain w j) (directions j)
    have order := B.parent_vector_order i (N.parentBankOpening D (N.completedBankChain w j))
      (directions j) budget.le
    change (B.sectorFrame i (N.parentExitVector D (N.completedBankChain w j))).re ≤
        (B.sectorFrame i (N.parentEntryVector D (N.completedBankChain w j))).re ∧
      (B.sectorFrame i (N.parentEntryVector D (N.completedBankChain w j))).im ≤
        (B.sectorFrame i (N.parentExitVector D (N.completedBankChain w j))).im at order
    exact ⟨quadrants.1.1.le, fun zero => (ne_of_gt quadrants.1.1 zero).elim,
      quadrants.2.2.le, fun zero => (ne_of_gt quadrants.2.2 zero).elim, order⟩

variable (directions : ∀ j, K.projectedVertex
  (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
    K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)

include directions

/-- The entire right comparison bank is distinguished by its horizontal coordinate,
including all gap segments and their repeated endpoints. -/
theorem entranceComparisonChain_point_eq_of_horizontal_eq
    (j k : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    (equal : ((B.entranceComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point j s).re =
        ((B.entranceComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point k r).re) :
    (B.entranceComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point j s =
        (B.entranceComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point k r := by
  let order := B.comparisonChains_increment_order i w target original sectors budget directions
  exact PolygonalChain.point_eq_of_weak_linear_eq _ Complex.reCLM.toLinearMap
    (fun k => (order k).1) (fun k => (order k).2.1) j k s r equal

/-- The entire left comparison bank is distinguished by its vertical coordinate. -/
theorem exitComparisonChain_point_eq_of_vertical_eq
    (j k : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    (equal : ((B.exitComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point j s).im =
        ((B.exitComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point k r).im) :
    (B.exitComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point j s =
        (B.exitComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point k r := by
  let order := B.comparisonChains_increment_order i w target original sectors budget directions
  exact PolygonalChain.point_eq_of_weak_linear_eq _ Complex.imCLM.toLinearMap
    (fun k => (order k).2.2.1) (fun k => (order k).2.2.2.1) j k s r equal

/-- Opposite complete comparison banks have the correct circle order whenever the
two tested points lie in the same source quadrant. Branch gaps need not be radial. -/
theorem comparisonChains_circle_order (center : ℂ)
    (j k : Fin (2 * N.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    (left_quadrant :
      0 ≤ ((B.exitComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).point j s - center).re ∧
      0 ≤ ((B.exitComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).point j s - center).im)
    (right_quadrant :
      0 ≤ ((B.entranceComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).point k r - center).re ∧
      0 ≤ ((B.entranceComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).point k r - center).im)
    (same_radius : ‖(B.exitComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point j s - center‖ =
        ‖(B.entranceComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point k r - center‖) :
    ((B.exitComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point j s - center).re ≤
        ((B.entranceComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point k r - center).re ∧
    ((B.entranceComparisonChain i w
      (D.boundaryPosition (N.completedContour.cycle.point target))).point k r - center).im ≤
        ((B.exitComparisonChain i w
          (D.boundaryPosition (N.completedContour.cycle.point target))).point j s - center).im := by
  let order := B.comparisonChains_increment_order i w target original sectors budget directions
  exact PolygonalChain.circle_order_of_mixed_increments
    (B.exitComparisonChain i w (D.boundaryPosition (N.completedContour.cycle.point target)))
    (B.entranceComparisonChain i w (D.boundaryPosition (N.completedContour.cycle.point target))) rfl
    (fun k => (order k).2.2.2.2.1) (fun k => (order k).2.2.2.2.2)
    (fun k => (order k).1) (fun k => (order k).2.2.1) center j k s r
    left_quadrant right_quadrant same_radius

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
