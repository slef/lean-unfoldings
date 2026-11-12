module

public import Unfoldings.Cap.CompletedComparisonValues
public import Unfoldings.Geometry.QuadrantSegments

/-! Common-source quadrant margins for actual bank edges and straight branch-copy gaps. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)

theorem completedRootPath_point_bankChain (w : C.Vertex Set.univ)
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    (N.completedRootPath w).point j s = AffineMap.lineMap
      (K.projectedVertex (N.completedBankChain w j).val)
      (K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val))
      (s : ℝ) := by
  change AffineMap.lineMap _
    (K.projectedVertex (N.spanningCompletion.parents.parent^[j.val + 1] w)) (s : ℝ) = _
  rw [Function.iterate_succ_apply']
  rfl

theorem completedRootPath_point_in_sector {t : ℝ} (i : FiveSector) (w : C.Vertex Set.univ)
    (positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
      (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i)
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    (N.completedRootPath w).point j s - source ∈ closedFiveSector t i :=
  (positions j.castSucc).sub_of_mem_segment (positions j.succ)
    (lineMap_mem_segment ℝ _ _ s.property)

namespace FiveSectorFrameData

variable {N} {D : FacewiseDevelopment C N.completedRetain}
  {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)
  (i : FiveSector) (w : C.Vertex Set.univ) (center : Plane) (μ radius : ℝ)
  (positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
    (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i)
  (face_bounds : ∀ f (p : Plane), p ∈ (K.projectedTriangle f).carrier →
    ‖p - source‖ ≤ radius → p - source ∈ closedFiveSector t i →
    μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).re ∧
      μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).im)

include positions face_bounds

/-- Both original bank-edge values have the actual physical point's quantitative
source-quadrant margin. The source is shared by every bank. -/
theorem comparisonChains_original_quadrant_margin (origin : Plane)
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval)
    (bounded : ‖(N.completedRootPath w).point j s - source‖ ≤ radius) :
    let p := (N.completedRootPath w).point j s
    let right := (B.entranceComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s -
      B.sectorFrame i center
    let left := (B.exitComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s -
      B.sectorFrame i center
    (μ * ‖p - source‖ ≤ right.re ∧ μ * ‖p - source‖ ≤ right.im) ∧
      (μ * ‖p - source‖ ≤ left.re ∧ μ * ‖p - source‖ ≤ left.im) := by
  have physical := N.completedRootPath_point_bankChain w j s
  have reverse : AffineMap.lineMap
      (K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val))
      (K.projectedVertex (N.completedBankChain w j).val) (1 - (s : ℝ)) =
        (N.completedRootPath w).point j s := by
    rw [AffineMap.lineMap_apply_one_sub, physical]
  have parameter : 1 - (s : ℝ) ∈ Set.Icc 0 1 :=
    ⟨by linarith [s.property.2], by linarith [s.property.1]⟩
  have faces := N.parent_bank_points_mem_faces D (N.completedBankChain w j) parameter
  rw [reverse] at faces
  have cone := N.completedRootPath_point_in_sector i w positions j s
  have first := face_bounds (N.parentBankOpening D (N.completedBankChain w j)).entranceFace
    _ faces.1 bounded cone
  have last := face_bounds (N.parentBankOpening D (N.completedBankChain w j)).exitFace
    _ faces.2 bounded cone
  dsimp only
  rw [B.entranceComparisonChain_original_point, B.exitComparisonChain_original_point,
    N.parentEntrancePoint_eq_projectedPlacement D, N.parentExitPoint_eq_projectedPlacement D,
    reverse, ← map_sub, ← map_sub]
  exact ⟨first, last⟩

variable (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)

include original

/-- Every straight branch gap keeps the same positive margin as its physical vertex;
no radial monotonicity of that chord is asserted. -/
theorem comparisonChains_gap_quadrant_margin
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval)
    (bounded : ‖K.projectedVertex (N.completedBankChain w j).val - source‖ ≤ radius) :
    let p := K.projectedVertex (N.completedBankChain w j).val
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let right := (B.entranceComparisonChain i w origin).point ⟨2 * j.val, by omega⟩ s -
      B.sectorFrame i center
    let left := (B.exitComparisonChain i w origin).point ⟨2 * j.val, by omega⟩ s -
      B.sectorFrame i center
    (μ * ‖p - source‖ ≤ right.re ∧ μ * ‖p - source‖ ≤ right.im) ∧
      (μ * ‖p - source‖ ≤ left.re ∧ μ * ‖p - source‖ ≤ left.im) := by
  have cone := positions j.castSucc
  change K.projectedVertex (N.completedBankChain w j).val - source ∈ _ at cone
  obtain ⟨f, g, first_face, last_face, right⟩ :=
    B.entranceComparisonChain_gap_face_values i w target original j s
  obtain ⟨h, k, other_first, other_last, left⟩ :=
    B.exitComparisonChain_gap_face_values i w target original j s
  dsimp only
  rw [right, left, ← map_sub, ← map_sub]
  constructor
  · exact lineMap_frame_sub_quadrant_lower_bound (B.sectorFrame i).toLinearEquiv.toLinearMap
      center _ _ _ s.property
      (face_bounds f _ first_face bounded cone) (face_bounds g _ last_face bounded cone)
  · exact lineMap_frame_sub_quadrant_lower_bound (B.sectorFrame i).toLinearEquiv.toLinearMap
      center _ _ _ s.property
      (face_bounds h _ other_first bounded cone) (face_bounds k _ other_last bounded cone)

end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
