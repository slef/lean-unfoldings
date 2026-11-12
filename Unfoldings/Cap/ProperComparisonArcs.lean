module

public import Unfoldings.Cap.SimpleComparisonPaths
public import Unfoldings.Topology.SphereArc

/-! Simple actual comparison subarcs stop on a common source circle with proved bank order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- Construct the simple arcs from the actual comparison-bank images. Their interiors
stay inside the source circle, their ends lie on it in the derived opposite-bank order,
and the entire arcs retain that order on every common source circle. -/
theorem exists_proper_comparison_arcs (i : FiveSector) (w : C.Vertex Set.univ) (center : Plane)
    (μ radius : ℝ) (nonnegative : 0 ≤ μ)
    (positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
      (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i)
    (face_bounds : ∀ f (p : Plane), p ∈ (K.projectedTriangle f).carrier →
      ‖p - source‖ ≤ radius → p - source ∈ closedFiveSector t i →
      μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).re ∧
        μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).im)
    (target : Fin (N.completedContour.length + 1))
    (original : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval)
    (at_radius : ‖(N.completedRootPath w).point terminal parameter - source‖ = radius)
    (vertices_bounded : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
      j.val ≤ terminal.val → ‖(N.completedRootPath w).vertex j - source‖ ≤ radius)
    (points_bounded : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
      PolygonalChain.Before j r terminal parameter →
        ‖(N.completedRootPath w).point j r - source‖ ≤ radius)
    (circle : ℝ)
    (start : ‖D.boundaryPosition (N.completedContour.cycle.point target) - center‖ < circle)
    (finish : circle < μ * radius) :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let R := B.entranceComparisonPrefix i w origin terminal parameter
    let L := B.exitComparisonPrefix i w origin terminal parameter
    let c := B.sectorFrame i center
    ∃ right left : SphereArc c (B.sectorFrame i origin) circle,
      Set.range right.curve ⊆ Set.range R.path ∧ Set.range left.curve ⊆ Set.range L.path ∧
      ((left.finish - c).re ≤ (right.finish - c).re ∧
        (right.finish - c).im ≤ (left.finish - c).im) ∧
      ∀ s r : unitInterval, ‖left.curve s - c‖ = ‖right.curve r - c‖ →
        (left.curve s - c).re ≤ (right.curve r - c).re ∧
          (right.curve r - c).im ≤ (left.curve s - c).im := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let R := B.entranceComparisonPrefix i w origin terminal parameter
  let L := B.exitComparisonPrefix i w origin terminal parameter
  let c := B.sectorFrame i center
  obtain ⟨right, left, right_simple, left_simple, right_range, left_range⟩ :=
    B.exists_simple_comparison_prefix_paths i w center μ radius positions face_bounds target
      terminal parameter at_radius (start.trans finish) original sectors budget directions
  let rpath := right.cast (B.entranceComparisonPrefix_start i w origin terminal parameter).symm rfl
  let lpath := left.cast (B.exitComparisonPrefix_start i w origin terminal parameter).symm rfl
  have first_distance : dist c (B.sectorFrame i origin) = ‖origin - center‖ := by
    rw [dist_eq_norm, ← map_sub, (B.sectorFrame i).norm_map, norm_sub_rev]
  have margins := B.comparisonPrefixes_last_margin i w center μ radius positions face_bounds target
    terminal parameter at_radius
  have right_distance : μ * radius ≤ dist c (R.vertex (Fin.last (2 * terminal.val + 1 + 1))) := by
    rw [dist_eq_norm, norm_sub_rev]
    exact margins.1.1.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have left_distance : μ * radius ≤ dist c (L.vertex (Fin.last (2 * terminal.val + 1 + 1))) := by
    rw [dist_eq_norm, norm_sub_rev]
    exact margins.2.2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  obtain ⟨rightArc, right_subset⟩ := exists_sphereArc_of_injective_path rpath right_simple c circle
    (by rw [first_distance]; exact start) (finish.le.trans right_distance)
  obtain ⟨leftArc, left_subset⟩ := exists_sphereArc_of_injective_path lpath left_simple c circle
    (by rw [first_distance]; exact start) (finish.le.trans left_distance)
  have right_image : Set.range rightArc.curve ⊆ Set.range R.path :=
    right_subset.trans right_range.subset
  have left_image : Set.range leftArc.curve ⊆ Set.range L.path :=
    left_subset.trans left_range.subset
  have order {l r : ℂ} (left_member : l ∈ Set.range L.path) (right_member : r ∈ Set.range R.path)
      (equal : ‖l - c‖ = ‖r - c‖) :
      (l - c).re ≤ (r - c).re ∧ (r - c).im ≤ (l - c).im := by
    obtain ⟨u, at_u⟩ := left_member
    obtain ⟨v, at_v⟩ := right_member
    obtain ⟨j, s, left_point⟩ := L.path_point_covered (by omega) u
    obtain ⟨k, z, right_point⟩ := R.path_point_covered (by omega) v
    have left_value : l = L.point j s := at_u.symm.trans left_point
    have right_value : r = R.point k z := at_v.symm.trans right_point
    rw [left_value, right_value] at equal ⊢
    exact B.comparisonPrefixes_circle_order i w center μ radius nonnegative positions face_bounds
      target original terminal parameter vertices_bounded points_bounded sectors directions budget
      j k s z equal
  have left_on : ‖leftArc.finish - c‖ = circle := by
    simpa only [dist_eq_norm, norm_sub_rev] using leftArc.on_sphere
  have right_on : ‖rightArc.finish - c‖ = circle := by
    simpa only [dist_eq_norm, norm_sub_rev] using rightArc.on_sphere
  refine ⟨rightArc, leftArc, right_image, left_image, ?_, ?_⟩
  · exact order (left_image ⟨1, leftArc.curve.target⟩) (right_image ⟨1, rightArc.curve.target⟩)
      (left_on.trans right_on.symm)
  · intro s r equal
    exact order (left_image (Set.mem_range_self s)) (right_image (Set.mem_range_self r)) equal

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
