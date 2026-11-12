module

public import Unfoldings.Cap.CompletedPrefixCircleOrder
public import Unfoldings.Cap.CompletedPrefixGraphs
public import Unfoldings.Geometry.ChainGraphArc

/-! Reparametrize actual finite comparison banks as simple paths with the same whole images. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)
  (i : FiveSector) (w : C.Vertex Set.univ) (center : Plane) (μ radius : ℝ)
  (positions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
    (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i)
  (face_bounds : ∀ f (p : Plane), p ∈ (K.projectedTriangle f).carrier →
    ‖p - source‖ ≤ radius → p - source ∈ closedFiveSector t i →
    μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).re ∧
      μ * ‖p - source‖ ≤ (B.sectorFrame i (D.projectedPlacement K f p - center)).im)
  (target : Fin (N.completedContour.length + 1))
  (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval)
  (at_radius : ‖(N.completedRootPath w).point terminal parameter - source‖ = radius)
  (far : ‖D.boundaryPosition (N.completedContour.cycle.point target) - center‖ < μ * radius)

include positions face_bounds at_radius far

theorem comparisonPrefixes_endpoint_progress :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let R := B.entranceComparisonPrefix i w origin terminal parameter
    let L := B.exitComparisonPrefix i w origin terminal parameter
    (R.vertex 0).re < (R.vertex (Fin.last (2 * terminal.val + 1 + 1))).re ∧
      (L.vertex 0).im < (L.vertex (Fin.last (2 * terminal.val + 1 + 1))).im := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  have margins := B.comparisonPrefixes_last_margin i w center μ radius positions face_bounds target
    terminal parameter at_radius
  have horizontal := (le_abs_self (B.sectorFrame i (origin - center)).re).trans
    (Complex.abs_re_le_norm _)
  have vertical := (le_abs_self (B.sectorFrame i (origin - center)).im).trans
    (Complex.abs_im_le_norm _)
  rw [(B.sectorFrame i).norm_map, map_sub, Complex.sub_re] at horizontal
  rw [(B.sectorFrame i).norm_map, map_sub, Complex.sub_im] at vertical
  dsimp only at margins ⊢
  rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im] at margins
  rw [B.entranceComparisonPrefix_start, B.exitComparisonPrefix_start]
  constructor <;> linarith [margins.1.1, margins.2.2]

variable
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
  (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
  (directions : ∀ j, K.projectedVertex
    (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
      K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)

include original sectors budget directions

/-- The simple paths retain precisely the actual comparison-bank images, rather
than replacing them by unrelated safe curves. Their initial trace copy is unchanged. -/
theorem exists_simple_comparison_prefix_paths :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let R := B.entranceComparisonPrefix i w origin terminal parameter
    let L := B.exitComparisonPrefix i w origin terminal parameter
    ∃ right : Path (R.vertex 0) (R.vertex (Fin.last (2 * terminal.val + 1 + 1))),
    ∃ left : Path (L.vertex 0) (L.vertex (Fin.last (2 * terminal.val + 1 + 1))),
      Function.Injective right ∧ Function.Injective left ∧
        Set.range right = Set.range R.path ∧ Set.range left = Set.range L.path := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let R := B.entranceComparisonChain i w origin
  let L := B.exitComparisonChain i w origin
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  have order := B.comparisonChains_increment_order i w target original sectors budget directions
  have progress := B.comparisonPrefixes_endpoint_progress i w center μ radius positions face_bounds
    target terminal parameter at_radius far
  obtain ⟨right, right_injective, right_range⟩ :=
    (R.truncate endpoint parameter).exists_injective_graph_path Complex.reCLM
      (R.truncate_linear_nonnegative Complex.reCLM.toLinearMap (fun k => (order k).1)
        endpoint parameter)
      (R.truncate_linear_flat Complex.reCLM.toLinearMap (fun k => (order k).2.1)
        endpoint parameter) (by omega) progress.1
  obtain ⟨left, left_injective, left_range⟩ :=
    (L.truncate endpoint parameter).exists_injective_graph_path Complex.imCLM
      (L.truncate_linear_nonnegative Complex.imCLM.toLinearMap (fun k => (order k).2.2.1)
        endpoint parameter)
      (L.truncate_linear_flat Complex.imCLM.toLinearMap (fun k => (order k).2.2.2.1)
        endpoint parameter) (by omega) progress.2
  exact ⟨right, left, right_injective, left_injective, right_range, left_range⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
