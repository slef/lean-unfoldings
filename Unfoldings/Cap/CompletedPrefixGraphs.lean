module

public import Unfoldings.Cap.CompletedComparisonPrefixes
public import Unfoldings.Cap.CompletedComparisonProgress
public import Unfoldings.Cap.CompletedTraceVertexCopy
public import Unfoldings.Geometry.ChainLinearGraph
public import Unfoldings.Geometry.ChainTruncationLinear

/-! The actual finite comparison banks are graph arcs with the correct visible-trace start. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem entranceComparisonPrefix_start (i : FiveSector) (w : C.Vertex Set.univ) (origin : Plane)
    (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval) :
    (B.entranceComparisonPrefix i w origin terminal parameter).vertex 0 =
      B.sectorFrame i origin := by
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  exact ((B.entranceComparisonChain i w origin).truncate_vertex_before endpoint parameter 0
    (Nat.zero_le _)).trans rfl

theorem exitComparisonPrefix_start (i : FiveSector) (w : C.Vertex Set.univ) (origin : Plane)
    (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval) :
    (B.exitComparisonPrefix i w origin terminal parameter).vertex 0 = B.sectorFrame i origin := by
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  exact ((B.exitComparisonChain i w origin).truncate_vertex_before endpoint parameter 0
    (Nat.zero_le _)).trans rfl

/-- A visible branch value is exactly the common initial point of its two actual
comparison prefixes, using the contour copy selected by that trace. -/
theorem trace_vertex_comparison_prefix_starts (i : FiveSector) (w : C.Vertex Set.univ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K source (N.calibratedFrame D B.anchor B.reference)
      (fiveSectorFrame t positive small i).place G domain z)
    (vertex : source + (fiveSectorFrame t positive small i).place.symm z = K.projectedVertex w)
    (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval) :
    ∃ target : Fin (N.completedContour.length + 1),
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w ∧
      (B.entranceComparisonPrefix i w
        (D.boundaryPosition (N.completedContour.cycle.point target)) terminal parameter).vertex 0 =
          G z ∧
      (B.exitComparisonPrefix i w
        (D.boundaryPosition (N.completedContour.cycle.point target)) terminal parameter).vertex 0 =
          G z := by
  obtain ⟨target, original, value⟩ := B.trace_vertex_is_boundary_copy i w trace vertex
  refine ⟨target, original, ?_, ?_⟩
  · rw [B.entranceComparisonPrefix_start, value]
  · rw [B.exitComparisonPrefix_start, value]

variable (i : FiveSector) (w : C.Vertex Set.univ) (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
  (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
  (directions : ∀ j, K.projectedVertex
    (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
      K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
  (terminal : Fin (N.spanningCompletion.parents.distanceToRoot w)) (parameter : unitInterval)

/-- The right bank's entire geometric image is a graph over its horizontal interval;
zero-length branch gaps cause no spurs or self-intersections. -/
def entranceComparisonPrefixGraph :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let P := B.entranceComparisonPrefix i w origin terminal parameter
    Set.range P.path ≃ₜ Set.Icc (P.vertex 0).re
      (P.vertex (Fin.last (2 * terminal.val + 1 + 1))).re := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let P := B.entranceComparisonChain i w origin
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  have order := B.comparisonChains_increment_order i w target original sectors budget directions
  exact (P.truncate endpoint parameter).linearGraphHomeomorph Complex.reCLM
    (P.truncate_linear_nonnegative Complex.reCLM.toLinearMap (fun k => (order k).1)
      endpoint parameter)
    (P.truncate_linear_flat Complex.reCLM.toLinearMap (fun k => (order k).2.1)
      endpoint parameter) (by omega)

/-- The left bank's entire image is similarly a graph over its vertical interval. -/
def exitComparisonPrefixGraph :
    let origin := D.boundaryPosition (N.completedContour.cycle.point target)
    let P := B.exitComparisonPrefix i w origin terminal parameter
    Set.range P.path ≃ₜ Set.Icc (P.vertex 0).im
      (P.vertex (Fin.last (2 * terminal.val + 1 + 1))).im := by
  let origin := D.boundaryPosition (N.completedContour.cycle.point target)
  let P := B.exitComparisonChain i w origin
  let endpoint : Fin (2 * N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨2 * terminal.val + 1, by omega⟩
  have order := B.comparisonChains_increment_order i w target original sectors budget directions
  exact (P.truncate endpoint parameter).linearGraphHomeomorph Complex.imCLM
    (P.truncate_linear_nonnegative Complex.imCLM.toLinearMap (fun k => (order k).2.2.1)
      endpoint parameter)
    (P.truncate_linear_flat Complex.imCLM.toLinearMap (fun k => (order k).2.2.2.1)
      endpoint parameter) (by omega)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
