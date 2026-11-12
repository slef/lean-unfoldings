module

public import Unfoldings.Cap.GeometricFineTailTracking
public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Cap.CompletedBankVectorOrder

/-! Actual completed cut paths track the prescribed geometric tails before the deep cutoff. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricComponentSector

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {c : F.Component}
  (data : M.GeometricComponentSector F covered positive small lower c)

/-- The actual forest supplies cut support, outwardness, genuine fine edges, and
an endpoint beyond the deep cutoff. Only the common physical start and component
are identified; no fine/coarse path correspondence is an input. -/
theorem tail_point_on_completed_path
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F)
    (anchor : M.ExtendedCutPiece F) (component : M.cutPieceLabel F covered anchor = c)
    (start : Q.projectedVertex w ∈
      segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor))
    {z : F.GeometricVertex}
    (nonroot : z ∉ (M.geometricParents F covered positive small lower).roots)
    (same_component : M.geometricComponent F covered z = c)
    (H : M.SectorTailGraph F covered positive small lower data.sector z)
    (same_start : Q.projectedVertex w = F.geometricPosition z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior Q.footprint)
    (tail_finish : cutoff < M.geometricTailEndHeight F covered positive small lower data.sector z)
    {h : ℝ} (member : h ∈ Set.Icc
      (M.geometricTailStartHeight F covered positive small lower data.sector z) cutoff) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      H.graph.point h = (fiveSectorFrame t positive small data.sector).place
        ((R.completedRootPath w).point j s - K.projectedVertex origin) := by
  let P := R.completedRootPath w
  let B := fiveSectorFrame t positive small data.sector
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have cover := fun j => R.completedRootPath_edge_subset on_cuts j
  have whole_cover := fun j => (cover j).trans (M.extendedGeometricCuts_eq_piece_union F).subset
  have path_start : P.vertex 0 ∈
      segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor) := start
  have end_on_cuts := R.completedRootPath_vertex_mem on_cuts
    (Fin.last (R.spanningCompletion.parents.distanceToRoot w))
  obtain ⟨k, endpoint⟩ := Set.mem_iUnion.mp
    ((M.extendedGeometricCuts_eq_piece_union F).subset end_on_cuts)
  have same := P.labels_eq_of_segment_cover (M.cutPieceFirst F) (M.cutPieceLast F)
    (M.cutPieceLabel F covered) (M.cutPiece_labels_compatible F covered lower)
    whole_cover anchor path_start (Fin.last _) k endpoint
  have position := (data.cut_piece_geometry k (same.trans component)).2 _ endpoint
  have quadrant : 0 ≤ (B.place (P.vertex (Fin.last _) - K.projectedVertex origin)).re ∧
      0 ≤ (B.place (P.vertex (Fin.last _) - K.projectedVertex origin)).im :=
    B.quadrant_nonneg position
  have size : ‖P.vertex (Fin.last _) - K.projectedVertex origin‖ ≤
      (B.place (P.vertex (Fin.last _) - K.projectedVertex origin)).re +
        (B.place (P.vertex (Fin.last _) - K.projectedVertex origin)).im := by
    have bound := Complex.norm_le_abs_re_add_abs_im
      (B.place (P.vertex (Fin.last _) - K.projectedVertex origin))
    simpa only [B.place.norm_map, abs_of_nonneg quadrant.1, abs_of_nonneg quadrant.2] using bound
  have beyond : cutoff < ‖P.vertex (Fin.last _) - K.projectedVertex origin‖ := by
    by_contra not_beyond
    exact (R.completedRootPath_last_frontier w).2 (deep (by
      change dist (P.vertex (Fin.last _)) (K.projectedVertex origin) ≤ cutoff
      rw [dist_eq_norm]
      exact le_of_not_gt not_beyond))
  have genuine (j : Fin (R.spanningCompletion.parents.distanceToRoot w)) : P.edge j ≠ 0 := by
    change Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val + 1] w) -
      Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val] w) ≠ 0
    rw [Function.iterate_succ_apply']
    exact R.completed_parent_direction_ne_zero _
      (R.spanningCompletion.parents.iterate_lt_distanceToRoot_not_mem w j.isLt)
  have component_genuine :=
    M.geometric_component_nonconstant F covered positive small lower z nonroot
  rw [same_component] at component_genuine
  exact data.tail_point_on_cut_chain component_genuine P cover anchor component path_start
    (R.completedRootPath_outward outward on_cuts) genuine H same_start (beyond.trans_le size)
    tail_finish member

end Unfoldings.ConvexCap.SectorForest.GeometricComponentSector
