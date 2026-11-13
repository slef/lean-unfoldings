module

public import Unfoldings.Roof.GeometricSectorCutPoint
public import Unfoldings.Roof.GeometricChainSectors
public import Unfoldings.Roof.LeafCompletedTailTracking
public import Unfoldings.Cap.MatchedStripBankOrder
public import Unfoldings.Cap.SharedBankCirclePrefix
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Actual regular facing banks have gap order whenever their physical points coincide. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

/-- The two cells may have collapsed cells between them. The actual cut tail,
its fine parent path, and all curvature-sector data are derived from geometry. -/
theorem regular_level_bank_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    {S T : MonotoneStrip} (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells) {ε : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (first_width : S.lower.coordinate h < S.upper.coordinate h)
    (last_width : T.lower.coordinate h < T.upper.coordinate h)
    (same_point : S.upper.point h = T.lower.point h)
    (regular : ∀ f j, origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ≠ (Q.projectedTriangle f).vertex j) :
    (data.value (S.upper.point h)).re ≤ (other.value (T.lower.point h)).re ∧
      (other.value (T.lower.point h)).im ≤ (data.value (S.upper.point h)).im := by
  have first_closed : S.upper.point h ∈ closure data.strictDomain :=
    (S.bank_points_mem_closure_of_width ⟨height.1.le, height.2.le⟩ first_width).2
  have last_closed : T.lower.point h ∈ closure other.strictDomain :=
    (T.bank_points_mem_closure_of_width ⟨height.1.le, height.2.le⟩ last_width).1
  by_cases on_cut : origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ∈ M.extendedGeometricCuts F
  · have coordinates := congrArg Complex.re same_point
    change S.upper.coordinate h = T.lower.coordinate h at coordinates
    have inside : S.upper.point h ∈
        (fiveSectorFrame t positive small i).enclosingStrip.strictCarrier := by
      change (fiveSectorFrame t positive small i).enclosingStrip.lower.coordinate
        ((S.upper.point h).re + (S.upper.point h).im) < (S.upper.point h).re ∧
          (S.upper.point h).re <
          (fiveSectorFrame t positive small i).enclosingStrip.upper.coordinate
            ((S.upper.point h).re + (S.upper.point h).im)
      rw [S.upper.point_height]
      exact ⟨(P.cell_bounds first_cell h).1.trans_lt first_width,
        coordinates.trans_lt (last_width.trans_le (P.cell_bounds last_cell h).2)⟩
    obtain ⟨leaf, after, point⟩ := M.exists_sector_leaf_at_cut_point F covered positive small
      i deep inside (by rw [S.upper.point_height]; exact ⟨height.1.le, height.2.le⟩) on_cut
    rw [S.upper.point_height] at after point
    obtain ⟨w, position⟩ := leaf_vertices leaf
    obtain ⟨j, s, tracked⟩ := leaf.tailGraph_point_on_completed_path R outward w position
      footprint deep ⟨after, height.2.le⟩
    rw [point] at tracked
    have physical : origin + (fiveSectorFrame t positive small i).place.symm
        (S.upper.point h) = (R.completedRootPath w).point j s := by
      rw [tracked, LinearIsometryEquiv.symm_apply_apply]
      abel
    obtain ⟨anchor, _, at_start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered positive
      small leaf.val leaf.property.1
    have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
      rw [position, M.extendedGeometricCuts_eq_piece_union F]
      exact Set.mem_iUnion.mpr ⟨anchor, at_start⟩
    exact B.matched_strip_bank_point_order i data other height same_point first_width last_width
      (R.completedBankChain w j) (R.completedRootPath_vertex_mem on_cuts j.castSucc)
      (leaf.completed_bank_directions R outward w position j)
      (leaf.completed_curved_subtree_sectors R outward w position curvature_covered j) budget s
      regular (physical.trans (R.completedRootPath_point_bankChain w j s))
  · have coherent := D.projected_coherentAt_of_not_cut Q
      (fun cut => on_cut (R.projectedCutSet_subset cut))
    have last_coherent : D.ProjectedCoherentAt Q
        (origin + (fiveSectorFrame t positive small i).place.symm
          (T.lower.point h)) := by
      rw [← same_point]
      exact coherent
    have first_value := D.traceVisibleAt_eq_of_coherent (origin) _ _
      (data.visible_closure first_closed) coherent
    have last_value := D.traceVisibleAt_eq_of_coherent (origin) _ _
      (other.visible_closure last_closed) last_coherent
    rw [same_point] at first_value
    have equal := (congrArg data.value same_point).trans (first_value.trans last_value.symm)
    exact ⟨(congrArg Complex.re equal).le, (congrArg Complex.im equal).symm.le⟩

end Unfoldings.ConvexRoof.SectorForest
