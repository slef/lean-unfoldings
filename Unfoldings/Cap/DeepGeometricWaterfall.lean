module

public import Unfoldings.Cap.GeometricWaterfallSectors
public import Unfoldings.Cap.GeometricTailCutoff

/-! Deep clipping makes the actual waterfall strip interiors lie in the regular roof region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

theorem sector_strip_slab_inside_clip (i : FiveSector) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆
      interior (K.clipFootprint Z)) {z : ℂ}
    (inside : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.strictCarrier)
    (height : z.re + z.im ∈ Set.Icc 0 cutoff) :
    K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
      interior (K.clipFootprint Z) := by
  let B := fiveSectorFrame t positive small i
  have cone : B.place.symm z ∈ strictRayCone (fiveSectorFirst t i) (fiveSectorLast t i) :=
    B.enclosingStrip_strict_cone
      (by simpa only [B.place.apply_symm_apply] using height.1)
      (by simpa only [B.place.apply_symm_apply] using inside)
  obtain ⟨a, ha, b, hb, equal⟩ := cone
  have quadrant := B.quadrant_nonneg ⟨a, b, ha.le, hb.le, equal⟩
  rw [B.place.apply_symm_apply] at quadrant
  have bound := (complex_norm_le_diagonal_of_nonneg quadrant.1 quadrant.2).trans height.2
  apply deep
  rw [Metric.mem_closedBall, dist_eq_norm]
  have vector : K.projectedVertex origin + B.place.symm z - K.projectedVertex origin =
      B.place.symm z := by abel
  rw [vector, B.place.symm.norm_map]
  exact bound

include covered lower in
/-- No safe-cut, strip-cover, or endpoint-height certificate is supplied. A ball contained in
the actual clip suffices to construct the finite subdivision with regular physical interiors. -/
theorem exists_deep_geometric_sector_waterfall (i : FiveSector) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆
      interior (K.clipFootprint Z)) :
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      ∀ R ∈ T.cells, ∀ z ∈ R.strictCarrier,
        z.re + z.im ∈ Set.Icc 0 cutoff →
          K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
            interior (K.clipFootprint Z) \ M.extendedGeometricCuts F := by
  obtain ⟨T, avoids⟩ := M.exists_geometric_sector_waterfall_all_edges_avoiding F covered
    positive small lower i cutoff (fun w _ => w.tail_end_beyond_clip_ball deep)
  refine ⟨T, ?_⟩
  intro R cell z inside height
  let B := fiveSectorFrame t positive small i
  let x := K.projectedVertex origin + B.place.symm z
  have bounds := T.cell_bounds cell (z.re + z.im)
  have root_inside : z ∈ B.enclosingStrip.strictCarrier :=
    ⟨bounds.1.trans_lt inside.1, inside.2.trans_le bounds.2⟩
  have physical_inside := sector_strip_slab_inside_clip positive small i
    deep root_inside height
  refine ⟨physical_inside, ?_⟩
  intro on_cut
  rw [M.extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips F covered positive small lower]
    at on_cut
  rcases on_cut with on_edge | tip
  · obtain ⟨e, member⟩ := Set.mem_iUnion.mp on_edge
    have coordinate : B.place (x - K.projectedVertex origin) = z := by
      have vector : x - K.projectedVertex origin = B.place.symm z := by dsimp only [x]; abel
      rw [vector, B.place.apply_symm_apply]
    have absent := avoids R cell e.val e.property x member
    change (B.place (x - K.projectedVertex origin)).re +
      (B.place (x - K.projectedVertex origin)).im ∈ Set.Icc 0 cutoff →
        B.place (x - K.projectedVertex origin) ∉ R.strictCarrier at absent
    rw [coordinate] at absent
    exact absent height inside
  · obtain ⟨c, equal⟩ := tip
    change (F.componentTail c).tip = x at equal
    have tip_inside : (F.componentTail c).tip ∈ interior (K.clipFootprint Z) := by
      rw [equal]
      exact physical_inside
    exact (F.componentTail c).boundary.2 tip_inside

end Unfoldings.ConvexCap.SectorForest
