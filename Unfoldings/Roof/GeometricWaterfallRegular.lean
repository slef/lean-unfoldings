module

public import Unfoldings.Roof.DeepGeometricWaterfall

/-! Regularity applies to every constructed subdivision retaining the actual leaf tails. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_waterfall_avoids (i : FiveSector) (cutoff : ℝ)
    (T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ G ∈ T.separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) :
    ∀ R ∈ T.cells, ∀ w : F.GeometricVertex,
      w ∉ (M.geometricParents F covered positive small).roots →
      ∀ x ∈ segment ℝ (F.geometricPosition w)
        (F.geometricPosition (M.geometricParent F covered w)),
        let z := (fiveSectorFrame t positive small i).place (x - origin)
        z.re + z.im ∈ Set.Icc 0 cutoff → z ∉ R.strictCarrier := by
  intro R cell w nonroot x member
  let B := fiveSectorFrame t positive small i
  let z := B.place (x - origin)
  change z.re + z.im ∈ Set.Icc 0 cutoff → z ∉ R.strictCarrier
  intro slab inside
  by_cases assigned : (M.geometricComponentSector F covered positive small
      (M.geometricComponent F covered w)).sector = i
  · obtain ⟨leaf, reaches, after⟩ :=
      M.exists_geometric_sector_leaf_support F covered positive small i w nonroot assigned
        member
    obtain ⟨G, separator, completion⟩ := represented leaf (after.trans slab.2)
    have tail_point := leaf.tailGraph.point_eq_of_mem_ancestor_edge nonroot reaches member
    have coordinate : G.coordinate (z.re + z.im) = z.re :=
      (completion.2 (z.re + z.im) ⟨after, slab.2⟩).trans (congrArg Complex.re tail_point)
    have equal := G.point_eq_of_coordinate z coordinate
    exact T.separator_avoids_cells separator cell (z.re + z.im) (equal.symm ▸ inside)
  · have bounds := T.cell_bounds cell (z.re + z.im)
    have root_inside : z ∈ B.enclosingStrip.strictCarrier :=
      ⟨bounds.1.trans_lt inside.1, inside.2.trans_le bounds.2⟩
    have cone := B.enclosingStrip_strict_cone slab.1 root_inside
    have strict := strictRayCone_subset_strictFiveSector positive small i cone
    have closed := M.geometric_edge_position_in_sector F covered positive small w member
    exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small
      (fun equal => assigned equal.symm)) strict closed

theorem geometric_waterfall_regular (i : FiveSector) (cutoff : ℝ)
    (deep : Metric.closedBall (origin) cutoff ⊆
      interior outer)
    (T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ G ∈ T.separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) :
    ∀ R ∈ T.cells, ∀ z ∈ R.strictCarrier,
      z.re + z.im ∈ Set.Icc 0 cutoff →
        origin + (fiveSectorFrame t positive small i).place.symm z ∈
          interior outer \ M.extendedGeometricCuts F := by
  have avoids := M.geometric_waterfall_avoids F covered positive small i cutoff T represented
  intro R cell z inside height
  let B := fiveSectorFrame t positive small i
  let x := origin + B.place.symm z
  have bounds := T.cell_bounds cell (z.re + z.im)
  have root_inside : z ∈ B.enclosingStrip.strictCarrier :=
    ⟨bounds.1.trans_lt inside.1, inside.2.trans_le bounds.2⟩
  have physical_inside := sector_strip_slab_inside_clip positive small i deep root_inside height
  refine ⟨physical_inside, ?_⟩
  intro on_cut
  rw [M.extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips F covered positive small]
    at on_cut
  rcases on_cut with on_edge | tip
  · obtain ⟨e, member⟩ := Set.mem_iUnion.mp on_edge
    have coordinate : B.place (x - origin) = z := by
      have vector : x - origin = B.place.symm z := by dsimp only [x]; abel
      rw [vector, B.place.apply_symm_apply]
    have absent := avoids R cell e.val e.property x member
    change (B.place (x - origin)).re +
      (B.place (x - origin)).im ∈ Set.Icc 0 cutoff →
        B.place (x - origin) ∉ R.strictCarrier at absent
    rw [coordinate] at absent
    exact absent height inside
  · obtain ⟨c, equal⟩ := tip
    change (F.componentTail c).tip = x at equal
    have tip_inside : (F.componentTail c).tip ∈ interior outer := by
      rw [equal]
      exact physical_inside
    exact (F.componentTail c).boundary.2 tip_inside

end Unfoldings.ConvexRoof.SectorForest
