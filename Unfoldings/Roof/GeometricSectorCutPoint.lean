module

public import Unfoldings.Roof.GeometricWaterfallRegular

/-! Every actual cut point strictly inside a sweep sector belongs to a leaf tail in that sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

/-- The sector of the actual containing cut component is derived from the
strict physical location. No separator provenance or fine mesh is required. -/
theorem exists_sector_leaf_at_cut_point (i : FiveSector) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    {z : ℂ} (inside : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.strictCarrier)
    (height : z.re + z.im ∈ Set.Icc 0 cutoff)
    (on_cut : origin + (fiveSectorFrame t positive small i).place.symm z ∈
      M.extendedGeometricCuts F) :
    ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ z.re + z.im ∧
        leaf.tailGraph.graph.point (z.re + z.im) = z := by
  let B := fiveSectorFrame t positive small i
  let x := origin + B.place.symm z
  have coordinate : B.place (x - origin) = z := by
    dsimp only [x]
    rw [add_sub_cancel_left, B.place.apply_symm_apply]
  have physical_inside := sector_strip_slab_inside_clip positive small i deep inside height
  change x ∈ interior (outerDomain) at physical_inside
  rw [M.extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips F covered positive small]
    at on_cut
  rcases on_cut with on_edge | tip
  · obtain ⟨e, member⟩ := Set.mem_iUnion.mp on_edge
    have assigned : (M.geometricComponentSector F covered positive small
        (M.geometricComponent F covered e.val)).sector = i := by
      by_contra different
      have root_inside : B.place (x - origin) ∈
          B.enclosingStrip.strictCarrier := coordinate.symm ▸ inside
      have forward : 0 ≤ (B.place (x - origin)).re +
          (B.place (x - origin)).im := by
        rw [coordinate]
        exact height.1
      have cone := B.enclosingStrip_strict_cone forward root_inside
      have strict := strictRayCone_subset_strictFiveSector positive small i cone
      have closed :=
        M.geometric_edge_position_in_sector F covered positive small e.val member
      exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small
        (fun equal => different equal.symm)) strict closed
    obtain ⟨leaf, reaches, after⟩ :=
      M.exists_geometric_sector_leaf_support F covered positive small i e.val e.property
        assigned member
    have point := leaf.tailGraph.point_eq_of_mem_ancestor_edge e.property reaches member
    change leaf.tailGraph.graph.point
      ((B.place (x - origin)).re + (B.place (x - origin)).im) =
        B.place (x - origin) at point
    rw [coordinate] at after point
    exact ⟨leaf, after, point⟩
  · obtain ⟨c, equal⟩ := tip
    change (F.componentTail c).tip = x at equal
    have tip_inside : (F.componentTail c).tip ∈ interior (outerDomain) := by
      rw [equal]
      exact physical_inside
    exact ((F.componentTail c).boundary.2 tip_inside).elim

end Unfoldings.ConvexRoof.SectorForest
