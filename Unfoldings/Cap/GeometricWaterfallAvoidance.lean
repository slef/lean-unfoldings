module

public import Unfoldings.Cap.GeometricWaterfall
public import Unfoldings.Cap.GeometricTailEdgeCover
public import Unfoldings.Cap.GeometricLeafSupport

/-! Actual cut edges lie on the constructed waterfall boundaries, away from strip interiors. -/

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

/-- Every cut point is supported by an actual leaf in its already chosen component sector. -/
theorem exists_geometric_sector_leaf_support (i : FiveSector) (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots)
    (assigned : (M.geometricComponentSector F covered positive small lower
      (M.geometricComponent F covered w)).sector = i)
    {x : Plane} (member : x ∈ segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))) :
    ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      (M.geometricParents F covered positive small lower).Ancestor leaf.val w ∧
        leaf.point.re + leaf.point.im ≤
          ((fiveSectorFrame t positive small i).place (x - K.projectedVertex origin)).re +
            ((fiveSectorFrame t positive small i).place (x - K.projectedVertex origin)).im := by
  let P := M.geometricParents F covered positive small lower
  let B := fiveSectorFrame t positive small i
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp B.place.toLinearEquiv.toLinearMap
  have directions : ∀ z : F.GeometricVertex, P.Ancestor z w → z ∉ P.roots →
      F.geometricPosition (M.geometricParent F covered z) - F.geometricPosition z ∈
        closedFiveSector t i := by
    intro z ancestor z_nonroot
    rw [← assigned]
    exact (M.geometricComponentSector F covered positive small lower _).directions z z_nonroot
      (M.geometricComponent_of_ancestor F covered positive small lower ancestor)
  obtain ⟨leaf, reaches, leaf_nonroot, leaf_height, childless⟩ :=
    P.exists_descendant_leaf_within (geometricSweepHeight F B.place) w nonroot
      (fun z ancestor z_nonroot => M.geometricSweepHeight_parent_lt F covered positive small lower
        i z z_nonroot (directions z ancestor z_nonroot))
  have label : (M.geometricComponentSector F covered positive small lower
      (M.geometricComponent F covered leaf)).sector = i := by
    rw [M.geometricComponent_of_ancestor F covered positive small lower reaches]
    exact assigned
  let chosen : M.GeometricSectorLeaf F covered positive small lower i :=
    ⟨leaf, leaf_nonroot, childless, label⟩
  have step := M.geometricSweepHeight_parent_lt F covered positive small lower i w nonroot
    (directions w ⟨0, rfl⟩ nonroot)
  change height (F.geometricPosition w - K.projectedVertex origin) <
    height (F.geometricPosition (M.geometricParent F covered w) - K.projectedVertex origin) at step
  simp only [map_sub] at step
  have ascending : height (F.geometricPosition w) ≤
      height (F.geometricPosition (M.geometricParent F covered w)) := by linarith
  have after : geometricSweepHeight F B.place w ≤
      (B.place (x - K.projectedVertex origin)).re +
        (B.place (x - K.projectedVertex origin)).im := by
    change height (F.geometricPosition w - K.projectedVertex origin) ≤
      height (x - K.projectedVertex origin)
    simp only [map_sub]
    exact sub_le_sub_right (linear_segment_lower_bound height ascending member) _
  exact ⟨chosen, reaches, leaf_height.trans after⟩

/-- Construct a covering finite subdivision whose strict cell interiors avoid every assigned
geometric cut edge throughout the physical slab. Exact tails, including contacts, are retained. -/
theorem exists_geometric_sector_waterfall_avoiding (i : FiveSector) (cutoff : ℝ)
    (tips_beyond : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff →
        cutoff < M.geometricTailEndHeight F covered positive small lower i w.val) :
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
        leaf.point.re + leaf.point.im ≤ cutoff → ∃ G ∈ T.separators,
          MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
      ∀ R ∈ T.cells, ∀ w : F.GeometricVertex,
        w ∉ (M.geometricParents F covered positive small lower).roots →
        (M.geometricComponentSector F covered positive small lower
          (M.geometricComponent F covered w)).sector = i →
        ∀ x ∈ segment ℝ (F.geometricPosition w)
          (F.geometricPosition (M.geometricParent F covered w)),
          let z := (fiveSectorFrame t positive small i).place (x - K.projectedVertex origin)
          z.re + z.im ≤ cutoff → z ∉ R.strictCarrier := by
  obtain ⟨T, _, represented⟩ :=
    M.exists_geometric_sector_waterfall F covered positive small lower i cutoff tips_beyond
  refine ⟨T, represented, ?_⟩
  intro R cell w nonroot assigned x member
  let z := (fiveSectorFrame t positive small i).place (x - K.projectedVertex origin)
  change z.re + z.im ≤ cutoff → z ∉ R.strictCarrier
  intro below
  obtain ⟨leaf, reaches, after⟩ :=
    M.exists_geometric_sector_leaf_support F covered positive small lower i w nonroot assigned
      member
  obtain ⟨G, separator, completion⟩ := represented leaf (after.trans below)
  have tail_point := leaf.tailGraph.point_eq_of_mem_ancestor_edge nonroot reaches member
  have coordinate : G.coordinate (z.re + z.im) = z.re :=
    (completion.2 (z.re + z.im) ⟨after, below⟩).trans (congrArg Complex.re tail_point)
  have equal := G.point_eq_of_coordinate z coordinate
  rw [← equal]
  exact T.separator_avoids_cells separator cell (z.re + z.im)

end Unfoldings.ConvexCap.SectorForest
