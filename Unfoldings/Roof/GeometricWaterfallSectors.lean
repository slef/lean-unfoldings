module

public import Unfoldings.Cap.GeometricWaterfallSectors

public import Unfoldings.Roof.GeometricWaterfallAvoidance
public import Unfoldings.Geometry.FiveSectorInteriors
public import Unfoldings.Geometry.RayStripInterior

/-! A waterfall strip interior avoids geometric cut edges from every sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_edge_position_in_sector (w : F.GeometricVertex) {x : Plane}
    (member : x ∈ segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))) :
    x - origin ∈ closedFiveSector t
      (M.geometricComponentSector F covered positive small
        (M.geometricComponent F covered w)).sector := by
  let data := M.geometricComponentSector F covered positive small
    (M.geometricComponent F covered w)
  let A := AffineEquiv.constVAdd ℝ Plane (-origin)
  have first : A (F.geometricPosition w) ∈ closedFiveSector t data.sector := by
    change -origin + F.geometricPosition w ∈ _
    simpa only [sub_eq_add_neg, add_comm] using data.positions w rfl
  have last : A (F.geometricPosition (M.geometricParent F covered w)) ∈
      closedFiveSector t data.sector := by
    change -origin + F.geometricPosition (M.geometricParent F covered w) ∈ _
    simpa only [sub_eq_add_neg, add_comm] using
      data.positions _ (M.geometricComponent_parent F covered w)
  have image : A '' segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w)) =
        segment ℝ (A (F.geometricPosition w))
          (A (F.geometricPosition (M.geometricParent F covered w))) :=
    image_segment ℝ A.toAffineMap _ _
  have in_segment := image.subset ⟨x, member, rfl⟩
  have in_cone := (convex_inDirectionWedge (fiveSectorFirst t data.sector)
    (fiveSectorLast t data.sector)).segment_subset first last in_segment
  change InDirectionWedge _ _ (-origin + x) at in_cone
  change InDirectionWedge (fiveSectorFirst t data.sector) (fiveSectorLast t data.sector)
    (x - origin)
  simpa only [sub_eq_add_neg, add_comm] using in_cone

/-- Coverage and disjointness come from the constructed subdivision; here its strict interiors
are shown to avoid every geometric cut edge, including edges assigned to another sector. -/
theorem exists_geometric_sector_waterfall_all_edges_avoiding (i : FiveSector) (cutoff : ℝ)
    (tips_beyond : ∀ w : M.GeometricSectorLeaf F covered positive small i,
      w.point.re + w.point.im ≤ cutoff →
        cutoff < M.geometricTailEndHeight F covered positive small i w.val) :
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      ∀ R ∈ T.cells, ∀ w : F.GeometricVertex,
        w ∉ (M.geometricParents F covered positive small).roots →
        ∀ x ∈ segment ℝ (F.geometricPosition w)
          (F.geometricPosition (M.geometricParent F covered w)),
          let z := (fiveSectorFrame t positive small i).place (x - origin)
          z.re + z.im ∈ Set.Icc 0 cutoff → z ∉ R.strictCarrier := by
  obtain ⟨T, _, avoids⟩ := M.exists_geometric_sector_waterfall_avoiding F covered positive small
    i cutoff tips_beyond
  refine ⟨T, ?_⟩
  intro R cell w nonroot x member
  let B := fiveSectorFrame t positive small i
  let z := B.place (x - origin)
  change z.re + z.im ∈ Set.Icc 0 cutoff → z ∉ R.strictCarrier
  intro slab inside
  by_cases assigned : (M.geometricComponentSector F covered positive small
      (M.geometricComponent F covered w)).sector = i
  · exact avoids R cell w nonroot assigned x member slab.2 inside
  · have bounds := T.cell_bounds cell (z.re + z.im)
    have root_inside : z ∈ B.enclosingStrip.strictCarrier :=
      ⟨bounds.1.trans_lt inside.1, inside.2.trans_le bounds.2⟩
    have cone := B.enclosingStrip_strict_cone slab.1 root_inside
    have strict := strictRayCone_subset_strictFiveSector positive small i cone
    have closed := M.geometric_edge_position_in_sector F covered positive small w member
    exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small
      (fun equal => assigned equal.symm)) strict closed

end ConvexRoof.SectorForest
end Unfoldings
