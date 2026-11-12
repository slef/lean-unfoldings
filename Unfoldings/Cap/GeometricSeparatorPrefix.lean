module

public import Unfoldings.Cap.GeometricWaterfallRegular
public import Unfoldings.Cap.GeometricTailLeaves
public import Unfoldings.Geometry.SubdivisionWallContacts

/-! A separator's strict-sector prefix can meet actual cuts only at coherent wall contacts. -/

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

/-- Before its own leaf, a separator touching a cut must touch an earlier leaf's
recorded tail. Their later separation forces this contact into the coherent set. -/
theorem separator_prefix_cut_mem_coherent {i : FiveSector} {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G)
    {E : Set ℂ} (pinches : ∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff)
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (leaf : M.GeometricSectorLeaf F covered positive small lower i)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    {h : ℝ} (height : h ∈ Set.Icc 0 cutoff) (before : h < leaf.point.re + leaf.point.im)
    (inside : H.point h ∈ (fiveSectorFrame t positive small i).enclosingStrip.strictCarrier)
    (on_cut : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (H.point h) ∈ M.extendedGeometricCuts F) : H.point h ∈ E := by
  let B := fiveSectorFrame t positive small i
  let x := K.projectedVertex origin + B.place.symm (H.point h)
  have coordinate : B.place (x - K.projectedVertex origin) = H.point h := by
    have vector : x - K.projectedVertex origin = B.place.symm (H.point h) := by
      dsimp only [x]
      abel
    rw [vector, B.place.apply_symm_apply]
  have physical_inside := sector_strip_slab_inside_clip positive small i deep inside
    (by rw [H.point_height]; exact height)
  rw [M.extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips F covered positive small lower]
    at on_cut
  rcases on_cut with on_edge | tip
  · obtain ⟨e, member⟩ := Set.mem_iUnion.mp on_edge
    have assigned : (M.geometricComponentSector F covered positive small lower
        (M.geometricComponent F covered e.val)).sector = i := by
      by_contra different
      have root_inside : B.place (x - K.projectedVertex origin) ∈
          B.enclosingStrip.strictCarrier :=
        coordinate.symm ▸ inside
      have forward : 0 ≤ (B.place (x - K.projectedVertex origin)).re +
          (B.place (x - K.projectedVertex origin)).im := by
        rw [coordinate, H.point_height]
        exact height.1
      have cone := B.enclosingStrip_strict_cone forward root_inside
      have strict := strictRayCone_subset_strictFiveSector positive small i cone
      have closed :=
        M.geometric_edge_position_in_sector F covered positive small lower e.val member
      exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small
        (fun equal => different equal.symm)) strict closed
    obtain ⟨other, reaches, after⟩ :=
      M.exists_geometric_sector_leaf_support F covered positive small lower i e.val e.property
        assigned member
    rw [coordinate, H.point_height] at after
    obtain ⟨G, wall, completes⟩ := represented other (after.trans height.2)
    have graph_point := other.tailGraph.point_eq_of_mem_ancestor_edge e.property reaches member
    change other.tailGraph.graph.point
      ((B.place (x - K.projectedVertex origin)).re + (B.place (x - K.projectedVertex origin)).im) =
        B.place (x - K.projectedVertex origin) at graph_point
    rw [coordinate, H.point_height] at graph_point
    have graph_coordinate : other.tailGraph.graph.coordinate h = H.coordinate h :=
      congrArg Complex.re graph_point
    have contact : H.coordinate h = G.coordinate h :=
      graph_coordinate.symm.trans (completes.2 h ⟨after, height.2⟩).symm
    have distinct : other.val ≠ leaf.val := by
      intro equal
      have same : other = leaf := Subtype.ext equal
      subst other
      exact (not_le_of_gt before) after
    have target_distinct := other.tailGraph.leaf_coordinate_ne leaf.property.1 leaf.property.2.1
      distinct (after.trans before.le) (active.trans_lt (other.tail_end_beyond_clip_ball deep))
    have later_distinct : H.coordinate (leaf.point.re + leaf.point.im) ≠
        G.coordinate (leaf.point.re + leaf.point.im) := by
      rw [completion.2 _ ⟨le_rfl, active⟩, leaf.tailGraph_target,
        completes.2 _ ⟨after.trans before.le, active⟩]
      exact Ne.symm target_distinct
    exact P.wall_contact_reopening_mem pinches (P.separators_walls separator)
      (P.separators_walls wall) height contact ⟨before.le, active⟩ later_distinct
  · obtain ⟨c, equal⟩ := tip
    change (F.componentTail c).tip = x at equal
    have tip_inside : (F.componentTail c).tip ∈ interior (K.clipFootprint Z) := by
      rw [equal]
      exact physical_inside
    exact ((F.componentTail c).boundary.2 tip_inside).elim

/-- This also handles contact with an exterior sector ray. If an adjacent cell
has collapsed here but has width later, its own pinch invariant gives coherence. -/
theorem shared_separator_prefix_uncut_or_coherent {i : FiveSector} {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G)
    {E : Set ℂ} (pinches : ∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff)
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (leaf : M.GeometricSectorLeaf F covered positive small lower i)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : leaf.point ∈ E)
    {L R : MonotoneStrip} (left_cell : L ∈ P.cells) (right_cell : R ∈ P.cells)
    (left_wall : L.upper = H) (right_wall : R.lower = H)
    {h a b : ℝ} (height : h ∈ Set.Icc 0 (leaf.point.re + leaf.point.im))
    (first_later : a ∈ Set.Icc h cutoff)
    (first_width : L.lower.coordinate a < L.upper.coordinate a)
    (last_later : b ∈ Set.Icc h cutoff)
    (last_width : R.lower.coordinate b < R.upper.coordinate b) :
    H.point h ∈ E ∨ K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (H.point h) ∉ M.extendedGeometricCuts F := by
  have slab : h ∈ Set.Icc 0 cutoff := ⟨height.1, height.2.trans active⟩
  by_cases left_width : L.lower.coordinate h < L.upper.coordinate h
  · by_cases right_width : R.lower.coordinate h < R.upper.coordinate h
    · have lower_bound : (fiveSectorFrame t positive small i).enclosingStrip.lower.coordinate h <
          H.coordinate h := (P.cell_bounds left_cell h).1.trans_lt (by
            rw [← left_wall]
            exact left_width)
      have upper_bound : H.coordinate h <
          (fiveSectorFrame t positive small i).enclosingStrip.upper.coordinate h :=
        lt_of_lt_of_le (by rw [← right_wall]; exact right_width) (P.cell_bounds right_cell h).2
      have inside : H.point h ∈
          (fiveSectorFrame t positive small i).enclosingStrip.strictCarrier := by
        change (fiveSectorFrame t positive small i).enclosingStrip.lower.coordinate
          ((H.point h).re + (H.point h).im) < (H.point h).re ∧
          (H.point h).re < (fiveSectorFrame t positive small i).enclosingStrip.upper.coordinate
            ((H.point h).re + (H.point h).im)
        rw [H.point_height]
        exact ⟨lower_bound, upper_bound⟩
      by_cases before : h < leaf.point.re + leaf.point.im
      · by_cases on_cut : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
            (H.point h) ∈ M.extendedGeometricCuts F
        · exact Or.inl (M.separator_prefix_cut_mem_coherent F covered positive small lower deep P
            represented pinches separator leaf active completion slab before inside on_cut)
        · exact Or.inr on_cut
      · have equal : h = leaf.point.re + leaf.point.im :=
          le_antisymm height.2 (le_of_not_gt before)
        have target : H.point (leaf.point.re + leaf.point.im) = leaf.point :=
          H.point_eq_of_coordinate leaf.point
            ((completion.2 _ ⟨le_rfl, active⟩).trans leaf.tailGraph_target)
        left
        rw [equal, target]
        exact leaf_coherent
    · have collapsed : R.lower.coordinate h = R.upper.coordinate h :=
        le_antisymm (R.ordered h) (le_of_not_gt right_width)
      have coherent := pinches R right_cell h slab collapsed b last_later last_width
      rw [right_wall] at coherent
      exact Or.inl coherent
  · have collapsed : L.lower.coordinate h = L.upper.coordinate h :=
      le_antisymm (L.ordered h) (le_of_not_gt left_width)
    have coherent := pinches L left_cell h slab collapsed a first_later first_width
    rw [L.lower.point_eq_of_same_coordinate L.upper collapsed, left_wall] at coherent
    exact Or.inl coherent

end Unfoldings.ConvexCap.SectorForest
