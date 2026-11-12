module

public import Unfoldings.Cap.GeometricRecoverableWaterfall
public import Unfoldings.Cap.GeometricWaterfallRegular
public import Unfoldings.Cap.ExtendedLeafCoherence
public import Unfoldings.Cap.ExtendedWaterfallDomains
public import Unfoldings.Cap.ClosedSectorStrip
public import Unfoldings.Cap.GeometricVertexCutPiece

/-! Retain actual leaf/separator provenance with cut avoidance and coherent waterfall domains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- Construct the subdivision before its development, deriving all coherence needed at
reopening pinches. In particular no bank lift or compatible trace is a hypothesis. -/
theorem cornerExtendedOutward_exists_terminal_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let covered := T.cornerTails_covers_rim inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small lower i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ G ∈ P.separators,
          ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
            leaf.point.re + leaf.point.im ≤ cutoff ∧
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
          leaf.point.re + leaf.point.im ≤ cutoff →
            ∃ G ∈ P.separators,
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
          S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        (∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
          z.re + z.im ∈ Set.Icc 0 cutoff →
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
              interior (K.clipFootprint Z) \ M.extendedGeometricCuts F) ∧
        (∀ S ∈ P.cells, S.TerminalTailsFrom
          (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
          (fun leaf => leaf.tailGraph.graph) cutoff) ∧
        (∀ S ∈ P.cells, S.ApproachedPinchesIn
          (Set.range (fun w : {w : L.partition.pairedComplex.Vertex Set.univ //
            Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
            (fiveSectorFrame t positive small i).place
              (Q.projectedVertex w.val - K.projectedVertex origin))) 0 cutoff) ∧
        ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (K.projectedVertex origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have leaf_coherence := M.cornerExtended_geometric_leaf_coherent positive small T internal
    source_height lower conforming height
  have coherent_leaf (D : FacewiseDevelopment L.partition.pairedComplex R.retain)
      (w : F.GeometricVertex)
      (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots)
      (childless : ∀ child ∉ (M.geometricParents F covered positive small lower).roots,
        M.geometricParent F covered child ≠ w) :
      F.geometricPosition w ∈ Q.footprint ∧ D.ProjectedCoherentAt Q (F.geometricPosition w) := by
    obtain ⟨v, position, coherent⟩ := leaf_coherence w nonroot childless
    change Q.projectedVertex v = F.geometricPosition w at position
    exact ⟨position ▸ Q.projectedVertex_mem_footprint v, coherent (R.completedDevelopment D)⟩
  refine fun i => ?_
  let B := fiveSectorFrame t positive small i
  obtain ⟨P, provenance, represented, good⟩ :=
    M.exists_geometric_sector_waterfall_with_terminal_tails F covered positive small lower i cutoff
      (fun w _ => w.tail_end_beyond_clip_ball deep)
  have vertex_pinches : ∀ S ∈ P.cells, S.ApproachedPinchesIn
      (Set.range (fun w : {w : L.partition.pairedComplex.Vertex Set.univ //
        Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
        B.place (Q.projectedVertex w.val - K.projectedVertex origin))) 0 cutoff := by
    intro S cell h bounds collapsed approached
    obtain ⟨w, at_point⟩ := (good S cell).2.1 h bounds collapsed approached
    have root_bounds := P.cell_bounds cell h
    have root : S.lower.point h ∈ B.enclosingStrip.carrier := by
      change B.enclosingStrip.lower.coordinate ((S.lower.point h).re + (S.lower.point h).im) ≤
          (S.lower.point h).re ∧ (S.lower.point h).re ≤
          B.enclosingStrip.upper.coordinate ((S.lower.point h).re + (S.lower.point h).im)
      rw [S.lower.point_height]
      exact ⟨root_bounds.1, (S.ordered h).trans root_bounds.2⟩
    have physical_inside := deep (closed_sector_strip_slab_mem_closedBall positive small i
      (K.projectedVertex origin) root (by
        rw [S.lower.point_height]
        exact ⟨bounds.1.le, bounds.2.le⟩))
    have position : K.projectedVertex origin + B.place.symm (S.lower.point h) =
        F.geometricPosition w := by
      rw [← at_point, B.place.symm_apply_apply]
      abel
    have nonroot : w ∉ (M.geometricParents F covered positive small lower).roots := by
      rintro ⟨c, equal⟩
      rw [position, ← equal] at physical_inside
      exact (F.componentTail c).boundary.2 physical_inside
    obtain ⟨v, physical_vertex, _⟩ := M.meshed_geometric_nonroot_vertex F covered positive small
      lower T w nonroot
    have on_cuts : Q.projectedVertex v ∈ M.extendedGeometricCuts F := by
      change Q.projectedVertex v = F.geometricPosition w at physical_vertex
      rw [physical_vertex, M.extendedGeometricCuts_eq_piece_union F]
      obtain ⟨piece, _, member⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered
        positive small lower w nonroot
      exact Set.mem_iUnion.mpr ⟨piece, member⟩
    refine ⟨⟨v, on_cuts⟩, ?_⟩
    change B.place (Q.projectedVertex v - K.projectedVertex origin) = S.lower.point h
    change Q.projectedVertex v = F.geometricPosition w at physical_vertex
    rw [physical_vertex]
    exact at_point
  have terminal_tails := fun S cell => (good S cell).2.2
  have good := fun S cell => (good S cell).1
  have regular := M.geometric_waterfall_regular F covered positive small lower i cutoff deep
    P represented
  refine ⟨P, provenance, represented, fun S cell =>
    ⟨(good S cell).1, (good S cell).2.1⟩, fun S cell => (good S cell).2.2,
    regular, terminal_tails, vertex_pinches, ?_⟩
  intro D S cell z member slab
  rcases member with strict | coherent
  · have physical := regular S cell z strict slab
    refine ⟨?_, D.projected_coherentAt_of_not_cut Q ?_⟩
    · rw [L.partition.normalizedCap_footprint L.conforming lower]
      exact interior_subset physical.1
    · exact fun on_cut => physical.2 (R.projectedCutSet_subset on_cut)
  · rcases coherent with zero | ⟨w, equal⟩
    · subst z
      have source_coherent := coherent_leaf D (Sum.inl origin)
        (M.geometric_original_nonroot F covered positive small lower origin)
        (M.geometric_origin_childless F covered positive small lower)
      change K.projectedVertex origin ∈ Q.footprint ∧
        D.ProjectedCoherentAt Q (K.projectedVertex origin) at source_coherent
      simpa only [map_zero, add_zero] using source_coherent
    · have position : K.projectedVertex origin + B.place.symm z =
          F.geometricPosition w.val := by
        rw [← equal]
        change K.projectedVertex origin + B.place.symm
          (B.place (F.geometricPosition w.val - K.projectedVertex origin)) = _
        rw [B.place.symm_apply_apply]
        abel
      rw [position]
      exact coherent_leaf D w.val w.property.1 w.property.2.1

/-- Retain the terminal-vertex interface without the actual tail witness. -/
theorem cornerExtendedOutward_exists_vertex_pinched_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let covered := T.cornerTails_covers_rim inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small lower i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ G ∈ P.separators,
          ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
            leaf.point.re + leaf.point.im ≤ cutoff ∧
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
          leaf.point.re + leaf.point.im ≤ cutoff →
            ∃ G ∈ P.separators,
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
          S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        (∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
          z.re + z.im ∈ Set.Icc 0 cutoff →
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
              interior (K.clipFootprint Z) \ M.extendedGeometricCuts F) ∧
        (∀ S ∈ P.cells, S.ApproachedPinchesIn
          (Set.range (fun w : {w : L.partition.pairedComplex.Vertex Set.univ //
            Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
            (fiveSectorFrame t positive small i).place
              (Q.projectedVertex w.val - K.projectedVertex origin))) 0 cutoff) ∧
        ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (K.projectedVertex origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, pinches, regular, _, vertices, physical⟩ :=
    M.cornerExtendedOutward_exists_terminal_waterfall positive small T internal source_height
      lower conforming height cutoff deep i
  exact ⟨P, provenance, represented, coordinates, pinches, regular, vertices, physical⟩

/-- Retain the coherent-domain interface without the extra terminal-pinch output. -/
theorem cornerExtendedOutward_exists_provenant_coherent_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let covered := T.cornerTails_covers_rim inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small lower i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ G ∈ P.separators,
          ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
            leaf.point.re + leaf.point.im ≤ cutoff ∧
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
          leaf.point.re + leaf.point.im ≤ cutoff →
            ∃ G ∈ P.separators,
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
          S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        (∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
          z.re + z.im ∈ Set.Icc 0 cutoff →
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
              interior (K.clipFootprint Z) \ M.extendedGeometricCuts F) ∧
        ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (K.projectedVertex origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, pinches, regular, _, physical⟩ :=
    M.cornerExtendedOutward_exists_vertex_pinched_waterfall positive small T internal source_height
      lower conforming height cutoff deep i
  exact ⟨P, provenance, represented, coordinates, pinches, regular, physical⟩

end Unfoldings.ConvexCap.SectorForest
