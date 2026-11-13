module

public import Unfoldings.Roof.GeometricRecoverableWaterfall
public import Unfoldings.Roof.GeometricWaterfallRegular
public import Unfoldings.Roof.CompletionSourceCoherence
public import Unfoldings.Roof.CompletionWaterfallDomains
public import Unfoldings.Cap.ClosedSectorStrip
public import Unfoldings.Roof.GeometricVertexCutPiece

/-! Retain actual leaf/separator provenance with cut avoidance and coherent waterfall domains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}

/-- Construct the subdivision before its development, deriving all coherence needed at
reopening pinches. In particular no bank lift or compatible trace is a hypothesis. -/
theorem completionOutward_exists_terminal_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.CompletionMesh φ region extra)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes T.tentHeight (Real.sin φ / 2) i).normal 2)
    (cutoff : ℝ)
    (deep : Metric.closedBall origin cutoff ⊆
      interior (SpatialEnvelope.clip (K.completionPlanes T.tentHeight
        (Real.sin φ / 2)) T.level)) :
    let inside := M.inside
    let F := T.cornerTails inside
    let covered := T.cornerTails_covers_rim inside
    let L := T.radialMesh M.inside
    let Q := L.cap
    letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
    let R := (M.completionOutwardForest T positive small).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ G ∈ P.separators,
          ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
            leaf.point.re + leaf.point.im ≤ cutoff ∧
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ leaf : M.GeometricSectorLeaf F covered positive small i,
          leaf.point.re + leaf.point.im ≤ cutoff →
            ∃ G ∈ P.separators,
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
          S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        (∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
          z.re + z.im ∈ Set.Icc 0 cutoff →
            origin + (fiveSectorFrame t positive small i).place.symm z ∈
              interior (SpatialEnvelope.clip (K.completionPlanes T.tentHeight
                (Real.sin φ / 2)) T.level) \ M.extendedGeometricCuts F) ∧
        (∀ S ∈ P.cells, S.TerminalTailsFrom
          (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
          (fun leaf => leaf.tailGraph.graph) cutoff) ∧
        (∀ S ∈ P.cells, S.ApproachedPinchesIn
          (Set.range (fun w : {w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ //
            Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
            (fiveSectorFrame t positive small i).place
              (Q.projectedVertex w.val - origin))) 0 cutoff) ∧
        ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  let inside := M.inside
  let F := T.cornerTails inside
  let covered := T.cornerTails_covers_rim inside
  let L := T.radialMesh M.inside
  let Q := L.cap
  let := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
  let R := (M.completionOutwardForest T positive small).val
  have leaf_coherence := M.completion_geometric_leaf_coherent T positive small height
  have coherent_leaf (D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain)
      (w : F.GeometricVertex)
      (nonroot : w ∉ (M.geometricParents F covered positive small).roots)
      (childless : ∀ child ∉ (M.geometricParents F covered positive small).roots,
        M.geometricParent F covered child ≠ w) :
      F.geometricPosition w ∈ Q.footprint ∧ D.ProjectedCoherentAt Q (F.geometricPosition w) := by
    obtain ⟨v, position, coherent⟩ := leaf_coherence w nonroot childless
    change Q.projectedVertex v = F.geometricPosition w at position
    exact ⟨position ▸ Q.projectedVertex_mem_footprint v, coherent (R.completedDevelopment D)⟩
  refine fun i => ?_
  let B := fiveSectorFrame t positive small i
  obtain ⟨P, provenance, represented, good⟩ :=
    M.exists_geometric_sector_waterfall_with_terminal_tails F covered positive small i cutoff
      (fun w _ => w.tail_end_beyond_clip_ball deep)
  have vertex_pinches : ∀ S ∈ P.cells, S.ApproachedPinchesIn
      (Set.range (fun w : {w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ //
        Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
        B.place (Q.projectedVertex w.val - origin))) 0 cutoff := by
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
      (origin) root (by
        rw [S.lower.point_height]
        exact ⟨bounds.1.le, bounds.2.le⟩))
    have position : origin + B.place.symm (S.lower.point h) =
        F.geometricPosition w := by
      rw [← at_point, B.place.symm_apply_apply]
      abel
    have nonroot : w ∉ (M.geometricParents F covered positive small).roots := by
      rintro ⟨c, equal⟩
      rw [position, ← equal] at physical_inside
      exact (F.componentTail c).boundary.2 physical_inside
    obtain ⟨v, physical_vertex, _⟩ := M.meshed_geometric_nonroot_vertex T positive small w nonroot
    have on_cuts : Q.projectedVertex v ∈ M.extendedGeometricCuts F := by
      change Q.projectedVertex v = F.geometricPosition w at physical_vertex
      rw [physical_vertex, M.extendedGeometricCuts_eq_piece_union F]
      obtain ⟨piece, _, member⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered
        positive small w nonroot
      exact Set.mem_iUnion.mpr ⟨piece, member⟩
    refine ⟨⟨v, on_cuts⟩, ?_⟩
    change B.place (Q.projectedVertex v - origin) = S.lower.point h
    change Q.projectedVertex v = F.geometricPosition w at physical_vertex
    rw [physical_vertex]
    exact at_point
  have terminal_tails := fun S cell => (good S cell).2.2
  have good := fun S cell => (good S cell).1
  have regular := M.geometric_waterfall_regular F covered positive small i cutoff deep
    P represented
  refine ⟨P, provenance, represented, fun S cell =>
    ⟨(good S cell).1, (good S cell).2.1⟩, fun S cell => (good S cell).2.2,
    regular, terminal_tails, vertex_pinches, ?_⟩
  intro D S cell z member slab
  rcases member with strict | coherent
  · have physical := regular S cell z strict slab
    refine ⟨?_, D.projected_coherentAt_of_not_cut Q ?_⟩
    · rw [L.cap_footprint]
      exact interior_subset physical.1
    · exact fun on_cut => physical.2 (R.projectedCutSet_subset on_cut)
  · rcases coherent with zero | ⟨w, equal⟩
    · subst z
      have source_coherent := M.completion_source_coherent T positive small height D
      simpa only [map_zero, add_zero] using source_coherent
    · have position : origin + B.place.symm z =
          F.geometricPosition w.val := by
        rw [← equal]
        change origin + B.place.symm
          (B.place (F.geometricPosition w.val - origin)) = _
        rw [B.place.symm_apply_apply]
        abel
      rw [position]
      exact coherent_leaf D w.val w.property.1 w.property.2.1

/-- Retain the terminal-vertex interface without the actual tail witness. -/
theorem completionOutward_exists_vertex_pinched_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.CompletionMesh φ region extra)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes T.tentHeight (Real.sin φ / 2) i).normal 2)
    (cutoff : ℝ)
    (deep : Metric.closedBall origin cutoff ⊆
      interior (SpatialEnvelope.clip (K.completionPlanes T.tentHeight
        (Real.sin φ / 2)) T.level)) :
    let inside := M.inside
    let F := T.cornerTails inside
    let covered := T.cornerTails_covers_rim inside
    let L := T.radialMesh M.inside
    let Q := L.cap
    letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
    let R := (M.completionOutwardForest T positive small).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ G ∈ P.separators,
          ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
            leaf.point.re + leaf.point.im ≤ cutoff ∧
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ leaf : M.GeometricSectorLeaf F covered positive small i,
          leaf.point.re + leaf.point.im ≤ cutoff →
            ∃ G ∈ P.separators,
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
          S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        (∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
          z.re + z.im ∈ Set.Icc 0 cutoff →
            origin + (fiveSectorFrame t positive small i).place.symm z ∈
              interior (SpatialEnvelope.clip (K.completionPlanes T.tentHeight
                (Real.sin φ / 2)) T.level) \ M.extendedGeometricCuts F) ∧
        (∀ S ∈ P.cells, S.ApproachedPinchesIn
          (Set.range (fun w : {w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ //
            Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
            (fiveSectorFrame t positive small i).place
              (Q.projectedVertex w.val - origin))) 0 cutoff) ∧
        ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, pinches, regular, _, vertices, physical⟩ :=
    M.completionOutward_exists_terminal_waterfall positive small T
        height cutoff deep i
  exact ⟨P, provenance, represented, coordinates, pinches, regular, vertices, physical⟩

/-- Retain the coherent-domain interface without the extra terminal-pinch output. -/
theorem completionOutward_exists_provenant_coherent_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.CompletionMesh φ region extra)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes T.tentHeight (Real.sin φ / 2) i).normal 2)
    (cutoff : ℝ)
    (deep : Metric.closedBall origin cutoff ⊆
      interior (SpatialEnvelope.clip (K.completionPlanes T.tentHeight
        (Real.sin φ / 2)) T.level)) :
    let inside := M.inside
    let F := T.cornerTails inside
    let covered := T.cornerTails_covers_rim inside
    let L := T.radialMesh M.inside
    let Q := L.cap
    letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
    let R := (M.completionOutwardForest T positive small).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ G ∈ P.separators,
          ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
            leaf.point.re + leaf.point.im ≤ cutoff ∧
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ leaf : M.GeometricSectorLeaf F covered positive small i,
          leaf.point.re + leaf.point.im ≤ cutoff →
            ∃ G ∈ P.separators,
              MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
        (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
          S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        (∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
          z.re + z.im ∈ Set.Icc 0 cutoff →
            origin + (fiveSectorFrame t positive small i).place.symm z ∈
              interior (SpatialEnvelope.clip (K.completionPlanes T.tentHeight
                (Real.sin φ / 2)) T.level) \ M.extendedGeometricCuts F) ∧
        ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, pinches, regular, _, physical⟩ :=
    M.completionOutward_exists_vertex_pinched_waterfall positive small T
        height cutoff deep i
  exact ⟨P, provenance, represented, coordinates, pinches, regular, physical⟩

end Unfoldings.ConvexRoof.SectorForest
