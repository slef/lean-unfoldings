module

public import Unfoldings.Cap.GeometricRecoverableWaterfall
public import Unfoldings.Cap.GeometricWaterfallRegular
public import Unfoldings.Cap.ExtendedLeafCoherence
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! The same actual waterfall has coherent domains for every minimal roof development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- Construct the subdivision before its development, deriving all coherence needed at
reopening pinches. In particular no bank lift or compatible trace is a hypothesis. -/
theorem cornerExtendedOutward_exists_coherent_waterfall (positive : 0 < t) (small : t < 1)
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
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
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
  obtain ⟨P, _, represented, good⟩ :=
    M.exists_geometric_sector_waterfall_recoverable F covered positive small lower i cutoff
      (fun w _ => w.tail_end_beyond_clip_ball deep)
  have regular := M.geometric_waterfall_regular F covered positive small lower i cutoff deep
    P represented
  refine ⟨P, fun S cell => (good S cell).2.2, ?_⟩
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

end Unfoldings.ConvexCap.SectorForest
