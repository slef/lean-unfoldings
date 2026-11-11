module

public import Unfoldings.Cap.GeometricRecoverableWaterfall
public import Unfoldings.Cap.GeometricWaterfallRegular
public import Unfoldings.Cap.ExtendedLeafCoherence
public import Unfoldings.Cap.ExtendedWaterfallInjective
public import Unfoldings.Cap.CenteredCoherentMap

/-! Uniform actual-map injectivity on whole waterfall strips, including reopening leaf pinches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Every constructed strip has an injective actual map on the whole physical height slab.
Its possibly separate positive-width components are compared through proved coherent leaves.
The tilt is chosen before either mesh. Separation of different developed strips remains open. -/
theorem exists_uniform_extended_waterfall_full_injectivity :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (tpos : 0 < t) (tsmall : t < 1) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest tpos tsmall T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ calibration : Plane ≃ₗᵢ[ℝ] ℂ, ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t tpos tsmall i).enclosingStrip.Subdivision,
                      ∀ S ∈ P.cells,
                        Set.InjOn (D.centeredMap Q (K.projectedVertex origin) calibration
                          (fiveSectorFrame t tpos tsmall i).place)
                          {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} := by
  obtain ⟨δ, δpositive, margins⟩ :=
    FacewiseDevelopment.exists_coordinatePlacement_axis_threshold.{0, 0}
  obtain ⟨φ, bounds, normal, control⟩ := exists_uniform_completed_direction_control δpositive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt t origin M tpos tsmall internal source_height Z lower T conforming
    cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest tpos tsmall T internal source_height lower).val
  refine fun D => ?_
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  have wedges := M.cornerExtendedOutward_curvedPathWedges tpos tsmall T internal source_height
    lower conforming height
  have roof_tilt : Q.TiltBound φ := L.partition.normalizedCap_tiltBound L.conforming lower tilt
  obtain ⟨calibration, close⟩ := control Q roof_tilt (K.projectedVertex origin)
    (M.extendedGeometricCuts F) R wedges (R.completedDevelopment D)
  have leaf_coherence := M.cornerExtended_geometric_leaf_coherent tpos tsmall T internal
    source_height lower conforming height
  have coherent_leaf (w : F.GeometricVertex)
      (nonroot : w ∉ (M.geometricParents F covered tpos tsmall lower).roots)
      (childless : ∀ child ∉ (M.geometricParents F covered tpos tsmall lower).roots,
        M.geometricParent F covered child ≠ w) :
      F.geometricPosition w ∈ Q.footprint ∧
        D.ProjectedCoherentAt Q (F.geometricPosition w) := by
    obtain ⟨v, position, coherent⟩ := leaf_coherence w nonroot childless
    change Q.projectedVertex v = F.geometricPosition w at position
    refine ⟨position ▸ Q.projectedVertex_mem_footprint v, ?_⟩
    exact coherent (R.completedDevelopment D)
  have source_coherent := coherent_leaf (Sum.inl origin)
    (M.geometric_original_nonroot F covered tpos tsmall lower origin)
    (M.geometric_origin_childless F covered tpos tsmall lower)
  change K.projectedVertex origin ∈ Q.footprint ∧
    D.ProjectedCoherentAt Q (K.projectedVertex origin) at source_coherent
  refine ⟨calibration, ?_⟩
  intro i
  let B := fiveSectorFrame t tpos tsmall i
  let E := insert (0 : ℂ) (Set.range (fun w :
    M.GeometricSectorLeaf F covered tpos tsmall lower i => w.point))
  obtain ⟨P, _, represented, good⟩ := M.exists_geometric_sector_waterfall_recoverable F covered
    tpos tsmall lower i cutoff (fun w _ => w.tail_end_beyond_clip_ball deep)
  have regular := M.geometric_waterfall_regular F covered tpos tsmall lower i cutoff deep
    P represented
  refine ⟨P, ?_⟩
  intro S cell
  apply D.centeredMap_injOn_strip_recoverable (K.projectedVertex origin) calibration B.place
    (margins (R.completedDevelopment D) Q calibration close B.place) S E 0 cutoff
    (good S cell).2.2
  intro z member slab
  rcases member with strict | coherent
  · have physical := regular S cell z strict slab
    refine ⟨?_, D.projected_coherentAt_of_not_cut Q ?_⟩
    · rw [L.partition.normalizedCap_footprint L.conforming lower]
      exact interior_subset physical.1
    · exact fun on_cut => physical.2 (R.projectedCutSet_subset on_cut)
  · rcases coherent with zero | ⟨w, equal⟩
    · subst z
      simpa only [map_zero, add_zero] using source_coherent
    · have position : K.projectedVertex origin + B.place.symm z =
          F.geometricPosition w.val := by
        rw [← equal]
        change K.projectedVertex origin + B.place.symm
          (B.place (F.geometricPosition w.val - K.projectedVertex origin)) = _
        rw [B.place.symm_apply_apply]
        abel
      rw [position]
      exact coherent_leaf w.val w.property.1 w.property.2.1

end Unfoldings.ConvexCap
