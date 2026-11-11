module

public import Unfoldings.Cap.GeometricRecoverableWaterfall
public import Unfoldings.Cap.GeometricWaterfallRegular
public import Unfoldings.Cap.ExtendedLeafCoherence
public import Unfoldings.Cap.ExtendedWaterfallInjective
public import Unfoldings.Cap.CenteredMapSourceError
public import Unfoldings.Cap.CompletedLinearError
public import Unfoldings.Geometry.NearIdentityMargins

/-! Uniform bank frames, whole-strip injectivity, and common-source position control. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- One actual calibration gives the bank quadrants, injective whole-strip maps, and any
requested source-position error. All geometric domains and coherent pinch values are derived;
the common positive tilt threshold is chosen before both original and auxiliary meshes. -/
theorem exists_uniform_extended_waterfall_control (t : ℝ) (tpos : 0 < t) (tsmall : t < 1)
    {ε : ℝ} (εpositive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (internal : ¬ C.IsBoundaryVertex Set.univ origin)
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
                  ∃ bankFrame : R.FiveSectorFrameData tpos tsmall (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t tpos tsmall i).enclosingStrip.Subdivision,
                      ∀ S ∈ P.cells,
                        Set.InjOn (D.centeredMap Q (K.projectedVertex origin) calibration
                          (fiveSectorFrame t tpos tsmall i).place)
                          {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∧
                        ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
                          ‖(D.centeredMap Q (K.projectedVertex origin) calibration
                              (fiveSectorFrame t tpos tsmall i).place z -
                            D.centeredMap Q (K.projectedVertex origin) calibration
                              (fiveSectorFrame t tpos tsmall i).place 0) - z‖ ≤
                            ε * (z.re + z.im) := by
  let c := min (ε / 2) (1 / 8)
  have cpositive : 0 < c := lt_min (by positivity) (by norm_num)
  have csmall : c < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have cε : 2 * c ≤ ε := by linarith [min_le_left (ε / 2) (1 / 8)]
  obtain ⟨φ, bounds, normal, control⟩ :=
    exists_uniform_completed_frame_linear_error.{0, 0} t tpos tsmall cpositive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming
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
  obtain ⟨_, frames⟩ := control Q roof_tilt (K.projectedVertex origin)
    (M.extendedGeometricCuts F) R wedges
  obtain ⟨bankFrame, linear_error⟩ := frames (R.completedDevelopment D)
  let calibration := R.calibratedFrame (R.completedDevelopment D)
    bankFrame.anchor bankFrame.reference
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
  refine ⟨bankFrame, ?_⟩
  refine fun i => ?_
  let B := fiveSectorFrame t tpos tsmall i
  let E := insert (0 : ℂ) (Set.range (fun w :
    M.GeometricSectorLeaf F covered tpos tsmall lower i => w.point))
  obtain ⟨P, provenance, represented, good⟩ :=
    M.exists_geometric_sector_waterfall_recoverable F covered tpos tsmall lower i cutoff
      (fun w _ => w.tail_end_beyond_clip_ball deep)
  have regular := M.geometric_waterfall_regular F covered tpos tsmall lower i cutoff deep
    P represented
  refine ⟨P, ?_⟩
  intro S cell
  have inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
      z.re + z.im ∈ Set.Icc 0 cutoff →
      K.projectedVertex origin + B.place.symm z ∈ Q.footprint ∧
        D.ProjectedCoherentAt Q (K.projectedVertex origin + B.place.symm z) := by
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
  have source_walls := P.cell_wall_provenance cell
  have first_source : S.lower.coordinate 0 = 0 := by
    rcases source_walls.1 with equal | wall
    · rw [equal]
      exact B.enclosingStrip_source.1
    · obtain ⟨w, _, completion⟩ := provenance S.lower wall
      exact completion.1
  have last_source : S.upper.coordinate 0 = 0 := by
    rcases source_walls.2 with equal | wall
    · rw [equal]
      exact B.enclosingStrip_source.2
    · obtain ⟨w, _, completion⟩ := provenance S.upper wall
      exact completion.1
  refine ⟨?_, ?_⟩
  · exact D.centeredMap_injOn_strip_recoverable (K.projectedVertex origin) calibration B.place
      (fun f => affineAxisMargins_pos_of_linear_error _ csmall (linear_error B.place f))
      S E 0 cutoff (good S cell).2.2 inside
  · intro z member slab
    have bound := D.centeredMap_source_error (K.projectedVertex origin) calibration B.place
      cpositive.le (linear_error B.place) S E first_source last_source (good S cell).2.2
      inside member slab
    exact bound.trans (by nlinarith [mul_le_mul_of_nonneg_right cε slab.1])

end Unfoldings.ConvexCap
