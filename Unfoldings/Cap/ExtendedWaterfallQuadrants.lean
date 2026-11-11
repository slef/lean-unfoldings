module

public import Unfoldings.Cap.ExtendedWaterfallControl
public import Unfoldings.Cap.SectorPositionMargins

/-! Every actual developed strip stays in its sector quadrant relative to the common source. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The actual common-source placement remains in the sector's open quadrant, with uniform
tilt before both meshes and the same calibration as the complete-bank order theorems. -/
theorem exists_uniform_extended_waterfall_quadrants (t : ℝ) (tpos : 0 < t) (tsmall : t < 1) :
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
                          0 < (D.centeredMap Q (K.projectedVertex origin) calibration
                              (fiveSectorFrame t tpos tsmall i).place z -
                            D.centeredMap Q (K.projectedVertex origin) calibration
                              (fiveSectorFrame t tpos tsmall i).place 0).re ∧
                          0 < (D.centeredMap Q (K.projectedVertex origin) calibration
                              (fiveSectorFrame t tpos tsmall i).place z -
                            D.centeredMap Q (K.projectedVertex origin) calibration
                              (fiveSectorFrame t tpos tsmall i).place 0).im := by
  classical
  have margins := fun i : FiveSector =>
    (fiveSectorFrame t tpos tsmall i).exists_enclosingStrip_coordinate_margin
  choose μ μpositive μbound using margins
  obtain ⟨j, minimal⟩ := Finite.exists_min μ
  let ε := μ j / 2
  have εpositive : 0 < ε := div_pos (μpositive j) (by norm_num)
  obtain ⟨φ, bounds, control⟩ := exists_uniform_extended_waterfall_control t tpos tsmall εpositive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest tpos tsmall T internal source_height lower).val
  refine fun D => ?_
  obtain ⟨bankFrame, strip_control⟩ := control K tilt M internal source_height lower T conforming
    cutoff deep D
  refine ⟨bankFrame, ?_⟩
  refine fun i => ?_
  obtain ⟨P, controlled⟩ := strip_control i
  refine ⟨P, fun S cell => ⟨(controlled S cell).1, ?_⟩⟩
  intro z member slab
  let B := fiveSectorFrame t tpos tsmall i
  have bounds := P.cell_bounds cell (z.re + z.im)
  have root_strict : z ∈ B.enclosingStrip.strictCarrier :=
    ⟨bounds.1.trans_lt member.1, member.2.trans_le bounds.2⟩
  have root_member : z ∈ B.enclosingStrip.carrier := ⟨root_strict.1.le, root_strict.2.le⟩
  have hpositive : 0 < z.re + z.im := by
    by_contra nonpositive
    have zero : z.re + z.im = 0 := le_antisymm (le_of_not_gt nonpositive) slab.1
    have impossible := root_strict.1.trans root_strict.2
    rw [zero, B.enclosingStrip_source.1, B.enclosingStrip_source.2] at impossible
    exact (lt_irrefl _ impossible).elim
  have small : ε < μ i := (show ε < μ j from by dsimp only [ε]; linarith [μpositive j]).trans_le
    (minimal i)
  have position := μbound i z root_member slab.1
  exact source_quadrant_of_relative_error small hpositive position.1 position.2
    ((controlled S cell).2 z member slab)

end Unfoldings.ConvexCap
