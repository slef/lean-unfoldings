module

public import Unfoldings.Cap.ExtendedWaterfallControl
public import Unfoldings.Cap.WaterfallFaceError

/-! Uniform common-source position control for every actual roof face and bank copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The tilt threshold precedes both meshes. The calibration is the same actual frame
used for bank order, and the estimate includes every containing-face copy on a cut. -/
theorem exists_uniform_extended_face_position_control (t : ℝ) (tpos : 0 < t) (tsmall : t < 1)
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
                  ∀ f p, p ∈ (Q.projectedTriangle f).carrier →
                    p ∈ sectorSweepInterior tpos tsmall (K.projectedVertex origin) cutoff →
                    ‖(calibration (D.projectedPlacement Q f p) -
                        calibration (D.projectedMap Q (K.projectedVertex origin))) -
                      Complex.orthonormalBasisOneI.repr.symm (p - K.projectedVertex origin)‖ ≤
                        ε * ‖p - K.projectedVertex origin‖ := by
  classical
  obtain ⟨φ, bounds, control⟩ := exists_uniform_extended_waterfall_control t tpos tsmall
    (div_pos εpositive (by norm_num : (0 : ℝ) < 2))
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
  let calibration := R.calibratedFrame (R.completedDevelopment D)
    bankFrame.anchor bankFrame.reference
  have strips : ∀ i : FiveSector,
      ∃ P : (fiveSectorFrame t tpos tsmall i).enclosingStrip.Subdivision,
        ∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
          ‖(D.centeredMap Q (K.projectedVertex origin) calibration
              (fiveSectorFrame t tpos tsmall i).place z -
            D.centeredMap Q (K.projectedVertex origin) calibration
              (fiveSectorFrame t tpos tsmall i).place 0) - z‖ ≤ ε / 2 * (z.re + z.im) := by
    intro i
    obtain ⟨P, controlled⟩ := strip_control i
    exact ⟨P, fun S cell => (controlled S cell).2⟩
  choose P estimates using strips
  refine ⟨bankFrame, ?_⟩
  refine fun f p member region => ?_
  have error := D.projectedPlacement_source_error_of_waterfall Q tpos tsmall
    (K.projectedVertex origin) calibration P cutoff (by positivity) estimates f member region
  convert error using 1
  ring

end Unfoldings.ConvexCap
