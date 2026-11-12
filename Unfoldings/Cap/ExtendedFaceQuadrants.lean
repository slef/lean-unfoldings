module

public import Unfoldings.Cap.ExtendedFacePositionControl
public import Unfoldings.Cap.FacePositionMargins

/-! All actual bank and branch copies stay uniformly inside their assigned sector quadrants. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- A single positive coordinate margin and tilt threshold work before either mesh,
for every actual containing-face copy, in the common bank-order calibration. -/
theorem exists_uniform_extended_face_quadrants (t : ℝ) (tpos : 0 < t) (tsmall : t < 1) :
    ∃ μ > 0, ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
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
                  ∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
                    p - K.projectedVertex origin ∈ closedFiveSector t i →
                    p ∈ sectorSweepInterior tpos tsmall (K.projectedVertex origin) cutoff →
                    let frame := (fiveSectorFrame t tpos tsmall i).place
                    μ * ‖p - K.projectedVertex origin‖ ≤
                      (D.centeredCoordinatePlacement Q (K.projectedVertex origin) calibration
                        frame f (frame (p - K.projectedVertex origin)) -
                        D.centeredMap Q (K.projectedVertex origin) calibration frame 0).re ∧
                    μ * ‖p - K.projectedVertex origin‖ ≤
                      (D.centeredCoordinatePlacement Q (K.projectedVertex origin) calibration
                        frame f (frame (p - K.projectedVertex origin)) -
                        D.centeredMap Q (K.projectedVertex origin) calibration frame 0).im := by
  classical
  have margins := fun i : FiveSector =>
    (fiveSectorFrame t tpos tsmall i).exists_enclosingStrip_norm_coordinate_margin
  choose μ positive margin using margins
  obtain ⟨j, minimal⟩ := Finite.exists_min μ
  let ε := μ j / 2
  have εpositive : 0 < ε := div_pos (positive j) (by norm_num)
  obtain ⟨φ, bounds, control⟩ := exists_uniform_extended_face_position_control t tpos tsmall
    εpositive
  refine ⟨ε, εpositive, φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest tpos tsmall T internal source_height lower).val
  refine fun D => ?_
  obtain ⟨bankFrame, error⟩ := control K tilt M internal source_height lower T conforming
    cutoff deep D
  let calibration := R.calibratedFrame (R.completedDevelopment D)
    bankFrame.anchor bankFrame.reference
  refine ⟨bankFrame, ?_⟩
  refine fun i f p member cone region => ?_
  let B := fiveSectorFrame t tpos tsmall i
  have nonnegative := B.quadrant_nonneg cone
  have coordinates := margin i (B.place (p - K.projectedVertex origin))
    (B.enclosingStrip_mem cone) (add_nonneg nonnegative.1 nonnegative.2)
  rw [B.place.norm_map] at coordinates
  have first := (mul_le_mul_of_nonneg_right (minimal i) (norm_nonneg
    (p - K.projectedVertex origin))).trans coordinates.1
  have last := (mul_le_mul_of_nonneg_right (minimal i) (norm_nonneg
    (p - K.projectedVertex origin))).trans coordinates.2
  have result := D.centered_face_quadrant_margin Q (K.projectedVertex origin) calibration
    B.place f p first last (error f p member region)
  have half : μ j - ε = ε := by dsimp only [ε]; ring
  rw [half] at result
  exact result

end Unfoldings.ConvexCap
