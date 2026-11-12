module

public import Unfoldings.Cap.WaterfallBankControl

/-! One actual calibration controls every face copy and the same radial matched strip banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The positive margin and tilt precede both meshes. Every actual branch copy stays
in its source quadrant in the same calibration as the radial matched bank traces. -/
theorem exists_uniform_extended_bank_geometry (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ μ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
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
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ B : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                    R.WaterfallBankControl positive small D B (μ / 2) cutoff ∧
                    ∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
                      p - K.projectedVertex origin ∈ closedFiveSector t i →
                      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
                      μ * ‖p - K.projectedVertex origin‖ ≤
                        (B.sectorFrame i (D.projectedPlacement Q f p -
                          D.projectedMap Q (K.projectedVertex origin))).re ∧
                      μ * ‖p - K.projectedVertex origin‖ ≤
                        (B.sectorFrame i (D.projectedPlacement Q f p -
                          D.projectedMap Q (K.projectedVertex origin))).im := by
  classical
  have margins : ∀ i : FiveSector, ∃ μ > 0, μ ≤ (1 : ℝ) / 4 ∧
      ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
        0 ≤ z.re + z.im → μ * ‖z‖ ≤ z.re ∧ μ * ‖z‖ ≤ z.im := by
    intro i
    obtain ⟨μ, μpositive, bound⟩ :=
      (fiveSectorFrame t positive small i).exists_enclosingStrip_norm_coordinate_margin
    refine ⟨min μ (1 / 4), lt_min μpositive (by norm_num), min_le_right _ _, ?_⟩
    intro z member forward
    have coordinates := bound z member forward
    have compare := mul_le_mul_of_nonneg_right (min_le_left μ (1 / 4)) (norm_nonneg z)
    exact ⟨compare.trans coordinates.1, compare.trans coordinates.2⟩
  choose μ μpositive μsmall margin using margins
  obtain ⟨j, minimal⟩ := Finite.exists_min μ
  let η := μ j / 2
  let ε := μ j / 4
  have ηpositive : 0 < η := div_pos (μpositive j) (by norm_num)
  have ηsmall : η ≤ 1 / 8 := by dsimp only [η]; linarith [μsmall j]
  have εpositive : 0 < ε := div_pos (μpositive j) (by norm_num)
  have εη : ε = η / 2 := by dsimp only [ε, η]; ring
  have common_margin (i : FiveSector) (z : ℂ)
      (member : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier)
      (forward : 0 ≤ z.re + z.im) : μ j * ‖z‖ ≤ z.re ∧ μ j * ‖z‖ ≤ z.im := by
    have coordinates := margin i z member forward
    have compare := mul_le_mul_of_nonneg_right (minimal i) (norm_nonneg z)
    exact ⟨compare.trans coordinates.1, compare.trans coordinates.2⟩
  obtain ⟨φ, bounds, control⟩ :=
    exists_uniform_extended_radial_bank_traces t positive small εpositive
  refine ⟨η, ⟨ηpositive, ηsmall⟩, φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  refine fun D => ?_
  obtain ⟨B, controlled⟩ := control K tilt M internal source_height lower T conforming cutoff deep D
  have data : R.WaterfallBankControl positive small D B ε cutoff := controlled
  refine ⟨B, ?_, ?_⟩
  · rwa [← εη]
  · intro i f p member cone region
    have result := RadialCutForest.WaterfallBankControl.all_face_quadrant_margin R positive small
      D B data εpositive.le common_margin i f member cone region
    have coefficient : μ j - 2 * ε = η := by dsimp only [ε, η]; ring
    rwa [coefficient] at result

end Unfoldings.ConvexCap
