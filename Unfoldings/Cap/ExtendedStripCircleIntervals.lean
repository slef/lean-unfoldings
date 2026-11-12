module

public import Unfoldings.Cap.ExtendedRadialStripData
public import Unfoldings.Cap.RadialStripCircleInterval

/-! Uniform source-circle intervals for every actual constructed waterfall strip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The tilt and error thresholds precede both meshes. In one actual calibration,
every strip meets every sufficiently small source circle in at most one bank-bounded interval.
All geometric hypotheses of the interval criterion are supplied by the construction. -/
theorem exists_uniform_extended_strip_circle_intervals (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
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
                L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      ∀ S ∈ P.cells,
                        ∃ data : R.RadialStripTraceData positive small D calibration i S
                          ε cutoff,
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (cutoff / 4),
                            S.HasBankCircleInterval data.value data.center cutoff radius := by
  classical
  have margins := fun i : FiveSector =>
    (fiveSectorFrame t positive small i).exists_enclosingStrip_coordinate_margin
  choose μ μpositive margin using margins
  obtain ⟨j, minimal⟩ := Finite.exists_min μ
  let ε := min (μ j / 2) (1 / 8)
  have εpositive : 0 < ε := lt_min (div_pos (μpositive j) (by norm_num)) (by norm_num)
  have εsmall : ε ≤ 1 / 8 := min_le_right _ _
  have error_margin (i : FiveSector) : ε < μ i :=
    ((min_le_left _ _).trans_lt (by linarith [μpositive j])).trans_le (minimal i)
  obtain ⟨φ, bounds, normal, construct⟩ :=
    exists_uniform_extended_radial_strip_data.{u, v} t positive small εpositive
  refine ⟨ε, ⟨εpositive, εsmall⟩, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  obtain ⟨budget, frames⟩ :=
    construct K tilt M internal source_height lower T conforming cutoff deep
  refine ⟨budget, fun D => ?_⟩
  obtain ⟨B, operator_bound, strips⟩ := frames D
  refine ⟨B, operator_bound, ?_⟩
  refine fun i => ?_
  obtain ⟨P, traces⟩ := strips i
  refine ⟨P, fun S cell => ?_⟩
  obtain ⟨data⟩ := traces S cell
  refine ⟨data, fun radius bounds => ?_⟩
  have cutoff_positive : 0 < cutoff := by linarith [bounds.1, bounds.2]
  have far : radius < (1 / 2 - ε) * cutoff := bounds.2.trans_le (by
    have coefficient : (1 : ℝ) / 4 ≤ 1 / 2 - ε := by linarith [εsmall]
    have product := mul_le_mul_of_nonneg_right coefficient cutoff_positive.le
    linarith)
  apply data.circle_interval (error_margin i) _ bounds.1 far
  intro z member forward
  exact margin i z ((P.cover z).mpr ⟨S, cell, member⟩) forward

end Unfoldings.ConvexCap
