module

public import Unfoldings.Cap.ExtendedBankGeometry
public import Unfoldings.Cap.UniformCurvature

/-! Retain the strict curvature budget and actual radial-bank geometry in one uniform choice. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The common positive margin and tilt precede both meshes. The actual roof's
curvature budget and all calibrated bank/face bounds hold simultaneously. -/
theorem exists_uniform_extended_bank_geometry_budget (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ μ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (3 : ℝ) / 4 ≤ Real.cos φ ∧
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
  obtain ⟨μ, μbounds, χ, χbounds, geometry⟩ :=
    exists_uniform_extended_bank_geometry.{u, v} t positive small
  obtain ⟨ψ, ψbounds, normal, curvature⟩ := exists_positive_tilt_curvature_budget Real.pi_pos
  let φ := min χ ψ
  have φpositive : 0 < φ := lt_min χbounds.1 ψbounds.1
  have φχ : φ ≤ χ := min_le_left _ _
  have φψ : φ ≤ ψ := min_le_right _ _
  have normalφ : (3 : ℝ) / 4 ≤ Real.cos φ := normal.trans
    (Real.cos_le_cos_of_nonneg_of_le_pi φpositive.le (by linarith [ψbounds.2, Real.pi_pos]) φψ)
  refine ⟨μ, μbounds, φ, ⟨φpositive, φχ.trans_lt χbounds.2⟩, normalφ, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  have tiltχ := TiltBound.of_le K tilt φpositive.le (by linarith [χbounds.2, Real.pi_pos]) φχ
  have tiltψ := TiltBound.of_le K tilt φpositive.le (by linarith [ψbounds.2, Real.pi_pos]) φψ
  have roof_tilt : Q.TiltBound ψ := L.partition.normalizedCap_tiltBound L.conforming lower tiltψ
  have budget : L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi :=
    (Q.totalCurvature_le_normal_budget normal roof_tilt).trans_lt curvature
  refine ⟨budget, ?_⟩
  exact geometry K tiltχ M internal source_height lower T conforming cutoff deep

end Unfoldings.ConvexCap
