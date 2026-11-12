module

public import Unfoldings.Cap.ExtendedBankGeometryBudget
public import Unfoldings.Cap.ExtendedBankChainPositions
public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Cap.SectorSweepBall
public import Unfoldings.Cap.ProperComparisonData
public import Unfoldings.Cap.ExtendedCalibratedComparisonArcs

/-! Uniformly construct proper comparison arcs in the actual roof and radial-bank calibration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- One tilt chosen before both meshes supplies radial matched strips and all-face
geometry, and constructs the finite proper comparison arcs for each actual branch copy.
No bank lift, quadrant bound, curve simplicity, or circle-order input is supplied. -/
theorem exists_uniform_extended_proper_comparison_arcs (t : ℝ) (positive : 0 < t) (small : t < 1) :
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
                    (∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
                      p - K.projectedVertex origin ∈ closedFiveSector t i →
                      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
                      μ * ‖p - K.projectedVertex origin‖ ≤
                        (B.sectorFrame i (D.projectedPlacement Q f p -
                          D.projectedMap Q (K.projectedVertex origin))).re ∧
                      μ * ‖p - K.projectedVertex origin‖ ≤
                        (B.sectorFrame i (D.projectedPlacement Q f p -
                          D.projectedMap Q (K.projectedVertex origin))).im) ∧
                    ∀ radius : ℝ, 2 * radius < cutoff →
                    ∀ w : L.partition.pairedComplex.Vertex Set.univ,
                      Q.projectedVertex w ∈ M.extendedGeometricCuts F →
                      ‖Q.projectedVertex w - K.projectedVertex origin‖ < radius →
                    ∀ target : Fin (R.completedContour.length + 1),
                      L.partition.pairedComplex.vertexForgetCuts (Set.subset_univ _)
                        (L.partition.pairedComplex.boundaryEndVertex R.completedRetain
                          (R.completedContour.cycle.point target)) = w →
                    ∀ circle : ℝ,
                      ‖(R.completedDevelopment D).boundaryPosition
                        (R.completedContour.cycle.point target) -
                          D.projectedMap Q (K.projectedVertex origin)‖ < circle →
                      circle < μ * radius →
                      Nonempty (B.ProperComparisonData w target
                        (D.projectedMap Q (K.projectedVertex origin)) radius circle) := by
  obtain ⟨μ, μbounds, φ, φbounds, normal, geometry⟩ :=
    exists_uniform_extended_bank_geometry_budget.{u, v} t positive small
  refine ⟨μ, μbounds, φ, φbounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let network := M.cornerExtendedOutwardForest positive small T internal source_height lower
  let R := network.val
  obtain ⟨budget, banks⟩ := geometry K tilt M internal source_height lower T conforming cutoff deep
  refine ⟨budget, fun D => ?_⟩
  obtain ⟨B, control, face_bounds⟩ := banks D
  refine ⟨B, control, face_bounds, ?_⟩
  exact M.cornerExtendedOutward_proper_comparison_data positive small T internal source_height
    lower conforming (fun f => normal.trans (tilt f)) cutoff deep μ μbounds.1.le
    D B face_bounds budget

end Unfoldings.ConvexCap
