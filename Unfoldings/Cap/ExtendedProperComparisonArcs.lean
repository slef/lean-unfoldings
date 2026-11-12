module

public import Unfoldings.Cap.ExtendedBankGeometryBudget
public import Unfoldings.Cap.ExtendedBankChainPositions
public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Cap.SectorSweepBall
public import Unfoldings.Cap.ProperComparisonData

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
  intro radius room w member start target original circle near far
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  obtain ⟨i, sectors, positions⟩ := M.cornerExtendedOutward_bankChain_sector_positions
    positive small T internal source_height lower conforming height w member
  have radius_positive : 0 < radius := (norm_nonneg _).trans_lt start
  have radius_cutoff : radius ≤ cutoff := by linarith
  have deepQ : Metric.closedBall (K.projectedVertex origin) radius ⊆ interior Q.footprint := by
    rw [L.partition.normalizedCap_footprint L.conforming lower]
    exact (Metric.closedBall_subset_closedBall radius_cutoff).trans deep
  have distance (p : Plane) : dist (K.projectedVertex origin) p =
      ‖p - K.projectedVertex origin‖ := (dist_comm _ _).trans (dist_eq_norm _ _)
  obtain ⟨terminal, parameter, endpoint, vertices, points⟩ :=
    R.completedRootPath_exists_radius_prefix network.property member radius
      (by rw [distance]; exact start) deepQ
  have endpoint_norm : ‖(R.completedRootPath w).point terminal parameter -
      K.projectedVertex origin‖ = radius := (distance _).symm.trans endpoint
  have vertices_norm : ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
      j.val ≤ terminal.val →
        ‖(R.completedRootPath w).vertex j - K.projectedVertex origin‖ ≤ radius :=
    fun j before => (distance _).symm.trans_le (vertices j before)
  have points_norm : ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
      PolygonalChain.Before j r terminal parameter →
        ‖(R.completedRootPath w).point j r - K.projectedVertex origin‖ ≤ radius :=
    fun j r before => (distance _).symm.trans_le (points j r before)
  have bounded_faces (f) (p : Plane) (at_face : p ∈ (Q.projectedTriangle f).carrier)
      (bounded : ‖p - K.projectedVertex origin‖ ≤ radius)
      (cone : p - K.projectedVertex origin ∈ closedFiveSector t i) :=
    face_bounds i f p at_face cone (closedBall_subset_sectorSweepInterior positive small
      (K.projectedVertex origin) room
      (by change dist p (K.projectedVertex origin) ≤ radius; rw [dist_eq_norm]; exact bounded))
  obtain ⟨right, left, right_image, left_image, _, order⟩ := B.exists_proper_comparison_arcs
    i w (D.projectedMap Q (K.projectedVertex origin)) μ radius μbounds.1.le positions bounded_faces
    target original (fun j => (sectors j).2) budget (fun j => (sectors j).1) terminal parameter
    endpoint_norm vertices_norm points_norm circle near far
  exact ⟨{
    sector := i
    terminal := terminal
    parameter := parameter
    original := original
    endpoint_radius := endpoint_norm
    positions := positions
    vertices_bounded := vertices_norm
    points_bounded := points_norm
    right := right
    left := left
    right_image := right_image
    left_image := left_image
    circle_order := order }⟩

end Unfoldings.ConvexCap
