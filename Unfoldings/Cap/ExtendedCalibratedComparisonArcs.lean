module

public import Unfoldings.Cap.ExtendedBankChainPositions
public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Cap.SectorSweepBall
public import Unfoldings.Cap.ProperComparisonData
public import Unfoldings.Cap.CompletedProperComparisonData

/-! Actual roof face bounds construct proper comparison arcs in any specified bank calibration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- Apply the actual physical prefix construction in this same calibration.
The start is a specified contour copy, not a different copy of the same vertex. -/
theorem cornerExtendedOutward_proper_comparison_data (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (μ : ℝ) (nonnegative : 0 ≤ μ) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ (D : FacewiseDevelopment L.partition.pairedComplex R.retain)
      (B : R.FiveSectorFrameData positive small (R.completedDevelopment D)),
      (∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
        p - K.projectedVertex origin ∈ closedFiveSector t i →
        p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
        μ * ‖p - K.projectedVertex origin‖ ≤
          (B.sectorFrame i (D.projectedPlacement Q f p -
            D.projectedMap Q (K.projectedVertex origin))).re ∧
        μ * ‖p - K.projectedVertex origin‖ ≤
          (B.sectorFrame i (D.projectedPlacement Q f p -
            D.projectedMap Q (K.projectedVertex origin))).im) →
      L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi →
      ∀ radius : ℝ, 2 * radius < cutoff →
      ∀ w : L.partition.pairedComplex.Vertex Set.univ,
        Q.projectedVertex w ∈ M.extendedGeometricCuts F →
        ‖Q.projectedVertex w - K.projectedVertex origin‖ < radius →
      ∀ target : Fin (R.completedContour.length + 1),
        L.partition.pairedComplex.vertexForgetCuts (Set.subset_univ _)
          (L.partition.pairedComplex.boundaryEndVertex R.completedRetain
            (R.completedContour.cycle.point target)) = w →
      ∀ circle : ℝ,
        ‖(R.completedDevelopment D).boundaryPosition (R.completedContour.cycle.point target) -
          D.projectedMap Q (K.projectedVertex origin)‖ < circle →
        circle < μ * radius →
        Nonempty (B.ProperComparisonData w target
          (D.projectedMap Q (K.projectedVertex origin)) radius circle) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let network := M.cornerExtendedOutwardForest positive small T internal source_height lower
  let R := network.val
  refine fun D B face_bounds budget => ?_
  intro radius room w member start target original circle near far
  obtain ⟨i, sectors, positions⟩ := M.cornerExtendedOutward_bankChain_sector_positions
    positive small T internal source_height lower conforming height w member
  have radius_positive : 0 < radius := (norm_nonneg _).trans_lt start
  have radius_cutoff : radius ≤ cutoff := by linarith
  have deepQ : Metric.closedBall (K.projectedVertex origin) radius ⊆ interior Q.footprint := by
    rw [L.partition.normalizedCap_footprint L.conforming lower]
    exact (Metric.closedBall_subset_closedBall radius_cutoff).trans deep
  have bounded_faces (f) (p : Plane) (at_face : p ∈ (Q.projectedTriangle f).carrier)
      (bounded : ‖p - K.projectedVertex origin‖ ≤ radius)
      (cone : p - K.projectedVertex origin ∈ closedFiveSector t i) :=
    face_bounds i f p at_face cone (closedBall_subset_sectorSweepInterior positive small
      (K.projectedVertex origin) room
      (by change dist p (K.projectedVertex origin) ≤ radius; rw [dist_eq_norm]; exact bounded))
  obtain ⟨comparison, _⟩ := B.exists_proper_comparison_data_in_sector i network.property w member
    (D.projectedMap Q (K.projectedVertex origin)) μ radius nonnegative start deepQ positions
    (fun j => (sectors j).1) (fun j => (sectors j).2) bounded_faces budget target original
    circle near far
  exact ⟨comparison⟩

end Unfoldings.ConvexCap.SectorForest
